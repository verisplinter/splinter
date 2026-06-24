// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Skeleton refinement boundary:
// SystemModel<UnifiedCacheProgramModel> -> CrashAwareCachingDiskJournal.

#![allow(unused_imports)]
#![allow(unused_variables)]

use vstd::prelude::*;
use vstd::assert_maps_equal;

use crate::abstract_system::MsgHistory_v::MsgHistory;
use crate::disk::GenericDisk_v::{Address, AU};
use crate::implementation::AbstractSuperblock_v::{
    AbstractSuperblockImage, abstract_superblock_raw_wf, empty_abstract_superblock_image,
    parse_abstract_superblock,
};
use crate::implementation::AnotherAtomicState_v::{
    AtomicInflightInfo, AtomicJournalState,
};
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachedJournal_v::CachedJournal;
use crate::implementation::CachingDiskAdapterRefinement_v::{
    cache_filled_addr, cache_filled_page,
    caching_disk_i as adapter_caching_disk_i, project_cache_pages, project_cache_status,
    cache_disk_ops_begin_refines_caching_disk_internal,
    cache_disk_ops_end_refines_caching_disk_internal,
    projected_cache_access_outside_aus_unchanged,
};
use crate::implementation::CachingDisk_v::{addresses_in_aus, CachingDisk, PageStatus};
use crate::implementation::CachingDiskJournal_v::CachingDiskJournal;
use crate::implementation::CrashAwareCachingDiskJournal_v::{
    CachingDiskJournalFrozenMetadata, CachingDiskJournalImage, CrashAwareCachingDiskJournal,
    EphemeralCachingDiskJournal, PersistentCachingDiskJournal,
};
use crate::implementation::CrashAwareCachingDiskJournalRefinement_v::*;
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::implementation::JournalTypes_v::to_journal_records;
use crate::implementation::UnifiedCacheProgramModel_v::UnifiedCacheProgramModel;
use crate::implementation::UnifiedCacheSystem_v::UnifiedCacheSystem;
use crate::journal::LinkedJournal_v::{DiskView, TruncatedJournal};
use crate::spec::AsyncDisk_t::{DiskRequest, DiskResponse, RawPage};
use crate::trusted::ProgramModelTrait_t::{DiskModel, ProgramModelTrait};
use crate::trusted::SystemModel_t::SystemModel;

verus! {

pub open spec fn async_disk_superblock_raw_i(
    disk_content: Map<Address, RawPage>,
) -> RawPage
{
    if disk_content.contains_key(spec_superblock_addr()) {
        disk_content[spec_superblock_addr()]
    } else {
        arbitrary()
    }
}

pub open spec fn async_disk_superblock_image_i(
    disk_content: Map<Address, RawPage>,
) -> AbstractSuperblockImage
{
    parse_abstract_superblock(async_disk_superblock_raw_i(disk_content))
}

pub open spec fn async_disk_superblock_page_wf(
    disk_content: Map<Address, RawPage>,
) -> bool
{
    &&& disk_content.contains_key(spec_superblock_addr())
    &&& abstract_superblock_raw_wf(disk_content[spec_superblock_addr()])
}

// Journal-side projection of the shared-cache system state. Before the program
// has loaded the superblock, the durable image comes from the async disk; after
// loading, it comes from the cached program metadata.
#[verifier::ext_equal]
pub struct UnifiedCacheJournalSource {
    pub journal: AtomicJournalState::State,
    pub cache: Cache::State,
    pub disk: DiskModel,
    // Mirrors UnifiedCacheSystem::persistent_image. When it is None, the
    // durable image is derived from the async disk superblock page.
    pub persistent_image: Option<AbstractSuperblockImage>,
    // In-flight state is the candidate image the caller may select on crash via
    // keep_in_flight. This shard should not independently decide durability.
    pub in_flight: Option<AtomicInflightInfo>,
    pub in_flight_image: Option<AbstractSuperblockImage>,
}

pub open spec fn unified_cache_journal_source(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> UnifiedCacheJournalSource
    {
        let state = model.program.state;
        UnifiedCacheJournalSource{
            journal: state.journal,
            cache: state.cache,
            disk: model.disk,
            persistent_image: state.persistent_image,
            in_flight: state.in_flight,
            in_flight_image: if state.in_flight is Some {
                Option::Some(state.atomic_inflight_superblock_i())
            } else {
                Option::None
            },
        }
}

impl UnifiedCacheJournalSource {
    pub open spec fn superblock_loaded(self) -> bool
    {
        self.persistent_image is Some
    }

    pub open spec fn persistent_superblock_image_i(self) -> AbstractSuperblockImage
    {
        if self.persistent_image is Some {
            self.persistent_image.unwrap()
        } else {
            async_disk_superblock_image_i(self.disk.content)
        }
    }

    pub open spec fn journal_image_tj_i(
        disk_content: Map<Address, RawPage>,
        image: AbstractSuperblockImage,
    ) -> TruncatedJournal
    {
        TruncatedJournal{
            freshest_rec: image.journal_snapshot.freshest_rec(),
            disk_view: DiskView{
                boundary_lsn: image.journal_snapshot.boundary_lsn,
                entries: to_journal_records(disk_content),
            },
        }
    }

    pub open spec fn journal_image_projection_aus_i(
        self,
        image: AbstractSuperblockImage,
    ) -> Set<AU>
    {
        if self.journal.ready() {
            self.journal.loaded_index_aus()
        } else {
            let tj = Self::journal_image_tj_i(self.disk.content, image);
            tj.disk_view.loose_build_lsn_au_index_au_walk(
                tj.freshest_rec,
                image.journal_snapshot.first(),
            ).values()
        }
    }

    pub open spec fn journal_image_i(
        self,
        image: AbstractSuperblockImage,
    ) -> CachingDiskJournalImage
    {
        CachingDiskJournalImage{
            persistent: self.disk.content.restrict(
                addresses_in_aus(self.journal_image_projection_aus_i(image)),
            ),
            snapshot: image.journal_snapshot,
            seq_end: image.journal_seq_end,
        }
    }

    pub open spec fn persistent_journal_image_i(self) -> CachingDiskJournalImage
    {
        self.journal_image_i(self.persistent_superblock_image_i())
    }

    pub open spec fn journal_projection_aus(self) -> Set<AU>
    {
        if self.journal.ready() {
            self.journal.owned_aus()
        } else {
            self.journal_image_projection_aus_i(self.persistent_superblock_image_i())
        }
    }

    pub open spec fn journal_caching_disk_i(self) -> CachingDisk::State
    {
        adapter_caching_disk_i(self.cache, self.disk, self.journal_projection_aus())
    }

    pub open spec fn journal_caching_disk_state_i(self) -> CachingDiskJournal::State
    {
        CachingDiskJournal::State{
            journal: self.journal.journal,
            disk: self.journal_caching_disk_i(),
            mini_allocator: self.journal.mini_allocator,
            au_page_bounds: self.journal.au_page_bounds,
        }
    }

    pub open spec fn ephemeral_journal_i(self) -> EphemeralCachingDiskJournal
    {
        if self.superblock_loaded() {
            EphemeralCachingDiskJournal::Known{v: self.journal_caching_disk_state_i()}
        } else {
            EphemeralCachingDiskJournal::Unknown
        }
    }

    pub open spec fn frozen_journal_metadata_i(self) -> Option<CachingDiskJournalFrozenMetadata>
    {
        if self.journal.in_flight is Some {
            let image = self.journal.in_flight.unwrap();
            Option::Some(CachingDiskJournalFrozenMetadata{
                snapshot: image.snapshot,
                seq_end: image.seq_end,
            })
        } else {
            Option::None
        }
    }

    pub open spec fn persistent_journal_i(self) -> PersistentCachingDiskJournal
    {
        let persistent_image = self.persistent_journal_image_i();
        if self.superblock_loaded() {
            PersistentCachingDiskJournal::Metadata{meta: persistent_image.metadata()}
        } else {
            PersistentCachingDiskJournal::Image{image: persistent_image}
        }
    }

    pub open spec fn i(self) -> CrashAwareCachingDiskJournal::State
    {
        CrashAwareCachingDiskJournal::State{
            persistent: self.persistent_journal_i(),
            ephemeral: self.ephemeral_journal_i(),
            frozen: self.frozen_journal_metadata_i(),
            prepared: self.journal.prepared,
        }
    }

    pub open spec fn inv(self) -> bool
    {
        &&& self.journal.wf()
        &&& async_disk_superblock_page_wf(self.disk.content)
        &&& self.persistent_superblock_image_i().wf()
        &&& self.cache.inv()
        &&& self.disk.inv()
        &&& self.journal_caching_disk_i().inv()
        &&& !self.superblock_loaded() ==> {
            &&& self.journal == AtomicJournalState::State::empty()
            &&& self.in_flight is None
            &&& self.in_flight_image is None
        }
        &&& self.in_flight is Some <==> self.journal.in_flight is Some
        &&& self.in_flight is Some <==> self.in_flight_image is Some
        &&& self.in_flight_image is Some ==> {
            let image = self.in_flight_image.unwrap();
            let journal_image = self.journal.in_flight.unwrap();
            &&& image.wf()
            &&& image.journal_snapshot == journal_image.snapshot
            &&& image.journal_seq_end == journal_image.seq_end
        }
    }

    pub open spec fn semantic_inv(self) -> bool
    {
        self.i().refinement_inv()
    }

    pub open spec fn same_except_cache_and_disk(self, post: Self) -> bool
    {
        &&& post.journal == self.journal
        &&& post.persistent_image == self.persistent_image
        &&& post.in_flight == self.in_flight
        &&& post.in_flight_image == self.in_flight_image
    }

    pub open spec fn disk_model_agrees_on_journal_owned_au_ranges(
        self,
        post: Self,
    ) -> bool
    {
        let aus = self.journal_projection_aus();
        &&& post.journal_projection_aus() =~= aus
        &&& post.disk.requests == self.disk.requests
        &&& post.disk.responses == self.disk.responses
        &&& post.disk.content.restrict(addresses_in_aus(aus))
            == self.disk.content.restrict(addresses_in_aus(aus))
        // Needed only when persistent_image is None and the source derives the
        // durable superblock image from the async disk.
        &&& post.disk.content.contains_key(spec_superblock_addr())
        &&& post.disk.content[spec_superblock_addr()]
            == self.disk.content[spec_superblock_addr()]
    }

    pub open spec fn cache_model_agrees_on_journal_owned_au_ranges(
        self,
        post: Self,
    ) -> bool
    {
        let aus = self.journal_projection_aus();
        &&& post.cache.inv()
        &&& project_cache_pages(post.cache, aus) == project_cache_pages(self.cache, aus)
        &&& project_cache_status(post.cache, aus) == project_cache_status(self.cache, aus)
    }

    pub proof fn inv_preserved_by_disk_model_agreement_on_journal_owned_au_ranges(
        self,
        post: Self,
    )
        requires
            self.inv(),
            self.same_except_cache_and_disk(post),
            self.disk_model_agrees_on_journal_owned_au_ranges(post),
            self.cache_model_agrees_on_journal_owned_au_ranges(post),
        ensures
            post.inv(),
    {
        let aus = self.journal_projection_aus();

        assert(post.journal.wf());

        assert(async_disk_superblock_page_wf(post.disk.content)) by {
            assert(async_disk_superblock_page_wf(self.disk.content));
            assert(self.disk.content.contains_key(spec_superblock_addr()));
            assert(abstract_superblock_raw_wf(self.disk.content[spec_superblock_addr()]));
            assert(post.disk.content.contains_key(spec_superblock_addr()));
            assert(post.disk.content[spec_superblock_addr()]
                == self.disk.content[spec_superblock_addr()]);
        }

        assert(post.persistent_superblock_image_i()
            == self.persistent_superblock_image_i()) by {
            if self.persistent_image is Some {
                assert(post.persistent_image is Some);
            } else {
                assert(post.persistent_image is None);
                assert(self.disk.content.contains_key(spec_superblock_addr()));
                assert(post.disk.content.contains_key(spec_superblock_addr()));
                assert(async_disk_superblock_raw_i(post.disk.content)
                    == async_disk_superblock_raw_i(self.disk.content));
            }
        }
        assert(post.persistent_superblock_image_i().wf());

        assert(post.disk.inv()) by {
            assert(self.disk.inv());
            assert(post.disk.requests.dom() == self.disk.requests.dom());
            assert(post.disk.responses.dom() == self.disk.responses.dom());
        }

        assert(post.journal_caching_disk_i() == self.journal_caching_disk_i()) by {
            assert(post.journal_projection_aus() =~= aus);
            assert_maps_equal!(
                post.journal_caching_disk_i().cache,
                self.journal_caching_disk_i().cache,
                addr => {
                    assert(post.journal_projection_aus().contains(addr.au)
                        <==> aus.contains(addr.au));
                    assert(project_cache_pages(post.cache, aus)
                        == project_cache_pages(self.cache, aus));
                }
            );
            assert_maps_equal!(
                post.journal_caching_disk_i().status,
                self.journal_caching_disk_i().status,
                addr => {
                    assert(post.journal_projection_aus().contains(addr.au)
                        <==> aus.contains(addr.au));
                    assert(project_cache_status(post.cache, aus)
                        == project_cache_status(self.cache, aus));
                }
            );
            assert_maps_equal!(
                post.journal_caching_disk_i().persistent,
                self.journal_caching_disk_i().persistent,
                addr => {
                    assert(post.journal_projection_aus().contains(addr.au)
                        <==> aus.contains(addr.au));
                    assert(addresses_in_aus(post.journal_projection_aus()).contains(addr)
                        <==> addresses_in_aus(aus).contains(addr));
                    if addresses_in_aus(aus).contains(addr) {
                        assert(post.disk.content.restrict(addresses_in_aus(aus))
                            == self.disk.content.restrict(addresses_in_aus(aus)));
                    }
                }
            );
        }

        assert(post.journal_caching_disk_i().inv());
    }

    pub proof fn journal_caching_disk_i_preserved_by_disk_model_agreement_on_journal_owned_au_ranges(
        self,
        post: Self,
    )
        requires
            self.disk_model_agrees_on_journal_owned_au_ranges(post),
            self.cache_model_agrees_on_journal_owned_au_ranges(post),
        ensures
            post.journal_caching_disk_i() == self.journal_caching_disk_i(),
    {
        let aus = self.journal_projection_aus();

        assert(post.journal_caching_disk_i() == self.journal_caching_disk_i()) by {
            assert(post.journal_projection_aus() =~= aus);
            assert_maps_equal!(
                post.journal_caching_disk_i().cache,
                self.journal_caching_disk_i().cache,
                addr => {
                    assert(post.journal_projection_aus().contains(addr.au)
                        <==> aus.contains(addr.au));
                    assert(project_cache_pages(post.cache, aus)
                        == project_cache_pages(self.cache, aus));
                }
            );
            assert_maps_equal!(
                post.journal_caching_disk_i().status,
                self.journal_caching_disk_i().status,
                addr => {
                    assert(post.journal_projection_aus().contains(addr.au)
                        <==> aus.contains(addr.au));
                    assert(project_cache_status(post.cache, aus)
                        == project_cache_status(self.cache, aus));
                }
            );
            assert_maps_equal!(
                post.journal_caching_disk_i().persistent,
                self.journal_caching_disk_i().persistent,
                addr => {
                    assert(post.journal_projection_aus().contains(addr.au)
                        <==> aus.contains(addr.au));
                    assert(addresses_in_aus(post.journal_projection_aus()).contains(addr)
                        <==> addresses_in_aus(aus).contains(addr));
                    if addresses_in_aus(aus).contains(addr) {
                        assert(post.disk.content.restrict(addresses_in_aus(aus))
                            == self.disk.content.restrict(addresses_in_aus(aus)));
                    }
                }
            );
        }
    }

    pub proof fn journal_caching_disk_i_preserved_by_cache_access_outside_journal_projection(
        self,
        post: Self,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    )
        requires
            self.inv(),
            post.disk == self.disk,
            post.journal_projection_aus() =~= self.journal_projection_aus(),
            Cache::State::next(self.cache, post.cache, Cache::Label::Access{reads, writes}),
            writes.dom().disjoint(addresses_in_aus(self.journal_projection_aus())),
        ensures
            self.disk_model_agrees_on_journal_owned_au_ranges(post),
            self.cache_model_agrees_on_journal_owned_au_ranges(post),
            post.journal_caching_disk_i() == self.journal_caching_disk_i(),
    {
        let aus = self.journal_projection_aus();
        projected_cache_access_outside_aus_unchanged(
            self.cache,
            post.cache,
            aus,
            reads,
            writes,
        );
        assert(post.cache.inv()) by {
            Cache::State::inv_next(self.cache, post.cache, Cache::Label::Access{reads, writes});
        }
        assert(self.disk_model_agrees_on_journal_owned_au_ranges(post));
        assert(self.cache_model_agrees_on_journal_owned_au_ranges(post));
        self.journal_caching_disk_i_preserved_by_disk_model_agreement_on_journal_owned_au_ranges(
            post,
        );
    }

    pub proof fn inv_preserved_by_cache_access_outside_journal_projection(
        self,
        post: Self,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    )
        requires
            self.inv(),
            self.same_except_cache_and_disk(post),
            post.disk == self.disk,
            post.journal_projection_aus() =~= self.journal_projection_aus(),
            Cache::State::next(self.cache, post.cache, Cache::Label::Access{reads, writes}),
            writes.dom().disjoint(addresses_in_aus(self.journal_projection_aus())),
        ensures
            post.inv(),
            post.journal_caching_disk_i() == self.journal_caching_disk_i(),
    {
        self.journal_caching_disk_i_preserved_by_cache_access_outside_journal_projection(
            post,
            reads,
            writes,
        );
        assert(self.disk_model_agrees_on_journal_owned_au_ranges(post));
        assert(self.cache_model_agrees_on_journal_owned_au_ranges(post));
        self.inv_preserved_by_disk_model_agreement_on_journal_owned_au_ranges(post);
    }

    pub proof fn journal_interpretation_unchanged_by_same_projection(
        self,
        post: Self,
    )
        requires
            self.same_except_cache_and_disk(post),
            self.persistent_journal_i() == post.persistent_journal_i(),
            self.journal_caching_disk_i() == post.journal_caching_disk_i(),
        ensures
            self.i() == post.i(),
    {
        assert(self.superblock_loaded() == post.superblock_loaded());
        assert(self.journal_caching_disk_state_i() == post.journal_caching_disk_state_i());
        assert(self.ephemeral_journal_i() == post.ephemeral_journal_i());
        assert(self.frozen_journal_metadata_i() == post.frozen_journal_metadata_i());
        assert(self.i() == post.i());
    }

    pub proof fn unchanged_by_same_cache_and_disk_content(
        self,
        post: Self,
    )
        requires
            inv(self),
            self.same_except_cache_and_disk(post),
            post.cache == self.cache,
            post.disk.content == self.disk.content,
            post.disk.inv(),
        ensures
            post.i() == self.i(),
            inv(post),
    {
        assert(post.superblock_loaded() == self.superblock_loaded());
        assert(post.persistent_superblock_image_i()
            == self.persistent_superblock_image_i()) by {
            if self.persistent_image is Some {
                assert(post.persistent_image == self.persistent_image);
            } else {
                assert(post.persistent_image is None);
                assert(async_disk_superblock_raw_i(post.disk.content)
                    == async_disk_superblock_raw_i(self.disk.content));
            }
        }

        assert(post.journal_projection_aus() =~= self.journal_projection_aus()) by {
            if self.journal.ready() {
                assert(post.journal == self.journal);
            } else {
                assert(post.persistent_superblock_image_i()
                    == self.persistent_superblock_image_i());
                assert(post.disk.content == self.disk.content);
            }
        }

        assert(post.persistent_journal_image_i() == self.persistent_journal_image_i()) by {
            let image = self.persistent_superblock_image_i();
            assert(post.persistent_superblock_image_i() == image);
            assert(post.journal_image_projection_aus_i(image)
                =~= self.journal_image_projection_aus_i(image));
            assert_maps_equal!(
                post.persistent_journal_image_i().persistent,
                self.persistent_journal_image_i().persistent,
                addr => {
                    if post.persistent_journal_image_i().persistent.contains_key(addr) {
                        assert(self.persistent_journal_image_i().persistent.contains_key(addr));
                    }
                    if self.persistent_journal_image_i().persistent.contains_key(addr) {
                        assert(post.persistent_journal_image_i().persistent.contains_key(addr));
                    }
                }
            );
        }
        assert(post.persistent_journal_i() == self.persistent_journal_i());

        assert(post.journal_caching_disk_i() == self.journal_caching_disk_i()) by {
            assert(post.journal_projection_aus() =~= self.journal_projection_aus());
            assert_maps_equal!(
                post.journal_caching_disk_i().cache,
                self.journal_caching_disk_i().cache,
                addr => {}
            );
            assert_maps_equal!(
                post.journal_caching_disk_i().status,
                self.journal_caching_disk_i().status,
                addr => {}
            );
            assert_maps_equal!(
                post.journal_caching_disk_i().persistent,
                self.journal_caching_disk_i().persistent,
                addr => {
                    if post.journal_caching_disk_i().persistent.contains_key(addr) {
                        assert(self.journal_caching_disk_i().persistent.contains_key(addr));
                    }
                    if self.journal_caching_disk_i().persistent.contains_key(addr) {
                        assert(post.journal_caching_disk_i().persistent.contains_key(addr));
                    }
                }
            );
        }
        self.journal_interpretation_unchanged_by_same_projection(post);
        assert(post.i() == self.i());

        assert(post.inv()) by {
            assert(post.journal.wf());
            assert(async_disk_superblock_page_wf(post.disk.content));
            assert(post.persistent_superblock_image_i().wf());
            assert(post.cache.inv());
            assert(post.disk.inv());
            assert(post.journal_caching_disk_i().inv());
            if !post.superblock_loaded() {
                assert(!self.superblock_loaded());
                assert(post.journal == AtomicJournalState::State::empty());
                assert(post.in_flight is None);
                assert(post.in_flight_image is None);
            }
        }
        assert(post.semantic_inv()) by {
            assert(self.semantic_inv());
            assert(post.i() == self.i());
        }
        assert(inv(post));
    }

    pub proof fn loaded_caching_disk_internal_refines_journal_internal(
        self,
        post: Self,
    )
        requires
            self.same_except_cache_and_disk(post),
            self.superblock_loaded(),
            CachingDisk::State::next(
                self.journal_caching_disk_i(),
                post.journal_caching_disk_i(),
                CachingDisk::Label::Internal{},
            ),
        ensures
            CrashAwareCachingDiskJournal::State::next(
                self.i(),
                post.i(),
                CrashAwareCachingDiskJournal::Label::Internal,
            ),
    {
        assert(post.superblock_loaded());
        assert(self.persistent_journal_i() == post.persistent_journal_i());
        assert(self.frozen_journal_metadata_i() == post.frozen_journal_metadata_i());
        assert(self.journal_caching_disk_state_i().journal
            == post.journal_caching_disk_state_i().journal);
        assert(self.journal_caching_disk_state_i().mini_allocator
            == post.journal_caching_disk_state_i().mini_allocator);
        assert(self.journal_caching_disk_state_i().au_page_bounds
            == post.journal_caching_disk_state_i().au_page_bounds);

        assert(CachingDiskJournal::State::caching_disk_internal(
            self.journal_caching_disk_state_i(),
            post.journal_caching_disk_state_i(),
            CachingDiskJournal::Label::Internal,
            post.journal_caching_disk_i(),
        )) by {
            reveal(CachingDiskJournal::State::caching_disk_internal);
        }
        assert(CachingDiskJournal::State::next_by(
            self.journal_caching_disk_state_i(),
            post.journal_caching_disk_state_i(),
            CachingDiskJournal::Label::Internal,
            CachingDiskJournal::Step::caching_disk_internal(post.journal_caching_disk_i()),
        )) by {
            reveal(CachingDiskJournal::State::next_by);
        }
        reveal(CachingDiskJournal::State::next);

        assert(CrashAwareCachingDiskJournal::State::internal(
            self.i(),
            post.i(),
            CrashAwareCachingDiskJournal::Label::Internal,
            post.journal_caching_disk_state_i(),
        )) by {
            reveal(CrashAwareCachingDiskJournal::State::internal);
        }
        assert(CrashAwareCachingDiskJournal::State::next_by(
            self.i(),
            post.i(),
            CrashAwareCachingDiskJournal::Label::Internal,
            CrashAwareCachingDiskJournal::Step::internal(post.journal_caching_disk_state_i()),
        )) by {
            reveal(CrashAwareCachingDiskJournal::State::next_by);
        }
        reveal(CrashAwareCachingDiskJournal::State::next);
    }

    pub proof fn loaded_cache_disk_ops_begin_refines_journal_internal(
        self,
        post: Self,
        requests: Set<DiskRequest>,
    )
        requires
            inv(self),
            self.same_except_cache_and_disk(post),
            self.superblock_loaded(),
            post.disk.content == self.disk.content,
            post.disk.inv(),
            Cache::State::next(
                self.cache,
                post.cache,
                Cache::Label::DiskOps{requests, responses: Map::empty()},
            ),
        ensures
            CrashAwareCachingDiskJournal::State::next(
                self.i(),
                post.i(),
                CrashAwareCachingDiskJournal::Label::Internal,
            ),
            inv(post),
    {
        let aus = self.journal_projection_aus();
        let projected_post = adapter_caching_disk_i(post.cache, self.disk, aus);
        cache_disk_ops_begin_refines_caching_disk_internal(
            self.cache,
            post.cache,
            self.disk,
            aus,
            requests,
        );
        assert(post.journal_projection_aus() =~= aus);
        assert(post.journal_caching_disk_i() == projected_post) by {
            assert_maps_equal!(
                post.journal_caching_disk_i().cache,
                projected_post.cache,
                addr => {}
            );
            assert_maps_equal!(
                post.journal_caching_disk_i().status,
                projected_post.status,
                addr => {}
            );
            assert_maps_equal!(
                post.journal_caching_disk_i().persistent,
                projected_post.persistent,
                addr => {
                    if post.journal_caching_disk_i().persistent.contains_key(addr) {
                        assert(post.disk.content.contains_key(addr));
                        assert(post.disk.content[addr] == self.disk.content[addr]);
                    }
                    if projected_post.persistent.contains_key(addr) {
                        assert(self.disk.content.contains_key(addr));
                        assert(post.disk.content.contains_key(addr));
                        assert(post.disk.content[addr] == self.disk.content[addr]);
                    }
                }
            );
        }
        assert(CachingDisk::State::next(
            self.journal_caching_disk_i(),
            post.journal_caching_disk_i(),
            CachingDisk::Label::Internal{},
        ));
        self.loaded_caching_disk_internal_refines_journal_internal(post);
        CachingDisk::State::inv_next(
            self.journal_caching_disk_i(),
            post.journal_caching_disk_i(),
            CachingDisk::Label::Internal{},
        );
        assert(post.inv()) by {
            assert(post.journal.wf());
            assert(async_disk_superblock_page_wf(post.disk.content));
            assert(post.persistent_superblock_image_i() == self.persistent_superblock_image_i());
            assert(post.persistent_superblock_image_i().wf());
            assert(post.cache.inv()) by {
                Cache::State::inv_next(
                    self.cache,
                    post.cache,
                    Cache::Label::DiskOps{requests, responses: Map::empty()},
                );
            }
            assert(post.journal_caching_disk_i().inv());
        }
        self.i().next_refines(post.i(), CrashAwareCachingDiskJournal::Label::Internal);
        assert(post.semantic_inv());
        assert(inv(post));
    }

    pub proof fn loaded_cache_disk_ops_end_refines_journal_internal(
        self,
        post: Self,
        responses: Map<Address, DiskResponse>,
    )
        requires
            inv(self),
            self.same_except_cache_and_disk(post),
            self.superblock_loaded(),
            post.disk.content == self.disk.content,
            post.disk.inv(),
            Cache::State::next(
                self.cache,
                post.cache,
                Cache::Label::DiskOps{requests: Set::empty(), responses},
            ),
            forall |addr: Address| {
                &&& #[trigger] responses.contains_key(addr)
                &&& addresses_in_aus(self.journal_projection_aus()).contains(addr)
            } ==> {
                &&& self.disk.content.contains_key(addr)
                &&& responses[addr] is ReadResp ==> responses[addr]->data
                    == self.disk.content[addr]
                &&& responses[addr] is WriteResp ==> {
                    &&& cache_filled_addr(self.cache, addr)
                    &&& self.disk.content[addr] == cache_filled_page(self.cache, addr)
                }
            },
        ensures
            CrashAwareCachingDiskJournal::State::next(
                self.i(),
                post.i(),
                CrashAwareCachingDiskJournal::Label::Internal,
            ),
            inv(post),
    {
        let aus = self.journal_projection_aus();
        let projected_post = adapter_caching_disk_i(post.cache, self.disk, aus);
        cache_disk_ops_end_refines_caching_disk_internal(
            self.cache,
            post.cache,
            self.disk,
            aus,
            responses,
        );
        assert(post.journal_projection_aus() =~= aus);
        assert(post.journal_caching_disk_i() == projected_post) by {
            assert_maps_equal!(
                post.journal_caching_disk_i().cache,
                projected_post.cache,
                addr => {}
            );
            assert_maps_equal!(
                post.journal_caching_disk_i().status,
                projected_post.status,
                addr => {}
            );
            assert_maps_equal!(
                post.journal_caching_disk_i().persistent,
                projected_post.persistent,
                addr => {
                    if post.journal_caching_disk_i().persistent.contains_key(addr) {
                        assert(post.disk.content.contains_key(addr));
                        assert(post.disk.content[addr] == self.disk.content[addr]);
                    }
                    if projected_post.persistent.contains_key(addr) {
                        assert(self.disk.content.contains_key(addr));
                        assert(post.disk.content.contains_key(addr));
                        assert(post.disk.content[addr] == self.disk.content[addr]);
                    }
                }
            );
        }
        assert(CachingDisk::State::next(
            self.journal_caching_disk_i(),
            post.journal_caching_disk_i(),
            CachingDisk::Label::Internal{},
        ));
        self.loaded_caching_disk_internal_refines_journal_internal(post);
        CachingDisk::State::inv_next(
            self.journal_caching_disk_i(),
            post.journal_caching_disk_i(),
            CachingDisk::Label::Internal{},
        );
        assert(post.inv()) by {
            assert(post.journal.wf());
            assert(async_disk_superblock_page_wf(post.disk.content));
            assert(post.persistent_superblock_image_i() == self.persistent_superblock_image_i());
            assert(post.persistent_superblock_image_i().wf());
            assert(post.cache.inv()) by {
                Cache::State::inv_next(
                    self.cache,
                    post.cache,
                    Cache::Label::DiskOps{requests: Set::empty(), responses},
                );
            }
            assert(post.journal_caching_disk_i().inv());
        }
        self.i().next_refines(post.i(), CrashAwareCachingDiskJournal::Label::Internal);
        assert(post.semantic_inv());
        assert(inv(post));
    }
}

pub open spec fn unified_cache_journal_i(
    src: UnifiedCacheJournalSource,
) -> CrashAwareCachingDiskJournal::State
{
    src.i()
}

pub open spec fn unified_cache_journal_i_lbl(
    lbl: AtomicJournalState::Label,
) -> CrashAwareCachingDiskJournal::Label
{
    match lbl {
        AtomicJournalState::Label::Put{messages} => {
            CrashAwareCachingDiskJournal::Label::Put{records: messages}
        },
        AtomicJournalState::Label::LoadIndex{discovered_aus, ..} => {
            CrashAwareCachingDiskJournal::Label::LoadIndex{discovered_aus}
        },
        AtomicJournalState::Label::ReadForRecovery{messages, ..} => {
            CrashAwareCachingDiskJournal::Label::ReadForRecovery{records: messages}
        },
        AtomicJournalState::Label::JournalMarshal{..} => {
            CrashAwareCachingDiskJournal::Label::Internal
        },
        AtomicJournalState::Label::ObserveCleanAUs{aus} => {
            CrashAwareCachingDiskJournal::Label::ObserveCleanAUs{aus}
        },
        AtomicJournalState::Label::FillAUs{aus} => {
            CrashAwareCachingDiskJournal::Label::InternalAlloc{
                allocs: aus,
                deallocs: Set::empty(),
                prune_aus: Set::empty(),
            }
        },
        AtomicJournalState::Label::QueryEndLsn{end_lsn} => {
            CrashAwareCachingDiskJournal::Label::QueryEndLsn{end_lsn}
        },
        AtomicJournalState::Label::CommitStart{snapshot, seq_end, ..} => {
            CrashAwareCachingDiskJournal::Label::CommitStart{
                new_boundary_lsn: snapshot.boundary_lsn,
                snapshot,
                seq_end,
            }
        },
        AtomicJournalState::Label::CommitPrepared => {
            CrashAwareCachingDiskJournal::Label::CommitPrepared
        },
        AtomicJournalState::Label::CommitComplete{require_end, discarded_aus} => {
            CrashAwareCachingDiskJournal::Label::CommitComplete{
                require_end,
                discarded: discarded_aus,
            }
        },
    }
}

pub open spec fn inv(src: UnifiedCacheJournalSource) -> bool
{
    &&& src.inv()
    &&& src.semantic_inv()
}

pub open spec fn init_shared_facts(src: UnifiedCacheJournalSource) -> bool
{
    &&& async_disk_superblock_page_wf(src.disk.content)
    &&& src.persistent_superblock_image_i() == empty_abstract_superblock_image()
    &&& src.cache.inv()
    &&& src.disk.inv()
}

pub proof fn init_refines(pre: SystemModel::State<UnifiedCacheProgramModel>)
    requires
        SystemModel::State::initialize(pre, pre.program, pre.disk),
        init_shared_facts(unified_cache_journal_source(pre)),
    ensures
        CrashAwareCachingDiskJournal::State::init(
            unified_cache_journal_i(unified_cache_journal_source(pre)),
        ),
        inv(unified_cache_journal_source(pre)),
{
    reveal(SystemModel::State::initialize);
    assert(UnifiedCacheProgramModel::is_mkfs(pre.disk));
    assert(UnifiedCacheProgramModel::init(pre.program));

    reveal(UnifiedCacheSystem::State::init);
    reveal(UnifiedCacheSystem::State::init_by);
    let config = choose |config: UnifiedCacheSystem::Config|
        UnifiedCacheSystem::State::init_by(pre.program.state, config);

    match config {
        UnifiedCacheSystem::Config::initialize(cache_slots, free_aus) => {
            assert(UnifiedCacheSystem::State::initialize(
                pre.program.state,
                cache_slots,
                free_aus,
            )) by {
                reveal(UnifiedCacheSystem::State::initialize);
            }
            reveal(UnifiedCacheSystem::State::initialize);

            let src = unified_cache_journal_source(pre);
            let dst = unified_cache_journal_i(src);

            assert(src.journal_projection_aus() =~= Set::<AU>::empty()) by {
                let image = src.persistent_superblock_image_i();
                let tj = UnifiedCacheJournalSource::journal_image_tj_i(
                    src.disk.content,
                    image,
                );
                assert forall |au: AU| #[trigger] src.journal_projection_aus().contains(au)
                    implies false by {
                    assert(src.journal_image_projection_aus_i(image).contains(au));
                    assert(tj.disk_view.loose_build_lsn_au_index_au_walk(
                        tj.freshest_rec,
                        image.journal_snapshot.first(),
                    ).values().contains(au));
                    assert(false);
                }
            }

            assert(async_disk_superblock_page_wf(src.disk.content));
            assert(src.persistent_superblock_image_i() == empty_abstract_superblock_image());
            assert(src.persistent_superblock_image_i().wf());
            assert(src.cache.inv());
            assert(src.disk.inv());

            assert(src.journal_caching_disk_i().cache == Map::<Address, RawPage>::empty()) by {
                assert_maps_equal!(
                    src.journal_caching_disk_i().cache,
                    Map::<Address, RawPage>::empty(),
                    addr => {
                        assert(!addresses_in_aus(src.journal_projection_aus()).contains(addr));
                    }
                );
            }
            assert(src.journal_caching_disk_i().persistent == Map::<Address, RawPage>::empty()) by {
                assert_maps_equal!(
                    src.journal_caching_disk_i().persistent,
                    Map::<Address, RawPage>::empty(),
                    addr => {
                        assert(!addresses_in_aus(src.journal_projection_aus()).contains(addr));
                    }
                );
            }
            assert(src.journal_caching_disk_i().status == Map::<Address, PageStatus>::empty()) by {
                assert_maps_equal!(
                    src.journal_caching_disk_i().status,
                    Map::<Address, PageStatus>::empty(),
                    addr => {
                        assert(!addresses_in_aus(src.journal_projection_aus()).contains(addr));
                    }
                );
            }
            assert(src.journal_caching_disk_i().inv());

            assert(src.persistent_journal_image_i() == CachingDiskJournalImage::empty()) by {
                assert(src.persistent_journal_image_i().persistent == Map::<Address, RawPage>::empty());
                assert(src.persistent_journal_image_i().snapshot
                    == empty_abstract_superblock_image().journal_snapshot);
                assert(src.persistent_journal_image_i().seq_end == 0);
            }

            assert(dst.persistent is Image);
            assert(dst.persistent->image == CachingDiskJournalImage::empty());
            assert(dst.ephemeral is Unknown);
            assert(dst.frozen is None);
            assert(dst.prepared == false);
            assert(CrashAwareCachingDiskJournal::State::initialize(dst)) by {
                reveal(CrashAwareCachingDiskJournal::State::initialize);
            }
            assert(CrashAwareCachingDiskJournal::State::init(dst)) by {
                reveal(CrashAwareCachingDiskJournal::State::init);
                reveal(CrashAwareCachingDiskJournal::State::init_by);
                assert(CrashAwareCachingDiskJournal::State::init_by(
                    dst,
                    CrashAwareCachingDiskJournal::Config::initialize(),
                ));
            }
            CrashAwareCachingDiskJournal::State::initialize_inductive(dst);
            dst.init_refines();
            assert(src.semantic_inv());
            assert(src.inv());
            assert(inv(src));
        },
        UnifiedCacheSystem::Config::dummy_to_use_type_params(_) => {
            assert(false);
        },
    }
}

pub proof fn query_end_lsn_refines(
    pre: UnifiedCacheJournalSource,
    post: UnifiedCacheJournalSource,
    end_lsn: nat,
)
    requires
        inv(pre),
        AtomicJournalState::State::next(
            pre.journal,
            post.journal,
            AtomicJournalState::Label::QueryEndLsn{end_lsn},
        ),
        pre.same_except_cache_and_disk(post),
        post.cache == pre.cache,
        post.disk == pre.disk,
    ensures
        CrashAwareCachingDiskJournal::State::next(
            unified_cache_journal_i(pre),
            unified_cache_journal_i(post),
            CrashAwareCachingDiskJournal::Label::QueryEndLsn{end_lsn},
        ),
        inv(post),
{
    let src = pre;
    let dst = post;
    let atomic_lbl = AtomicJournalState::Label::QueryEndLsn{end_lsn};

    assert(dst == src);

    reveal(AtomicJournalState::State::next);
    reveal(AtomicJournalState::State::next_by);
    let atomic_step = choose |step: AtomicJournalState::Step|
        AtomicJournalState::State::next_by(src.journal, dst.journal, atomic_lbl, step);
    match atomic_step {
        AtomicJournalState::Step::query_end_lsn() => {
            assert(AtomicJournalState::State::query_end_lsn(
                src.journal,
                dst.journal,
                atomic_lbl,
            ));
            let cj_lbl = CachingDiskJournal::Label::QueryEndLsn{end_lsn};
            assert(CachedJournal::State::next(
                src.journal.journal,
                src.journal.journal,
                CachedJournal::Label::QueryEndLsn{end_lsn},
            ));
            assert(src.superblock_loaded()) by {
                if !src.superblock_loaded() {
                    assert(src.journal == AtomicJournalState::State::empty());
                    assert(src.journal.journal.status is None);
                    reveal(CachedJournal::State::next);
                    reveal(CachedJournal::State::next_by);
                    let cj_step = choose |step: CachedJournal::Step|
                        CachedJournal::State::next_by(
                            src.journal.journal,
                            src.journal.journal,
                            CachedJournal::Label::QueryEndLsn{end_lsn},
                            step,
                        );
                    match cj_step {
                        CachedJournal::Step::query_end_lsn() => {
                            assert(CachedJournal::State::query_end_lsn(
                                src.journal.journal,
                                src.journal.journal,
                                CachedJournal::Label::QueryEndLsn{end_lsn},
                            ));
                        },
                        _ => {
                            assert(false);
                        },
                    }
                    assert(false);
                }
            }

            assert(CachingDiskJournal::State::query_end_lsn(
                src.journal_caching_disk_state_i(),
                src.journal_caching_disk_state_i(),
                cj_lbl,
            ));
            assert(CachingDiskJournal::State::next_by(
                src.journal_caching_disk_state_i(),
                src.journal_caching_disk_state_i(),
                cj_lbl,
                CachingDiskJournal::Step::query_end_lsn(),
            )) by {
                reveal(CachingDiskJournal::State::next_by);
            }
            reveal(CachingDiskJournal::State::next);

            let lbl = CrashAwareCachingDiskJournal::Label::QueryEndLsn{end_lsn};
            assert(CrashAwareCachingDiskJournal::State::query_end_lsn(
                src.i(),
                dst.i(),
                lbl,
            ));
            assert(CrashAwareCachingDiskJournal::State::next_by(
                src.i(),
                dst.i(),
                lbl,
                CrashAwareCachingDiskJournal::Step::query_end_lsn(),
            )) by {
                reveal(CrashAwareCachingDiskJournal::State::next_by);
            }
            reveal(CrashAwareCachingDiskJournal::State::next);
        },
        _ => {
            assert(false);
        },
    }

    assert(src.inv());
    assert(src.semantic_inv());
    assert(dst.inv());
    assert(dst.semantic_inv());
    assert(inv(dst));
}

pub proof fn query_end_lsn_self_refines(
    src: UnifiedCacheJournalSource,
    end_lsn: nat,
)
    requires
        inv(src),
        src.superblock_loaded(),
        src.journal.ready(),
        end_lsn == src.journal.journal.seq_end(),
    ensures
        CrashAwareCachingDiskJournal::State::next(
            unified_cache_journal_i(src),
            unified_cache_journal_i(src),
            CrashAwareCachingDiskJournal::Label::QueryEndLsn{end_lsn},
        ),
        inv(src),
{
    let atomic_lbl = AtomicJournalState::Label::QueryEndLsn{end_lsn};
    let cached_lbl = CachedJournal::Label::QueryEndLsn{end_lsn};

    assert(CachedJournal::State::next(
        src.journal.journal,
        src.journal.journal,
        cached_lbl,
    )) by {
        assert(CachedJournal::State::next_by(
            src.journal.journal,
            src.journal.journal,
            cached_lbl,
            CachedJournal::Step::query_end_lsn(),
        )) by {
            reveal(CachedJournal::State::next_by);
            reveal(CachedJournal::State::query_end_lsn);
        }
        reveal(CachedJournal::State::next);
    }
    assert(AtomicJournalState::State::next(src.journal, src.journal, atomic_lbl)) by {
        assert(AtomicJournalState::State::next_by(
            src.journal,
            src.journal,
            atomic_lbl,
            AtomicJournalState::Step::query_end_lsn(),
        )) by {
            reveal(AtomicJournalState::State::next_by);
            reveal(AtomicJournalState::State::query_end_lsn);
        }
        reveal(AtomicJournalState::State::next);
    }
    assert(src.same_except_cache_and_disk(src));
    query_end_lsn_refines(src, src, end_lsn);
}

pub proof fn query_lsn_persistence_self_refines(
    src: UnifiedCacheJournalSource,
    sync_lsn: nat,
)
    requires
        inv(src),
        sync_lsn <= unified_cache_journal_i(src).persistent.metadata().seq_end,
    ensures
        CrashAwareCachingDiskJournal::State::next(
            unified_cache_journal_i(src),
            unified_cache_journal_i(src),
            CrashAwareCachingDiskJournal::Label::QueryLsnPersistence{sync_lsn},
        ),
        inv(src),
{
    let lbl = CrashAwareCachingDiskJournal::Label::QueryLsnPersistence{sync_lsn};
    assert(CrashAwareCachingDiskJournal::State::query_lsn_persistence(
        src.i(),
        src.i(),
        lbl,
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::query_lsn_persistence);
    }
    assert(CrashAwareCachingDiskJournal::State::next_by(
        src.i(),
        src.i(),
        lbl,
        CrashAwareCachingDiskJournal::Step::query_lsn_persistence(),
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::next_by);
    }
    reveal(CrashAwareCachingDiskJournal::State::next);
}

pub proof fn recovery_complete_refines_query_end_lsn(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
)
    requires
        inv(unified_cache_journal_source(pre)),
        UnifiedCacheSystem::State::recovery_complete(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Internal,
        ),
        post.disk == pre.disk,
    ensures
        CrashAwareCachingDiskJournal::State::next(
            unified_cache_journal_i(unified_cache_journal_source(pre)),
            unified_cache_journal_i(unified_cache_journal_source(post)),
            CrashAwareCachingDiskJournal::Label::QueryEndLsn{
                end_lsn: pre.program.state.branch.seq_end(),
            },
        ),
        inv(unified_cache_journal_source(post)),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let end_lsn = pre_state.branch.seq_end();
    let atomic_lbl = AtomicJournalState::Label::QueryEndLsn{end_lsn};

    assert(UnifiedCacheSystem::State::recovery_complete(
        pre_state,
        post_state,
        UnifiedCacheSystem::Label::Internal,
    ));
    assert(AtomicJournalState::State::next(pre_state.journal, pre_state.journal, atomic_lbl));
    assert(post_state == UnifiedCacheSystem::State{
        recovery_state: post_state.recovery_state,
        ..pre_state
    });

    let src = unified_cache_journal_source(pre);
    let dst = unified_cache_journal_source(post);
    assert(src.same_except_cache_and_disk(dst));
    assert(dst.cache == src.cache);
    assert(dst.disk == src.disk);
    query_end_lsn_refines(src, dst, end_lsn);
}

pub proof fn put_preserves_projection_aus(
    pre: UnifiedCacheJournalSource,
    post: UnifiedCacheJournalSource,
    records: MsgHistory,
)
    requires
        pre.superblock_loaded(),
        pre.journal.ready(),
        post.persistent_image == pre.persistent_image,
        AtomicJournalState::State::next(
            pre.journal,
            post.journal,
            AtomicJournalState::Label::Put{messages: records},
        ),
    ensures
        post.superblock_loaded(),
        post.journal.ready(),
        post.journal_projection_aus() =~= pre.journal_projection_aus(),
        post.journal.in_flight == pre.journal.in_flight,
        post.journal.prepared == pre.journal.prepared,
        post.journal.persistent_seq_end == pre.journal.persistent_seq_end,
        post.journal.journal.seq_end() == records.seq_end,
{
    let atomic_lbl = AtomicJournalState::Label::Put{messages: records};
    reveal(AtomicJournalState::State::next);
    reveal(AtomicJournalState::State::next_by);
    let atomic_step = choose |step: AtomicJournalState::Step|
        AtomicJournalState::State::next_by(pre.journal, post.journal, atomic_lbl, step);
    match atomic_step {
        AtomicJournalState::Step::put(new_journal) => {
            assert(AtomicJournalState::State::put(
                pre.journal,
                post.journal,
                atomic_lbl,
                new_journal,
            )) by {
                reveal(AtomicJournalState::State::put);
            }
            assert(post.journal.journal == new_journal);
            assert(post.journal.mini_allocator == pre.journal.mini_allocator);
            assert(post.journal.au_page_bounds == pre.journal.au_page_bounds);
            assert(post.journal.persistent_seq_end == pre.journal.persistent_seq_end);
            assert(post.journal.in_flight == pre.journal.in_flight);
            assert(post.journal.prepared == pre.journal.prepared);
            assert(CachedJournal::State::next(
                pre.journal.journal,
                post.journal.journal,
                CachedJournal::Label::Put{messages: records},
            ));
            CachedJournal::State::put_effect(
                pre.journal.journal,
                post.journal.journal,
                records,
            );
            assert(post.journal.ready());
            assert(post.journal.journal.seq_end() == records.seq_end);
            assert(post.journal_projection_aus() =~= pre.journal_projection_aus());
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn put_refines(
    pre: UnifiedCacheJournalSource,
    post: UnifiedCacheJournalSource,
    records: MsgHistory,
)
    requires
        inv(pre),
        pre.superblock_loaded(),
        post.cache.inv(),
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.in_flight == pre.in_flight,
        post.in_flight_image == pre.in_flight_image,
        post.journal_caching_disk_i() == pre.journal_caching_disk_i(),
        AtomicJournalState::State::next(
            pre.journal,
            post.journal,
            AtomicJournalState::Label::Put{messages: records},
        ),
    ensures
        CrashAwareCachingDiskJournal::State::next(
            unified_cache_journal_i(pre),
            unified_cache_journal_i(post),
            CrashAwareCachingDiskJournal::Label::Put{records},
        ),
        inv(post),
{
    let atomic_lbl = AtomicJournalState::Label::Put{messages: records};
    reveal(AtomicJournalState::State::next);
    reveal(AtomicJournalState::State::next_by);
    let atomic_step = choose |step: AtomicJournalState::Step|
        AtomicJournalState::State::next_by(pre.journal, post.journal, atomic_lbl, step);
    match atomic_step {
        AtomicJournalState::Step::put(new_journal) => {
            assert(AtomicJournalState::State::put(
                pre.journal,
                post.journal,
                atomic_lbl,
                new_journal,
            )) by {
                reveal(AtomicJournalState::State::put);
            }
            assert(post.journal.journal == new_journal);
            assert(post.journal.mini_allocator == pre.journal.mini_allocator);
            assert(post.journal.au_page_bounds == pre.journal.au_page_bounds);
            assert(post.journal.persistent_seq_end == pre.journal.persistent_seq_end);
            assert(post.journal.in_flight == pre.journal.in_flight);
            assert(post.journal.prepared == pre.journal.prepared);
        },
        _ => {
            assert(false);
        },
    }

    AtomicJournalState::State::wf_next(pre.journal, post.journal, atomic_lbl);
    assert(post.superblock_loaded());
    assert(post.persistent_superblock_image_i() == pre.persistent_superblock_image_i());
    assert(post.journal_caching_disk_state_i().disk == pre.journal_caching_disk_state_i().disk);
    assert(post.journal_caching_disk_state_i().mini_allocator
        == pre.journal_caching_disk_state_i().mini_allocator);
    assert(post.journal_caching_disk_state_i().au_page_bounds
        == pre.journal_caching_disk_state_i().au_page_bounds);

    let cj_lbl = CachingDiskJournal::Label::Put{messages: records};
    assert(CachingDiskJournal::State::put(
        pre.journal_caching_disk_state_i(),
        post.journal_caching_disk_state_i(),
        cj_lbl,
        post.journal.journal,
    )) by {
        reveal(CachingDiskJournal::State::put);
    }
    assert(CachingDiskJournal::State::next_by(
        pre.journal_caching_disk_state_i(),
        post.journal_caching_disk_state_i(),
        cj_lbl,
        CachingDiskJournal::Step::put(post.journal.journal),
    )) by {
        reveal(CachingDiskJournal::State::next_by);
    }
    reveal(CachingDiskJournal::State::next);

    let src = unified_cache_journal_i(pre);
    let dst = unified_cache_journal_i(post);
    let lbl = CrashAwareCachingDiskJournal::Label::Put{records};
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(CrashAwareCachingDiskJournal::State::put(
        src,
        dst,
        lbl,
        post.journal_caching_disk_state_i(),
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::put);
    }
    assert(CrashAwareCachingDiskJournal::State::next_by(
        src,
        dst,
        lbl,
        CrashAwareCachingDiskJournal::Step::put(post.journal_caching_disk_state_i()),
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::next_by);
    }
    reveal(CrashAwareCachingDiskJournal::State::next);
    src.next_refines(dst, lbl);

    assert(post.inv()) by {
        assert(post.journal.wf());
        assert(async_disk_superblock_page_wf(post.disk.content));
        assert(post.persistent_superblock_image_i().wf());
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.journal_caching_disk_i().inv());
        assert(post.in_flight is Some <==> post.journal.in_flight is Some);
        assert(post.in_flight is Some <==> post.in_flight_image is Some);
    }
    assert(post.semantic_inv());
    assert(inv(post));
}

pub proof fn next_refines(
    pre: UnifiedCacheJournalSource,
    post: UnifiedCacheJournalSource,
    lbl: AtomicJournalState::Label,
)
    requires
        AtomicJournalState::State::next(pre.journal, post.journal, lbl),
        inv(pre),
    ensures
        CrashAwareCachingDiskJournal::State::next(
            unified_cache_journal_i(pre),
            unified_cache_journal_i(post),
            unified_cache_journal_i_lbl(lbl),
        ),
        inv(post),
{
    match lbl {
        AtomicJournalState::Label::Put{..}
        | AtomicJournalState::Label::LoadIndex{..}
        | AtomicJournalState::Label::ReadForRecovery{..}
        | AtomicJournalState::Label::JournalMarshal{..}
        | AtomicJournalState::Label::ObserveCleanAUs{..}
        | AtomicJournalState::Label::FillAUs{..}
        | AtomicJournalState::Label::QueryEndLsn{..}
        | AtomicJournalState::Label::CommitStart{..}
        | AtomicJournalState::Label::CommitPrepared
        | AtomicJournalState::Label::CommitComplete{..} => {
            assume(false);
        },
    }
}

} // verus!
