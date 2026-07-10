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
use crate::abstract_system::StampedMap_v::LSN;
use crate::disk::GenericDisk_v::{Address, AU};
use crate::implementation::AbstractSuperblock_v::{
    AbstractSuperblockImage, abstract_superblock_raw_wf, empty_abstract_superblock_image,
    parse_abstract_superblock,
};
use crate::implementation::AtomicJournalState_v::AtomicJournalState;
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachedJournal_v::{
    au_walk_addrs_in_entries_subset, CachedJournal, JournalSnapshot,
};
use crate::implementation::CachingDiskAdapterRefinement_v::{
	    cache_filled_addr, cache_filled_page,
	    caching_disk_i as adapter_caching_disk_i, caching_disk_i_equal_by_aus_ext,
        backed_raw_cache_entry_in_caching_disk_i_visible,
        caching_disk_i_equal_from_raw_projection_agreement,
        project_cache_pages, project_cache_status, project_persistent,
	    cache_access_refines_caching_disk_access,
	    cache_evictable_refines_observe_clean_aus,
	    cache_internal_refines_caching_disk_internal,
	    cache_disk_ops_begin_refines_caching_disk_internal,
	    cache_disk_ops_end_refines_caching_disk_internal,
	    ownership_projection_forget_refines,
	    projected_cache_access_outside_aus_unchanged, projected_cache_read_only_access_unchanged,
	};
use crate::implementation::CachingDisk_v::{addresses_in_aus, status_map, CachingDisk, PageStatus};
use crate::implementation::CachingDiskJournal_v::{CachingDiskJournal, cj_lsn_au_index};
use crate::implementation::CrashAwareCachingDiskJournal_v::{
    caching_disk_journal_accessible_aus,
    CachingDiskJournalFrozenMetadata, CachingDiskJournalImage, CrashAwareCachingDiskJournal,
    EphemeralCachingDiskJournal, PersistentCachingDiskJournal,
};
use crate::implementation::CrashAwareCachingDiskJournalRefinement_v::*;
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::implementation::JournalTypes_v::{to_journal_records, to_journal_records_restrict};
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
    pub in_flight: Option<AbstractSuperblockImage>,
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
            in_flight: state.sync_image(),
            in_flight_image: state.sync_image(),
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
        let tj = Self::journal_image_tj_i(self.disk.content, image);
        tj.disk_view.loose_build_lsn_au_index_au_walk(
            tj.freshest_rec,
            image.journal_snapshot.first(),
        ).values()
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

    pub open spec fn caching_disk_i_for_aus(self, aus: Set<AU>) -> CachingDisk::State
    {
        adapter_caching_disk_i(self.cache, self.disk, aus)
    }

    pub open spec fn journal_caching_disk_i(self) -> CachingDisk::State
    {
        self.caching_disk_i_for_aus(self.journal_projection_aus())
    }

    pub open spec fn journal_fill_aus_shared_projection_inv(self, aus: Set<AU>) -> bool
    {
        let disk = self.caching_disk_i_for_aus(self.journal_projection_aus() + aus);
        &&& disk.inv()
        &&& disk.cache.dom() <= Set::new(|addr: Address| addr.wf())
        &&& disk.persistent.dom() <= Set::new(|addr: Address| addr.wf())
    }

    pub open spec fn journal_caching_disk_state_i(self) -> CachingDiskJournal::State
    {
        CachingDiskJournal::State{
            journal: self.journal.journal,
            disk: self.journal_caching_disk_i(),
            mini_allocator: self.journal.mini_allocator,
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
        &&& self.superblock_loaded() ==> {
            &&& self.journal.persistent_seq_end
                == self.persistent_superblock_image_i().journal_seq_end
        }
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
        &&& self.i().refinement_inv()
        &&& self.superblock_loaded() && self.journal.journal.status is None ==>
            self.journal.journal.snapshot == self.persistent_superblock_image_i().journal_snapshot
        &&& self.superblock_loaded() && self.journal.journal.status is None ==>
            self.persistent_journal_image_i().wf()
        &&& self.superblock_loaded() && self.journal.journal.status is None ==> {
            let image = self.persistent_journal_image_i();
            &&& self.journal_projection_aus() =~=
                image.tj().disk_view.loose_build_lsn_au_index_au_walk(
                    image.snapshot.freshest_rec(),
                    image.snapshot.first(),
                ).values()
        }
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
            assert(project_persistent(post.disk, aus) == project_persistent(self.disk, aus)) by {
                assert_maps_equal!(project_persistent(post.disk, aus), project_persistent(self.disk, aus), addr => {
                    if addresses_in_aus(aus).contains(addr) {
                        assert(post.disk.content.restrict(addresses_in_aus(aus))
                            == self.disk.content.restrict(addresses_in_aus(aus)));
                    }
                });
            }
            caching_disk_i_equal_from_raw_projection_agreement(
                post.cache,
                self.cache,
                post.disk,
                self.disk,
                aus,
            );
            caching_disk_i_equal_by_aus_ext(post.cache, post.disk, post.journal_projection_aus(), aus);
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
            assert(project_persistent(post.disk, aus) == project_persistent(self.disk, aus)) by {
                assert_maps_equal!(project_persistent(post.disk, aus), project_persistent(self.disk, aus), addr => {
                    if addresses_in_aus(aus).contains(addr) {
                        assert(post.disk.content.restrict(addresses_in_aus(aus))
                            == self.disk.content.restrict(addresses_in_aus(aus)));
                    }
                });
            }
            caching_disk_i_equal_from_raw_projection_agreement(
                post.cache,
                self.cache,
                post.disk,
                self.disk,
                aus,
            );
            caching_disk_i_equal_by_aus_ext(post.cache, post.disk, post.journal_projection_aus(), aus);
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

    pub proof fn journal_image_matches_materialized(
        self,
        image: AbstractSuperblockImage,
        frozen: CachingDiskJournalFrozenMetadata,
    )
        requires
            inv(self),
            self.superblock_loaded(),
            self.journal.ready(),
            image.wf(),
            frozen.snapshot == image.journal_snapshot,
            frozen.seq_end == image.journal_seq_end,
            self.journal_caching_disk_state_i().i().frozen_metadata_valid(
                frozen_image_metadata_i(frozen),
            ),
            materialization_certificate(self.journal_caching_disk_state_i(), frozen),
        ensures
            self.journal_image_i(image)
                == CachingDiskJournalImage::materialized_from_persistent(
                    self.journal_caching_disk_state_i(),
                    frozen,
                ),
            self.journal_image_i(image)
                == CachingDiskJournalImage::materialized_from_loaded_index(
                    self.journal_caching_disk_state_i(),
                    frozen,
                ),
    {
        let state = self.journal_caching_disk_state_i();
        let meta = frozen_image_metadata_i(frozen);
        let image_lsns = Set::new(|lsn: nat|
            image.journal_snapshot.boundary_lsn <= lsn < image.journal_seq_end);
        let frozen_lsns = state.frozen_lsns(frozen.snapshot);
        assert(image_lsns =~= frozen_lsns) by {
            assert(state.frozen_seq_end(frozen.snapshot) == frozen.seq_end) by {
                if frozen.snapshot.freshest_rec() is Some {
                    let root = frozen.snapshot.freshest_rec().unwrap();
                    assert(meta.freshest_rec is Some);
                    assert(meta.freshest_rec.unwrap() == root);
                    assert(state.i().disk_view.entries.contains_key(root));
                    assert(state.i().disk_view.entries[root].message_seq.seq_end == meta.seq_end);
                    assert(state.journal_disk_view().entries[root].message_seq.seq_end
                        == frozen.seq_end);
                } else {
                    assert(meta.freshest_rec is None);
                    assert(meta.boundary_lsn == meta.seq_end);
                }
            }
            assert forall |lsn: LSN| #[trigger] image_lsns.contains(lsn)
                <==> frozen_lsns.contains(lsn) by {}
        }
        assert(state.lsn_au_index_or_empty() == state.visible_lsn_au_index());
        CrashAwareCachingDiskJournal::State::materialization_certificate_implies_persistent_frozen_loose_domain_matches_visible(
            state,
            frozen,
        );
        CrashAwareCachingDiskJournal::State::materialization_certificate_implies_materialized_index_values_match_visible(
            state,
            frozen,
        );
        let materialized = CachingDiskJournalImage::materialized_from_persistent(state, frozen);
        CrashAwareCachingDiskJournal::State::materialization_certificate_implies_materialized_image_refines(
            state,
            frozen,
        );
        CrashAwareCachingDiskJournal::State::materialized_loaded_index_matches_persistent_when_domains_match(
            state,
            frozen,
        );
        assert(materialized.wf());
        assert(CachingDiskJournalImage::materialized_from_loaded_index(state, frozen) == materialized);

        let full_tj = UnifiedCacheJournalSource::journal_image_tj_i(self.disk.content, image);
        let full_dv = full_tj.disk_view;
        let restricted_dv = materialized.tj().disk_view;
        let root = image.journal_snapshot.freshest_rec();
        let first = image.journal_snapshot.first();
        let full_index = full_dv.loose_build_lsn_au_index_au_walk(root, first);
        let restricted_index = restricted_dv.loose_build_lsn_au_index_au_walk(root, first);

        assert(self.journal_image_projection_aus_i(image) =~= full_index.values());
        assert(restricted_dv.entries <= full_dv.entries) by {
            assert forall |addr: Address| #[trigger] restricted_dv.entries.contains_key(addr)
                implies full_dv.entries.contains_key(addr)
                    && restricted_dv.entries[addr] == full_dv.entries[addr] by {
                assert(to_journal_records(materialized.persistent).contains_key(addr));
                assert(materialized.persistent.contains_key(addr));
                assert(state.disk.persistent.contains_key(addr));
                assert(state.disk.persistent[addr] == self.disk.content[addr]);
                assert(materialized.persistent[addr] == self.disk.content[addr]);
                assert(self.disk.content.contains_key(addr));
                assert(restricted_dv.entries[addr] == to_journal_records(materialized.persistent)[addr]);
                assert(full_dv.entries[addr] == to_journal_records(self.disk.content)[addr]);
            }
        }

        materialized.i_valid_image_seq_end_implies_wf();
        assert(materialized.i().valid_image());
        materialized.i().valid_image_implies_tight_valid_image();
        assert(restricted_dv.path_decodable(root));
        assert(restricted_dv.path_build_tight(root).pointer_is_upstream(root, first));
        let ranking = choose |ranking|
            restricted_dv.path_valid_ranking(root, ranking);
        assert(restricted_dv.is_sub_disk(full_dv));
        full_dv.path_valid_ranking_lifts_from_sub_disk(restricted_dv, root, ranking);
        assert(full_dv.path_decodable(root));
        restricted_dv.path_build_tight_extends_same(full_dv, root);
        assert(full_dv.path_build_tight(root) == restricted_dv.path_build_tight(root));
        assert(full_dv.path_build_tight(root).pointer_is_upstream(root, first));
        full_dv.loose_build_lsn_au_index_au_walk_matches_tight(root, first);
        restricted_dv.loose_build_lsn_au_index_au_walk_matches_tight(root, first);
        assert(full_index =~= restricted_index);

        assert(self.journal_image_projection_aus_i(image)
            =~= state.lsn_au_index_or_empty().restrict(frozen_lsns).values()) by {
            assert(self.journal_image_projection_aus_i(image) =~= full_index.values());
            assert(full_index =~= restricted_index);
            assert(restricted_index.values()
                =~= state.lsn_au_index_or_empty().restrict(frozen_lsns).values());
        }
        assert(state.frozen_loose_domain(frozen.snapshot)
            =~= addresses_in_aus(self.journal_image_projection_aus_i(image))) by {
            assert forall |addr: Address|
                #[trigger] state.frozen_loose_domain(frozen.snapshot).contains(addr)
                <==> addresses_in_aus(self.journal_image_projection_aus_i(image)).contains(addr) by {
                assert(state.frozen_loose_domain(frozen.snapshot)
                    == addresses_in_aus(
                        state.lsn_au_index_or_empty().restrict(frozen_lsns).values(),
                    ));
                if state.frozen_loose_domain(frozen.snapshot).contains(addr) {
                    assert(self.journal_image_projection_aus_i(image).contains(addr.au));
                }
                if addresses_in_aus(self.journal_image_projection_aus_i(image)).contains(addr) {
                    assert(state.lsn_au_index_or_empty().restrict(frozen_lsns).values().contains(addr.au));
                }
            }
        }
        assert(state.persistent_frozen_loose_domain(frozen)
            =~= addresses_in_aus(self.journal_image_projection_aus_i(image))) by {
            assert(state.persistent_frozen_loose_domain(frozen)
                =~= state.frozen_loose_domain(frozen.snapshot));
        }
        assert(self.journal_image_projection_aus_i(image) <= self.journal_projection_aus()) by {
            assert(self.journal_projection_aus() == self.journal.owned_aus());
            assert(self.journal.owned_aus() == self.journal.loaded_index_aus()
                + self.journal.mini_allocator.all_aus());
            assert(self.journal.loaded_index_aus() == cj_lsn_au_index(self.journal.journal).values());
            assert forall |au: AU| #[trigger] self.journal_image_projection_aus_i(image).contains(au)
                implies self.journal_projection_aus().contains(au) by {
                assert(state.lsn_au_index_or_empty().restrict(frozen_lsns).values().contains(au));
                assert(state.lsn_au_index_or_empty().contains_value(au));
                assert(cj_lsn_au_index(self.journal.journal) == state.visible_lsn_au_index());
                assert(cj_lsn_au_index(self.journal.journal).contains_value(au));
                assert(cj_lsn_au_index(self.journal.journal).values().contains(au));
            }
        }

        assert(materialized.persistent == self.journal_image_i(image).persistent) by {
            assert_maps_equal!(
                materialized.persistent,
                self.journal_image_i(image).persistent,
                addr => {
                    if materialized.persistent.contains_key(addr) {
                        assert(state.disk.persistent.contains_key(addr));
                        assert(state.persistent_frozen_loose_domain(frozen).contains(addr));
                        assert(state.frozen_loose_domain(frozen.snapshot).contains(addr));
                        assert(addresses_in_aus(self.journal_projection_aus()).contains(addr));
                    }
                    if self.journal_image_i(image).persistent.contains_key(addr) {
                        assert(addresses_in_aus(self.journal_image_projection_aus_i(image)).contains(addr));
                        assert(state.persistent_frozen_loose_domain(frozen).contains(addr));
                        assert(state.frozen_loose_domain(frozen.snapshot).contains(addr));
                        assert(addresses_in_aus(self.journal_projection_aus()).contains(addr));
                        assert(state.disk.persistent.contains_key(addr));
                    }
                }
            );
        }
        assert(materialized.snapshot == self.journal_image_i(image).snapshot);
        assert(materialized.seq_end == self.journal_image_i(image).seq_end);
        assert(materialized == self.journal_image_i(image));
    }

    pub proof fn post_crash_persistent_image_matches_materialized(
        self,
        post: Self,
        image: AbstractSuperblockImage,
        frozen: CachingDiskJournalFrozenMetadata,
    )
        requires
            inv(self),
            self.superblock_loaded(),
            self.journal.ready(),
            post.persistent_image is None,
            post.journal == AtomicJournalState::State::empty(),
            post.disk.content == self.disk.content,
            post.persistent_superblock_image_i() == image,
            image.wf(),
            frozen.snapshot == image.journal_snapshot,
            frozen.seq_end == image.journal_seq_end,
            self.journal_caching_disk_state_i().i().frozen_metadata_valid(
                frozen_image_metadata_i(frozen),
            ),
            materialization_certificate(self.journal_caching_disk_state_i(), frozen),
        ensures
            post.persistent_journal_image_i()
                == CachingDiskJournalImage::materialized_from_persistent(
                    self.journal_caching_disk_state_i(),
                    frozen,
                ),
            post.persistent_journal_image_i()
                == CachingDiskJournalImage::materialized_from_loaded_index(
                    self.journal_caching_disk_state_i(),
                    frozen,
                ),
    {
        let state = self.journal_caching_disk_state_i();
        let materialized = CachingDiskJournalImage::materialized_from_persistent(state, frozen);
        self.journal_image_matches_materialized(image, frozen);
        assert(materialized == self.journal_image_i(image));
        assert(CachingDiskJournalImage::materialized_from_loaded_index(state, frozen) == materialized);

        CrashAwareCachingDiskJournal::State::materialization_certificate_implies_materialized_image_refines(
            state,
            frozen,
        );
        assert(materialized.wf());

        assert(post.persistent_journal_image_i().snapshot == materialized.snapshot);
        assert(post.persistent_journal_image_i().seq_end == materialized.seq_end);

        let full_tj = UnifiedCacheJournalSource::journal_image_tj_i(post.disk.content, image);
        let full_dv = full_tj.disk_view;
        let restricted_dv = materialized.tj().disk_view;
        let root = image.journal_snapshot.freshest_rec();
        let first = image.journal_snapshot.first();
        let full_index = full_dv.loose_build_lsn_au_index_au_walk(root, first);
        let restricted_index = restricted_dv.loose_build_lsn_au_index_au_walk(root, first);

        assert(post.journal.ready() == false);
        assert(post.journal_image_projection_aus_i(image) =~= full_index.values());

        assert(restricted_dv.entries <= full_dv.entries) by {
            assert forall |addr: Address| #[trigger] restricted_dv.entries.contains_key(addr)
                implies full_dv.entries.contains_key(addr)
                    && restricted_dv.entries[addr] == full_dv.entries[addr] by {
                assert(to_journal_records(materialized.persistent).contains_key(addr));
                assert(materialized.persistent.contains_key(addr));
                assert(materialized.persistent[addr] == self.disk.content[addr]) by {
                    assert(self.journal_image_i(image).persistent.contains_key(addr));
                    assert(self.journal_image_i(image).persistent[addr] == self.disk.content[addr]);
                }
                assert(post.disk.content.contains_key(addr));
                assert(post.disk.content[addr] == self.disk.content[addr]);
                assert(restricted_dv.entries[addr] == to_journal_records(materialized.persistent)[addr]);
                assert(full_dv.entries[addr] == to_journal_records(post.disk.content)[addr]);
            }
        }

        materialized.i_valid_image_seq_end_implies_wf();
        assert(materialized.i().valid_image());
        materialized.i().valid_image_implies_tight_valid_image();
        assert(restricted_dv.path_decodable(root));
        assert(restricted_dv.path_build_tight(root).pointer_is_upstream(root, first));
        let ranking = choose |ranking|
            restricted_dv.path_valid_ranking(root, ranking);
        assert(restricted_dv.is_sub_disk(full_dv));
        full_dv.path_valid_ranking_lifts_from_sub_disk(restricted_dv, root, ranking);
        assert(full_dv.path_decodable(root));
        restricted_dv.path_build_tight_extends_same(full_dv, root);
        assert(full_dv.path_build_tight(root) == restricted_dv.path_build_tight(root));
        assert(full_dv.path_build_tight(root).pointer_is_upstream(root, first));
        full_dv.loose_build_lsn_au_index_au_walk_matches_tight(root, first);
        restricted_dv.loose_build_lsn_au_index_au_walk_matches_tight(root, first);
        assert(full_index =~= restricted_index);

        CrashAwareCachingDiskJournal::State::materialization_certificate_implies_materialized_index_values_match_visible(
            state,
            frozen,
        );
        let image_lsns = Set::new(|lsn: nat|
            image.journal_snapshot.boundary_lsn <= lsn < image.journal_seq_end);
        let frozen_lsns = state.frozen_lsns(frozen.snapshot);
        assert(image_lsns =~= frozen_lsns) by {
            assert(state.frozen_seq_end(frozen.snapshot) == frozen.seq_end) by {
                if frozen.snapshot.freshest_rec() is Some {
                    let root = frozen.snapshot.freshest_rec().unwrap();
                    assert(state.journal_disk_view().entries[root].message_seq.seq_end
                        == frozen.seq_end);
                } else {
                    assert(frozen.snapshot.boundary_lsn == frozen.seq_end);
                }
            }
            assert forall |lsn: LSN| #[trigger] image_lsns.contains(lsn)
                <==> frozen_lsns.contains(lsn) by {}
        }
        assert(restricted_index.values() =~= self.journal_image_projection_aus_i(image)) by {
            assert(self.journal.ready());
            assert(self.journal_image_projection_aus_i(image)
                == cj_lsn_au_index(self.journal.journal).restrict(image_lsns).values());
            assert(cj_lsn_au_index(self.journal.journal) == state.visible_lsn_au_index());
            assert(state.lsn_au_index_or_empty() == state.visible_lsn_au_index());
            assert_maps_equal!(
                cj_lsn_au_index(self.journal.journal).restrict(image_lsns),
                state.lsn_au_index_or_empty().restrict(frozen_lsns),
                lsn => {}
            );
        }
        assert(post.journal_image_projection_aus_i(image)
            =~= self.journal_image_projection_aus_i(image)) by {
            assert(post.journal_image_projection_aus_i(image) =~= full_index.values());
            assert(full_index =~= restricted_index);
        }

        assert(post.persistent_journal_image_i().persistent == materialized.persistent) by {
            assert_maps_equal!(
                post.persistent_journal_image_i().persistent,
                materialized.persistent,
                addr => {
                    if post.persistent_journal_image_i().persistent.contains_key(addr) {
                        assert(self.journal_image_i(image).persistent.contains_key(addr));
                    }
                    if materialized.persistent.contains_key(addr) {
                        assert(self.journal_image_i(image).persistent.contains_key(addr));
                        assert(post.persistent_journal_image_i().persistent.contains_key(addr));
                    }
                }
            );
        }
        assert(post.persistent_journal_image_i() == materialized);
    }

    pub proof fn unloaded_post_crash_persistent_image_matches_materialized(
        self,
        post: Self,
        image: AbstractSuperblockImage,
        frozen: CachingDiskJournalFrozenMetadata,
    )
        requires
            inv(self),
            self.superblock_loaded(),
            !self.journal.ready(),
            post.persistent_image is None,
            post.journal == AtomicJournalState::State::empty(),
            post.disk.content == self.disk.content,
            post.persistent_superblock_image_i() == image,
            image == self.persistent_superblock_image_i(),
            image.wf(),
            frozen.snapshot == image.journal_snapshot,
            frozen.seq_end == image.journal_seq_end,
        ensures
            post.persistent_journal_image_i()
                == CachingDiskJournalImage::materialized_from_persistent(
                    self.journal_caching_disk_state_i(),
                    frozen,
                ),
            post.persistent_journal_image_i()
                == CachingDiskJournalImage::materialized_from_loaded_index(
                    self.journal_caching_disk_state_i(),
                    frozen,
                ),
    {
        let state = self.journal_caching_disk_state_i();
        let materialized = CachingDiskJournalImage::materialized_from_persistent(state, frozen);
        let source_image = self.journal_image_i(image);
        let root = image.journal_snapshot.freshest_rec();
        let first = image.journal_snapshot.first();
        let source_tj = source_image.tj();
        let source_index = source_tj.disk_view.loose_build_lsn_au_index_au_walk(root, first);
        let frozen_lsns = Set::new(|lsn: LSN|
            frozen.snapshot.boundary_lsn <= lsn < frozen.seq_end);

        assert(self.journal.journal.status is None);
        assert(self.journal_projection_aus() =~= self.journal_image_projection_aus_i(image));
        assert(self.journal_projection_aus() =~= source_index.values());
        assert(state.disk.persistent == source_image.persistent) by {
            assert_maps_equal!(
                state.disk.persistent,
                source_image.persistent,
                addr => {
                    assert(self.journal_projection_aus()
                        =~= self.journal_image_projection_aus_i(image));
                }
            );
        }
        assert(state.persistent_lsn_au_index(frozen.snapshot) == source_index) by {
            assert(state.persistent_journal_disk_view(frozen.snapshot) == source_tj.disk_view);
        }
        assert(source_image.i().valid_image());
        source_image.i().valid_image_implies_tight_valid_image();
        assert(source_tj.disk_view.path_decodable(root));
        assert(source_tj.disk_view.path_build_tight(root).pointer_is_upstream(root, first));
        source_tj.disk_view.loose_build_lsn_au_index_au_walk_matches_tight(root, first);
        let tight_tj = source_image.i().tight_tj();
        let tight_index = tight_tj.build_lsn_au_index_from_first(first);
        assert(tight_tj.disk_view == source_tj.disk_view.path_build_tight(root));
        assert(tight_tj.freshest_rec == root);
        assert(source_index == tight_index);
        tight_tj.build_lsn_au_index_from_first_ensures(first);
        reveal(TruncatedJournal::au_domain_valid);
        assert(source_index.dom() <= frozen_lsns) by {
            assert forall |lsn: LSN| #[trigger] source_index.contains_key(lsn)
                implies frozen_lsns.contains(lsn) by {
                assert(tight_index.contains_key(lsn));
                assert(tight_tj.au_domain_valid(tight_index));
                assert(tight_tj.seq_start() <= lsn < tight_tj.seq_end());
                source_image.i().valid_image_implies_tight_seq_bounds();
                assert(tight_tj.seq_start() == frozen.snapshot.boundary_lsn);
                assert(tight_tj.seq_end() == frozen.seq_end);
            }
        }
        assert(source_index.restrict(frozen_lsns) == source_index) by {
            assert_maps_equal!(
                source_index.restrict(frozen_lsns),
                source_index,
                lsn => {
                    if source_index.contains_key(lsn) {
                        assert(source_index.dom().contains(lsn));
                        assert(frozen_lsns.contains(lsn));
                    }
                }
            );
        }
        assert(state.persistent_frozen_loose_domain(frozen)
            =~= addresses_in_aus(self.journal_image_projection_aus_i(image))) by {
            assert(state.persistent_lsn_au_index(frozen.snapshot).restrict(frozen_lsns)
                == source_index);
        }
        assert(state.frozen_loose_domain(frozen.snapshot)
            =~= addresses_in_aus(self.journal_image_projection_aus_i(image))) by {
            assert(self.journal_projection_aus() =~= self.journal_image_projection_aus_i(image));
            assert(state.visible_lsn_au_index() == source_index) by {
                assert(self.i().semantic_inv());
                assert(state.disk.addrs_clean_or_evictable(state.disk.cache.dom()));
                state.disk.clean_cache_visible_eq_persistent();
                assert(state.disk.visible() == state.disk.persistent);
                assert(state.journal_disk_view().entries
                    == state.persistent_journal_disk_view(frozen.snapshot).entries);
                assert(state.persistent_journal_disk_view(frozen.snapshot) == source_tj.disk_view);
                assert(state.journal_disk_view() == source_tj.disk_view);
            }
            assert(state.lsn_au_index_or_empty() == source_index);
        }
        CrashAwareCachingDiskJournal::State::materialized_loaded_index_matches_persistent_when_domains_match(
            state,
            frozen,
        );
        assert(materialized.persistent == source_image.persistent) by {
            assert_maps_equal!(
                materialized.persistent,
                source_image.persistent,
                addr => {
                    if materialized.persistent.contains_key(addr) {
                        assert(state.disk.persistent.contains_key(addr));
                        assert(source_image.persistent.contains_key(addr));
                    }
                    if source_image.persistent.contains_key(addr) {
                        assert(state.disk.persistent.contains_key(addr));
                        assert(state.persistent_frozen_loose_domain(frozen).contains(addr));
                    }
                }
            );
        }
        assert(materialized.snapshot == source_image.snapshot);
        assert(materialized.seq_end == source_image.seq_end);
        assert(materialized == source_image);

        assert(post.persistent_journal_image_i() == source_image) by {
            assert(post.journal_image_projection_aus_i(image)
                =~= self.journal_image_projection_aus_i(image));
            assert_maps_equal!(
                post.persistent_journal_image_i().persistent,
                source_image.persistent,
                addr => {
                    if post.persistent_journal_image_i().persistent.contains_key(addr) {
                        assert(source_image.persistent.contains_key(addr));
                    }
                    if source_image.persistent.contains_key(addr) {
                        assert(post.persistent_journal_image_i().persistent.contains_key(addr));
                    }
                }
            );
        }
        assert(post.persistent_journal_image_i() == materialized);
        assert(CachingDiskJournalImage::materialized_from_loaded_index(state, frozen) == materialized);
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

    pub proof fn loaded_caching_disk_internal_refines_journal_internal_preserves_inv(
        self,
        post: Self,
    )
        requires
            inv(self),
            self.same_except_cache_and_disk(post),
            self.superblock_loaded(),
            self.journal.ready(),
            post.cache == self.cache,
            post.disk.inv(),
            async_disk_superblock_page_wf(post.disk.content),
            post.persistent_superblock_image_i() == self.persistent_superblock_image_i(),
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
            inv(post),
    {
        self.loaded_caching_disk_internal_refines_journal_internal(post);
        CachingDisk::State::inv_next(
            self.journal_caching_disk_i(),
            post.journal_caching_disk_i(),
            CachingDisk::Label::Internal{},
        );
        assert(post.inv()) by {
            assert(post.journal.wf());
            assert(async_disk_superblock_page_wf(post.disk.content));
            assert(post.persistent_superblock_image_i().wf());
            assert(post.cache.inv());
            assert(post.disk.inv());
            assert(post.journal_caching_disk_i().inv());
            assert(post.journal.ready());
        }
        self.i().next_refines(post.i(), CrashAwareCachingDiskJournal::Label::Internal);
        assert(post.semantic_inv()) by {
            assert(post.journal.ready());
        }
        assert(inv(post));
    }

    pub proof fn loaded_cache_internal_refines_journal_internal(
        self,
        post: Self,
    )
        requires
            inv(self),
            self.same_except_cache_and_disk(post),
            self.superblock_loaded(),
            post.disk.content == self.disk.content,
            post.disk.inv(),
            Cache::State::next(self.cache, post.cache, Cache::Label::Internal{}),
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
        cache_internal_refines_caching_disk_internal(self.cache, post.cache, self.disk, aus);
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
                Cache::State::inv_next(self.cache, post.cache, Cache::Label::Internal{});
            }
            assert(post.journal_caching_disk_i().inv());
        }
        self.i().next_refines(post.i(), CrashAwareCachingDiskJournal::Label::Internal);
        assert(post.semantic_inv());
        assert(inv(post));
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
                &&& responses[addr] is ReadResp ==> {
                    self.disk.content.contains_key(addr) ==> responses[addr]->data
                        == self.disk.content[addr]
                }
                &&& responses[addr] is WriteResp ==> {
                    &&& self.disk.content.contains_key(addr)
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
            }

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
            src.journal_caching_disk_i().empty_status_clean_pages_agree();
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

pub proof fn load_ephemeral_refines(
    pre: UnifiedCacheJournalSource,
    post: UnifiedCacheJournalSource,
    image: AbstractSuperblockImage,
)
    requires
        inv(pre),
        !pre.superblock_loaded(),
        pre.persistent_superblock_image_i() == image,
        post.persistent_image == Option::Some(image),
        post.cache == pre.cache,
        post.disk.content == pre.disk.content,
        post.disk.inv(),
        post.in_flight is None,
        post.in_flight_image is None,
        AtomicJournalState::State::initialize(
            post.journal,
            image.journal_snapshot,
            image.journal_seq_end,
        ),
        pre.journal_caching_disk_i().cache == Map::<Address, RawPage>::empty(),
        pre.journal_caching_disk_i().status == Map::<Address, PageStatus>::empty(),
        post.journal_caching_disk_i().cache == Map::<Address, RawPage>::empty(),
        post.journal_caching_disk_i().status == Map::<Address, PageStatus>::empty(),
    ensures
        CrashAwareCachingDiskJournal::State::next(
            unified_cache_journal_i(pre),
            unified_cache_journal_i(post),
            CrashAwareCachingDiskJournal::Label::LoadEphemeral,
        ),
        inv(post),
{
    reveal(AtomicJournalState::State::initialize);

    assert(pre.journal == AtomicJournalState::State::empty());
    assert(pre.in_flight is None);
    assert(pre.in_flight_image is None);
    assert(post.superblock_loaded());
    assert(post.persistent_superblock_image_i() == image);
    assert(post.persistent_superblock_image_i().wf());
    assert(post.journal.wf());
    assert(post.cache.inv());

    assert(post.journal_image_projection_aus_i(image)
        =~= pre.journal_image_projection_aus_i(image)) by {
        let pre_tj = UnifiedCacheJournalSource::journal_image_tj_i(pre.disk.content, image);
        let post_tj = UnifiedCacheJournalSource::journal_image_tj_i(post.disk.content, image);
        assert(pre_tj == post_tj);
    }
    assert(post.journal_projection_aus() =~= pre.journal_projection_aus()) by {
        assert(!post.journal.ready());
        assert(!pre.journal.ready());
    }
    assert(post.persistent_journal_image_i() == pre.persistent_journal_image_i()) by {
        assert_maps_equal!(
            post.persistent_journal_image_i().persistent,
            pre.persistent_journal_image_i().persistent,
            addr => {
                if post.persistent_journal_image_i().persistent.contains_key(addr) {
                    assert(pre.persistent_journal_image_i().persistent.contains_key(addr));
                }
                if pre.persistent_journal_image_i().persistent.contains_key(addr) {
                    assert(post.persistent_journal_image_i().persistent.contains_key(addr));
                }
            }
        );
    }
    let persistent_image = pre.persistent_journal_image_i();
    assert(post.persistent_journal_image_i() == persistent_image);
    assert(pre.persistent_journal_i() == PersistentCachingDiskJournal::Image{
        image: persistent_image,
    });
    assert(post.persistent_journal_i() == PersistentCachingDiskJournal::Metadata{
        meta: persistent_image.metadata(),
    });

    assert(post.journal_caching_disk_i().persistent == persistent_image.persistent) by {
        assert_maps_equal!(
            post.journal_caching_disk_i().persistent,
            persistent_image.persistent,
            addr => {
                if post.journal_caching_disk_i().persistent.contains_key(addr) {
                    assert(persistent_image.persistent.contains_key(addr));
                }
                if persistent_image.persistent.contains_key(addr) {
                    assert(post.journal_caching_disk_i().persistent.contains_key(addr));
                }
            }
        );
    }
    assert(post.journal_caching_disk_i()
        == CachingDiskJournal::State::disk_from_persistent(persistent_image.persistent));
    assert(post.journal_caching_disk_state_i()
        == CachingDiskJournal::State::load_from_persistent(
            persistent_image.snapshot,
            persistent_image.persistent,
        ));

    let src = unified_cache_journal_i(pre);
    let dst = unified_cache_journal_i(post);
    assert(src.ephemeral is Unknown);
    assert(src.persistent == PersistentCachingDiskJournal::Image{image: persistent_image});
    assert(dst.ephemeral == EphemeralCachingDiskJournal::Known{
        v: CachingDiskJournal::State::load_from_persistent(
            persistent_image.snapshot,
            persistent_image.persistent,
        ),
    });
    assert(dst.persistent == PersistentCachingDiskJournal::Metadata{
        meta: persistent_image.metadata(),
    });
    assert(CrashAwareCachingDiskJournal::State::load_ephemeral(
        src,
        dst,
        CrashAwareCachingDiskJournal::Label::LoadEphemeral,
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::load_ephemeral);
    }
    assert(CrashAwareCachingDiskJournal::State::next_by(
        src,
        dst,
        CrashAwareCachingDiskJournal::Label::LoadEphemeral,
        CrashAwareCachingDiskJournal::Step::load_ephemeral(),
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::next_by);
    }
    reveal(CrashAwareCachingDiskJournal::State::next);
    src.next_refines(dst, CrashAwareCachingDiskJournal::Label::LoadEphemeral);
    assert(post.semantic_inv()) by {
        assert(post.i().refinement_inv());
        assert(post.superblock_loaded());
        assert(post.journal.journal.status is None);
        assert(post.journal.journal.snapshot
            == post.persistent_superblock_image_i().journal_snapshot);
        assert(post.persistent_journal_image_i().wf());

        let abs_image = post.persistent_superblock_image_i();
        let full_tj = UnifiedCacheJournalSource::journal_image_tj_i(
            post.disk.content,
            abs_image,
        );
        let full_dv = full_tj.disk_view;
        let restricted_image = post.persistent_journal_image_i();
        let restricted_dv = restricted_image.tj().disk_view;
        let root = restricted_image.snapshot.freshest_rec();
        let first = restricted_image.snapshot.first();
        let full_index = full_dv.loose_build_lsn_au_index_au_walk(root, first);
        let restricted_index = restricted_dv.loose_build_lsn_au_index_au_walk(root, first);

        assert(root == full_tj.freshest_rec);
        assert(first == abs_image.journal_snapshot.first());
        assert(post.journal_projection_aus() =~= full_index.values());

        assert(restricted_image.i().valid_image());
        restricted_image.i().valid_image_implies_tight_valid_image();
        assert(restricted_dv.path_decodable(root));
        assert(restricted_dv.path_build_tight(root).pointer_is_upstream(root, first));
        assert(restricted_dv.entries <= full_dv.entries) by {
            assert forall |addr: Address| #[trigger] restricted_dv.entries.contains_key(addr)
                implies full_dv.entries.contains_key(addr)
                    && restricted_dv.entries[addr] == full_dv.entries[addr] by {
                assert(restricted_image.persistent.contains_key(addr));
                assert(post.disk.content.contains_key(addr));
                assert(restricted_image.persistent[addr] == post.disk.content[addr]);
                assert(restricted_dv.entries[addr] == to_journal_records(
                    restricted_image.persistent,
                )[addr]);
                assert(full_dv.entries[addr] == to_journal_records(post.disk.content)[addr]);
            }
        }
        let ranking = choose |ranking|
            restricted_dv.path_valid_ranking(root, ranking);
        assert(restricted_dv.is_sub_disk(full_dv));
        full_dv.path_valid_ranking_lifts_from_sub_disk(restricted_dv, root, ranking);
        assert(full_dv.path_decodable(root));
        restricted_dv.path_build_tight_extends_same(full_dv, root);
        assert(full_dv.path_build_tight(root) == restricted_dv.path_build_tight(root));
        assert(full_dv.path_build_tight(root).pointer_is_upstream(root, first));
        full_dv.loose_build_lsn_au_index_au_walk_matches_tight(root, first);
        restricted_dv.loose_build_lsn_au_index_au_walk_matches_tight(root, first);
        assert(full_index =~= restricted_index);
        assert(post.journal_projection_aus() =~= restricted_index.values());
    }
    assert(post.inv());
    assert(inv(post));
}

pub proof fn load_index_refines(
    pre: UnifiedCacheJournalSource,
    post: UnifiedCacheJournalSource,
    cache_reads: Map<Address, RawPage>,
    journal_reads: Map<Address, RawPage>,
    discovered_aus: Set<AU>,
)
    requires
        inv(pre),
        pre.superblock_loaded(),
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.in_flight == pre.in_flight,
        post.in_flight_image == pre.in_flight_image,
        journal_reads <= cache_reads,
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access{reads: cache_reads, writes: Map::empty()},
        ),
        AtomicJournalState::State::next(
            pre.journal,
            post.journal,
            AtomicJournalState::Label::LoadIndex{
                reads: to_journal_records(journal_reads),
                discovered_aus,
            },
        ),
    ensures
        CrashAwareCachingDiskJournal::State::next(
            unified_cache_journal_i(pre),
            unified_cache_journal_i(post),
            CrashAwareCachingDiskJournal::Label::LoadIndex{discovered_aus},
        ),
        inv(post),
{
    let empty_writes = Map::<Address, RawPage>::empty();
    let cache_lbl = Cache::Label::Access{reads: cache_reads, writes: empty_writes};
    let atomic_lbl = AtomicJournalState::Label::LoadIndex{
        reads: to_journal_records(journal_reads),
        discovered_aus,
    };
    let aus = pre.journal_projection_aus();
    let cj_lbl = CachingDiskJournal::Label::LoadIndex{discovered_aus};
    let component_addrs = addresses_in_aus(aus);
    let image = pre.persistent_journal_image_i();
    let component_backed_addrs = component_addrs.intersect(image.persistent.dom());
    let component_reads = journal_reads.restrict(component_backed_addrs);

    AtomicJournalState::State::wf_next(pre.journal, post.journal, atomic_lbl);
    reveal(AtomicJournalState::State::next);
    reveal(AtomicJournalState::State::next_by);
    let atomic_step = choose |step: AtomicJournalState::Step|
        AtomicJournalState::State::next_by(pre.journal, post.journal, atomic_lbl, step);
    match atomic_step {
        AtomicJournalState::Step::load_index(new_journal, au_depth, page_depth) => {
            assert(AtomicJournalState::State::load_index(
                pre.journal,
                post.journal,
                atomic_lbl,
                new_journal,
                au_depth,
                page_depth,
            )) by {
                reveal(AtomicJournalState::State::load_index);
            }
            assert(post.journal.journal == new_journal);
            assert(post.journal.mini_allocator == pre.journal.mini_allocator);
            assert(post.journal.persistent_seq_end == pre.journal.persistent_seq_end);
            assert(post.journal.in_flight == pre.journal.in_flight);
            assert(post.journal.prepared == pre.journal.prepared);
            assert(CachedJournal::State::next(
                pre.journal.journal,
                post.journal.journal,
                CachedJournal::Label::LoadIndex{
                    reads: to_journal_records(journal_reads),
                    discovered_aus,
                },
            ));
            CachedJournal::State::load_index_effect(
                pre.journal.journal,
                post.journal.journal,
                to_journal_records(journal_reads),
                discovered_aus,
            );
            assert(pre.journal.journal.status is None);
            assert(post.journal.journal.status is Some);
            assert(post.journal.loaded_index_aus() == discovered_aus);
        },
        _ => {
            assert(false);
        },
    }

    Cache::State::inv_next(pre.cache, post.cache, cache_lbl);
    assert(!pre.journal.ready());
    assert(post.journal.ready());
    let image_entries = to_journal_records(image.persistent);
    let source_reads = to_journal_records(journal_reads);
    assert(image.wf());
    assert(image.valid_image());
    assert(pre.journal.journal.snapshot == image.snapshot);
    assert forall |addr: Address| #[trigger] source_reads.contains_key(addr)
        && image_entries.contains_key(addr)
        implies source_reads[addr] == image_entries[addr] by {
        assert(journal_reads.contains_key(addr));
        assert(cache_reads.contains_key(addr));
        assert(image.persistent.contains_key(addr));
        assert(image.persistent[addr] == pre.disk.content[addr]);
        assert(addresses_in_aus(aus).contains(addr));
        Cache::State::access_read_valid(pre.cache, post.cache, cache_reads, empty_writes, addr);
        assert(pre.cache.valid_read(addr, cache_reads[addr]));
        pre.cache.build_lookup_map_ensures();
        assert(pre.cache.build_lookup_map_props(pre.cache.lookup_map));
        assert(pre.cache.entries.contains_key(pre.cache.lookup_map[addr]));
        assert(cache_filled_addr(pre.cache, addr));
        assert(cache_filled_page(pre.cache, addr) == cache_reads[addr]);
        assert(project_cache_pages(pre.cache, aus).contains_key(addr));
        assert(project_cache_pages(pre.cache, aus)[addr] == cache_reads[addr]);
        assert(pre.journal_caching_disk_i().cache.contains_key(addr));
        assert(pre.journal_caching_disk_i().cache[addr] == cache_reads[addr]);
        assert(pre.i().ephemeral is Known);
        assert(pre.i().ephemeral->v == pre.journal_caching_disk_state_i());
        assert(pre.i().semantic_inv());
        assert(pre.journal_caching_disk_i().addrs_clean_or_evictable(
            pre.journal_caching_disk_i().cache.dom(),
        ));
        assert(pre.journal_caching_disk_i().cache.dom().contains(addr));
        pre.journal_caching_disk_i().addr_clean_or_evictable(
            pre.journal_caching_disk_i().cache.dom(),
            addr,
        );
        assert(pre.journal_caching_disk_i().status.contains_key(addr));
        assert(pre.journal_caching_disk_i().status[addr] == PageStatus::Clean);
        assert(pre.journal_caching_disk_i().inv());
        pre.journal_caching_disk_i().clean_page_agrees(addr);
        assert(pre.journal_caching_disk_i().persistent[addr] == pre.disk.content[addr]);
        assert(journal_reads[addr] == cache_reads[addr]);
        assert(source_reads[addr] == image_entries[addr]);
    }
    assert(image.i().valid_image());
    image.i().valid_image_implies_tight_valid_image();
    CachedJournal::State::load_index_matches_loose_full(
        pre.journal.journal,
        post.journal.journal,
        source_reads,
        discovered_aus,
        image_entries,
    );
    assert(discovered_aus <= aus) by {
        let image_dv = image.tj().disk_view;
        let root = image.snapshot.freshest_rec();
        let first = image.snapshot.first();
        let loose_index = image_dv.loose_build_lsn_au_index_au_walk(root, first);
        let tight_dv = image_dv.path_build_tight(root);
        assert(post.journal.journal.status.unwrap().lsn_au_index.values()
            =~= loose_index.values());
        image_dv.path_build_tight_is_sub_disk(root);
        image_dv.loose_build_lsn_au_index_au_walk_matches_tight(root, first);
        tight_dv.build_lsn_au_index_equiv_page_walk(root, first);
        tight_dv.build_lsn_au_index_page_walk_exist_valid_entries(root);
        let tight_index = tight_dv.build_lsn_au_index_au_walk(root, first);
        assert(loose_index =~= tight_index);
        assert forall |au: AU| #[trigger] discovered_aus.contains(au)
            implies aus.contains(au) by {
            assert(loose_index.values().contains(au));
            assert(tight_index.values().contains(au));
            let lsn = choose |lsn: nat| #![auto] tight_index.contains_key(lsn) && tight_index[lsn] == au;
            assert(tight_index.contains_key(lsn));
            assert(tight_index[lsn] == au);
            assert(tight_dv.build_lsn_au_index_page_walk(root).contains_key(lsn));
            assert(tight_dv.build_lsn_au_index_page_walk(root)[lsn] == au);
            let addr = tight_dv.instantiate_index_keys_exist_valid_entries(
                tight_dv.build_lsn_au_index_page_walk(root),
                lsn,
            );
            assert(addr.au == au);
            assert(tight_dv.addr_supports_lsn(addr, lsn));
            assert(tight_dv.entries.contains_key(addr));
            assert(image_dv.entries.contains_key(addr));
            assert(image_entries.contains_key(addr));
            assert(image.persistent.contains_key(addr));
            assert(addresses_in_aus(aus).contains(addr));
            assert(aus.contains(addr.au));
        }
    }
    assert(post.journal.owned_aus() =~= discovered_aus) by {
        assert(post.journal.loaded_index_aus() == discovered_aus);
        assert(post.journal.mini_allocator == pre.journal.mini_allocator);
        assert(pre.journal_caching_disk_state_i().refinement_inv());
        assert(pre.journal_caching_disk_state_i().journal.status is None);
        assert(pre.journal_caching_disk_state_i().unloaded_mini_allocator_empty());
        assert(pre.journal.mini_allocator.allocs.dom() =~= Set::<AU>::empty());
        assert(pre.journal.mini_allocator.all_aus() =~= Set::<AU>::empty());
    }
    assert(aus <= discovered_aus) by {
        let image_dv = image.tj().disk_view;
        let root = image.snapshot.freshest_rec();
        let first = image.snapshot.first();
        assert(aus =~= image_dv.loose_build_lsn_au_index_au_walk(root, first).values());
    }
    assert(post.journal_projection_aus() =~= aus);
    projected_cache_read_only_access_unchanged(pre.cache, post.cache, aus, cache_reads);

    assert(post.journal_caching_disk_i() == pre.journal_caching_disk_i()) by {
        assert(project_persistent(post.disk, aus) == project_persistent(pre.disk, aus));
        caching_disk_i_equal_from_raw_projection_agreement(
            post.cache,
            pre.cache,
            post.disk,
            pre.disk,
            aus,
        );
        caching_disk_i_equal_by_aus_ext(post.cache, post.disk, post.journal_projection_aus(), aus);
    }
    assert(component_reads <= pre.journal_caching_disk_i().visible()) by {
        assert forall |addr: Address| #[trigger] component_reads.contains_key(addr)
            implies {
                &&& pre.journal_caching_disk_i().visible().contains_key(addr)
                &&& component_reads[addr] == pre.journal_caching_disk_i().visible()[addr]
        } by {
            assert(journal_reads.contains_key(addr));
            assert(component_backed_addrs.contains(addr));
            assert(component_addrs.contains(addr));
            assert(image.persistent.contains_key(addr));
            assert(cache_reads.contains_key(addr));
            assert(aus.contains(addr.au));
            assert(component_addrs.contains(addr));
            Cache::State::access_read_valid(pre.cache, post.cache, cache_reads, empty_writes, addr);
            assert(pre.cache.valid_read(addr, cache_reads[addr]));
            pre.cache.build_lookup_map_ensures();
            assert(pre.cache.build_lookup_map_props(pre.cache.lookup_map));
            assert(pre.cache.entries.contains_key(pre.cache.lookup_map[addr]));
            assert(cache_filled_addr(pre.cache, addr));
            assert(cache_filled_page(pre.cache, addr) == cache_reads[addr]);
            assert(journal_reads[addr] == cache_reads[addr]);
            assert(component_reads[addr] == journal_reads[addr]);
            assert(project_cache_pages(pre.cache, aus).contains_key(addr));
            assert(project_cache_pages(pre.cache, aus)[addr] == cache_reads[addr]);
            assert(project_persistent(pre.disk, aus).contains_key(addr)) by {
                assert(image.persistent[addr] == pre.disk.content[addr]);
                assert(addresses_in_aus(aus).contains(addr));
            }
            assert(pre.i().ephemeral is Known);
            assert(pre.i().ephemeral->v == pre.journal_caching_disk_state_i());
            assert(pre.i().semantic_inv());
            assert(pre.journal_caching_disk_i().addrs_clean_or_evictable(
                pre.journal_caching_disk_i().cache.dom(),
            ));
            assert(pre.journal_caching_disk_i().cache.dom().contains(addr));
            pre.journal_caching_disk_i().addr_clean_or_evictable(
                pre.journal_caching_disk_i().cache.dom(),
                addr,
            );
            assert(pre.journal_caching_disk_i().status.contains_key(addr));
            assert(pre.journal_caching_disk_i().status[addr] == PageStatus::Clean);
            assert(pre.journal_caching_disk_i().inv());
            pre.journal_caching_disk_i().clean_page_agrees(addr);
            assert(pre.journal_caching_disk_i().persistent[addr]
                == pre.journal_caching_disk_i().cache[addr]);
            assert(pre.journal_caching_disk_i().persistent[addr]
                == project_persistent(pre.disk, aus)[addr]);
            assert(pre.journal_caching_disk_i().cache[addr]
                == project_cache_pages(pre.cache, aus)[addr]);
            assert(project_persistent(pre.disk, aus)[addr] == project_cache_pages(pre.cache, aus)[addr]);
            backed_raw_cache_entry_in_caching_disk_i_visible(pre.cache, pre.disk, aus, addr);
            assert(pre.journal_caching_disk_i().visible().contains_key(addr));
            assert(pre.journal_caching_disk_i().visible()[addr] == component_reads[addr]);
        }
    }
    assert(component_reads <= pre.journal_caching_disk_i().cache) by {
        assert forall |addr: Address| #[trigger] component_reads.contains_key(addr)
            implies {
                &&& pre.journal_caching_disk_i().cache.contains_key(addr)
                &&& component_reads[addr] == pre.journal_caching_disk_i().cache[addr]
        } by {
            assert(journal_reads.contains_key(addr));
            assert(component_backed_addrs.contains(addr));
            assert(component_addrs.contains(addr));
            assert(cache_reads.contains_key(addr));
            assert(aus.contains(addr.au));
            assert(addresses_in_aus(aus).contains(addr));
            Cache::State::access_read_valid(pre.cache, post.cache, cache_reads, empty_writes, addr);
            assert(pre.cache.valid_read(addr, cache_reads[addr]));
            pre.cache.build_lookup_map_ensures();
            assert(pre.cache.build_lookup_map_props(pre.cache.lookup_map));
            assert(pre.cache.entries.contains_key(pre.cache.lookup_map[addr]));
            assert(cache_filled_addr(pre.cache, addr));
            assert(cache_filled_page(pre.cache, addr) == cache_reads[addr]);
            assert(journal_reads[addr] == cache_reads[addr]);
            assert(component_reads[addr] == journal_reads[addr]);
            assert(project_cache_pages(pre.cache, aus).contains_key(addr));
            assert(project_cache_pages(pre.cache, aus)[addr] == cache_reads[addr]);
            assert(pre.journal_caching_disk_i() == adapter_caching_disk_i(pre.cache, pre.disk, aus));
            assert(pre.journal_caching_disk_i().cache.contains_key(addr));
            assert(pre.journal_caching_disk_i().cache[addr]
                == project_cache_pages(pre.cache, aus)[addr]);
            assert(pre.journal_caching_disk_i().cache[addr] == component_reads[addr]);
        }
    }

    assert(CachingDisk::State::access(
        pre.journal_caching_disk_i(),
        pre.journal_caching_disk_i(),
        CachingDisk::Label::Access{reads: component_reads, writes: empty_writes},
    )) by {
        reveal(CachingDisk::State::access);
        assert_maps_equal!(
            pre.journal_caching_disk_i().cache.union_prefer_right(empty_writes),
            pre.journal_caching_disk_i().cache,
            addr => {}
        );
        assert_maps_equal!(
            status_map(empty_writes.dom(), PageStatus::Dirty),
            Map::<Address, PageStatus>::empty(),
            addr => {}
        );
        assert_maps_equal!(
            pre.journal_caching_disk_i().status.union_prefer_right(
                status_map(empty_writes.dom(), PageStatus::Dirty),
            ),
            pre.journal_caching_disk_i().status,
            addr => {}
        );
    }
    assert(CachingDisk::State::next_by(
        pre.journal_caching_disk_i(),
        pre.journal_caching_disk_i(),
        CachingDisk::Label::Access{reads: component_reads, writes: empty_writes},
        CachingDisk::Step::access(),
    )) by {
        reveal(CachingDisk::State::next_by);
    }
    reveal(CachingDisk::State::next);

    match atomic_step {
        AtomicJournalState::Step::load_index(new_journal, au_depth, page_depth) => {
            let root = pre.journal.journal.snapshot.freshest_rec();
            let bdy = pre.journal.journal.snapshot.boundary_lsn;
            let first = pre.journal.journal.snapshot.first();
            let source_lbl = CachedJournal::Label::LoadIndex{
                reads: source_reads,
                discovered_aus,
            };
            assert(AtomicJournalState::State::load_index(
                pre.journal,
                post.journal,
                atomic_lbl,
                new_journal,
                au_depth,
                page_depth,
            )) by {
                reveal(AtomicJournalState::State::load_index);
            }
            assert(CachedJournal::State::load_index(
                pre.journal.journal,
                post.journal.journal,
                source_lbl,
                au_depth,
                page_depth,
            ));

            let image_dv = image.tj().disk_view;
            let image_index = image_dv.loose_build_lsn_au_index_au_walk(root, first);
            let tight_tj = image.i().tight_tj();
            let tight_dv = tight_tj.disk_view;
            let tight_entries = tight_dv.entries;
            let tight_index = tight_tj.build_lsn_au_index_from_first(first);
            assert(root == image.snapshot.freshest_rec());
            assert(bdy == image.snapshot.boundary_lsn);
            assert(first == image.snapshot.first());
            assert(image_dv == DiskView{
                boundary_lsn: pre.journal.journal.snapshot.boundary_lsn,
                entries: image_entries,
            });
            image_dv.loose_build_lsn_au_index_au_walk_matches_tight(root, first);
            assert(tight_tj.disk_view == image_dv.path_build_tight(root));
            assert(tight_tj.freshest_rec == root);
            assert(tight_dv.pointer_is_upstream(root, first));
            assert(image_index == tight_index);
            assert(aus =~= image_index.values());
            assert forall |addr: Address| #[trigger] source_reads.contains_key(addr)
                && tight_entries.contains_key(addr)
                implies source_reads[addr] == tight_entries[addr] by {
                assert(tight_dv.entries <= image_entries);
                assert(image_entries.contains_key(addr));
                assert(tight_entries[addr] == image_entries[addr]);
                assert(source_reads[addr] == image_entries[addr]);
            }
            assert forall |addr: Address| #[trigger] tight_entries.contains_key(addr)
                implies component_backed_addrs.contains(addr) by {
                assert(tight_dv.domain_au_bounded_wrt_index(tight_index));
                assert(tight_index.values().contains(addr.au));
                assert(image_index.values().contains(addr.au));
                assert(aus.contains(addr.au));
                assert(component_addrs.contains(addr));
                assert(tight_dv.entries <= image_entries);
                assert(image_entries.contains_key(addr));
                assert(image.persistent.contains_key(addr));
                assert(component_backed_addrs.contains(addr));
            }
            au_walk_addrs_in_entries_subset(
                source_reads,
                tight_entries,
                bdy,
                root,
                first,
                au_depth,
                page_depth,
                component_backed_addrs,
            );
            CachedJournal::State::load_index_with_restricted_reads(
                pre.journal.journal,
                post.journal.journal,
                source_reads,
                component_backed_addrs,
                discovered_aus,
                au_depth,
                page_depth,
            );
            to_journal_records_restrict(journal_reads, component_backed_addrs);
            assert(to_journal_records(component_reads) =~= source_reads.restrict(component_backed_addrs));
            assert(CachedJournal::State::next(
                pre.journal.journal,
                post.journal.journal,
                CachedJournal::Label::LoadIndex{
                    reads: to_journal_records(component_reads),
                    discovered_aus,
                },
            ));
        },
        _ => {
            assert(false);
        },
    }

    assert(post.journal_caching_disk_state_i().disk == pre.journal_caching_disk_i());
    assert(post.journal_caching_disk_state_i().mini_allocator == pre.journal.mini_allocator);
    assert(CachingDiskJournal::State::load_index(
        pre.journal_caching_disk_state_i(),
        post.journal_caching_disk_state_i(),
        cj_lbl,
        post.journal.journal,
        component_reads,
    )) by {
        reveal(CachingDiskJournal::State::load_index);
    }
    assert(CachingDiskJournal::State::next_by(
        pre.journal_caching_disk_state_i(),
        post.journal_caching_disk_state_i(),
        cj_lbl,
        CachingDiskJournal::Step::load_index(post.journal.journal, component_reads),
    )) by {
        reveal(CachingDiskJournal::State::next_by);
    }
    reveal(CachingDiskJournal::State::next);

    let src = unified_cache_journal_i(pre);
    let dst = unified_cache_journal_i(post);
    let target_lbl = CrashAwareCachingDiskJournal::Label::LoadIndex{discovered_aus};
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(src.persistent == dst.persistent);
    assert(src.frozen == dst.frozen);
    assert(src.prepared == dst.prepared);
    assert(CrashAwareCachingDiskJournal::State::load_index(
        src,
        dst,
        target_lbl,
        post.journal_caching_disk_state_i(),
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::load_index);
    }
    assert(CrashAwareCachingDiskJournal::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskJournal::Step::load_index(post.journal_caching_disk_state_i()),
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::next_by);
    }
    reveal(CrashAwareCachingDiskJournal::State::next);
    src.next_refines(dst, target_lbl);

    assert(post.inv()) by {
        assert(post.journal.wf());
        assert(async_disk_superblock_page_wf(post.disk.content));
        assert(post.persistent_superblock_image_i() == pre.persistent_superblock_image_i());
        assert(post.persistent_superblock_image_i().wf());
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.journal_caching_disk_i().inv());
        assert(post.journal.persistent_seq_end == pre.journal.persistent_seq_end);
        assert(post.in_flight is Some <==> post.journal.in_flight is Some);
        assert(post.in_flight is Some <==> post.in_flight_image is Some);
    }
    assert(post.semantic_inv());
    assert(inv(post));
}

pub proof fn read_for_recovery_refines(
    pre: UnifiedCacheJournalSource,
    post: UnifiedCacheJournalSource,
    addr: Address,
    journal_reads: Map<Address, RawPage>,
    cache_reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        inv(pre),
        pre.superblock_loaded(),
        pre.journal.ready(),
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.in_flight == pre.in_flight,
        post.in_flight_image == pre.in_flight_image,
        journal_reads.contains_key(addr),
        journal_reads <= cache_reads,
        writes.dom().disjoint(addresses_in_aus(pre.journal_projection_aus())),
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access{reads: cache_reads, writes},
        ),
        AtomicJournalState::State::next(
            pre.journal,
            post.journal,
            AtomicJournalState::Label::ReadForRecovery{
                messages: to_journal_records(journal_reads)[addr].message_seq.maybe_discard_old(
                    pre.journal.journal.snapshot.boundary_lsn,
                ),
                reads: to_journal_records(journal_reads),
            },
        ),
    ensures
        CrashAwareCachingDiskJournal::State::next(
            unified_cache_journal_i(pre),
            unified_cache_journal_i(post),
            CrashAwareCachingDiskJournal::Label::ReadForRecovery{
                records: to_journal_records(journal_reads)[addr].message_seq.maybe_discard_old(
                    pre.journal.journal.snapshot.boundary_lsn,
                ),
            },
        ),
        to_journal_records(journal_reads)[addr].message_seq.maybe_discard_old(
            pre.journal.journal.snapshot.boundary_lsn,
        ).wf(),
        post.journal == pre.journal,
        post.journal_projection_aus() =~= pre.journal_projection_aus(),
        inv(post),
{
    let records = to_journal_records(journal_reads)[addr].message_seq.maybe_discard_old(
        pre.journal.journal.snapshot.boundary_lsn,
    );
    let cache_lbl = Cache::Label::Access{reads: cache_reads, writes};
    let atomic_lbl = AtomicJournalState::Label::ReadForRecovery{
        messages: records,
        reads: to_journal_records(journal_reads),
    };

    AtomicJournalState::State::wf_next(pre.journal, post.journal, atomic_lbl);
    reveal(AtomicJournalState::State::next);
    reveal(AtomicJournalState::State::next_by);
    let atomic_step = choose |step: AtomicJournalState::Step|
        AtomicJournalState::State::next_by(pre.journal, post.journal, atomic_lbl, step);
    match atomic_step {
        AtomicJournalState::Step::read_for_recovery(new_journal) => {
            assert(AtomicJournalState::State::read_for_recovery(
                pre.journal,
                post.journal,
                atomic_lbl,
                new_journal,
            )) by {
                reveal(AtomicJournalState::State::read_for_recovery);
            }
            reveal(AtomicJournalState::State::read_for_recovery);
            let full_cj_lbl = CachedJournal::Label::ReadForRecovery{
                messages: records,
                reads: to_journal_records(journal_reads),
            };
            assert(CachedJournal::State::next(
                pre.journal.journal,
                new_journal,
                full_cj_lbl,
            ));

            reveal(CachedJournal::State::next);
            reveal(CachedJournal::State::next_by);
            let cj_step = choose |step: CachedJournal::Step|
                CachedJournal::State::next_by(
                    pre.journal.journal,
                    new_journal,
                    full_cj_lbl,
                    step,
                );
            match cj_step {
                CachedJournal::Step::read_for_recovery(start_lsn, read_addr) => {
                    assert(CachedJournal::State::read_for_recovery(
                        pre.journal.journal,
                        new_journal,
                        full_cj_lbl,
                        start_lsn,
                        read_addr,
                    )) by {
                        reveal(CachedJournal::State::read_for_recovery);
                    }
                    reveal(CachedJournal::State::read_for_recovery);
                    assert(new_journal == pre.journal.journal);
                    assert(post.journal.journal == pre.journal.journal);
                    assert(post.journal.mini_allocator == pre.journal.mini_allocator);
                    assert(post.journal.persistent_seq_end == pre.journal.persistent_seq_end);
                    assert(post.journal.in_flight == pre.journal.in_flight);
                    assert(post.journal.prepared == pre.journal.prepared);
                    assert(post.journal == pre.journal);

                    let full_reads = to_journal_records(journal_reads);
                    assert(full_reads.contains_key(read_addr));
                    assert(journal_reads.contains_key(read_addr));
                    assert(cache_reads.contains_key(read_addr));
                    assert(cache_reads[read_addr] == journal_reads[read_addr]);

                    let index = pre.journal.journal.status.unwrap().lsn_au_index;
                    assert(index.contains_key(start_lsn));
                    assert(index[start_lsn] == read_addr.au);
                    assert(index.values().contains(read_addr.au));
                    assert(pre.journal.journal.status.unwrap().au_page_bounds.contains_key(read_addr.au));
                    assert(read_addr.page
                        <= pre.journal.journal.status.unwrap().au_page_bounds[read_addr.au]);
                    assert(pre.journal.loaded_index_aus().contains(read_addr.au));
                    assert(pre.journal_projection_aus().contains(read_addr.au));
                    assert(addresses_in_aus(pre.journal_projection_aus()).contains(read_addr));

                    Cache::State::access_read_valid(
                        pre.cache,
                        post.cache,
                        cache_reads,
                        writes,
                        read_addr,
                    );
                    pre.cache.build_lookup_map_ensures();
                    assert(cache_filled_addr(pre.cache, read_addr));
                    assert(cache_filled_page(pre.cache, read_addr) == cache_reads[read_addr]);
                    assert(project_cache_pages(pre.cache, pre.journal_projection_aus()).contains_key(read_addr));
                    assert(pre.journal_caching_disk_i().cache.contains_key(read_addr));
                    assert(pre.journal_caching_disk_i().cache[read_addr] == cache_reads[read_addr]);

                    let raw_journal_reads = Map::<Address, RawPage>::empty().insert(
                        read_addr,
                        cache_reads[read_addr],
                    );
                    let restricted_reads = to_journal_records(raw_journal_reads);
                    let restricted_cj_lbl = CachedJournal::Label::ReadForRecovery{
                        messages: records,
                        reads: restricted_reads,
                    };
                    let disk_lbl = CachingDisk::Label::Access{
                        reads: raw_journal_reads,
                        writes: Map::<Address, RawPage>::empty(),
                    };
                    let empty_raw_writes = Map::<Address, RawPage>::empty();
                    let empty_status_updates = status_map(
                        empty_raw_writes.dom(),
                        PageStatus::Dirty,
                    );
                    assert(empty_status_updates == Map::<Address, PageStatus>::empty()) by {
                        assert_maps_equal!(
                            empty_status_updates,
                            Map::<Address, PageStatus>::empty(),
                            status_addr => {}
                        );
                    }
                    assert(pre.journal_caching_disk_i().cache.union_prefer_right(empty_raw_writes)
                        == pre.journal_caching_disk_i().cache) by {
                        assert_maps_equal!(
                            pre.journal_caching_disk_i().cache.union_prefer_right(empty_raw_writes),
                            pre.journal_caching_disk_i().cache,
                            cache_addr => {}
                        );
                    }
                    assert(pre.journal_caching_disk_i().status.union_prefer_right(empty_status_updates)
                        == pre.journal_caching_disk_i().status) by {
                        assert_maps_equal!(
                            pre.journal_caching_disk_i().status.union_prefer_right(empty_status_updates),
                            pre.journal_caching_disk_i().status,
                            status_addr => {}
                        );
                    }
                    assert(CachingDisk::State::access(
                        pre.journal_caching_disk_i(),
                        pre.journal_caching_disk_i(),
                        disk_lbl,
                    )) by {
                        reveal(CachingDisk::State::access);
                    }
                    assert(CachingDisk::State::next_by(
                        pre.journal_caching_disk_i(),
                        pre.journal_caching_disk_i(),
                        disk_lbl,
                        CachingDisk::Step::access(),
                    )) by {
                        reveal(CachingDisk::State::next_by);
                    }
                    reveal(CachingDisk::State::next);

                    assert(restricted_reads.contains_key(read_addr));
                    assert(restricted_reads[read_addr] == full_reads[read_addr]);
                    assert(restricted_reads[read_addr].message_seq == full_reads[read_addr].message_seq);
                    assert(CachedJournal::State::read_for_recovery(
                        pre.journal.journal,
                        pre.journal.journal,
                        restricted_cj_lbl,
                        start_lsn,
                        read_addr,
                    ));
                    assert(CachedJournal::State::next_by(
                        pre.journal.journal,
                        pre.journal.journal,
                        restricted_cj_lbl,
                        CachedJournal::Step::read_for_recovery(start_lsn, read_addr),
                    )) by {
                        reveal(CachedJournal::State::next_by);
                    }
                    reveal(CachedJournal::State::next);

                    let src = pre.i();
                    let inner = src.ephemeral->v;
                    assert(src.ephemeral is Known);
                    assert(inner == pre.journal_caching_disk_state_i());
                    assert forall |read: Address| #[trigger] raw_journal_reads.contains_key(read) implies {
                        &&& inner.au_page_bounds_i().contains_key(read.au)
                        &&& read.page <= inner.au_page_bounds_i()[read.au]
                    } by {
                        assert(read == read_addr);
                        assert(inner.au_page_bounds_i()
                            == pre.journal.journal.status.unwrap().au_page_bounds);
                    }
                    let cdj_lbl = CachingDiskJournal::Label::ReadForRecovery{messages: records};
                    assert(CachingDiskJournal::State::read_for_recovery(
                        inner,
                        inner,
                        cdj_lbl,
                        raw_journal_reads,
                    )) by {
                        reveal(CachingDiskJournal::State::read_for_recovery);
                    }
                    assert(CachingDiskJournal::State::next_by(
                        inner,
                        inner,
                        cdj_lbl,
                        CachingDiskJournal::Step::read_for_recovery(raw_journal_reads),
                    )) by {
                        reveal(CachingDiskJournal::State::next_by);
                    }
                    reveal(CachingDiskJournal::State::next);
                    assert(inner.refinement_inv());
                    inner.read_for_recovery_refines(inner, cdj_lbl, raw_journal_reads);
                    assert(records.wf());
                },
                _ => {
                    assert(false);
                },
            }
        },
        _ => {
            assert(false);
        },
    }

    assert(post.journal == pre.journal);
    assert(post.journal_projection_aus() =~= pre.journal_projection_aus());
    pre.inv_preserved_by_cache_access_outside_journal_projection(post, cache_reads, writes);
    assert(post.persistent_journal_i() == pre.persistent_journal_i());
    pre.journal_interpretation_unchanged_by_same_projection(post);
    assert(post.i() == pre.i());

    let src = pre.i();
    let dst = post.i();
    let lbl = CrashAwareCachingDiskJournal::Label::ReadForRecovery{records};
    assert(src == dst);
    assert(CrashAwareCachingDiskJournal::State::read_for_recovery(src, dst, lbl)) by {
        reveal(CrashAwareCachingDiskJournal::State::read_for_recovery);
    }
    assert(CrashAwareCachingDiskJournal::State::next_by(
        src,
        dst,
        lbl,
        CrashAwareCachingDiskJournal::Step::read_for_recovery(),
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::next_by);
    }
    reveal(CrashAwareCachingDiskJournal::State::next);
    assert(post.semantic_inv());
    assert(inv(post));
}

pub proof fn observe_clean_aus_refines(
    pre: UnifiedCacheJournalSource,
    post: UnifiedCacheJournalSource,
    aus: Set<AU>,
)
    requires
        inv(pre),
        pre.superblock_loaded(),
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.in_flight == pre.in_flight,
        post.in_flight_image == pre.in_flight_image,
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::EvictableCheck{aus},
        ),
        AtomicJournalState::State::next(
            pre.journal,
            post.journal,
            AtomicJournalState::Label::ObserveCleanAUs{aus},
        ),
    ensures
        CrashAwareCachingDiskJournal::State::next(
            unified_cache_journal_i(pre),
            unified_cache_journal_i(post),
            CrashAwareCachingDiskJournal::Label::ObserveCleanAUs{aus},
        ),
        post.cache == pre.cache,
        post.journal_projection_aus() =~= pre.journal_projection_aus(),
        post.journal.ready(),
        post.journal.persistent_seq_end == pre.journal.persistent_seq_end,
        post.journal.in_flight == pre.journal.in_flight,
        post.journal.prepared == pre.journal.prepared,
        post.journal.journal.seq_end() == pre.journal.journal.seq_end(),
        inv(post),
{
    let atomic_lbl = AtomicJournalState::Label::ObserveCleanAUs{aus};
    let cache_lbl = Cache::Label::EvictableCheck{aus};

    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let cache_step = choose |step: Cache::Step|
        Cache::State::next_by(pre.cache, post.cache, cache_lbl, step);
    match cache_step {
        Cache::Step::evictable() => {
            reveal(Cache::State::evictable);
            assert(post.cache == pre.cache);
        },
        _ => {
            assert(false);
        },
    }

    AtomicJournalState::State::wf_next(pre.journal, post.journal, atomic_lbl);
    reveal(AtomicJournalState::State::next);
    reveal(AtomicJournalState::State::next_by);
    let atomic_step = choose |step: AtomicJournalState::Step|
        AtomicJournalState::State::next_by(pre.journal, post.journal, atomic_lbl, step);
    match atomic_step {
        AtomicJournalState::Step::observe_clean_aus(new_journal) => {
            assert(AtomicJournalState::State::observe_clean_aus(
                pre.journal,
                post.journal,
                atomic_lbl,
                new_journal,
            )) by {
                reveal(AtomicJournalState::State::observe_clean_aus);
            }
            assert(post.journal.journal == new_journal);
            assert(post.journal.mini_allocator == pre.journal.mini_allocator);
            assert(post.journal.persistent_seq_end == pre.journal.persistent_seq_end);
            assert(post.journal.in_flight == pre.journal.in_flight);
            assert(post.journal.prepared == pre.journal.prepared);
            CachedJournal::State::observe_clean_aus_effect(
                pre.journal.journal,
                post.journal.journal,
                aus,
            );
            assert(post.journal.loaded_index_aus() == pre.journal.loaded_index_aus());
            assert(post.journal.owned_aus() =~= pre.journal.owned_aus());
            assert(post.journal.journal.seq_end() == pre.journal.journal.seq_end());
        },
        _ => {
            assert(false);
        },
    }

    assert(post.superblock_loaded());
    assert(post.persistent_superblock_image_i() == pre.persistent_superblock_image_i());
    assert(post.journal_projection_aus() =~= pre.journal_projection_aus()) by {
        assert(pre.journal.ready());
        assert(post.journal.ready());
        assert(pre.journal_projection_aus() == pre.journal.owned_aus());
        assert(post.journal_projection_aus() == post.journal.owned_aus());
    }
    assert(post.journal_caching_disk_i() == pre.journal_caching_disk_i()) by {
        assert_maps_equal!(
            post.journal_caching_disk_i().cache,
            pre.journal_caching_disk_i().cache,
            addr => {}
        );
        assert_maps_equal!(
            post.journal_caching_disk_i().status,
            pre.journal_caching_disk_i().status,
            addr => {}
        );
        assert_maps_equal!(
            post.journal_caching_disk_i().persistent,
            pre.journal_caching_disk_i().persistent,
            addr => {}
        );
    }

    cache_evictable_refines_observe_clean_aus(
        pre.cache,
        pre.disk,
        pre.journal_projection_aus(),
        aus,
    );
    assert(CachingDisk::State::next(
        pre.journal_caching_disk_i(),
        pre.journal_caching_disk_i(),
        CachingDisk::Label::ObserveCleanAUs{aus},
    ));
    assert(CachingDiskJournal::State::observe_clean_aus(
        pre.journal_caching_disk_state_i(),
        post.journal_caching_disk_state_i(),
        CachingDiskJournal::Label::ObserveCleanAUs{aus},
        post.journal.journal,
    )) by {
        reveal(CachingDiskJournal::State::observe_clean_aus);
    }
    assert(CachingDiskJournal::State::next_by(
        pre.journal_caching_disk_state_i(),
        post.journal_caching_disk_state_i(),
        CachingDiskJournal::Label::ObserveCleanAUs{aus},
        CachingDiskJournal::Step::observe_clean_aus(post.journal.journal),
    )) by {
        reveal(CachingDiskJournal::State::next_by);
    }
    reveal(CachingDiskJournal::State::next);

    let src = unified_cache_journal_i(pre);
    let dst = unified_cache_journal_i(post);
    let target_lbl = CrashAwareCachingDiskJournal::Label::ObserveCleanAUs{aus};
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(CrashAwareCachingDiskJournal::State::observe_clean_aus(
        src,
        dst,
        target_lbl,
        post.journal_caching_disk_state_i(),
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::observe_clean_aus);
    }
    assert(CrashAwareCachingDiskJournal::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskJournal::Step::observe_clean_aus(
            post.journal_caching_disk_state_i(),
        ),
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::next_by);
    }
    reveal(CrashAwareCachingDiskJournal::State::next);
    src.next_refines(dst, target_lbl);

    assert(post.inv()) by {
        assert(post.journal.wf());
        assert(async_disk_superblock_page_wf(post.disk.content));
        assert(post.persistent_superblock_image_i().wf());
        assert(post.cache.inv()) by {
            Cache::State::inv_next(pre.cache, post.cache, cache_lbl);
        }
        assert(post.disk.inv());
        assert(post.journal_caching_disk_i().inv());
        assert(post.journal.persistent_seq_end
            == post.persistent_superblock_image_i().journal_seq_end);
        assert(post.in_flight is Some <==> post.journal.in_flight is Some);
        assert(post.in_flight is Some <==> post.in_flight_image is Some);
    }
    assert(post.semantic_inv());
    assert(inv(post));
}

pub proof fn journal_marshal_refines(
    pre: UnifiedCacheJournalSource,
    post: UnifiedCacheJournalSource,
    addr: Address,
    raw_page: RawPage,
)
    requires
        inv(pre),
        pre.superblock_loaded(),
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.in_flight == pre.in_flight,
        post.in_flight_image == pre.in_flight_image,
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access{
                reads: Map::empty(),
                writes: Map::<Address, RawPage>::empty().insert(addr, raw_page),
            },
        ),
        AtomicJournalState::State::next(
            pre.journal,
            post.journal,
            AtomicJournalState::Label::JournalMarshal{
                addr,
                writes: to_journal_records(
                    Map::<Address, RawPage>::empty().insert(addr, raw_page),
                ),
            },
        ),
    ensures
        CrashAwareCachingDiskJournal::State::next(
            unified_cache_journal_i(pre),
            unified_cache_journal_i(post),
            CrashAwareCachingDiskJournal::Label::Internal,
        ),
        addr.wf(),
        pre.journal_projection_aus().contains(addr.au),
        post.journal.ready(),
        post.journal.persistent_seq_end == pre.journal.persistent_seq_end,
        post.journal.in_flight == pre.journal.in_flight,
        post.journal.prepared == pre.journal.prepared,
        post.journal.journal.seq_end() == pre.journal.journal.seq_end(),
        inv(post),
{
    let writes = Map::<Address, RawPage>::empty().insert(addr, raw_page);
    let cache_lbl = Cache::Label::Access{reads: Map::empty(), writes};
    let atomic_lbl = AtomicJournalState::Label::JournalMarshal{
        addr,
        writes: to_journal_records(writes),
    };

    AtomicJournalState::State::wf_next(pre.journal, post.journal, atomic_lbl);
    Cache::State::inv_next(pre.cache, post.cache, cache_lbl);

    reveal(AtomicJournalState::State::next);
    reveal(AtomicJournalState::State::next_by);
    let atomic_step = choose |step: AtomicJournalState::Step|
        AtomicJournalState::State::next_by(pre.journal, post.journal, atomic_lbl, step);
    match atomic_step {
        AtomicJournalState::Step::journal_marshal(new_journal) => {
            assert(AtomicJournalState::State::journal_marshal(
                pre.journal,
                post.journal,
                atomic_lbl,
                new_journal,
            )) by {
                reveal(AtomicJournalState::State::journal_marshal);
            }
            assert(post.journal.journal == new_journal);
            assert(post.journal.mini_allocator
                == pre.journal.mini_allocator.allocate(addr));
            assert(post.journal.persistent_seq_end == pre.journal.persistent_seq_end);
            assert(post.journal.in_flight == pre.journal.in_flight);
            assert(post.journal.prepared == pre.journal.prepared);
            assert(pre.journal.mini_allocator.tight_next_addr(
                pre.journal.journal.snapshot.freshest_rec(),
                addr,
            ));
            assert(pre.journal.mini_allocator.can_allocate(addr));
        },
        _ => {
            assert(false);
        },
    }

    assert(pre.journal.ready());
    assert(post.superblock_loaded());
    assert(post.persistent_superblock_image_i() == pre.persistent_superblock_image_i());
    assert(writes.dom() =~= Set::new(|a: Address| a == addr));
    assert(writes.dom() <= addresses_in_aus(pre.journal_projection_aus())) by {
        assert(pre.journal_projection_aus() == pre.journal.owned_aus());
        assert(pre.journal.mini_allocator.all_aus().contains(addr.au));
        assert(pre.journal.owned_aus().contains(addr.au));
        assert forall |a: Address| #[trigger] writes.contains_key(a)
            implies addresses_in_aus(pre.journal_projection_aus()).contains(a) by {
            assert(a == addr);
        }
    }

    reveal(CachedJournal::State::next);
    reveal(CachedJournal::State::next_by);
    let journal_lbl = CachedJournal::Label::JournalMarshal{
        writes: to_journal_records(writes),
    };
    CachedJournal::State::status_some_next_effect(
        pre.journal.journal,
        post.journal.journal,
        journal_lbl,
    );
    assert(post.journal.ready());
    let journal_step = choose |step: CachedJournal::Step|
        CachedJournal::State::next_by(pre.journal.journal, post.journal.journal, journal_lbl, step);
    match journal_step {
        CachedJournal::Step::internal_journal_marshal(cut, hidden_addr) => {
            reveal(CachedJournal::State::internal_journal_marshal);
            assert(hidden_addr == addr) by {
                assert(to_journal_records(writes).contains_key(hidden_addr));
                assert(writes.contains_key(hidden_addr));
                assert(writes.contains_key(addr));
            }
            let marshalled_msgs =
                pre.journal.journal.status.unwrap().unmarshalled_tail.discard_recent(cut);
            CachingDiskJournal::State::lsn_au_index_append_record_values_subset(
                cj_lsn_au_index(pre.journal.journal),
                marshalled_msgs,
                addr.au,
            );
            assert(post.journal.journal.status.unwrap().unmarshalled_tail.seq_end
                == pre.journal.journal.status.unwrap().unmarshalled_tail.seq_end);
            assert(post.journal.journal.seq_end() == pre.journal.journal.seq_end());
        },
        _ => {
            assert(false);
        },
    }

    let old_cdj_for_index = pre.journal_caching_disk_state_i();
    assert(old_cdj_for_index.semantic_inv()) by {
        let src = unified_cache_journal_i(pre);
        assert(src.refinement_inv());
        assert(src.ephemeral is Known);
        assert(src.ephemeral->v == old_cdj_for_index);
    }
    old_cdj_for_index.cached_journal_marshal_preserves_loaded_index_values(
        post.journal.journal,
        addr,
        writes,
    );
    crate::implementation::CachingDiskJournal_v::mini_allocator_allocate_preserves_all_aus(
        pre.journal.mini_allocator,
        addr,
    );
    assert(post.journal.mini_allocator.all_aus()
        == pre.journal.mini_allocator.all_aus()) by {
        assert(pre.journal.mini_allocator.allocate(addr).all_aus()
            == pre.journal.mini_allocator.all_aus());
        assert forall |au: AU| #[trigger] post.journal.mini_allocator.all_aus().contains(au)
            <==> pre.journal.mini_allocator.all_aus().contains(au) by { }
    }
    assert(post.journal.loaded_index_aus() <= pre.journal.loaded_index_aus().insert(addr.au)) by {
        assert forall |au: AU| #[trigger] post.journal.loaded_index_aus().contains(au)
            implies pre.journal.loaded_index_aus().insert(addr.au).contains(au) by {
            assert(cj_lsn_au_index(post.journal.journal).values().contains(au));
        }
    }
    assert(pre.journal_projection_aus().contains(addr.au)) by {
        assert(writes.dom().contains(addr));
        assert(addresses_in_aus(pre.journal_projection_aus()).contains(addr));
    }
    assert(post.journal_projection_aus() =~= pre.journal_projection_aus()) by {
        assert(pre.journal_projection_aus() == pre.journal.owned_aus());
        assert(post.journal_projection_aus() == post.journal.owned_aus());
        assert(pre.journal.owned_aus() == pre.journal.loaded_index_aus()
            + pre.journal.mini_allocator.all_aus());
        assert(post.journal.owned_aus() == post.journal.loaded_index_aus()
            + post.journal.mini_allocator.all_aus());
        assert(pre.journal.mini_allocator.all_aus().contains(addr.au));
        assert forall |au: AU| #[trigger] post.journal_projection_aus().contains(au)
            implies pre.journal_projection_aus().contains(au) by {
            if post.journal.loaded_index_aus().contains(au) {
                assert(pre.journal.loaded_index_aus().insert(addr.au).contains(au));
            }
        }
        assert forall |au: AU| #[trigger] pre.journal_projection_aus().contains(au)
            implies post.journal_projection_aus().contains(au) by {
            if pre.journal.loaded_index_aus().contains(au) {
                assert(cj_lsn_au_index(pre.journal.journal).values().contains(au));
                assert(cj_lsn_au_index(post.journal.journal).values().contains(au));
            }
        }
    }

    cache_access_refines_caching_disk_access(
        pre.cache,
        post.cache,
        pre.disk,
        pre.journal_projection_aus(),
        Map::empty(),
        writes,
    );
    assert(CachingDisk::State::next(
        pre.journal_caching_disk_i(),
        post.journal_caching_disk_i(),
        CachingDisk::Label::Access{reads: Map::empty(), writes},
    )) by {
        assert(pre.journal_caching_disk_i()
            == adapter_caching_disk_i(pre.cache, pre.disk, pre.journal_projection_aus()));
        assert(post.journal_caching_disk_i()
            == adapter_caching_disk_i(post.cache, post.disk, pre.journal_projection_aus())) by {
            assert(post.journal_projection_aus() =~= pre.journal_projection_aus());
        }
    }

    let old_cdj = pre.journal_caching_disk_state_i();
    let new_cdj = post.journal_caching_disk_state_i();
    let cdj_lbl = CachingDiskJournal::Label::Internal;
    assert(old_cdj.mini_allocator.tight_next_addr(old_cdj.journal.snapshot.freshest_rec(), addr));
    assert(CachingDiskJournal::State::journal_marshal(
        old_cdj,
        new_cdj,
        cdj_lbl,
        post.journal.journal,
        post.journal_caching_disk_i(),
        addr,
        writes,
    )) by {
        reveal(CachingDiskJournal::State::journal_marshal);
        assert(to_journal_records(writes).dom() =~= writes.dom()) by {
            assert forall |a: Address| #[trigger] to_journal_records(writes).contains_key(a)
                <==> writes.contains_key(a) by { }
        }
        assert(cj_lsn_au_index(old_cdj.journal).values()
            <= cj_lsn_au_index(post.journal.journal).values());
    }
    assert(CachingDiskJournal::State::next_by(
        old_cdj,
        new_cdj,
        cdj_lbl,
        CachingDiskJournal::Step::journal_marshal(
            post.journal.journal,
            post.journal_caching_disk_i(),
            addr,
            writes,
        ),
    )) by {
        reveal(CachingDiskJournal::State::next_by);
    }
    reveal(CachingDiskJournal::State::next);

    let src = unified_cache_journal_i(pre);
    let dst = unified_cache_journal_i(post);
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(CrashAwareCachingDiskJournal::State::internal(
        src,
        dst,
        CrashAwareCachingDiskJournal::Label::Internal,
        new_cdj,
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::internal);
    }
    assert(CrashAwareCachingDiskJournal::State::next_by(
        src,
        dst,
        CrashAwareCachingDiskJournal::Label::Internal,
        CrashAwareCachingDiskJournal::Step::internal(new_cdj),
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::next_by);
    }
    reveal(CrashAwareCachingDiskJournal::State::next);
    src.next_refines(dst, CrashAwareCachingDiskJournal::Label::Internal);

    assert(post.inv()) by {
        assert(post.journal.wf());
        assert(async_disk_superblock_page_wf(post.disk.content));
        assert(post.persistent_superblock_image_i().wf());
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.journal_caching_disk_i().inv());
        assert(post.journal.persistent_seq_end
            == post.persistent_superblock_image_i().journal_seq_end);
        assert(post.in_flight is Some <==> post.journal.in_flight is Some);
        assert(post.in_flight is Some <==> post.in_flight_image is Some);
    }
    assert(post.semantic_inv());
    assert(inv(post));
}

pub proof fn fill_aus_refines(
    pre: UnifiedCacheJournalSource,
    post: UnifiedCacheJournalSource,
    aus: Set<AU>,
)
    requires
        inv(pre),
        pre.superblock_loaded(),
        pre.journal.ready(),
        post.cache == pre.cache,
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.in_flight == pre.in_flight,
        post.in_flight_image == pre.in_flight_image,
        aus.disjoint(pre.journal_projection_aus()),
        pre.journal_fill_aus_shared_projection_inv(aus),
        AtomicJournalState::State::next(
            pre.journal,
            post.journal,
            AtomicJournalState::Label::FillAUs{aus},
        ),
    ensures
        CrashAwareCachingDiskJournal::State::next(
            unified_cache_journal_i(pre),
            unified_cache_journal_i(post),
            CrashAwareCachingDiskJournal::Label::InternalAlloc{
                allocs: aus,
                deallocs: Set::empty(),
                prune_aus: Set::empty(),
            },
        ),
        post.journal_projection_aus() =~= pre.journal_projection_aus() + aus,
        post.journal.ready(),
        post.journal.journal == pre.journal.journal,
        post.journal.persistent_seq_end == pre.journal.persistent_seq_end,
        post.journal.in_flight == pre.journal.in_flight,
        post.journal.prepared == pre.journal.prepared,
        inv(post),
{
    let atomic_lbl = AtomicJournalState::Label::FillAUs{aus};
    AtomicJournalState::State::wf_next(pre.journal, post.journal, atomic_lbl);
    reveal(AtomicJournalState::State::next);
    reveal(AtomicJournalState::State::next_by);
    let atomic_step = choose |step: AtomicJournalState::Step|
        AtomicJournalState::State::next_by(pre.journal, post.journal, atomic_lbl, step);
    match atomic_step {
        AtomicJournalState::Step::fill_aus() => {
            assert(AtomicJournalState::State::fill_aus(
                pre.journal,
                post.journal,
                atomic_lbl,
            )) by {
                reveal(AtomicJournalState::State::fill_aus);
            }
            assert(post.journal.journal == pre.journal.journal);
            assert(post.journal.mini_allocator == pre.journal.mini_allocator.add_aus(aus));
            assert(post.journal.persistent_seq_end == pre.journal.persistent_seq_end);
            assert(post.journal.in_flight == pre.journal.in_flight);
            assert(post.journal.prepared == pre.journal.prepared);
        },
        _ => {
            assert(false);
        },
    }

    assert(post.superblock_loaded());
    assert(post.persistent_superblock_image_i() == pre.persistent_superblock_image_i());
    assert(post.journal.ready());
    crate::implementation::CachingDiskJournal_v::mini_allocator_add_aus_preserves_all_aus(
        pre.journal.mini_allocator,
        aus,
    );
    assert(post.journal.loaded_index_aus() == pre.journal.loaded_index_aus());
    assert(post.journal.owned_aus() =~= pre.journal.owned_aus() + aus);
    assert(post.journal_projection_aus() =~= pre.journal_projection_aus() + aus) by {
        assert(pre.journal_projection_aus() == pre.journal.owned_aus());
        assert(post.journal_projection_aus() == post.journal.owned_aus());
    }

    let empty = Set::<AU>::empty();
    let target_lbl = CrashAwareCachingDiskJournal::Label::InternalAlloc{
        allocs: aus,
        deallocs: empty,
        prune_aus: empty,
    };
    let cdj_lbl = CachingDiskJournal::Label::InternalAlloc{
        allocs: aus,
        deallocs: empty,
        prune_aus: empty,
    };
    let old_cdj = pre.journal_caching_disk_state_i();
    let new_cdj = post.journal_caching_disk_state_i();
    assert(new_cdj.disk == pre.caching_disk_i_for_aus(pre.journal_projection_aus() + aus)) by {
        assert(post.cache == pre.cache);
        assert(post.disk == pre.disk);
        assert(post.journal_projection_aus() =~= pre.journal_projection_aus() + aus);
        assert_maps_equal!(
            new_cdj.disk.cache,
            pre.caching_disk_i_for_aus(pre.journal_projection_aus() + aus).cache,
            addr => {}
        );
        assert_maps_equal!(
            new_cdj.disk.status,
            pre.caching_disk_i_for_aus(pre.journal_projection_aus() + aus).status,
            addr => {}
        );
        assert_maps_equal!(
            new_cdj.disk.persistent,
            pre.caching_disk_i_for_aus(pre.journal_projection_aus() + aus).persistent,
            addr => {}
        );
    }
    assert(old_cdj.journal.status is Some);
    assert(aus.disjoint(old_cdj.mini_allocator.all_aus())) by {
        assert(pre.journal_projection_aus() == pre.journal.owned_aus());
        assert forall |au: AU| #[trigger] aus.contains(au)
            implies !old_cdj.mini_allocator.all_aus().contains(au) by {
            assert(pre.journal.owned_aus().contains(au) ==> false) by {
                if pre.journal.owned_aus().contains(au) {
                    assert(pre.journal_projection_aus().contains(au));
                    assert(false);
                }
            }
        }
    }
    assert(aus.disjoint(cj_lsn_au_index(old_cdj.journal).values())) by {
        assert(pre.journal_projection_aus() == pre.journal.owned_aus());
        assert forall |au: AU| #[trigger] aus.contains(au)
            implies !cj_lsn_au_index(old_cdj.journal).values().contains(au) by {
            if cj_lsn_au_index(old_cdj.journal).values().contains(au) {
                assert(pre.journal.loaded_index_aus().contains(au));
                assert(pre.journal.owned_aus().contains(au));
                assert(pre.journal_projection_aus().contains(au));
                assert(false);
            }
        }
    }
    assert(new_cdj.disk.inv());
    assert(old_cdj.disk.cache <= new_cdj.disk.cache) by {
        assert forall |addr: Address| #[trigger] old_cdj.disk.cache.contains_key(addr)
            implies new_cdj.disk.cache.contains_key(addr)
                && new_cdj.disk.cache[addr] == old_cdj.disk.cache[addr] by {
            assert(addresses_in_aus(pre.journal_projection_aus()).contains(addr));
            assert(addresses_in_aus(post.journal_projection_aus()).contains(addr));
        }
    }
    assert(old_cdj.disk.persistent <= new_cdj.disk.persistent) by {
        assert forall |addr: Address| #[trigger] old_cdj.disk.persistent.contains_key(addr)
            implies new_cdj.disk.persistent.contains_key(addr)
                && new_cdj.disk.persistent[addr] == old_cdj.disk.persistent[addr] by {
            assert(addresses_in_aus(pre.journal_projection_aus()).contains(addr));
            assert(addresses_in_aus(post.journal_projection_aus()).contains(addr));
        }
    }
    assert(old_cdj.disk.status <= new_cdj.disk.status) by {
        assert forall |addr: Address| #[trigger] old_cdj.disk.status.contains_key(addr)
            implies new_cdj.disk.status.contains_key(addr)
                && new_cdj.disk.status[addr] == old_cdj.disk.status[addr] by {
            assert(addresses_in_aus(pre.journal_projection_aus()).contains(addr));
            assert(addresses_in_aus(post.journal_projection_aus()).contains(addr));
        }
    }
    assert(new_cdj.disk.cache.dom() <= addresses_in_aus(
        cj_lsn_au_index(old_cdj.journal).values() + old_cdj.mini_allocator.all_aus() + aus,
    )) by {
        assert(post.journal_projection_aus() =~=
            cj_lsn_au_index(old_cdj.journal).values() + old_cdj.mini_allocator.all_aus() + aus);
    }
    assert(new_cdj.disk.persistent.dom() <= addresses_in_aus(
        cj_lsn_au_index(old_cdj.journal).values() + old_cdj.mini_allocator.all_aus() + aus,
    )) by {
        assert(post.journal_projection_aus() =~=
            cj_lsn_au_index(old_cdj.journal).values() + old_cdj.mini_allocator.all_aus() + aus);
    }
    assert(new_cdj.disk.status.dom() <= addresses_in_aus(
        cj_lsn_au_index(old_cdj.journal).values() + old_cdj.mini_allocator.all_aus() + aus,
    )) by {
        assert(post.journal_projection_aus() =~=
            cj_lsn_au_index(old_cdj.journal).values() + old_cdj.mini_allocator.all_aus() + aus);
    }
    assert(new_cdj.disk.cache.dom() - old_cdj.disk.cache.dom() <= addresses_in_aus(aus)) by {
        assert forall |addr: Address| #[trigger] (new_cdj.disk.cache.dom() - old_cdj.disk.cache.dom()).contains(addr)
            implies addresses_in_aus(aus).contains(addr) by {
            assert(addresses_in_aus(post.journal_projection_aus()).contains(addr));
            if !addresses_in_aus(aus).contains(addr) {
                assert(addresses_in_aus(pre.journal_projection_aus()).contains(addr));
                assert(old_cdj.disk.cache.contains_key(addr));
                assert(false);
            }
        }
    }
    assert(new_cdj.disk.persistent.dom() - old_cdj.disk.persistent.dom() <= addresses_in_aus(aus)) by {
        assert forall |addr: Address| #[trigger] (new_cdj.disk.persistent.dom() - old_cdj.disk.persistent.dom()).contains(addr)
            implies addresses_in_aus(aus).contains(addr) by {
            assert(addresses_in_aus(post.journal_projection_aus()).contains(addr));
            if !addresses_in_aus(aus).contains(addr) {
                assert(addresses_in_aus(pre.journal_projection_aus()).contains(addr));
                assert(old_cdj.disk.persistent.contains_key(addr));
                assert(false);
            }
        }
    }
    assert(new_cdj.disk.status.dom() - old_cdj.disk.status.dom() <= addresses_in_aus(aus)) by {
        assert forall |addr: Address| #[trigger] (new_cdj.disk.status.dom() - old_cdj.disk.status.dom()).contains(addr)
            implies addresses_in_aus(aus).contains(addr) by {
            assert(addresses_in_aus(post.journal_projection_aus()).contains(addr));
            if !addresses_in_aus(aus).contains(addr) {
                assert(addresses_in_aus(pre.journal_projection_aus()).contains(addr));
                assert(old_cdj.disk.status.contains_key(addr));
                assert(false);
            }
        }
    }
    assert(new_cdj.disk.cache.dom() <= Set::new(|addr: Address| addr.wf()));
    assert(new_cdj.disk.persistent.dom() <= Set::new(|addr: Address| addr.wf()));
    assert(CachingDiskJournal::State::mini_allocator_fill(
        old_cdj,
        new_cdj,
        cdj_lbl,
        new_cdj.disk,
    )) by {
        reveal(CachingDiskJournal::State::mini_allocator_fill);
    }
    assert(CachingDiskJournal::State::next_by(
        old_cdj,
        new_cdj,
        cdj_lbl,
        CachingDiskJournal::Step::mini_allocator_fill(new_cdj.disk),
    )) by {
        reveal(CachingDiskJournal::State::next_by);
    }
    reveal(CachingDiskJournal::State::next);

    let src = unified_cache_journal_i(pre);
    let dst = unified_cache_journal_i(post);
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(aus.disjoint(caching_disk_journal_accessible_aus(src.ephemeral->v))) by {
        assert(src.ephemeral->v == old_cdj);
        assert(caching_disk_journal_accessible_aus(old_cdj)
            == cj_lsn_au_index(old_cdj.journal).values() + old_cdj.mini_allocator.all_aus());
    }
    assert(CrashAwareCachingDiskJournal::State::internal_alloc(
        src,
        dst,
        target_lbl,
        new_cdj,
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::internal_alloc);
    }
    assert(CrashAwareCachingDiskJournal::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskJournal::Step::internal_alloc(new_cdj),
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::next_by);
    }
    reveal(CrashAwareCachingDiskJournal::State::next);
    src.next_refines(dst, target_lbl);

    assert(post.inv()) by {
        assert(post.journal.wf());
        assert(async_disk_superblock_page_wf(post.disk.content));
        assert(post.persistent_superblock_image_i().wf());
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.journal_caching_disk_i().inv());
        assert(post.journal.persistent_seq_end
            == post.persistent_superblock_image_i().journal_seq_end);
        assert(post.in_flight is Some <==> post.journal.in_flight is Some);
        assert(post.in_flight is Some <==> post.in_flight_image is Some);
    }
    assert(post.semantic_inv());
    assert(inv(post));
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
        pre.program.state.journal.journal.seq_end() == pre.program.state.branch.seq_end(),
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
    assert(pre_state.journal.journal.seq_end() == end_lsn) by {
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        assert(AtomicJournalState::State::next_by(
            pre_state.journal,
            pre_state.journal,
            atomic_lbl,
            AtomicJournalState::Step::query_end_lsn(),
        ));
        assert(AtomicJournalState::State::query_end_lsn(
            pre_state.journal,
            pre_state.journal,
            atomic_lbl,
        ));
        reveal(AtomicJournalState::State::query_end_lsn);
        let cached_lbl = CachedJournal::Label::QueryEndLsn{end_lsn};
        assert(CachedJournal::State::next(
            pre_state.journal.journal,
            pre_state.journal.journal,
            cached_lbl,
        ));
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        assert(CachedJournal::State::next_by(
            pre_state.journal.journal,
            pre_state.journal.journal,
            cached_lbl,
            CachedJournal::Step::query_end_lsn(),
        ));
        assert(CachedJournal::State::query_end_lsn(
            pre_state.journal.journal,
            pre_state.journal.journal,
            cached_lbl,
        ));
        reveal(CachedJournal::State::query_end_lsn);
    }
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
            assert(post.journal.journal.status.unwrap().au_page_bounds
                == pre.journal.journal.status.unwrap().au_page_bounds);
            assert(post.journal.persistent_seq_end == pre.journal.persistent_seq_end);
            assert(post.journal.in_flight == pre.journal.in_flight);
            assert(post.journal.prepared == pre.journal.prepared);
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
            assert(post.journal.journal.status.unwrap().au_page_bounds
                == pre.journal.journal.status.unwrap().au_page_bounds);
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
    assert(post.journal_caching_disk_state_i().au_page_bounds_i()
        == pre.journal_caching_disk_state_i().au_page_bounds_i());

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

pub proof fn commit_start_refines(
    pre: UnifiedCacheJournalSource,
    post: UnifiedCacheJournalSource,
    snapshot: JournalSnapshot,
    seq_end: nat,
    reads: Map<Address, RawPage>,
)
    requires
        inv(pre),
        pre.superblock_loaded(),
        pre.journal.ready(),
        post.disk == pre.disk,
        post.persistent_image == pre.persistent_image,
        post.in_flight is Some,
        post.in_flight_image is Some,
        post.in_flight_image.unwrap().wf(),
        post.in_flight_image.unwrap().journal_snapshot == snapshot,
        post.in_flight_image.unwrap().journal_seq_end == seq_end,
        Cache::State::next(
            pre.cache,
            post.cache,
            Cache::Label::Access{reads, writes: Map::empty()},
        ),
        AtomicJournalState::State::next(
            pre.journal,
            post.journal,
            AtomicJournalState::Label::CommitStart{
                snapshot,
                seq_end,
                reads: to_journal_records(reads),
            },
        ),
    ensures
        CrashAwareCachingDiskJournal::State::next(
            unified_cache_journal_i(pre),
            unified_cache_journal_i(post),
            CrashAwareCachingDiskJournal::Label::CommitStart{
                new_boundary_lsn: snapshot.boundary_lsn,
                snapshot,
                seq_end,
            },
        ),
        inv(post),
{
    let empty_writes = Map::<Address, RawPage>::empty();
    let cache_lbl = Cache::Label::Access{reads, writes: empty_writes};
    let atomic_lbl = AtomicJournalState::Label::CommitStart{
        snapshot,
        seq_end,
        reads: to_journal_records(reads),
    };
    let aus = pre.journal_projection_aus();
    let component_addrs = Set::new(|addr: Address| {
        snapshot.freshest_rec() is Some && addr == snapshot.freshest_rec().unwrap()
    });
    let component_reads = reads.restrict(component_addrs);

    AtomicJournalState::State::wf_next(pre.journal, post.journal, atomic_lbl);
    AtomicJournalState::State::commit_start_effect(pre.journal, post.journal, atomic_lbl);
    Cache::State::inv_next(pre.cache, post.cache, cache_lbl);

    assert(pre.journal.in_flight is None) by {
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        assert(AtomicJournalState::State::next_by(
            pre.journal,
            post.journal,
            atomic_lbl,
            AtomicJournalState::Step::commit_start(),
        ));
        reveal(AtomicJournalState::State::commit_start);
    }
    assert(post.superblock_loaded());
    assert(post.journal.ready()) by {
        assert(post.journal.journal == pre.journal.journal);
    }
    assert(post.journal.journal.status.unwrap().au_page_bounds
        == pre.journal.journal.status.unwrap().au_page_bounds) by {
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        assert(AtomicJournalState::State::next_by(
            pre.journal,
            post.journal,
            atomic_lbl,
            AtomicJournalState::Step::commit_start(),
        ));
        reveal(AtomicJournalState::State::commit_start);
    }
    assert(post.journal_projection_aus() =~= aus) by {
        assert(post.journal.journal == pre.journal.journal);
        assert(post.journal.mini_allocator == pre.journal.mini_allocator);
    }
    projected_cache_read_only_access_unchanged(pre.cache, post.cache, aus, reads);
    assert(post.journal_caching_disk_i() == pre.journal_caching_disk_i()) by {
        assert(project_persistent(post.disk, aus) == project_persistent(pre.disk, aus));
        caching_disk_i_equal_from_raw_projection_agreement(
            post.cache,
            pre.cache,
            post.disk,
            pre.disk,
            aus,
        );
        caching_disk_i_equal_by_aus_ext(post.cache, post.disk, post.journal_projection_aus(), aus);
    }
    assert(post.journal_caching_disk_state_i() == pre.journal_caching_disk_state_i()) by {
        assert(post.journal.journal == pre.journal.journal);
        assert(post.journal.mini_allocator == pre.journal.mini_allocator);
        assert(post.journal.journal.status.unwrap().au_page_bounds
            == pre.journal.journal.status.unwrap().au_page_bounds);
    }

    let inner = pre.journal_caching_disk_state_i();
    assert(component_reads <= pre.journal_caching_disk_i().cache) by {
        assert forall |addr: Address| #[trigger] component_reads.contains_key(addr)
            implies {
                &&& pre.journal_caching_disk_i().cache.contains_key(addr)
                &&& component_reads[addr] == pre.journal_caching_disk_i().cache[addr]
            } by {
            assert(reads.contains_key(addr));
            assert(component_addrs.contains(addr));
            assert(snapshot.freshest_rec() is Some);
            let root = snapshot.freshest_rec().unwrap();
            assert(addr == root);
            reveal(AtomicJournalState::State::next);
            reveal(AtomicJournalState::State::next_by);
            assert(AtomicJournalState::State::next_by(
                pre.journal,
                post.journal,
                atomic_lbl,
                AtomicJournalState::Step::commit_start(),
            ));
            reveal(AtomicJournalState::State::commit_start);
            assert(AtomicJournalState::State::commit_start(pre.journal, post.journal, atomic_lbl));
            let full_lbl = CachedJournal::Label::FreezeForCommit{
                frozen: snapshot,
                reads: to_journal_records(reads),
            };
            assert(CachedJournal::State::next(pre.journal.journal, pre.journal.journal, full_lbl));
            reveal(CachedJournal::State::next);
            reveal(CachedJournal::State::next_by);
            assert(CachedJournal::State::next_by(
                pre.journal.journal,
                pre.journal.journal,
                full_lbl,
                CachedJournal::Step::freeze_for_commit(),
            ));
            reveal(CachedJournal::State::freeze_for_commit);
            let index = pre.journal.journal.status.unwrap().lsn_au_index;
            assert(index.contains_value(root.au));
            assert(pre.journal.loaded_index_aus().contains(root.au));
            assert(aus.contains(root.au));
            assert(addresses_in_aus(aus).contains(addr));
            Cache::State::access_read_valid(pre.cache, post.cache, reads, empty_writes, addr);
            assert(pre.cache.valid_read(addr, reads[addr]));
            pre.cache.build_lookup_map_ensures();
            assert(pre.cache.build_lookup_map_props(pre.cache.lookup_map));
            assert(pre.cache.entries.contains_key(pre.cache.lookup_map[addr]));
            assert(cache_filled_addr(pre.cache, addr));
            assert(cache_filled_page(pre.cache, addr) == reads[addr]);
            assert(component_reads[addr] == reads[addr]);
            assert(project_cache_pages(pre.cache, aus).contains_key(addr));
            assert(pre.journal_caching_disk_i().cache.contains_key(addr));
            assert(pre.journal_caching_disk_i().cache[addr] == reads[addr]);
        }
    }

    let cj_lbl = CachingDiskJournal::Label::FreezeForCommit{frozen: snapshot, seq_end};
    to_journal_records_restrict(reads, component_addrs);

    assert(CachingDisk::State::access(
        inner.disk,
        inner.disk,
        CachingDisk::Label::Access{reads: component_reads, writes: empty_writes},
    )) by {
        reveal(CachingDisk::State::access);
        assert(inner.disk == pre.journal_caching_disk_i());
        assert_maps_equal!(
            inner.disk.cache.union_prefer_right(empty_writes),
            inner.disk.cache,
            addr => {}
        );
        assert_maps_equal!(
            status_map(empty_writes.dom(), PageStatus::Dirty),
            Map::<Address, PageStatus>::empty(),
            addr => {}
        );
        assert_maps_equal!(
            inner.disk.status.union_prefer_right(
                status_map(empty_writes.dom(), PageStatus::Dirty),
            ),
            inner.disk.status,
            addr => {}
        );
    }
    assert(CachingDisk::State::next_by(
        inner.disk,
        inner.disk,
        CachingDisk::Label::Access{reads: component_reads, writes: empty_writes},
        CachingDisk::Step::access(),
    )) by {
        reveal(CachingDisk::State::next_by);
    }
    reveal(CachingDisk::State::next);
    inner.disk_reads_ensures(component_reads);

    assert(CachedJournal::State::next(
        inner.journal,
        inner.journal,
        CachedJournal::Label::FreezeForCommit{
            frozen: snapshot,
            reads: to_journal_records(component_reads),
        },
    )) by {
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        assert(AtomicJournalState::State::next_by(
            pre.journal,
            post.journal,
            atomic_lbl,
            AtomicJournalState::Step::commit_start(),
        ));
        reveal(AtomicJournalState::State::commit_start);
        assert(AtomicJournalState::State::commit_start(pre.journal, post.journal, atomic_lbl));
        let full_lbl = CachedJournal::Label::FreezeForCommit{
            frozen: snapshot,
            reads: to_journal_records(reads),
        };
        assert(CachedJournal::State::next(pre.journal.journal, pre.journal.journal, full_lbl));
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        assert(CachedJournal::State::next_by(
            pre.journal.journal,
            pre.journal.journal,
            full_lbl,
            CachedJournal::Step::freeze_for_commit(),
        ));
        reveal(CachedJournal::State::freeze_for_commit);
        assert(inner.journal == pre.journal.journal);
        if snapshot.freshest_rec() is Some {
            let root = snapshot.freshest_rec().unwrap();
            let index = pre.journal.journal.status.unwrap().lsn_au_index;
            assert(reads.contains_key(root));
            assert(index.contains_value(root.au));
            assert(pre.journal.loaded_index_aus().contains(root.au));
            assert(aus.contains(root.au));
            assert(component_addrs.contains(root));
            assert(component_reads.contains_key(root));
            assert(to_journal_records(component_reads)[root]
                == to_journal_records(reads)[root]);
        }
        assert(CachedJournal::State::freeze_for_commit(
            inner.journal,
            inner.journal,
            CachedJournal::Label::FreezeForCommit{
                frozen: snapshot,
                reads: to_journal_records(component_reads),
            },
        ));
        assert(CachedJournal::State::next_by(
            inner.journal,
            inner.journal,
            CachedJournal::Label::FreezeForCommit{
                frozen: snapshot,
                reads: to_journal_records(component_reads),
            },
            CachedJournal::Step::freeze_for_commit(),
        )) by {
            reveal(CachedJournal::State::next_by);
        }
    }

    if snapshot.freshest_rec() is Some {
        let root = snapshot.freshest_rec().unwrap();
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        assert(AtomicJournalState::State::next_by(
            pre.journal,
            post.journal,
            atomic_lbl,
            AtomicJournalState::Step::commit_start(),
        ));
        reveal(AtomicJournalState::State::commit_start);
        assert(AtomicJournalState::State::commit_start(pre.journal, post.journal, atomic_lbl));
        let full_lbl = CachedJournal::Label::FreezeForCommit{
            frozen: snapshot,
            reads: to_journal_records(reads),
        };
        assert(CachedJournal::State::next(pre.journal.journal, pre.journal.journal, full_lbl));
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        assert(CachedJournal::State::next_by(
            pre.journal.journal,
            pre.journal.journal,
            full_lbl,
            CachedJournal::Step::freeze_for_commit(),
        ));
        reveal(CachedJournal::State::freeze_for_commit);
        let index = pre.journal.journal.status.unwrap().lsn_au_index;
        assert(reads.contains_key(root));
        assert(index.contains_value(root.au));
        assert(pre.journal.loaded_index_aus().contains(root.au));
        assert(aus.contains(root.au));
        assert(component_addrs.contains(root));
        assert(pre.journal.journal.status.unwrap().au_page_bounds.contains_key(root.au));
        assert(root.page <= pre.journal.journal.status.unwrap().au_page_bounds[root.au]);
        assert(inner.au_page_bounds_i().contains_key(root.au));
        assert(root.page <= inner.au_page_bounds_i()[root.au]);
        assert(component_reads.contains_key(root));
        assert(to_journal_records(component_reads).contains_key(root));
        assert(to_journal_records(component_reads)[root] == to_journal_records(reads)[root]);
        assert(inner.refinement_inv());
        assert(inner.lsn_au_index_or_empty().values().contains(root.au));
        assert(inner.live_bounded_addr(root));
        inner.indexed_au_page_bound_addr_in_journal_disk_image(root);
        inner.live_bounded_addr_visible(root);
        CachingDisk::State::access_read_matches_visible(
            inner.disk,
            inner.disk,
            component_reads,
            empty_writes,
            root,
        );
        assert(component_reads[root] == inner.disk.visible()[root]);
        assert(inner.journal_disk_view().entries.contains_key(root));
        assert(inner.journal_disk_view().entries[root]
            == to_journal_records(inner.disk.visible())[root]);
        assert(to_journal_records(component_reads)[root] == inner.journal_disk_view().entries[root]);
        assert(seq_end == inner.frozen_seq_end(snapshot));
    } else {
        assert(seq_end == snapshot.boundary_lsn) by {
            reveal(AtomicJournalState::State::next);
            reveal(AtomicJournalState::State::next_by);
            assert(AtomicJournalState::State::next_by(
                pre.journal,
                post.journal,
                atomic_lbl,
                AtomicJournalState::Step::commit_start(),
            ));
            reveal(AtomicJournalState::State::commit_start);
        }
        assert(seq_end == inner.frozen_seq_end(snapshot));
    }

    assert(CachingDiskJournal::State::freeze_for_commit(
        inner,
        inner,
        cj_lbl,
        component_reads,
    )) by {
        reveal(CachingDiskJournal::State::freeze_for_commit);
    }
    assert(CachingDiskJournal::State::next_by(
        inner,
        inner,
        cj_lbl,
        CachingDiskJournal::Step::freeze_for_commit(component_reads),
    )) by {
        reveal(CachingDiskJournal::State::next_by);
    }
    reveal(CachingDiskJournal::State::next);

    let src = unified_cache_journal_i(pre);
    let dst = unified_cache_journal_i(post);
    let target_lbl = CrashAwareCachingDiskJournal::Label::CommitStart{
        new_boundary_lsn: snapshot.boundary_lsn,
        snapshot,
        seq_end,
    };
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(src.frozen is None);
    assert(dst.frozen == Option::Some(CachingDiskJournalFrozenMetadata{snapshot, seq_end}));
    assert(!dst.prepared);
    assert(src.persistent.metadata().seq_end <= seq_end) by {
        assert(src.persistent.metadata().seq_end == pre.journal.persistent_seq_end);
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        assert(AtomicJournalState::State::next_by(
            pre.journal,
            post.journal,
            atomic_lbl,
            AtomicJournalState::Step::commit_start(),
        ));
        reveal(AtomicJournalState::State::commit_start);
    }
    assert(CrashAwareCachingDiskJournal::State::commit_start(src, dst, target_lbl)) by {
        reveal(CrashAwareCachingDiskJournal::State::commit_start);
    }
    assert(CrashAwareCachingDiskJournal::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskJournal::Step::commit_start(),
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::next_by);
    }
    reveal(CrashAwareCachingDiskJournal::State::next);
    src.next_refines(dst, target_lbl);

    assert(post.inv()) by {
        assert(post.journal.wf());
        assert(async_disk_superblock_page_wf(post.disk.content));
        assert(post.persistent_superblock_image_i() == pre.persistent_superblock_image_i());
        assert(post.persistent_superblock_image_i().wf());
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.journal_caching_disk_i().inv());
        assert(post.journal.persistent_seq_end == pre.journal.persistent_seq_end);
        assert(post.in_flight is Some <==> post.journal.in_flight is Some);
        assert(post.in_flight is Some <==> post.in_flight_image is Some);
    }
    assert(post.semantic_inv());
    assert(inv(post));
}

pub proof fn commit_prepared_refines(
    pre: UnifiedCacheJournalSource,
    post: UnifiedCacheJournalSource,
)
    requires
        inv(pre),
        post.cache == pre.cache,
        post.disk.content == pre.disk.content,
        post.disk.inv(),
        post.persistent_image == pre.persistent_image,
        post.in_flight == pre.in_flight,
        post.in_flight_image == pre.in_flight_image,
        !pre.journal.prepared,
        AtomicJournalState::State::next(
            pre.journal,
            post.journal,
            AtomicJournalState::Label::CommitPrepared,
        ),
    ensures
        CrashAwareCachingDiskJournal::State::next(
            unified_cache_journal_i(pre),
            unified_cache_journal_i(post),
            CrashAwareCachingDiskJournal::Label::CommitPrepared,
        ),
        inv(post),
{
    let atomic_lbl = AtomicJournalState::Label::CommitPrepared;

    AtomicJournalState::State::wf_next(pre.journal, post.journal, atomic_lbl);
    reveal(AtomicJournalState::State::next);
    reveal(AtomicJournalState::State::next_by);
    assert(AtomicJournalState::State::next_by(
        pre.journal,
        post.journal,
        atomic_lbl,
        AtomicJournalState::Step::commit_prepared(),
    ));
    assert(AtomicJournalState::State::commit_prepared(
        pre.journal,
        post.journal,
        atomic_lbl,
    )) by {
        reveal(AtomicJournalState::State::commit_prepared);
    }
    assert(post.journal == AtomicJournalState::State{
        prepared: true,
        ..pre.journal
    });
    assert(post.journal.in_flight == pre.journal.in_flight);
    assert(post.journal.persistent_seq_end == pre.journal.persistent_seq_end);
    assert(post.journal.journal == pre.journal.journal);
    assert(post.journal.mini_allocator == pre.journal.mini_allocator);

    assert(post.superblock_loaded() == pre.superblock_loaded());
    assert(pre.superblock_loaded()) by {
        if !pre.superblock_loaded() {
            assert(pre.in_flight is None);
            assert(pre.journal.in_flight is None);
        }
    }
    assert(post.persistent_superblock_image_i()
        == pre.persistent_superblock_image_i()) by {
        if pre.persistent_image is Some {
            assert(post.persistent_image == pre.persistent_image);
        } else {
            assert(post.disk.content == pre.disk.content);
        }
    }
    assert(post.journal_projection_aus() =~= pre.journal_projection_aus()) by {
        if pre.journal.ready() {
            assert(post.journal.journal == pre.journal.journal);
            assert(post.journal.mini_allocator == pre.journal.mini_allocator);
        } else {
            assert(post.journal.journal == pre.journal.journal);
        }
    }
    assert(post.journal_caching_disk_i() == pre.journal_caching_disk_i()) by {
        assert_maps_equal!(
            post.journal_caching_disk_i().cache,
            pre.journal_caching_disk_i().cache,
            addr => {}
        );
        assert_maps_equal!(
            post.journal_caching_disk_i().status,
            pre.journal_caching_disk_i().status,
            addr => {}
        );
        assert_maps_equal!(
            post.journal_caching_disk_i().persistent,
            pre.journal_caching_disk_i().persistent,
            addr => {
                if post.journal_caching_disk_i().persistent.contains_key(addr) {
                    assert(pre.journal_caching_disk_i().persistent.contains_key(addr));
                }
                if pre.journal_caching_disk_i().persistent.contains_key(addr) {
                    assert(post.journal_caching_disk_i().persistent.contains_key(addr));
                }
            }
        );
    }
    assert(post.journal_caching_disk_state_i() == pre.journal_caching_disk_state_i());

    let src = unified_cache_journal_i(pre);
    let dst = unified_cache_journal_i(post);
    let target_lbl = CrashAwareCachingDiskJournal::Label::CommitPrepared;
    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(src.frozen is Some);
    assert(!src.prepared);
    assert(dst.prepared);
    assert(src.frozen == dst.frozen);
    assert(src.ephemeral == dst.ephemeral);
    assert(src.persistent == dst.persistent);
    assert(CrashAwareCachingDiskJournal::State::commit_prepared(
        src,
        dst,
        target_lbl,
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::commit_prepared);
        let frozen = src.frozen.unwrap();
        assert(src.ephemeral->v == pre.journal_caching_disk_state_i());
        assert(frozen.snapshot == pre.journal.in_flight.unwrap().snapshot);
        assert(frozen.seq_end == pre.journal.in_flight.unwrap().seq_end);
        assert(CachingDiskJournal::State::next(
            src.ephemeral->v,
            src.ephemeral->v,
            CachingDiskJournal::Label::CommitPrepared{
                frozen: frozen.snapshot,
                seq_end: frozen.seq_end,
            },
        )) by {
            assert(CachingDiskJournal::State::commit_prepared(
                src.ephemeral->v,
                src.ephemeral->v,
                CachingDiskJournal::Label::CommitPrepared{
                    frozen: frozen.snapshot,
                    seq_end: frozen.seq_end,
                },
            )) by {
                reveal(CachingDiskJournal::State::commit_prepared);
                reveal(AtomicJournalState::State::commit_prepared);
            }
            assert(CachingDiskJournal::State::next_by(
                src.ephemeral->v,
                src.ephemeral->v,
                CachingDiskJournal::Label::CommitPrepared{
                    frozen: frozen.snapshot,
                    seq_end: frozen.seq_end,
                },
                CachingDiskJournal::Step::commit_prepared(),
            )) by {
                reveal(CachingDiskJournal::State::next_by);
            }
            reveal(CachingDiskJournal::State::next);
        }
    }
    assert(CrashAwareCachingDiskJournal::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskJournal::Step::commit_prepared(),
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::next_by);
    }
    reveal(CrashAwareCachingDiskJournal::State::next);
    src.next_refines(dst, target_lbl);

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

pub proof fn commit_complete_refines(
    pre: UnifiedCacheJournalSource,
    post: UnifiedCacheJournalSource,
    require_end: nat,
    discarded_aus: Set<AU>,
)
    requires
        inv(pre),
        post.cache == pre.cache,
        post.disk.content == pre.disk.content,
        post.disk.inv(),
        post.persistent_image == pre.in_flight_image,
        post.in_flight is None,
        post.in_flight_image is None,
        AtomicJournalState::State::next(
            pre.journal,
            post.journal,
            AtomicJournalState::Label::CommitComplete{
                require_end,
                discarded_aus,
            },
        ),
    ensures
        CrashAwareCachingDiskJournal::State::next(
            unified_cache_journal_i(pre),
            unified_cache_journal_i(post),
            CrashAwareCachingDiskJournal::Label::CommitComplete{
                require_end,
                discarded: discarded_aus,
            },
        ),
        inv(post),
{
    let atomic_lbl = AtomicJournalState::Label::CommitComplete{
        require_end,
        discarded_aus,
    };

    AtomicJournalState::State::wf_next(pre.journal, post.journal, atomic_lbl);
    AtomicJournalState::State::commit_complete_effect(pre.journal, post.journal, atomic_lbl);

    assert(pre.in_flight is Some) by {
        assert(pre.in_flight is Some <==> pre.journal.in_flight is Some);
    }
    assert(pre.in_flight_image is Some) by {
        assert(pre.in_flight is Some <==> pre.in_flight_image is Some);
    }
    let image = pre.in_flight_image.unwrap();
    let journal_image = pre.journal.in_flight.unwrap();
    let frozen = CachingDiskJournalFrozenMetadata{
        snapshot: journal_image.snapshot,
        seq_end: journal_image.seq_end,
    };

    assert(post.superblock_loaded());
    assert(post.persistent_superblock_image_i() == image);
    assert(image.journal_snapshot == journal_image.snapshot);
    assert(image.journal_seq_end == journal_image.seq_end);
    assert(post.persistent_journal_i() == PersistentCachingDiskJournal::Metadata{
        meta: frozen,
    });
    assert(post.frozen_journal_metadata_i() is None);
    assert(post.journal_projection_aus() =~= post.journal.owned_aus()) by {
        assert(post.journal.ready());
    }

    let src = unified_cache_journal_i(pre);
    let dst = unified_cache_journal_i(post);
    let target_lbl = CrashAwareCachingDiskJournal::Label::CommitComplete{
        require_end,
        discarded: discarded_aus,
    };

    assert(src.ephemeral is Known);
    assert(dst.ephemeral is Known);
    assert(src.frozen == Option::Some(frozen));
    assert(src.prepared) by {
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        assert(AtomicJournalState::State::next_by(
            pre.journal,
            post.journal,
            atomic_lbl,
            AtomicJournalState::Step::commit_complete(post.journal.journal),
        ));
        reveal(AtomicJournalState::State::commit_complete);
    }
    assert(dst.frozen is None);
    assert(!dst.prepared);
    assert(dst.persistent == PersistentCachingDiskJournal::Metadata{meta: frozen});
    assert(src.ephemeral->v == pre.journal_caching_disk_state_i());
    assert(dst.ephemeral->v == post.journal_caching_disk_state_i());

    assert(post.journal_projection_aus()
        =~= pre.journal_projection_aus().difference(discarded_aus)) by {
        assert(pre.journal.ready());
        assert(post.journal.ready());
        assert(pre.journal_projection_aus() == pre.journal.owned_aus());
        assert(post.journal_projection_aus() == post.journal.owned_aus());
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        assert(AtomicJournalState::State::next_by(
            pre.journal,
            post.journal,
            atomic_lbl,
            AtomicJournalState::Step::commit_complete(post.journal.journal),
        ));
        assert(AtomicJournalState::State::commit_complete(
            pre.journal,
            post.journal,
            atomic_lbl,
            post.journal.journal,
        ));
        reveal(AtomicJournalState::State::commit_complete);
        let cj_lbl = CachedJournal::Label::DiscardOld{
            start_lsn: frozen.snapshot.boundary_lsn,
            require_end,
            deallocs: discarded_aus,
        };
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        assert(CachedJournal::State::next_by(
            pre.journal.journal,
            post.journal.journal,
            cj_lbl,
            CachedJournal::Step::discard_old(),
        ));
        reveal(CachedJournal::State::discard_old);
        let old_index = pre.journal.journal.status.unwrap().lsn_au_index;
        let new_index = post.journal.journal.status.unwrap().lsn_au_index;
        assert(discarded_aus == old_index.values().difference(new_index.values()));
        assert(pre.journal.loaded_index_aus() == old_index.values());
        assert(post.journal.loaded_index_aus() == new_index.values());
        assert(post.journal.mini_allocator.all_aus()
            == pre.journal.mini_allocator.all_aus().difference(discarded_aus));
        assert forall |au: AU| #[trigger] post.journal_projection_aus().contains(au)
            implies pre.journal_projection_aus().difference(discarded_aus).contains(au) by {
            assert(post.journal.owned_aus().contains(au));
            if post.journal.loaded_index_aus().contains(au) {
                assert(new_index.values().contains(au));
                assert(old_index.values().contains(au));
                assert(pre.journal.loaded_index_aus().contains(au));
            } else {
                assert(post.journal.mini_allocator.all_aus().contains(au));
                assert(pre.journal.mini_allocator.all_aus().contains(au));
            }
            assert(!discarded_aus.contains(au)) by {
                assert(post.journal.owned_aus().disjoint(discarded_aus));
            }
        }
        assert forall |au: AU|
            #[trigger] pre.journal_projection_aus().difference(discarded_aus).contains(au)
            implies post.journal_projection_aus().contains(au) by {
            assert(pre.journal.owned_aus().contains(au));
            assert(!discarded_aus.contains(au));
            if pre.journal.loaded_index_aus().contains(au) {
                assert(old_index.values().contains(au));
                if !new_index.values().contains(au) {
                    assert(old_index.values().difference(new_index.values()).contains(au));
                    assert(discarded_aus.contains(au));
                    assert(false);
                }
                assert(post.journal.loaded_index_aus().contains(au));
            } else {
                assert(pre.journal.mini_allocator.all_aus().contains(au));
                assert(pre.journal.mini_allocator.all_aus().difference(discarded_aus).contains(au));
                assert(post.journal.mini_allocator.all_aus().contains(au));
            }
            assert(post.journal.owned_aus().contains(au));
        }
    }
    ownership_projection_forget_refines(
        pre.cache,
        pre.disk,
        pre.journal_projection_aus(),
        discarded_aus,
    );
    assert(post.journal_caching_disk_i()
        == adapter_caching_disk_i(
            pre.cache,
            pre.disk,
            pre.journal_projection_aus().difference(discarded_aus),
        )) by {
        assert(post.cache == pre.cache);
        assert(post.disk.content == pre.disk.content);
        assert_maps_equal!(
            post.journal_caching_disk_i().cache,
            adapter_caching_disk_i(
                pre.cache,
                pre.disk,
                pre.journal_projection_aus().difference(discarded_aus),
            ).cache,
            addr => {}
        );
        assert_maps_equal!(
            post.journal_caching_disk_i().persistent,
            adapter_caching_disk_i(
                pre.cache,
                pre.disk,
                pre.journal_projection_aus().difference(discarded_aus),
            ).persistent,
            addr => {
                if post.journal_caching_disk_i().persistent.contains_key(addr) {
                    assert(post.disk.content.contains_key(addr));
                    assert(pre.disk.content.contains_key(addr));
                    assert(post.disk.content[addr] == pre.disk.content[addr]);
                }
                if adapter_caching_disk_i(
                    pre.cache,
                    pre.disk,
                    pre.journal_projection_aus().difference(discarded_aus),
                ).persistent.contains_key(addr) {
                    assert(pre.disk.content.contains_key(addr));
                    assert(post.disk.content.contains_key(addr));
                    assert(post.disk.content[addr] == pre.disk.content[addr]);
                }
            }
        );
        assert_maps_equal!(
            post.journal_caching_disk_i().status,
            adapter_caching_disk_i(
                pre.cache,
                pre.disk,
                pre.journal_projection_aus().difference(discarded_aus),
            ).status,
            addr => {}
        );
    }

    let cdj_lbl = CachingDiskJournal::Label::DiscardOld{
        start_lsn: frozen.snapshot.boundary_lsn,
        require_end,
        deallocs: discarded_aus,
    };
    assert(CachedJournal::State::next(
        pre.journal.journal,
        post.journal.journal,
        CachedJournal::Label::DiscardOld{
            start_lsn: frozen.snapshot.boundary_lsn,
            require_end,
            deallocs: discarded_aus,
        },
    )) by {
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        assert(AtomicJournalState::State::next_by(
            pre.journal,
            post.journal,
            atomic_lbl,
            AtomicJournalState::Step::commit_complete(post.journal.journal),
        ));
        reveal(AtomicJournalState::State::commit_complete);
    }
    assert(CachingDisk::State::next(
        pre.journal_caching_disk_i(),
        post.journal_caching_disk_i(),
        CachingDisk::Label::Forget{aus: discarded_aus},
    ));
    assert(CachingDiskJournal::State::discard_old(
        src.ephemeral->v,
        dst.ephemeral->v,
        cdj_lbl,
        post.journal.journal,
        post.journal_caching_disk_i(),
    )) by {
        reveal(CachingDiskJournal::State::discard_old);
    }
    assert(CachingDiskJournal::State::next_by(
        src.ephemeral->v,
        dst.ephemeral->v,
        cdj_lbl,
        CachingDiskJournal::Step::discard_old(
            post.journal.journal,
            post.journal_caching_disk_i(),
        ),
    )) by {
        reveal(CachingDiskJournal::State::next_by);
    }
    reveal(CachingDiskJournal::State::next);
    assert(CachingDiskJournal::State::next(
        src.ephemeral->v,
        dst.ephemeral->v,
        cdj_lbl,
    ));
    assert(CrashAwareCachingDiskJournal::State::commit_complete(
        src,
        dst,
        target_lbl,
        dst.ephemeral->v,
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::commit_complete);
    }
    assert(CrashAwareCachingDiskJournal::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskJournal::Step::commit_complete(dst.ephemeral->v),
    )) by {
        reveal(CrashAwareCachingDiskJournal::State::next_by);
    }
    reveal(CrashAwareCachingDiskJournal::State::next);
    src.next_refines(dst, target_lbl);

    assert(post.inv()) by {
        assert(post.journal.wf());
        assert(async_disk_superblock_page_wf(post.disk.content));
        assert(post.persistent_superblock_image_i().wf());
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.journal_caching_disk_i().inv());
        assert(post.journal.persistent_seq_end
            == post.persistent_superblock_image_i().journal_seq_end);
        assert(post.in_flight is Some <==> post.journal.in_flight is Some);
        assert(post.in_flight is Some <==> post.in_flight_image is Some);
    }
    assert(post.semantic_inv());
    assert(inv(post));
}

} // verus!
