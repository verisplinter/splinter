// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Direct refinement from CrashAwareCachingDiskJournal to AbstractCrashAwareJournal.

#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::assert_maps_equal;

use crate::abstract_system::AbstractCrashAwareJournal_v::{
    AbstractCrashAwareJournal, Ephemeral as AbstractEphemeral,
};
use crate::abstract_system::AbstractJournal_v::AbstractJournal;
use crate::abstract_system::MsgHistory_v::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::allocation_layer::AllocationJournal_v::{
    AllocationJournal, JournalMetadata, JournalImage, addrs_in_aus, maps_agree_on,
};
use crate::allocation_layer::AllocationJournalAbstractRefinement_v::*;
use crate::disk::GenericDisk_v::{Address, AU};
use crate::implementation::CachedJournal_v::*;
use crate::implementation::CachingDisk_v::CachingDiskRawPage as RawPage;
use crate::implementation::CachingDiskJournal_v::{
    CachingDiskJournal, cj_lsn_au_index,
};
use crate::implementation::CachingDiskJournalRefinement_v::*;
use crate::implementation::CrashAwareCachingDiskJournal_v::*;
use crate::implementation::JournalTypes_v::{to_journal_records, to_journal_records_restrict};
use crate::journal::LinkedJournal_v::*;

verus!{

impl EphemeralCachingDiskJournal {
    pub open spec fn i_abstract(self) -> AbstractEphemeral {
        match self {
            EphemeralCachingDiskJournal::Unknown => AbstractEphemeral::Unknown,
            EphemeralCachingDiskJournal::Known{v} =>
                AbstractEphemeral::Known{v: v.i().i_abstract()},
        }
    }
}

pub open spec fn frozen_image_metadata_i(frozen: CachingDiskJournalFrozenMetadata)
    -> JournalMetadata
{
    JournalMetadata{
        boundary_lsn: frozen.snapshot.boundary_lsn,
        seq_end: frozen.seq_end,
        freshest_rec: frozen.snapshot.freshest_rec(),
        first: frozen.snapshot.first(),
    }
}

pub open spec fn frozen_metadata_i(
    frozen: CachingDiskJournalFrozenMetadata,
    journal: CachingDiskJournal::State,
) -> MsgHistory {
    journal.i().frozen_image(frozen_image_metadata_i(frozen)).i()
}

pub open spec fn materialization_certificate(
    state: CachingDiskJournal::State,
    frozen: CachingDiskJournalFrozenMetadata,
) -> bool
{
    state.frozen_materialization_certificate(frozen.snapshot, frozen.seq_end)
}

impl CrashAwareCachingDiskJournal::State {
    pub open spec fn persistent_i(self) -> MsgHistory {
        if self.persistent is Image {
            self.persistent->image.i().i()
        } else if self.ephemeral is Known {
            frozen_metadata_i(self.persistent.metadata(), self.ephemeral->v)
        } else {
            arbitrary()
        }
    }

    pub open spec fn frozen_i(self) -> Option<MsgHistory> {
        if self.frozen is None {
            Option::None
        } else if self.ephemeral is Known {
            Option::Some(frozen_metadata_i(self.frozen.unwrap(), self.ephemeral->v))
        } else {
            arbitrary()
        }
    }

    pub open spec fn i_abstract(self) -> AbstractCrashAwareJournal::State {
        AbstractCrashAwareJournal::State{
            persistent: self.persistent_i(),
            ephemeral: self.ephemeral.i_abstract(),
            frozen: self.frozen_i(),
        }
    }

    pub open spec fn semantic_inv(self) -> bool {
        &&& self.persistent is Image ==> self.persistent->image.wf()
        &&& self.ephemeral is Known ==> self.ephemeral->v.refinement_inv()
        &&& self.ephemeral is Known && self.ephemeral->v.journal.status is None ==>
            self.ephemeral->v.disk.addrs_clean_or_evictable(
                self.ephemeral->v.disk.cache.dom(),
            )
        &&& self.ephemeral is Known && self.ephemeral->v.journal.status is Some ==>
            self.ephemeral->v.clean_watermark_au_page_bounds_clean_or_evictable()
        &&& self.ephemeral is Known && self.ephemeral->v.journal.status is Some ==>
            self.ephemeral->v.clean_watermark_records_bounded_by_clean_au_page_bounds()
        &&& self.ephemeral is Known ==>
            self.ephemeral->v.i().frozen_metadata_valid(
                frozen_image_metadata_i(self.persistent.metadata()),
            )
        &&& self.ephemeral is Known && self.ephemeral->v.journal.status is Some ==>
            materialization_certificate(
                self.ephemeral->v,
                self.persistent.metadata(),
            )
        &&& self.ephemeral is Known && self.ephemeral->v.journal.status is None ==>
            self.ephemeral->v.persistent_visible_agree_on(
                self.ephemeral->v.frozen_loose_domain(self.persistent.metadata().snapshot),
            )
        &&& self.frozen is Some && self.ephemeral is Known ==>
            self.ephemeral->v.i().frozen_metadata_valid(
                frozen_image_metadata_i(self.frozen.unwrap()),
            )
        &&& self.frozen is Some && self.ephemeral is Known ==>
            self.ephemeral->v.frozen_snapshot_valid(
                self.frozen.unwrap().snapshot,
                self.frozen.unwrap().seq_end,
            )
        &&& self.prepared && self.frozen is Some ==>
            materialization_certificate(self.ephemeral->v, self.frozen.unwrap())
    }

    pub open spec fn refinement_inv(self) -> bool {
        &&& self.inv()
        &&& self.semantic_inv()
    }

    proof fn loaded_next_refines_abstract(
        pre: CachingDiskJournal::State,
        post: CachingDiskJournal::State,
        lbl: CachingDiskJournal::Label,
    )
        requires
            pre.refinement_inv(),
            CachingDiskJournal::State::next(pre, post, lbl),
        ensures
            post.refinement_inv(),
            AbstractJournal::State::next(
                pre.i().i_abstract(),
                post.i().i_abstract(),
                pre.i().label_i_abstract(lbl.i(pre)),
            ),
    {
        pre.semantic_inv_implies_i_inv();
        pre.next_refines(post, lbl);
        post.semantic_inv_implies_i_inv();
        pre.i().next_refines_abstract(post.i(), lbl.i(pre));
    }

    pub proof fn persistent_i_wf(self)
        requires
            self.refinement_inv(),
        ensures
            self.persistent_i().wf(),
            self.persistent_i().seq_end == self.persistent.metadata().seq_end,
    {
        if self.persistent is Image {
            let image = self.persistent->image;
            assert(image.wf());
            image.i().i_wf();
        } else {
            self.ephemeral->v.semantic_inv_implies_i_inv();
            let state = self.ephemeral->v.i();
            let meta = frozen_image_metadata_i(self.persistent.metadata());
            let freeze_lbl = AllocationJournal::Label::FreezeForCommit{frozen_journal: meta};
            assert(AllocationJournal::State::next(state, state, freeze_lbl)) by {
                reveal(AllocationJournal::State::next);
                reveal(AllocationJournal::State::next_by);
                assert(AllocationJournal::State::next_by(
                    state,
                    state,
                    freeze_lbl,
                    AllocationJournal::Step::freeze_for_commit(),
                ));
            }
            AllocationJournal::State::frozen_journal_is_valid_image(
                state,
                state,
                freeze_lbl,
            );
            state.frozen_image(meta).i_wf();
        }
    }

    pub proof fn ephemeral_i_wf(self)
        requires
            self.refinement_inv(),
            self.ephemeral is Known,
        ensures
            self.i_abstract().ephemeral is Known,
            self.i_abstract().ephemeral->v.wf(),
    {
        self.ephemeral->v.semantic_inv_implies_i_inv();
        let allocation = self.ephemeral->v.i();
        assert(allocation.inv());
        assert(allocation.semantic_inv());
        assert(allocation.refinement_inv());
        allocation.i_inv();

        let likes = allocation.i();
        assert(likes.inv());
        likes.i_inv();

        let linked = likes.i();
        assert(linked.inv());
        linked.i_wf();

        let paged = linked.i();
        assert(paged.wf());
        let prefix = paged.truncated_journal.i();
        if paged.truncated_journal.freshest_rec is Some {
            let rec =
                paged.truncated_journal.freshest_rec.unwrap();
            rec.i_lemma(
                paged.truncated_journal.boundary_lsn,
            );
        } else {
            assert(prefix == MsgHistory::empty_history_at(
                paged.truncated_journal.boundary_lsn,
            ));
        }
        assert(prefix.wf());
        assert(prefix.seq_end
            == paged.truncated_journal.seq_end());
        assert(prefix.seq_end
            == paged.unmarshalled_tail.seq_start);
        prefix.concat_lemma(paged.unmarshalled_tail);
        assert(paged.i().wf());
        assert(self.i_abstract().ephemeral->v
            == allocation.i_abstract());
    }

    proof fn loaded_internal_preserves_frozen_i(
        pre: CachingDiskJournal::State,
        post: CachingDiskJournal::State,
        lbl: CachingDiskJournal::Label,
        frozen: CachingDiskJournalFrozenMetadata,
    )
        requires
            pre.refinement_inv(),
            CachingDiskJournal::State::next(pre, post, lbl),
            lbl.i(pre) is InternalAllocations,
            pre.i().frozen_metadata_valid(frozen_image_metadata_i(frozen)),
        ensures
            post.refinement_inv(),
            post.i().frozen_metadata_valid(frozen_image_metadata_i(frozen)),
            frozen_metadata_i(frozen, post) == frozen_metadata_i(frozen, pre),
    {
        pre.semantic_inv_implies_i_inv();
        pre.next_refines(post, lbl);
        post.semantic_inv_implies_i_inv();
        let meta = frozen_image_metadata_i(frozen);
        AllocationJournal::State::internal_allocations_preserves_frozen_metadata_tight(
            pre.i(),
            post.i(),
            lbl.i(pre),
            meta,
        );
        assert(post.i().frozen_image(meta).tight_tj()
            == pre.i().frozen_image(meta).tight_tj());
    }

    pub proof fn materialization_certificate_implies_persistent_frozen_loose_domain_matches_visible(
        state: CachingDiskJournal::State,
        frozen: CachingDiskJournalFrozenMetadata,
    )
        requires
            state.refinement_inv(),
            materialization_certificate(state, frozen),
        ensures
            state.persistent_frozen_loose_domain(frozen)
                =~= state.frozen_loose_domain(frozen.snapshot),
    {
        let meta = frozen_image_metadata_i(frozen);
        let concrete_prefix = state.frozen_prefix_domain(frozen.snapshot);
        let allocation_prefix = state.i().frozen_prefix_domain(meta);

        state.frozen_snapshot_valid_implies_i_metadata_valid(frozen.snapshot, frozen.seq_end);
        state.i_metadata_valid_implies_frozen_tj_matches_i(frozen.snapshot, frozen.seq_end);
        let freeze_lbl = AllocationJournal::Label::FreezeForCommit{frozen_journal: meta};
        assert(AllocationJournal::State::next_by(
            state.i(),
            state.i(),
            freeze_lbl,
            AllocationJournal::Step::freeze_for_commit(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        assert(AllocationJournal::State::next(state.i(), state.i(), freeze_lbl)) by {
            reveal(AllocationJournal::State::next);
        }
        state.semantic_inv_implies_i_inv();
        AllocationJournal::State::frozen_journal_is_valid_image(
            state.i(),
            state.i(),
            freeze_lbl,
        );
        let base_image = state.i().frozen_image(meta);
        let persistent_dv = state.persistent_journal_disk_view(frozen.snapshot);
        let base_tight = base_image.tight_tj();
        let root = frozen.snapshot.freshest_rec();
        let first = frozen.snapshot.first();
        let base_bounds = base_tight.disk_view.build_au_page_bounds_au_walk(
            base_tight.freshest_rec,
            first,
        );
        base_image.valid_image_implies_tight_valid_image();
        base_image.valid_image_implies_tight_seq_bounds();
        base_image.tj.disk_view.path_build_tight_is_sub_disk(base_image.tj.freshest_rec);
        base_tight.disk_view.build_au_page_bounds_au_walk_domain_matches_build_tight(
            base_tight.freshest_rec,
            first,
        );
        assert(base_tight.disk_view.build_tight(base_tight.freshest_rec)
            == base_tight.disk_view) by {
            base_tight.disk_view.decodable_implies_path_decodable(base_tight.freshest_rec);
            base_image.tj.disk_view.path_build_tight_idempotent(base_image.tj.freshest_rec);
            base_tight.disk_view.path_build_tight_equals_build_tight(base_tight.freshest_rec);
        }
        assert(base_tight.disk_view.entries_bounded_by_au_page_bounds(base_bounds)
            == base_tight.disk_view.entries);
        assert(base_tight.build_lsn_au_index_from_first(first)
            == state.i().frozen_lsn_au_index(meta));
        assert(base_tight.disk_view.entries <= persistent_dv.entries) by {
            assert forall |addr: Address| #[trigger] base_tight.disk_view.entries.contains_key(addr)
                implies persistent_dv.entries.contains_key(addr)
                    && persistent_dv.entries[addr] == base_tight.disk_view.entries[addr] by {
                assert(base_tight.disk_view.is_sub_disk_with_newer_lsn(state.i().tj().disk_view));
                assert(state.i().tj().disk_view.entries.contains_key(addr));
                assert(state.i().tj().disk_view.entries[addr] == base_tight.disk_view.entries[addr]);
                assert(base_tight.disk_view.is_sub_disk(base_image.tj.disk_view)) by {
                    base_image.tj.disk_view.path_build_tight_is_sub_disk(base_image.tj.freshest_rec);
                }
                assert(base_image.tj.disk_view.entries.contains_key(addr));
                assert(base_tight.disk_view.entries_bounded_by_au_page_bounds(base_bounds)
                    .contains_key(addr));
                assert(base_bounds.contains_key(addr.au));
                assert(addr.page <= base_bounds[addr.au]);
                assert(state.i().frozen_loose_domain(meta).contains(addr)) by {
                    assert(base_tight.disk_view.domain_au_bounded_wrt_index(
                        state.i().frozen_lsn_au_index(meta),
                    ));
                    assert(state.i().frozen_lsn_au_index(meta).values().contains(addr.au));
                }
                assert(state.i().frozen_prefix_domain(meta).contains(addr));
                assert(allocation_prefix.contains(addr));
                assert(concrete_prefix.contains(addr));
                assert(state.disk.persistent.restrict(concrete_prefix)
                    == state.disk.visible().restrict(concrete_prefix));
                assert(state.disk.visible().contains_key(addr));
                assert(state.disk.visible().restrict(concrete_prefix).contains_key(addr));
                assert(state.disk.persistent.restrict(concrete_prefix).contains_key(addr));
                assert(state.disk.persistent.contains_key(addr));
                assert(state.disk.persistent.restrict(concrete_prefix)[addr]
                    == state.disk.visible().restrict(concrete_prefix)[addr]);
                assert(state.disk.persistent.restrict(concrete_prefix)[addr]
                    == state.disk.persistent[addr]);
                assert(state.disk.visible().restrict(concrete_prefix)[addr]
                    == state.disk.visible()[addr]);
                assert(state.disk.persistent[addr] == state.disk.visible()[addr]);
                assert(persistent_dv.entries.contains_key(addr));
                assert(persistent_dv.entries[addr] == to_journal_records(state.disk.persistent)[addr]);
                assert(state.i().disk_view.entries[addr] == to_journal_records(state.disk.visible())[addr]);
                assert(to_journal_records(state.disk.persistent)[addr]
                    == to_journal_records(state.disk.visible())[addr]);
            }
        }
        assert(base_tight.disk_view.is_sub_disk(persistent_dv)) by {
            assert(base_tight.disk_view.boundary_lsn == persistent_dv.boundary_lsn);
            assert(base_tight.disk_view.entries <= persistent_dv.entries);
        }
        assert(base_tight.freshest_rec == root);
        assert(base_tight.disk_view.path_decodable(root)) by {
            base_tight.disk_view.decodable_implies_path_decodable(base_tight.freshest_rec);
        }
        assert(base_tight.disk_view.path_build_tight(root) == base_tight.disk_view) by {
            assert(root == base_tight.freshest_rec);
            base_image.tj.disk_view.path_build_tight_idempotent(base_image.tj.freshest_rec);
            base_tight.disk_view.path_build_tight_equals_build_tight(base_tight.freshest_rec);
            assert(base_image.tj.disk_view.path_build_tight(base_image.tj.freshest_rec)
                == base_tight.disk_view);
            assert(base_tight.disk_view.path_build_tight(base_tight.freshest_rec)
                == base_tight.disk_view);
        }
        base_tight.disk_view.path_build_tight_preserved_in_superdisk(
            persistent_dv,
            root,
        );
        persistent_dv.loose_build_lsn_au_index_au_walk_matches_tight(root, first);
        assert(persistent_dv.path_build_tight(root) == base_tight.disk_view);
        assert(state.persistent_lsn_au_index(frozen.snapshot)
            == base_tight.disk_view.build_lsn_au_index_au_walk(root, first));
        assert(base_tight.build_lsn_au_index_from_first(first)
            == state.i().frozen_lsn_au_index(meta));
        assert(base_tight.disk_view.build_lsn_au_index_au_walk(root, first)
            == state.i().frozen_lsn_au_index(meta));
        assert_maps_equal!(
            state.persistent_lsn_au_index(frozen.snapshot).restrict(state.frozen_lsns(frozen.snapshot)),
            state.lsn_au_index_or_empty().restrict(state.frozen_lsns(frozen.snapshot)),
            lsn => {}
        );
    }

    pub proof fn materialized_loaded_index_matches_persistent_when_domains_match(
        state: CachingDiskJournal::State,
        frozen: CachingDiskJournalFrozenMetadata,
    )
        requires
            state.persistent_frozen_loose_domain(frozen)
                =~= state.frozen_loose_domain(frozen.snapshot),
        ensures
            CachingDiskJournalImage::materialized_from_loaded_index(state, frozen)
                == CachingDiskJournalImage::materialized_from_persistent(state, frozen),
    {
        assert(state.disk.persistent.restrict(state.frozen_loose_domain(frozen.snapshot))
            == state.disk.persistent.restrict(state.persistent_frozen_loose_domain(frozen))) by {
            assert_maps_equal!(
                state.disk.persistent.restrict(state.frozen_loose_domain(frozen.snapshot)),
                state.disk.persistent.restrict(state.persistent_frozen_loose_domain(frozen)),
                addr => {}
            );
        }
    }

    pub proof fn materialization_certificate_implies_materialized_image_refines(
        state: CachingDiskJournal::State,
        frozen: CachingDiskJournalFrozenMetadata,
    )
        requires
            state.refinement_inv(),
            materialization_certificate(state, frozen),
        ensures
            CachingDiskJournalImage::materialized_from_persistent(
                state,
                frozen,
            ).wf(),
            CachingDiskJournalImage::materialized_from_loaded_index(
                state,
                frozen,
            ).wf(),
            state.i().acceptable_frozen_image(
                frozen_image_metadata_i(frozen),
                CachingDiskJournalImage::materialized_from_persistent(
                    state,
                    frozen,
                ).i(),
            ),
            state.i().acceptable_frozen_image(
                frozen_image_metadata_i(frozen),
                CachingDiskJournalImage::materialized_from_loaded_index(
                    state,
                    frozen,
                ).i(),
            ),
    {
        let meta = frozen_image_metadata_i(frozen);
        let image = CachingDiskJournalImage::materialized_from_persistent(state, frozen);
        let concrete_prefix = state.frozen_prefix_domain(frozen.snapshot);
        let allocation_prefix = state.i().frozen_prefix_domain(meta);

        state.frozen_snapshot_valid_implies_i_metadata_valid(frozen.snapshot, frozen.seq_end);
        state.i_metadata_valid_implies_frozen_tj_matches_i(frozen.snapshot, frozen.seq_end);
        let freeze_lbl = AllocationJournal::Label::FreezeForCommit{frozen_journal: meta};
        assert(AllocationJournal::State::next_by(
            state.i(),
            state.i(),
            freeze_lbl,
            AllocationJournal::Step::freeze_for_commit(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        assert(AllocationJournal::State::next(state.i(), state.i(), freeze_lbl)) by {
            reveal(AllocationJournal::State::next);
        }
        state.semantic_inv_implies_i_inv();
        AllocationJournal::State::frozen_journal_is_valid_image(
            state.i(),
            state.i(),
            freeze_lbl,
        );
        let base_image = state.i().frozen_image(meta);
        assert(base_image.valid_image());

        state.persistent_dom_wf();
        assert(image.i().tj.disk_view.wf_addrs()) by {
            assert forall |addr: Address| #[trigger] image.i().tj.disk_view.entries.contains_key(addr)
                implies addr.wf() by {
                assert(to_journal_records(image.persistent).contains_key(addr));
                assert(image.persistent.contains_key(addr));
                assert(image.persistent.dom().contains(addr));
                assert(state.disk.persistent.contains_key(addr));
                assert(state.disk.persistent.dom().contains(addr));
            }
        }
        Self::materialization_certificate_implies_persistent_frozen_loose_domain_matches_visible(
            state,
            frozen,
        );
        assert(state.frozen_loose_domain(frozen.snapshot) =~= state.i().frozen_loose_domain(meta));
        assert(image.i().tj.disk_view.entries.dom() <= state.i().frozen_loose_domain(meta)) by {
            assert forall |addr: Address|
                #[trigger] image.i().tj.disk_view.entries.dom().contains(addr)
                implies state.i().frozen_loose_domain(meta).contains(addr) by {
                assert(image.i().tj.disk_view.entries.contains_key(addr));
                assert(to_journal_records(image.persistent).contains_key(addr));
                assert(image.persistent.contains_key(addr));
                assert(state.disk.persistent.restrict(state.persistent_frozen_loose_domain(frozen)).contains_key(addr));
                assert(state.persistent_frozen_loose_domain(frozen).contains(addr));
                assert(state.frozen_loose_domain(frozen.snapshot).contains(addr));
            }
        }

        assert(maps_agree_on(
            allocation_prefix,
            image.i().tj.disk_view.entries,
            state.i().disk_view.entries,
        )) by {
            assert(allocation_prefix =~= concrete_prefix);
            assert_maps_equal!(
                image.i().tj.disk_view.entries.restrict(allocation_prefix),
                state.i().disk_view.entries.restrict(allocation_prefix),
                addr => {
                    if image.i().tj.disk_view.entries.restrict(allocation_prefix).contains_key(addr) {
                        assert(allocation_prefix.contains(addr));
                        assert(concrete_prefix.contains(addr));
                        assert(image.i().tj.disk_view.entries.contains_key(addr));
                        assert(to_journal_records(image.persistent).contains_key(addr));
                        assert(image.persistent.contains_key(addr));
                        assert(image.persistent[addr] == state.disk.persistent[addr]);
                        assert(state.disk.persistent.restrict(concrete_prefix)
                            == state.disk.visible().restrict(concrete_prefix));
                        assert(state.disk.visible().contains_key(addr));
                        assert(state.disk.persistent.restrict(concrete_prefix).contains_key(addr));
                        assert(state.disk.visible().restrict(concrete_prefix).contains_key(addr));
                        assert(state.disk.persistent.restrict(concrete_prefix)[addr]
                            == state.disk.visible().restrict(concrete_prefix)[addr]);
                        assert(state.disk.persistent.restrict(concrete_prefix)[addr]
                            == state.disk.persistent[addr]);
                        assert(state.disk.visible().restrict(concrete_prefix)[addr]
                            == state.disk.visible()[addr]);
                        assert(state.disk.persistent[addr] == state.disk.visible()[addr]);
                        assert(state.i().disk_view.entries.contains_key(addr));
                        assert(state.i().disk_view.entries[addr] == to_journal_records(state.disk.visible())[addr]);
                        assert(image.i().tj.disk_view.entries[addr]
                            == to_journal_records(image.persistent)[addr]);
                        assert(to_journal_records(image.persistent)[addr]
                            == to_journal_records(state.disk.visible())[addr]);
                    }
                    if state.i().disk_view.entries.restrict(allocation_prefix).contains_key(addr) {
                        assert(allocation_prefix.contains(addr));
                        assert(concrete_prefix.contains(addr));
                        assert(state.i().disk_view.entries.contains_key(addr));
                        assert(state.disk.visible().contains_key(addr));
                        assert(state.disk.persistent.restrict(concrete_prefix)
                            == state.disk.visible().restrict(concrete_prefix));
                        assert(state.disk.visible().restrict(concrete_prefix).contains_key(addr));
                        assert(state.disk.persistent.restrict(concrete_prefix).contains_key(addr));
                        assert(state.disk.persistent.contains_key(addr));
                        assert(state.disk.visible().restrict(concrete_prefix)[addr]
                            == state.disk.visible()[addr]);
                        assert(state.disk.persistent.restrict(concrete_prefix)[addr]
                            == state.disk.persistent[addr]);
                        assert(state.disk.persistent.restrict(concrete_prefix)[addr]
                            == state.disk.visible().restrict(concrete_prefix)[addr]);
                        assert(state.disk.persistent[addr] == state.disk.visible()[addr]);
                        assert(image.persistent.contains_key(addr));
                        assert(image.persistent[addr] == state.disk.persistent[addr]);
                        assert(to_journal_records(image.persistent).contains_key(addr));
                        assert(image.i().tj.disk_view.entries.contains_key(addr));
                        assert(to_journal_records(image.persistent)[addr]
                            == to_journal_records(state.disk.visible())[addr]);
                    }
                }
            );
        }

        let base_tight = base_image.tight_tj();
        let image_tj = image.i().tj;
        let image_dv = image_tj.disk_view;
        let root = image_tj.freshest_rec;
        let tight_index = base_tight.build_lsn_au_index_from_first(meta.first);
        let base_bounds = base_tight.disk_view.build_au_page_bounds_au_walk(
            base_tight.freshest_rec,
            meta.first,
        );
        base_image.valid_image_implies_tight_valid_image();
        base_image.valid_image_implies_tight_seq_bounds();
        base_image.tj.disk_view.path_build_tight_is_sub_disk(base_image.tj.freshest_rec);
        base_tight.disk_view.decodable_implies_path_decodable(base_tight.freshest_rec);
        base_image.tj.disk_view.path_build_tight_idempotent(base_image.tj.freshest_rec);
        base_tight.disk_view.path_build_tight_equals_build_tight(base_tight.freshest_rec);
        base_tight.disk_view.build_au_page_bounds_au_walk_domain_matches_build_tight(
            base_tight.freshest_rec,
            meta.first,
        );
        assert(base_tight.disk_view.build_tight(base_tight.freshest_rec)
            == base_tight.disk_view);
        assert(base_tight.disk_view.entries_bounded_by_au_page_bounds(base_bounds)
            == base_tight.disk_view.entries);
        assert(base_tight.build_lsn_au_index_from_first(meta.first)
            == state.i().frozen_lsn_au_index(meta));
        assert(base_tight.disk_view.entries <= image_dv.entries) by {
            assert forall |addr: Address| #[trigger] base_tight.disk_view.entries.contains_key(addr)
                implies image_dv.entries.contains_key(addr)
                    && image_dv.entries[addr] == base_tight.disk_view.entries[addr] by {
                assert(base_tight.disk_view.is_sub_disk_with_newer_lsn(state.i().tj().disk_view));
                assert(state.i().tj().disk_view.entries.contains_key(addr));
                assert(state.i().tj().disk_view.entries[addr] == base_tight.disk_view.entries[addr]);
                assert(base_tight.disk_view.is_sub_disk(base_image.tj.disk_view)) by {
                    base_image.tj.disk_view.path_build_tight_is_sub_disk(base_image.tj.freshest_rec);
                }
                assert(base_image.tj.disk_view.entries.contains_key(addr));
                assert(base_tight.disk_view.entries_bounded_by_au_page_bounds(base_bounds)
                    .contains_key(addr));
                assert(base_bounds.contains_key(addr.au));
                assert(addr.page <= base_bounds[addr.au]);
                assert(allocation_prefix.contains(addr));
                assert(maps_agree_on(
                    allocation_prefix,
                    image.i().tj.disk_view.entries,
                    state.i().disk_view.entries,
                ));
                assert(image.i().tj.disk_view.entries.restrict(allocation_prefix)
                    == state.i().disk_view.entries.restrict(allocation_prefix));
                assert(state.i().disk_view.entries.contains_key(addr));
                assert(state.i().disk_view.entries[addr] == state.i().tj().disk_view.entries[addr]) by {
                    state.semantic_inv_implies_i_inv();
                    assert(state.i().tj().disk_view.is_sub_disk(state.i().disk_view));
                }
                assert(state.i().disk_view.entries.restrict(allocation_prefix).contains_key(addr));
                assert(image.i().tj.disk_view.entries.restrict(allocation_prefix).contains_key(addr));
                assert(image.i().tj.disk_view.entries.restrict(allocation_prefix)[addr]
                    == state.i().disk_view.entries.restrict(allocation_prefix)[addr]);
                assert(image.i().tj.disk_view.entries.contains_key(addr));
                assert(image.i().tj.disk_view.entries[addr] == state.i().disk_view.entries[addr]);
            }
        }
        assert(base_tight.disk_view.is_sub_disk(image_dv)) by {
            assert(base_tight.disk_view.boundary_lsn == image_dv.boundary_lsn);
            assert(base_tight.disk_view.entries <= image_dv.entries);
        }
        assert(base_tight.disk_view.path_build_tight(base_tight.freshest_rec)
            == base_tight.disk_view);
        base_tight.disk_view.path_build_tight_preserved_in_superdisk(image_dv, root);
        assert(image.i().tight_tj() == base_tight);
        assert(image.i().tj.disk_view.domain_au_bounded_wrt_index(tight_index)) by {
            assert forall |addr: Address| #[trigger] image.i().tj.disk_view.entries.dom().contains(addr)
                implies tight_index.values().contains(addr.au) by {
                assert(state.i().frozen_loose_domain(meta).contains(addr));
                assert(state.i().frozen_domain(meta).contains(addr));
                assert(addrs_in_aus(state.i().frozen_lsn_au_index(meta).values()).contains(addr));
                assert(state.i().frozen_lsn_au_index(meta).values().contains(addr.au));
            }
        }
        assert(image.i().bounded_live_entries_are_tight()) by {
            assert forall |addr: Address| {
                let record = image.i().tj.disk_view.entries[addr];
                &&& #[trigger] image.i().tj.disk_view.entries.contains_key(addr)
                &&& base_bounds.contains_key(addr.au)
                &&& addr.page <= base_bounds[addr.au]
                &&& image.i().tj.seq_start() < record.message_seq.seq_end
            } implies base_tight.disk_view.entries.contains_key(addr) by {
                assert(state.i().frozen_loose_domain(meta).contains(addr));
                assert(allocation_prefix.contains(addr));
                assert(maps_agree_on(
                    allocation_prefix,
                    image.i().tj.disk_view.entries,
                    state.i().disk_view.entries,
                ));
                assert(image.i().tj.disk_view.entries.restrict(allocation_prefix)
                    == state.i().disk_view.entries.restrict(allocation_prefix));
                assert(image.i().tj.disk_view.entries.restrict(allocation_prefix).contains_key(addr));
                assert(state.i().disk_view.entries.restrict(allocation_prefix).contains_key(addr));
                assert(image.i().tj.disk_view.entries.restrict(allocation_prefix)[addr]
                    == image.i().tj.disk_view.entries[addr]);
                assert(state.i().disk_view.entries.restrict(allocation_prefix)[addr]
                    == state.i().disk_view.entries[addr]);
                assert(image.i().tj.disk_view.entries.restrict(allocation_prefix)[addr]
                    == state.i().disk_view.entries.restrict(allocation_prefix)[addr]);
                assert(state.i().disk_view.entries.contains_key(addr));
                assert(state.i().disk_view.entries[addr] == image.i().tj.disk_view.entries[addr]);
                assert(base_image.tj.disk_view.entries.contains_key(addr)) by {
                    assert(state.i().frozen_tj(meta).disk_view.entries.contains_key(addr));
                }
                assert(base_image.tj.disk_view.entries[addr]
                    == image.i().tj.disk_view.entries[addr]);
                assert(base_image.bounded_live_entries_are_tight());
            }
        }
        assert(image.i().au_page_bounds_covered()) by {
            assert forall |addr: Address| {
                &&& #[trigger] tight_index.values().contains(addr.au)
                &&& base_bounds.contains_key(addr.au)
                &&& addr.page <= base_bounds[addr.au]
            } implies image.i().tj.disk_view.entries.contains_key(addr) by {
                assert(tight_index == state.i().frozen_lsn_au_index(meta));
                assert(state.i().frozen_lsn_au_index(meta).values().contains(addr.au));
                assert(allocation_prefix.contains(addr)) by {
                    assert(state.i().frozen_loose_domain(meta).contains(addr)) by {
                        assert(state.i().frozen_domain(meta).contains(addr));
                        assert(addrs_in_aus(state.i().frozen_lsn_au_index(meta).values()).contains(addr));
                    }
                }
                AllocationJournal::State::frozen_prefix_domain_bounded_by_au_page_bounds(
                    state.i(),
                    meta,
                    addr,
                );
                assert(state.i().lsn_au_index.values().contains(addr.au)) by {
                    let lsn = choose |lsn: LSN| #![trigger state.i().frozen_lsn_au_index(meta).contains_key(lsn)] {
                        state.i().frozen_lsn_au_index(meta).contains_key(lsn)
                            && state.i().frozen_lsn_au_index(meta)[lsn] == addr.au
                    };
                    assert(state.i().frozen_lsn_au_index(meta).contains_key(lsn));
                    assert(state.i().lsn_au_index.contains_key(lsn));
                    assert(state.i().lsn_au_index[lsn] == addr.au);
                }
                assert(state.i().au_page_bounds_covered());
                assert(state.i().disk_view.entries.contains_key(addr));
                assert(maps_agree_on(
                    allocation_prefix,
                    image.i().tj.disk_view.entries,
                    state.i().disk_view.entries,
                ));
                assert(image.i().tj.disk_view.entries.restrict(allocation_prefix)
                    == state.i().disk_view.entries.restrict(allocation_prefix));
                assert(state.i().disk_view.entries.restrict(allocation_prefix).contains_key(addr));
                assert(image.i().tj.disk_view.entries.restrict(allocation_prefix).contains_key(addr));
                assert(image.i().tj.disk_view.entries.contains_key(addr));
            }
        }
        assert(image.i().valid_image());
        assert(image.i().first == meta.first);
        assert(image.i().tj.freshest_rec == meta.freshest_rec);
        assert(image.i().tj.disk_view.boundary_lsn == meta.boundary_lsn);
        assert(image.i().tj.seq_end() == meta.seq_end);
        assert(image.seq_end == meta.seq_end);
        image.i_valid_image_seq_end_implies_wf();
        assert(state.persistent_frozen_loose_domain(frozen)
            =~= state.frozen_loose_domain(frozen.snapshot));
        Self::materialized_loaded_index_matches_persistent_when_domains_match(state, frozen);
        assert(CachingDiskJournalImage::materialized_from_loaded_index(state, frozen) == image);
    }

    pub proof fn materialization_certificate_implies_materialized_index_values_match_visible(
        state: CachingDiskJournal::State,
        frozen: CachingDiskJournalFrozenMetadata,
    )
        requires
            state.refinement_inv(),
            materialization_certificate(state, frozen),
        ensures
            ({
                let image = CachingDiskJournalImage::materialized_from_persistent(
                    state,
                    frozen,
                );
                let index = image.tj().disk_view.loose_build_lsn_au_index_au_walk(
                    frozen.snapshot.freshest_rec(),
                    frozen.snapshot.first(),
                );
                index.values() =~= state.lsn_au_index_or_empty().restrict(
                    state.frozen_lsns(frozen.snapshot),
                ).values()
            }),
    {
        let meta = frozen_image_metadata_i(frozen);
        let image = CachingDiskJournalImage::materialized_from_persistent(state, frozen);
        let root = frozen.snapshot.freshest_rec();
        let first = frozen.snapshot.first();

        Self::materialization_certificate_implies_materialized_image_refines(
            state,
            frozen,
        );
        state.frozen_snapshot_valid_implies_i_metadata_valid(frozen.snapshot, frozen.seq_end);
        state.i_metadata_valid_implies_frozen_tj_matches_i(frozen.snapshot, frozen.seq_end);

        let freeze_lbl = AllocationJournal::Label::FreezeForCommit{frozen_journal: meta};
        assert(AllocationJournal::State::next_by(
            state.i(),
            state.i(),
            freeze_lbl,
            AllocationJournal::Step::freeze_for_commit(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        assert(AllocationJournal::State::next(state.i(), state.i(), freeze_lbl)) by {
            reveal(AllocationJournal::State::next);
        }
        state.semantic_inv_implies_i_inv();
        AllocationJournal::State::frozen_journal_is_valid_image(
            state.i(),
            state.i(),
            freeze_lbl,
        );
        AllocationJournal::State::acceptable_frozen_image_matches_frozen_image(
            state.i(),
            meta,
            image.i(),
        );

        let materialized_dv = image.tj().disk_view;
        let materialized_index = materialized_dv.loose_build_lsn_au_index_au_walk(
            root,
            first,
        );
        let tight_tj = image.i().tight_tj();
        let tight_index = tight_tj.build_lsn_au_index_from_first(first);
        assert(image.i().valid_image());
        image.i().valid_image_implies_tight_valid_image();
        assert(materialized_dv.path_decodable(root));
        assert(materialized_dv.path_build_tight(root).pointer_is_upstream(root, first));
        materialized_dv.loose_build_lsn_au_index_au_walk_matches_tight(root, first);
        assert(tight_tj.disk_view == materialized_dv.path_build_tight(root));
        assert(tight_tj.freshest_rec == root);
        assert(materialized_index == tight_tj.disk_view.build_lsn_au_index_au_walk(
            root,
            first,
        ));
        assert(tight_index == tight_tj.disk_view.build_lsn_au_index_au_walk(root, first));
        assert(tight_index == state.i().frozen_lsn_au_index(meta)) by {
            assert(image.i().tight_tj() == state.i().frozen_image(meta).tight_tj());
            assert(state.i().frozen_image(meta).tight_tj().build_lsn_au_index_from_first(first)
                == state.i().frozen_lsn_au_index(meta));
        }
        assert(materialized_index.values() =~= state.i().frozen_lsn_au_index(meta).values());
        assert(state.i().frozen_lsn_au_index(meta).values()
            =~= state.lsn_au_index_or_empty().restrict(
                state.frozen_lsns(frozen.snapshot),
            ).values());
    }

    pub proof fn prepared_materialized_image_refines(
        self,
        frozen: CachingDiskJournalFrozenMetadata,
    )
        requires
            self.refinement_inv(),
            self.ephemeral is Known,
            self.frozen is Some,
            self.frozen.unwrap() == frozen,
            self.ephemeral->v.frozen_snapshot_valid(frozen.snapshot, frozen.seq_end),
            CachingDiskJournal::State::next(
                self.ephemeral->v,
                self.ephemeral->v,
                CachingDiskJournal::Label::CommitPrepared{
                    frozen: frozen.snapshot,
                    seq_end: frozen.seq_end,
                },
            ),
        ensures
            materialization_certificate(self.ephemeral->v, frozen),
            CachingDiskJournalImage::materialized_from_persistent(
                self.ephemeral->v,
                frozen,
            ).wf(),
            self.ephemeral->v.i().acceptable_frozen_image(
                frozen_image_metadata_i(frozen),
                CachingDiskJournalImage::materialized_from_persistent(
                    self.ephemeral->v,
                    frozen,
                ).i(),
            ),
    {
        let state = self.ephemeral->v;
        CachingDiskJournal::State::commit_prepared_effect(
            state,
            frozen.snapshot,
            frozen.seq_end,
        );
        state.frozen_snapshot_valid_implies_i_metadata_valid(frozen.snapshot, frozen.seq_end);
        if frozen.snapshot.freshest_rec() is Some {
            assert(state.clean_watermark_au_page_bounds_clean_or_evictable());
            state.clean_watermark_au_page_bounds_clean_implies_frozen_materialization_certificate(
                frozen.snapshot,
                frozen.seq_end,
            );
        } else {
            state.rootless_frozen_snapshot_materialization_certificate(
                frozen.snapshot,
                frozen.seq_end,
            );
        }
        assert(materialization_certificate(state, frozen));
        Self::materialization_certificate_implies_materialized_image_refines(state, frozen);
    }

    pub proof fn loaded_materialized_persistent_image_refines(
        image: CachingDiskJournalImage,
    )
        requires
            image.wf(),
        ensures
            ({
                let loaded = CachingDiskJournal::State::load_from_persistent(
                    image.snapshot,
                    image.persistent,
                );
                let frozen = image.metadata();
                let materialized = CachingDiskJournalImage::materialized_from_persistent(
                    loaded,
                    frozen,
                );
                let meta = frozen_image_metadata_i(frozen);
                &&& materialized == image
                &&& materialized.wf()
                &&& loaded.i().frozen_metadata_valid(meta)
                &&& loaded.i().acceptable_frozen_image(meta, materialized.i())
            }),
    {
        let loaded = CachingDiskJournal::State::load_from_persistent(
            image.snapshot,
            image.persistent,
        );
        let frozen = image.metadata();
        let materialized = CachingDiskJournalImage::materialized_from_persistent(
            loaded,
            frozen,
        );
        let persistent = image.i();
        let meta = frozen_image_metadata_i(frozen);

        CachingDiskJournal::State::load_from_persistent_refines_image(
            image.snapshot,
            image.persistent,
            persistent,
        );
        AllocationJournal::State::initialize_inductive(loaded.i(), persistent);
        AllocationJournal::State::initialize_semantic_inv(loaded.i(), persistent);
        assert(loaded.i().semantic_inv());

        assert(loaded.i().disk_view == persistent.tj.disk_view);
        assert(loaded.i().lsn_au_index == loaded.lsn_au_index_or_empty());
        assert(loaded.journal_disk_view().entries == persistent.tj.disk_view.entries);
        assert(loaded.frozen_seq_end(frozen.snapshot) == frozen.seq_end) by {
            if frozen.snapshot.freshest_rec() is Some {
                let root = frozen.snapshot.freshest_rec().unwrap();
                assert(persistent.tj.disk_view.entries.contains_key(root));
                assert(persistent.tj.disk_view.entries[root].message_seq.seq_end
                    == persistent.tj.seq_end());
                assert(persistent.tj.seq_end() == frozen.seq_end);
            } else {
                assert(frozen.snapshot.boundary_lsn == persistent.tj.seq_end());
                assert(persistent.tj.seq_end() == frozen.seq_end);
            }
        }
        assert(loaded.i().frozen_lsns(meta) =~= loaded.frozen_lsns(frozen.snapshot)) by {
            assert forall |lsn: LSN| #[trigger] loaded.i().frozen_lsns(meta).contains(lsn)
                <==> loaded.frozen_lsns(frozen.snapshot).contains(lsn) by {}
        }
        assert(loaded.i().frozen_lsn_au_index(meta)
            =~= loaded.lsn_au_index_or_empty().restrict(loaded.frozen_lsns(frozen.snapshot))) by {
            assert forall |lsn: LSN|
                #[trigger] loaded.i().frozen_lsn_au_index(meta).contains_key(lsn)
                <==> loaded.lsn_au_index_or_empty().restrict(
                    loaded.frozen_lsns(frozen.snapshot),
                ).contains_key(lsn) by {}
            assert forall |lsn: LSN|
                #[trigger] loaded.i().frozen_lsn_au_index(meta).contains_key(lsn)
                implies loaded.i().frozen_lsn_au_index(meta)[lsn]
                    == loaded.lsn_au_index_or_empty().restrict(
                        loaded.frozen_lsns(frozen.snapshot),
                    )[lsn] by {}
        }
        assert(loaded.i().frozen_lsn_au_index(meta).values()
            =~= loaded.lsn_au_index_or_empty().restrict(
                loaded.frozen_lsns(frozen.snapshot),
            ).values());
        assert(loaded.i().frozen_loose_domain(meta)
            =~= loaded.frozen_loose_domain(frozen.snapshot)) by {
            assert forall |addr: Address|
                #[trigger] loaded.i().frozen_loose_domain(meta).contains(addr)
                <==> loaded.frozen_loose_domain(frozen.snapshot).contains(addr) by {}
        }

        let freeze_lbl = AllocationJournal::Label::FreezeForCommit{frozen_journal: meta};
        assert(AllocationJournal::State::next_by(
            loaded.i(),
            loaded.i(),
            freeze_lbl,
            AllocationJournal::Step::freeze_for_commit(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        assert(AllocationJournal::State::next(loaded.i(), loaded.i(), freeze_lbl)) by {
            reveal(AllocationJournal::State::next);
        }
        assert(loaded.i().frozen_metadata_valid(meta));
        loaded.semantic_inv_implies_i_inv();
        AllocationJournal::State::frozen_journal_is_valid_image(
            loaded.i(),
            loaded.i(),
            freeze_lbl,
        );

        assert(loaded.i().acceptable_frozen_image(meta, persistent)) by {
            assert(persistent.valid_image());
            assert(persistent.first == meta.first);
            assert(persistent.tj.freshest_rec == meta.freshest_rec);
            assert(persistent.tj.disk_view.boundary_lsn == meta.boundary_lsn);
            assert(persistent.tj.seq_end() == meta.seq_end);
            let tight_index = persistent.tight_tj().build_lsn_au_index_from_first(
                persistent.first,
            );
            assert(loaded.i().lsn_au_index == tight_index);
            assert(persistent.tj.disk_view.domain_au_bounded_wrt_index(tight_index));
            assert(persistent.tj.disk_view.entries.dom()
                <= loaded.i().frozen_loose_domain(meta)) by {
                assert forall |addr: Address|
                    #[trigger] persistent.tj.disk_view.entries.dom().contains(addr)
                    implies loaded.i().frozen_loose_domain(meta).contains(addr) by {
                    assert(tight_index.values().contains(addr.au));
                    assert(loaded.i().lsn_au_index.values().contains(addr.au));
                    let lsn = choose |lsn: nat| #![trigger loaded.i().lsn_au_index[lsn]] {
                        &&& loaded.i().lsn_au_index.contains_key(lsn)
                        &&& loaded.i().lsn_au_index[lsn] == addr.au
                    };
                    assert(tight_index.contains_key(lsn));
                    persistent.tight_tj().build_lsn_au_index_from_first_ensures(
                        persistent.first,
                    );
                    reveal(TruncatedJournal::au_domain_valid);
                    assert(persistent.tight_tj().seq_start() <= lsn
                        < persistent.tight_tj().seq_end());
                    persistent.valid_image_implies_tight_seq_bounds();
                    assert(meta.boundary_lsn <= lsn < meta.seq_end);
                    assert(loaded.i().frozen_lsns(meta).contains(lsn));
                    assert(loaded.i().frozen_lsn_au_index(meta).contains_key(lsn));
                    assert(loaded.i().frozen_lsn_au_index(meta)[lsn] == addr.au);
                    assert(loaded.i().frozen_lsn_au_index(meta).values().contains(addr.au));
                }
            }
            assert(maps_agree_on(
                loaded.i().frozen_prefix_domain(meta),
                persistent.tj.disk_view.entries,
                loaded.i().disk_view.entries,
            ));
        }

        assert(materialized.persistent == image.persistent) by {
            assert_maps_equal!(materialized.persistent, image.persistent, addr => {
                if materialized.persistent.contains_key(addr) {
                    assert(loaded.disk.persistent.contains_key(addr));
                }
                if image.persistent.contains_key(addr) {
                    assert(persistent.tj.disk_view.entries.contains_key(addr));
                    assert(loaded.i().frozen_loose_domain(meta).contains(addr));
                    assert(loaded.frozen_loose_domain(frozen.snapshot).contains(addr));
                    assert(loaded.disk.persistent.restrict(
                        loaded.frozen_loose_domain(frozen.snapshot),
                    ).contains_key(addr));
                }
            });
        }
        assert(materialized.snapshot == image.snapshot);
        assert(materialized.seq_end == image.seq_end);
        assert(materialized == image);
        assert(materialized.wf());
        assert(loaded.i().acceptable_frozen_image(meta, materialized.i()));
    }

    pub proof fn unloaded_materialized_persistent_image_refines(
        state: CachingDiskJournal::State,
        frozen: CachingDiskJournalFrozenMetadata,
    )
        requires
            state.refinement_inv(),
            state.journal.status is None,
            state.i().frozen_metadata_valid(frozen_image_metadata_i(frozen)),
            state.persistent_visible_agree_on(state.frozen_loose_domain(frozen.snapshot)),
        ensures
            ({
                let materialized = CachingDiskJournalImage::materialized_from_persistent(
                    state,
                    frozen,
                );
                let loaded_index_materialized = CachingDiskJournalImage::materialized_from_loaded_index(
                    state,
                    frozen,
                );
                let meta = frozen_image_metadata_i(frozen);
                &&& materialized.wf()
                &&& loaded_index_materialized.wf()
                &&& state.i().acceptable_frozen_image(meta, materialized.i())
                &&& state.i().acceptable_frozen_image(meta, loaded_index_materialized.i())
            }),
    {
        let materialized = CachingDiskJournalImage::materialized_from_persistent(
            state,
            frozen,
        );
        let meta = frozen_image_metadata_i(frozen);

        state.semantic_inv_implies_i_inv();
        state.i_metadata_valid_implies_frozen_tj_matches_i(frozen.snapshot, frozen.seq_end);
        let freeze_lbl = AllocationJournal::Label::FreezeForCommit{frozen_journal: meta};
        assert(AllocationJournal::State::next_by(
            state.i(),
            state.i(),
            freeze_lbl,
            AllocationJournal::Step::freeze_for_commit(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        assert(AllocationJournal::State::next(state.i(), state.i(), freeze_lbl)) by {
            reveal(AllocationJournal::State::next);
        }
        AllocationJournal::State::frozen_journal_is_valid_image(
            state.i(),
            state.i(),
            freeze_lbl,
        );

        let domain = state.frozen_loose_domain(frozen.snapshot);
        assert(state.persistent_frozen_loose_domain(frozen) =~= domain) by {
            let persistent_dv = state.persistent_journal_disk_view(frozen.snapshot);
            let base_image = state.i().frozen_image(meta);
            let base_tight = base_image.tight_tj();
            let root = frozen.snapshot.freshest_rec();
            let first = frozen.snapshot.first();
            base_image.valid_image_implies_tight_valid_image();
            base_image.valid_image_implies_tight_seq_bounds();
            base_image.tj.disk_view.path_build_tight_is_sub_disk(base_image.tj.freshest_rec);
            assert(base_tight.build_lsn_au_index_from_first(first)
                == state.i().frozen_lsn_au_index(meta));
            assert(base_tight.disk_view.entries <= persistent_dv.entries) by {
                assert forall |addr: Address| #[trigger] base_tight.disk_view.entries.contains_key(addr)
                    implies persistent_dv.entries.contains_key(addr)
                        && persistent_dv.entries[addr] == base_tight.disk_view.entries[addr] by {
                    assert(base_tight.disk_view.is_sub_disk(base_image.tj.disk_view)) by {
                        base_image.tj.disk_view.path_build_tight_is_sub_disk(base_image.tj.freshest_rec);
                    }
                    assert(base_image.tj.disk_view.entries.contains_key(addr));
                    assert(state.i().frozen_tj(meta).disk_view.entries.contains_key(addr));
                    assert(state.frozen_tj(frozen.snapshot).disk_view.entries.contains_key(addr));
                    assert(domain.contains(addr));
                    assert(state.disk.persistent.restrict(domain)
                        == state.disk.visible().restrict(domain));
                    assert(state.disk.visible().restrict(domain).contains_key(addr));
                    assert(state.disk.persistent.restrict(domain).contains_key(addr));
                    assert(state.disk.persistent.contains_key(addr));
                    assert(state.disk.visible().contains_key(addr));
                    assert(state.disk.persistent.restrict(domain)[addr]
                        == state.disk.visible().restrict(domain)[addr]);
                    assert(state.disk.persistent.restrict(domain)[addr]
                        == state.disk.persistent[addr]);
                    assert(state.disk.visible().restrict(domain)[addr]
                        == state.disk.visible()[addr]);
                    assert(state.disk.persistent[addr] == state.disk.visible()[addr]);
                    assert(persistent_dv.entries.contains_key(addr));
                    assert(persistent_dv.entries[addr] == to_journal_records(state.disk.persistent)[addr]);
                    assert(base_tight.disk_view.entries[addr]
                        == to_journal_records(state.disk.visible())[addr]);
                    assert(to_journal_records(state.disk.persistent)[addr]
                        == to_journal_records(state.disk.visible())[addr]);
                }
            }
            assert(base_tight.disk_view.is_sub_disk(persistent_dv)) by {
                assert(base_tight.disk_view.boundary_lsn == persistent_dv.boundary_lsn);
                assert(base_tight.disk_view.entries <= persistent_dv.entries);
            }
            assert(base_tight.freshest_rec == root);
            assert(base_tight.disk_view.path_decodable(root)) by {
                base_tight.disk_view.decodable_implies_path_decodable(base_tight.freshest_rec);
            }
            assert(base_tight.disk_view.path_build_tight(root) == base_tight.disk_view) by {
                assert(root == base_tight.freshest_rec);
                base_image.tj.disk_view.path_build_tight_idempotent(base_image.tj.freshest_rec);
                base_tight.disk_view.path_build_tight_equals_build_tight(base_tight.freshest_rec);
                assert(base_image.tj.disk_view.path_build_tight(base_image.tj.freshest_rec)
                    == base_tight.disk_view);
                assert(base_tight.disk_view.path_build_tight(base_tight.freshest_rec)
                    == base_tight.disk_view);
            }
            base_tight.disk_view.path_build_tight_preserved_in_superdisk(
                persistent_dv,
                root,
            );
            persistent_dv.loose_build_lsn_au_index_au_walk_matches_tight(root, first);
            assert(state.persistent_lsn_au_index(frozen.snapshot)
                == base_tight.disk_view.build_lsn_au_index_au_walk(root, first));
            assert(base_tight.disk_view.build_lsn_au_index_au_walk(root, first)
                == state.i().frozen_lsn_au_index(meta));
            assert_maps_equal!(
                state.persistent_lsn_au_index(frozen.snapshot).restrict(state.frozen_lsns(frozen.snapshot)),
                state.lsn_au_index_or_empty().restrict(state.frozen_lsns(frozen.snapshot)),
                lsn => {}
            );
        }
        Self::materialized_loaded_index_matches_persistent_when_domains_match(state, frozen);
        to_journal_records_restrict(state.disk.persistent, domain);
        to_journal_records_restrict(state.disk.visible(), domain);
        assert(materialized.i().tj.disk_view.entries
            == state.frozen_tj(frozen.snapshot).disk_view.entries) by {
            assert_maps_equal!(
                materialized.i().tj.disk_view.entries,
                state.frozen_tj(frozen.snapshot).disk_view.entries,
                addr => {}
            );
        }
        assert(materialized.i() == state.i().frozen_image(meta));
        assert(materialized.i().valid_image());
        assert(materialized.i().tj.seq_end() == meta.seq_end);
        assert(materialized.seq_end == meta.seq_end);
        materialized.i_valid_image_seq_end_implies_wf();
        assert(materialized.wf());
        assert(maps_agree_on(
            state.i().frozen_prefix_domain(meta),
            materialized.i().tj.disk_view.entries,
            state.i().disk_view.entries,
        )) by {
            let prefix = state.i().frozen_prefix_domain(meta);
            assert_maps_equal!(
                materialized.i().tj.disk_view.entries.restrict(prefix),
                state.i().disk_view.entries.restrict(prefix),
                addr => {
                    if materialized.i().tj.disk_view.entries.restrict(prefix).contains_key(addr) {
                        assert(prefix.contains(addr));
                        assert(state.i().frozen_loose_domain(meta).contains(addr));
                        assert(state.i().frozen_tj(meta).disk_view.entries.contains_key(addr));
                        assert(state.i().frozen_tj(meta).disk_view.entries[addr]
                            == state.i().disk_view.entries[addr]);
                    }
                    if state.i().disk_view.entries.restrict(prefix).contains_key(addr) {
                        assert(prefix.contains(addr));
                        assert(state.i().frozen_loose_domain(meta).contains(addr));
                        assert(state.i().frozen_tj(meta).disk_view.entries.contains_key(addr));
                        assert(state.i().frozen_tj(meta).disk_view.entries[addr]
                            == state.i().disk_view.entries[addr]);
                    }
                }
            );
        }
        assert(state.i().acceptable_frozen_image(meta, materialized.i()));
    }

    pub open spec fn label_i_abstract(self, post: Self, lbl: CrashAwareCachingDiskJournal::Label)
        -> AbstractCrashAwareJournal::Label
    {
        match lbl {
            CrashAwareCachingDiskJournal::Label::LoadEphemeral =>
                AbstractCrashAwareJournal::Label::LoadEphemeralFromPersistentLabel,
            CrashAwareCachingDiskJournal::Label::ReadForRecovery{records} =>
                AbstractCrashAwareJournal::Label::ReadForRecoveryLabel{records},
            CrashAwareCachingDiskJournal::Label::QueryEndLsn{end_lsn} =>
                AbstractCrashAwareJournal::Label::QueryEndLsnLabel{end_lsn},
            CrashAwareCachingDiskJournal::Label::Put{records} =>
                AbstractCrashAwareJournal::Label::PutLabel{records},
            CrashAwareCachingDiskJournal::Label::QueryLsnPersistence{sync_lsn} =>
                AbstractCrashAwareJournal::Label::QueryLsnPersistenceLabel{sync_lsn},
            CrashAwareCachingDiskJournal::Label::CommitStart{
                new_boundary_lsn,
                snapshot,
                seq_end,
            } => if self.ephemeral is Known {
                AbstractCrashAwareJournal::Label::CommitStartLabel{
                    new_boundary_lsn,
                    frozen_journal: frozen_metadata_i(
                        CachingDiskJournalFrozenMetadata{snapshot, seq_end},
                        self.ephemeral->v,
                    ),
                }
            } else {
                arbitrary()
            },
            CrashAwareCachingDiskJournal::Label::CommitComplete{require_end, discarded} =>
                AbstractCrashAwareJournal::Label::CommitCompleteLabel{require_end},
            CrashAwareCachingDiskJournal::Label::Crash{keep_in_flight} =>
                AbstractCrashAwareJournal::Label::CrashLabel{keep_in_flight},
            _ => AbstractCrashAwareJournal::Label::InternalLabel,
        }
    }

    pub proof fn load_ephemeral_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::load_ephemeral(self, post, lbl),
        ensures
            post.refinement_inv(),
            AbstractCrashAwareJournal::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(post, lbl),
            ),
    {
        reveal(CrashAwareCachingDiskJournal::State::load_ephemeral);
        let image = self.persistent->image;
        let loaded = CachingDiskJournal::State::load_from_persistent(
            image.snapshot,
            image.persistent,
        );
        assert(post.ephemeral == EphemeralCachingDiskJournal::Known{v: loaded});
        CachingDiskJournal::State::load_from_persistent_refines_image(
            image.snapshot,
            image.persistent,
            image.i(),
        );
        assert(AllocationJournal::State::initialize(loaded.i(), image.i()));
        assert(loaded.i().mini_allocator == crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty());
        assert(loaded.i().mini_allocator.curr is None);
        assert(loaded.i().mini_allocator.all_aus() =~= Set::<AU>::empty());
        assert(loaded.i().mini_allocator.all_aus().disjoint(image.i().accessible_aus()));
        Self::loaded_materialized_persistent_image_refines(image);
        let domain = loaded.frozen_loose_domain(image.snapshot);
        assert(loaded.disk.cache == Map::<Address, RawPage>::empty());
        assert(loaded.disk.visible() == loaded.disk.persistent) by {
            assert_maps_equal!(loaded.disk.visible(), loaded.disk.persistent, addr => {
                if loaded.disk.visible().contains_key(addr) {
                    assert(!loaded.disk.cache.contains_key(addr));
                }
                if loaded.disk.persistent.contains_key(addr) {
                    assert(loaded.disk.visible().contains_key(addr));
                }
            });
        }
        assert(loaded.persistent_visible_agree_on(domain)) by {
            assert_maps_equal!(
                loaded.disk.persistent.restrict(domain),
                loaded.disk.visible().restrict(domain),
                addr => {}
            );
        }
        loaded.disk.addrs_clean_or_evictable_from_forall(loaded.disk.cache.dom());
        loaded.semantic_inv_implies_i_inv();
        let meta = frozen_image_metadata_i(image.metadata());
        assert(loaded.i().frozen_metadata_valid(meta));
        let freeze_lbl = AllocationJournal::Label::FreezeForCommit{frozen_journal: meta};
        assert(AllocationJournal::State::next(loaded.i(), loaded.i(), freeze_lbl)) by {
            reveal(AllocationJournal::State::next);
            reveal(AllocationJournal::State::next_by);
            assert(AllocationJournal::State::next_by(
                loaded.i(),
                loaded.i(),
                freeze_lbl,
                AllocationJournal::Step::freeze_for_commit(),
            ));
        }
        AllocationJournal::State::acceptable_frozen_image_matches_frozen_image(
            loaded.i(),
            meta,
            image.i(),
        );
        image.i().i_wf();
        loaded.i().initialized_i_abstract_journal_matches_image(image.i());
        assert(self.persistent_i() == image.i().i());
        assert(self.persistent_i().wf());
        assert(post.persistent_i() == self.persistent_i());
        assert(AbstractJournal::State::init_by(
            loaded.i().i_abstract(),
            AbstractJournal::Config::initialize(self.persistent_i()),
        )) by {
            reveal(AbstractJournal::State::init_by);
            reveal(AbstractJournal::State::initialize);
        }
        assert(AbstractCrashAwareJournal::State::next_by(
            self.i_abstract(),
            post.i_abstract(),
            self.label_i_abstract(post, lbl),
            AbstractCrashAwareJournal::Step::load_ephemeral_from_persistent(
                loaded.i().i_abstract(),
            ),
        )) by {
            reveal(AbstractCrashAwareJournal::State::next_by);
        }
        reveal(AbstractCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn read_for_recovery_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::read_for_recovery(self, post, lbl),
        ensures
            post.refinement_inv(),
            AbstractCrashAwareJournal::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(post, lbl),
            ),
    {
        reveal(CrashAwareCachingDiskJournal::State::read_for_recovery);
        let records = lbl.arrow_ReadForRecovery_records();
        let cj_lbl = CachingDiskJournal::Label::ReadForRecovery{messages: records};
        Self::loaded_next_refines_abstract(self.ephemeral->v, self.ephemeral->v, cj_lbl);
        assert(AbstractCrashAwareJournal::State::next_by(
            self.i_abstract(),
            post.i_abstract(),
            self.label_i_abstract(post, lbl),
            AbstractCrashAwareJournal::Step::read_for_recovery(),
        )) by {
            reveal(AbstractCrashAwareJournal::State::next_by);
        }
        reveal(AbstractCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn query_end_lsn_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::query_end_lsn(self, post, lbl),
        ensures
            post.refinement_inv(),
            AbstractCrashAwareJournal::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(post, lbl),
            ),
    {
        reveal(CrashAwareCachingDiskJournal::State::query_end_lsn);
        let end_lsn = lbl.arrow_QueryEndLsn_end_lsn();
        let cj_lbl = CachingDiskJournal::Label::QueryEndLsn{end_lsn};
        Self::loaded_next_refines_abstract(self.ephemeral->v, self.ephemeral->v, cj_lbl);
        assert(AbstractCrashAwareJournal::State::next_by(
            self.i_abstract(),
            post.i_abstract(),
            self.label_i_abstract(post, lbl),
            AbstractCrashAwareJournal::Step::query_end_lsn(),
        )) by {
            reveal(AbstractCrashAwareJournal::State::next_by);
        }
        reveal(AbstractCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn put_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
        new_ephemeral: CachingDiskJournal::State,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::put(self, post, lbl, new_ephemeral),
        ensures
            post.refinement_inv(),
            AbstractCrashAwareJournal::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(post, lbl),
            ),
    {
        reveal(CrashAwareCachingDiskJournal::State::put);
        let records = lbl.arrow_Put_records();
        let cj_lbl = CachingDiskJournal::Label::Put{messages: records};
        self.ephemeral->v.put_next_refines_transition(new_ephemeral, cj_lbl);
        Self::loaded_next_refines_abstract(self.ephemeral->v, new_ephemeral, cj_lbl);
        self.ephemeral->v.put_requires_loaded(new_ephemeral, records);
        CachingDiskJournal::State::put_preserves_clean_watermark_au_page_bounds_clean(
            self.ephemeral->v,
            new_ephemeral,
            records,
        );
        self.ephemeral->v.put_preserves_clean_watermark_records_bounded(
            new_ephemeral,
            records,
        );
        self.ephemeral->v.put_preserves_frozen_materialization_certificate(
            new_ephemeral,
            records,
            self.persistent.metadata().snapshot,
            self.persistent.metadata().seq_end,
        );
        if self.prepared && self.frozen is Some {
            self.ephemeral->v.put_preserves_frozen_materialization_certificate(
                new_ephemeral,
                records,
                self.frozen.unwrap().snapshot,
                self.frozen.unwrap().seq_end,
            );
        }
        let alloc_lbl = cj_lbl.i(self.ephemeral->v);
        let persistent_meta = frozen_image_metadata_i(self.persistent.metadata());
        AllocationJournal::State::put_preserves_frozen_metadata(
            self.ephemeral->v.i(),
            new_ephemeral.i(),
            alloc_lbl,
            persistent_meta,
        );
        if self.frozen is Some {
            AllocationJournal::State::put_preserves_frozen_metadata(
                self.ephemeral->v.i(),
                new_ephemeral.i(),
                alloc_lbl,
                frozen_image_metadata_i(self.frozen.unwrap()),
            );
        }
        assert(post.persistent_i() == self.persistent_i());
        assert(post.frozen_i() == self.frozen_i());
        assert(AbstractCrashAwareJournal::State::next_by(
            self.i_abstract(),
            post.i_abstract(),
            self.label_i_abstract(post, lbl),
            AbstractCrashAwareJournal::Step::put(new_ephemeral.i().i_abstract()),
        )) by {
            reveal(AbstractCrashAwareJournal::State::next_by);
        }
        reveal(AbstractCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn query_lsn_persistence_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::query_lsn_persistence(self, post, lbl),
        ensures
            post.refinement_inv(),
            AbstractCrashAwareJournal::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(post, lbl),
            ),
    {
        reveal(CrashAwareCachingDiskJournal::State::query_lsn_persistence);
        self.persistent_i_wf();
        assert(lbl.arrow_QueryLsnPersistence_sync_lsn() <= self.persistent_i().seq_end);
        assert(AbstractCrashAwareJournal::State::next_by(
            self.i_abstract(),
            post.i_abstract(),
            self.label_i_abstract(post, lbl),
            AbstractCrashAwareJournal::Step::query_lsn_persistence(),
        )) by {
            reveal(AbstractCrashAwareJournal::State::next_by);
        }
        reveal(AbstractCrashAwareJournal::State::next);
        assert(post == self);
        assert(post.refinement_inv());
    }

    pub proof fn commit_start_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::commit_start(self, post, lbl),
        ensures
            post.refinement_inv(),
            AbstractCrashAwareJournal::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(post, lbl),
            ),
    {
        reveal(CrashAwareCachingDiskJournal::State::commit_start);
        let snapshot = lbl.arrow_CommitStart_snapshot();
        let seq_end = lbl.arrow_CommitStart_seq_end();
        let cj_lbl = CachingDiskJournal::Label::FreezeForCommit{frozen: snapshot, seq_end};
        let frozen = CachingDiskJournalFrozenMetadata{snapshot, seq_end};
        self.ephemeral->v.freeze_for_commit_next_refines_transition(
            self.ephemeral->v,
            cj_lbl,
        );
        Self::loaded_next_refines_abstract(
            self.ephemeral->v,
            self.ephemeral->v,
            cj_lbl,
        );
        self.ephemeral->v.freeze_for_commit_image_valid(snapshot, seq_end);
        self.ephemeral->v.frozen_snapshot_valid_implies_i_metadata_valid(snapshot, seq_end);
        assert(self.ephemeral->v.frozen_metadata(snapshot) == frozen_image_metadata_i(frozen));
        assert(cj_lbl.i(self.ephemeral->v)
            == AllocationJournal::Label::FreezeForCommit{
                frozen_journal: frozen_image_metadata_i(frozen),
            });
        assert(self.ephemeral->v.i().frozen_metadata_valid(
            frozen_image_metadata_i(frozen),
        ));
        self.ephemeral->v.semantic_inv_implies_i_inv();
        let meta = frozen_image_metadata_i(frozen);
        let alloc_lbl = AllocationJournal::Label::FreezeForCommit{frozen_journal: meta};
        assert(AllocationJournal::State::next_by(
            self.ephemeral->v.i(),
            self.ephemeral->v.i(),
            alloc_lbl,
            AllocationJournal::Step::freeze_for_commit(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        assert(AllocationJournal::State::next(
            self.ephemeral->v.i(),
            self.ephemeral->v.i(),
            alloc_lbl,
        )) by {
            reveal(AllocationJournal::State::next);
        }
        AllocationJournal::State::frozen_journal_is_valid_image(
            self.ephemeral->v.i(),
            self.ephemeral->v.i(),
            alloc_lbl,
        );
        self.ephemeral->v.i().frozen_image(meta).i_wf();
        self.persistent_i_wf();
        assert(self.persistent_i().seq_end <= frozen_metadata_i(frozen, self.ephemeral->v).seq_end);
        assert(AbstractCrashAwareJournal::State::next_by(
            self.i_abstract(),
            post.i_abstract(),
            self.label_i_abstract(post, lbl),
            AbstractCrashAwareJournal::Step::commit_start(),
        )) by {
            reveal(AbstractCrashAwareJournal::State::next_by);
        }
        reveal(AbstractCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn commit_prepared_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::commit_prepared(self, post, lbl),
        ensures
            post.refinement_inv(),
            AbstractCrashAwareJournal::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(post, lbl),
            ),
    {
        reveal(CrashAwareCachingDiskJournal::State::commit_prepared);
        let frozen = self.frozen.unwrap();
        let cj_lbl = CachingDiskJournal::Label::CommitPrepared{
            frozen: frozen.snapshot,
            seq_end: frozen.seq_end,
        };
        Self::loaded_next_refines_abstract(
            self.ephemeral->v,
            self.ephemeral->v,
            cj_lbl,
        );
        self.prepared_materialized_image_refines(frozen);
        assert(AbstractCrashAwareJournal::State::next_by(
            self.i_abstract(),
            post.i_abstract(),
            self.label_i_abstract(post, lbl),
            AbstractCrashAwareJournal::Step::internal(
                self.ephemeral->v.i().i_abstract(),
            ),
        )) by {
            reveal(AbstractCrashAwareJournal::State::next_by);
        }
        reveal(AbstractCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn commit_complete_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
        new_ephemeral: CachingDiskJournal::State,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::commit_complete(
                self,
                post,
                lbl,
                new_ephemeral,
            ),
        ensures
            post.refinement_inv(),
            AbstractCrashAwareJournal::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(post, lbl),
            ),
    {
        reveal(CrashAwareCachingDiskJournal::State::commit_complete);
        let frozen = self.frozen.unwrap();
        let meta = frozen_image_metadata_i(frozen);
        let cj_lbl = CachingDiskJournal::Label::DiscardOld{
            start_lsn: frozen.snapshot.boundary_lsn,
            require_end: lbl.arrow_CommitComplete_require_end(),
            deallocs: lbl.arrow_CommitComplete_discarded(),
        };
        CachingDiskJournal::State::discard_old_preserves_clean_watermark_au_page_bounds_clean(
            self.ephemeral->v,
            new_ephemeral,
            frozen.snapshot.boundary_lsn,
            lbl.arrow_CommitComplete_require_end(),
            lbl.arrow_CommitComplete_discarded(),
        );
        self.ephemeral->v.discard_old_preserves_frozen_materialization_certificate_at_boundary(
            new_ephemeral,
            cj_lbl,
            frozen.snapshot,
            frozen.seq_end,
        );
        self.ephemeral->v.discard_old_preserves_clean_watermark_records_bounded(
            new_ephemeral,
            frozen.snapshot.boundary_lsn,
            lbl.arrow_CommitComplete_require_end(),
            lbl.arrow_CommitComplete_discarded(),
        );
        assert(cj_lbl.i(self.ephemeral->v).arrow_DiscardOld_deallocs()
            == lbl.arrow_CommitComplete_discarded());
        assert(new_ephemeral.i().frozen_image(meta)
            == self.ephemeral->v.i().frozen_image(meta));
        Self::loaded_next_refines_abstract(
            self.ephemeral->v,
            new_ephemeral,
            cj_lbl,
        );
        let freeze_lbl = AllocationJournal::Label::FreezeForCommit{frozen_journal: meta};
        assert(AllocationJournal::State::next(
            self.ephemeral->v.i(),
            self.ephemeral->v.i(),
            freeze_lbl,
        )) by {
            reveal(AllocationJournal::State::next);
            reveal(AllocationJournal::State::next_by);
            assert(AllocationJournal::State::next_by(
                self.ephemeral->v.i(),
                self.ephemeral->v.i(),
                freeze_lbl,
                AllocationJournal::Step::freeze_for_commit(),
            ));
        }
        self.ephemeral->v.semantic_inv_implies_i_inv();
        AllocationJournal::State::frozen_journal_is_valid_image(
            self.ephemeral->v.i(),
            self.ephemeral->v.i(),
            freeze_lbl,
        );
        self.ephemeral->v.i().frozen_image(meta).i_wf();
        assert(post.persistent_i() == self.frozen_i().unwrap());
        assert(AbstractCrashAwareJournal::State::next_by(
            self.i_abstract(),
            post.i_abstract(),
            self.label_i_abstract(post, lbl),
            AbstractCrashAwareJournal::Step::commit_complete(
                new_ephemeral.i().i_abstract(),
            ),
        )) by {
            reveal(AbstractCrashAwareJournal::State::next_by);
        }
        reveal(AbstractCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn crash_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::crash(self, post, lbl),
        ensures
            post.refinement_inv(),
            AbstractCrashAwareJournal::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(post, lbl),
            ),
    {
        reveal(CrashAwareCachingDiskJournal::State::crash);
        let prepared_image = if lbl.arrow_Crash_keep_in_flight() {
            CachingDiskJournalImage::materialized_from_loaded_index(
                self.ephemeral->v,
                self.frozen.unwrap(),
            )
        } else if self.ephemeral is Unknown {
            self.persistent->image
        } else {
            CachingDiskJournalImage::materialized_from_loaded_index(
                self.ephemeral->v,
                self.persistent.metadata(),
            )
        };
        if self.ephemeral is Known {
            let metadata = if lbl.arrow_Crash_keep_in_flight() {
                frozen_image_metadata_i(self.frozen.unwrap())
            } else {
                frozen_image_metadata_i(self.persistent.metadata())
            };
            let frozen = if lbl.arrow_Crash_keep_in_flight() {
                self.frozen.unwrap()
            } else {
                self.persistent.metadata()
            };
            if lbl.arrow_Crash_keep_in_flight() || self.ephemeral->v.journal.status is Some {
                Self::materialization_certificate_implies_materialized_image_refines(
                    self.ephemeral->v,
                    frozen,
                );
            } else {
                Self::unloaded_materialized_persistent_image_refines(
                    self.ephemeral->v,
                    frozen,
                );
            }
            assert(self.ephemeral->v.i().acceptable_frozen_image(metadata, prepared_image.i()));
            assert(prepared_image.i().valid_image());
            assert(prepared_image.seq_end == frozen.seq_end);
            assert(frozen_image_metadata_i(frozen).seq_end == frozen.seq_end);
            assert(prepared_image.i().tj.seq_end() == metadata.seq_end);
            prepared_image.i_valid_image_seq_end_implies_wf();
            let state = self.ephemeral->v.i();
            let freeze_lbl = AllocationJournal::Label::FreezeForCommit{
                frozen_journal: metadata,
            };
            assert(AllocationJournal::State::next(state, state, freeze_lbl)) by {
                reveal(AllocationJournal::State::next);
                reveal(AllocationJournal::State::next_by);
                assert(AllocationJournal::State::next_by(
                    state,
                    state,
                    freeze_lbl,
                    AllocationJournal::Step::freeze_for_commit(),
                ));
            }
            self.ephemeral->v.semantic_inv_implies_i_inv();
            AllocationJournal::State::acceptable_frozen_image_matches_frozen_image(
                state,
                metadata,
                prepared_image.i(),
            );
            if lbl.arrow_Crash_keep_in_flight() {
                assert(post.persistent_i() == self.frozen_i().unwrap());
            } else {
                assert(post.persistent_i() == self.persistent_i());
            }
        } else {
            assert(!lbl.arrow_Crash_keep_in_flight());
            assert(prepared_image == self.persistent->image);
            assert(post.persistent_i() == self.persistent_i());
        }
        assert(AbstractCrashAwareJournal::State::next_by(
            self.i_abstract(),
            post.i_abstract(),
            self.label_i_abstract(post, lbl),
            AbstractCrashAwareJournal::Step::crash(),
        )) by {
            reveal(AbstractCrashAwareJournal::State::next_by);
        }
        reveal(AbstractCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn load_index_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
        new_ephemeral: CachingDiskJournal::State,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::load_index(self, post, lbl, new_ephemeral),
        ensures
            post.refinement_inv(),
            AbstractCrashAwareJournal::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(post, lbl),
            ),
    {
        reveal(CrashAwareCachingDiskJournal::State::load_index);
        let discovered_aus = lbl.arrow_LoadIndex_discovered_aus();
        let cj_lbl = CachingDiskJournal::Label::LoadIndex{discovered_aus};
        CrashAwareCachingDiskJournal::State::load_index_requires_recovery_phase(
            self,
            post,
            lbl,
            new_ephemeral,
        );
        Self::loaded_next_refines_abstract(self.ephemeral->v, new_ephemeral, cj_lbl);
        CachingDiskJournal::State::load_index_requires_unloaded(
            self.ephemeral->v,
            new_ephemeral,
            discovered_aus,
        );
        assert(self.ephemeral->v.journal.status is None);
        assert(self.ephemeral->v.disk.addrs_clean_or_evictable(
            self.ephemeral->v.disk.cache.dom(),
        ));
        CachingDiskJournal::State::load_index_recovery_clean_cache_implies_clean_watermark_au_page_bounds_clean(
            self.ephemeral->v,
            new_ephemeral,
            discovered_aus,
        );
        self.ephemeral->v.load_index_establishes_clean_watermark_records_bounded(
            new_ephemeral,
            discovered_aus,
        );
        assert(self.ephemeral->v.frozen_loose_persistence_certificate(
            self.persistent.metadata().snapshot,
        ));
        self.ephemeral->v.load_index_promotes_frozen_loose_to_materialization_certificate(
            new_ephemeral,
            discovered_aus,
            self.persistent.metadata().snapshot,
            self.persistent.metadata().seq_end,
        );
        assert(self.frozen is None);
        Self::loaded_internal_preserves_frozen_i(
            self.ephemeral->v,
            new_ephemeral,
            cj_lbl,
            self.persistent.metadata(),
        );
        assert(post.persistent_i() == self.persistent_i());
        assert(AbstractCrashAwareJournal::State::next_by(
            self.i_abstract(),
            post.i_abstract(),
            self.label_i_abstract(post, lbl),
            AbstractCrashAwareJournal::Step::internal(
                new_ephemeral.i().i_abstract(),
            ),
        )) by {
            reveal(AbstractCrashAwareJournal::State::next_by);
        }
        reveal(AbstractCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn observe_clean_aus_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
        new_ephemeral: CachingDiskJournal::State,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::observe_clean_aus(
                self,
                post,
                lbl,
                new_ephemeral,
            ),
        ensures
            post.refinement_inv(),
            AbstractCrashAwareJournal::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(post, lbl),
            ),
    {
        reveal(CrashAwareCachingDiskJournal::State::observe_clean_aus);
        let aus = lbl.arrow_ObserveCleanAUs_aus();
        let cj_lbl = CachingDiskJournal::Label::ObserveCleanAUs{aus};
        Self::loaded_next_refines_abstract(self.ephemeral->v, new_ephemeral, cj_lbl);
        self.ephemeral->v.observe_clean_aus_requires_loaded(new_ephemeral, aus);
        CachingDiskJournal::State::observe_clean_aus_preserves_clean_watermark_au_page_bounds_clean(
            self.ephemeral->v,
            new_ephemeral,
            aus,
        );
        self.ephemeral->v.observe_clean_aus_preserves_clean_watermark_records_bounded(
            new_ephemeral,
            aus,
        );
        self.ephemeral->v.observe_clean_aus_preserves_frozen_materialization_certificate(
            new_ephemeral,
            aus,
            self.persistent.metadata().snapshot,
            self.persistent.metadata().seq_end,
        );
        if self.frozen is Some {
            if self.prepared {
                self.ephemeral->v.observe_clean_aus_preserves_frozen_materialization_certificate(
                    new_ephemeral,
                    aus,
                    self.frozen.unwrap().snapshot,
                    self.frozen.unwrap().seq_end,
                );
            } else {
                self.ephemeral->v.observe_clean_aus_preserves_frozen_snapshot_and_prefix(
                    new_ephemeral,
                    aus,
                    self.frozen.unwrap().snapshot,
                    self.frozen.unwrap().seq_end,
                );
                new_ephemeral.frozen_snapshot_valid_implies_i_metadata_valid(
                    self.frozen.unwrap().snapshot,
                    self.frozen.unwrap().seq_end,
                );
            }
        }
        Self::loaded_internal_preserves_frozen_i(
            self.ephemeral->v,
            new_ephemeral,
            cj_lbl,
            self.persistent.metadata(),
        );
        if self.frozen is Some {
            Self::loaded_internal_preserves_frozen_i(
                self.ephemeral->v,
                new_ephemeral,
                cj_lbl,
                self.frozen.unwrap(),
            );
        }
        assert(post.persistent_i() == self.persistent_i());
        assert(post.frozen_i() == self.frozen_i());
        assert(AbstractCrashAwareJournal::State::next_by(
            self.i_abstract(),
            post.i_abstract(),
            self.label_i_abstract(post, lbl),
            AbstractCrashAwareJournal::Step::internal(
                new_ephemeral.i().i_abstract(),
            ),
        )) by {
            reveal(AbstractCrashAwareJournal::State::next_by);
        }
        reveal(AbstractCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn internal_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
        new_ephemeral: CachingDiskJournal::State,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::internal(self, post, lbl, new_ephemeral),
        ensures
            post.refinement_inv(),
            AbstractCrashAwareJournal::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(post, lbl),
            ),
    {
        reveal(CrashAwareCachingDiskJournal::State::internal);
        let cj_lbl = CachingDiskJournal::Label::Internal;
        Self::loaded_next_refines_abstract(self.ephemeral->v, new_ephemeral, cj_lbl);
        if self.ephemeral->v.journal.status is Some {
            self.ephemeral->v.internal_preserves_clean_watermark_au_page_bounds_clean(
                new_ephemeral,
            );
            self.ephemeral->v.internal_preserves_clean_watermark_records_bounded(
                new_ephemeral,
            );
            self.ephemeral->v.internal_preserves_frozen_materialization_certificate(
                new_ephemeral,
                self.persistent.metadata().snapshot,
                self.persistent.metadata().seq_end,
            );
        } else {
            CachingDiskJournal::State::internal_unloaded_preserves_cache_clean_or_evictable(
                self.ephemeral->v,
                new_ephemeral,
            );
            self.ephemeral->v.internal_unloaded_preserves_frozen_loose_persistence_certificate(
                new_ephemeral,
                self.persistent.metadata().snapshot,
                self.persistent.metadata().seq_end,
            );
            assert(new_ephemeral.journal.status is None);
        }
        if self.frozen is Some {
            if self.prepared {
                self.ephemeral->v.internal_preserves_frozen_materialization_certificate(
                    new_ephemeral,
                    self.frozen.unwrap().snapshot,
                    self.frozen.unwrap().seq_end,
                );
            } else {
                self.ephemeral->v.internal_preserves_frozen_snapshot(
                    new_ephemeral,
                    self.frozen.unwrap().snapshot,
                    self.frozen.unwrap().seq_end,
                );
            }
            new_ephemeral.frozen_snapshot_valid_implies_i_metadata_valid(
                self.frozen.unwrap().snapshot,
                self.frozen.unwrap().seq_end,
            );
        }
        Self::loaded_internal_preserves_frozen_i(
            self.ephemeral->v,
            new_ephemeral,
            cj_lbl,
            self.persistent.metadata(),
        );
        if self.frozen is Some {
            Self::loaded_internal_preserves_frozen_i(
                self.ephemeral->v,
                new_ephemeral,
                cj_lbl,
                self.frozen.unwrap(),
            );
        }
        assert(post.persistent_i() == self.persistent_i());
        assert(post.frozen_i() == self.frozen_i());
        assert(AbstractCrashAwareJournal::State::next_by(
            self.i_abstract(),
            post.i_abstract(),
            self.label_i_abstract(post, lbl),
            AbstractCrashAwareJournal::Step::internal(
                new_ephemeral.i().i_abstract(),
            ),
        )) by {
            reveal(AbstractCrashAwareJournal::State::next_by);
        }
        reveal(AbstractCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn internal_alloc_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
        new_ephemeral: CachingDiskJournal::State,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::internal_alloc(
                self,
                post,
                lbl,
                new_ephemeral,
            ),
        ensures
            post.refinement_inv(),
            AbstractCrashAwareJournal::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(post, lbl),
            ),
    {
        reveal(CrashAwareCachingDiskJournal::State::internal_alloc);
        let allocs = lbl.arrow_InternalAlloc_allocs();
        let deallocs = lbl.arrow_InternalAlloc_deallocs();
        let prune_aus = lbl.arrow_InternalAlloc_prune_aus();
        let cj_lbl = CachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus};
        Self::loaded_next_refines_abstract(self.ephemeral->v, new_ephemeral, cj_lbl);
        CachingDiskJournal::State::internal_alloc_requires_loaded(
            self.ephemeral->v,
            new_ephemeral,
            allocs,
            deallocs,
            prune_aus,
        );
        CachingDiskJournal::State::internal_alloc_preserves_clean_watermark_au_page_bounds_clean(
            self.ephemeral->v,
            new_ephemeral,
            allocs,
            deallocs,
            prune_aus,
        );
        self.ephemeral->v.internal_alloc_preserves_clean_watermark_records_bounded(
            new_ephemeral,
            allocs,
            deallocs,
            prune_aus,
        );
        self.ephemeral->v.internal_alloc_preserves_frozen_materialization_certificate(
            new_ephemeral,
            allocs,
            deallocs,
            prune_aus,
            self.persistent.metadata().snapshot,
            self.persistent.metadata().seq_end,
        );
        if self.frozen is Some {
            if self.prepared {
                self.ephemeral->v.internal_alloc_preserves_frozen_materialization_certificate(
                    new_ephemeral,
                    allocs,
                    deallocs,
                    prune_aus,
                    self.frozen.unwrap().snapshot,
                    self.frozen.unwrap().seq_end,
                );
            } else {
                self.ephemeral->v.internal_alloc_preserves_frozen_snapshot(
                    new_ephemeral,
                    allocs,
                    deallocs,
                    prune_aus,
                    self.frozen.unwrap().snapshot,
                    self.frozen.unwrap().seq_end,
                );
            }
            new_ephemeral.frozen_snapshot_valid_implies_i_metadata_valid(
                self.frozen.unwrap().snapshot,
                self.frozen.unwrap().seq_end,
            );
        }
        Self::loaded_internal_preserves_frozen_i(
            self.ephemeral->v,
            new_ephemeral,
            cj_lbl,
            self.persistent.metadata(),
        );
        if self.frozen is Some {
            Self::loaded_internal_preserves_frozen_i(
                self.ephemeral->v,
                new_ephemeral,
                cj_lbl,
                self.frozen.unwrap(),
            );
        }
        assert(post.persistent_i() == self.persistent_i());
        assert(post.frozen_i() == self.frozen_i());
        assert(AbstractCrashAwareJournal::State::next_by(
            self.i_abstract(),
            post.i_abstract(),
            self.label_i_abstract(post, lbl),
            AbstractCrashAwareJournal::Step::internal(
                new_ephemeral.i().i_abstract(),
            ),
        )) by {
            reveal(AbstractCrashAwareJournal::State::next_by);
        }
        reveal(AbstractCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn next_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.refinement_inv(),
            CrashAwareCachingDiskJournal::State::next(self, post, lbl),
        ensures
            post.refinement_inv(),
            AbstractCrashAwareJournal::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(post, lbl),
            ),
    {
        CrashAwareCachingDiskJournal::State::inv_next(self, post, lbl);
        reveal(CrashAwareCachingDiskJournal::State::next);
        reveal(CrashAwareCachingDiskJournal::State::next_by);
        let step = choose |step: CrashAwareCachingDiskJournal::Step| #![auto]
            CrashAwareCachingDiskJournal::State::next_by(self, post, lbl, step);
        match step {
            CrashAwareCachingDiskJournal::Step::load_ephemeral() => {
                self.load_ephemeral_refines(post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::read_for_recovery() => {
                self.read_for_recovery_refines(post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::query_end_lsn() => {
                self.query_end_lsn_refines(post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::put(new_ephemeral) => {
                self.put_refines(post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::query_lsn_persistence() => {
                self.query_lsn_persistence_refines(post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::commit_start() => {
                self.commit_start_refines(post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::commit_prepared() => {
                self.commit_prepared_refines(post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::commit_complete(new_ephemeral) => {
                self.commit_complete_refines(post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::crash() => {
                self.crash_refines(post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::load_index(new_ephemeral) => {
                self.load_index_refines(post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::observe_clean_aus(new_ephemeral) => {
                self.observe_clean_aus_refines(post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::internal(new_ephemeral) => {
                self.internal_refines(post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::internal_alloc(new_ephemeral) => {
                self.internal_alloc_refines(post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::dummy_to_use_type_params(_) => {
                assert(false);
            },
        }
    }

    pub proof fn next_refines_abstract(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.refinement_inv(),
            CrashAwareCachingDiskJournal::State::next(self, post, lbl),
        ensures
            post.refinement_inv(),
            AbstractCrashAwareJournal::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(post, lbl),
            ),
    {
        self.next_refines(post, lbl);
    }

    pub proof fn init_refines(self)
        requires
            CrashAwareCachingDiskJournal::State::initialize(self),
        ensures
            self.refinement_inv(),
            AbstractCrashAwareJournal::State::initialize(self.i_abstract()),
    {
        CrashAwareCachingDiskJournal::State::initialize_inductive(self);
        JournalImage::empty_is_valid_image();
        assert(self.persistent is Image);
        assert(self.persistent->image == CachingDiskJournalImage::empty());
        assert(self.persistent->image.i() == JournalImage::empty());
        assert(self.persistent->image.wf());
        assert(self.semantic_inv());
        assert(self.refinement_inv());
        TruncatedJournal::mkfs_ensures();
        assert(JournalImage::empty().tight_tj() == TruncatedJournal::mkfs());
        JournalImage::empty().i_wf();
        assert(self.persistent_i() == MsgHistory::empty_history_at(0));
        assert(AbstractCrashAwareJournal::State::initialize(self.i_abstract())) by {
            reveal(AbstractCrashAwareJournal::State::initialize);
        }
    }

    pub proof fn init_refines_abstract(self)
        requires
            CrashAwareCachingDiskJournal::State::initialize(self),
        ensures
            AbstractCrashAwareJournal::State::initialize(self.i_abstract()),
    {
        self.init_refines();
    }
}

} // verus!
