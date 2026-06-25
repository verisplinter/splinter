// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Loaded-state refinement from CachingDiskJournal to AllocationJournal.

#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::map::*;
use vstd::assert_maps_equal;

use crate::abstract_system::MsgHistory_v::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::allocation_layer::AllocationJournal_v::{
    AllocationJournal, JournalImage, JournalMetadata, addrs_in_aus, lsn_au_index_append_record,
    lsn_au_index_discard_up_to, lsn_au_index_discard_up_to_ensures,
};
use crate::allocation_layer::AllocationJournalRefinement_v::*;
use crate::disk::GenericDisk_v::{Address, AU, to_aus, to_aus_domain};
use crate::spec::AsyncDisk_t::RawPage;
use crate::implementation::CachedJournal_v::*;
use crate::implementation::CachingDisk_v::*;
use crate::implementation::CachingDiskJournal_v::*;
use crate::implementation::JournalTypes_v::to_journal_records;
use crate::journal::LinkedJournal_v::*;

verus!{

impl CachingDiskJournal::State {
    pub open spec fn frozen_persistence_certificate(
        self,
        frozen: JournalSnapshot,
    ) -> bool
    {
        self.persistent_visible_agree_on(self.frozen_prefix_domain(frozen))
    }

    pub open spec fn frozen_loose_persistence_certificate(
        self,
        frozen: JournalSnapshot,
    ) -> bool
    {
        self.persistent_visible_agree_on(self.frozen_loose_domain(frozen))
    }

    pub open spec fn frozen_materialization_certificate(
        self,
        frozen: JournalSnapshot,
        seq_end: LSN,
    ) -> bool
    {
        &&& self.frozen_snapshot_valid(frozen, seq_end)
        &&& self.frozen_persistence_certificate(frozen)
    }

    pub open spec fn allocation_unmarshalled_tail(self) -> MsgHistory {
        if self.journal.status is Some {
            cj_unmarshalled_tail(self.journal)
        } else {
            MsgHistory::empty_history_at(self.journal_tj().seq_end())
        }
    }

    pub open spec fn allocation_first(self) -> AU {
        if cj_freshest_rec(self.journal) is Some {
            self.lsn_au_index_or_empty()[self.journal_disk_view().boundary_lsn]
        } else {
            0
        }
    }

    pub open spec fn allocation_view_inv(self) -> bool {
        let disk_view = self.journal_disk_view();
        let unmarshalled_tail = self.allocation_unmarshalled_tail();
        let lsn_au_index = self.lsn_au_index_or_empty();
        &&& unmarshalled_tail.wf()
        &&& disk_view.wf_addrs()
        &&& self.mini_allocator.wf()
        &&& forall |lsn: LSN| #[trigger] lsn_au_index.contains_key(lsn)
            ==> lsn < unmarshalled_tail.seq_start
        &&& AllocationJournal::State::disk_domain_bounded_by_owned_aus(
            disk_view,
            lsn_au_index,
            self.mini_allocator,
        )
    }

    pub open spec fn allocation_view_semantic_inv(self) -> bool {
        let disk_view = self.journal_disk_view();
        let semantic_dv = self.journal_tj().disk_view;
        let freshest_rec = cj_freshest_rec(self.journal);
        let unmarshalled_tail = self.allocation_unmarshalled_tail();
        let lsn_au_index = self.lsn_au_index_or_empty();
        let au_page_bounds = self.au_page_bounds_i();
        let first = self.allocation_first();
        let computed_index = semantic_dv.build_lsn_au_index_au_walk(freshest_rec, first);
        &&& unmarshalled_tail.wf()
        &&& disk_view.wf_addrs()
        &&& self.mini_allocator.wf()
        &&& disk_view.path_decodable(freshest_rec)
        &&& semantic_dv.wf()
        &&& semantic_dv.wf_addrs()
        &&& semantic_dv.acyclic()
        &&& semantic_dv.is_nondangling_pointer(freshest_rec)
        &&& semantic_dv.block_in_bounds(freshest_rec)
        &&& semantic_dv.seq_start() <= semantic_dv.seq_end(freshest_rec)
        &&& semantic_dv.seq_end(freshest_rec) == unmarshalled_tail.seq_start
        &&& au_page_bounds.dom() =~= lsn_au_index.values()
        &&& freshest_rec is Some ==> {
            let root = freshest_rec.unwrap();
            &&& au_page_bounds.contains_key(root.au)
            &&& au_page_bounds[root.au] == root.page
            &&& lsn_au_index.contains_key(disk_view.boundary_lsn)
        }
        &&& AllocationJournal::State::semantic_journal_structure(
            semantic_dv,
            freshest_rec,
            computed_index,
            first,
        )
        &&& lsn_au_index == computed_index
        &&& AllocationJournal::State::disk_domain_bounded_by_owned_aus(
            disk_view,
            lsn_au_index,
            self.mini_allocator,
        )
        &&& AllocationJournal::State::disk_domain_not_free(semantic_dv, self.mini_allocator)
        &&& AllocationJournal::State::mini_allocator_follows_freshest_rec(
            freshest_rec,
            self.mini_allocator,
        )
        &&& semantic_dv.is_sub_disk(disk_view)
        &&& semantic_dv.domain_tight_wrt_index(lsn_au_index, freshest_rec)
        &&& forall |addr: Address| {
            &&& #[trigger] disk_view.entries.contains_key(addr)
            &&& au_page_bounds.contains_key(addr.au)
            &&& addr.page <= au_page_bounds[addr.au]
            &&& disk_view.boundary_lsn < disk_view.entries[addr].message_seq.seq_end
        } ==> semantic_dv.entries.contains_key(addr)
        &&& forall |addr: Address| #[trigger] semantic_dv.entries.contains_key(addr) ==> {
            &&& au_page_bounds.contains_key(addr.au)
            &&& addr.page <= au_page_bounds[addr.au]
        }
    }

    pub open spec(checked) fn semantic_inv(self) -> bool {
        &&& self.allocation_view_inv()
        &&& self.allocation_view_semantic_inv()
        &&& self.unloaded_backing_image_valid()
    }

    pub open spec(checked) fn refinement_inv(self) -> bool {
        &&& self.inv()
        &&& self.semantic_inv()
    }

    pub proof fn semantic_inv_implies_i_inv(self)
        requires
            self.semantic_inv(),
        ensures
            self.i().refinement_inv(),
            self.i().inv(),
            self.i().semantic_inv(),
            self.unloaded_backing_image_valid(),
    {
    }

    pub proof fn persistent_dom_wf(self)
        requires
            self.semantic_inv(),
        ensures
            self.disk.persistent.dom() <= Set::new(|addr: Address| addr.wf()),
    {
        assert(self.allocation_view_inv());
        assert(self.journal_disk_view().wf_addrs());
        assert forall |addr: Address| #[trigger] self.disk.persistent.dom().contains(addr)
            implies addr.wf() by {
            assert(self.disk.persistent.contains_key(addr));
            assert(self.disk.visible().contains_key(addr));
            assert(to_journal_records(self.disk.visible()).contains_key(addr));
            assert(self.journal_disk_view().entries.contains_key(addr));
        }
    }

    pub proof fn i_frozen_image_accessible_aus(
        self,
        meta: JournalMetadata,
    )
        requires
            self.refinement_inv(),
            self.i().frozen_metadata_valid(meta),
        ensures
            self.i().frozen_image(meta).accessible_aus() <= self.accessible_aus(),
    {
        self.i_accessible_aus_subset_accessible_aus();
        let image = self.i().frozen_image(meta);
        assert(image.accessible_aus() <= self.i().accessible_aus()) by {
            assert forall |au: AU| #[trigger] image.accessible_aus().contains(au)
                implies self.i().accessible_aus().contains(au) by {
                let addr = choose |addr: Address|
                    #![trigger image.tj.disk_view.entries.dom().contains(addr)]
                    image.tj.disk_view.entries.dom().contains(addr) && addr.au == au;
                assert(image.tj.disk_view.entries.contains_key(addr));
                assert(self.i().disk_view.entries.contains_key(addr));
                to_aus_domain(self.i().disk_view.entries.dom());
                assert(to_aus(self.i().disk_view.entries.dom()).contains(addr.au));
                assert(self.i().accessible_aus().contains(addr.au));
            }
        }
        assert forall |au: AU| #[trigger] image.accessible_aus().contains(au)
            implies self.accessible_aus().contains(au) by {
            assert(self.i().accessible_aus().contains(au));
        }
    }

    pub proof fn i_accessible_aus_subset_accessible_aus(self)
        requires
            self.refinement_inv(),
        ensures
            self.i().accessible_aus() <= self.accessible_aus(),
    {
        assert(self.i().disk_view == self.journal_disk_view());
        assert(self.i().mini_allocator == self.mini_allocator);
        assert(self.i().lsn_au_index == self.lsn_au_index_or_empty());
        assert forall |au: AU| #[trigger] self.i().accessible_aus().contains(au)
            implies self.accessible_aus().contains(au) by {
            if self.i().mini_allocator.all_aus().contains(au) {
                assert(self.mini_allocator.all_aus().contains(au));
            } else {
                assert(to_aus(self.journal_disk_view().entries.dom()).contains(au));
                if self.journal.status is Some {
                    assert(AllocationJournal::State::disk_domain_bounded_by_owned_aus(
                        self.journal_disk_view(),
                        self.lsn_au_index_or_empty(),
                        self.mini_allocator,
                    ));
                    assert(self.lsn_au_index_or_empty().values().contains(au));
                    assert(self.accessible_aus().contains(au));
                } else {
                    assert(self.journal_disk_view().entries.dom() == self.disk.visible().dom()) by {
                        assert_maps_equal!(
                            self.journal_disk_view().entries,
                            self.journal_disk_view().entries,
                        );
                        assert forall |addr: Address|
                            #[trigger] self.journal_disk_view().entries.contains_key(addr)
                            <==> self.disk.visible().contains_key(addr) by { }
                    }
                    assert(to_aus(self.disk.visible().dom()).contains(au));
                    assert(self.accessible_aus().contains(au));
                }
            }
        }
    }

    pub proof fn i_refinement_inv_implies_semantic_inv(self)
        requires
            self.inv(),
            self.i().refinement_inv(),
            self.unloaded_backing_image_valid(),
        ensures
            self.semantic_inv(),
    {
    }

    pub proof fn loaded_i_view_facts(self)
        requires
            self.inv(),
            self.semantic_inv(),
            self.journal.status is Some,
        ensures
            self.i().refinement_inv(),
            self.i().inv(),
            self.i().semantic_inv(),
            self.i().tj() == self.journal_tj(),
            self.i().disk_view == self.journal_disk_view(),
            self.i().unmarshalled_tail == cj_unmarshalled_tail(self.journal),
            self.i().seq_end() == self.journal.seq_end(),
            self.i().lsn_au_index == cj_lsn_au_index(self.journal),
    {
        self.semantic_inv_implies_i_inv();
        self.interpreted_tj_matches();
    }

    pub proof fn freeze_for_commit_label_implies_i_metadata_valid(
        self,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.inv(),
            self.semantic_inv(),
            CachingDiskJournal::State::next(
                self,
                self,
                CachingDiskJournal::Label::FreezeForCommit{frozen, seq_end},
            ),
        ensures
            self.i().frozen_metadata_valid(self.frozen_metadata(frozen)),
    {
        self.freeze_for_commit_image_valid(frozen, seq_end);
        self.loaded_i_view_facts();
        self.i().tj_inherits_semantic_structure();
        let meta = self.frozen_metadata(frozen);
        assert(meta.seq_end == seq_end);
        assert(meta.boundary_lsn == frozen.boundary_lsn);
        assert(meta.freshest_rec == frozen.freshest_rec());
        assert(meta.first == frozen.first());
        assert(self.i().seq_start() == self.journal.snapshot.boundary_lsn);
        assert(self.i().seq_end() == self.journal.seq_end());
        assert(self.journal.seq_start() <= frozen.boundary_lsn);
        assert(frozen.boundary_lsn <= self.journal.seq_end());
        if meta.freshest_rec is Some {
            let root = meta.freshest_rec.unwrap();
            let last_lsn = (meta.seq_end - 1) as nat;
            assert(self.i().disk_view.entries.contains_key(root));
            assert(self.i().disk_view.entries[root].message_seq.seq_end == meta.seq_end);
            assert(meta.boundary_lsn < meta.seq_end);
            assert(self.i().lsn_au_index.contains_key(meta.boundary_lsn));
            assert(self.i().lsn_au_index[meta.boundary_lsn] == meta.first);
            assert(self.i().au_page_bounds.contains_key(root.au));
            assert(root.page <= self.i().au_page_bounds[root.au]);
            assert(self.journal_tj().disk_view.entries[root].message_seq.contains(last_lsn));
            assert(self.journal_tj().disk_view.addr_supports_lsn(root, last_lsn));
            let aj = self.i();
            let first = if aj.freshest_rec is Some {
                aj.lsn_au_index[aj.seq_start()]
            } else {
                0
            };
            assert(aj.lsn_au_index == aj.tj().build_lsn_au_index_from_first(first));
            aj.tj().build_lsn_au_index_from_first_ensures(first);
            assert(self.journal_tj().disk_view.index_keys_exist_valid_entries(
                self.i().lsn_au_index,
            ));
            self.journal_tj().disk_view.addr_supports_lsn_consistent_with_index(
                self.i().lsn_au_index,
                last_lsn,
                root,
            );
            assert(self.i().lsn_au_index.contains_key(last_lsn));
            assert(self.i().lsn_au_index[last_lsn] == root.au);
        } else {
            assert(meta.first == 0);
            assert(meta.boundary_lsn == meta.seq_end);
        }
    }

    pub proof fn frozen_snapshot_valid_implies_i_metadata_valid(
        self,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.inv(),
            self.semantic_inv(),
            self.frozen_snapshot_valid(frozen, seq_end),
        ensures
            self.i().frozen_metadata_valid(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
    {
        self.loaded_i_view_facts();
        self.i().tj_inherits_semantic_structure();
        let meta = JournalMetadata{
            boundary_lsn: frozen.boundary_lsn,
            seq_end,
            freshest_rec: frozen.freshest_rec(),
            first: frozen.first(),
        };
        assert(self.i().seq_start() == self.journal.snapshot.boundary_lsn);
        assert(self.i().seq_end() == self.journal.seq_end());
        assert(self.journal.seq_start() <= frozen.boundary_lsn);
        assert(frozen.boundary_lsn <= seq_end);
        if meta.freshest_rec is Some {
            let root = meta.freshest_rec.unwrap();
            let last_lsn = (meta.seq_end - 1) as nat;
            assert(self.i().disk_view.entries.contains_key(root));
            assert(self.i().disk_view.entries[root].message_seq.seq_end == meta.seq_end);
            assert(meta.boundary_lsn < meta.seq_end);
            assert(self.i().lsn_au_index.contains_key(meta.boundary_lsn));
            assert(self.i().lsn_au_index[meta.boundary_lsn] == meta.first);
            assert(self.i().au_page_bounds.contains_key(root.au));
            assert(root.page <= self.i().au_page_bounds[root.au]);
            assert(self.journal_tj().disk_view.entries.contains_key(root)) by {
                assert(self.allocation_view_semantic_inv());
                assert(self.journal_disk_view().entries.contains_key(root));
                assert(self.au_page_bounds.contains_key(root.au));
                assert(root.page <= self.au_page_bounds[root.au]);
                assert(self.journal_disk_view().boundary_lsn
                    < self.journal_disk_view().entries[root].message_seq.seq_end);
            }
            assert(self.journal_tj().disk_view.entries[root].message_seq.contains(last_lsn));
            assert(self.journal_tj().disk_view.addr_supports_lsn(root, last_lsn));
            let aj = self.i();
            let first = if aj.freshest_rec is Some {
                aj.lsn_au_index[aj.seq_start()]
            } else {
                0
            };
            assert(aj.lsn_au_index == aj.tj().build_lsn_au_index_from_first(first));
            aj.tj().build_lsn_au_index_from_first_ensures(first);
            assert(self.journal_tj().disk_view.index_keys_exist_valid_entries(
                self.i().lsn_au_index,
            ));
            self.journal_tj().disk_view.addr_supports_lsn_consistent_with_index(
                self.i().lsn_au_index,
                last_lsn,
                root,
            );
            assert(self.i().lsn_au_index.contains_key(last_lsn));
            assert(self.i().lsn_au_index[last_lsn] == root.au);
        } else {
            assert(meta.first == 0);
            assert(meta.boundary_lsn == meta.seq_end);
        }
        assert(self.frozen_metadata(frozen) == JournalMetadata{
            boundary_lsn: frozen.boundary_lsn,
            seq_end,
            freshest_rec: frozen.freshest_rec(),
            first: frozen.first(),
        });
    }

    pub proof fn frozen_tj_matches_i_frozen_tj(
        self,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.inv(),
            self.semantic_inv(),
            self.frozen_snapshot_valid(frozen, seq_end),
        ensures
            self.frozen_loose_domain(frozen) =~= self.i().frozen_loose_domain(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
            self.frozen_tj(frozen) == self.i().frozen_tj(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
            self.frozen_prefix_domain(frozen) =~= self.i().frozen_prefix_domain(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
            (JournalImage{
                tj: self.frozen_tj(frozen),
                first: frozen.first(),
            }) == self.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
    {
        let meta = JournalMetadata{
            boundary_lsn: frozen.boundary_lsn,
            seq_end,
            freshest_rec: frozen.freshest_rec(),
            first: frozen.first(),
        };
        assert(self.frozen_metadata(frozen) == meta);
        assert(self.i().disk_view == self.journal_disk_view());
        assert(self.i().lsn_au_index == self.lsn_au_index_or_empty());
        assert(self.i().frozen_lsns(meta) =~= self.frozen_lsns(frozen)) by {
            assert forall |lsn: LSN| #[trigger] self.i().frozen_lsns(meta).contains(lsn)
                <==> self.frozen_lsns(frozen).contains(lsn) by {}
        }
        assert(self.i().frozen_lsn_au_index(meta)
            =~= self.lsn_au_index_or_empty().restrict(self.frozen_lsns(frozen))) by {
            assert forall |lsn: LSN|
                #[trigger] self.i().frozen_lsn_au_index(meta).contains_key(lsn)
                <==> self.lsn_au_index_or_empty().restrict(self.frozen_lsns(frozen)).contains_key(lsn) by {}
            assert forall |lsn: LSN|
                #[trigger] self.i().frozen_lsn_au_index(meta).contains_key(lsn)
                implies self.i().frozen_lsn_au_index(meta)[lsn]
                    == self.lsn_au_index_or_empty().restrict(self.frozen_lsns(frozen))[lsn] by {}
        }
        assert(self.i().frozen_lsn_au_index(meta).values()
            =~= self.lsn_au_index_or_empty().restrict(self.frozen_lsns(frozen)).values());
        assert(addrs_in_aus(self.i().frozen_lsn_au_index(meta).values())
            =~= addresses_in_aus(
                self.lsn_au_index_or_empty().restrict(self.frozen_lsns(frozen)).values(),
            )) by {
            assert forall |addr: Address| #[trigger] addrs_in_aus(
                self.i().frozen_lsn_au_index(meta).values(),
            ).contains(addr)
                <==> addresses_in_aus(
                    self.lsn_au_index_or_empty().restrict(self.frozen_lsns(frozen)).values(),
                ).contains(addr) by {}
        }
        assert(self.i().frozen_domain(meta) =~= self.frozen_loose_domain(frozen));
        assert(self.i().frozen_loose_domain(meta) =~= self.frozen_loose_domain(frozen));
        assert(self.i().frozen_tj(meta).disk_view.entries
            =~= self.frozen_tj(frozen).disk_view.entries) by {
            assert_maps_equal!(
                self.i().frozen_tj(meta).disk_view.entries,
                self.frozen_tj(frozen).disk_view.entries,
            );
        }
        assert(self.i().frozen_tj(meta) == self.frozen_tj(frozen));
        assert(self.i().frozen_image(meta).tight_tj()
            == (JournalImage{tj: self.frozen_tj(frozen), first: frozen.first()}).tight_tj());
        assert(self.frozen_prefix_domain(frozen) =~= self.i().frozen_prefix_domain(meta)) by {
            assert forall |addr: Address| #[trigger] self.frozen_prefix_domain(frozen).contains(addr)
                <==> self.i().frozen_prefix_domain(meta).contains(addr) by {}
        }
    }

    pub proof fn i_metadata_valid_implies_frozen_tj_matches_i(
        self,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.inv(),
            self.semantic_inv(),
            self.i().frozen_metadata_valid(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
        ensures
            self.frozen_metadata(frozen) == (JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
            self.frozen_loose_domain(frozen) =~= self.i().frozen_loose_domain(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
            self.frozen_tj(frozen) == self.i().frozen_tj(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
            self.frozen_prefix_domain(frozen) =~= self.i().frozen_prefix_domain(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
            (JournalImage{
                tj: self.frozen_tj(frozen),
                first: frozen.first(),
            }) == self.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
    {
        let meta = JournalMetadata{
            boundary_lsn: frozen.boundary_lsn,
            seq_end,
            freshest_rec: frozen.freshest_rec(),
            first: frozen.first(),
        };
        assert(self.i().disk_view == self.journal_disk_view());
        assert(self.i().lsn_au_index == self.lsn_au_index_or_empty());
        if frozen.freshest_rec() is Some {
            let root = frozen.freshest_rec().unwrap();
            assert(self.i().disk_view.entries[root].message_seq.seq_end == seq_end);
            assert(self.journal_disk_view().entries[root].message_seq.seq_end == seq_end);
            assert(self.frozen_seq_end(frozen) == seq_end);
        } else {
            assert(frozen.boundary_lsn == seq_end);
            assert(self.frozen_seq_end(frozen) == seq_end);
        }
        assert(self.frozen_metadata(frozen) == meta);
        assert(self.i().frozen_lsns(meta) =~= self.frozen_lsns(frozen)) by {
            assert forall |lsn: LSN| #[trigger] self.i().frozen_lsns(meta).contains(lsn)
                <==> self.frozen_lsns(frozen).contains(lsn) by {}
        }
        assert(self.i().frozen_lsn_au_index(meta)
            =~= self.lsn_au_index_or_empty().restrict(self.frozen_lsns(frozen))) by {
            assert forall |lsn: LSN|
                #[trigger] self.i().frozen_lsn_au_index(meta).contains_key(lsn)
                <==> self.lsn_au_index_or_empty().restrict(self.frozen_lsns(frozen)).contains_key(lsn) by {}
            assert forall |lsn: LSN|
                #[trigger] self.i().frozen_lsn_au_index(meta).contains_key(lsn)
                implies self.i().frozen_lsn_au_index(meta)[lsn]
                    == self.lsn_au_index_or_empty().restrict(self.frozen_lsns(frozen))[lsn] by {}
        }
        assert(self.i().frozen_lsn_au_index(meta).values()
            =~= self.lsn_au_index_or_empty().restrict(self.frozen_lsns(frozen)).values());
        assert(addrs_in_aus(self.i().frozen_lsn_au_index(meta).values())
            =~= addresses_in_aus(
                self.lsn_au_index_or_empty().restrict(self.frozen_lsns(frozen)).values(),
            )) by {
            assert forall |addr: Address| #[trigger] addrs_in_aus(
                self.i().frozen_lsn_au_index(meta).values(),
            ).contains(addr)
                <==> addresses_in_aus(
                    self.lsn_au_index_or_empty().restrict(self.frozen_lsns(frozen)).values(),
                ).contains(addr) by {}
        }
        assert(self.i().frozen_domain(meta) =~= self.frozen_loose_domain(frozen));
        assert(self.i().frozen_loose_domain(meta) =~= self.frozen_loose_domain(frozen));
        assert(self.i().frozen_tj(meta).disk_view.entries
            =~= self.frozen_tj(frozen).disk_view.entries) by {
            assert_maps_equal!(
                self.i().frozen_tj(meta).disk_view.entries,
                self.frozen_tj(frozen).disk_view.entries,
            );
        }
        assert(self.i().frozen_tj(meta) == self.frozen_tj(frozen));
        assert(self.i().frozen_image(meta).tight_tj()
            == (JournalImage{tj: self.frozen_tj(frozen), first: frozen.first()}).tight_tj());
        assert(self.frozen_prefix_domain(frozen) =~= self.i().frozen_prefix_domain(meta)) by {
            assert forall |addr: Address| #[trigger] self.frozen_prefix_domain(frozen).contains(addr)
                <==> self.i().frozen_prefix_domain(meta).contains(addr) by {}
        }
    }

    pub proof fn frozen_prefix_domain_matches_i(
        self,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.inv(),
            self.semantic_inv(),
            self.frozen_snapshot_valid(frozen, seq_end),
        ensures
            self.frozen_prefix_domain(frozen) =~= self.i().frozen_prefix_domain(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
    {
        let meta = JournalMetadata{
            boundary_lsn: frozen.boundary_lsn,
            seq_end,
            freshest_rec: frozen.freshest_rec(),
            first: frozen.first(),
        };
        self.frozen_tj_matches_i_frozen_tj(frozen, seq_end);
        assert(self.i().frozen_image(meta).tight_tj()
            == (JournalImage{tj: self.frozen_tj(frozen), first: frozen.first()}).tight_tj());
        assert(self.i().frozen_loose_domain(meta) =~= self.frozen_loose_domain(frozen));
        assert(self.frozen_prefix_domain(frozen) =~= self.i().frozen_prefix_domain(meta)) by {
            assert forall |addr: Address| #[trigger] self.frozen_prefix_domain(frozen).contains(addr)
                <==> self.i().frozen_prefix_domain(meta).contains(addr) by {}
        }
    }

    pub proof fn disk_reads_ensures(self, reads: Map<Address, RawPage>)
        requires
            self.disk.inv(),
            CachingDisk::State::next(
                self.disk,
                self.disk,
                CachingDisk::Label::Access{reads, writes: Map::empty()},
            ),
        ensures
            reads <= self.disk.cache,
            forall |addr: Address| #[trigger] reads.contains_key(addr)
                ==> to_journal_records(reads)[addr] == self.journal_disk_view().entries[addr],
    {
        CachingDisk::State::access_effect(self.disk, self.disk, reads, Map::empty());
        assert forall |addr: Address| #[trigger] reads.contains_key(addr)
            implies to_journal_records(reads)[addr] == self.journal_disk_view().entries[addr] by {
            assert(reads <= self.disk.cache);
            assert(self.disk.visible().contains_key(addr));
            assert(self.disk.visible()[addr] == self.disk.cache[addr]);
            assert(reads[addr] == self.disk.visible()[addr]);
        }
    }

}

impl CachingDiskJournal::Label {
    pub open spec fn i(self, state: CachingDiskJournal::State) -> AllocationJournal::Label {
        match self {
            Self::ReadForRecovery{messages} => {
                AllocationJournal::Label::ReadForRecovery{messages}
            },
            Self::FreezeForCommit{frozen, seq_end} => {
                AllocationJournal::Label::FreezeForCommit{
                    frozen_journal: JournalMetadata{
                        boundary_lsn: frozen.boundary_lsn,
                        seq_end,
                        freshest_rec: frozen.freshest_rec(),
                        first: frozen.first(),
                    },
                }
            },
            Self::QueryEndLsn{end_lsn} => {
                AllocationJournal::Label::QueryEndLsn{end_lsn}
            },
            Self::Put{messages} => {
                AllocationJournal::Label::Put{messages}
            },
            Self::DiscardOld{start_lsn, require_end, deallocs} => {
                AllocationJournal::Label::DiscardOld{
                    start_lsn,
                    require_end,
                    deallocs,
                }
            },
            Self::ObserveCleanAUs{aus} => {
                AllocationJournal::Label::InternalAllocations{
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                }
            },
            Self::CommitPrepared{frozen, seq_end} => {
                AllocationJournal::Label::InternalAllocations{
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                }
            },
            Self::LoadIndex{discovered_aus} => {
                AllocationJournal::Label::InternalAllocations{
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                }
            },
            Self::Internal => {
                AllocationJournal::Label::InternalAllocations{
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                }
            },
            Self::InternalAlloc{allocs, deallocs, prune_aus} => {
                AllocationJournal::Label::InternalAllocations{allocs, deallocs}
            },
        }
    }
}

impl CachingDiskJournal::State {
    pub proof fn init_refines(
        self,
        snapshot: JournalSnapshot,
        disk: CachingDisk::State,
    )
        requires
            CachingDiskJournal::State::initialize(self, snapshot, disk),
            self.backing_journal_image().valid_image(),
        ensures
            self.inv(),
            self.semantic_inv(),
            self.refinement_inv(),
            AllocationJournal::State::initialize(
                self.i(),
                self.backing_journal_image(),
            ),
    {
        reveal(CachingDiskJournal::State::initialize);
        reveal(AllocationJournal::State::initialize);

        CachingDiskJournal::State::initialize_inductive(self, snapshot, disk);
        let image = self.backing_journal_image();
        image.valid_image_implies_tight_valid_image();
        image.tj.disk_view.path_build_bookkeeping_matches_tight(
            image.tj.freshest_rec,
            snapshot.first(),
        );
        assert(self.inv());
        assert(self.journal == CachedJournal::State{snapshot, status: Option::None});
        assert(self.i().disk_view == self.journal_disk_view());
        assert(self.i().freshest_rec == image.tj.freshest_rec);
        assert(image.tj == self.journal_backing_tj());
        assert(image.tight_tj() == self.journal_tj());
        assert(self.journal_backing_tj().seq_end() == self.journal_tj().seq_end());
        image.tj.disk_view.loose_build_lsn_au_index_au_walk_matches_tight(
            image.tj.freshest_rec,
            snapshot.first(),
        );
        image.tj.disk_view.loose_build_au_page_bounds_au_walk_matches_tight(
            image.tj.freshest_rec,
            snapshot.first(),
        );
        assert(self.lsn_au_index_or_empty()
            == image.tj.disk_view.loose_build_lsn_au_index_au_walk(
                image.tj.freshest_rec,
                snapshot.first(),
            ));
        assert(self.i().au_page_bounds
            == image.tj.disk_view.loose_build_au_page_bounds_au_walk(
                image.tj.freshest_rec,
                snapshot.first(),
            ));
        assert_maps_equal!(
            self.lsn_au_index_or_empty(),
            self.journal_tj().build_lsn_au_index_from_first(snapshot.first())
        );
        assert(self.i().lsn_au_index == self.lsn_au_index_or_empty());
        assert(self.i().lsn_au_index
            == image.tj.disk_view.path_build_lsn_au_index_au_walk(
                image.tj.freshest_rec,
                snapshot.first(),
            ));
        assert(self.i().au_page_bounds
            == image.tj.disk_view.path_build_au_page_bounds_au_walk(
                image.tj.freshest_rec,
                snapshot.first(),
            ));
        assert(self.i().unmarshalled_tail
            == MsgHistory::empty_history_at(self.journal_tj().seq_end()));
        assert(image.valid_image());
        AllocationJournal::State::initialize_inductive(self.i(), image);
        AllocationJournal::State::initialize_semantic_inv(self.i(), image);
        assert(self.unloaded_backing_image_valid());
        assert(self.semantic_inv());
        assert(self.refinement_inv());
    }

    pub proof fn load_from_persistent_refines_image(
        snapshot: JournalSnapshot,
        persistent: Map<Address, RawPage>,
        image: JournalImage,
    )
        requires
            image == (JournalImage{
                tj: TruncatedJournal{
                    freshest_rec: snapshot.freshest_rec(),
                    disk_view: DiskView{
                        boundary_lsn: snapshot.boundary_lsn,
                        entries: to_journal_records(persistent),
                    },
                },
                first: snapshot.first(),
            }),
            image.valid_image(),
        ensures
            ({
                let loaded = CachingDiskJournal::State::load_from_persistent(snapshot, persistent);
                &&& loaded.backing_journal_image() == image
                &&& loaded.refinement_inv()
                &&& AllocationJournal::State::initialize(loaded.i(), image)
            }),
    {
        let loaded = CachingDiskJournal::State::load_from_persistent(snapshot, persistent);
        let disk = CachingDiskJournal::State::disk_from_persistent(persistent);
        assert(loaded.disk == disk);
        assert(loaded.disk.visible() =~= persistent) by {
            assert forall |addr: Address| #[trigger] loaded.disk.visible().contains_key(addr)
                implies persistent.contains_key(addr) by {
                assert(loaded.disk.cache == Map::<Address, RawPage>::empty());
            }
            assert forall |addr: Address| #[trigger] persistent.contains_key(addr)
                implies loaded.disk.visible().contains_key(addr) by {
                assert(loaded.disk.persistent.contains_key(addr));
            }
        }
        assert(loaded.journal_disk_view().entries == to_journal_records(persistent)) by {
            assert_maps_equal!(
                loaded.journal_disk_view().entries,
                to_journal_records(persistent),
                addr => {
                    if loaded.journal_disk_view().entries.contains_key(addr) {
                        assert(loaded.disk.visible().contains_key(addr));
                        assert(persistent.contains_key(addr));
                        assert(loaded.disk.visible()[addr] == persistent[addr]);
                    }
                    if to_journal_records(persistent).contains_key(addr) {
                        assert(persistent.contains_key(addr));
                        assert(loaded.disk.visible().contains_key(addr));
                        assert(loaded.disk.visible()[addr] == persistent[addr]);
                    }
                }
            );
        }
        assert(loaded.journal_disk_view() == image.tj.disk_view);
        assert(loaded.journal_backing_tj() == image.tj);
        assert(loaded.backing_journal_image() == image);
        let init_bounds = image.tj.disk_view.loose_build_au_page_bounds_au_walk(
            image.tj.freshest_rec,
            image.first,
        );
        assert(loaded.au_page_bounds_i() == init_bounds);
        image.valid_image_implies_tight_valid_image();
        image.tj.disk_view.path_build_bookkeeping_matches_tight(
            image.tj.freshest_rec,
            snapshot.first(),
        );
        image.tj.disk_view.loose_build_lsn_au_index_au_walk_matches_tight(
            image.tj.freshest_rec,
            snapshot.first(),
        );
        image.tj.disk_view.loose_build_au_page_bounds_au_walk_matches_tight(
            image.tj.freshest_rec,
            snapshot.first(),
        );
        assert(loaded.inv());
        assert(loaded.i().disk_view == loaded.journal_disk_view());
        assert(loaded.i().freshest_rec == image.tj.freshest_rec);
        assert(image.tj == loaded.journal_backing_tj());
        assert(image.tight_tj() == loaded.journal_tj());
        assert(loaded.journal_backing_tj().seq_end() == loaded.journal_tj().seq_end());
        assert(loaded.lsn_au_index_or_empty()
            == image.tj.disk_view.loose_build_lsn_au_index_au_walk(
                image.tj.freshest_rec,
                snapshot.first(),
            ));
        assert(loaded.i().au_page_bounds
            == image.tj.disk_view.loose_build_au_page_bounds_au_walk(
                image.tj.freshest_rec,
                snapshot.first(),
            ));
        assert_maps_equal!(
            loaded.lsn_au_index_or_empty(),
            loaded.journal_tj().build_lsn_au_index_from_first(snapshot.first())
        );
        assert(loaded.i().lsn_au_index == loaded.lsn_au_index_or_empty());
        assert(loaded.i().lsn_au_index
            == image.tj.disk_view.path_build_lsn_au_index_au_walk(
                image.tj.freshest_rec,
                snapshot.first(),
            ));
        assert(loaded.i().au_page_bounds
            == image.tj.disk_view.path_build_au_page_bounds_au_walk(
                image.tj.freshest_rec,
                snapshot.first(),
            ));
        assert(loaded.i().unmarshalled_tail
            == MsgHistory::empty_history_at(loaded.journal_tj().seq_end()));
        AllocationJournal::State::initialize_inductive(loaded.i(), image);
        AllocationJournal::State::initialize_semantic_inv(loaded.i(), image);
        assert(loaded.unloaded_backing_image_valid());
        assert(loaded.semantic_inv());
        assert(loaded.refinement_inv());
    }

    pub proof fn query_end_lsn_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
    )
        requires
            self.inv(),
            post.inv(),
            self.semantic_inv(),
            CachingDiskJournal::State::query_end_lsn(self, post, lbl),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::query_end_lsn);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let end_lsn = lbl.arrow_QueryEndLsn_end_lsn();
        let journal_lbl = CachedJournal::Label::QueryEndLsn{end_lsn};
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(self.journal, self.journal, journal_lbl, step);
        match cj_step {
            CachedJournal::Step::query_end_lsn() => {
                reveal(CachedJournal::State::query_end_lsn);
            },
            _ => {
                assert(false);
            },
        }
        let i_lbl = lbl.i(self);
        self.loaded_i_view_facts();
        assert(post == self);
        assert(self.i().seq_end() == self.journal.seq_end());
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            i_lbl,
            AllocationJournal::Step::query_end_lsn(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn put_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
        new_journal: CachedJournal::State,
    )
        requires
            self.inv(),
            post.inv(),
            self.semantic_inv(),
            CachingDiskJournal::State::put(self, post, lbl, new_journal),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::put);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let messages = lbl.arrow_Put_messages();
        let journal_lbl = CachedJournal::Label::Put{messages};
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(self.journal, new_journal, journal_lbl, step);
        match cj_step {
            CachedJournal::Step::put() => {
                reveal(CachedJournal::State::put);
            },
            _ => {
                assert(false);
            },
        }
        let i_lbl = lbl.i(self);
        self.loaded_i_view_facts();
        assert(post.journal == new_journal);
        assert(post.disk == self.disk);
        assert(post.mini_allocator == self.mini_allocator);
        assert(post.journal.snapshot == self.journal.snapshot);
        assert(post.journal_tj() == self.journal_tj());
        assert(self.i().seq_end() == self.journal.seq_end());
        assert(post.i().unmarshalled_tail == self.i().unmarshalled_tail.concat(messages));
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            i_lbl,
            AllocationJournal::Step::put(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn read_for_recovery_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
        reads: Map<Address, RawPage>,
    )
        requires
            self.inv(),
            post.inv(),
            self.semantic_inv(),
            CachingDiskJournal::State::read_for_recovery(self, post, lbl, reads),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::read_for_recovery);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        self.disk_reads_ensures(reads);
        self.loaded_i_view_facts();

        let messages = lbl.arrow_ReadForRecovery_messages();
        let journal_lbl = CachedJournal::Label::ReadForRecovery{
            messages,
            reads: to_journal_records(reads),
        };
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(self.journal, self.journal, journal_lbl, step);
        match cj_step {
            CachedJournal::Step::read_for_recovery(start_lsn, addr) => {
                reveal(CachedJournal::State::read_for_recovery);
                assert(reads.contains_key(addr));
                assert(messages == to_journal_records(reads)[addr].message_seq.maybe_discard_old(
                    self.journal.snapshot.boundary_lsn,
                ));
                assert(self.i().disk_view.entries.contains_key(addr));
                assert(to_journal_records(reads)[addr] == self.journal_disk_view().entries[addr]);
                assert(self.journal_disk_view().entries[addr] == self.i().disk_view.entries[addr]);
                assert(self.i().au_page_bounds.contains_key(addr.au));
                assert(addr.page <= self.i().au_page_bounds[addr.au]);
                let record = self.i().disk_view.entries[addr];
                let actual_start_lsn = record.message_seq.maybe_discard_old(
                    self.i().disk_view.boundary_lsn,
                ).seq_start;
                assert(start_lsn == actual_start_lsn);
                assert(start_lsn < record.message_seq.seq_end);
                assert(self.i().lsn_au_index.contains_key(start_lsn));
                assert(self.i().lsn_au_index[start_lsn] == addr.au);
                assert(messages == record.message_seq.maybe_discard_old(
                    self.i().disk_view.boundary_lsn,
                ));
                assert(post == self);
                assert(AllocationJournal::State::next_by(
                    self.i(),
                    post.i(),
                    lbl.i(self),
                    AllocationJournal::Step::read_for_recovery(start_lsn, addr),
                )) by {
                    reveal(AllocationJournal::State::next_by);
                }
            },
            _ => {
                assert(false);
            },
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn freeze_for_commit_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
        reads: Map<Address, RawPage>,
    )
        requires
            self.inv(),
            post.inv(),
            self.semantic_inv(),
            CachingDiskJournal::State::freeze_for_commit(self, post, lbl, reads),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::freeze_for_commit);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        self.disk_reads_ensures(reads);

        let frozen = lbl.arrow_FreezeForCommit_frozen();
        let seq_end = lbl.arrow_FreezeForCommit_seq_end();
        let meta = JournalMetadata{
            boundary_lsn: frozen.boundary_lsn,
            seq_end,
            freshest_rec: frozen.freshest_rec(),
            first: frozen.first(),
        };
        assert(seq_end == self.frozen_seq_end(frozen));
        let journal_lbl = CachedJournal::Label::FreezeForCommit{
            frozen,
            reads: to_journal_records(reads),
        };
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(self.journal, self.journal, journal_lbl, step);
        match cj_step {
            CachedJournal::Step::freeze_for_commit() => {
                reveal(CachedJournal::State::freeze_for_commit);
            },
            _ => {
                assert(false);
            },
        }
        assert(post == self);
        if frozen.freshest_rec() is Some {
            let root = frozen.freshest_rec().unwrap();
            let frozen_seq_end = to_journal_records(reads)[root].message_seq.seq_end;
            assert(reads.contains_key(root));
            assert(to_journal_records(reads).contains_key(root));
            assert(self.disk.visible().contains_key(root));
            assert(self.journal_disk_view().entries.contains_key(root));
            assert(to_journal_records(reads)[root] == self.journal_disk_view().entries[root]);
            assert(self.i().tj().disk_view.entries.contains_key(root));
            assert(frozen_seq_end == self.frozen_seq_end(frozen));
            assert(frozen.boundary_lsn < to_journal_records(reads)[root].message_seq.seq_end);
        }

        assert(CachingDiskJournal::State::freeze_for_commit(self, self, lbl, reads));
        assert(lbl == CachingDiskJournal::Label::FreezeForCommit{frozen, seq_end});
        assert(CachingDiskJournal::State::next_by(
            self,
            self,
            lbl,
            CachingDiskJournal::Step::freeze_for_commit(reads),
        )) by {
            reveal(CachingDiskJournal::State::next_by);
        };
        reveal(CachingDiskJournal::State::next);
        assert(CachingDiskJournal::State::next(self, self, lbl));
        self.freeze_for_commit_label_implies_i_metadata_valid(frozen, seq_end);
        assert(meta == self.frozen_metadata(frozen));
        assert(self.i().frozen_metadata_valid(meta));
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::freeze_for_commit(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn internal_noop_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
    )
        requires
            self.inv(),
            post.inv(),
            self.semantic_inv(),
            CachingDiskJournal::State::internal_noop(self, post, lbl),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::internal_noop);
        assert(post == self);
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::internal_no_op(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn caching_disk_internal_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
        new_disk: CachingDisk::State,
    )
        requires
            self.inv(),
            post.inv(),
            self.semantic_inv(),
            CachingDiskJournal::State::caching_disk_internal(
                self,
                post,
                lbl,
                new_disk,
            ),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::caching_disk_internal);
        CachingDisk::State::internal_visible_unchanged(self.disk, post.disk);
        assert(post.journal == self.journal);
        assert(post.mini_allocator == self.mini_allocator);
        assert(post.disk.visible() == self.disk.visible());
        assert(post.journal_disk_view().entries == self.journal_disk_view().entries);
        assert(post.journal_disk_view() == self.journal_disk_view());
        assert(post.journal_tj() == self.journal_tj());
        assert(post.i() == self.i());
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::internal_no_op(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn load_index_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
        new_journal: CachedJournal::State,
        reads: Map<Address, RawPage>,
    )
        requires
            self.inv(),
            post.inv(),
            self.semantic_inv(),
            CachingDiskJournal::State::load_index(
                self,
                post,
                lbl,
                new_journal,
                reads,
            ),
        ensures
            post.i() == self.i(),
            post.disk == self.disk,
            post.journal.status is Some,
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::load_index);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        assert(lbl is LoadIndex);
        let discovered_aus = lbl.arrow_LoadIndex_discovered_aus();
        self.disk_reads_ensures(reads);
        let journal_lbl = CachedJournal::Label::LoadIndex{
            reads: to_journal_records(reads),
            discovered_aus,
        };
        let entries = self.journal_disk_view().entries;
        let loose_dv = self.journal_disk_view();
        let snapshot = self.journal.snapshot;
        let image = self.backing_journal_image();
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(self.journal, new_journal, journal_lbl, step);
        match cj_step {
            CachedJournal::Step::load_index(au_depth, page_depth) => {
                reveal(CachedJournal::State::load_index);
            },
            _ => {
                assert(false);
            },
        }
        assert(self.journal.status is None);
        assert(post.journal == new_journal);
        assert(post.disk == self.disk);
        assert(post.mini_allocator == self.mini_allocator);
        assert(post.journal.status is Some);
        assert(post.journal.snapshot == self.journal.snapshot);
        assert(post.i().freshest_rec == self.i().freshest_rec);
        assert(post.i().disk_view == self.i().disk_view);
        assert(image.valid_image());
        image.valid_image_implies_tight_valid_image();
        assert(image.tj.disk_view == loose_dv);
        assert(image.tj.freshest_rec == snapshot.freshest_rec());
        assert(loose_dv.path_decodable(snapshot.freshest_rec()));
        assert(loose_dv.path_build_tight(snapshot.freshest_rec()).pointer_is_upstream(
            snapshot.freshest_rec(),
            snapshot.first(),
        ));
        assert forall |addr: Address| #[trigger] to_journal_records(reads).contains_key(addr)
            && entries.contains_key(addr)
            implies to_journal_records(reads)[addr] == entries[addr] by {
            assert(reads.contains_key(addr));
            assert(entries == self.journal_disk_view().entries);
            assert(to_journal_records(reads)[addr] == self.journal_disk_view().entries[addr]);
        };
        load_index_au_page_bounds_matches_loose_full(
            self.journal,
            post.journal,
            to_journal_records(reads),
            discovered_aus,
            entries,
        );
        assert_maps_equal!(
            post.au_page_bounds,
            loose_dv.loose_build_au_page_bounds_au_walk(
                snapshot.freshest_rec(),
                snapshot.first(),
            )
        );
        assert(post.i().au_page_bounds == self.i().au_page_bounds);
        assert(post.journal_tj() == self.journal_tj());
        CachedJournal::State::load_index_matches_loose_full(
            self.journal,
            post.journal,
            to_journal_records(reads),
            discovered_aus,
            entries,
        );
        assert_maps_equal!(
            cj_lsn_au_index(post.journal),
            loose_dv.loose_build_lsn_au_index_au_walk(snapshot.freshest_rec(), snapshot.first())
        );
        assert(post.journal_tj().seq_end() == cj_unmarshalled_tail(post.journal).seq_start);

        assert(post.i().tj() == self.i().tj());
        assert(post.i().unmarshalled_tail == self.i().unmarshalled_tail) by {
            assert(post.journal_tj().seq_end() == cj_unmarshalled_tail(post.journal).seq_start);
            assert(self.journal_tj().disk_view
                == loose_dv.path_build_tight(snapshot.freshest_rec()));
            assert(post.journal_tj().seq_end() == self.journal_tj().seq_end());
            assert(cj_unmarshalled_tail(post.journal)
                == MsgHistory::empty_history_at(post.journal_tj().seq_end()));
        }
        assert(post.i().mini_allocator == self.i().mini_allocator);
        assert_maps_equal!(
            post.i().lsn_au_index,
            loose_dv.loose_build_lsn_au_index_au_walk(snapshot.freshest_rec(), snapshot.first())
        );
        assert_maps_equal!(
            self.i().lsn_au_index,
            loose_dv.loose_build_lsn_au_index_au_walk(snapshot.freshest_rec(), snapshot.first())
        );
        assert_maps_equal!(post.i().lsn_au_index, self.i().lsn_au_index);
        assert(post.i() == self.i());
        assert(lbl.i(self).arrow_InternalAllocations_allocs() == Set::<AU>::empty());
        assert(lbl.i(self).arrow_InternalAllocations_deallocs() == Set::<AU>::empty());
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::internal_no_op(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn observe_clean_aus_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
        new_journal: CachedJournal::State,
    )
        requires
            self.inv(),
            post.inv(),
            self.semantic_inv(),
            CachingDiskJournal::State::observe_clean_aus(
                self,
                post,
                lbl,
                new_journal,
            ),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::observe_clean_aus);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let aus = lbl.arrow_ObserveCleanAUs_aus();
        let journal_lbl = CachedJournal::Label::ObserveCleanAUs{aus};
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(self.journal, post.journal, journal_lbl, step);
        match cj_step {
            CachedJournal::Step::advance_watermark(target_lsn) => {
                reveal(CachedJournal::State::advance_watermark);
            },
            _ => {
                assert(false);
            },
        }
        assert(post.disk == self.disk);
        assert(post.disk.visible() == self.disk.visible());
        assert(post.journal.snapshot == self.journal.snapshot);
        assert(post.journal.status is Some);
        assert(self.journal.status is Some);
        assert(post.journal.status.unwrap().lsn_au_index
            == self.journal.status.unwrap().lsn_au_index);
        assert(post.journal.status.unwrap().unmarshalled_tail
            == self.journal.status.unwrap().unmarshalled_tail);
        assert(post.mini_allocator == self.mini_allocator);
        assert(post.journal_disk_view().entries == self.journal_disk_view().entries);
        assert(post.journal_disk_view() == self.journal_disk_view());
        assert(post.journal_tj() == self.journal_tj());
        assert(post.i() == self.i());
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::internal_no_op(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn journal_marshal_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
        new_journal: CachedJournal::State,
        new_disk: CachingDisk::State,
        addr: Address,
        writes: Map<Address, RawPage>,
    )
        requires
            self.inv(),
            post.inv(),
            self.semantic_inv(),
            CachingDiskJournal::State::journal_marshal(
                self,
                post,
                lbl,
                new_journal,
                new_disk,
                addr,
                writes,
            ),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::journal_marshal);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        CachingDisk::State::access_visible_effect(self.disk, post.disk, Map::empty(), writes);

        let journal_lbl = CachedJournal::Label::JournalMarshal{writes: to_journal_records(writes)};
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(self.journal, new_journal, journal_lbl, step);
        let (cut, hidden_addr) = match cj_step {
            CachedJournal::Step::internal_journal_marshal(cut, hidden_addr) => {
                reveal(CachedJournal::State::internal_journal_marshal);
                (cut, hidden_addr)
            },
            _ => {
                assert(false);
                arbitrary()
            },
        };
        let marshalled_msgs = self.journal.status.unwrap().unmarshalled_tail.discard_recent(cut);
        let expected_record = JournalRecord{
            message_seq: marshalled_msgs,
            prior_rec: self.journal.snapshot.freshest_rec(),
        };
        assert(to_journal_records(writes) == Map::empty().insert(hidden_addr, expected_record));
        assert(to_journal_records(writes).contains_key(hidden_addr));
        assert(to_journal_records(writes).contains_key(hidden_addr) == writes.contains_key(hidden_addr));
        assert(writes.contains_key(hidden_addr));
        assert(writes.dom().contains(hidden_addr));
        assert(writes.dom() =~= Set::new(|a: Address| a == addr));
        assert(Set::new(|a: Address| a == addr).contains(hidden_addr));
        assert(hidden_addr == addr);
        assert(to_journal_records(writes) == Map::empty().insert(addr, expected_record));
        assert(post.journal == new_journal);
        assert(post.journal.snapshot == JournalSnapshot{
            root: Some(JournalRoot{
                freshest_rec: addr,
                first: if self.journal.snapshot.root is None { addr.au } else { self.journal.snapshot.first() },
            }),
            ..self.journal.snapshot
        });
        assert(post.journal.status is Some);
        assert(self.journal.status is Some);
        assert(post.journal.status.unwrap().unmarshalled_tail
            == self.journal.status.unwrap().unmarshalled_tail.discard_old(cut));
        assert(post.journal.status.unwrap().lsn_au_index
            == lsn_au_index_append_record(
                self.journal.status.unwrap().lsn_au_index,
                marshalled_msgs,
                addr.au,
            ));
        assert(post.mini_allocator == self.mini_allocator.allocate(addr).observe(addr));
        assert(post.disk.visible() == self.disk.visible().union_prefer_right(writes));
        assert_maps_equal!(
            post.journal_disk_view().entries,
            self.journal_disk_view().entries.union_prefer_right(to_journal_records(writes)),
            a => {
                if writes.contains_key(a) {
                } else {
                }
            }
        );
        assert_maps_equal!(
            post.i().disk_view.entries,
            self.i().disk_view.entries.insert(addr, expected_record),
            a => {
                if a == addr {
                    assert(to_journal_records(writes).contains_key(addr));
                    assert(to_journal_records(writes)[addr] == expected_record);
                    assert(post.journal_disk_view().entries.contains_key(addr));
                    assert(post.journal_disk_view().entries[addr] == expected_record);
                } else {
                    assert(!writes.contains_key(a)) by {
                        if writes.contains_key(a) {
                            assert(writes.dom().contains(a));
                            assert(writes.dom() =~= Set::new(|x: Address| x == addr));
                            assert(a == addr);
                            assert(false);
                        }
                    }
                }
            }
        );
        assert(post.i().disk_view == DiskView{
            entries: self.i().disk_view.entries.insert(addr, expected_record),
            ..self.i().disk_view
        });
        assert(post.i().freshest_rec == Some(addr));
        assert(post.i().unmarshalled_tail == self.i().unmarshalled_tail.discard_old(cut));
        assert_maps_equal!(
            post.i().lsn_au_index,
            lsn_au_index_append_record(self.i().lsn_au_index, marshalled_msgs, addr.au),
            lsn => {
            }
        );
        assert(post.i().au_page_bounds == self.i().au_page_bounds.insert(addr.au, addr.page));
        assert(post.i().mini_allocator == self.i().mini_allocator.allocate(addr).observe(addr));
        assert(self.i().mini_allocator.tight_next_addr(self.i().freshest_rec, addr));
        assert(lbl.i(self).arrow_InternalAllocations_allocs() == Set::<AU>::empty());
        assert(lbl.i(self).arrow_InternalAllocations_deallocs() == Set::<AU>::empty());
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::internal_journal_marshal(cut, addr),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn commit_prepared_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
    )
        requires
            self.inv(),
            post.inv(),
            self.semantic_inv(),
            CachingDiskJournal::State::commit_prepared(self, post, lbl),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::commit_prepared);
        assert(post == self);
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::internal_no_op(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn discard_old_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
        new_journal: CachedJournal::State,
        new_disk: CachingDisk::State,
    )
        requires
            self.inv(),
            post.inv(),
            self.semantic_inv(),
            CachingDiskJournal::State::discard_old(
                self,
                post,
                lbl,
                new_journal,
                new_disk,
            ),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::discard_old);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let start_lsn = lbl.arrow_DiscardOld_start_lsn();
        let require_end = lbl.arrow_DiscardOld_require_end();
        let label_deallocs = lbl.arrow_DiscardOld_deallocs();
        let old_au_index = cj_lsn_au_index(self.journal);
        let expected_new_au_index = lsn_au_index_discard_up_to(old_au_index, start_lsn);
        CachingDisk::State::forget_effect(self.disk, post.disk, label_deallocs);

        let journal_lbl = CachedJournal::Label::DiscardOld{
            start_lsn,
            require_end,
            deallocs: label_deallocs,
        };
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(self.journal, post.journal, journal_lbl, step);
        match cj_step {
            CachedJournal::Step::discard_old() => {
                reveal(CachedJournal::State::discard_old);
            },
            _ => {
                assert(false);
            },
        }
        assert(label_deallocs == old_au_index.values().difference(expected_new_au_index.values()));
        let new_au_index = cj_lsn_au_index(post.journal);
        let discard_addrs = addresses_in_aus(label_deallocs);
        self.loaded_i_view_facts();
        assert(post.journal == new_journal);
        assert(post.mini_allocator == self.mini_allocator.prune(label_deallocs));
        assert(self.i().lsn_au_index == old_au_index);
        assert_maps_equal!(new_au_index, expected_new_au_index);
        assert_maps_equal!(post.i().lsn_au_index, expected_new_au_index);
        assert(lbl.i(self).arrow_DiscardOld_deallocs() == label_deallocs);
        assert(label_deallocs
            == self.i().lsn_au_index.values().difference(expected_new_au_index.values()));
        assert(post.i().mini_allocator
            == self.i().mini_allocator.prune(lbl.i(self).arrow_DiscardOld_deallocs()));
        assert(post.i().unmarshalled_tail
            == self.i().unmarshalled_tail.bounded_discard(start_lsn));
        assert(post.i().au_page_bounds
            == AllocationJournal::State::au_page_bounds_restrict(
                self.i().au_page_bounds,
                expected_new_au_index.values(),
            ));

        let post_disk_view = DiskView{
            boundary_lsn: start_lsn,
            entries: AllocationJournal::State::disk_view_without_aus(
                self.i().disk_view,
                label_deallocs,
            ).entries,
        };
        assert_maps_equal!(
            post.i().disk_view.entries,
            post_disk_view.entries,
            addr => {
                if post.i().disk_view.entries.contains_key(addr) {
                    assert(post.disk.visible().contains_key(addr));
                    assert(!discard_addrs.contains(addr));
                    assert(self.disk.visible().contains_key(addr));
                    assert(self.i().disk_view.entries.contains_key(addr));
                    assert(!label_deallocs.contains(addr.au));
                    assert(post.disk.visible()[addr] == self.disk.visible()[addr]);
                }
                if post_disk_view.entries.contains_key(addr) {
                    assert(self.i().disk_view.entries.contains_key(addr));
                    assert(!label_deallocs.contains(addr.au));
                    assert(!discard_addrs.contains(addr));
                    assert(self.disk.visible().contains_key(addr));
                    assert(post.disk.visible().contains_key(addr));
                }
            }
        );
        assert(post.i().disk_view == post_disk_view);

        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::discard_old(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn discard_old_next_preserves_i_frozen_metadata_at_boundary(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
        frozen: JournalMetadata,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            lbl is DiscardOld,
            CachingDiskJournal::State::next(self, post, lbl),
            self.i().frozen_metadata_valid(frozen),
            lbl.arrow_DiscardOld_start_lsn() == frozen.boundary_lsn,
        ensures
            post.refinement_inv(),
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
            post.i().frozen_metadata_valid(frozen),
            post.i().frozen_image(frozen) == self.i().frozen_image(frozen),
            post.i().frozen_prefix_domain(frozen) =~= self.i().frozen_prefix_domain(frozen),
            post.journal.status is Some,
            ({
                let start_lsn = lbl.arrow_DiscardOld_start_lsn();
                let old_au_index = cj_lsn_au_index(self.journal);
                let new_au_index = lsn_au_index_discard_up_to(old_au_index, start_lsn);
                post.i().lsn_au_index == new_au_index
            }),
            ({
                let start_lsn = lbl.arrow_DiscardOld_start_lsn();
                let old_au_index = cj_lsn_au_index(self.journal);
                let new_au_index = lsn_au_index_discard_up_to(old_au_index, start_lsn);
                lbl.arrow_DiscardOld_deallocs()
                    == old_au_index.values().difference(new_au_index.values())
            }),
            CachingDisk::State::next(
                self.disk,
                post.disk,
                CachingDisk::Label::Forget{aus: lbl.arrow_DiscardOld_deallocs()},
            ),
    {
        let start_lsn = lbl.arrow_DiscardOld_start_lsn();
        let require_end = lbl.arrow_DiscardOld_require_end();
        let label_deallocs = lbl.arrow_DiscardOld_deallocs();
        let old_au_index = cj_lsn_au_index(self.journal);
        let new_au_index = lsn_au_index_discard_up_to(old_au_index, start_lsn);
        let journal_lbl = CachedJournal::Label::DiscardOld{
            start_lsn,
            require_end,
            deallocs: label_deallocs,
        };

        self.next_refines(post, lbl);
        assert(AllocationJournal::State::discard_old(self.i(), post.i(), lbl.i(self))) by {
            reveal(AllocationJournal::State::next);
            reveal(AllocationJournal::State::next_by);
        }
        AllocationJournal::State::discard_old_preserves_frozen_metadata_at_boundary(
            self.i(),
            post.i(),
            lbl.i(self),
            frozen,
        );
        assert(CachingDiskJournal::State::discard_old(self, post, lbl, post.journal, post.disk)) by {
            reveal(CachingDiskJournal::State::next);
            reveal(CachingDiskJournal::State::next_by);
            let step = choose |step: CachingDiskJournal::Step|
                CachingDiskJournal::State::next_by(self, post, lbl, step);
            match step {
                CachingDiskJournal::Step::discard_old(new_journal, new_disk) => {
                    reveal(CachingDiskJournal::State::discard_old);
                    assert(post.journal == new_journal);
                    assert(post.disk == new_disk);
                },
                _ => {
                    assert(false);
                },
            }
        }
        assert(CachedJournal::State::next(self.journal, post.journal, journal_lbl)) by {
            reveal(CachingDiskJournal::State::discard_old);
        }
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        let cj_step = choose |step: CachedJournal::Step|
            CachedJournal::State::next_by(self.journal, post.journal, journal_lbl, step);
        match cj_step {
            CachedJournal::Step::discard_old() => {
                reveal(CachedJournal::State::discard_old);
            },
            _ => {
                assert(false);
            },
        }
        assert(label_deallocs == old_au_index.values().difference(new_au_index.values()));
        assert(post.journal.status is Some);
        post.loaded_i_view_facts();
        assert_maps_equal!(post.i().lsn_au_index, new_au_index);
        assert(CachingDisk::State::next(
            self.disk,
            post.disk,
            CachingDisk::Label::Forget{aus: label_deallocs},
        )) by {
            reveal(CachingDiskJournal::State::discard_old);
        }
    }

    pub proof fn discard_old_preserves_frozen_snapshot_and_prefix_at_boundary(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            lbl is DiscardOld,
            CachingDiskJournal::State::next(self, post, lbl),
            self.frozen_snapshot_valid(frozen, seq_end),
            self.persistent_visible_agree_on(self.frozen_prefix_domain(frozen)),
            lbl.arrow_DiscardOld_start_lsn() == frozen.boundary_lsn,
        ensures
            post.refinement_inv(),
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
            post.i().frozen_metadata_valid(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
            post.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }).tight_tj() == self.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }).tight_tj(),
            post.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }) == self.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
            post.frozen_snapshot_valid(frozen, seq_end),
            post.frozen_prefix_domain(frozen) =~= self.frozen_prefix_domain(frozen),
            post.persistent_visible_agree_on(post.frozen_prefix_domain(frozen)),
    {
        let meta = JournalMetadata{
            boundary_lsn: frozen.boundary_lsn,
            seq_end,
            freshest_rec: frozen.freshest_rec(),
            first: frozen.first(),
        };
        let start_lsn = lbl.arrow_DiscardOld_start_lsn();
        let label_deallocs = lbl.arrow_DiscardOld_deallocs();
        let old_au_index = cj_lsn_au_index(self.journal);
        let new_au_index = lsn_au_index_discard_up_to(old_au_index, start_lsn);

        self.frozen_snapshot_valid_implies_i_metadata_valid(frozen, seq_end);
        self.discard_old_next_preserves_i_frozen_metadata_at_boundary(post, lbl, meta);
        assert(label_deallocs == old_au_index.values().difference(new_au_index.values()));
        self.loaded_i_view_facts();
        self.i_metadata_valid_implies_frozen_tj_matches_i(frozen, seq_end);
        post.i_metadata_valid_implies_frozen_tj_matches_i(frozen, seq_end);
        assert(post.frozen_snapshot_valid(frozen, seq_end));
        assert(post.frozen_prefix_domain(frozen) =~= self.frozen_prefix_domain(frozen)) by {
            assert(post.frozen_prefix_domain(frozen) =~= post.i().frozen_prefix_domain(meta));
            assert(self.frozen_prefix_domain(frozen) =~= self.i().frozen_prefix_domain(meta));
            assert(post.i().frozen_image(meta) == self.i().frozen_image(meta));
            assert(post.i().frozen_prefix_domain(meta) =~= self.i().frozen_prefix_domain(meta));
        }
        lsn_au_index_discard_up_to_ensures(old_au_index, start_lsn);
        assert(self.i().lsn_au_index == old_au_index);
        assert_maps_equal!(post.i().lsn_au_index, new_au_index);
        assert(addresses_in_aus(label_deallocs).disjoint(self.frozen_prefix_domain(frozen))) by {
            assert forall |addr: Address| #[trigger] addresses_in_aus(label_deallocs).contains(addr)
                implies !self.frozen_prefix_domain(frozen).contains(addr) by {
                if self.frozen_prefix_domain(frozen).contains(addr) {
                    assert(label_deallocs.contains(addr.au));
                    assert(self.i().frozen_prefix_domain(meta).contains(addr));
                    assert(self.i().frozen_loose_domain(meta).contains(addr));
                    assert(addrs_in_aus(self.i().frozen_lsn_au_index(meta).values()).contains(addr));
                    let lsn = choose |lsn: LSN| #![trigger self.i().frozen_lsn_au_index(meta).contains_key(lsn)] {
                        &&& self.i().frozen_lsn_au_index(meta).contains_key(lsn)
                        &&& self.i().frozen_lsn_au_index(meta)[lsn] == addr.au
                    };
                    assert(meta.boundary_lsn <= lsn);
                    assert(start_lsn == meta.boundary_lsn);
                    assert(self.i().lsn_au_index.contains_key(lsn));
                    assert(old_au_index.contains_key(lsn));
                    assert(new_au_index.contains_key(lsn));
                    assert(new_au_index[lsn] == old_au_index[lsn]);
                    assert(old_au_index[lsn] == addr.au);
                    assert(new_au_index.values().contains(addr.au));
                    assert(!label_deallocs.contains(addr.au));
                    assert(false);
                }
            }
        }
        CachingDisk::State::forget_preserves_persistent_visible_agree_on(
            self.disk,
            post.disk,
            label_deallocs,
            self.frozen_prefix_domain(frozen),
        );
        post.disk.persistent_visible_agree_on_equal_addrs(
            self.frozen_prefix_domain(frozen),
            post.frozen_prefix_domain(frozen),
        );
        assert(post.persistent_visible_agree_on(post.frozen_prefix_domain(frozen)));
    }

    pub proof fn discard_old_preserves_frozen_materialization_certificate_at_boundary(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            lbl is DiscardOld,
            CachingDiskJournal::State::next(self, post, lbl),
            self.frozen_materialization_certificate(frozen, seq_end),
            lbl.arrow_DiscardOld_start_lsn() == frozen.boundary_lsn,
        ensures
            post.refinement_inv(),
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
            post.frozen_materialization_certificate(frozen, seq_end),
            post.i().frozen_metadata_valid(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
            post.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }) == self.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
    {
        self.discard_old_preserves_frozen_snapshot_and_prefix_at_boundary(
            post,
            lbl,
            frozen,
            seq_end,
        );
        post.frozen_snapshot_valid_implies_i_metadata_valid(frozen, seq_end);
        assert(post.frozen_persistence_certificate(frozen));
    }

    pub proof fn put_requires_loaded(
        self,
        post: Self,
        records: MsgHistory,
    )
        requires
            CachingDiskJournal::State::next(
                self,
                post,
                CachingDiskJournal::Label::Put{messages: records},
            ),
        ensures
            self.journal.status is Some,
            post.journal.status is Some,
    {
        let lbl = CachingDiskJournal::Label::Put{messages: records};
        let journal_lbl = CachedJournal::Label::Put{messages: records};

        assert(CachingDiskJournal::State::put(self, post, lbl, post.journal)) by {
            reveal(CachingDiskJournal::State::next);
            reveal(CachingDiskJournal::State::next_by);
            let step = choose |step: CachingDiskJournal::Step|
                CachingDiskJournal::State::next_by(self, post, lbl, step);
            match step {
                CachingDiskJournal::Step::put(new_journal) => {
                    reveal(CachingDiskJournal::State::put);
                    assert(post.journal == new_journal);
                },
                _ => {
                    assert(false);
                },
            }
        }
        assert(CachedJournal::State::next(self.journal, post.journal, journal_lbl)) by {
            reveal(CachingDiskJournal::State::put);
        }
        CachedJournal::State::put_effect(self.journal, post.journal, records);
    }

    pub proof fn observe_clean_aus_requires_loaded(
        self,
        post: Self,
        aus: Set<AU>,
    )
        requires
            CachingDiskJournal::State::next(
                self,
                post,
                CachingDiskJournal::Label::ObserveCleanAUs{aus},
            ),
        ensures
            self.journal.status is Some,
            post.journal.status is Some,
    {
        let lbl = CachingDiskJournal::Label::ObserveCleanAUs{aus};
        let journal_lbl = CachedJournal::Label::ObserveCleanAUs{aus};

        assert(CachingDiskJournal::State::observe_clean_aus(self, post, lbl, post.journal)) by {
            reveal(CachingDiskJournal::State::next);
            reveal(CachingDiskJournal::State::next_by);
            let step = choose |step: CachingDiskJournal::Step|
                CachingDiskJournal::State::next_by(self, post, lbl, step);
            match step {
                CachingDiskJournal::Step::observe_clean_aus(new_journal) => {
                    reveal(CachingDiskJournal::State::observe_clean_aus);
                    assert(post.journal == new_journal);
                },
                _ => {
                    assert(false);
                },
            }
        }
        assert(CachedJournal::State::next(self.journal, post.journal, journal_lbl)) by {
            reveal(CachingDiskJournal::State::observe_clean_aus);
        }
        CachedJournal::State::observe_clean_aus_effect(self.journal, post.journal, aus);
    }

    pub proof fn put_preserves_frozen_snapshot_and_prefix(
        self,
        post: Self,
        records: MsgHistory,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.refinement_inv(),
            post.refinement_inv(),
            self.frozen_snapshot_valid(frozen, seq_end),
            CachingDiskJournal::State::next(
                self,
                post,
                CachingDiskJournal::Label::Put{messages: records},
            ),
        ensures
            self.frozen_snapshot_preserved_by(post, frozen, seq_end),
            post.frozen_snapshot_valid(frozen, seq_end),
            post.frozen_tj(frozen) == self.frozen_tj(frozen),
            post.frozen_prefix_domain(frozen) =~= self.frozen_prefix_domain(frozen),
            self.persistent_visible_agree_on(self.frozen_prefix_domain(frozen)) ==>
                post.persistent_visible_agree_on(post.frozen_prefix_domain(frozen)),
            post.disk == self.disk,
    {
        let lbl = CachingDiskJournal::Label::Put{messages: records};
        let journal_lbl = CachedJournal::Label::Put{messages: records};

        assert(CachingDiskJournal::State::put(self, post, lbl, post.journal)) by {
            reveal(CachingDiskJournal::State::next);
            reveal(CachingDiskJournal::State::next_by);
            let step = choose |step: CachingDiskJournal::Step|
                CachingDiskJournal::State::next_by(self, post, lbl, step);
            match step {
                CachingDiskJournal::Step::put(new_journal) => {
                    reveal(CachingDiskJournal::State::put);
                    assert(post.journal == new_journal);
                },
                _ => {
                    assert(false);
                },
            }
        }
        assert(CachedJournal::State::next(self.journal, post.journal, journal_lbl)) by {
            reveal(CachingDiskJournal::State::put);
        }
        CachedJournal::State::put_effect(self.journal, post.journal, records);
        assert(records.wf()) by {
            reveal(CachedJournal::State::next);
            reveal(CachedJournal::State::next_by);
            let step = choose |step: CachedJournal::Step|
                CachedJournal::State::next_by(self.journal, post.journal, journal_lbl, step);
            match step {
                CachedJournal::Step::put() => {
                    reveal(CachedJournal::State::put);
                },
                _ => {
                    assert(false);
                },
            }
        }
        assert(records.seq_start == self.journal.seq_end()) by {
            reveal(CachedJournal::State::next);
            reveal(CachedJournal::State::next_by);
            let step = choose |step: CachedJournal::Step|
                CachedJournal::State::next_by(self.journal, post.journal, journal_lbl, step);
            match step {
                CachedJournal::Step::put() => {
                    reveal(CachedJournal::State::put);
                },
                _ => {
                    assert(false);
                },
            }
        }
        assert(self.journal.seq_end() <= post.journal.seq_end()) by {
            assert(records.seq_start <= records.seq_end);
            assert(post.journal.status.unwrap().unmarshalled_tail
                == self.journal.status.unwrap().unmarshalled_tail.concat(records));
            assert(post.journal.seq_end() == records.seq_end);
        }
        CachingDiskJournal::State::put_loaded_status_and_clean_watermark_unchanged(
            self,
            post,
            records,
        );

        assert(post.au_page_bounds == self.au_page_bounds) by {
            reveal(CachingDiskJournal::State::put);
        }
        assert(post.lsn_au_index_or_empty() == self.lsn_au_index_or_empty());
        assert(post.journal_disk_view() == self.journal_disk_view());
        assert(post.frozen_seq_end(frozen) == self.frozen_seq_end(frozen)) by {
            if frozen.freshest_rec() is Some {
                let root = frozen.freshest_rec().unwrap();
                assert(post.journal_disk_view().entries[root]
                    == self.journal_disk_view().entries[root]);
            }
        }
        assert(post.frozen_lsns(frozen) =~= self.frozen_lsns(frozen)) by {
            assert forall |lsn: LSN| #[trigger] post.frozen_lsns(frozen).contains(lsn)
                <==> self.frozen_lsns(frozen).contains(lsn) by {}
        }
        assert(post.frozen_loose_domain(frozen) =~= self.frozen_loose_domain(frozen)) by {
            assert forall |addr: Address|
                #[trigger] post.frozen_loose_domain(frozen).contains(addr)
                <==> self.frozen_loose_domain(frozen).contains(addr) by {}
        }
        assert(post.frozen_tj(frozen).disk_view.entries
            == self.frozen_tj(frozen).disk_view.entries) by {
            assert_maps_equal!(
                post.frozen_tj(frozen).disk_view.entries,
                self.frozen_tj(frozen).disk_view.entries,
                addr => {}
            );
        }
        assert(post.frozen_tj(frozen) == self.frozen_tj(frozen));
        assert(post.frozen_prefix_domain(frozen) =~= self.frozen_prefix_domain(frozen)) by {
            assert forall |addr: Address|
                #[trigger] post.frozen_prefix_domain(frozen).contains(addr)
                <==> self.frozen_prefix_domain(frozen).contains(addr) by {}
        }
        assert(self.frozen_snapshot_preserved_by(post, frozen, seq_end));
    }

    pub proof fn load_index_preserves_frozen_snapshot_and_prefix(
        self,
        post: Self,
        discovered_aus: Set<AU>,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.refinement_inv(),
            self.i().frozen_metadata_valid(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
            self.persistent_visible_agree_on(self.frozen_loose_domain(frozen)),
            CachingDiskJournal::State::next(
                self,
                post,
                CachingDiskJournal::Label::LoadIndex{discovered_aus},
            ),
        ensures
            post.refinement_inv(),
            post.frozen_snapshot_valid(frozen, seq_end),
            post.frozen_tj(frozen) == self.frozen_tj(frozen),
            post.frozen_loose_domain(frozen) =~= self.frozen_loose_domain(frozen),
            post.frozen_prefix_domain(frozen) <= self.frozen_loose_domain(frozen),
            post.persistent_visible_agree_on(post.frozen_prefix_domain(frozen)),
            post.disk == self.disk,
    {
        let lbl = CachingDiskJournal::Label::LoadIndex{discovered_aus};
        let meta = JournalMetadata{
            boundary_lsn: frozen.boundary_lsn,
            seq_end,
            freshest_rec: frozen.freshest_rec(),
            first: frozen.first(),
        };

        self.next_refines(post, lbl);
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(self, post, lbl, step);
        match step {
            CachingDiskJournal::Step::load_index(new_journal, reads) => {
                self.load_index_refines(post, lbl, new_journal, reads);
            },
            _ => {
                assert(false);
            },
        }
        AllocationJournal::State::internal_allocations_preserves_frozen_metadata_tight(
            self.i(),
            post.i(),
            lbl.i(self),
            meta,
        );
        assert(post.refinement_inv());

        self.i_metadata_valid_implies_frozen_tj_matches_i(frozen, seq_end);
        post.i_metadata_valid_implies_frozen_tj_matches_i(frozen, seq_end);
        assert(post.i() == self.i());
        assert(post.i().frozen_loose_domain(meta) =~= self.i().frozen_loose_domain(meta));
        assert(post.frozen_loose_domain(frozen) =~= self.frozen_loose_domain(frozen)) by {
            assert forall |addr: Address|
                #[trigger] post.frozen_loose_domain(frozen).contains(addr)
                <==> self.frozen_loose_domain(frozen).contains(addr) by {
                if post.frozen_loose_domain(frozen).contains(addr) {
                    assert(post.i().frozen_loose_domain(meta).contains(addr));
                    assert(self.i().frozen_loose_domain(meta).contains(addr));
                }
                if self.frozen_loose_domain(frozen).contains(addr) {
                    assert(self.i().frozen_loose_domain(meta).contains(addr));
                    assert(post.i().frozen_loose_domain(meta).contains(addr));
                }
            }
        }
        assert(post.frozen_tj(frozen) == self.frozen_tj(frozen)) by {
            assert(post.frozen_tj(frozen) == post.i().frozen_tj(meta));
            assert(self.frozen_tj(frozen) == self.i().frozen_tj(meta));
            assert(post.i().frozen_tj(meta) == self.i().frozen_tj(meta));
        }

        post.loaded_i_view_facts();
        assert(post.frozen_metadata(frozen) == meta);
        assert(post.frozen_snapshot_valid(frozen, seq_end));

        assert(post.frozen_prefix_domain(frozen) <= self.frozen_loose_domain(frozen)) by {
            assert forall |addr: Address|
                #[trigger] post.frozen_prefix_domain(frozen).contains(addr)
                implies self.frozen_loose_domain(frozen).contains(addr) by {
                assert(post.frozen_loose_domain(frozen).contains(addr));
            }
        }

        assert(post.persistent_visible_agree_on(post.frozen_prefix_domain(frozen))) by {
            assert_maps_equal!(
                post.disk.persistent.restrict(post.frozen_prefix_domain(frozen)),
                post.disk.visible().restrict(post.frozen_prefix_domain(frozen)),
                addr => {
                    if post.frozen_prefix_domain(frozen).contains(addr) {
                        assert(self.frozen_loose_domain(frozen).contains(addr));
                        assert(self.disk.persistent.restrict(self.frozen_loose_domain(frozen))
                            == self.disk.visible().restrict(self.frozen_loose_domain(frozen)));
                        assert(self.disk.persistent.restrict(self.frozen_loose_domain(frozen)).contains_key(addr)
                            == self.disk.persistent.contains_key(addr));
                        assert(self.disk.visible().restrict(self.frozen_loose_domain(frozen)).contains_key(addr)
                            == self.disk.visible().contains_key(addr));
                        if self.disk.persistent.contains_key(addr) {
                            assert(self.disk.persistent.restrict(self.frozen_loose_domain(frozen)).contains_key(addr));
                            assert(self.disk.visible().restrict(self.frozen_loose_domain(frozen)).contains_key(addr));
                            assert(self.disk.persistent.restrict(self.frozen_loose_domain(frozen))[addr]
                                == self.disk.visible().restrict(self.frozen_loose_domain(frozen))[addr]);
                            assert(self.disk.persistent[addr] == self.disk.visible()[addr]);
                        }
                    }
                }
            );
        }
    }

    pub proof fn internal_preserves_frozen_snapshot_and_prefix(
        self,
        post: Self,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.refinement_inv(),
            self.frozen_snapshot_valid(frozen, seq_end),
            self.persistent_visible_agree_on(self.frozen_prefix_domain(frozen)),
            CachingDiskJournal::State::next(
                self,
                post,
                CachingDiskJournal::Label::Internal,
            ),
        ensures
            post.refinement_inv(),
            post.frozen_snapshot_valid(frozen, seq_end),
            post.frozen_prefix_domain(frozen) =~= self.frozen_prefix_domain(frozen),
            post.persistent_visible_agree_on(post.frozen_prefix_domain(frozen)),
    {
        let lbl = CachingDiskJournal::Label::Internal;
        let meta = JournalMetadata{
            boundary_lsn: frozen.boundary_lsn,
            seq_end,
            freshest_rec: frozen.freshest_rec(),
            first: frozen.first(),
        };

        self.next_refines(post, lbl);
        assert(self.journal.status is Some);
        CachingDiskJournal::State::internal_loaded_status_and_clean_watermark_monotonic(self, post);
        self.frozen_snapshot_valid_implies_i_metadata_valid(frozen, seq_end);
        AllocationJournal::State::internal_allocations_preserves_frozen_metadata_tight(
            self.i(),
            post.i(),
            lbl.i(self),
            meta,
        );
        assert(post.refinement_inv());

        self.i_metadata_valid_implies_frozen_tj_matches_i(frozen, seq_end);
        post.i_metadata_valid_implies_frozen_tj_matches_i(frozen, seq_end);
        assert(post.frozen_snapshot_valid(frozen, seq_end));
        assert(post.frozen_prefix_domain(frozen) =~= self.frozen_prefix_domain(frozen)) by {
            assert(post.frozen_prefix_domain(frozen) =~= post.i().frozen_prefix_domain(meta));
            assert(self.frozen_prefix_domain(frozen) =~= self.i().frozen_prefix_domain(meta));
            assert(post.i().frozen_prefix_domain(meta) =~= self.i().frozen_prefix_domain(meta));
        }

        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(self, post, lbl, step);
        match step {
            CachingDiskJournal::Step::caching_disk_internal(new_disk) => {
                reveal(CachingDiskJournal::State::caching_disk_internal);
                CachingDisk::State::internal_preserves_persistent_visible_agree_on(
                    self.disk,
                    post.disk,
                    self.frozen_prefix_domain(frozen),
                );
            },
            CachingDiskJournal::Step::journal_marshal(new_journal, new_disk, addr, writes) => {
                reveal(CachingDiskJournal::State::journal_marshal);
                reveal(CachedJournal::State::next);
                reveal(CachedJournal::State::next_by);
                let journal_lbl = CachedJournal::Label::JournalMarshal{
                    writes: to_journal_records(writes),
                };
                let journal_step = choose |step: CachedJournal::Step|
                    CachedJournal::State::next_by(self.journal, post.journal, journal_lbl, step);
                let cut = match journal_step {
                    CachedJournal::Step::internal_journal_marshal(cut, hidden_addr) => {
                        reveal(CachedJournal::State::internal_journal_marshal);
                        assert(to_journal_records(writes).contains_key(hidden_addr));
                        assert(writes.contains_key(hidden_addr));
                        assert(writes.dom().contains(hidden_addr));
                        assert(writes.dom() =~= Set::new(|a: Address| a == addr));
                        assert(hidden_addr == addr);
                        cut
                    },
                    _ => {
                        assert(false);
                        arbitrary()
                    },
                };
                assert(self.i().mini_allocator.tight_next_addr(self.i().freshest_rec, addr));
                AllocationJournal::State::tight_next_addr_not_in_frozen_prefix(
                    self.i(),
                    addr,
                    meta,
                );
                assert(!self.frozen_prefix_domain(frozen).contains(addr)) by {
                    assert(self.frozen_prefix_domain(frozen) =~= self.i().frozen_prefix_domain(meta));
                }
                assert(writes.dom().disjoint(self.frozen_prefix_domain(frozen))) by {
                    assert forall |a: Address| #[trigger] writes.dom().contains(a)
                        implies !self.frozen_prefix_domain(frozen).contains(a) by {
                        assert(writes.dom() =~= Set::new(|x: Address| x == addr));
                        assert(a == addr);
                    }
                }
                CachingDisk::State::access_preserves_persistent_visible_agree_on(
                    self.disk,
                    post.disk,
                    Map::empty(),
                    writes,
                    self.frozen_prefix_domain(frozen),
                );
            },
            CachingDiskJournal::Step::internal_noop() => {
                reveal(CachingDiskJournal::State::internal_noop);
                assert(post == self);
            },
            _ => {
                assert(false);
            },
        }
        post.disk.persistent_visible_agree_on_equal_addrs(
            self.frozen_prefix_domain(frozen),
            post.frozen_prefix_domain(frozen),
        );
        assert(post.persistent_visible_agree_on(post.frozen_prefix_domain(frozen)));
    }

    pub proof fn internal_preserves_frozen_snapshot(
        self,
        post: Self,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.refinement_inv(),
            self.frozen_snapshot_valid(frozen, seq_end),
            CachingDiskJournal::State::next(
                self,
                post,
                CachingDiskJournal::Label::Internal,
            ),
        ensures
            post.refinement_inv(),
            post.frozen_snapshot_valid(frozen, seq_end),
            post.frozen_prefix_domain(frozen) =~= self.frozen_prefix_domain(frozen),
            post.i().frozen_metadata_valid(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
            post.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }).tight_tj() == self.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }).tight_tj(),
    {
        let lbl = CachingDiskJournal::Label::Internal;
        let meta = JournalMetadata{
            boundary_lsn: frozen.boundary_lsn,
            seq_end,
            freshest_rec: frozen.freshest_rec(),
            first: frozen.first(),
        };

        self.next_refines(post, lbl);
        assert(self.journal.status is Some);
        CachingDiskJournal::State::internal_loaded_status_and_clean_watermark_monotonic(self, post);
        self.frozen_snapshot_valid_implies_i_metadata_valid(frozen, seq_end);
        AllocationJournal::State::internal_allocations_preserves_frozen_metadata_tight(
            self.i(),
            post.i(),
            lbl.i(self),
            meta,
        );
        assert(post.refinement_inv());

        self.i_metadata_valid_implies_frozen_tj_matches_i(frozen, seq_end);
        post.i_metadata_valid_implies_frozen_tj_matches_i(frozen, seq_end);
        assert(post.frozen_snapshot_valid(frozen, seq_end));
        assert(post.frozen_prefix_domain(frozen) =~= self.frozen_prefix_domain(frozen)) by {
            assert(post.frozen_prefix_domain(frozen) =~= post.i().frozen_prefix_domain(meta));
            assert(self.frozen_prefix_domain(frozen) =~= self.i().frozen_prefix_domain(meta));
            assert(post.i().frozen_prefix_domain(meta) =~= self.i().frozen_prefix_domain(meta));
        }
    }

    pub proof fn internal_unloaded_preserves_frozen_loose_agreement(
        self,
        post: Self,
        frozen: JournalSnapshot,
    )
        requires
            self.refinement_inv(),
            self.journal.status is None,
            self.persistent_visible_agree_on(self.frozen_loose_domain(frozen)),
            CachingDiskJournal::State::next(
                self,
                post,
                CachingDiskJournal::Label::Internal,
            ),
        ensures
            post.refinement_inv(),
            post.journal.status is None,
            post.frozen_loose_domain(frozen) =~= self.frozen_loose_domain(frozen),
            post.persistent_visible_agree_on(post.frozen_loose_domain(frozen)),
    {
        let lbl = CachingDiskJournal::Label::Internal;

        self.next_refines(post, lbl);
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(self, post, lbl, step);
        match step {
            CachingDiskJournal::Step::caching_disk_internal(new_disk) => {
                reveal(CachingDiskJournal::State::caching_disk_internal);
                CachingDisk::State::internal_visible_unchanged(self.disk, post.disk);
                CachingDisk::State::internal_preserves_persistent_visible_agree_on(
                    self.disk,
                    post.disk,
                    self.frozen_loose_domain(frozen),
                );
                assert(post.journal == self.journal);
                assert(post.mini_allocator == self.mini_allocator);
                assert(post.au_page_bounds == self.au_page_bounds);
                assert(post.journal.status is None);
                assert(post.journal_disk_view() == self.journal_disk_view());
                assert(post.visible_lsn_au_index() == self.visible_lsn_au_index());
                assert(post.lsn_au_index_or_empty() == self.lsn_au_index_or_empty());
            },
            CachingDiskJournal::Step::journal_marshal(new_journal, new_disk, addr, writes) => {
                reveal(CachingDiskJournal::State::journal_marshal);
                reveal(CachedJournal::State::next);
                reveal(CachedJournal::State::next_by);
                let journal_lbl = CachedJournal::Label::JournalMarshal{
                    writes: to_journal_records(writes),
                };
                let journal_step = choose |step: CachedJournal::Step|
                    CachedJournal::State::next_by(self.journal, post.journal, journal_lbl, step);
                match journal_step {
                    CachedJournal::Step::internal_journal_marshal(cut, hidden_addr) => {
                        reveal(CachedJournal::State::internal_journal_marshal);
                        assert(self.journal.status is Some);
                        assert(false);
                    },
                    _ => {
                        assert(false);
                    },
                }
            },
            CachingDiskJournal::Step::internal_noop() => {
                reveal(CachingDiskJournal::State::internal_noop);
                assert(post == self);
                assert(post.journal.status is None);
                assert(post.lsn_au_index_or_empty() == self.lsn_au_index_or_empty());
                assert(post.disk.persistent_visible_agree_on(self.frozen_loose_domain(frozen)));
            },
            _ => {
                assert(false);
            },
        }
        assert(post.frozen_loose_domain(frozen) =~= self.frozen_loose_domain(frozen)) by {
            assert forall |addr: Address|
                #[trigger] post.frozen_loose_domain(frozen).contains(addr)
                <==> self.frozen_loose_domain(frozen).contains(addr) by {}
        }
        post.disk.persistent_visible_agree_on_equal_addrs(
            self.frozen_loose_domain(frozen),
            post.frozen_loose_domain(frozen),
        );
        assert(post.persistent_visible_agree_on(post.frozen_loose_domain(frozen)));
    }

    pub proof fn frozen_prefix_addr_in_i_lsn_au_index_values(
        self,
        frozen: JournalSnapshot,
        seq_end: LSN,
        addr: Address,
    )
        requires
            self.refinement_inv(),
            self.frozen_snapshot_valid(frozen, seq_end),
            self.frozen_prefix_domain(frozen).contains(addr),
        ensures
            self.i().lsn_au_index.values().contains(addr.au),
    {
        let meta = JournalMetadata{
            boundary_lsn: frozen.boundary_lsn,
            seq_end,
            freshest_rec: frozen.freshest_rec(),
            first: frozen.first(),
        };
        self.frozen_snapshot_valid_implies_i_metadata_valid(frozen, seq_end);
        self.i_metadata_valid_implies_frozen_tj_matches_i(frozen, seq_end);
        assert(self.i().frozen_prefix_domain(meta).contains(addr));
        assert(self.i().frozen_loose_domain(meta).contains(addr));
        assert(addrs_in_aus(self.i().frozen_lsn_au_index(meta).values()).contains(addr));
        let lsn = choose |lsn: LSN| #![trigger self.i().frozen_lsn_au_index(meta).contains_key(lsn)] {
            &&& self.i().frozen_lsn_au_index(meta).contains_key(lsn)
            &&& self.i().frozen_lsn_au_index(meta)[lsn] == addr.au
        };
        assert(self.i().lsn_au_index.contains_key(lsn));
        assert(self.i().lsn_au_index[lsn] == addr.au);
    }

    pub proof fn internal_alloc_preserves_frozen_snapshot_and_prefix(
        self,
        post: Self,
        allocs: Set<AU>,
        deallocs: Set<AU>,
        prune_aus: Set<AU>,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.refinement_inv(),
            self.frozen_snapshot_valid(frozen, seq_end),
            self.persistent_visible_agree_on(self.frozen_prefix_domain(frozen)),
            CachingDiskJournal::State::next(
                self,
                post,
                CachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus},
            ),
        ensures
            post.refinement_inv(),
            post.frozen_snapshot_valid(frozen, seq_end),
            post.frozen_prefix_domain(frozen) =~= self.frozen_prefix_domain(frozen),
            post.persistent_visible_agree_on(post.frozen_prefix_domain(frozen)),
    {
        let lbl = CachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus};
        let meta = JournalMetadata{
            boundary_lsn: frozen.boundary_lsn,
            seq_end,
            freshest_rec: frozen.freshest_rec(),
            first: frozen.first(),
        };

        self.next_refines(post, lbl);
        CachingDiskJournal::State::internal_alloc_preserves_journal(
            self,
            post,
            allocs,
            deallocs,
            prune_aus,
        );
        self.frozen_snapshot_valid_implies_i_metadata_valid(frozen, seq_end);
        AllocationJournal::State::internal_allocations_preserves_frozen_metadata_tight(
            self.i(),
            post.i(),
            lbl.i(self),
            meta,
        );
        assert(post.refinement_inv());

        self.i_metadata_valid_implies_frozen_tj_matches_i(frozen, seq_end);
        post.i_metadata_valid_implies_frozen_tj_matches_i(frozen, seq_end);
        assert(post.frozen_snapshot_valid(frozen, seq_end));
        assert(post.frozen_prefix_domain(frozen) =~= self.frozen_prefix_domain(frozen)) by {
            assert(post.frozen_prefix_domain(frozen) =~= post.i().frozen_prefix_domain(meta));
            assert(self.frozen_prefix_domain(frozen) =~= self.i().frozen_prefix_domain(meta));
            assert(post.i().frozen_prefix_domain(meta) =~= self.i().frozen_prefix_domain(meta));
        }

        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(self, post, lbl, step);
        match step {
            CachingDiskJournal::Step::mini_allocator_fill(new_disk) => {
                reveal(CachingDiskJournal::State::mini_allocator_fill);
                assert((post.disk.cache.dom() - self.disk.cache.dom())
                    .disjoint(self.frozen_prefix_domain(frozen))) by {
                    assert forall |addr: Address|
                        #[trigger] (post.disk.cache.dom() - self.disk.cache.dom()).contains(addr)
                        implies !self.frozen_prefix_domain(frozen).contains(addr) by {
                        assert(addresses_in_aus(allocs).contains(addr));
                        assert(allocs.contains(addr.au));
                        if self.frozen_prefix_domain(frozen).contains(addr) {
                            self.frozen_prefix_addr_in_i_lsn_au_index_values(frozen, seq_end, addr);
                            assert(allocs.disjoint(self.i().lsn_au_index.values()));
                            assert(!allocs.contains(addr.au));
                            assert(false);
                        }
                    }
                }
                assert((post.disk.persistent.dom() - self.disk.persistent.dom())
                    .disjoint(self.frozen_prefix_domain(frozen))) by {
                    assert forall |addr: Address|
                        #[trigger] (post.disk.persistent.dom() - self.disk.persistent.dom()).contains(addr)
                        implies !self.frozen_prefix_domain(frozen).contains(addr) by {
                        assert(addresses_in_aus(allocs).contains(addr));
                        assert(allocs.contains(addr.au));
                        if self.frozen_prefix_domain(frozen).contains(addr) {
                            self.frozen_prefix_addr_in_i_lsn_au_index_values(frozen, seq_end, addr);
                            assert(allocs.disjoint(self.i().lsn_au_index.values()));
                            assert(!allocs.contains(addr.au));
                            assert(false);
                        }
                    }
                }
                CachingDisk::State::extension_preserves_persistent_visible_agree_on(
                    self.disk,
                    post.disk,
                    self.frozen_prefix_domain(frozen),
                );
            },
            CachingDiskJournal::Step::mini_allocator_prune(new_disk) => {
                reveal(CachingDiskJournal::State::mini_allocator_prune);
                assert(addresses_in_aus(deallocs).disjoint(self.frozen_prefix_domain(frozen))) by {
                    assert forall |addr: Address| #[trigger] addresses_in_aus(deallocs).contains(addr)
                        implies !self.frozen_prefix_domain(frozen).contains(addr) by {
                        if self.frozen_prefix_domain(frozen).contains(addr) {
                            self.frozen_prefix_addr_in_i_lsn_au_index_values(frozen, seq_end, addr);
                            assert(deallocs.contains(addr.au));
                            assert(deallocs <= prune_aus);
                            assert(self.mini_allocator.allocs.contains_key(addr.au));
                            assert(self.mini_allocator.allocs[addr.au].all_pages_free());
                            assert(self.i().mini_allocator == self.mini_allocator);
                            assert(!self.mini_allocator.allocs[addr.au].all_pages_free()) by {
                                assert(self.indexed_aus_not_all_pages_free());
                            }
                            assert(false);
                        }
                    }
                }
                CachingDisk::State::forget_preserves_persistent_visible_agree_on(
                    self.disk,
                    post.disk,
                    deallocs,
                    self.frozen_prefix_domain(frozen),
                );
            },
            _ => {
                assert(false);
            },
        }
        post.disk.persistent_visible_agree_on_equal_addrs(
            self.frozen_prefix_domain(frozen),
            post.frozen_prefix_domain(frozen),
        );
        assert(post.persistent_visible_agree_on(post.frozen_prefix_domain(frozen)));
    }

    pub proof fn internal_alloc_preserves_frozen_snapshot(
        self,
        post: Self,
        allocs: Set<AU>,
        deallocs: Set<AU>,
        prune_aus: Set<AU>,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.refinement_inv(),
            self.frozen_snapshot_valid(frozen, seq_end),
            CachingDiskJournal::State::next(
                self,
                post,
                CachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus},
            ),
        ensures
            post.refinement_inv(),
            post.frozen_snapshot_valid(frozen, seq_end),
            post.frozen_prefix_domain(frozen) =~= self.frozen_prefix_domain(frozen),
            post.i().frozen_metadata_valid(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
            post.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }).tight_tj() == self.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }).tight_tj(),
    {
        let lbl = CachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus};
        let meta = JournalMetadata{
            boundary_lsn: frozen.boundary_lsn,
            seq_end,
            freshest_rec: frozen.freshest_rec(),
            first: frozen.first(),
        };

        self.next_refines(post, lbl);
        CachingDiskJournal::State::internal_alloc_preserves_journal(
            self,
            post,
            allocs,
            deallocs,
            prune_aus,
        );
        self.frozen_snapshot_valid_implies_i_metadata_valid(frozen, seq_end);
        AllocationJournal::State::internal_allocations_preserves_frozen_metadata_tight(
            self.i(),
            post.i(),
            lbl.i(self),
            meta,
        );
        assert(post.refinement_inv());

        self.i_metadata_valid_implies_frozen_tj_matches_i(frozen, seq_end);
        post.i_metadata_valid_implies_frozen_tj_matches_i(frozen, seq_end);
        assert(post.frozen_snapshot_valid(frozen, seq_end));
        assert(post.frozen_prefix_domain(frozen) =~= self.frozen_prefix_domain(frozen)) by {
            assert(post.frozen_prefix_domain(frozen) =~= post.i().frozen_prefix_domain(meta));
            assert(self.frozen_prefix_domain(frozen) =~= self.i().frozen_prefix_domain(meta));
            assert(post.i().frozen_prefix_domain(meta) =~= self.i().frozen_prefix_domain(meta));
        }
    }

    pub proof fn observe_clean_aus_preserves_frozen_snapshot_and_prefix(
        self,
        post: Self,
        aus: Set<AU>,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.refinement_inv(),
            post.refinement_inv(),
            self.frozen_snapshot_valid(frozen, seq_end),
            CachingDiskJournal::State::next(
                self,
                post,
                CachingDiskJournal::Label::ObserveCleanAUs{aus},
            ),
        ensures
            self.frozen_snapshot_preserved_by(post, frozen, seq_end),
            post.frozen_snapshot_valid(frozen, seq_end),
            post.frozen_tj(frozen) == self.frozen_tj(frozen),
            post.frozen_prefix_domain(frozen) =~= self.frozen_prefix_domain(frozen),
            self.persistent_visible_agree_on(self.frozen_prefix_domain(frozen)) ==>
                post.persistent_visible_agree_on(post.frozen_prefix_domain(frozen)),
            post.disk == self.disk,
    {
        CachingDiskJournal::State::observe_clean_aus_visible_unchanged(self, post, aus);
        CachingDiskJournal::State::observe_clean_aus_loaded_status_and_clean_watermark_monotonic(
            self,
            post,
            aus,
        );
        assert(post.au_page_bounds == self.au_page_bounds) by {
            reveal(CachingDiskJournal::State::next);
            reveal(CachingDiskJournal::State::next_by);
            let lbl = CachingDiskJournal::Label::ObserveCleanAUs{aus};
            let step = choose |step: CachingDiskJournal::Step|
                CachingDiskJournal::State::next_by(self, post, lbl, step);
            match step {
                CachingDiskJournal::Step::observe_clean_aus(new_journal) => {
                    reveal(CachingDiskJournal::State::observe_clean_aus);
                },
                _ => {
                    assert(false);
                },
            }
        }
        assert(post.lsn_au_index_or_empty() == self.lsn_au_index_or_empty()) by {
            reveal(CachingDiskJournal::State::next);
            reveal(CachingDiskJournal::State::next_by);
            let lbl = CachingDiskJournal::Label::ObserveCleanAUs{aus};
            let step = choose |step: CachingDiskJournal::Step|
                CachingDiskJournal::State::next_by(self, post, lbl, step);
            match step {
                CachingDiskJournal::Step::observe_clean_aus(new_journal) => {
                    reveal(CachingDiskJournal::State::observe_clean_aus);
                    CachedJournal::State::observe_clean_aus_effect(self.journal, post.journal, aus);
                },
                _ => {
                    assert(false);
                },
            }
        }
        assert(post.journal.seq_end() == self.journal.seq_end()) by {
            reveal(CachingDiskJournal::State::next);
            reveal(CachingDiskJournal::State::next_by);
            let lbl = CachingDiskJournal::Label::ObserveCleanAUs{aus};
            let step = choose |step: CachingDiskJournal::Step|
                CachingDiskJournal::State::next_by(self, post, lbl, step);
            match step {
                CachingDiskJournal::Step::observe_clean_aus(new_journal) => {
                    reveal(CachingDiskJournal::State::observe_clean_aus);
                    CachedJournal::State::observe_clean_aus_effect(self.journal, post.journal, aus);
                },
                _ => {
                    assert(false);
                },
            }
        }
        assert(post.frozen_seq_end(frozen) == self.frozen_seq_end(frozen)) by {
            if frozen.freshest_rec() is Some {
                let root = frozen.freshest_rec().unwrap();
                assert(post.journal_disk_view().entries[root]
                    == self.journal_disk_view().entries[root]);
            }
        }
        assert(post.frozen_lsns(frozen) =~= self.frozen_lsns(frozen)) by {
            assert forall |lsn: LSN| #[trigger] post.frozen_lsns(frozen).contains(lsn)
                <==> self.frozen_lsns(frozen).contains(lsn) by {}
        }
        assert(post.frozen_loose_domain(frozen) =~= self.frozen_loose_domain(frozen)) by {
            assert forall |addr: Address|
                #[trigger] post.frozen_loose_domain(frozen).contains(addr)
                <==> self.frozen_loose_domain(frozen).contains(addr) by {}
        }
        assert(post.frozen_tj(frozen).disk_view.entries
            == self.frozen_tj(frozen).disk_view.entries) by {
            assert_maps_equal!(
                post.frozen_tj(frozen).disk_view.entries,
                self.frozen_tj(frozen).disk_view.entries,
                addr => {}
            );
        }
        assert(post.frozen_tj(frozen) == self.frozen_tj(frozen));
        assert(post.frozen_prefix_domain(frozen) =~= self.frozen_prefix_domain(frozen)) by {
            assert forall |addr: Address|
                #[trigger] post.frozen_prefix_domain(frozen).contains(addr)
                <==> self.frozen_prefix_domain(frozen).contains(addr) by {}
        }
        assert(self.frozen_snapshot_preserved_by(post, frozen, seq_end));
    }

    pub proof fn put_preserves_frozen_materialization_certificate(
        self,
        post: Self,
        records: MsgHistory,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.refinement_inv(),
            post.refinement_inv(),
            self.frozen_materialization_certificate(frozen, seq_end),
            CachingDiskJournal::State::next(
                self,
                post,
                CachingDiskJournal::Label::Put{messages: records},
            ),
        ensures
            post.frozen_materialization_certificate(frozen, seq_end),
            post.i().frozen_metadata_valid(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
    {
        self.put_preserves_frozen_snapshot_and_prefix(post, records, frozen, seq_end);
        post.frozen_snapshot_valid_implies_i_metadata_valid(frozen, seq_end);
        assert(post.frozen_persistence_certificate(frozen));
    }

    pub proof fn observe_clean_aus_preserves_frozen_materialization_certificate(
        self,
        post: Self,
        aus: Set<AU>,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.refinement_inv(),
            post.refinement_inv(),
            self.frozen_materialization_certificate(frozen, seq_end),
            CachingDiskJournal::State::next(
                self,
                post,
                CachingDiskJournal::Label::ObserveCleanAUs{aus},
            ),
        ensures
            post.frozen_materialization_certificate(frozen, seq_end),
            post.i().frozen_metadata_valid(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
            post.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }).tight_tj() == self.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }).tight_tj(),
    {
        let lbl = CachingDiskJournal::Label::ObserveCleanAUs{aus};
        let meta = JournalMetadata{
            boundary_lsn: frozen.boundary_lsn,
            seq_end,
            freshest_rec: frozen.freshest_rec(),
            first: frozen.first(),
        };
        self.observe_clean_aus_preserves_frozen_snapshot_and_prefix(
            post,
            aus,
            frozen,
            seq_end,
        );
        self.next_refines(post, lbl);
        self.frozen_snapshot_valid_implies_i_metadata_valid(frozen, seq_end);
        AllocationJournal::State::internal_allocations_preserves_frozen_metadata_tight(
            self.i(),
            post.i(),
            lbl.i(self),
            meta,
        );
        post.frozen_snapshot_valid_implies_i_metadata_valid(frozen, seq_end);
        assert(post.frozen_persistence_certificate(frozen));
    }

    pub proof fn load_index_promotes_frozen_loose_to_materialization_certificate(
        self,
        post: Self,
        discovered_aus: Set<AU>,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.refinement_inv(),
            self.i().frozen_metadata_valid(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
            self.frozen_loose_persistence_certificate(frozen),
            CachingDiskJournal::State::next(
                self,
                post,
                CachingDiskJournal::Label::LoadIndex{discovered_aus},
            ),
        ensures
            post.refinement_inv(),
            post.frozen_materialization_certificate(frozen, seq_end),
            post.i().frozen_metadata_valid(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
            post.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }).tight_tj() == self.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }).tight_tj(),
    {
        let lbl = CachingDiskJournal::Label::LoadIndex{discovered_aus};
        let meta = JournalMetadata{
            boundary_lsn: frozen.boundary_lsn,
            seq_end,
            freshest_rec: frozen.freshest_rec(),
            first: frozen.first(),
        };
        self.load_index_preserves_frozen_snapshot_and_prefix(
            post,
            discovered_aus,
            frozen,
            seq_end,
        );
        self.next_refines(post, lbl);
        AllocationJournal::State::internal_allocations_preserves_frozen_metadata_tight(
            self.i(),
            post.i(),
            lbl.i(self),
            meta,
        );
        post.frozen_snapshot_valid_implies_i_metadata_valid(frozen, seq_end);
        assert(post.frozen_persistence_certificate(frozen));
    }

    pub proof fn internal_preserves_frozen_materialization_certificate(
        self,
        post: Self,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.refinement_inv(),
            self.frozen_materialization_certificate(frozen, seq_end),
            CachingDiskJournal::State::next(
                self,
                post,
                CachingDiskJournal::Label::Internal,
            ),
        ensures
            post.refinement_inv(),
            post.frozen_materialization_certificate(frozen, seq_end),
            post.i().frozen_metadata_valid(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
            post.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }).tight_tj() == self.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }).tight_tj(),
    {
        let lbl = CachingDiskJournal::Label::Internal;
        let meta = JournalMetadata{
            boundary_lsn: frozen.boundary_lsn,
            seq_end,
            freshest_rec: frozen.freshest_rec(),
            first: frozen.first(),
        };
        self.internal_preserves_frozen_snapshot_and_prefix(post, frozen, seq_end);
        self.next_refines(post, lbl);
        self.frozen_snapshot_valid_implies_i_metadata_valid(frozen, seq_end);
        AllocationJournal::State::internal_allocations_preserves_frozen_metadata_tight(
            self.i(),
            post.i(),
            lbl.i(self),
            meta,
        );
        post.frozen_snapshot_valid_implies_i_metadata_valid(frozen, seq_end);
        assert(post.frozen_persistence_certificate(frozen));
    }

    pub proof fn internal_unloaded_preserves_frozen_loose_persistence_certificate(
        self,
        post: Self,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.refinement_inv(),
            self.journal.status is None,
            self.i().frozen_metadata_valid(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
            self.frozen_loose_persistence_certificate(frozen),
            CachingDiskJournal::State::next(
                self,
                post,
                CachingDiskJournal::Label::Internal,
            ),
        ensures
            post.refinement_inv(),
            post.journal.status is None,
            post.frozen_loose_domain(frozen) =~= self.frozen_loose_domain(frozen),
            post.frozen_loose_persistence_certificate(frozen),
            post.i().frozen_metadata_valid(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
            post.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }).tight_tj() == self.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }).tight_tj(),
    {
        let lbl = CachingDiskJournal::Label::Internal;
        let meta = JournalMetadata{
            boundary_lsn: frozen.boundary_lsn,
            seq_end,
            freshest_rec: frozen.freshest_rec(),
            first: frozen.first(),
        };
        self.internal_unloaded_preserves_frozen_loose_agreement(post, frozen);
        self.next_refines(post, lbl);
        AllocationJournal::State::internal_allocations_preserves_frozen_metadata_tight(
            self.i(),
            post.i(),
            lbl.i(self),
            meta,
        );
        assert(post.frozen_loose_persistence_certificate(frozen));
    }

    pub proof fn internal_alloc_preserves_frozen_materialization_certificate(
        self,
        post: Self,
        allocs: Set<AU>,
        deallocs: Set<AU>,
        prune_aus: Set<AU>,
        frozen: JournalSnapshot,
        seq_end: LSN,
    )
        requires
            self.refinement_inv(),
            self.frozen_materialization_certificate(frozen, seq_end),
            CachingDiskJournal::State::next(
                self,
                post,
                CachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus},
            ),
        ensures
            post.refinement_inv(),
            post.frozen_materialization_certificate(frozen, seq_end),
            post.i().frozen_metadata_valid(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }),
            post.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }).tight_tj() == self.i().frozen_image(JournalMetadata{
                boundary_lsn: frozen.boundary_lsn,
                seq_end,
                freshest_rec: frozen.freshest_rec(),
                first: frozen.first(),
            }).tight_tj(),
    {
        let lbl = CachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus};
        let meta = JournalMetadata{
            boundary_lsn: frozen.boundary_lsn,
            seq_end,
            freshest_rec: frozen.freshest_rec(),
            first: frozen.first(),
        };
        self.internal_alloc_preserves_frozen_snapshot_and_prefix(
            post,
            allocs,
            deallocs,
            prune_aus,
            frozen,
            seq_end,
        );
        self.next_refines(post, lbl);
        self.frozen_snapshot_valid_implies_i_metadata_valid(frozen, seq_end);
        AllocationJournal::State::internal_allocations_preserves_frozen_metadata_tight(
            self.i(),
            post.i(),
            lbl.i(self),
            meta,
        );
        post.frozen_snapshot_valid_implies_i_metadata_valid(frozen, seq_end);
        assert(post.frozen_persistence_certificate(frozen));
    }

    pub proof fn mini_allocator_fill_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
        new_disk: CachingDisk::State,
    )
        requires
            self.inv(),
            post.inv(),
            self.semantic_inv(),
            CachingDiskJournal::State::mini_allocator_fill(self, post, lbl, new_disk),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::mini_allocator_fill);
        let allocs = lbl.arrow_InternalAlloc_allocs();
        assert(lbl.arrow_InternalAlloc_deallocs() == Set::<AU>::empty());
        assert(lbl.arrow_InternalAlloc_prune_aus() == Set::<AU>::empty());
        assert(post.journal == self.journal);
        assert(post.disk == new_disk);
        assert(post.mini_allocator == self.mini_allocator.add_aus(allocs));
        assert(allocs.disjoint(self.mini_allocator.allocs.dom()));
        assert(allocs.disjoint(self.i().lsn_au_index.values()));
        assert(post.i().disk_view.wf_addrs()) by {
            assert forall |addr: Address| #[trigger] post.i().disk_view.entries.contains_key(addr)
                implies addr.wf() by {
                assert(post.disk.visible().contains_key(addr));
                if post.disk.cache.contains_key(addr) {
                    assert(post.disk.cache.dom().contains(addr));
                } else {
                    assert(post.disk.persistent.contains_key(addr));
                    assert(post.disk.persistent.dom().contains(addr));
                }
            }
        }
        assert(self.i().disk_view.is_sub_disk(post.i().disk_view)) by {
            assert(self.i().disk_view.boundary_lsn == post.i().disk_view.boundary_lsn);
            assert(self.i().disk_view.entries <= post.i().disk_view.entries) by {
                assert forall |addr: Address| #[trigger] self.i().disk_view.entries.contains_key(addr)
                    implies post.i().disk_view.entries.contains_key(addr)
                        && post.i().disk_view.entries[addr] == self.i().disk_view.entries[addr] by {
                    assert(self.disk.visible().contains_key(addr));
                    assert(self.accessible_aus().contains(addr.au));
                    assert(!allocs.contains(addr.au)) by {
                        assert(allocs.disjoint(self.accessible_aus()));
                    }
                    if self.disk.cache.contains_key(addr) {
                        assert(post.disk.cache.contains_key(addr));
                        assert(post.disk.cache[addr] == self.disk.cache[addr]);
                        assert(post.disk.visible()[addr] == self.disk.visible()[addr]);
                    } else {
                        assert(self.disk.persistent.contains_key(addr));
                        assert(post.disk.persistent.contains_key(addr));
                        assert(post.disk.persistent[addr] == self.disk.persistent[addr]);
                        assert(!post.disk.cache.contains_key(addr)) by {
                            if post.disk.cache.contains_key(addr) {
                                assert(!self.disk.cache.contains_key(addr));
                                assert((post.disk.cache.dom() - self.disk.cache.dom()).contains(addr));
                                assert(addresses_in_aus(allocs).contains(addr));
                                assert(allocs.contains(addr.au));
                                assert(false);
                            }
                        }
                        assert(post.disk.visible()[addr] == self.disk.visible()[addr]);
                    }
                }
            }
        }
        assert(AllocationJournal::State::disk_domain_bounded_by_owned_aus(
            post.i().disk_view,
            self.i().lsn_au_index,
            post.i().mini_allocator,
        )) by {
            assert forall |addr: Address| #[trigger] post.i().disk_view.entries.dom().contains(addr)
                implies self.i().lsn_au_index.values().contains(addr.au)
                    || post.i().mini_allocator.all_aus().contains(addr.au) by {
                assert(post.disk.visible().contains_key(addr));
                assert(post.accessible_aus().contains(addr.au));
                if post.lsn_au_index_or_empty().values().contains(addr.au) {
                    assert(post.i().lsn_au_index.values().contains(addr.au));
                    assert(post.i().lsn_au_index == self.i().lsn_au_index);
                } else {
                    assert(post.mini_allocator.all_aus().contains(addr.au));
                }
            }
        }
        assert forall |addr: Address| {
            &&& #[trigger] post.i().disk_view.entries.contains_key(addr)
            &&& !self.i().disk_view.entries.contains_key(addr)
        } implies allocs.contains(addr.au) by {
            assert(post.disk.visible().contains_key(addr));
            assert(!self.disk.visible().contains_key(addr));
            if post.disk.cache.contains_key(addr) {
                assert(!self.disk.cache.contains_key(addr));
                assert((post.disk.cache.dom() - self.disk.cache.dom()).contains(addr));
                assert(addresses_in_aus(allocs).contains(addr));
            } else {
                assert(post.disk.persistent.contains_key(addr));
                assert(!self.disk.persistent.contains_key(addr));
                assert((post.disk.persistent.dom() - self.disk.persistent.dom()).contains(addr));
                assert(addresses_in_aus(allocs).contains(addr));
            }
        }
        assert(post.i().lsn_au_index == self.i().lsn_au_index);
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::internal_mini_allocator_fill(post.i().disk_view),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn mini_allocator_prune_refines(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
        new_disk: CachingDisk::State,
    )
        requires
            self.inv(),
            post.inv(),
            self.semantic_inv(),
            CachingDiskJournal::State::mini_allocator_prune(self, post, lbl, new_disk),
        ensures
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        reveal(CachingDiskJournal::State::mini_allocator_prune);
        let deallocs = lbl.arrow_InternalAlloc_deallocs();
        let prune_aus = lbl.arrow_InternalAlloc_prune_aus();
        assert(lbl.arrow_InternalAlloc_allocs() == Set::<AU>::empty());
        CachingDisk::State::forget_effect(self.disk, post.disk, deallocs);
        assert(post.journal == self.journal);
        assert(post.mini_allocator == self.mini_allocator.prune(prune_aus));
        assert(self.i().mini_allocator == self.mini_allocator);
        assert(post.i().lsn_au_index == self.i().lsn_au_index);
        assert(lbl.i(self).arrow_InternalAllocations_deallocs() == deallocs);
        assert forall |au: AU| #[trigger] prune_aus.contains(au)
            implies self.i().mini_allocator.can_remove(au) by {
            match lbl {
                CachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus} => {
                    assert(prune_aus.contains(au));
                    assert(self.mini_allocator.can_remove(au));
                    assert(self.i().mini_allocator == self.mini_allocator);
                },
                _ => {
                    assert(false);
                },
            }
        }
        assert forall |au: AU| #[trigger] deallocs.contains(au)
            implies self.i().mini_allocator.allocs.contains_key(au)
                && self.i().mini_allocator.allocs[au].all_pages_free() by {
            assert(deallocs <= prune_aus);
            assert(prune_aus.contains(au));
            assert(self.mini_allocator.can_remove(au));
            assert(self.mini_allocator.allocs.contains_key(au));
            assert(self.mini_allocator.allocs[au].all_pages_free());
            assert(self.i().mini_allocator == self.mini_allocator);
        }
        assert_maps_equal!(
            AllocationJournal::State::disk_view_without_aus(self.i().disk_view, deallocs).entries,
            post.i().disk_view.entries,
            addr => {
                if AllocationJournal::State::disk_view_without_aus(
                    self.i().disk_view,
                    deallocs,
                ).entries.contains_key(addr) {
                    assert(self.i().disk_view.entries.contains_key(addr));
                    assert(!deallocs.contains(addr.au));
                    assert(!addresses_in_aus(deallocs).contains(addr));
                    assert(post.disk.visible().contains_key(addr));
                    assert(post.disk.visible()[addr] == self.disk.visible()[addr]);
                    assert(post.i().disk_view.entries[addr] == self.i().disk_view.entries[addr]);
                }
                if post.i().disk_view.entries.contains_key(addr) {
                    assert(post.disk.visible().contains_key(addr));
                    assert(!addresses_in_aus(deallocs).contains(addr));
                    assert(!deallocs.contains(addr.au));
                    assert(self.disk.visible().contains_key(addr));
                    assert(self.i().disk_view.entries.contains_key(addr));
                }
            }
        );
        assert(post.i().disk_view.boundary_lsn == self.i().disk_view.boundary_lsn);
        assert(post.i().disk_view
            == AllocationJournal::State::disk_view_without_aus(self.i().disk_view, deallocs));
        assert(post.i().mini_allocator == self.i().mini_allocator.prune(prune_aus));
        assert(AllocationJournal::State::next_by(
            self.i(),
            post.i(),
            lbl.i(self),
            AllocationJournal::Step::internal_mini_allocator_prune(prune_aus),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        reveal(AllocationJournal::State::next);
    }

    pub proof fn unloaded_backing_image_valid_next(
        self,
        post: Self,
        lbl: CachingDiskJournal::Label,
    )
        requires
            self.inv(),
            self.unloaded_backing_image_valid(),
            CachingDiskJournal::State::next(self, post, lbl),
        ensures
            post.unloaded_backing_image_valid(),
    {
        reveal(CachingDiskJournal::State::next);
        let step = choose |step: CachingDiskJournal::Step| #![auto]
            CachingDiskJournal::State::next_by(self, post, lbl, step);
        reveal(CachingDiskJournal::State::next_by);
        if post.journal.status is None {
            match step {
                CachingDiskJournal::Step::caching_disk_internal(new_disk) => {
                    reveal(CachingDiskJournal::State::caching_disk_internal);
                    CachingDisk::State::internal_visible_unchanged(self.disk, post.disk);
                    assert(post.journal == self.journal);
                    assert(post.journal_disk_view().entries == self.journal_disk_view().entries);
                    assert(post.journal_disk_view() == self.journal_disk_view());
                    assert(post.backing_journal_image() == self.backing_journal_image());
                    assert(self.backing_journal_image().valid_image());
                },
                CachingDiskJournal::Step::load_index(new_journal, reads) => {
                    reveal(CachingDiskJournal::State::load_index);
                    let journal_lbl = CachedJournal::Label::LoadIndex{
                        reads: to_journal_records(reads),
                        discovered_aus: lbl.arrow_LoadIndex_discovered_aus(),
                    };
                    CachedJournal::State::status_some_next_effect(
                        self.journal,
                        post.journal,
                        journal_lbl,
                    );
                    assert(post.journal.status is Some);
                    assert(false);
                },
                CachingDiskJournal::Step::read_for_recovery(reads) => {
                    reveal(CachingDiskJournal::State::read_for_recovery);
                    let journal_lbl = CachedJournal::Label::ReadForRecovery{
                        messages: lbl.arrow_ReadForRecovery_messages(),
                        reads: to_journal_records(reads),
                    };
                    CachedJournal::State::status_some_next_effect(
                        self.journal,
                        self.journal,
                        journal_lbl,
                    );
                    assert(post == self);
                    assert(false);
                },
                CachingDiskJournal::Step::freeze_for_commit(reads) => {
                    reveal(CachingDiskJournal::State::freeze_for_commit);
                    let journal_lbl = CachedJournal::Label::FreezeForCommit{
                        frozen: lbl.arrow_FreezeForCommit_frozen(),
                        reads: to_journal_records(reads),
                    };
                    CachedJournal::State::status_some_next_effect(
                        self.journal,
                        self.journal,
                        journal_lbl,
                    );
                    assert(post == self);
                    assert(false);
                },
                CachingDiskJournal::Step::query_end_lsn() => {
                    reveal(CachingDiskJournal::State::query_end_lsn);
                    let journal_lbl = CachedJournal::Label::QueryEndLsn{
                        end_lsn: lbl.arrow_QueryEndLsn_end_lsn(),
                    };
                    CachedJournal::State::status_some_next_effect(
                        self.journal,
                        self.journal,
                        journal_lbl,
                    );
                    assert(post == self);
                    assert(false);
                },
                CachingDiskJournal::Step::put(new_journal) => {
                    reveal(CachingDiskJournal::State::put);
                    let journal_lbl = CachedJournal::Label::Put{
                        messages: lbl.arrow_Put_messages(),
                    };
                    CachedJournal::State::status_some_next_effect(
                        self.journal,
                        post.journal,
                        journal_lbl,
                    );
                    assert(post.journal.status is Some);
                    assert(false);
                },
                CachingDiskJournal::Step::journal_marshal(new_journal, new_disk, addr, writes) => {
                    reveal(CachingDiskJournal::State::journal_marshal);
                    let journal_lbl = CachedJournal::Label::JournalMarshal{
                        writes: to_journal_records(writes),
                    };
                    CachedJournal::State::status_some_next_effect(
                        self.journal,
                        post.journal,
                        journal_lbl,
                    );
                    assert(post.journal.status is Some);
                    assert(false);
                },
                CachingDiskJournal::Step::observe_clean_aus(new_journal) => {
                    reveal(CachingDiskJournal::State::observe_clean_aus);
                    let journal_lbl = CachedJournal::Label::ObserveCleanAUs{
                        aus: lbl.arrow_ObserveCleanAUs_aus(),
                    };
                    CachedJournal::State::status_some_next_effect(
                        self.journal,
                        post.journal,
                        journal_lbl,
                    );
                    assert(post.journal.status is Some);
                    assert(false);
                },
                CachingDiskJournal::Step::commit_prepared() => {
                    reveal(CachingDiskJournal::State::commit_prepared);
                    assert(post == self);
                    assert(false);
                },
                CachingDiskJournal::Step::discard_old(new_journal, new_disk) => {
                    reveal(CachingDiskJournal::State::discard_old);
                    let journal_lbl = CachedJournal::Label::DiscardOld{
                        start_lsn: lbl.arrow_DiscardOld_start_lsn(),
                        require_end: lbl.arrow_DiscardOld_require_end(),
                        deallocs: lbl.arrow_DiscardOld_deallocs(),
                    };
                    CachedJournal::State::status_some_next_effect(
                        self.journal,
                        post.journal,
                        journal_lbl,
                    );
                    assert(post.journal.status is Some);
                    assert(false);
                },
                CachingDiskJournal::Step::mini_allocator_fill(new_disk) => {
                    reveal(CachingDiskJournal::State::mini_allocator_fill);
                    assert(post.journal == self.journal);
                    assert(post.backing_journal_image() == self.backing_journal_image()) by {
                        assert(post.journal_disk_view() == self.journal_disk_view());
                    }
                    assert(self.backing_journal_image().valid_image());
                },
                CachingDiskJournal::Step::mini_allocator_prune(new_disk) => {
                    reveal(CachingDiskJournal::State::mini_allocator_prune);
                    assert(self.journal.status is Some);
                    assert(post.journal.status is Some);
                    assert(false);
                },
                CachingDiskJournal::Step::internal_noop() => {
                    reveal(CachingDiskJournal::State::internal_noop);
                    assert(post == self);
                },
                CachingDiskJournal::Step::dummy_to_use_type_params(_) => {
                    assert(false);
                },
            }
        }
    }

    pub proof fn next_refines(self, post: Self, lbl: CachingDiskJournal::Label)
        requires
            self.inv(),
            self.semantic_inv(),
            CachingDiskJournal::State::next(self, post, lbl),
        ensures
            post.inv(),
            post.semantic_inv(),
            post.refinement_inv(),
            AllocationJournal::State::next(self.i(), post.i(), lbl.i(self)),
    {
        CachingDiskJournal::State::inv_next(self, post, lbl);
        reveal(CachingDiskJournal::State::next);
        let step = choose |step: CachingDiskJournal::Step| #![auto]
            CachingDiskJournal::State::next_by(self, post, lbl, step);
        reveal(CachingDiskJournal::State::next_by);
        match step {
            CachingDiskJournal::Step::caching_disk_internal(new_disk) => {
                self.caching_disk_internal_refines(post, lbl, new_disk);
            },
            CachingDiskJournal::Step::load_index(new_journal, reads) => {
                self.load_index_refines(post, lbl, new_journal, reads);
            },
            CachingDiskJournal::Step::read_for_recovery(reads) => {
                self.read_for_recovery_refines(post, lbl, reads);
            },
            CachingDiskJournal::Step::freeze_for_commit(reads) => {
                self.freeze_for_commit_refines(post, lbl, reads);
            },
            CachingDiskJournal::Step::query_end_lsn() => {
                self.query_end_lsn_refines(post, lbl);
            },
            CachingDiskJournal::Step::put(new_journal) => {
                self.put_refines(post, lbl, new_journal);
            },
            CachingDiskJournal::Step::journal_marshal(new_journal, new_disk, addr, writes) => {
                self.journal_marshal_refines(post, lbl, new_journal, new_disk, addr, writes);
            },
            CachingDiskJournal::Step::observe_clean_aus(new_journal) => {
                self.observe_clean_aus_refines(post, lbl, new_journal);
            },
            CachingDiskJournal::Step::commit_prepared() => {
                self.commit_prepared_refines(post, lbl);
            },
            CachingDiskJournal::Step::discard_old(new_journal, new_disk) => {
                self.discard_old_refines(post, lbl, new_journal, new_disk);
            },
            CachingDiskJournal::Step::mini_allocator_fill(new_disk) => {
                self.mini_allocator_fill_refines(post, lbl, new_disk);
            },
            CachingDiskJournal::Step::mini_allocator_prune(new_disk) => {
                self.mini_allocator_prune_refines(post, lbl, new_disk);
            },
            CachingDiskJournal::Step::internal_noop() => {
                self.internal_noop_refines(post, lbl);
            },
            CachingDiskJournal::Step::dummy_to_use_type_params(_) => {
                assert(false);
            },
        }
        self.semantic_inv_implies_i_inv();
        self.i().next_refines(post.i(), lbl.i(self));
        self.unloaded_backing_image_valid_next(post, lbl);
        post.i_refinement_inv_implies_semantic_inv();
        assert(post.refinement_inv());
    }
}

} // verus!
