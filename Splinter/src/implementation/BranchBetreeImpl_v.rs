// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::multiset::Multiset;
use vstd::assert_maps_equal;
use vstd::assert_multisets_equal;
use vstd::assert_seqs_equal;
use vstd::assert_sets_equal;

use crate::abstract_system::MsgHistory_v::KeyedMessage;
use crate::allocation_layer::BranchTypes_v::BranchNode;
use crate::allocation_layer::AllocationBranchBetree_v::{
    CompactorInput, map_with_disjoint_values, read_ref_aus, summary_aus,
};
use crate::allocation_layer::Likes_v::{
    AULikes, to_au_likes, to_au_likes_empty, to_au_likes_singleton,
};
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::Buffer_v::Buffer;
use crate::betree::LinkedBetree_v::{
    Addrs, DiskView as BetreeDiskView, LinkedBetree, SplitAddrs, TwoAddrs,
};
use crate::betree::SplitRequest_v::SplitRequest;
use crate::disk::GenericDisk_v::{AU, Address, Pointer};
use crate::implementation::AtomicBranchBetreeState_v::{
    AtomicBranchBetreeControl, AtomicBranchBetreeState,
    empty_cached_betree, recovery_page_access,
};
use crate::implementation::AuLikesImpl_v::{
    AuLikesImpl, AuLikesUpdateResult, au_likes_delta_applicable,
    iau_seq_set, seq_to_au_likes, unique_iau_seq,
};
use crate::implementation::BetreeRecoveryImpl_v::{
    BetreeRecoveryApplyResult, BetreeRecoveryImpl, BetreeRecoveryNeed,
};
use crate::implementation::BetreeQueryImpl_v::{
    BetreeQueryResult, cached_betree_query_valid, load_betree_query,
    merge_messages,
};
use crate::implementation::BranchScanCursorImpl_v::{
    BranchScanCursor, cached_branch_scan_valid,
};
use crate::implementation::BranchScanSemantics_v::{
    keyed_entries_contains, keyed_entries_query,
    keyed_entries_query_index, sealed_branch_refines_buffer,
};
use crate::implementation::CompactionFilterImpl_v::CompactionFilterImpl;
use crate::implementation::CompactorMergeCursorImpl_v::{
    CompactorMergeCursor, CompactorMergeStepResult,
    compactor_source_disks_agree, keyed_entries_strictly_sorted,
    establish_compactor_source_disks_agree,
};
use crate::implementation::StreamingBranchBuilderImpl_v::{
    StreamingBranchPhase, StreamingFinishInputResult,
    StreamingFinishLevelResult,
};
use crate::implementation::BranchBetreeOwnershipImpl_v::{
    BetreeOwnershipUpdateResult, BranchBetreeOwnershipImpl,
    BranchOwnershipUpdateResult, BranchSummaryOwnershipImpl,
    betree_batch_replace_applicable,
};
use crate::implementation::BetreePageImpl_v::{
    betree_node_addr, build_grow_betree_root,
    build_initial_betree_root, marshall_betree_node_page,
};
use crate::implementation::BetreeMaintenanceImpl_v::{
    BetreeRootExtendResult, cached_betree_root_wf,
    extend_root_buffer_with_cache,
};
use crate::implementation::BetreePathImpl_v::{
    BetreePathLoadResult, betree_path_receipt_edges,
    cached_betree_path_prefix_valid, load_betree_path,
};
use crate::implementation::BetreeSplitWriteImpl_v::{
    build_split_write_batch, cached_split_parent_wf,
    cached_split_selected_child_wf, disjoint_au_views_are_unique,
    iaddr_views, iaddress_aus, iaddress_aus_likes,
    path_valid_after_child_read, split_added_au_likes,
    split_discard_au_likes,
};
use crate::implementation::BetreeFlushWriteImpl_v::{
    build_compact_write_batch, build_flush_write_batch,
    cached_flush_parent_wf, two_added_au_likes,
};
use crate::implementation::BetreeStructuralPageImpl_v::{
    IBetreeSplitRequest, compact_node_view, split_parent_view,
};
use crate::implementation::BetreeWriteBatchImpl_v::{
    betree_raw_writes, write_betree_pages,
};
use crate::implementation::CacheWritePrepareImpl_v::{
    CacheWritePrepareResult, prepare_cache_write_addrs,
};
use crate::implementation::CachedBranchBetree_v::{
    CachedBranchBetree, CachedBranchBetreeAccess, FrozenBranchBetree,
    loaded_branch_reads_for_roots, loaded_sealed_branch,
    valid_loaded_sealed_branch, valid_loaded_sealed_branches,
};
use crate::implementation::CachedBulkBranch_v::{
    CachedBulkBranch, CachedBulkBranchEvent,
};
use crate::implementation::CachingDiskBranchBetree_v::{
    PageAccess, to_betree_nodes, to_branch_nodes,
};
use crate::implementation::CachingDisk_v::addresses_in_aus;
use crate::implementation::CrashAwareCachingDiskBranchBetree_v::{
    BetreeMetadataRecoveryCore, BetreeMetadataRecoveryLabel,
    CachingDiskBranchBetreeMetadata,
    FrozenCachingDiskBranchBetree,
};
use crate::implementation::IBranchNode_v::{IBranchNode, iopt_addr};
use crate::implementation::IBetreeNode_v::IBetreeNode;
use crate::implementation::MemtableImpl_v::{
    MemtableBucket, MemtableEntry, MemtableImpl, MemtableUpdateResult,
};
use crate::implementation::BulkBranchImpl_v::{
    BulkBranchImpl, BulkBranchInitializeResult, BulkBranchSealResult,
    BulkBranchReadResult, WipLeafContents, bulk_branch_views,
    bulk_branches_wf, bulk_builders_wf, no_bulk_builders,
    BulkBuilderImpl, BulkSealResult, BulkStageResult, BulkStartResult,
};
use crate::implementation::BranchBulkBuilderImpl_v::BranchBulkPhase;
use crate::implementation::MiniAllocatorImpl_v::MiniAllocatorImpl;
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::implementation::AuPoolImpl_v::iau_vec_set;
use crate::implementation::Cache_v::Cache;
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::implementation::FracCacheImpl_v::{
    CACHE_SIZE_RECS, FetchErrorCode, FracCacheImpl, MutHandle,
    ReserveWriteResult,
};
use crate::marshalling::IBetreeNodeFormat_v::{
    BetreeNodePageFmt, raw_page_to_betree_node,
};
use crate::marshalling::IBranchNodeFormat_v::{
    BranchNodePageFmt, raw_page_to_branch_node,
};
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::WF_v::WF;
use crate::spec::ImplDisk_t::{IAddress, IAU};
use crate::spec::AsyncDisk_t::RawPage;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Message, Value};
use crate::disk::GenericDisk_v::{
    seq_addrs_disjoint_aus, set_addrs_disjoint_aus, to_aus,
};

verus! {

proof fn empty_recovery_likes_are_empty()
    ensures ({
        let metadata = CachingDiskBranchBetreeMetadata::empty();
        let loaded = BetreeMetadataRecoveryCore::start(metadata)
            .loaded_betree(metadata);
        &&& loaded.betree_aus == AULikes::empty()
        &&& loaded.branch_aus == AULikes::empty()
    }),
{
    let metadata = CachingDiskBranchBetreeMetadata::empty();
    let core = BetreeMetadataRecoveryCore::start(metadata);
    let tree = core.recovered_likes_tree(metadata);
    let empty_tree = LinkedBetree {
        root: Option::None,
        dv: BetreeDiskView { entries: Map::empty() },
        buffer_dv: BufferDisk::<BranchNode>::empty_disk(),
    };
    assert(tree == empty_tree);





    assert(empty_tree.valid_ranking(Map::<Address, nat>::empty()));
    assert(empty_tree.acyclic());



    assert(empty_tree.transitive_likes() == (
        Multiset::<Address>::empty(),
        Multiset::<Address>::empty(),
    ));
    to_au_likes_empty();
    assert(to_au_likes(empty_tree.transitive_likes().0)
        == AULikes::empty());
    assert(to_au_likes(empty_tree.transitive_likes().1)
        == AULikes::empty());
}

#[derive(Clone, Copy, Debug)]
pub struct BetreeMetadataImpl {
    pub root: Option<IAddress>,
    pub seq_end: u64,
}

impl BetreeMetadataImpl {
    pub open spec fn wf(&self) -> bool {
        match self.root {
            Some(root) => root@.wf(),
            None => true,
        }
    }

    pub fn empty() -> (out: Self)
        ensures
            out.wf(),
            out@ == CachingDiskBranchBetreeMetadata::empty(),
    {
        Self { root: None, seq_end: 0 }
    }
}

impl View for BetreeMetadataImpl {
    type V = CachingDiskBranchBetreeMetadata;

    open spec fn view(&self) -> Self::V {
        CachingDiskBranchBetreeMetadata {
            root: iopt_addr(self.root),
            seq_end: self.seq_end as nat,
        }
    }
}

pub struct BranchBetreeControlImpl {
    pub metadata: BetreeMetadataImpl,
    pub installed: bool,
    pub loading: bool,
    pub metadata_loaded: bool,
    pub frozen_metadata: Option<BetreeMetadataImpl>,
}

pub struct CompactorImpl {
    pub input_buffers: Vec<IAddress>,
    pub input_nodes: Ghost<crate::implementation::CachedBranch_v::LoadedBranch>,
    pub input_aus: Ghost<Set<AU>>,
    pub input_summaries: Ghost<Map<AU, Set<AU>>>,
    pub offset_map: Ghost<crate::betree::OffsetMap_v::OffsetMap>,
    pub filter: CompactionFilterImpl,
    pub merge: Option<CompactorMergeCursor>,
    pub merge_done: bool,
}

pub open spec fn compact_stream_entries(
    entries: Seq<KeyedMessage>,
) -> Seq<MemtableEntry> {
    entries.map(|i: int, item: KeyedMessage| MemtableEntry {
        key: item.key,
        message: item.message,
    })
}

pub open spec fn compactor_input_root_aus(
    compactor: CompactorImpl,
) -> Set<AU> {
    to_aus(Parsedview::<Seq<Address>>::parsedv(
        &compactor.input_buffers,
    ).to_set())
}

proof fn compact_stream_entries_index(
    entries: Seq<KeyedMessage>,
    index: int,
)
    requires 0 <= index < entries.len(),
    ensures
        compact_stream_entries(entries)[index] == (MemtableEntry {
            key: entries[index].key,
            message: entries[index].message,
        }),
{
}

proof fn compact_stream_entries_push(
    entries: Seq<KeyedMessage>,
    item: KeyedMessage,
)
    ensures
        compact_stream_entries(entries.push(item))
            == compact_stream_entries(entries).push(MemtableEntry {
                key: item.key,
                message: item.message,
            }),
{
    assert_seqs_equal!(
        compact_stream_entries(entries.push(item)),
        compact_stream_entries(entries).push(MemtableEntry {
            key: item.key,
            message: item.message,
        }),
        i => {
            if i < entries.len() {
                compact_stream_entries_index(entries, i);
            }
        }
    );
}

impl CompactorImpl {
    pub open spec fn wf(&self) -> bool {
        &&& self.filter.wf()
        &&& Parsedview::<Seq<Address>>::parsedv(&self.input_buffers)
            == self.filter.target@.buffers.slice(
                self.filter.start as int,
                self.filter.end as int,
            ).addrs
        &&& self.input_buffers@.len()
            == self.filter.end - self.filter.start
        &&& self.input_nodes@.dom() <= addresses_in_aus(self.input_aus@)
        &&& forall |i: int| 0 <= i < self.input_buffers@.len()
            ==> (#[trigger] self.input_buffers@[i])@
                == self.filter.target@.buffers.addrs[
                    self.filter.start as int + i]
        &&& self.offset_map@
            == self.filter.target@.make_offset_map().decrement(
                self.filter.start as nat,
            )
        &&& match self.merge {
            Some(ref merge) => {
                &&& merge.wf()
                &&& merge.filter.target@.buffers.addrs
                    == self.filter.target@.buffers.addrs
                &&& merge.filter.target@.pivots.pivots
                    == self.filter.target@.pivots.pivots
                &&& merge.filter.target@.flushed.offsets
                    == self.filter.target@.flushed.offsets
                &&& merge.filter.start == self.filter.start
                &&& merge.filter.end == self.filter.end
                &&& merge.source_aus() <= self.input_aus@
                &&& self.input_nodes@ == merge.scanned_nodes()
                &&& set_addrs_disjoint_aus(
                    Parsedview::<Seq<Address>>::parsedv(
                        &self.input_buffers,
                    ).to_set(),
                )
                &&& map_with_disjoint_values(self.input_summaries@)
                &&& forall |i: int| 0 <= i < merge.cursors@.len() ==> {
                    let source = (#[trigger] merge.cursors@[i]).source@;
                    &&& self.input_summaries@.contains_key(source.root.au)
                    &&& source.get_summary()
                        == self.input_summaries@[source.root.au]
                }
                &&& (self.merge_done ==> {
                    &&& merge.exhausted()
                    &&& merge.scan_complete()
                })
            },
            None => {
                &&& !self.merge_done
                &&& self.input_nodes@.is_empty()
                &&& self.input_aus@.is_empty()
                &&& self.input_summaries@.is_empty()
            },
        }
    }

    pub open spec fn cache_inv(&self, cache: Cache::State) -> bool {
        match self.merge {
            Some(ref merge) => merge.cache_inv(cache),
            None => true,
        }
    }

    pub fn matches_completion_target(
        &self,
        target: &IBetreeNode,
        start: usize,
        end: usize,
    ) -> (out: bool)
        requires
            self.wf(),
            target.wf(),
            target@.wf(),
            start < end <= target.buffers.len(),
        ensures
            out ==> {
                &&& self.filter.start == start
                &&& self.filter.end == end
                &&& Parsedview::<Seq<Address>>::parsedv(&self.input_buffers)
                    == target@.buffers.slice(
                        start as int,
                        end as int,
                    ).addrs
                &&& self.filter.target@.pivots.pivots
                    == target@.pivots.pivots
                &&& self.filter.target@.flushed.offsets
                    == target@.flushed.offsets
                &&& self.offset_map@
                    == target@.make_offset_map().decrement(start as nat)
            },
    {
        if self.filter.start != start
            || self.filter.end != end
            || self.input_buffers.len() != end - start
        {
            return false;
        }
        if !self.filter.matches_target_metadata(target) {
            return false;
        }
        let mut idx = 0usize;
        while idx < self.input_buffers.len()
            invariant
                self.wf(),
                target.wf(),
                target@.wf(),
                self.filter.start == start,
                self.filter.end == end,
                start < end <= target.buffers.len(),
                self.input_buffers.len() == end - start,
                idx <= self.input_buffers.len(),
                self.filter.target@.pivots.pivots
                    == target@.pivots.pivots,
                self.filter.target@.flushed.offsets
                    == target@.flushed.offsets,
                self.offset_map@
                    == target@.make_offset_map().decrement(start as nat),
                forall |i: int| 0 <= i < idx
                    ==> (#[trigger] self.input_buffers@[i])@
                        == target.buffers@[start as int + i]@,
            decreases self.input_buffers.len() - idx,
        {
            if self.input_buffers[idx].au != target.buffers[start + idx].au
                || self.input_buffers[idx].page
                    != target.buffers[start + idx].page
            {
                return false;
            }
            proof {
                assert(self.input_buffers@[idx as int]@
                    == target.buffers@[(start + idx) as int]@);
            }
            idx += 1;
        }
        proof {
            assert_seqs_equal!(
                Parsedview::<Seq<Address>>::parsedv(&self.input_buffers),
                target@.buffers.slice(start as int, end as int).addrs,
                i => {
                    assert(target@.buffers.slice(
                        start as int,
                        end as int,
                    ).addrs[i] == target@.buffers.addrs[start as int + i]);
                }
            );
        }
        true
    }

    pub proof fn input_roots_subset_input_aus(&self)
        requires self.wf(), self.merge is Some,
        ensures to_aus(
            Parsedview::<Seq<Address>>::parsedv(&self.input_buffers).to_set(),
        ) <= self.input_aus@,
    {
        let roots = Parsedview::<Seq<Address>>::parsedv(
            &self.input_buffers,
        ).to_set();
        let merge = self.merge->0;
        assert forall |au: AU| #[trigger] to_aus(roots).contains(au)
            implies self.input_aus@.contains(au) by {
            let addr = crate::disk::GenericDisk_v::to_aus_get_addr(
                roots,
                au,
            );
            let i = choose |i: int| 0 <= i < self.input_buffers@.len()
                && self.input_buffers@[i]@ == addr;
            assert(merge.cursors@[i].source@.root == addr);
            assert(merge.cursors@[i].source@.full_repr().contains(addr));
            assert(merge.cursors@[i].source@.get_summary().contains(au));
            assert(merge.source_aus().contains(au));
        }
    }

    pub proof fn completed_receipt_valid(
        &self,
        branch_summary: Map<AU, Set<AU>>,
    )
        requires
            self.wf(),
            self.merge is Some,
            self.merge_done,
            map_with_disjoint_values(branch_summary),
            compactor_input_root_aus(*self) <= branch_summary.dom(),
            self.input_summaries@ == branch_summary.restrict(
                compactor_input_root_aus(*self),
            ),
        ensures
            valid_loaded_sealed_branches(
                Parsedview::<Seq<Address>>::parsedv(
                    &self.input_buffers,
                ).to_set(),
                branch_summary,
                self.input_nodes@,
            ),
    {
        let merge = self.merge->0;
        merge.source_roots_match_filter();
        assert(merge.source_roots()
            == Parsedview::<Seq<Address>>::parsedv(
                &self.input_buffers,
            ).to_set());
        assert(set_addrs_disjoint_aus(merge.source_roots()));
        assert forall |i: int| 0 <= i < merge.cursors@.len()
            implies {
                let source = (#[trigger] merge.cursors@[i]).source@;
                &&& branch_summary.contains_key(source.root.au)
                &&& branch_summary[source.root.au]
                    == source.get_summary()
            } by {
            let source = merge.cursors@[i].source@;
            assert(self.input_summaries@.contains_key(source.root.au));
            assert(compactor_input_root_aus(*self)
                .contains(source.root.au)) by {
                let roots = Parsedview::<Seq<Address>>::parsedv(
                    &self.input_buffers,
                ).to_set();
                assert(roots.contains(source.root));
                crate::disk::GenericDisk_v::to_aus_domain(roots);
            }
            assert(self.input_summaries@[source.root.au]
                == branch_summary[source.root.au]);
        }
        merge.completed_receipt_valid(branch_summary);
        assert(self.input_nodes@ == merge.scanned_nodes());
    }

    pub proof fn completed_output_valid(
        &self,
        branch_summary: Map<AU, Set<AU>>,
    )
        requires
            self.wf(),
            self.merge is Some,
            self.merge_done,
            map_with_disjoint_values(branch_summary),
            compactor_input_root_aus(*self) <= branch_summary.dom(),
            self.input_summaries@ == branch_summary.restrict(
                compactor_input_root_aus(*self),
            ),
        ensures ({
            let disk = BufferDisk::<BranchNode> {
                entries: self.input_nodes@,
            };
            let target = self.filter.target@;
            let output = self.merge->0.output@;
            &&& forall |key: Key|
                keyed_entries_contains(output, key)
                    <==> disk.valid_compact_key_domain(
                        target,
                        self.filter.start as nat,
                        self.filter.end as nat,
                        key,
                    )
            &&& forall |key: Key|
                keyed_entries_contains(output, key)
                    ==> keyed_entries_query(output, key)
                        == disk.compact_key_value(
                            target,
                            self.filter.start as nat,
                            self.filter.end as nat,
                            key,
                        )
        }),
    {
        crate::implementation::CompactorCompletionSemantics_v::
            completed_output_valid(self, branch_summary);
    }

    pub proof fn sealed_output_valid(
        &self,
        branch_summary: Map<AU, Set<AU>>,
        output_branch: crate::betree::LinkedBranch_v::LinkedBranch<
            crate::allocation_layer::BranchTypes_v::Summary,
        >,
    )
        requires
            self.wf(),
            self.merge is Some,
            self.merge_done,
            map_with_disjoint_values(branch_summary),
            compactor_input_root_aus(*self) <= branch_summary.dom(),
            self.input_summaries@ == branch_summary.restrict(
                compactor_input_root_aus(*self),
            ),
            output_branch.valid_sealed_branch(),
            output_branch.tight_disk_view_with_summary(),
            output_branch.i().i().map
                == MemtableBucket::entries_map(compact_stream_entries(
                    self.merge->0.output@,
                )),
        ensures ({
            let input_disk = BufferDisk::<BranchNode> {
                entries: self.input_nodes@,
            };
            let output_disk = BufferDisk::<BranchNode> {
                entries: output_branch.disk_view.entries,
            };
            let target = self.filter.target@;
            &&& forall |key: Key|
                output_branch.root().linked_contains(
                    output_disk,
                    output_branch.root,
                    key,
                ) <==> input_disk.valid_compact_key_domain(
                    target,
                    self.filter.start as nat,
                    self.filter.end as nat,
                    key,
                )
            &&& forall |key: Key|
                output_branch.root().linked_contains(
                    output_disk,
                    output_branch.root,
                    key,
                ) ==> output_branch.root().linked_query(
                    output_disk,
                    output_branch.root,
                    key,
                ) == input_disk.compact_key_value(
                    target,
                    self.filter.start as nat,
                    self.filter.end as nat,
                    key,
                )
        }),
    {
        crate::implementation::CompactorCompletionSemantics_v::
            sealed_output_valid(self, branch_summary, output_branch);
    }
}

impl View for CompactorImpl {
    type V = CompactorInput;

    open spec fn view(&self) -> CompactorInput {
        CompactorInput {
            input_buffers: crate::betree::LinkedSeq_v::LinkedSeq {
                addrs: Parsedview::<Seq<Address>>::parsedv(
                    &self.input_buffers,
                ),
            },
            offset_map: self.offset_map@,
        }
    }
}

fn clone_addr_subrange(
    addrs: &Vec<IAddress>,
    start: usize,
    end: usize,
) -> (out: Vec<IAddress>)
    requires start <= end <= addrs.len(),
    ensures
        out@ == addrs@.subrange(start as int, end as int),
        out@.len() == end - start,
        Parsedview::<Seq<Address>>::parsedv(&out)
            == Parsedview::<Seq<Address>>::parsedv(addrs)
                .subrange(start as int, end as int),
{
    let mut out = Vec::<IAddress>::new();
    let mut index = start;
    while index < end
        invariant
            start <= index <= end,
            end <= addrs.len(),
            out@ == addrs@.subrange(start as int, index as int),
            Parsedview::<Seq<Address>>::parsedv(&out)
                == Parsedview::<Seq<Address>>::parsedv(addrs)
                    .subrange(start as int, index as int),
        decreases end - index,
    {
        out.push(addrs[index]);
        proof {
            assert(Parsedview::<Seq<Address>>::parsedv(&out)
                == Parsedview::<Seq<Address>>::parsedv(addrs)
                    .subrange(start as int, index as int + 1));
        }
        index += 1;
    }
    out
}

fn append_address(
    addrs: &Vec<IAddress>,
    last: IAddress,
) -> (out: Vec<IAddress>)
    ensures out@ == addrs@.push(last),
{
    let mut out = addrs.clone();
    out.push(last);
    out
}

fn split_destination_addrs(
    left: IAddress,
    right: IAddress,
    parent: IAddress,
    path_addrs: &Vec<IAddress>,
) -> (out: Vec<IAddress>)
    ensures
        out@ == seq![left, right, parent] + path_addrs@,
{
    let mut out = Vec::<IAddress>::new();
    out.push(left);
    out.push(right);
    out.push(parent);
    let mut index = 0usize;
    while index < path_addrs.len()
        invariant
            index <= path_addrs.len(),
            out@ == seq![left, right, parent]
                + path_addrs@.take(index as int),
        decreases path_addrs.len() - index,
    {
        out.push(path_addrs[index]);
        index += 1;
    }
    proof {
        assert(path_addrs@.take(index as int) == path_addrs@);
    }
    out
}

fn flush_destination_addrs(
    parent: IAddress,
    child: IAddress,
    path_addrs: &Vec<IAddress>,
) -> (out: Vec<IAddress>)
    ensures out@ == seq![parent, child] + path_addrs@,
{
    let mut out = Vec::<IAddress>::new();
    out.push(parent);
    out.push(child);
    let mut index = 0usize;
    while index < path_addrs.len()
        invariant
            index <= path_addrs.len(),
            out@ == seq![parent, child]
                + path_addrs@.take(index as int),
        decreases path_addrs.len() - index,
    {
        out.push(path_addrs[index]);
        index += 1;
    }
    proof { assert(path_addrs@.take(index as int) == path_addrs@); }
    out
}

fn compact_destination_addrs(
    node: IAddress,
    path_addrs: &Vec<IAddress>,
) -> (out: Vec<IAddress>)
    ensures out@ == seq![node] + path_addrs@,
{
    let mut out = Vec::<IAddress>::new();
    out.push(node);
    let mut index = 0usize;
    while index < path_addrs.len()
        invariant
            index <= path_addrs.len(),
            out@ == seq![node] + path_addrs@.take(index as int),
        decreases path_addrs.len() - index,
    {
        out.push(path_addrs[index]);
        index += 1;
    }
    proof { assert(path_addrs@.take(index as int) == path_addrs@); }
    out
}

pub open spec fn compactor_views(
    compactors: Seq<CompactorImpl>,
) -> Seq<CompactorInput> {
    Seq::new(compactors.len(), |i: int| compactors[i]@)
}

pub open spec fn compactor_receipt_views(
    compactors: Seq<CompactorImpl>,
) -> Seq<crate::implementation::CachedBranch_v::LoadedBranch> {
    Seq::new(compactors.len(), |i: int| compactors[i].input_nodes@)
}

pub open spec fn compactor_owned_input_aus(
    compactor: CompactorImpl,
    branch_summary: Map<AU, Set<AU>>,
) -> Set<AU> {
    summary_aus(branch_summary.restrict(to_aus(
        Parsedview::<Seq<Address>>::parsedv(&compactor.input_buffers).to_set(),
    )))
}

pub closed spec fn compactor_model_alignment(
    compactors: Seq<CompactorImpl>,
    branch_summary: Map<AU, Set<AU>>,
) -> bool {
    forall |i: int| 0 <= i < compactors.len()
        ==> (#[trigger] compactors[i]).merge is Some ==> {
            let compactor = #[trigger] compactors[i];
            &&& compactor_input_root_aus(compactor)
                <= branch_summary.dom()
            &&& compactor.input_summaries@
                == branch_summary.restrict(
                    compactor_input_root_aus(compactor),
                )
            &&& compactor.input_aus@
                == compactor_owned_input_aus(compactor, branch_summary)
        }
}

fn compactor_refs_are_live(
    compactors: &Vec<CompactorImpl>,
    branch_likes: &AuLikesImpl,
) -> (out: bool)
    requires branch_likes.wf(),
    ensures
        out ==> read_ref_aus(compactor_views(compactors@))
            <= branch_likes@.dom(),
{
    let mut compactor_idx = 0usize;
    while compactor_idx < compactors.len()
        invariant
            branch_likes.wf(),
            compactor_idx <= compactors.len(),
            forall |i: int, j: int|
                #![trigger compactors@[i].input_buffers@[j]]
                0 <= i < compactor_idx
                && 0 <= j < compactors@[i].input_buffers@.len()
                ==> branch_likes@.contains(
                    compactors@[i].input_buffers@[j]@.au,
                ),
        decreases compactors.len() - compactor_idx,
    {
        let mut root_idx = 0usize;
        while root_idx < compactors[compactor_idx].input_buffers.len()
            invariant
                branch_likes.wf(),
                compactor_idx < compactors.len(),
                root_idx <= compactors@[compactor_idx as int]
                    .input_buffers@.len(),
                forall |j: int| 0 <= j < root_idx
                    ==> branch_likes@.contains(
                        (#[trigger] compactors@[compactor_idx as int]
                            .input_buffers@[j])@.au,
                    ),
            decreases compactors@[compactor_idx as int]
                .input_buffers@.len() - root_idx,
        {
            let au = compactors[compactor_idx].input_buffers[root_idx].au;
            if !branch_likes.contains(au) {
                return false;
            }
            root_idx += 1;
        }
        compactor_idx += 1;
    }
    proof {
        assert forall |au: AU|
            #[trigger] read_ref_aus(compactor_views(compactors@)).contains(au)
            implies branch_likes@.dom().contains(au) by {
            let roots = CompactorInput::input_roots(
                compactor_views(compactors@),
            );
            let addr = crate::disk::GenericDisk_v::to_aus_get_addr(
                roots,
                au,
            );
            let root_sets = Seq::new(compactors@.len(), |i: int|
                compactor_views(compactors@)[i].input_buffers.addrs.to_set());
            crate::betree::Utils_v::lemma_union_seq_of_sets_contains(
                root_sets,
                addr,
            );
            let i = choose |i: int| 0 <= i < root_sets.len()
                && (#[trigger] root_sets[i]).contains(addr);
            let j = choose |j: int|
                0 <= j < compactors@[i].input_buffers@.len()
                && #[trigger] compactors@[i].input_buffers@[j]@ == addr;
            assert(compactor_views(compactors@)[i].input_buffers.addrs[j]
                == addr);
            assert(branch_likes@.contains(
                compactors@[i].input_buffers@[j]@.au,
            ));
            assert(addr.au == au);
        }
    }
    true
}

proof fn expose_compactor_model_alignment(
    compactors: Seq<CompactorImpl>,
    branch_summary: Map<AU, Set<AU>>,
)
    requires compactor_model_alignment(compactors, branch_summary),
    ensures forall |i: int| 0 <= i < compactors.len()
        ==> (#[trigger] compactors[i]).merge is Some ==> {
        let compactor = #[trigger] compactors[i];
        &&& compactor_input_root_aus(compactor) <= branch_summary.dom()
        &&& compactor.input_summaries@
            == branch_summary.restrict(compactor_input_root_aus(compactor))
        &&& compactor.input_aus@
            == compactor_owned_input_aus(compactor, branch_summary)
    },
{
    reveal(compactor_model_alignment);
}

proof fn empty_compactor_model_alignment(
    branch_summary: Map<AU, Set<AU>>,
)
    ensures compactor_model_alignment(
        Seq::<CompactorImpl>::empty(),
        branch_summary,
    ),
{
    reveal(compactor_model_alignment);
}

proof fn compactor_model_alignment_push_uninitialized(
    compactors: Seq<CompactorImpl>,
    branch_summary: Map<AU, Set<AU>>,
    compactor: CompactorImpl,
)
    requires
        compactor_model_alignment(compactors, branch_summary),
        compactor.merge is None,
    ensures compactor_model_alignment(
        compactors.push(compactor),
        branch_summary,
    ),
{
    expose_compactor_model_alignment(compactors, branch_summary);
    reveal(compactor_model_alignment);
    assert forall |i: int| 0 <= i < compactors.push(compactor).len()
        implies {
            let current = #[trigger] compactors.push(compactor)[i];
            current.merge is Some ==> {
                &&& compactor_input_root_aus(current) <= branch_summary.dom()
                &&& current.input_summaries@
                    == branch_summary.restrict(
                        compactor_input_root_aus(current),
                    )
                &&& current.input_aus@
                    == compactor_owned_input_aus(current, branch_summary)
            }
        } by {
        if i == compactors.len() {
            assert(compactors.push(compactor)[i] == compactor);
        } else {
            assert(compactors.push(compactor)[i] == compactors[i]);
        }
    }
}

proof fn compactor_model_alignment_update(
    compactors: Seq<CompactorImpl>,
    branch_summary: Map<AU, Set<AU>>,
    index: int,
    compactor: CompactorImpl,
)
    requires
        compactor_model_alignment(compactors, branch_summary),
        0 <= index < compactors.len(),
        compactor.merge is Some ==> {
            &&& compactor_input_root_aus(compactor) <= branch_summary.dom()
            &&& compactor.input_summaries@
                == branch_summary.restrict(
                    compactor_input_root_aus(compactor),
                )
            &&& compactor.input_aus@
                == compactor_owned_input_aus(compactor, branch_summary)
        },
    ensures compactor_model_alignment(
        compactors.update(index, compactor),
        branch_summary,
    ),
{
    expose_compactor_model_alignment(compactors, branch_summary);
    reveal(compactor_model_alignment);
    assert forall |i: int| 0 <= i < compactors.len()
        implies {
            let current = #[trigger] compactors.update(index, compactor)[i];
            current.merge is Some ==> {
                &&& compactor_input_root_aus(current) <= branch_summary.dom()
                &&& current.input_summaries@
                    == branch_summary.restrict(
                        compactor_input_root_aus(current),
                    )
                &&& current.input_aus@
                    == compactor_owned_input_aus(current, branch_summary)
            }
        } by {
        if i == index {
            assert(compactors.update(index, compactor)[i] == compactor);
        } else {
            assert(compactors.update(index, compactor)[i] == compactors[i]);
        }
    }
}

proof fn compactor_model_alignment_insert_unselected(
    compactors: Seq<CompactorImpl>,
    branch_summary: Map<AU, Set<AU>>,
    root: AU,
    summary: Set<AU>,
)
    requires
        compactor_model_alignment(compactors, branch_summary),
        forall |i: int| 0 <= i < compactors.len()
            && (#[trigger] compactors[i]).merge is Some
            ==> !compactor_input_root_aus(compactors[i]).contains(root),
    ensures compactor_model_alignment(
        compactors,
        branch_summary.insert(root, summary),
    ),
{
    expose_compactor_model_alignment(compactors, branch_summary);
    reveal(compactor_model_alignment);
    assert forall |i: int| 0 <= i < compactors.len()
        implies {
            let compactor = #[trigger] compactors[i];
            compactor.merge is Some ==> {
                &&& compactor_input_root_aus(compactor)
                    <= branch_summary.insert(root, summary).dom()
                &&& compactor.input_summaries@
                    == branch_summary.insert(root, summary).restrict(
                        compactor_input_root_aus(compactor),
                    )
                &&& compactor.input_aus@ == compactor_owned_input_aus(
                    compactor,
                    branch_summary.insert(root, summary),
                )
            }
        } by {
        if compactors[i].merge is Some {
            let roots = compactor_input_root_aus(compactors[i]);
            assert_maps_equal!(
                branch_summary.insert(root, summary).restrict(roots),
                branch_summary.restrict(roots),
                candidate => {}
            );
        }
    }
}

proof fn compactor_owned_input_aus_subset_summary(
    compactor: CompactorImpl,
    branch_summary: Map<AU, Set<AU>>,
)
    requires branch_summary.dom().finite(),
    ensures compactor_owned_input_aus(compactor, branch_summary)
        <= summary_aus(branch_summary),
{
    let roots = to_aus(
        Parsedview::<Seq<Address>>::parsedv(
            &compactor.input_buffers,
        ).to_set(),
    );
    let selected = branch_summary.restrict(roots);
    assert(selected.dom() <= branch_summary.dom());
    crate::betree::Utils_v::lemma_subset_finite(
        branch_summary.dom(),
        selected.dom(),
    );
    vstd::map_lib::lemma_values_finite(selected);
    vstd::map_lib::lemma_values_finite(branch_summary);
    assert forall |au: AU| #[trigger] summary_aus(selected).contains(au)
        implies summary_aus(branch_summary).contains(au) by {
        let summary = crate::betree::Utils_v::lemma_union_set_of_sets_contains(
            selected.values(),
            au,
        );
        let root = choose |root: AU| selected.contains_key(root)
            && selected[root] == summary;
        assert(branch_summary.contains_key(root));
        assert(branch_summary[root] == summary);
        assert(branch_summary.values().contains(summary));
        crate::betree::Utils_v::lemma_union_set_of_sets_subset(
            branch_summary.values(),
            summary,
        );
    }
}

proof fn compactor_model_alignment_insert_fresh_summary(
    compactors: Seq<CompactorImpl>,
    branch_summary: Map<AU, Set<AU>>,
    root: AU,
    summary: Set<AU>,
    protected_aus: Set<AU>,
)
    requires
        compactors_wf(compactors),
        compactor_model_alignment(compactors, branch_summary),
        branch_summary.dom().finite(),
        summary_aus(branch_summary) <= protected_aus,
        protected_aus.disjoint(summary),
        summary.contains(root),
    ensures compactor_model_alignment(
        compactors,
        branch_summary.insert(root, summary),
    ),
{
    expose_compactors_wf(compactors);
    expose_compactor_model_alignment(compactors, branch_summary);
    assert forall |i: int| 0 <= i < compactors.len()
        && (#[trigger] compactors[i]).merge is Some
        implies !compactor_input_root_aus(compactors[i]).contains(root) by {
        compactors[i].input_roots_subset_input_aus();
        compactor_owned_input_aus_subset_summary(
            compactors[i],
            branch_summary,
        );
        if compactor_input_root_aus(compactors[i]).contains(root) {
            assert(compactors[i].input_aus@.contains(root));
            assert(summary_aus(branch_summary).contains(root));
            assert(protected_aus.contains(root));
            assert(false);
        }
    }
    compactor_model_alignment_insert_unselected(
        compactors,
        branch_summary,
        root,
        summary,
    );
}

pub closed spec fn compactors_wf(compactors: Seq<CompactorImpl>) -> bool {
    forall |i: int| 0 <= i < compactors.len()
        ==> (#[trigger] compactors[i]).wf()
}

proof fn expose_compactors_wf(compactors: Seq<CompactorImpl>)
    requires compactors_wf(compactors),
    ensures forall |i: int| 0 <= i < compactors.len()
        ==> (#[trigger] compactors[i]).wf(),
{
    reveal(compactors_wf);
}

proof fn compactors_wf_push(
    compactors: Seq<CompactorImpl>,
    compactor: CompactorImpl,
)
    requires
        compactors_wf(compactors),
        compactor.wf(),
    ensures compactors_wf(compactors.push(compactor)),
{
    expose_compactors_wf(compactors);
    reveal(compactors_wf);
    assert forall |i: int| 0 <= i < compactors.push(compactor).len()
        implies (#[trigger] compactors.push(compactor)[i]).wf() by {
        if i == compactors.len() {
            assert(compactors.push(compactor)[i] == compactor);
        } else {
            assert(compactors.push(compactor)[i] == compactors[i]);
        }
    }
}

proof fn compactors_wf_update(
    compactors: Seq<CompactorImpl>,
    index: int,
    compactor: CompactorImpl,
)
    requires
        compactors_wf(compactors),
        0 <= index < compactors.len(),
        compactor.wf(),
    ensures compactors_wf(compactors.update(index, compactor)),
{
    expose_compactors_wf(compactors);
    reveal(compactors_wf);
    assert forall |i: int| 0 <= i < compactors.len()
        implies (#[trigger] compactors.update(index, compactor)[i]).wf() by {
        if i == index {
            assert(compactors.update(index, compactor)[i] == compactor);
        } else {
            assert(compactors.update(index, compactor)[i] == compactors[i]);
        }
    }
}

proof fn compactors_wf_remove(
    compactors: Seq<CompactorImpl>,
    index: int,
)
    requires
        compactors_wf(compactors),
        0 <= index < compactors.len(),
    ensures compactors_wf(compactors.remove(index)),
{
    expose_compactors_wf(compactors);
    reveal(compactors_wf);
    assert forall |i: int| 0 <= i < compactors.remove(index).len()
        implies (#[trigger] compactors.remove(index)[i]).wf() by {
        if i < index {
            assert(compactors.remove(index)[i] == compactors[i]);
        } else {
            assert(compactors.remove(index)[i] == compactors[i + 1]);
        }
    }
}

proof fn component_reclaims_compose(
    betree_deallocs: Set<AU>,
    branch_deallocs: Set<AU>,
    betree_persistent: Set<AU>,
    betree_frozen: Set<AU>,
    branch_persistent: Set<AU>,
    branch_frozen: Set<AU>,
    betree_reclaimed: Set<AU>,
    branch_reclaimed: Set<AU>,
)
    requires
        betree_deallocs.disjoint(branch_deallocs),
        betree_deallocs.disjoint(
            branch_persistent + branch_frozen,
        ),
        branch_deallocs.disjoint(
            betree_persistent + betree_frozen,
        ),
        betree_reclaimed =~= betree_deallocs
            - betree_persistent - betree_frozen,
        branch_reclaimed =~= branch_deallocs
            - branch_persistent - branch_frozen,
    ensures
        betree_reclaimed + branch_reclaimed
            =~= (betree_deallocs + branch_deallocs)
                - (betree_persistent + branch_persistent)
                - (betree_frozen + branch_frozen),
{
    let protected = (betree_persistent + branch_persistent)
        + (betree_frozen + branch_frozen);
    let all_deallocs = betree_deallocs + branch_deallocs;
    assert_sets_equal!(
        betree_reclaimed + branch_reclaimed,
        all_deallocs - protected,
        au => {
            if (betree_reclaimed + branch_reclaimed).contains(au) {
                if betree_reclaimed.contains(au) {
                    assert(betree_deallocs.contains(au));
                    assert(!branch_persistent.contains(au));
                    assert(!branch_frozen.contains(au));
                } else {
                    assert(branch_reclaimed.contains(au));
                    assert(branch_deallocs.contains(au));
                    assert(!betree_persistent.contains(au));
                    assert(!betree_frozen.contains(au));
                }
            } else if (all_deallocs - protected).contains(au) {
                if betree_deallocs.contains(au) {
                    assert(!branch_deallocs.contains(au));
                    assert(!betree_persistent.contains(au));
                    assert(!betree_frozen.contains(au));
                    assert(betree_reclaimed.contains(au));
                } else {
                    assert(branch_deallocs.contains(au));
                    assert(!branch_persistent.contains(au));
                    assert(!branch_frozen.contains(au));
                    assert(branch_reclaimed.contains(au));
                }
            }
        }
    );
}

proof fn ownership_reclaims_compose(
    ownership: BranchBetreeOwnershipImpl,
    betree_deallocs: Set<AU>,
    branch_deallocs: Set<AU>,
    betree_reclaimed: Set<AU>,
    branch_reclaimed: Set<AU>,
)
    requires
        ownership.wf(),
        betree_deallocs <= ownership.betree.active_aus(),
        branch_deallocs <= ownership.branches.active_summary_aus(),
        betree_reclaimed =~= betree_deallocs
            - ownership.betree.persistent_aus()
            - ownership.betree.frozen_aus(),
        branch_reclaimed =~= branch_deallocs
            - ownership.branches.persistent_aus()
            - ownership.branches.frozen_aus(),
    ensures
        betree_reclaimed.disjoint(branch_reclaimed),
        betree_reclaimed + branch_reclaimed
            =~= (betree_deallocs + branch_deallocs)
                - ownership.persistent_aus()
                - ownership.frozen_aus(),
{
    ownership.betree.ownership_sets_bounded();
    ownership.branches.ownership_sets_bounded();
    assert(betree_deallocs.disjoint(branch_deallocs));
    assert(betree_deallocs.disjoint(
        ownership.branches.persistent_aus()
            + ownership.branches.frozen_aus(),
    ));
    assert(branch_deallocs.disjoint(
        ownership.betree.persistent_aus()
            + ownership.betree.frozen_aus(),
    ));
    component_reclaims_compose(
        betree_deallocs,
        branch_deallocs,
        ownership.betree.persistent_aus(),
        ownership.betree.frozen_aus(),
        ownership.branches.persistent_aus(),
        ownership.branches.frozen_aus(),
        betree_reclaimed,
        branch_reclaimed,
    );
    assert(betree_reclaimed.disjoint(branch_reclaimed));
}

#[derive(Debug)]
pub enum BranchBetreeControlResult {
    Applied,
    Noop,
}

pub enum BranchBetreeRecoveryStepResult {
    NeedCacheLoad { addr: IAddress, handle: MutHandle },
    Advanced {
        label: Ghost<BetreeMetadataRecoveryLabel>,
        reads: Ghost<Map<Address, RawPage>>,
    },
    Complete,
    CacheFull,
    Blocked,
    InvalidPage,
}

pub enum BranchBetreePutResult {
    Applied,
    Noop,
}

pub enum BranchBetreeWipResult {
    Applied { idx: usize },
    Noop,
}

pub enum BranchBetreeAbortResult {
    Aborted { deallocs: Vec<IAU> },
}

pub enum BranchBetreeBuildResult {
    Applied {
        idx: usize,
        prepared_cache: Ghost<Cache::State>,
        access: Ghost<PageAccess>,
        event: Ghost<CachedBulkBranchEvent>,
    },
    NeedsAUs,
    CacheFull,
    Blocked,
    InvalidPage,
}

pub enum BranchBetreeBulkStartResult {
    Started { idx: usize },
    Empty,
    Overflow,
    InvalidCapacity,
    Blocked,
}

pub enum BranchBetreeBulkSealResult {
    Sealed {
        idx: usize,
        root: IAddress,
        aux_ptr: Option<IAddress>,
        prepared_cache: Ghost<Cache::State>,
        access: Ghost<PageAccess>,
        event: Ghost<CachedBulkBranchEvent>,
        deallocs: Vec<IAU>,
        branch: Ghost<crate::betree::LinkedBranch_v::LinkedBranch<
            crate::allocation_layer::BranchTypes_v::Summary,
        >>,
    },
    NeedsAUs,
    CacheFull,
    Blocked,
    InvalidPage,
}

pub enum BranchBetreeFlushResult {
    Flushed {
        new_root: IAddress,
        prepared_cache: Ghost<Cache::State>,
        access: Ghost<PageAccess>,
        allocs: Ghost<Set<AU>>,
        deallocs: Ghost<Set<AU>>,
    },
    CacheFull,
    Blocked,
    InvalidPage,
}

pub enum BranchBetreeExistingFlushResult {
    Flushed {
        new_root: IAddress,
        reclaimed: Vec<IAU>,
        prepared_cache: Ghost<Cache::State>,
        access: Ghost<PageAccess>,
        allocs: Ghost<Set<AU>>,
        deallocs: Ghost<Set<AU>>,
    },
    NeedCacheLoad { addr: IAddress, handle: MutHandle },
    CacheFull,
    Blocked,
    InvalidPage,
}

pub enum BranchBetreeGrowResult {
    Grew {
        new_root: IAddress,
        prepared_cache: Ghost<Cache::State>,
        access: Ghost<PageAccess>,
        allocs: Ghost<Set<AU>>,
    },
    CacheFull,
    Blocked,
    InvalidPage,
}

pub enum BranchBetreeCompactBeginResult {
    Began {
        input_idx: usize,
        access: Ghost<PageAccess>,
    },
    NeedCacheLoad { addr: IAddress, handle: MutHandle },
    Stale,
    CacheFull,
    Blocked,
    InvalidPage,
}

pub enum BranchBetreeCompactAbortResult {
    Aborted { deallocs: Ghost<Set<AU>> },
    Noop,
}

pub enum BranchBetreeCompactStreamResult {
    ReadAdvanced { reads: Ghost<Map<Address, RawPage>> },
    ItemAccepted,
    PageReady,
    Skipped,
    Done,
    NeedCacheLoad { addr: IAddress, handle: MutHandle },
    CacheFull,
    Blocked,
    InvalidPage,
}

pub enum BranchBetreeCompactCompleteResult {
    Completed {
        new_root: IAddress,
        betree_reclaimed: Vec<IAU>,
        branch_reclaimed: Vec<IAU>,
        prepared_cache: Ghost<Cache::State>,
        access: Ghost<PageAccess>,
        allocs: Ghost<Set<AU>>,
        deallocs: Ghost<Set<AU>>,
    },
    NeedCacheLoad { addr: IAddress, handle: MutHandle },
    Stale,
    CacheFull,
    Blocked,
    InvalidPage,
}

pub enum BranchBetreeSplitResult {
    Split {
        new_root: IAddress,
        reclaimed: Vec<IAU>,
        prepared_cache: Ghost<Cache::State>,
        access: Ghost<PageAccess>,
        allocs: Ghost<Set<AU>>,
        deallocs: Ghost<Set<AU>>,
    },
    NeedCacheLoad { addr: IAddress, handle: MutHandle },
    CacheFull,
    Blocked,
    InvalidPage,
}

pub enum BranchBetreeChildFlushResult {
    Flushed {
        new_root: IAddress,
        betree_reclaimed: Vec<IAU>,
        branch_reclaimed: Vec<IAU>,
        prepared_cache: Ghost<Cache::State>,
        access: Ghost<PageAccess>,
        allocs: Ghost<Set<AU>>,
        deallocs: Ghost<Set<AU>>,
    },
    NeedCacheLoad { addr: IAddress, handle: MutHandle },
    CacheFull,
    Blocked,
    InvalidPage,
}

pub enum BranchBetreeQueryResult {
    Hit {
        value: Value,
        access: Ghost<PageAccess>,
    },
    NeedCacheLoad { addr: IAddress, handle: MutHandle },
    CacheFull,
    Blocked,
    InvalidPage,
}

pub enum BranchBetreeCommitResult {
    Applied,
    Noop,
}

pub enum BranchBetreeCommitCompleteResult {
    Applied { reclaimed: Vec<IAU> },
    Noop,
}

impl BranchBetreeControlImpl {
    pub open spec fn wf(&self) -> bool {
        &&& self.metadata.wf()
        &&& match self.frozen_metadata {
            Some(metadata) => metadata.wf(),
            None => true,
        }
        &&& self.loading ==> self.installed && !self.metadata_loaded
        &&& self.metadata_loaded ==> self.installed && !self.loading
    }
}

pub struct BranchBetreeImpl {
    pub root: Option<IAddress>,
    pub ownership: BranchBetreeOwnershipImpl,
    pub branch_likes: AuLikesImpl,
    pub memtable: MemtableImpl,
    pub recovery: BetreeRecoveryImpl,
    pub wip_branches: Vec<BulkBranchImpl>,
    pub compactors: Vec<CompactorImpl>,
    pub control: BranchBetreeControlImpl,
}

impl BranchBetreeImpl {
    pub open spec fn root_wf(&self) -> bool {
        match self.root {
            Some(root) => root@.wf(),
            None => true,
        }
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.root_wf()
        &&& self.ownership.wf()
        &&& self.branch_likes.wf()
        &&& self.memtable.wf()
        &&& bulk_branches_wf(self.wip_branches@)
        &&& bulk_builders_wf(
            self.wip_branches@,
            &self.memtable,
        )
        &&& compactors_wf(self.compactors@)
        &&& compactor_model_alignment(
            self.compactors@,
            self.ownership.branches.active_summary_map(),
        )
        &&& self.control.wf()
        &&& !self.control.metadata_loaded
            ==> self.betree_i() == empty_cached_betree()
        &&& self.control.loading ==> {
            &&& self.recovery.wf()
            &&& iopt_addr(self.recovery.root)
                == self.control.metadata@.root
            &&& self.control.frozen_metadata is None
            &&& self.recovery.ownership.betree.active.bucket_count
                == self.ownership.betree.active.bucket_count
            &&& self.recovery.branch_likes.bucket_count
                == self.branch_likes.bucket_count
        }
        &&& self.ownership.betree.active.bucket_count
            == self.ownership.branches.active.bucket_count
        &&& self.ownership.betree.active.bucket_count
            == self.branch_likes.bucket_count
        &&& self.branch_likes@.dom()
            == self.ownership.branches.active_summary_map().dom()
        &&& self.ownership.current_durable_aus()
            == self.betree_i().durable_aus()
        &&& self.control.frozen_metadata is None
            ==> self.ownership.frozen_aus().is_empty()
    }

    pub open spec fn query_cache_inv(&self, cache: Cache::State) -> bool {
        self.root is Some ==> forall |key: Key|
            cached_betree_query_valid(
                cache,
                self.root.unwrap()@,
                key,
                CACHE_SIZE_RECS as nat,
                CACHE_SIZE_RECS as nat,
                self.ownership.betree.active_aus(),
                self.ownership.branches.active_summary_map(),
                self.ownership.branches.active_summary_aus(),
            )
    }

    pub open spec fn same_exec_state(&self, other: &Self) -> bool {
        &&& self.root == other.root
        &&& self.ownership == other.ownership
        &&& self.branch_likes@ == other.branch_likes@
        &&& self.memtable == other.memtable
        &&& self.recovery == other.recovery
        &&& self.wip_branches@ == other.wip_branches@
        &&& self.compactors@ == other.compactors@
        &&& self.control == other.control
    }

    pub proof fn compactor_wf_ensures(&self, idx: int)
        requires
            self.wf(),
            0 <= idx < self.compactors@.len(),
        ensures
            self.compactors@[idx].wf(),
    {
        expose_compactors_wf(self.compactors@);
    }

    pub proof fn compactor_input_aus_subset_active(&self, idx: int)
        requires
            self.wf(),
            0 <= idx < self.compactors@.len(),
            self.compactors@[idx].merge is Some,
        ensures
            self.compactors@[idx].wf(),
            self.compactors@[idx].merge->0.wf(),
            self.compactors@[idx].merge->0.source_aus()
                <= self.compactors@[idx].input_aus@,
            self.compactors@[idx].input_aus@
                <= self.ownership.branches.active_summary_aus(),
    {
        expose_compactors_wf(self.compactors@);
        expose_compactor_model_alignment(
            self.compactors@,
            self.ownership.branches.active_summary_map(),
        );
        self.ownership.branches.active_summary_projection();
        compactor_owned_input_aus_subset_summary(
            self.compactors@[idx],
            self.ownership.branches.active_summary_map(),
        );
    }

    pub open spec fn frozen_i(&self) -> Option<FrozenCachingDiskBranchBetree> {
        match self.control.frozen_metadata {
            Some(metadata) => Some(FrozenCachingDiskBranchBetree {
                metadata: metadata@,
                aus: self.ownership.frozen_aus(),
            }),
            None => None,
        }
    }

    pub open spec fn betree_i(&self) -> CachedBranchBetree::State {
        CachedBranchBetree::State {
            root: iopt_addr(self.root),
            memtable: self.memtable@,
            betree_aus: self.ownership.betree@,
            branch_aus: self.branch_likes@,
            branch_summary: self.ownership.branches@,
            compactors: compactor_views(self.compactors@),
            compactor_receipts: compactor_receipt_views(self.compactors@),
            wip_branches: bulk_branch_views(self.wip_branches@),
        }
    }

    pub open spec fn control_i(&self) -> AtomicBranchBetreeControl {
        AtomicBranchBetreeControl {
            metadata: self.control.metadata@,
            recovery: self.recovery@,
            persistent_aus: self.ownership.persistent_aus(),
            installed: self.control.installed,
            loading: self.control.loading,
            metadata_loaded: self.control.metadata_loaded,
            frozen: self.frozen_i(),
        }
    }

    pub proof fn protected_aus_match_ownership(&self)
        requires self.wf(),
        ensures
            self.control_i().protected_aus()
                =~= self.ownership.persistent_aus()
                    + self.ownership.frozen_aus(),
    {
        if self.control.frozen_metadata is Some {
            assert(self.control_i().frozen.unwrap().aus
                == self.ownership.frozen_aus());
        } else {
            assert(self.ownership.frozen_aus().is_empty());
        }
    }

    pub open spec fn i(&self) -> AtomicBranchBetreeState::State {
        AtomicBranchBetreeState::State {
            betree: self.betree_i(),
            control: self.control_i(),
        }
    }

    pub fn exec_seq_end(&self) -> (out: u64)
        requires self.wf(),
        ensures out as nat == self@.betree.memtable.seq_end,
    {
        self.memtable.seq_end
    }

    pub fn recovered_durable_aus(&self) -> (out: Vec<IAU>)
        requires
            self.wf(),
            self.control.loading,
            self.recovery.completion_matches(self.control.metadata@),
        ensures
            unique_iau_seq(out@),
            iau_seq_set(out@)
                =~= self.recovery@.loaded_betree(
                    self.control.metadata@,
                ).durable_aus(),
    {
        let out = self.recovery.ownership.current_durable_aus_vec();
        proof {
            assert(self.recovery.ownership.current_durable_aus()
                =~= self.recovery.ownership.persistent_aus()) by {
                assert forall |au: AU|
                    #![trigger self.recovery.ownership
                        .current_durable_aus().contains(au)]
                    self.recovery.ownership.current_durable_aus().contains(au)
                    == self.recovery.ownership.persistent_aus()
                        .contains(au) by { }
            }
        }
        out
    }

    pub fn frozen_aus_vec(&self) -> (out: Vec<IAU>)
        requires
            self.wf(),
            self.control.frozen_metadata is Some,
            self.ownership.frozen_aus()
                == self.ownership.current_durable_aus(),
        ensures
            unique_iau_seq(out@),
            iau_seq_set(out@) =~= self.ownership.frozen_aus(),
    {
        self.ownership.current_durable_aus_vec()
    }

    pub fn new(
        ownership_bucket_count: u32,
        memtable_bucket_count: u32,
    ) -> (out: Self)
        requires
            ownership_bucket_count > 0,
            memtable_bucket_count > 0,
        ensures
            out.wf(),
            out@ == AtomicBranchBetreeState::State::empty(),
            out.wip_branches@.len() == 0,
            out.compactors@.len() == 0,
            out.ownership.betree.all_aus().is_empty(),
            out.ownership.branches.all_summary_aus().is_empty(),
    {
        let metadata = BetreeMetadataImpl::empty();
        let recovery = BetreeRecoveryImpl::start(
            metadata.root,
            metadata.seq_end,
            ownership_bucket_count,
        );
        let ownership = BranchBetreeOwnershipImpl::new(ownership_bucket_count);
        let branch_likes = AuLikesImpl::new(ownership_bucket_count);
        let memtable = MemtableImpl::new(memtable_bucket_count, 0);
        let control = BranchBetreeControlImpl {
            metadata,
            installed: false,
            loading: false,
            metadata_loaded: false,
            frozen_metadata: None,
        };
        let out = Self {
            root: None,
            ownership,
            branch_likes,
            memtable,
            recovery,
            wip_branches: Vec::new(),
            compactors: Vec::new(),
            control,
        };
        proof {
            empty_compactor_model_alignment(
                out.ownership.branches.active_summary_map(),
            );
            assert(out.control.wf());
            assert(out.branch_likes@.dom() =~= Set::<AU>::empty());
            assert(out.ownership.betree@ == AULikes::empty());
            assert(out.ownership.branches@
                == Map::<AU, crate::allocation_layer::BranchTypes_v::Summary>::empty());
            assert(out.ownership.branches.active_summary_map().dom()
                =~= Set::<AU>::empty());
            empty_recovery_likes_are_empty();
            assert(out.betree_i() == empty_cached_betree());
            assert(out.ownership.current_durable_aus().is_empty());
            assert(out.betree_i().durable_aus().is_empty()) by {
                assert(out.betree_i().betree_aus.dom().is_empty());
                assert(out.betree_i().branch_aus.dom().is_empty());
                assert(out.betree_i().branch_summary.is_empty());
                assert(summary_aus(out.betree_i().branch_summary).is_empty()) by {
                    assert(out.betree_i().branch_summary.values().is_empty());
                    assert(out.betree_i().branch_summary.values().finite());
                    assert(out.betree_i().branch_summary.values().len() == 0);


                }

            }
            assert(out.wf());
            assert(out.control_i() == AtomicBranchBetreeControl::empty());
        }
        out
    }

    pub fn initialize_from_metadata(
        &mut self,
        metadata: BetreeMetadataImpl,
    )
        requires
            old(self).wf(),
            old(self)@ == AtomicBranchBetreeState::State::empty(),
            metadata.wf(),
        ensures
            self.wf(),
            self.control.metadata@ == metadata@,
            self.control.installed,
            !self.control.loading,
            !self.control.metadata_loaded,
            self.control.frozen_metadata is None,
            self.compactors@ == old(self).compactors@,
            self.ownership.betree.all_aus()
                == old(self).ownership.betree.all_aus(),
            self.ownership.branches.all_summary_aus()
                == old(self).ownership.branches.all_summary_aus(),
            self.root == old(self).root,
            self.ownership == old(self).ownership,
            self.branch_likes == old(self).branch_likes,
            self.memtable == old(self).memtable,
            self.wip_branches@ == old(self).wip_branches@,
            self.wip_branches@.len() == 0,
            self.control.metadata_loaded
                == old(self).control.metadata_loaded,
            self.control.frozen_metadata
                == old(self).control.frozen_metadata,
            AtomicBranchBetreeState::State::init_by(
                self@,
                AtomicBranchBetreeState::Config::initialize(metadata@),
            ),
    {
        let recovery = BetreeRecoveryImpl::start(
            metadata.root,
            metadata.seq_end,
            self.ownership.betree.active.bucket_count,
        );
        self.recovery = recovery;
        self.control = BranchBetreeControlImpl {
            metadata,
            installed: true,
            loading: false,
            metadata_loaded: false,
            frozen_metadata: None,
        };
        proof {
            assert(self.control.wf());
            assert(old(self).wip_branches@.len() == 0) by {
                assert(old(self).betree_i() == empty_cached_betree());
                assert(old(self).betree_i().wip_branches.len() == 0);
                assert(bulk_branch_views(old(self).wip_branches@).len()
                    == old(self).wip_branches@.len());
            }
            assert(self.compactors@.len() == 0) by {
                assert(old(self).betree_i() == empty_cached_betree());
                assert(old(self).betree_i().compactors.len() == 0);
                assert(compactor_views(old(self).compactors@).len()
                    == old(self).compactors@.len());
            }
            assert(self.compactors@ == Seq::<CompactorImpl>::empty());
            empty_compactor_model_alignment(
                self.ownership.branches.active_summary_map(),
            );
            assert(self.wf());
            reveal(AtomicBranchBetreeState::State::init_by);
        }
    }

    pub fn recovery_begin(&mut self) -> (result: BranchBetreeControlResult)
        requires old(self).wf(),
        ensures
            self.wf(),
            self.compactors@ == old(self).compactors@,
            self.ownership.betree.all_aus()
                == old(self).ownership.betree.all_aus(),
            self.ownership.branches.all_summary_aus()
                == old(self).ownership.branches.all_summary_aus(),
            self.root == old(self).root,
            self.ownership == old(self).ownership,
            self.branch_likes == old(self).branch_likes,
            self.memtable == old(self).memtable,
            self.wip_branches@ == old(self).wip_branches@,
            self.control.metadata == old(self).control.metadata,
            self.control.installed == old(self).control.installed,
            self.control.metadata_loaded
                == old(self).control.metadata_loaded,
            self.control.frozen_metadata
                == old(self).control.frozen_metadata,
            (result is Applied) <==>
                old(self).control.installed
                    && !old(self).control.loading
                    && !old(self).control.metadata_loaded
                    && old(self).control.frozen_metadata is None,
            match result {
                BranchBetreeControlResult::Applied => {
                    AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::Internal,
                    )
                },
                BranchBetreeControlResult::Noop => self@ == old(self)@,
            },
    {
        if !self.control.installed
            || self.control.loading
            || self.control.metadata_loaded
            || self.control.frozen_metadata.is_some()
        {
            return BranchBetreeControlResult::Noop;
        }
        let recovery = BetreeRecoveryImpl::start(
            self.control.metadata.root,
            self.control.metadata.seq_end,
            self.ownership.betree.active.bucket_count,
        );
        self.recovery = recovery;
        self.control.loading = true;
        proof {
            assert(self.control.wf());
            assert(self.recovery.ownership.betree.active.bucket_count
                == self.ownership.betree.active.bucket_count);
            assert(self.wf());
            assert(AtomicBranchBetreeState::State::next_by(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::Internal,
                AtomicBranchBetreeState::Step::recovery_begin(),
            )) by {
                reveal(AtomicBranchBetreeState::State::next_by);
            }
            assert(AtomicBranchBetreeState::State::next(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::Internal,
            )) by {
                reveal(AtomicBranchBetreeState::State::next);
            }
        }
        BranchBetreeControlResult::Applied
    }

    pub fn recover_metadata_step(
        &mut self,
        cache: &mut FracCacheImpl,
    ) -> (result: BranchBetreeRecoveryStepResult)
        requires
            old(self).wf(),
            old(self).control.loading,
            old(cache).wf(),
        ensures
            self.wf(),
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            self.compactors@ == old(self).compactors@,
            self.wip_branches@ == old(self).wip_branches@,
            self.ownership.betree.all_aus()
                == old(self).ownership.betree.all_aus(),
            self.ownership.branches.all_summary_aus()
                == old(self).ownership.branches.all_summary_aus(),
            self.root == old(self).root,
            self.ownership == old(self).ownership,
            self.branch_likes == old(self).branch_likes,
            self.memtable == old(self).memtable,
            self.control == old(self).control,
            match result {
                BranchBetreeRecoveryStepResult::NeedCacheLoad { addr, handle } => {
                    &&& self@ == old(self)@
                    &&& addr@ != spec_superblock_addr()
                    &&& cache.entry_fetched(&addr)
                    &&& cache.valid_load_handle(&addr, handle)
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        crate::implementation::FracCacheImpl_v::cache_load_label(&addr),
                    )
                },
                BranchBetreeRecoveryStepResult::Advanced { label, reads } => {
                    let access = recovery_page_access(label@);
                    &&& AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::RecoveryAccess{access},
                    )
                    &&& reads@ == access.reads()
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        Cache::Label::Access {
                            reads: access.reads(),
                            writes: access.writes(),
                        },
                    )
                },
                BranchBetreeRecoveryStepResult::Complete => {
                    &&& self@ == old(self)@
                    &&& cache@ == old(cache)@
                    &&& self.recovery@.complete()
                },
                BranchBetreeRecoveryStepResult::CacheFull
                | BranchBetreeRecoveryStepResult::Blocked
                | BranchBetreeRecoveryStepResult::InvalidPage => {
                    &&& self@ == old(self)@
                    &&& cache@ == old(cache)@
                },
            },
    {
        let need = self.recovery.next_need();
        let ghost cache0 = *cache;
        match need {
            BetreeRecoveryNeed::Complete => {
                return BranchBetreeRecoveryStepResult::Complete;
            },
            BetreeRecoveryNeed::Betree { addr } => {
                if addr.au == 0 && addr.page == 0 {
                    return BranchBetreeRecoveryStepResult::InvalidPage;
                }
                match cache.fetch(&addr, true) {
                    FetchErrorCode::LoadInitiate { slot_handle } => {
                        return BranchBetreeRecoveryStepResult::NeedCacheLoad {
                            addr,
                            handle: slot_handle,
                        };
                    },
                    FetchErrorCode::Success { slot_handle } => {
                        let ghost raw = slot_handle.rec@;
                        let ghost slot = slot_handle.idx;
                        let fmt = BetreeNodePageFmt::new();
                        let all_slice = Slice::all(&slot_handle.rec);
                        let parsed = fmt.try_parse(&all_slice, &slot_handle.rec);
                        proof {
                            if parsed is Some {
                                assert(fmt == BetreeNodePageFmt::spec_new());
                                assert(all_slice@.i(slot_handle.rec@) == slot_handle.rec@);
                                assert(fmt.parsable(raw));
                                assert(parsed.unwrap().parsedv() == fmt.parse(raw));
                                assert(raw_page_to_betree_node(raw) == parsed.unwrap()@);
                            }
                        }
                        cache.handle_release(&addr, slot_handle);
                        proof {
                            assert(cache@.entries == cache0@.entries);
                            assert(cache@.lookup_map == cache0@.lookup_map);
                            assert(cache@.status_map == cache0@.status_map);
                            assert(cache@ == cache0@);
                        }
                        let node = match parsed {
                            Some(node) => node,
                            None => return BranchBetreeRecoveryStepResult::InvalidPage,
                        };
                        let ghost old_recovery = self.recovery@;
                        match self.recovery.read_betree(addr, node) {
                            BetreeRecoveryApplyResult::Applied => {
                                let ghost reads = map![addr@ => raw];
                                let ghost label = BetreeMetadataRecoveryLabel::ReadBetree {
                                    addr: addr@,
                                    reads,
                                };
                                proof {
                                    assert(to_betree_nodes(reads)[addr@]
                                        == raw_page_to_betree_node(raw));
                                    assert(self.recovery@
                                        == old_recovery.read_betree(
                                            addr@,
                                            raw_page_to_betree_node(raw),
                                        ));
                                    assert(BetreeMetadataRecoveryCore::next(
                                        old_recovery,
                                        self.recovery@,
                                        label,
                                    )) by {

                                    }
                                    assert(self.wf());

                                    Cache::State::access_read_only_from_valid_reads(
                                        cache0@,
                                        reads,
                                    );
                                    let access = recovery_page_access(label);
                                    assert(access.reads() == reads);
                                    assert(access.writes()
                                        == Map::<Address, RawPage>::empty());
                                    assert(AtomicBranchBetreeState::State::recover(
                                        old(self)@,
                                        self@,
                                        AtomicBranchBetreeState::Label::RecoveryAccess{access},
                                        self.recovery@,
                                        label,
                                    ));
                                    assert(AtomicBranchBetreeState::State::next_by(
                                        old(self)@,
                                        self@,
                                        AtomicBranchBetreeState::Label::RecoveryAccess{access},
                                        AtomicBranchBetreeState::Step::recover(
                                            self.recovery@,
                                            label,
                                        ),
                                    )) by {
                                        reveal(AtomicBranchBetreeState::State::next_by);
                                    }
                                    assert(AtomicBranchBetreeState::State::next(
                                        old(self)@,
                                        self@,
                                        AtomicBranchBetreeState::Label::RecoveryAccess{access},
                                    )) by {
                                        reveal(AtomicBranchBetreeState::State::next);
                                    }
                                    assert(Cache::State::next(
                                        cache0@,
                                        cache@,
                                        Cache::Label::Access {
                                            reads: access.reads(),
                                            writes: access.writes(),
                                        },
                                    ));
                                }
                                return BranchBetreeRecoveryStepResult::Advanced {
                                    label: Ghost(label),
                                    reads: Ghost(reads),
                                };
                            },
                            BetreeRecoveryApplyResult::Invalid => {
                                return BranchBetreeRecoveryStepResult::InvalidPage;
                            },
                        }
                    },
                    FetchErrorCode::CacheFull => {
                        return BranchBetreeRecoveryStepResult::CacheFull;
                    },
                    FetchErrorCode::Awaiting | FetchErrorCode::NotPresent => {
                        return BranchBetreeRecoveryStepResult::Blocked;
                    },
                }
            },
            BetreeRecoveryNeed::BranchRoot { root } => {
                if root.au == 0 && root.page == 0 {
                    return BranchBetreeRecoveryStepResult::InvalidPage;
                }
                match cache.fetch(&root, true) {
                    FetchErrorCode::LoadInitiate { slot_handle } => {
                        return BranchBetreeRecoveryStepResult::NeedCacheLoad {
                            addr: root,
                            handle: slot_handle,
                        };
                    },
                    FetchErrorCode::Success { slot_handle } => {
                        let ghost raw = slot_handle.rec@;
                        let fmt = BranchNodePageFmt::new();
                        let all_slice = Slice::all(&slot_handle.rec);
                        let parsed = fmt.try_parse(&all_slice, &slot_handle.rec);
                        proof {
                            if parsed is Some {
                                assert(fmt == BranchNodePageFmt::spec_new());
                                assert(all_slice@.i(slot_handle.rec@) == slot_handle.rec@);
                                assert(fmt.parsable(raw));
                                assert(parsed.unwrap().parsedv() == fmt.parse(raw));
                                assert(raw_page_to_branch_node(raw) == parsed.unwrap()@);
                            }
                        }
                        cache.handle_release(&root, slot_handle);
                        proof {
                            assert(cache@.entries == cache0@.entries);
                            assert(cache@.lookup_map == cache0@.lookup_map);
                            assert(cache@.status_map == cache0@.status_map);
                            assert(cache@ == cache0@);
                        }
                        let node = match parsed {
                            Some(node) => node,
                            None => return BranchBetreeRecoveryStepResult::InvalidPage,
                        };
                        let ghost old_recovery = self.recovery@;
                        match self.recovery.read_branch_root(root, node) {
                            BetreeRecoveryApplyResult::Applied => {
                                let ghost reads = map![root@ => raw];
                                let ghost label = BetreeMetadataRecoveryLabel::ReadBranchRoot {
                                    root: root@,
                                    reads,
                                };
                                proof {
                                    assert(to_branch_nodes(reads)[root@]
                                        == raw_page_to_branch_node(raw));
                                    assert(BetreeMetadataRecoveryCore::next(
                                        old_recovery,
                                        self.recovery@,
                                        label,
                                    )) by {

                                    }
                                    assert(self.wf());

                                    Cache::State::access_read_only_from_valid_reads(
                                        cache0@,
                                        reads,
                                    );
                                    let access = recovery_page_access(label);
                                    assert(access.reads() == reads);
                                    assert(access.writes()
                                        == Map::<Address, RawPage>::empty());
                                    assert(AtomicBranchBetreeState::State::recover(
                                        old(self)@,
                                        self@,
                                        AtomicBranchBetreeState::Label::RecoveryAccess{access},
                                        self.recovery@,
                                        label,
                                    ));
                                    assert(AtomicBranchBetreeState::State::next_by(
                                        old(self)@,
                                        self@,
                                        AtomicBranchBetreeState::Label::RecoveryAccess{access},
                                        AtomicBranchBetreeState::Step::recover(
                                            self.recovery@,
                                            label,
                                        ),
                                    )) by {
                                        reveal(AtomicBranchBetreeState::State::next_by);
                                    }
                                    assert(AtomicBranchBetreeState::State::next(
                                        old(self)@,
                                        self@,
                                        AtomicBranchBetreeState::Label::RecoveryAccess{access},
                                    )) by {
                                        reveal(AtomicBranchBetreeState::State::next);
                                    }
                                    assert(Cache::State::next(
                                        cache0@,
                                        cache@,
                                        Cache::Label::Access {
                                            reads: access.reads(),
                                            writes: access.writes(),
                                        },
                                    ));
                                }
                                return BranchBetreeRecoveryStepResult::Advanced {
                                    label: Ghost(label),
                                    reads: Ghost(reads),
                                };
                            },
                            BetreeRecoveryApplyResult::Invalid => {
                                return BranchBetreeRecoveryStepResult::InvalidPage;
                            },
                        }
                    },
                    FetchErrorCode::CacheFull => {
                        return BranchBetreeRecoveryStepResult::CacheFull;
                    },
                    FetchErrorCode::Awaiting | FetchErrorCode::NotPresent => {
                        return BranchBetreeRecoveryStepResult::Blocked;
                    },
                }
            },
            BetreeRecoveryNeed::BranchAux { root, aux } => {
                if aux.au == 0 && aux.page == 0 {
                    return BranchBetreeRecoveryStepResult::InvalidPage;
                }
                match cache.fetch(&aux, true) {
                    FetchErrorCode::LoadInitiate { slot_handle } => {
                        return BranchBetreeRecoveryStepResult::NeedCacheLoad {
                            addr: aux,
                            handle: slot_handle,
                        };
                    },
                    FetchErrorCode::Success { slot_handle } => {
                        let ghost raw = slot_handle.rec@;
                        let fmt = BranchNodePageFmt::new();
                        let all_slice = Slice::all(&slot_handle.rec);
                        let parsed = fmt.try_parse(&all_slice, &slot_handle.rec);
                        proof {
                            if parsed is Some {
                                assert(fmt == BranchNodePageFmt::spec_new());
                                assert(all_slice@.i(slot_handle.rec@) == slot_handle.rec@);
                                assert(fmt.parsable(raw));
                                assert(parsed.unwrap().parsedv() == fmt.parse(raw));
                                assert(raw_page_to_branch_node(raw) == parsed.unwrap()@);
                            }
                        }
                        cache.handle_release(&aux, slot_handle);
                        proof {
                            assert(cache@.entries == cache0@.entries);
                            assert(cache@.lookup_map == cache0@.lookup_map);
                            assert(cache@.status_map == cache0@.status_map);
                            assert(cache@ == cache0@);
                        }
                        let node = match parsed {
                            Some(node) => node,
                            None => return BranchBetreeRecoveryStepResult::InvalidPage,
                        };
                        let ghost old_recovery = self.recovery@;
                        match self.recovery.read_branch_aux(root, node) {
                            BetreeRecoveryApplyResult::Applied => {
                                let ghost reads = map![aux@ => raw];
                                let ghost label = BetreeMetadataRecoveryLabel::ReadBranchAux {
                                    root: root@,
                                    reads,
                                };
                                proof {
                                    assert(old_recovery.pending_branch_aux[root@] == aux@);
                                    assert(to_branch_nodes(reads)[aux@]
                                        == raw_page_to_branch_node(raw));
                                    assert(BetreeMetadataRecoveryCore::next(
                                        old_recovery,
                                        self.recovery@,
                                        label,
                                    )) by {

                                    }
                                    assert(self.wf());

                                    Cache::State::access_read_only_from_valid_reads(
                                        cache0@,
                                        reads,
                                    );
                                    let access = recovery_page_access(label);
                                    assert(access.reads() == reads);
                                    assert(access.writes()
                                        == Map::<Address, RawPage>::empty());
                                    assert(AtomicBranchBetreeState::State::recover(
                                        old(self)@,
                                        self@,
                                        AtomicBranchBetreeState::Label::RecoveryAccess{access},
                                        self.recovery@,
                                        label,
                                    ));
                                    assert(AtomicBranchBetreeState::State::next_by(
                                        old(self)@,
                                        self@,
                                        AtomicBranchBetreeState::Label::RecoveryAccess{access},
                                        AtomicBranchBetreeState::Step::recover(
                                            self.recovery@,
                                            label,
                                        ),
                                    )) by {
                                        reveal(AtomicBranchBetreeState::State::next_by);
                                    }
                                    assert(AtomicBranchBetreeState::State::next(
                                        old(self)@,
                                        self@,
                                        AtomicBranchBetreeState::Label::RecoveryAccess{access},
                                    )) by {
                                        reveal(AtomicBranchBetreeState::State::next);
                                    }
                                    assert(Cache::State::next(
                                        cache0@,
                                        cache@,
                                        Cache::Label::Access {
                                            reads: access.reads(),
                                            writes: access.writes(),
                                        },
                                    ));
                                }
                                return BranchBetreeRecoveryStepResult::Advanced {
                                    label: Ghost(label),
                                    reads: Ghost(reads),
                                };
                            },
                            BetreeRecoveryApplyResult::Invalid => {
                                return BranchBetreeRecoveryStepResult::InvalidPage;
                            },
                        }
                    },
                    FetchErrorCode::CacheFull => {
                        return BranchBetreeRecoveryStepResult::CacheFull;
                    },
                    FetchErrorCode::Awaiting | FetchErrorCode::NotPresent => {
                        return BranchBetreeRecoveryStepResult::Blocked;
                    },
                }
            },
        }
    }

    pub fn recovery_complete(&mut self)
        requires
            old(self).wf(),
            old(self).control.loading,
            old(self).recovery.completion_matches(
                old(self).control.metadata@,
            ),
        ensures
            self.wf(),
            self.compactors@ == old(self).compactors@,
            self.wip_branches@ == old(self).wip_branches@,
            self.wip_branches@.len() == 0,
            self.root == old(self).control.metadata.root,
            self.control.metadata == old(self).control.metadata,
            self.control.installed == old(self).control.installed,
            self.control.frozen_metadata
                == old(self).control.frozen_metadata,
            self.ownership.persistent_aus()
                == old(self).recovery@.loaded_betree(
                    old(self).control.metadata@,
                ).durable_aus(),
            self.ownership.betree.all_aus()
                + self.ownership.branches.all_summary_aus()
                =~= old(self).recovery@.loaded_betree(
                    old(self).control.metadata@,
                ).durable_aus(),
            self.ownership.betree.all_aus()
                + self.ownership.branches.all_summary_aus()
                =~= old(self).recovery.ownership.betree.all_aus()
                    + old(self).recovery.ownership.branches
                        .all_summary_aus(),
            AtomicBranchBetreeState::State::next(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::RecoveryComplete{
                    discovered_aus: self.ownership.persistent_aus(),
                },
            ),
    {
        proof {
            self.recovery.completion_loaded_betree_matches(
                self.control.metadata@,
            );
            self.recovery.ownership
                .fully_persistent_owns_only_persistent_aus();
        }
        let ownership_bucket_count = self.ownership.betree.active.bucket_count;
        let memtable_bucket_count = self.memtable.bucket_count;
        let replacement_ownership = BranchBetreeOwnershipImpl::new(
            ownership_bucket_count,
        );
        let replacement_likes = AuLikesImpl::new(ownership_bucket_count);
        let mut old_ownership = replacement_ownership;
        let mut old_likes = replacement_likes;
        core::mem::swap(&mut self.ownership, &mut old_ownership);
        core::mem::swap(&mut self.ownership, &mut self.recovery.ownership);
        core::mem::swap(&mut old_likes, &mut self.branch_likes);
        core::mem::swap(&mut self.branch_likes, &mut self.recovery.branch_likes);

        self.root = self.control.metadata.root;
        self.memtable = MemtableImpl::new(
            memtable_bucket_count,
            self.control.metadata.seq_end,
        );
        self.control.loading = false;
        self.control.metadata_loaded = true;
        proof {
            assert(old(self).wip_branches@.len() == 0) by {
                assert(old(self).betree_i()
                    == empty_cached_betree());
                assert(old(self).betree_i().wip_branches.len() == 0);
                assert(bulk_branch_views(
                    old(self).wip_branches@,
                ).len() == old(self).wip_branches@.len());
            }
            assert(self.wip_branches@.len() == 0);
            assert(bulk_builders_wf(
                self.wip_branches@,
                &self.memtable,
            ));
            assert(self.betree_i()
                == old(self).recovery@.loaded_betree(
                    old(self).control.metadata@,
                ));
            assert(self.ownership.persistent_aus()
                == self.betree_i().durable_aus());
            assert(self.control_i().metadata
                == old(self).control_i().metadata);
            assert(self.control_i().recovery
                == old(self).control_i().recovery);
            assert(self.control_i().installed
                == old(self).control_i().installed);
            assert(self.control_i().frozen
                == old(self).control_i().frozen);
            assert(self.control.wf());
            assert(self.compactors@.len() == 0) by {
                assert(old(self).betree_i() == empty_cached_betree());
                assert(old(self).betree_i().compactors.len() == 0);
                assert(compactor_views(old(self).compactors@).len()
                    == old(self).compactors@.len());
            }
            assert(self.compactors@ == Seq::<CompactorImpl>::empty());
            empty_compactor_model_alignment(
                self.ownership.branches.active_summary_map(),
            );
            assert(self.wf());
            assert(AtomicBranchBetreeState::State::next_by(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::RecoveryComplete{
                    discovered_aus: self.ownership.persistent_aus(),
                },
                AtomicBranchBetreeState::Step::recovery_complete(),
            )) by {
                reveal(AtomicBranchBetreeState::State::next_by);
            }
            assert(AtomicBranchBetreeState::State::next(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::RecoveryComplete{
                    discovered_aus: self.ownership.persistent_aus(),
                },
            )) by {
                reveal(AtomicBranchBetreeState::State::next);
            }
        }
    }

    pub fn query_with_cache(
        &self,
        cache: &mut FracCacheImpl,
        key: Key,
    ) -> (result: BranchBetreeQueryResult)
        requires
            self.wf(),
            self.control.metadata_loaded,
            old(cache).wf(),
            self.query_cache_inv(old(cache)@),
        ensures
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            old(cache)@.inv() ==> cache@.inv(),
            forall |addr: Address, data: RawPage|
                old(cache)@.valid_read(addr, data)
                ==> cache@.valid_read(addr, data),
            forall |addr: Address, data: RawPage|
                cache@.valid_read(addr, data)
                ==> old(cache)@.valid_read(addr, data),
            match result {
                BranchBetreeQueryResult::Hit {
                    value,
                    access,
                } => {
                    &&& access@.wf()
                    &&& access@.read_only()
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        Cache::Label::Access {
                            reads: access@.reads(),
                            writes: access@.writes(),
                        },
                    )
                    &&& AtomicBranchBetreeState::State::next(
                        self@,
                        self@,
                        AtomicBranchBetreeState::Label::Query {
                            end_lsn: self.memtable.seq_end as nat,
                            key,
                            value,
                            access: access@,
                        },
                    )
                },
                BranchBetreeQueryResult::NeedCacheLoad { addr, handle } => {
                    &&& cache.entry_fetched(&addr)
                    &&& cache.valid_load_handle(&addr, handle)
                    &&& (self.ownership.betree.active_aus()
                        + self.ownership.branches.active_summary_aus())
                        .contains(addr@.au)
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        crate::implementation::FracCacheImpl_v::cache_load_label(&addr),
                    )
                },
                BranchBetreeQueryResult::CacheFull
                | BranchBetreeQueryResult::Blocked
                | BranchBetreeQueryResult::InvalidPage => {
                    cache@ == old(cache)@
                },
            },
    {
        let root = match self.root {
            Some(root) => root,
            None => {
                let disk_message = Message::Define {
                    value: Value(0),
                };
                let memtable_message = self.memtable.query(key);
                let final_message = merge_messages(
                    disk_message,
                    memtable_message,
                );
                let value = match final_message {
                    Message::Define { value } => value,
                    Message::Update { delta: _ } => {
                        proof { assert(false); }
                        Value(0)
                    },
                };
                let ghost receipt = crate::implementation::
                    CachedBranchBetree_v::LoadedBetreeQueryReceipt::
                        empty_for(key);
                let ghost access = PageAccess {
                    betree_reads: Map::empty(),
                    branch_reads: Map::empty(),
                    betree_writes: Map::empty(),
                    branch_writes: Map::empty(),
                };
                proof {
                    assert(Value(0)
                        == crate::spec::Messages_t::default_value());
                    assert(access.wf());
                    assert(access.read_only());
                    PageAccess::empty_cached_access_is_empty();
                    assert(access.reads()
                        == Map::<Address, RawPage>::empty());
                    assert(access.writes()
                        == Map::<Address, RawPage>::empty());
                    Cache::State::access_empty_is_noop(cache@);
                    assert(receipt.valid_for(
                        self.betree_i().root,
                        key,
                        access.loaded_betree_reads(),
                        access.loaded_branch_reads(),
                    ));
                    assert(final_message
                        == receipt.result().merge(
                            self.memtable@.query(key),
                        ));
                    assert(final_message == Message::Define { value });
                    assert(CachedBranchBetree::State::query(
                        self.betree_i(),
                        self.betree_i(),
                        CachedBranchBetree::Label::Query {
                            end_lsn: self.memtable.seq_end as nat,
                            key,
                            value,
                            access: access.cached_access(),
                        },
                        receipt,
                        access.loaded_betree_reads(),
                        access.loaded_branch_reads(),
                    )) by {

                    }
                    assert(CachedBranchBetree::State::next_by(
                        self.betree_i(),
                        self.betree_i(),
                        CachedBranchBetree::Label::Query {
                            end_lsn: self.memtable.seq_end as nat,
                            key,
                            value,
                            access: access.cached_access(),
                        },
                        CachedBranchBetree::Step::query(
                            receipt,
                            access.loaded_betree_reads(),
                            access.loaded_branch_reads(),
                        ),
                    )) by {
                        reveal(CachedBranchBetree::State::next_by);
                    }
                    assert(CachedBranchBetree::State::next(
                        self.betree_i(),
                        self.betree_i(),
                        CachedBranchBetree::Label::Query {
                            end_lsn: self.memtable.seq_end as nat,
                            key,
                            value,
                            access: access.cached_access(),
                        },
                    )) by {
                        reveal(CachedBranchBetree::State::next);
                    }
                    assert(AtomicBranchBetreeState::State::next_by(
                        self@,
                        self@,
                        AtomicBranchBetreeState::Label::Query {
                            end_lsn: self.memtable.seq_end as nat,
                            key,
                            value,
                            access,
                        },
                        AtomicBranchBetreeState::Step::query(
                            receipt,
                            access.loaded_betree_reads(),
                            access.loaded_branch_reads(),
                        ),
                    )) by {
                        reveal(AtomicBranchBetreeState::State::next_by);
                    }
                    assert(AtomicBranchBetreeState::State::next(
                        self@,
                        self@,
                        AtomicBranchBetreeState::Label::Query {
                            end_lsn: self.memtable.seq_end as nat,
                            key,
                            value,
                            access,
                        },
                    )) by {
                        reveal(AtomicBranchBetreeState::State::next);
                    }

                    assert(cache.valid_load_handles_preserved(*cache));
                }
                return BranchBetreeQueryResult::Hit {
                    value,
                    access: Ghost(access),
                };
            },
        };
        let ghost betree_aus = self.ownership.betree.active_aus();
        let ghost branch_summary = self.ownership.branches.active_summary_map();
        let ghost branch_aus = self.ownership.branches.active_summary_aus();
        let ghost cache0 = *cache;
        match load_betree_query(
            cache,
            root,
            key,
            CACHE_SIZE_RECS,
            CACHE_SIZE_RECS,
            Ghost(betree_aus),
            Ghost(branch_summary),
            Ghost(branch_aus),
        ) {
            BetreeQueryResult::NeedCacheLoad { addr, handle } => {
                proof {
                    if cache0@.inv() {
                        Cache::State::inv_next(
                            cache0@,
                            cache@,
                            crate::implementation::FracCacheImpl_v::cache_load_label(
                                &addr,
                            ),
                        );
                    }
                }
                BranchBetreeQueryResult::NeedCacheLoad { addr, handle }
            },
            BetreeQueryResult::CacheFull => BranchBetreeQueryResult::CacheFull,
            BetreeQueryResult::Blocked => BranchBetreeQueryResult::Blocked,
            BetreeQueryResult::InvalidPage => {
                BranchBetreeQueryResult::InvalidPage
            },
            BetreeQueryResult::Loaded {
                value: _,
                disk_message,
                betree_reads,
                branch_reads,
                receipt,
            } => {
                let memtable_message = self.memtable.query(key);
                let final_message = merge_messages(
                    disk_message,
                    memtable_message,
                );
                let value = match final_message {
                    Message::Define { value } => value,
                    Message::Update { delta: _ } => {
                        proof {
                            assert(disk_message is Define);
                            assert(false);
                        }
                        Value(0)
                    },
                };
                let ghost access = PageAccess {
                    betree_reads: betree_reads@,
                    branch_reads: branch_reads@,
                    betree_writes: Map::empty(),
                    branch_writes: Map::empty(),
                };
                proof {
                    if cache0@.inv() {
                        Cache::State::inv_next(
                            cache0@,
                            cache@,
                            Cache::Label::Access {
                                reads: betree_reads@.union_prefer_right(
                                    branch_reads@,
                                ),
                                writes: Map::empty(),
                            },
                        );
                    }
                    self.ownership.betree.ownership_sets_bounded();
                    self.ownership.branches.ownership_sets_bounded();
                    assert(betree_aus <= self.ownership.betree.all_aus());
                    assert(branch_aus
                        <= self.ownership.branches.all_summary_aus());
                    assert(betree_reads@.dom().disjoint(branch_reads@.dom())) by {
                        assert forall |addr: Address|
                            #[trigger] betree_reads@.dom().contains(addr)
                            implies !branch_reads@.dom().contains(addr) by {
                            if branch_reads@.dom().contains(addr) {
                                assert(betree_aus.contains(addr.au));
                                assert(branch_aus.contains(addr.au));
                                assert(self.ownership.betree.all_aus()
                                    .contains(addr.au));
                                assert(self.ownership.branches.all_summary_aus()
                                    .contains(addr.au));
                            }
                        }
                    }
                    assert(access.wf());
                    assert(access.read_only());
                    access.cached_read_only_shape();
                    assert(access.reads()
                        == betree_reads@.union_prefer_right(branch_reads@));
                    assert(access.writes() == Map::<Address, RawPage>::empty());
                    assert(final_message
                        == receipt@.result().merge(self.memtable@.query(key)));
                    assert(final_message == Message::Define { value });
                    assert(CachedBranchBetree::State::query(
                        self.betree_i(),
                        self.betree_i(),
                        CachedBranchBetree::Label::Query {
                            end_lsn: self.memtable.seq_end as nat,
                            key,
                            value,
                            access: PageAccess {
                                betree_reads: betree_reads@,
                                branch_reads: branch_reads@,
                                betree_writes: Map::empty(),
                                branch_writes: Map::empty(),
                            }.cached_access(),
                        },
                        receipt@,
                        to_betree_nodes(betree_reads@),
                        to_branch_nodes(branch_reads@),
                    )) by {

                    }
                    assert(CachedBranchBetree::State::next_by(
                        self.betree_i(),
                        self.betree_i(),
                        CachedBranchBetree::Label::Query {
                            end_lsn: self.memtable.seq_end as nat,
                            key,
                            value,
                            access: access.cached_access(),
                        },
                        CachedBranchBetree::Step::query(
                            receipt@,
                            access.loaded_betree_reads(),
                            access.loaded_branch_reads(),
                        ),
                    )) by {
                        reveal(CachedBranchBetree::State::next_by);
                    }
                    assert(CachedBranchBetree::State::next(
                        self.betree_i(),
                        self.betree_i(),
                        CachedBranchBetree::Label::Query {
                            end_lsn: self.memtable.seq_end as nat,
                            key,
                            value,
                            access: access.cached_access(),
                        },
                    )) by {
                        reveal(CachedBranchBetree::State::next);
                    }
                    assert(AtomicBranchBetreeState::State::next_by(
                        self@,
                        self@,
                        AtomicBranchBetreeState::Label::Query {
                            end_lsn: self.memtable.seq_end as nat,
                            key,
                            value,
                            access,
                        },
                        AtomicBranchBetreeState::Step::query(
                            receipt@,
                            access.loaded_betree_reads(),
                            access.loaded_branch_reads(),
                        ),
                    )) by {
                        reveal(AtomicBranchBetreeState::State::next_by);
                    }
                    assert(AtomicBranchBetreeState::State::next(
                        self@,
                        self@,
                        AtomicBranchBetreeState::Label::Query {
                            end_lsn: self.memtable.seq_end as nat,
                            key,
                            value,
                            access,
                        },
                    )) by {
                        reveal(AtomicBranchBetreeState::State::next);
                    }

                }
                BranchBetreeQueryResult::Hit {
                    value,
                    access: Ghost(access),
                }
            },
        }
    }

    pub fn branch_begin(
        &mut self,
        free_au_threshold: IAU,
    ) -> (result: BranchBetreeWipResult)
        requires
            old(self).wf(),
            old(self).control.metadata_loaded,
        ensures
            self.wf(),
            result is Applied,
            match result {
                BranchBetreeWipResult::Applied { idx } => {
                    &&& idx < self.wip_branches.len()
                    &&& idx == old(self).wip_branches.len()
                    &&& AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: Set::empty(),
                            access: PageAccess::empty(),
                        },
                    )
                },
                BranchBetreeWipResult::Noop => self@ == old(self)@,
            },
    {
        let branch = BulkBranchImpl::new(free_au_threshold);
        let idx = self.wip_branches.len();
        self.wip_branches.push(branch);
        proof {
            PageAccess::empty_cached_access_is_empty();
            assert(bulk_branch_views(self.wip_branches@)
                == bulk_branch_views(old(self).wip_branches@).push(
                    self.wip_branches@[idx as int]@,
                ));
            assert(self.betree_i().wip_branches
                == old(self).betree_i().wip_branches.push(
                    CachedBulkBranch::new(Set::empty()),
                ));
            assert(CachedBranchBetree::State::branch_begin(
                old(self).betree_i(),
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                    access: PageAccess::empty().cached_access(),
                },
            )) by {

            }
            assert(CachedBranchBetree::State::next_by(
                old(self).betree_i(),
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                    access: PageAccess::empty().cached_access(),
                },
                CachedBranchBetree::Step::branch_begin(),
            )) by {
                reveal(CachedBranchBetree::State::next_by);
            }
            assert(CachedBranchBetree::State::next(
                old(self).betree_i(),
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                    access: PageAccess::empty().cached_access(),
                },
            )) by {
                reveal(CachedBranchBetree::State::next);
            }
            assert(bulk_builders_wf(
                self.wip_branches@,
                &self.memtable,
            )) by {
                assert forall |i: int|
                    0 <= i < self.wip_branches@.len()
                    implies (#[trigger] self.wip_branches@[i])
                        .bulk_builder_wf(&self.memtable) by {
                    if i == idx as int {
                        assert(self.wip_branches@[i].bulk_builder is None);
                    } else {
                        assert(self.wip_branches@[i]
                            == old(self).wip_branches@[i]);
                    }
                }
            }

            assert(self.wf());
            assert(AtomicBranchBetreeState::State::next_by(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                    access: PageAccess::empty(),
                },
                AtomicBranchBetreeState::Step::branch_begin(
                    self.betree_i(),
                ),
            )) by {
                reveal(AtomicBranchBetreeState::State::next_by);
            }
            assert(AtomicBranchBetreeState::State::next(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                    access: PageAccess::empty(),
                },
            )) by {
                reveal(AtomicBranchBetreeState::State::next);
            }
        }
        BranchBetreeWipResult::Applied { idx }
    }

    pub fn branch_begin_bulk(
        &mut self,
        free_au_threshold: IAU,
    ) -> (result: BranchBetreeBulkStartResult)
        requires
            old(self).wf(),
            old(self).control.metadata_loaded,
        ensures
            self.wf(),
            self.compactors@ == old(self).compactors@,
            match result {
                BranchBetreeBulkStartResult::Started { idx } => {
                    &&& idx < self.wip_branches.len()
                    &&& idx == old(self).wip_branches.len()
                    &&& self.root == old(self).root
                    &&& self.ownership == old(self).ownership
                    &&& self.branch_likes == old(self).branch_likes
                    &&& self.memtable == old(self).memtable
                    &&& self.control == old(self).control
                    &&& self.wip_branches.len()
                        == old(self).wip_branches.len() + 1
                    &&& self.wip_branches@[idx as int]
                        .has_memtable_builder()
                    &&& self.wip_branches@[idx as int]
                        .bulk_builder_wf(&self.memtable)
                    &&& self.wip_branches@[idx as int]
                        .mini_allocator.i() == MiniAllocator::empty()
                    &&& forall |total_aus: IAU|
                        self.wip_branches@[idx as int]
                            .mini_allocator.bounded(total_aus)
                    &&& AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: Set::empty(),
                            access: PageAccess::empty(),
                        },
                    )
                },
                BranchBetreeBulkStartResult::Empty
                | BranchBetreeBulkStartResult::Overflow
                | BranchBetreeBulkStartResult::InvalidCapacity
                | BranchBetreeBulkStartResult::Blocked => {
                    *self == *old(self)
                },
            },
    {
        let builder = match crate::implementation::BranchBulkBuilderImpl_v::BranchBulkBuilder::start(
            &self.memtable,
        ) {
            crate::implementation::BranchBulkBuilderImpl_v::BranchBulkStartResult::Started {
                builder,
            } => builder,
            crate::implementation::BranchBulkBuilderImpl_v::BranchBulkStartResult::Empty => {
                return BranchBetreeBulkStartResult::Empty;
            },
            crate::implementation::BranchBulkBuilderImpl_v::BranchBulkStartResult::Overflow => {
                return BranchBetreeBulkStartResult::Overflow;
            },
            crate::implementation::BranchBulkBuilderImpl_v::BranchBulkStartResult::InvalidCapacity => {
                return BranchBetreeBulkStartResult::InvalidCapacity;
            },
        };
        let mut branch = BulkBranchImpl::new(free_au_threshold);
        branch.bulk_builder = Some(BulkBuilderImpl::Memtable {
            memtable: builder,
        });
        proof {
            assert(branch.allocated_pages() =~= Set::<Address>::empty()) by {
                assert forall |addr: Address|
                    !#[trigger] branch.allocated_pages().contains(addr) by {
                    assert(!branch.mini_allocator.i().allocs
                        .contains_key(addr.au));
                }
            }
            assert(branch.memtable_builder().staged_nodes@.dom()
                =~= Set::<Address>::empty());
            assert(branch.wf());
        }
        let idx = self.wip_branches.len();
        self.wip_branches.push(branch);
        proof {
            PageAccess::empty_cached_access_is_empty();
            assert(bulk_branch_views(self.wip_branches@)
                == bulk_branch_views(old(self).wip_branches@).push(
                    self.wip_branches@[idx as int]@,
                ));
            assert(self.wip_branches@[idx as int]@
                == CachedBulkBranch::new(Set::empty()));
            assert(self.betree_i().wip_branches
                == old(self).betree_i().wip_branches.push(
                    CachedBulkBranch::new(Set::empty()),
                ));
            assert(CachedBranchBetree::State::branch_begin(
                old(self).betree_i(),
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                    access: PageAccess::empty().cached_access(),
                },
            )) by {

            }
            assert(CachedBranchBetree::State::next_by(
                old(self).betree_i(),
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                    access: PageAccess::empty().cached_access(),
                },
                CachedBranchBetree::Step::branch_begin(),
            )) by {
                reveal(CachedBranchBetree::State::next_by);
            }
            assert(CachedBranchBetree::State::next(
                old(self).betree_i(),
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                    access: PageAccess::empty().cached_access(),
                },
            )) by {
                reveal(CachedBranchBetree::State::next);
            }
            assert(bulk_builders_wf(
                self.wip_branches@,
                &self.memtable,
            )) by {
                assert forall |i: int|
                    0 <= i < self.wip_branches@.len()
                    implies (#[trigger] self.wip_branches@[i])
                        .bulk_builder_wf(&self.memtable) by {
                    if i == idx as int {
                        assert(self.wip_branches@[i]
                            .bulk_builder is Some);
                    } else {
                        assert(self.wip_branches@[i]
                            == old(self).wip_branches@[i]);
                    }
                }
            }

            assert(self.wf());
            assert(AtomicBranchBetreeState::State::next_by(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                    access: PageAccess::empty(),
                },
                AtomicBranchBetreeState::Step::branch_begin(
                    self.betree_i(),
                ),
            )) by {
                reveal(AtomicBranchBetreeState::State::next_by);
            }
            assert(AtomicBranchBetreeState::State::next(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                    access: PageAccess::empty(),
                },
            )) by {
                reveal(AtomicBranchBetreeState::State::next);
            }
        }
        BranchBetreeBulkStartResult::Started { idx }
    }

    pub fn branch_begin_streaming(
        &mut self,
        free_au_threshold: IAU,
    ) -> (result: BranchBetreeBulkStartResult)
        requires
            old(self).wf(),
            old(self).control.metadata_loaded,
        ensures
            self.wf(),
            self.compactors@ == old(self).compactors@,
            match result {
                BranchBetreeBulkStartResult::Started { idx } => {
                    &&& idx < self.wip_branches.len()
                    &&& idx == old(self).wip_branches.len()
                    &&& self.wip_branches.len()
                        == old(self).wip_branches.len() + 1
                    &&& self.root == old(self).root
                    &&& self.ownership == old(self).ownership
                    &&& self.branch_likes == old(self).branch_likes
                    &&& self.memtable == old(self).memtable
                    &&& self.control == old(self).control
                    &&& self.wip_branches@[idx as int]
                        .has_streaming_builder()
                    &&& self.wip_branches@[idx as int]
                        .streaming_builder().source_entries@.len() == 0
                    &&& self.wip_branches@[idx as int]
                        .streaming_builder().phase is Reading
                    &&& self.wip_branches@[idx as int]
                        .mini_allocator.i() == MiniAllocator::empty()
                    &&& forall |cache: Cache::State|
                        self.wip_branches@[idx as int].cache_inv(cache)
                    &&& forall |total_aus: IAU|
                        self.wip_branches@[idx as int]
                            .mini_allocator.bounded(total_aus)
                    &&& AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: Set::empty(),
                            access: PageAccess::empty(),
                        },
                    )
                },
                BranchBetreeBulkStartResult::Empty
                | BranchBetreeBulkStartResult::Overflow
                | BranchBetreeBulkStartResult::InvalidCapacity
                | BranchBetreeBulkStartResult::Blocked => {
                    *self == *old(self)
                },
            },
    {
        let mut branch = BulkBranchImpl::new(free_au_threshold);
        let started = branch.begin_streaming_build();
        match started {
            BulkStartResult::Started => {},
            BulkStartResult::InvalidCapacity => {
                return BranchBetreeBulkStartResult::InvalidCapacity;
            },
            _ => {
                return BranchBetreeBulkStartResult::Blocked;
            },
        }
        proof {
            assert(branch.allocated_pages() =~= Set::<Address>::empty()) by {
                assert forall |addr: Address|
                    !#[trigger] branch.allocated_pages().contains(addr) by {
                    assert(!branch.mini_allocator.i().allocs
                        .contains_key(addr.au));
                }
            }
            assert(branch.wf());
        }
        let idx = self.wip_branches.len();
        self.wip_branches.push(branch);
        proof {
            PageAccess::empty_cached_access_is_empty();
            assert(self.wip_branches@[idx as int]@
                == CachedBulkBranch::new(Set::empty()));
            assert(bulk_branch_views(self.wip_branches@)
                == bulk_branch_views(old(self).wip_branches@).push(
                    CachedBulkBranch::new(Set::empty()),
                ));
            assert(CachedBranchBetree::State::branch_begin(
                old(self).betree_i(),
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                    access: PageAccess::empty().cached_access(),
                },
            )) by {}
            assert(CachedBranchBetree::State::next_by(
                old(self).betree_i(),
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                    access: PageAccess::empty().cached_access(),
                },
                CachedBranchBetree::Step::branch_begin(),
            )) by {
                reveal(CachedBranchBetree::State::next_by);
            }
            assert(CachedBranchBetree::State::next(
                old(self).betree_i(),
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                    access: PageAccess::empty().cached_access(),
                },
            )) by {
                reveal(CachedBranchBetree::State::next);
            }
            assert(bulk_builders_wf(
                self.wip_branches@,
                &self.memtable,
            )) by {
                assert forall |i: int| 0 <= i < self.wip_branches@.len()
                    implies (#[trigger] self.wip_branches@[i])
                        .bulk_builder_wf(&self.memtable) by {
                    if i == idx as int {
                        assert(self.wip_branches@[i]
                            .has_streaming_builder());
                    } else {
                        assert(self.wip_branches@[i]
                            == old(self).wip_branches@[i]);
                    }
                }
            }
            assert(self.wf());
            assert(AtomicBranchBetreeState::State::branch_begin(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                    access: PageAccess::empty(),
                },
                self.betree_i(),
            )) by {}
            assert(AtomicBranchBetreeState::State::next_by(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                    access: PageAccess::empty(),
                },
                AtomicBranchBetreeState::Step::branch_begin(
                    self.betree_i(),
                ),
            )) by {
                reveal(AtomicBranchBetreeState::State::next_by);
            }
            assert(AtomicBranchBetreeState::State::next(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                    access: PageAccess::empty(),
                },
            )) by {
                reveal(AtomicBranchBetreeState::State::next);
            }
        }
        BranchBetreeBulkStartResult::Started { idx }
    }

    pub fn branch_fill_aus(
        &mut self,
        idx: usize,
        aus: Vec<IAU>,
    ) -> (result: BranchBetreeWipResult)
        requires
            old(self).wf(),
            old(self).control.metadata_loaded,
            idx < old(self).wip_branches.len(),
            !old(self).wip_branches@[idx as int].sealed,
            MiniAllocatorImpl::iau_seq_unique(aus@),
            iau_vec_set(aus@).disjoint(
                MiniAllocatorImpl::allocators_au_set(
                    old(self).wip_branches@[idx as int]
                        .mini_allocator.allocators@,
                ),
            ),
            old(self).wip_branches@[idx as int]
                .mini_allocator.i().all_aus().disjoint(
                    old(self).ownership.betree.all_aus()
                        + old(self).ownership.branches.all_summary_aus(),
                ),
            iau_vec_set(aus@).disjoint(
                old(self).ownership.betree.all_aus()
                    + old(self).ownership.branches.all_summary_aus(),
            ),
            old(self).betree_i().is_fresh(iau_vec_set(aus@)),
        ensures
            self.wf(),
            self.compactors@ == old(self).compactors@,
            result is Applied,
            self.root == old(self).root,
            self.ownership == old(self).ownership,
            self.branch_likes@ == old(self).branch_likes@,
            self.wip_branches@[idx as int]
                .mini_allocator.i().all_aus().disjoint(
                    self.ownership.betree.all_aus()
                        + self.ownership.branches.all_summary_aus(),
                ),
            match result {
                BranchBetreeWipResult::Applied { idx: post_idx } => {
                    &&& post_idx == idx
                    &&& self.memtable == old(self).memtable
                    &&& self.wip_branches.len()
                        == old(self).wip_branches.len()
                    &&& self.wip_branches@[idx as int].bulk_builder
                        == old(self).wip_branches@[idx as int].bulk_builder
                    &&& self.wip_branches@[idx as int].sealed
                        == old(self).wip_branches@[idx as int].sealed
                    &&& self.control == old(self).control
                    &&& self.wip_branches@[idx as int]
                        .mini_allocator.i()
                        == old(self).wip_branches@[idx as int]
                            .mini_allocator.i().add_aus(iau_vec_set(aus@))
                    &&& forall |total_aus: IAU|
                        old(self).wip_branches@[idx as int]
                            .mini_allocator.bounded(total_aus)
                        && (forall |i: int| 0 <= i < aus@.len() ==> {
                            &&& 0 < (#[trigger] aus@[i] as nat)
                            &&& (aus@[i] as nat) < total_aus as nat
                        })
                        ==> self.wip_branches@[idx as int]
                            .mini_allocator.bounded(total_aus)
                    &&& AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: iau_vec_set(aus@),
                            deallocs: Set::empty(),
                            access: PageAccess::empty(),
                        },
                    )
                },
                BranchBetreeWipResult::Noop => self@ == old(self)@,
            },
    {
        let ghost old_branches = self.wip_branches@;
        let mut branch = self.wip_branches.remove(idx);
        branch.fill_aus(aus);
        self.wip_branches.insert(idx, branch);
        proof {
            PageAccess::empty_cached_access_is_empty();
            assert(self.wip_branches@
                == old_branches.remove(idx as int).insert(
                    idx as int,
                    self.wip_branches@[idx as int],
                ));
            assert(self.wip_branches@
                == old_branches.update(
                    idx as int,
                    self.wip_branches@[idx as int],
                ));
            assert(bulk_branch_views(self.wip_branches@)
                == bulk_branch_views(old_branches).update(
                    idx as int,
                    self.wip_branches@[idx as int]@,
                ));
            assert(bulk_builders_wf(
                self.wip_branches@,
                &self.memtable,
            )) by {
                assert forall |i: int|
                    0 <= i < self.wip_branches@.len()
                    implies (#[trigger] self.wip_branches@[i])
                        .bulk_builder_wf(&self.memtable) by {
                    if i == idx as int {
                        assert(self.wip_branches@[i].bulk_builder
                            == old_branches[i].bulk_builder);
                    } else {
                        assert(self.wip_branches@[i] == old_branches[i]);
                    }
                }
            }
            assert(CachedBranchBetree::State::branch_fill(
                old(self).betree_i(),
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs: iau_vec_set(aus@),
                    deallocs: Set::empty(),
                    access: PageAccess::empty().cached_access(),
                },
                idx as int,
                self.wip_branches@[idx as int]@,
            )) by {

            }
            assert(CachedBranchBetree::State::next_by(
                old(self).betree_i(),
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs: iau_vec_set(aus@),
                    deallocs: Set::empty(),
                    access: PageAccess::empty().cached_access(),
                },
                CachedBranchBetree::Step::branch_fill(
                    idx as int,
                    self.wip_branches@[idx as int]@,
                ),
            )) by {
                reveal(CachedBranchBetree::State::next_by);
            }
            assert(CachedBranchBetree::State::next(
                old(self).betree_i(),
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs: iau_vec_set(aus@),
                    deallocs: Set::empty(),
                    access: PageAccess::empty().cached_access(),
                },
            )) by {
                reveal(CachedBranchBetree::State::next);
            }
            assert(old(self).wip_branches@[idx as int]
                .mini_allocator.i().all_aus().disjoint(
                    old(self).ownership.betree.all_aus()
                        + old(self).ownership.branches.all_summary_aus(),
                ));
            assert(iau_vec_set(aus@).disjoint(
                old(self).ownership.betree.all_aus()
                    + old(self).ownership.branches.all_summary_aus(),
            ));
            assert(self.wip_branches@[idx as int]
                .mini_allocator.i().all_aus()
                =~= old(self).wip_branches@[idx as int]
                    .mini_allocator.i().all_aus() + iau_vec_set(aus@));

            assert(self.wf());
            assert(AtomicBranchBetreeState::State::next_by(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs: iau_vec_set(aus@),
                    deallocs: Set::empty(),
                    access: PageAccess::empty(),
                },
                AtomicBranchBetreeState::Step::branch_fill(
                    self.betree_i(),
                    idx as int,
                    self.wip_branches@[idx as int]@,
                ),
            )) by {
                reveal(AtomicBranchBetreeState::State::next_by);
            }
            assert(AtomicBranchBetreeState::State::next(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs: iau_vec_set(aus@),
                    deallocs: Set::empty(),
                    access: PageAccess::empty(),
                },
            )) by {
                reveal(AtomicBranchBetreeState::State::next);
            }
        }
        BranchBetreeWipResult::Applied { idx }
    }

    pub fn branch_abort(
        &mut self,
        idx: usize,
    ) -> (result: BranchBetreeAbortResult)
        requires
            old(self).wf(),
            old(self).control.metadata_loaded,
            idx < old(self).wip_branches.len(),
        ensures
            self.wf(),
            self.compactors@ == old(self).compactors@,
            self.root == old(self).root,
            self.control == old(self).control,
            self.memtable == old(self).memtable,
            self.ownership == old(self).ownership,
            self.branch_likes == old(self).branch_likes,
            self.wip_branches@
                == old(self).wip_branches@.remove(idx as int),
            self.ownership.betree.all_aus()
                == old(self).ownership.betree.all_aus(),
            self.ownership.branches.all_summary_aus()
                == old(self).ownership.branches.all_summary_aus(),
            match result {
                BranchBetreeAbortResult::Aborted { deallocs } => {
                    &&& unique_iau_seq(deallocs@)
                    &&& iau_seq_set(deallocs@)
                        =~= old(self).wip_branches@[idx as int]
                            .mini_allocator.i().all_aus()
                    &&& AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: iau_seq_set(deallocs@),
                            access: PageAccess::empty(),
                        },
                    )
                },
            },
    {
        let ghost pre_betree = self.betree_i();
        let ghost pre_wips = self.wip_branches@;
        let deallocs = self.wip_branches[idx]
            .mini_allocator.all_aus_vec();
        self.wip_branches.remove(idx);
        proof {
            PageAccess::empty_cached_access_is_empty();
            assert(self.wip_branches@
                == pre_wips.remove(idx as int));
            assert(bulk_branch_views(self.wip_branches@)
                == pre_betree.wip_branches.remove(idx as int)) by {
                assert_seqs_equal!(
                    bulk_branch_views(self.wip_branches@),
                    pre_betree.wip_branches.remove(idx as int),
                    i => {
                        if i < idx {
                            assert(self.wip_branches@[i] == pre_wips[i]);
                        } else {
                            assert(self.wip_branches@[i] == pre_wips[i + 1]);
                        }
                    }
                );
            }
            assert(bulk_builders_wf(
                self.wip_branches@,
                &self.memtable,
            )) by {
                assert forall |i: int|
                    0 <= i < self.wip_branches@.len()
                    implies (#[trigger] self.wip_branches@[i])
                        .bulk_builder_wf(&self.memtable) by {
                    if i < idx {
                        assert(self.wip_branches@[i] == pre_wips[i]);
                    } else {
                        assert(self.wip_branches@[i] == pre_wips[i + 1]);
                    }
                }
            }
            assert(CachedBranchBetree::State::branch_abort(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: iau_seq_set(deallocs@),
                    access: PageAccess::empty().cached_access(),
                },
                idx as int,
            )) by {

            }
            assert(CachedBranchBetree::State::next_by(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: iau_seq_set(deallocs@),
                    access: PageAccess::empty().cached_access(),
                },
                CachedBranchBetree::Step::branch_abort(idx as int),
            )) by {
                reveal(CachedBranchBetree::State::next_by);
            }
            assert(CachedBranchBetree::State::next(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: iau_seq_set(deallocs@),
                    access: PageAccess::empty().cached_access(),
                },
            )) by {
                reveal(CachedBranchBetree::State::next);
            }
            assert(self.wf());
            assert(AtomicBranchBetreeState::State::next_by(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: iau_seq_set(deallocs@),
                    access: PageAccess::empty(),
                },
                AtomicBranchBetreeState::Step::branch_abort(
                    self.betree_i(),
                    idx as int,
                ),
            )) by {
                reveal(AtomicBranchBetreeState::State::next_by);
            }
            assert(AtomicBranchBetreeState::State::next(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: iau_seq_set(deallocs@),
                    access: PageAccess::empty(),
                },
            )) by {
                reveal(AtomicBranchBetreeState::State::next);
            }
        }
        BranchBetreeAbortResult::Aborted { deallocs }
    }

    pub fn branch_begin_bulk_build(
        &mut self,
        idx: usize,
    ) -> (result: BranchBetreeBulkStartResult)
        requires
            old(self).wf(),
            old(self).control.metadata_loaded,
            idx < old(self).wip_branches.len(),
            old(self).wip_branches@[idx as int].bulk_builder is None,
            old(self).wip_branches@[idx as int].root is None,
            old(self).wip_branches@[idx as int]
                .allocated_pages().is_empty(),
        ensures
            self.wf(),
            self@ == old(self)@,
            match result {
                BranchBetreeBulkStartResult::Started { idx: post_idx } => {
                    &&& post_idx == idx
                    &&& self.wip_branches@[idx as int]
                        .has_memtable_builder()
                    &&& self.wip_branches@[idx as int]
                        .bulk_builder_wf(&self.memtable)
                },
                BranchBetreeBulkStartResult::Empty
                | BranchBetreeBulkStartResult::Overflow
                | BranchBetreeBulkStartResult::InvalidCapacity
                | BranchBetreeBulkStartResult::Blocked => {
                    *self == *old(self)
                },
            },
    {
        let builder = match crate::implementation::BranchBulkBuilderImpl_v::BranchBulkBuilder::start(
            &self.memtable,
        ) {
            crate::implementation::BranchBulkBuilderImpl_v::BranchBulkStartResult::Started {
                builder,
            } => builder,
            crate::implementation::BranchBulkBuilderImpl_v::BranchBulkStartResult::Empty => {
                return BranchBetreeBulkStartResult::Empty;
            },
            crate::implementation::BranchBulkBuilderImpl_v::BranchBulkStartResult::Overflow => {
                return BranchBetreeBulkStartResult::Overflow;
            },
            crate::implementation::BranchBulkBuilderImpl_v::BranchBulkStartResult::InvalidCapacity => {
                return BranchBetreeBulkStartResult::InvalidCapacity;
            },
        };
        let ghost old_branches = self.wip_branches@;
        let mut branch = self.wip_branches.remove(idx);
        branch.bulk_builder = Some(BulkBuilderImpl::Memtable {
            memtable: builder,
        });
        self.wip_branches.insert(idx, branch);
        proof {
            assert(self.wip_branches@
                == old_branches.update(
                    idx as int,
                    self.wip_branches@[idx as int],
                ));
            assert(bulk_branch_views(self.wip_branches@)
                == bulk_branch_views(old_branches)) by {
                assert forall |i: int|
                    0 <= i < self.wip_branches@.len()
                    implies #[trigger] self.wip_branches@[i]@
                        == old_branches[i]@ by {
                    if i != idx as int {
                        assert(self.wip_branches@[i] == old_branches[i]);
                    }
                }
            }
            assert(bulk_builders_wf(
                self.wip_branches@,
                &self.memtable,
            )) by {
                assert forall |i: int|
                    0 <= i < self.wip_branches@.len()
                    implies (#[trigger] self.wip_branches@[i])
                        .bulk_builder_wf(&self.memtable) by {
                    if i != idx as int {
                        assert(self.wip_branches@[i] == old_branches[i]);
                    }
                }
            }
            assert(self@ == old(self)@);
            assert(self.wf());
        }
        BranchBetreeBulkStartResult::Started { idx }
    }

    pub fn branch_stage_bulk_page(
        &mut self,
        cache: &mut FracCacheImpl,
        idx: usize,
        disk_au_count: IAU,
        disk_page_count: crate::spec::ImplDisk_t::IPage,
    ) -> (result: BranchBetreeBuildResult)
        requires
            old(self).wf(),
            old(self).control.metadata_loaded,
            idx < old(self).wip_branches.len(),
            old(self).wip_branches@[idx as int].bulk_builder is Some,
            old(self).wip_branches@[idx as int].builder_page_ready(),
            old(self).wip_branches@[idx as int]
                .mini_allocator.bounded(disk_au_count),
            old(self).wip_branches@[idx as int]
                .cache_inv(old(cache)@),
            old(cache).wf(),
            old(cache)@.inv(),
            0 < disk_page_count as nat,
            disk_page_count as nat
                == crate::disk::GenericDisk_v::page_count(),
        ensures
            self.wf(),
            self.root == old(self).root,
            self.branch_likes == old(self).branch_likes,
            self.compactors@ == old(self).compactors@,
            self.ownership == old(self).ownership,
            self.wip_branches@[idx as int]
                .mini_allocator.i().all_aus()
                == old(self).wip_branches@[idx as int]
                    .mini_allocator.i().all_aus(),
            old(self).wip_branches@[idx as int]
                .has_streaming_builder() ==> {
                &&& self.wip_branches@[idx as int]
                    .has_streaming_builder()
                &&& self.wip_branches@[idx as int]
                    .streaming_builder().phase
                    == old(self).wip_branches@[idx as int]
                        .streaming_builder().phase
                &&& self.wip_branches@[idx as int]
                    .streaming_builder().source_entries@
                    == old(self).wip_branches@[idx as int]
                        .streaming_builder().source_entries@
            },
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            match result {
                BranchBetreeBuildResult::Applied {
                    idx: post_idx,
                    prepared_cache,
                    access,
                    event,
                } => {
                    &&& post_idx == idx
                    &&& self.memtable == old(self).memtable
                    &&& self.control == old(self).control
                    &&& self.wip_branches.len()
                        == old(self).wip_branches.len()
                    &&& self.wip_branches@[idx as int].bulk_builder is Some
                    &&& (self.wip_branches@[idx as int]
                        .has_memtable_builder()
                        <==> old(self).wip_branches@[idx as int]
                            .has_memtable_builder())
                    &&& (self.wip_branches@[idx as int]
                        .has_streaming_builder()
                        <==> old(self).wip_branches@[idx as int]
                            .has_streaming_builder())
                    &&& !self.wip_branches@[idx as int].sealed
                    &&& self.wip_branches@[idx as int]
                        .mini_allocator.i().all_aus()
                        == old(self).wip_branches@[idx as int]
                            .mini_allocator.i().all_aus()
                    &&& self.wip_branches@[idx as int]
                        .mini_allocator.bounded(disk_au_count)
                    &&& event@ == CachedBulkBranchEvent::StagePage {
                        addr: event@->addr,
                        write_nodes: access@.loaded_branch_writes(),
                    }
                    &&& access@.wf()
                    &&& access@.only_branch()
                    &&& access@.betree_reads.is_empty()
                    &&& access@.betree_writes.is_empty()
                    &&& access@.branch_reads.is_empty()
                    &&& access@.writes().dom() <= addresses_in_aus(
                        old(self).wip_branches@[idx as int]
                            .mini_allocator.i().all_aus(),
                    )
                    &&& self.wip_branches@[idx as int]
                        .cache_inv(cache@)
                    &&& Cache::State::next(
                        old(cache)@,
                        prepared_cache@,
                        Cache::Label::Internal,
                    )
                    &&& Cache::State::next(
                        prepared_cache@,
                        cache@,
                        Cache::Label::Access {
                            reads: access@.reads(),
                            writes: access@.writes(),
                        },
                    )
                    &&& AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: Set::empty(),
                            access: access@,
                        },
                    )
                },
                BranchBetreeBuildResult::NeedsAUs
                | BranchBetreeBuildResult::CacheFull
                | BranchBetreeBuildResult::Blocked
                | BranchBetreeBuildResult::InvalidPage => {
                    &&& self@ == old(self)@
                    &&& self.wip_branches@ == old(self).wip_branches@
                    &&& cache@ == old(cache)@
                },
            },
    {
        let ghost old_branches = self.wip_branches@;
        let mut branch = self.wip_branches.remove(idx);
        let stage_result = branch.stage_bulk_page_with_cache(
            &self.memtable,
            cache,
            disk_au_count,
            disk_page_count,
        );
        self.wip_branches.insert(idx, branch);
        proof {
            assert(self.wip_branches@
                == old_branches.update(
                    idx as int,
                    self.wip_branches@[idx as int],
                ));
            assert(bulk_branch_views(self.wip_branches@)
                == bulk_branch_views(old_branches).update(
                    idx as int,
                    self.wip_branches@[idx as int]@,
                ));
            if !(stage_result is Staged) {
                assert(self.wip_branches@[idx as int]
                    == old_branches[idx as int]);
                assert(self.wip_branches@ == old_branches) by {
                    assert_seqs_equal!(
                        self.wip_branches@,
                        old_branches,
                        i => {}
                    );
                }
                assert(self@ == old(self)@);
            } else if old(self).wip_branches@[idx as int]
                .has_streaming_builder()
            {
                assert(self.wip_branches@[idx as int]
                    .streaming_builder().source_entries@
                    == old(self).wip_branches@[idx as int]
                        .streaming_builder().source_entries@);
            }
        }
        match stage_result {
            BulkStageResult::NeedsAUs => {
                BranchBetreeBuildResult::NeedsAUs
            },
            BulkStageResult::CacheFull => {
                BranchBetreeBuildResult::CacheFull
            },
            BulkStageResult::Blocked => {
                BranchBetreeBuildResult::Blocked
            },
            BulkStageResult::InvalidPage => {
                BranchBetreeBuildResult::InvalidPage
            },
            BulkStageResult::Staged {
                addr: _,
                prepared_cache,
                writes,
                event,
            } => {
                let ghost access = PageAccess {
                    betree_reads: Map::empty(),
                    branch_reads: Map::empty(),
                    betree_writes: Map::empty(),
                    branch_writes: writes@,
                };
                proof {
                    assert(access.wf());
                    assert(access.reads()
                        == Map::<Address, RawPage>::empty());
                    assert_maps_equal!(access.writes(), writes@, addr => {});
                    assert(CachedBranchBetree::State::branch_build(
                        old(self).betree_i(),
                        self.betree_i(),
                        CachedBranchBetree::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: Set::empty(),
                            access: access.cached_access(),
                        },
                        idx as int,
                        self.wip_branches@[idx as int]@,
                        event@,
                    )) by {

                    }
                    reveal(CachedBranchBetree::State::next);
                    reveal(CachedBranchBetree::State::next_by);
                    assert(CachedBranchBetree::State::next_by(
                        old(self).betree_i(),
                        self.betree_i(),
                        CachedBranchBetree::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: Set::empty(),
                            access: access.cached_access(),
                        },
                        CachedBranchBetree::Step::branch_build(
                            idx as int,
                            self.wip_branches@[idx as int]@,
                            event@,
                        ),
                    ));
                    assert(CachedBranchBetree::State::next(
                        old(self).betree_i(),
                        self.betree_i(),
                        CachedBranchBetree::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: Set::empty(),
                            access: access.cached_access(),
                        },
                    ));
                    assert(AtomicBranchBetreeState::State::next_by(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: Set::empty(),
                            access,
                        },
                        AtomicBranchBetreeState::Step::branch_build(
                            self.betree_i(),
                            idx as int,
                            self.wip_branches@[idx as int]@,
                            event@,
                        ),
                    )) by {
                        reveal(AtomicBranchBetreeState::State::next_by);
                    }
                    assert(AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: Set::empty(),
                            access,
                        },
                    )) by {
                        reveal(AtomicBranchBetreeState::State::next);
                    }
                    assert(bulk_builders_wf(
                        self.wip_branches@,
                        &self.memtable,
                    )) by {
                        assert forall |i: int|
                            0 <= i < self.wip_branches@.len()
                            implies (#[trigger] self.wip_branches@[i])
                                .bulk_builder_wf(&self.memtable) by {
                            if i != idx as int {
                                assert(self.wip_branches@[i]
                                    == old_branches[i]);
                            }
                        }
                    }

                    assert(self.wf());
                }
                BranchBetreeBuildResult::Applied {
                    idx,
                    prepared_cache,
                    access: Ghost(access),
                    event,
                }
            },
        }
    }

    pub fn branch_bulk_seal(
        &mut self,
        cache: &mut FracCacheImpl,
        idx: usize,
        disk_au_count: IAU,
        disk_page_count: crate::spec::ImplDisk_t::IPage,
    ) -> (result: BranchBetreeBulkSealResult)
        requires
            old(self).wf(),
            old(self).control.metadata_loaded,
            idx < old(self).wip_branches.len(),
            old(self).wip_branches@[idx as int].bulk_builder is Some,
            old(self).wip_branches@[idx as int].builder_ready_to_seal(),
            old(self).wip_branches@[idx as int]
                .mini_allocator.bounded(disk_au_count),
            old(self).wip_branches@[idx as int]
                .cache_inv(old(cache)@),
            old(cache).wf(),
            old(cache)@.inv(),
            0 < disk_page_count as nat,
            disk_page_count as nat
                == crate::disk::GenericDisk_v::page_count(),
        ensures
            self.wf(),
            self.root == old(self).root,
            self.branch_likes == old(self).branch_likes,
            self.compactors@ == old(self).compactors@,
            self.ownership == old(self).ownership,
            self.wip_branches@[idx as int]
                .mini_allocator.i().all_aus()
                <= old(self).wip_branches@[idx as int]
                    .mini_allocator.i().all_aus(),
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            match result {
                BranchBetreeBulkSealResult::Sealed {
                    idx: post_idx,
                    root,
                    aux_ptr,
                    prepared_cache,
                    access,
                    event,
                    deallocs,
                    branch,
                } => {
                    &&& post_idx == idx
                    &&& self.memtable == old(self).memtable
                    &&& self.control == old(self).control
                    &&& self.wip_branches.len()
                        == old(self).wip_branches.len()
                    &&& self.wip_branches@[idx as int]
                        .bulk_builder is None
                    &&& self.wip_branches@[idx as int].sealed
                    &&& self.wip_branches@[idx as int]
                        .mini_allocator.bounded(disk_au_count)
                    &&& iau_vec_set(deallocs@)
                        <= old(self).wip_branches@[idx as int]
                            .mini_allocator.i().all_aus()
                    &&& self.wip_branches@[idx as int]
                        .mini_allocator.i().all_aus()
                        == old(self).wip_branches@[idx as int]
                            .mini_allocator.i().all_aus()
                            - iau_vec_set(deallocs@)
                    &&& event@ == CachedBulkBranchEvent::BulkSeal {
                        root: root@,
                        aux_ptr: iopt_addr(aux_ptr),
                        write_nodes: to_branch_nodes(
                            access@.branch_writes,
                        ),
                    }
                    &&& access@.wf()
                    &&& access@.betree_reads.is_empty()
                    &&& access@.betree_writes.is_empty()
                    &&& access@.branch_reads.is_empty()
                    &&& branch@.valid_sealed_branch()
                    &&& branch@.tight_disk_view_with_summary()
                    &&& branch@.i().i().map
                        == old(self).wip_branches@[idx as int]
                            .builder_source_map()
                    &&& (old(self).wip_branches@[idx as int]
                        .has_memtable_builder() ==> branch@.i().i().map
                            == self.memtable@.buffer.map)
                    &&& self.wip_branches@[idx as int]
                        .sealed_branch@ == Some(branch@)
                    &&& self.wip_branches@[idx as int]
                        .sealed_source@ == Some(
                            old(self).wip_branches@[idx as int]
                                .builder_source_map(),
                        )
                    &&& self.wip_branches@[idx as int]
                        .cache_inv(cache@)
                    &&& Cache::State::next(
                        old(cache)@,
                        prepared_cache@,
                        Cache::Label::Internal,
                    )
                    &&& Cache::State::next(
                        prepared_cache@,
                        cache@,
                        Cache::Label::Access {
                            reads: access@.reads(),
                            writes: access@.writes(),
                        },
                    )
                    &&& AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: iau_vec_set(deallocs@),
                            access: access@,
                        },
                    )
                },
                BranchBetreeBulkSealResult::NeedsAUs
                | BranchBetreeBulkSealResult::CacheFull
                | BranchBetreeBulkSealResult::Blocked
                | BranchBetreeBulkSealResult::InvalidPage => {
                    &&& self@ == old(self)@
                    &&& self.wip_branches@ == old(self).wip_branches@
                    &&& cache@ == old(cache)@
                },
            },
    {
        let ghost old_branches = self.wip_branches@;
        let mut branch_impl = self.wip_branches.remove(idx);
        let seal_result = branch_impl.bulk_seal_with_cache(
            &self.memtable,
            cache,
            disk_au_count,
            disk_page_count,
        );
        self.wip_branches.insert(idx, branch_impl);
        proof {
            assert(self.wip_branches@
                == old_branches.update(
                    idx as int,
                    self.wip_branches@[idx as int],
                ));
            assert(bulk_branch_views(self.wip_branches@)
                == bulk_branch_views(old_branches).update(
                    idx as int,
                    self.wip_branches@[idx as int]@,
                ));
            if !(seal_result is Sealed) {
                assert(self.wip_branches@[idx as int]
                    == old_branches[idx as int]);
                assert(self.wip_branches@ == old_branches) by {
                    assert_seqs_equal!(
                        self.wip_branches@,
                        old_branches,
                        i => {}
                    );
                }
                assert(self@ == old(self)@);
            }
        }
        match seal_result {
            BulkSealResult::NeedsAUs => {
                BranchBetreeBulkSealResult::NeedsAUs
            },
            BulkSealResult::CacheFull => {
                BranchBetreeBulkSealResult::CacheFull
            },
            BulkSealResult::Blocked => {
                BranchBetreeBulkSealResult::Blocked
            },
            BulkSealResult::InvalidPage => {
                BranchBetreeBulkSealResult::InvalidPage
            },
            BulkSealResult::Sealed {
                root,
                aux_ptr,
                prepared_cache,
                writes,
                event,
                deallocs,
                branch,
            } => {
                let ghost access = PageAccess {
                    betree_reads: Map::empty(),
                    branch_reads: Map::empty(),
                    betree_writes: Map::empty(),
                    branch_writes: writes@,
                };
                proof {
                    assert(access.wf());
                    assert(access.reads()
                        == Map::<Address, RawPage>::empty());
                    assert_maps_equal!(access.writes(), writes@, addr => {});
                    assert(CachedBranchBetree::State::branch_build(
                        old(self).betree_i(),
                        self.betree_i(),
                        CachedBranchBetree::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: iau_vec_set(deallocs@),
                            access: access.cached_access(),
                        },
                        idx as int,
                        self.wip_branches@[idx as int]@,
                        event@,
                    )) by {

                    }
                    reveal(CachedBranchBetree::State::next);
                    reveal(CachedBranchBetree::State::next_by);
                    assert(CachedBranchBetree::State::next_by(
                        old(self).betree_i(),
                        self.betree_i(),
                        CachedBranchBetree::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: iau_vec_set(deallocs@),
                            access: access.cached_access(),
                        },
                        CachedBranchBetree::Step::branch_build(
                            idx as int,
                            self.wip_branches@[idx as int]@,
                            event@,
                        ),
                    ));
                    assert(CachedBranchBetree::State::next(
                        old(self).betree_i(),
                        self.betree_i(),
                        CachedBranchBetree::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: iau_vec_set(deallocs@),
                            access: access.cached_access(),
                        },
                    ));
                    assert(AtomicBranchBetreeState::State::next_by(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: iau_vec_set(deallocs@),
                            access,
                        },
                        AtomicBranchBetreeState::Step::branch_build(
                            self.betree_i(),
                            idx as int,
                            self.wip_branches@[idx as int]@,
                            event@,
                        ),
                    )) by {
                        reveal(AtomicBranchBetreeState::State::next_by);
                    }
                    assert(AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: iau_vec_set(deallocs@),
                            access,
                        },
                    )) by {
                        reveal(AtomicBranchBetreeState::State::next);
                    }
                    assert(bulk_builders_wf(
                        self.wip_branches@,
                        &self.memtable,
                    )) by {
                        assert forall |i: int|
                            0 <= i < self.wip_branches@.len()
                            implies (#[trigger] self.wip_branches@[i])
                                .bulk_builder_wf(&self.memtable) by {
                            if i == idx as int {
                                assert(self.wip_branches@[i]
                                    .bulk_builder is None);
                            } else {
                                assert(self.wip_branches@[i]
                                    == old_branches[i]);
                            }
                        }
                    }
                    assert(self.wip_branches@[idx as int]
                        .sealed_branch@ == Some(branch@));

                    assert(self.wf());
                }
                BranchBetreeBulkSealResult::Sealed {
                    idx,
                    root,
                    aux_ptr,
                    prepared_cache,
                    access: Ghost(access),
                    event,
                    deallocs,
                    branch,
                }
            },
        }
    }

    /* Old single-leaf prototype retained for reference. The live flush path
     * uses branch_begin_bulk_build followed by incremental page staging.
    /* Preserved in the legacy WipBranchImpl_v integration for a possible
     * branch-as-memtable design. The active path streams StagePage events and
     * finishes with BulkSeal.
    pub fn branch_build_memtable_leaf(
        &mut self,
        cache: &mut FracCacheImpl,
        idx: usize,
        disk_au_count: IAU,
        disk_page_count: crate::spec::ImplDisk_t::IPage,
    ) -> (result: BranchBetreeBuildResult)
        requires
            old(self).wf(),
            old(self).control.metadata_loaded,
            idx < old(self).wip_branches.len(),
            !old(self).wip_branches@[idx as int].sealed,
            old(self).wip_branches@[idx as int].root is None,
            old(self).wip_branches@[idx as int].bulk_builder is None,
            old(self).wip_branches@[idx as int]
                .mini_allocator.bounded(disk_au_count),
            old(self).wip_branches@[idx as int]
                .mini_allocator.i().allocated_aus().is_empty(),
            old(cache).wf(),
            0 < disk_page_count as nat,
            disk_page_count as nat
                == crate::disk::GenericDisk_v::page_count(),
        ensures
            self.wf(),
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            match result {
                BranchBetreeBuildResult::Applied {
                    idx: post_idx,
                    prepared_cache,
                    access,
                    event,
                } => {
                    &&& post_idx == idx
                    &&& access@.wf()
                    &&& access@.betree_reads.is_empty()
                    &&& access@.betree_writes.is_empty()
                    &&& access@.branch_reads.is_empty()
                    &&& self.wip_branches@[idx as int]
                        .cache_inv(cache@)
                    &&& self.wip_branches@[idx as int]
                        .represents_buffer(self.memtable@.buffer)
                    &&& self.wip_branches@[idx as int]
                        .cache_inv(cache@)
                    &&& Cache::State::next(
                        old(cache)@,
                        prepared_cache@,
                        Cache::Label::Internal,
                    )
                    &&& Cache::State::next(
                        prepared_cache@,
                        cache@,
                        Cache::Label::Access {
                            reads: access@.reads(),
                            writes: access@.writes(),
                        },
                    )
                    &&& AtomicBranchBetreeState::State::branch_build(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: Set::empty(),
                            access: access@,
                        },
                        self.betree_i(),
                        idx as int,
                        self.wip_branches@[idx as int]@,
                        event@,
                    )
                },
                BranchBetreeBuildResult::NeedsAUs
                | BranchBetreeBuildResult::CacheFull
                | BranchBetreeBuildResult::Blocked
                | BranchBetreeBuildResult::InvalidPage => {
                    &&& self@ == old(self)@
                    &&& cache@ == old(cache)@
                },
            },
    {
        let memtable_empty = self.memtable.is_empty();
        if memtable_empty {
            proof { assert(cache@ == old(cache)@); }
            return BranchBetreeBuildResult::Blocked;
        }
        let entries = self.memtable.flatten_sorted();
        proof {
            if entries@.len() == 0 {
                assert(MemtableBucket::entries_map(entries@)
                    == Map::<Key, Message>::empty());
                assert(self.memtable@.buffer.map.is_empty());
                assert(self.memtable@.is_empty());
                assert(false);
            }
        }
        let contents = WipLeafContents::from_sorted_entries(&entries);
        let ghost old_branches = self.wip_branches@;
        let mut branch = self.wip_branches.remove(idx);
        let build_result = branch.initialize_leaf_with_cache(
            cache,
            contents,
            disk_au_count,
            disk_page_count,
        );
        self.wip_branches.insert(idx, branch);
        proof {
            assert(self.wip_branches@
                == old_branches.update(
                    idx as int,
                    self.wip_branches@[idx as int],
                ));
            assert(bulk_branch_views(self.wip_branches@)
                == bulk_branch_views(old_branches).update(
                    idx as int,
                    self.wip_branches@[idx as int]@,
                ));
        }
        match build_result {
            BulkBranchInitializeResult::NeedsAUs => {
                BranchBetreeBuildResult::NeedsAUs
            },
            BulkBranchInitializeResult::CacheFull => {
                BranchBetreeBuildResult::CacheFull
            },
            BulkBranchInitializeResult::Blocked => {
                BranchBetreeBuildResult::Blocked
            },
            BulkBranchInitializeResult::Initialized {
                root: _,
                prepared_cache,
                writes,
                event,
            } => {
                let ghost access = PageAccess {
                    betree_reads: Map::empty(),
                    branch_reads: Map::empty(),
                    betree_writes: Map::empty(),
                    branch_writes: writes@,
                };
                proof {
                    assert(access.wf());
                    assert(access.reads() == Map::<Address, RawPage>::empty());
                    assert_maps_equal!(access.writes(), writes@, addr => {});
                    assert(CachedBranchBetree::State::branch_build(
                        old(self).betree_i(),
                        self.betree_i(),
                        CachedBranchBetree::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: Set::empty(),
                            access: access.cached_access(),
                        },
                        idx as int,
                        self.wip_branches@[idx as int]@,
                        event@,
                    )) by {

                    }
                    MemtableBucket::sorted_entries_form_buffer(
                        entries@,
                        self.memtable@.buffer,
                    );
                    assert(self.wip_branches@[idx as int]
                        .represents_buffer(self.memtable@.buffer));

                    assert(self.wf());
                }
                BranchBetreeBuildResult::Applied {
                    idx,
                    prepared_cache,
                    access: Ghost(access),
                    event,
                }
            },
        }
    }

    pub fn branch_seal_leaf(
        &mut self,
        cache: &mut FracCacheImpl,
        idx: usize,
    ) -> (result: BranchBetreeBuildResult)
        requires
            old(self).wf(),
            old(self).control.metadata_loaded,
            idx < old(self).wip_branches.len(),
            !old(self).wip_branches@[idx as int].sealed,
            old(self).wip_branches@[idx as int].root is Some,
            old(self).wip_branches@[idx as int].cache_inv(old(cache)@),
            old(self).wip_branches@[idx as int]
                .represents_buffer(old(self).memtable@.buffer),
            old(self).wip_branches@[idx as int]
                .mini_allocator.i().all_aus()
                == old(self).wip_branches@[idx as int]
                    .mini_allocator.i().allocated_aus(),
            old(cache).wf(),
        ensures
            self.wf(),
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            match result {
                BranchBetreeBuildResult::Applied {
                    idx: post_idx,
                    prepared_cache,
                    access,
                    event,
                } => {
                    &&& post_idx == idx
                    &&& prepared_cache@ == old(cache)@
                    &&& access@.wf()
                    &&& access@.read_only()
                    &&& access@.betree_reads.is_empty()
                    &&& access@.betree_writes.is_empty()
                    &&& access@.branch_writes.is_empty()
                    &&& self.wip_branches@[idx as int]
                        .represents_buffer(self.memtable@.buffer)
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        Cache::Label::Access {
                            reads: access@.reads(),
                            writes: access@.writes(),
                        },
                    )
                    &&& AtomicBranchBetreeState::State::branch_build(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: Set::empty(),
                            access: access@,
                        },
                        self.betree_i(),
                        idx as int,
                        self.wip_branches@[idx as int]@,
                        event@,
                    )
                },
                BranchBetreeBuildResult::NeedsAUs
                | BranchBetreeBuildResult::CacheFull
                | BranchBetreeBuildResult::Blocked
                | BranchBetreeBuildResult::InvalidPage => {
                    &&& self@ == old(self)@
                    &&& cache@ == old(cache)@
                },
            },
    {
        let ghost old_branches = self.wip_branches@;
        let mut branch = self.wip_branches.remove(idx);
        let seal_result = branch.seal_leaf_with_cache(cache);
        self.wip_branches.insert(idx, branch);
        proof {
            assert(self.wip_branches@
                == old_branches.update(
                    idx as int,
                    self.wip_branches@[idx as int],
                ));
            assert(bulk_branch_views(self.wip_branches@)
                == bulk_branch_views(old_branches).update(
                    idx as int,
                    self.wip_branches@[idx as int]@,
                ));
        }
        match seal_result {
            BulkBranchSealResult::CacheFull => {
                BranchBetreeBuildResult::CacheFull
            },
            BulkBranchSealResult::Blocked => {
                BranchBetreeBuildResult::Blocked
            },
            BulkBranchSealResult::InvalidPage => {
                BranchBetreeBuildResult::InvalidPage
            },
            BulkBranchSealResult::Sealed { reads, event } => {
                let ghost access = PageAccess {
                    betree_reads: Map::empty(),
                    branch_reads: reads@,
                    betree_writes: Map::empty(),
                    branch_writes: Map::empty(),
                };
                proof {
                    assert(access.wf());
                    assert(access.read_only());
                    assert_maps_equal!(access.reads(), reads@, addr => {});
                    assert(access.writes() == Map::<Address, RawPage>::empty());
                    assert(CachedBranchBetree::State::branch_build(
                        old(self).betree_i(),
                        self.betree_i(),
                        CachedBranchBetree::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: Set::empty(),
                            access: access.cached_access(),
                        },
                        idx as int,
                        self.wip_branches@[idx as int]@,
                        event@,
                    )) by {

                    }
                    assert(self.wip_branches@[idx as int].root_node
                        == old(self).wip_branches@[idx as int].root_node);
                    assert(self.memtable@ == old(self).memtable@);

                    assert(self.wf());
                }
                BranchBetreeBuildResult::Applied {
                    idx,
                    prepared_cache: Ghost(old(cache)@),
                    access: Ghost(access),
                    event,
                }
            },
        }
    }

    */

    */

    pub fn flush_initial_memtable_with_cache(
        &mut self,
        cache: &mut FracCacheImpl,
        idx: usize,
        new_root_addr: IAddress,
    ) -> (result: BranchBetreeFlushResult)
        requires
            old(self).wf(),
            old(self).control.metadata_loaded,
            old(self).root is None,
            no_bulk_builders(old(self).wip_branches@),
            idx < old(self).wip_branches.len(),
            old(self).wip_branches@[idx as int].wf(),
            old(self).wip_branches@[idx as int].sealed,
            old(self).wip_branches@[idx as int].root is Some,
            old(self).wip_branches@[idx as int].cache_inv(old(cache)@),
            old(self).wip_branches@[idx as int]
                .sealed_branch@ is Some,
            old(self).wip_branches@[idx as int]
                .sealed_branch@.unwrap().i().i().map
                    == old(self).memtable@.buffer.map,
            old(self).ownership.betree.all_aus().disjoint(
                old(self).wip_branches@[idx as int]
                    .mini_allocator.i().all_aus(),
            ),
            old(self).ownership.branches.all_summary_aus().disjoint(
                old(self).wip_branches@[idx as int]
                    .mini_allocator.i().all_aus(),
            ),
            new_root_addr@.wf(),
            betree_node_addr(new_root_addr@),
            old(self).ownership.betree.all_aus().disjoint(
                set![new_root_addr@.au],
            ),
            old(self).ownership.branches.all_summary_aus().disjoint(
                set![new_root_addr@.au],
            ),
            old(self).wip_branches@[idx as int]
                .mini_allocator.i().all_aus().disjoint(
                    set![new_root_addr@.au],
                ),
            old(self).betree_i().is_fresh(set![new_root_addr@.au]),
            old(cache).wf(),
        ensures
            self.wf(),
            self.compactors@ == old(self).compactors@,
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            match result {
                BranchBetreeFlushResult::Flushed {
                    new_root,
                    prepared_cache,
                    access,
                    allocs,
                    deallocs,
                } => {
                    &&& new_root == new_root_addr
                    &&& allocs@ == set![new_root_addr@.au]
                    &&& deallocs@ == Set::<AU>::empty()
                    &&& self.root == Some(new_root_addr)
                    &&& self.wip_branches@
                        == old(self).wip_branches@.remove(idx as int)
                    &&& self.memtable@ == old(self).memtable@.drain()
                    &&& self.memtable.seq_end == old(self).memtable.seq_end
                    &&& self.control == old(self).control
                    &&& self.ownership.betree.all_aus()
                        <= old(self).ownership.betree.all_aus()
                            + allocs@
                    &&& self.ownership.branches.all_summary_aus()
                        <= old(self).ownership.branches.all_summary_aus()
                            + old(self).wip_branches@[idx as int]
                                .mini_allocator.i().all_aus()
                    &&& self.ownership.betree.all_aus()
                            + self.ownership.branches.all_summary_aus()
                        <= old(self).ownership.betree.all_aus()
                            + old(self).ownership.branches.all_summary_aus()
                            + allocs@
                            + old(self).wip_branches@[idx as int]
                                .mini_allocator.i().all_aus()
                    &&& access@.wf()
                    &&& access@.branch_writes.is_empty()
                    &&& Cache::State::next(
                        old(cache)@,
                        prepared_cache@,
                        Cache::Label::Internal,
                    )
                    &&& Cache::State::next(
                        prepared_cache@,
                        cache@,
                        Cache::Label::Access {
                            reads: access@.reads(),
                            writes: access@.writes(),
                        },
                    )
                    &&& AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: allocs@,
                            deallocs: deallocs@,
                            access: access@,
                        },
                    )
                },
                BranchBetreeFlushResult::CacheFull
                | BranchBetreeFlushResult::Blocked
                | BranchBetreeFlushResult::InvalidPage => {
                    &&& self@ == old(self)@
                    &&& self.ownership == old(self).ownership
                    &&& self.wip_branches@ == old(self).wip_branches@
                    &&& cache@ == old(cache)@
                },
            },
    {
        let ghost pre_state = self@;
        let ghost pre_impl = *self;
        let ghost pre_betree = self.betree_i();
        let ghost pre_branch_likes = self.branch_likes@;
        let ghost pre_wip_seq = self.wip_branches@;
        let ghost cache0 = *cache;
        let ghost pre_wip = self.wip_branches@[idx as int];
        let ghost pre_memtable = self.memtable@;
        let branch_root = self.wip_branches[idx].root.unwrap();
        let ghost branch_reads = pre_wip.sealed_branch_reads(cache0@);
        let node = match build_initial_betree_root(branch_root) {
            Some(node) => node,
            None => return BranchBetreeFlushResult::InvalidPage,
        };
        let ghost borrowed_cache;
        let ghost prepared_cache;
        let mut reserved = false;
        let mut handle = if cache.contains_addr(&new_root_addr) {
            match cache.fetch(&new_root_addr, false) {
                FetchErrorCode::Success { slot_handle } => {
                    proof {
                        borrowed_cache = *cache;
                        prepared_cache = cache0@;
                        FracCacheImpl::valid_write_handle_model_entry(
                            &borrowed_cache,
                            &new_root_addr,
                            slot_handle,
                        );
                    }
                    slot_handle
                },
                FetchErrorCode::CacheFull => {
                    return BranchBetreeFlushResult::CacheFull;
                },
                FetchErrorCode::Awaiting | FetchErrorCode::NotPresent => {
                    return BranchBetreeFlushResult::Blocked;
                },
                FetchErrorCode::LoadInitiate { slot_handle: _ } => {
                    proof { assert(false); }
                    return BranchBetreeFlushResult::Blocked;
                },
            }
        } else {
            reserved = true;
            match cache.reserve_for_write_absent(&new_root_addr) {
                ReserveWriteResult::Reserved { slot_handle } => {
                    proof {
                        borrowed_cache = *cache;
                        prepared_cache = cache@;
                    }
                    slot_handle
                },
                ReserveWriteResult::CacheFull => {
                    return BranchBetreeFlushResult::CacheFull;
                },
            }
        };
        let ghost write_slot = handle.idx;
        let page = marshall_betree_node_page(&node);
        let ghost writes = map![new_root_addr@ => page@];
        handle.rec = page;
        proof {
            assert(cache.valid_write_handle(&new_root_addr, handle));
            assert(cache@.valid_write(new_root_addr@));
        }
        cache.write_release(&new_root_addr, handle);
        proof {
            if !reserved {
                reveal(Cache::State::next);
                reveal(Cache::State::next_by);
                assert(Cache::State::next_by(
                    cache0@,
                    prepared_cache,
                    Cache::Label::Internal,
                    Cache::Step::noop(),
                ));
                assert(Cache::State::next(
                    cache0@,
                    prepared_cache,
                    Cache::Label::Internal,
                ));
            }
            assert forall |addr: Address|
                #[trigger] branch_reads.contains_key(addr)
                implies prepared_cache.valid_read(addr, branch_reads[addr]) by {
                assert(addr != new_root_addr@) by {
                    if addr == new_root_addr@ {
                        assert(to_branch_nodes(branch_reads)
                            .contains_key(addr));
                        assert(pre_wip.sealed_branch@.unwrap()
                            .disk_view.entries.contains_key(addr));
                        assert(pre_wip.sealed_branch@.unwrap()
                            .full_repr().contains(addr));
                        assert(pre_wip.mini_allocator.i().all_aus()
                            .contains(addr.au));
                        assert(set![new_root_addr@.au].contains(addr.au));
                    }
                }
                assert(cache0@.valid_read(addr, branch_reads[addr]));
            }
            if reserved {
                Cache::State::access_add_reads(
                    prepared_cache,
                    cache@,
                    branch_reads,
                    writes,
                );
            } else {
                Cache::State::access_from_borrowed_write_slot(
                    cache0@,
                    borrowed_cache@,
                    cache@,
                    branch_reads,
                    new_root_addr@,
                    write_slot,
                    page@,
                );
            }
        }

        let summary = self.wip_branches[idx].mini_allocator.all_aus_vec();
        proof {
            assert(!self.ownership.branches.active@
                .contains_key(branch_root@.au)) by {
                if self.ownership.branches.active@
                    .contains_key(branch_root@.au)
                {
                    self.ownership.branches.root_record_is_owned(
                        branch_root@.au,
                    );
                    assert(pre_wip.mini_allocator.i().all_aus()
                        .contains(branch_root@.au));
                }
            }
            self.ownership.branches.active_summary_map_dom();
            assert(!pre_branch_likes.dom().contains(branch_root@.au));
            assert(pre_branch_likes.count(branch_root@.au) == 0);
        }
        let betree_allocated = self.ownership.allocate_betree_au(
            new_root_addr.au,
        );
        match betree_allocated {
            BetreeOwnershipUpdateResult::Applied { reclaimed: _ } => {},
            BetreeOwnershipUpdateResult::Noop => {
                proof { assert(false); }
                return BranchBetreeFlushResult::Blocked;
            },
        }
        let branch_added = self.ownership.add_ephemeral_branch(
            branch_root.au,
            summary,
        );
        match branch_added {
            BranchOwnershipUpdateResult::Applied { reclaimed: _ } => {},
            BranchOwnershipUpdateResult::Noop => {
                proof { assert(false); }
                return BranchBetreeFlushResult::Blocked;
            },
        }
        let like_added = self.branch_likes.increment(branch_root.au);
        match like_added {
            AuLikesUpdateResult::Applied { became_zero: _ } => {},
            AuLikesUpdateResult::Noop => {
                proof { assert(false); }
                return BranchBetreeFlushResult::Blocked;
            },
        }
        self.wip_branches.remove(idx);
        self.memtable.drain();
        self.root = Some(new_root_addr);

        let ghost access = PageAccess {
            betree_reads: Map::empty(),
            branch_reads,
            betree_writes: writes,
            branch_writes: Map::empty(),
        };
        let ghost allocs = set![new_root_addr@.au];
        let ghost deallocs = Set::<AU>::empty();
        proof {
            broadcast use vstd::multiset::group_multiset_axioms;
            assert(access.wf()) by {
            }
            assert_maps_equal!(access.reads(), branch_reads, addr => {});
            assert_maps_equal!(access.writes(), writes, addr => {});
            assert(Cache::State::next(
                prepared_cache,
                cache@,
                Cache::Label::Access {
                    reads: access.reads(),
                    writes: access.writes(),
                },
            ));
            assert(to_betree_nodes(writes)[new_root_addr@] == node@);
            assert(node@ == crate::betree::LinkedBetree_v::BetreeNode::empty_root(
                crate::betree::Domain_v::total_domain(),
            ).extend_buffer_seq(crate::betree::LinkedSeq_v::LinkedSeq {
                addrs: seq![branch_root@],
            }));
            assert(to_betree_nodes(writes)
                == crate::implementation::CachedBranchBetree_v::flush_memtable_writes(
                    None,
                    branch_root@,
                    new_root_addr@,
                    Map::empty(),
                )) by {
                assert_maps_equal!(
                    to_betree_nodes(writes),
                    crate::implementation::CachedBranchBetree_v::flush_memtable_writes(
                        None,
                        branch_root@,
                        new_root_addr@,
                        Map::empty(),
                    ),
                    addr => {}
                );
            }
            pre_wip.sealed_branch_reads_valid(branch_reads);
            assert(loaded_sealed_branch(
                branch_root@,
                to_branch_nodes(branch_reads).restrict(
                    addresses_in_aus(
                        pre_wip.mini_allocator.i().all_aus(),
                    ),
                ),
            ).i().i().map == pre_memtable.buffer.map);
            assert(self.ownership.betree@
                == pre_betree.betree_aus.insert(new_root_addr@.au));
            assert(self.branch_likes@
                == pre_branch_likes.insert(branch_root@.au));
            assert(self.ownership.branches@
                == pre_betree.branch_summary.insert(
                    branch_root@.au,
                    pre_wip.mini_allocator.i().all_aus(),
                ));
            assert(self.branch_likes@.dom()
                =~= pre_branch_likes.dom().insert(branch_root@.au));
            self.ownership.branches.active_summary_map_dom();
            assert(self.ownership.branches.active_summary_map().dom()
                =~= pre_betree.branch_summary.dom().insert(
                    branch_root@.au,
                ));
            assert(self.branch_likes@.dom()
                == self.ownership.branches.active_summary_map().dom());
            assert(self.wip_branches@
                == pre_wip_seq.remove(idx as int));
            assert(bulk_branch_views(self.wip_branches@)
                == pre_betree.wip_branches.remove(idx as int)) by {
                assert_seqs_equal!(
                    bulk_branch_views(self.wip_branches@),
                    pre_betree.wip_branches.remove(idx as int),
                    i => {
                        if i < idx {
                            assert(self.wip_branches@[i]
                                == pre_wip_seq[i]);
                        } else {
                            assert(self.wip_branches@[i]
                                == pre_wip_seq[i + 1]);
                        }
                    }
                );
            }
            assert(self.memtable@ == pre_betree.memtable.drain());
            assert(pre_betree.root is None);
            to_au_likes_empty();
            assert(pre_betree.betree_aus.sub(AULikes::empty())
                == pre_betree.betree_aus);
            assert(pre_betree.betree_aus.sub(to_au_likes(
                Multiset::<Address>::empty(),
            )).insert(new_root_addr@.au)
                == self.ownership.betree@);
            assert(pre_betree.betree_aus.dom()
                <= self.ownership.betree@.dom());
            assert(pre_betree.betree_aus.dom()
                - self.ownership.betree@.dom()
                =~= Set::<AU>::empty());
            self.ownership.current_durable_matches_views(
                self.branch_likes@,
            );
            assert(self.ownership.current_durable_aus()
                == self.betree_i().durable_aus());
            access.cached_no_branch_writes_shape();
            assert(access.loaded_betree_reads()
                == to_betree_nodes(Map::<Address, RawPage>::empty()));
            assert(access.loaded_betree_writes() == to_betree_nodes(writes));
            assert(access.loaded_branch_reads() == to_branch_nodes(branch_reads));
            assert(access.cached_access() == CachedBranchBetreeAccess {
                betree_reads: to_betree_nodes(
                    Map::<Address, RawPage>::empty(),
                ),
                branch_reads: to_branch_nodes(branch_reads),
                betree_writes: to_betree_nodes(writes),
                branch_writes: Map::empty(),
            });
            assert(CachedBranchBetree::State::flush_memtable(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access: access.cached_access(),
                },
                idx as int,
                new_root_addr@,
                access.loaded_betree_reads(),
                access.loaded_betree_writes(),
                access.loaded_branch_reads(),
            )) by {

            }
            assert(CachedBranchBetree::State::next_by(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access: access.cached_access(),
                },
                CachedBranchBetree::Step::flush_memtable(
                    idx as int,
                    new_root_addr@,
                    access.loaded_betree_reads(),
                    access.loaded_betree_writes(),
                    access.loaded_branch_reads(),
                ),
            )) by {
                reveal(CachedBranchBetree::State::next_by);
            }
            assert(CachedBranchBetree::State::next(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access: access.cached_access(),
                },
            )) by {
                reveal(CachedBranchBetree::State::next);
            }
            pre_impl.ownership.branches.active_summary_projection();
            pre_impl.ownership.branches.ownership_sets_bounded();
            assert(summary_aus(pre_betree.branch_summary)
                <= pre_impl.ownership.branches.all_summary_aus());
            assert(pre_wip.mini_allocator.i().all_aus()
                .contains(branch_root@.au));
            compactor_model_alignment_insert_fresh_summary(
                pre_impl.compactors@,
                pre_betree.branch_summary,
                branch_root@.au,
                pre_wip.mini_allocator.i().all_aus(),
                pre_impl.ownership.branches.all_summary_aus(),
            );
            assert(self.ownership.branches.active_summary_map()
                == pre_betree.branch_summary.insert(
                    branch_root@.au,
                    pre_wip.mini_allocator.i().all_aus(),
                ));
            assert(compactor_model_alignment(
                self.compactors@,
                self.ownership.branches.active_summary_map(),
            ));
            assert(self.wf());
            assert(AtomicBranchBetreeState::State::next_by(
                pre_state,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access,
                },
                AtomicBranchBetreeState::Step::flush_memtable(
                    self.betree_i(),
                    idx as int,
                    new_root_addr@,
                    access.loaded_betree_reads(),
                    access.loaded_betree_writes(),
                    access.loaded_branch_reads(),
                ),
            )) by {
                reveal(AtomicBranchBetreeState::State::next_by);
            }
            assert(AtomicBranchBetreeState::State::next(
                pre_state,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access,
                },
            )) by {
                reveal(AtomicBranchBetreeState::State::next);
            }
        }
        BranchBetreeFlushResult::Flushed {
            new_root: new_root_addr,
            prepared_cache: Ghost(prepared_cache),
            access: Ghost(access),
            allocs: Ghost(allocs),
            deallocs: Ghost(deallocs),
        }
    }

    pub fn flush_existing_memtable_with_cache(
        &mut self,
        cache: &mut FracCacheImpl,
        idx: usize,
        new_root_addr: IAddress,
    ) -> (result: BranchBetreeExistingFlushResult)
        requires
            old(self).wf(),
            old(self).control.metadata_loaded,
            old(self).root is Some,
            no_bulk_builders(old(self).wip_branches@),
            idx < old(self).wip_branches.len(),
            old(self).wip_branches@[idx as int].sealed,
            old(self).wip_branches@[idx as int].root is Some,
            old(self).wip_branches@[idx as int].cache_inv(old(cache)@),
            old(self).wip_branches@[idx as int]
                .sealed_branch@ is Some,
            old(self).wip_branches@[idx as int]
                .sealed_branch@.unwrap().i().i().map
                    == old(self).memtable@.buffer.map,
            old(self).ownership.betree.active_aus().contains(
                old(self).root.unwrap()@.au,
            ),
            old(self).ownership.betree.all_aus().disjoint(
                old(self).wip_branches@[idx as int]
                    .mini_allocator.i().all_aus(),
            ),
            old(self).ownership.branches.all_summary_aus().disjoint(
                old(self).wip_branches@[idx as int]
                    .mini_allocator.i().all_aus(),
            ),
            new_root_addr@.wf(),
            betree_node_addr(new_root_addr@),
            old(self).ownership.betree.all_aus().disjoint(
                set![new_root_addr@.au],
            ),
            old(self).ownership.branches.all_summary_aus().disjoint(
                set![new_root_addr@.au],
            ),
            old(self).wip_branches@[idx as int]
                .mini_allocator.i().all_aus().disjoint(
                    set![new_root_addr@.au],
                ),
            old(self).betree_i().is_fresh(set![new_root_addr@.au]),
            cached_betree_root_wf(
                old(cache)@,
                old(self).root.unwrap()@,
            ),
            old(cache).wf(),
        ensures
            self.wf(),
            self.compactors@ == old(self).compactors@,
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            match result {
                BranchBetreeExistingFlushResult::Flushed {
                    new_root,
                    reclaimed,
                    prepared_cache,
                    access,
                    allocs,
                    deallocs,
                } => {
                    &&& new_root == new_root_addr
                    &&& allocs@ == set![new_root_addr@.au]
                    &&& deallocs@
                        == set![old(self).root.unwrap()@.au]
                    &&& unique_iau_seq(reclaimed@)
                    &&& iau_seq_set(reclaimed@)
                        == old(self).control_i().reclaimable(deallocs@)
                    &&& self.root == Some(new_root_addr)
                    &&& self.wip_branches@
                        == old(self).wip_branches@.remove(idx as int)
                    &&& self.memtable@ == old(self).memtable@.drain()
                    &&& self.memtable.seq_end == old(self).memtable.seq_end
                    &&& self.control == old(self).control
                    &&& self.ownership.betree.all_aus()
                        <= old(self).ownership.betree.all_aus()
                            + allocs@
                    &&& self.ownership.branches.all_summary_aus()
                        <= old(self).ownership.branches.all_summary_aus()
                            + old(self).wip_branches@[idx as int]
                                .mini_allocator.i().all_aus()
                    &&& self.ownership.betree.all_aus()
                            + self.ownership.branches.all_summary_aus()
                        <= old(self).ownership.betree.all_aus()
                            + old(self).ownership.branches.all_summary_aus()
                            + allocs@
                            + old(self).wip_branches@[idx as int]
                                .mini_allocator.i().all_aus()
                    &&& access@.wf()
                    &&& access@.branch_writes.is_empty()
                    &&& Cache::State::next(
                        old(cache)@,
                        prepared_cache@,
                        Cache::Label::Internal,
                    )
                    &&& Cache::State::next(
                        prepared_cache@,
                        cache@,
                        Cache::Label::Access {
                            reads: access@.reads(),
                            writes: access@.writes(),
                        },
                    )
                    &&& AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: allocs@,
                            deallocs: deallocs@,
                            access: access@,
                        },
                    )
                },
                BranchBetreeExistingFlushResult::NeedCacheLoad {
                    addr,
                    handle,
                } => {
                    &&& self@ == old(self)@
                    &&& self.ownership == old(self).ownership
                    &&& self.wip_branches@ == old(self).wip_branches@
                    &&& addr == old(self).root.unwrap()
                    &&& self.wip_branches@[idx as int].cache_inv(cache@)
                    &&& cache.entry_fetched(&addr)
                    &&& cache.valid_load_handle(&addr, handle)
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        crate::implementation::FracCacheImpl_v::cache_load_label(
                            &addr,
                        ),
                    )
                },
                BranchBetreeExistingFlushResult::CacheFull
                | BranchBetreeExistingFlushResult::Blocked
                | BranchBetreeExistingFlushResult::InvalidPage => {
                    &&& self@ == old(self)@
                    &&& self.ownership == old(self).ownership
                    &&& self.wip_branches@ == old(self).wip_branches@
                    &&& cache@ == old(cache)@
                },
            },
    {
        let ghost pre_state = self@;
        let ghost pre_impl = *self;
        let ghost pre_betree = self.betree_i();
        let ghost pre_branch_likes = self.branch_likes@;
        let ghost pre_wip_seq = self.wip_branches@;
        let ghost pre_wip = self.wip_branches@[idx as int];
        let ghost pre_memtable = self.memtable@;
        let ghost pre_betree_all = self.ownership.betree.all_aus();
        let ghost cache0 = *cache;
        let old_root = self.root.unwrap();
        let branch_root = self.wip_branches[idx].root.unwrap();
        let ghost branch_reads = pre_wip.sealed_branch_reads(cache0@);
        proof {
            self.ownership.betree.view_domain_matches_active();
            self.ownership.betree.view_count_matches_active(
                old_root@.au,
            );
            assert(pre_betree.betree_aus.dom().contains(old_root@.au));
            assert(pre_betree.betree_aus.count(old_root@.au) == 1);
            assert(old_root@.au != new_root_addr@.au);
            assert(old_root@ != new_root_addr@);
        }
        let root_result = extend_root_buffer_with_cache(
            cache,
            old_root,
            new_root_addr,
            branch_root,
        );
        let (prepared_cache, betree_reads, betree_writes) = match root_result {
            BetreeRootExtendResult::Extended {
                prepared_cache,
                reads,
                writes,
            } => (prepared_cache, reads, writes),
            BetreeRootExtendResult::NeedCacheLoad { addr, handle } => {
                proof {

                    assert(self.wip_branches@[idx as int]
                        .cache_inv(cache@));
                }
                return BranchBetreeExistingFlushResult::NeedCacheLoad {
                    addr,
                    handle,
                };
            },
            BetreeRootExtendResult::CacheFull => {
                return BranchBetreeExistingFlushResult::CacheFull;
            },
            BetreeRootExtendResult::Blocked => {
                return BranchBetreeExistingFlushResult::Blocked;
            },
            BetreeRootExtendResult::InvalidPage => {
                return BranchBetreeExistingFlushResult::InvalidPage;
            },
        };
        proof {
            assert forall |addr: Address|
                #[trigger] branch_reads.contains_key(addr)
                    && !betree_reads@.contains_key(addr)
                implies prepared_cache@.valid_read(
                    addr,
                    branch_reads[addr],
                ) by {
                assert(addr != new_root_addr@) by {
                    if addr == new_root_addr@ {
                        assert(to_branch_nodes(branch_reads)
                            .contains_key(addr));
                        assert(pre_wip.sealed_branch@.unwrap()
                            .disk_view.entries.contains_key(addr));
                        assert(pre_wip.sealed_branch@.unwrap()
                            .full_repr().contains(addr));
                        assert(pre_wip.mini_allocator.i().all_aus()
                            .contains(addr.au));
                        assert(set![new_root_addr@.au].contains(addr.au));
                    }
                }
                assert(cache0@.valid_read(addr, branch_reads[addr]));
            }
            Cache::State::access_union_prefer_right_reads(
                prepared_cache@,
                cache@,
                betree_reads@,
                branch_reads,
                betree_writes@,
            );
        }

        let summary = self.wip_branches[idx].mini_allocator.all_aus_vec();
        proof {
            assert(iau_seq_set(summary@)
                =~= pre_wip.mini_allocator.i().all_aus());
            assert(!self.ownership.branches.active@
                .contains_key(branch_root@.au)) by {
                if self.ownership.branches.active@
                    .contains_key(branch_root@.au)
                {
                    self.ownership.branches.root_record_is_owned(
                        branch_root@.au,
                    );
                }
            }
            self.ownership.branches.active_summary_map_dom();
            assert(!pre_branch_likes.dom().contains(branch_root@.au));
            assert(pre_branch_likes.count(branch_root@.au) == 0);
        }
        let replaced = self.ownership.replace_betree_au(
            old_root.au,
            new_root_addr.au,
        );
        let reclaimed = match replaced {
            BetreeOwnershipUpdateResult::Applied { reclaimed } => reclaimed,
            BetreeOwnershipUpdateResult::Noop => {
                proof { assert(false); }
                return BranchBetreeExistingFlushResult::Blocked;
            },
        };
        proof {
            assert(self.ownership.branches.all_summary_aus().disjoint(
                iau_seq_set(summary@),
            ));
            assert(self.ownership.betree.all_aus().disjoint(
                iau_seq_set(summary@),
            )) by {
                assert forall |au: AU|
                    #[trigger] self.ownership.betree.all_aus().contains(au)
                    implies !iau_seq_set(summary@).contains(au) by {
                    if au == new_root_addr@.au {
                        assert(pre_wip.mini_allocator.i().all_aus()
                            .disjoint(set![new_root_addr@.au]));
                    } else {
                        assert(pre_betree_all.contains(au));
                    }
                }
            }
        }
        let branch_added = self.ownership.add_ephemeral_branch(
            branch_root.au,
            summary,
        );
        match branch_added {
            BranchOwnershipUpdateResult::Applied { reclaimed: _ } => {},
            BranchOwnershipUpdateResult::Noop => {
                proof { assert(false); }
                return BranchBetreeExistingFlushResult::Blocked;
            },
        }
        let like_added = self.branch_likes.increment(branch_root.au);
        match like_added {
            AuLikesUpdateResult::Applied { became_zero: _ } => {},
            AuLikesUpdateResult::Noop => {
                proof { assert(false); }
                return BranchBetreeExistingFlushResult::Blocked;
            },
        }
        self.wip_branches.remove(idx);
        self.memtable.drain();
        self.root = Some(new_root_addr);

        let ghost access = PageAccess {
            betree_reads: betree_reads@,
            branch_reads,
            betree_writes: betree_writes@,
            branch_writes: Map::empty(),
        };
        let ghost allocs = set![new_root_addr@.au];
        let ghost deallocs = set![old_root@.au];
        proof {
            broadcast use vstd::multiset::group_multiset_axioms;
            assert(access.wf()) by {
                assert(betree_reads@.dom() == set![old_root@]);
                assert(betree_reads@.dom().disjoint(
                    branch_reads.dom(),
                )) by {
                    if !betree_reads@.dom().disjoint(
                        branch_reads.dom(),
                    ) {
                        let addr = choose |addr: Address|
                            betree_reads@.contains_key(addr)
                            && branch_reads.contains_key(addr);
                        assert(addr == old_root@);
                        assert(to_branch_nodes(branch_reads)
                            .contains_key(addr));
                        assert(pre_wip.sealed_branch@.unwrap()
                            .disk_view.entries.contains_key(addr));
                        assert(pre_wip.sealed_branch@.unwrap()
                            .full_repr().contains(addr));
                        assert(pre_wip.mini_allocator.i().all_aus()
                            .contains(addr.au));
                        assert(pre_betree_all.contains(addr.au));
                    }
                }
            }
            assert_maps_equal!(
                access.reads(),
                branch_reads.union_prefer_right(betree_reads@),
                addr => {}
            );
            assert(branch_reads.dom().disjoint(betree_reads@.dom()));
            assert_maps_equal!(
                branch_reads.union_prefer_right(betree_reads@),
                betree_reads@.union_prefer_right(branch_reads),
                addr => {}
            );
            assert_maps_equal!(access.writes(), betree_writes@, addr => {});
            assert(Cache::State::next(
                prepared_cache@,
                cache@,
                Cache::Label::Access {
                    reads: access.reads(),
                    writes: access.writes(),
                },
            ));
            pre_wip.sealed_branch_reads_valid(branch_reads);
            assert(loaded_sealed_branch(
                branch_root@,
                to_branch_nodes(branch_reads).restrict(
                    addresses_in_aus(
                        pre_wip.mini_allocator.i().all_aus(),
                    ),
                ),
            ).i().i().map == pre_memtable.buffer.map);
            assert(self.ownership.betree@
                == pre_betree.betree_aus.remove(old_root@.au)
                    .insert(new_root_addr@.au));
            assert(self.branch_likes@
                == pre_branch_likes.insert(branch_root@.au));
            assert(self.ownership.branches@
                == pre_betree.branch_summary.insert(
                    branch_root@.au,
                    pre_wip.mini_allocator.i().all_aus(),
                ));
            self.ownership.branches.active_summary_map_dom();
            assert(self.branch_likes@.dom()
                == self.ownership.branches.active_summary_map().dom());
            assert(self.wip_branches@ == pre_wip_seq.remove(idx as int));
            assert(bulk_branch_views(self.wip_branches@)
                == pre_betree.wip_branches.remove(idx as int)) by {
                assert_seqs_equal!(
                    bulk_branch_views(self.wip_branches@),
                    pre_betree.wip_branches.remove(idx as int),
                    i => {
                        if i < idx {
                            assert(self.wip_branches@[i] == pre_wip_seq[i]);
                        } else {
                            assert(self.wip_branches@[i]
                                == pre_wip_seq[i + 1]);
                        }
                    }
                );
            }
            assert(self.memtable@ == pre_betree.memtable.drain());
            to_au_likes_singleton(old_root@);
            assert(pre_betree.betree_aus.sub(to_au_likes(
                Multiset::singleton(old_root@),
            )).insert(new_root_addr@.au)
                == self.ownership.betree@);
            assert(pre_betree.betree_aus.dom()
                - self.ownership.betree@.dom()
                =~= deallocs) by {
                assert forall |au: AU|
                    #[trigger] (pre_betree.betree_aus.dom()
                        - self.ownership.betree@.dom()).contains(au)
                    == deallocs.contains(au) by {
                    if au == old_root@.au {
                        assert(pre_betree.betree_aus.dom().contains(au));
                        assert(pre_betree.betree_aus.count(au) == 1);
                        assert(pre_betree.betree_aus.remove(au).count(au)
                            == 0);
                        assert(new_root_addr@.au != au);
                        assert(pre_betree.betree_aus.remove(au)
                            .insert(new_root_addr@.au).count(au) == 0);
                        assert(!self.ownership.betree@.dom().contains(au));
                    } else if pre_betree.betree_aus.dom().contains(au) {
                        assert(self.ownership.betree@.dom().contains(au));
                    }
                }
            }
            self.ownership.current_durable_matches_views(
                self.branch_likes@,
            );
            assert(self.ownership.current_durable_aus()
                == self.betree_i().durable_aus());
            access.cached_no_branch_writes_shape();
            assert(access.loaded_betree_reads()
                == to_betree_nodes(betree_reads@));
            assert(access.loaded_betree_writes()
                == to_betree_nodes(betree_writes@));
            assert(access.loaded_branch_reads() == to_branch_nodes(branch_reads));
            assert(access.cached_access() == CachedBranchBetreeAccess {
                betree_reads: to_betree_nodes(betree_reads@),
                branch_reads: to_branch_nodes(branch_reads),
                betree_writes: to_betree_nodes(betree_writes@),
                branch_writes: Map::empty(),
            });
            assert(CachedBranchBetree::State::flush_memtable(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access: access.cached_access(),
                },
                idx as int,
                new_root_addr@,
                to_betree_nodes(betree_reads@),
                to_betree_nodes(betree_writes@),
                to_branch_nodes(branch_reads),
            )) by {

            }
            assert(CachedBranchBetree::State::next_by(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access: access.cached_access(),
                },
                CachedBranchBetree::Step::flush_memtable(
                    idx as int,
                    new_root_addr@,
                    to_betree_nodes(betree_reads@),
                    to_betree_nodes(betree_writes@),
                    to_branch_nodes(branch_reads),
                ),
            )) by {
                reveal(CachedBranchBetree::State::next_by);
            }
            assert(CachedBranchBetree::State::next(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access: access.cached_access(),
                },
            )) by {
                reveal(CachedBranchBetree::State::next);
            }
            assert_sets_equal!(
                iau_seq_set(reclaimed@),
                pre_state.control.reclaimable(deallocs),
                au => {


                    if au == old_root@.au {
                        pre_impl.ownership.betree.ownership_sets_bounded();
                        pre_impl.ownership.branches.ownership_sets_bounded();




                        assert(pre_betree.betree_aus.dom().contains(au));
                        assert(pre_impl.ownership.betree.active@
                            .contains_key(au));
                        assert(!pre_impl.ownership.betree.retired@
                            .contains_key(au));
                        assert(!pre_impl.ownership.branches.persistent_aus()
                            .contains(au));
                        assert(!pre_impl.ownership.branches.frozen_aus()
                            .contains(au));
                        assert(pre_impl.ownership.betree.active@[au]
                            .persistent
                            <==> pre_impl.ownership.persistent_aus()
                                .contains(au));
                        assert(pre_impl.ownership.betree.active@[au]
                            .frozen
                            <==> pre_impl.ownership.frozen_aus()
                                .contains(au));
                    }
                }
            );
            pre_impl.ownership.branches.active_summary_projection();
            pre_impl.ownership.branches.ownership_sets_bounded();
            assert(summary_aus(pre_betree.branch_summary)
                <= pre_impl.ownership.branches.all_summary_aus());
            assert(pre_wip.mini_allocator.i().all_aus()
                .contains(branch_root@.au));
            compactor_model_alignment_insert_fresh_summary(
                pre_impl.compactors@,
                pre_betree.branch_summary,
                branch_root@.au,
                pre_wip.mini_allocator.i().all_aus(),
                pre_impl.ownership.branches.all_summary_aus(),
            );
            assert(self.ownership.branches.active_summary_map()
                == pre_betree.branch_summary.insert(
                    branch_root@.au,
                    pre_wip.mini_allocator.i().all_aus(),
                ));
            assert(compactor_model_alignment(
                self.compactors@,
                self.ownership.branches.active_summary_map(),
            ));
            assert(self.wf());
            assert(AtomicBranchBetreeState::State::next_by(
                pre_state,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access,
                },
                AtomicBranchBetreeState::Step::flush_memtable(
                    self.betree_i(),
                    idx as int,
                    new_root_addr@,
                    to_betree_nodes(betree_reads@),
                    to_betree_nodes(betree_writes@),
                    to_branch_nodes(branch_reads),
                ),
            )) by {
                reveal(AtomicBranchBetreeState::State::next_by);
            }
            assert(AtomicBranchBetreeState::State::next(
                pre_state,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access,
                },
            )) by {
                reveal(AtomicBranchBetreeState::State::next);
            }

        }
        BranchBetreeExistingFlushResult::Flushed {
            new_root: new_root_addr,
            reclaimed,
            prepared_cache,
            access: Ghost(access),
            allocs: Ghost(allocs),
            deallocs: Ghost(deallocs),
        }
    }

    pub fn grow_with_cache(
        &mut self,
        cache: &mut FracCacheImpl,
        new_root_addr: IAddress,
    ) -> (result: BranchBetreeGrowResult)
        requires
            old(self).wf(),
            old(self).control.metadata_loaded,
            new_root_addr@.wf(),
            betree_node_addr(new_root_addr@),
            old(self).ownership.betree.all_aus().disjoint(
                set![new_root_addr@.au],
            ),
            old(self).ownership.branches.all_summary_aus().disjoint(
                set![new_root_addr@.au],
            ),
            old(self).betree_i().is_fresh(set![new_root_addr@.au]),
            old(cache).wf(),
        ensures
            self.wf(),
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            match result {
                BranchBetreeGrowResult::Grew {
                    new_root,
                    prepared_cache,
                    access,
                    allocs,
                } => {
                    &&& new_root == new_root_addr
                    &&& allocs@ == set![new_root_addr@.au]
                    &&& access@.wf()
                    &&& access@.only_betree()
                    &&& access@.reads().is_empty()
                    &&& Cache::State::next(
                        old(cache)@,
                        prepared_cache@,
                        Cache::Label::Internal,
                    )
                    &&& Cache::State::next(
                        prepared_cache@,
                        cache@,
                        Cache::Label::Access {
                            reads: access@.reads(),
                            writes: access@.writes(),
                        },
                    )
                    &&& AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: allocs@,
                            deallocs: Set::empty(),
                            access: access@,
                        },
                    )
                },
                BranchBetreeGrowResult::CacheFull
                | BranchBetreeGrowResult::Blocked
                | BranchBetreeGrowResult::InvalidPage => {
                    &&& self@ == old(self)@
                    &&& cache@ == old(cache)@
                },
            },
    {
        let ghost pre_betree = self.betree_i();
        let ghost cache0 = *cache;
        let node = match build_grow_betree_root(self.root) {
            Some(node) => node,
            None => return BranchBetreeGrowResult::InvalidPage,
        };
        if cache.contains_addr(&new_root_addr) {
            return BranchBetreeGrowResult::Blocked;
        }
        let mut handle = match cache.reserve_for_write_absent(&new_root_addr) {
            ReserveWriteResult::Reserved { slot_handle } => slot_handle,
            ReserveWriteResult::CacheFull => {
                return BranchBetreeGrowResult::CacheFull;
            },
        };
        let ghost prepared_cache = cache@;
        let page = marshall_betree_node_page(&node);
        let ghost writes = map![new_root_addr@ => page@];
        handle.rec = page;
        proof {
            assert(cache.valid_write_handle(&new_root_addr, handle));
            assert(cache@.valid_write(new_root_addr@));
        }
        cache.write_release(&new_root_addr, handle);
        proof {
            assert(Cache::State::next(
                prepared_cache,
                cache@,
                Cache::Label::Access {
                    reads: Map::empty(),
                    writes,
                },
            ));
        }
        let allocated = self.ownership.allocate_betree_au(
            new_root_addr.au,
        );
        match allocated {
            BetreeOwnershipUpdateResult::Applied { reclaimed: _ } => {},
            BetreeOwnershipUpdateResult::Noop => {
                proof { assert(false); }
                return BranchBetreeGrowResult::Blocked;
            },
        }
        self.root = Some(new_root_addr);
        let ghost access = PageAccess {
            betree_reads: Map::empty(),
            branch_reads: Map::empty(),
            betree_writes: writes,
            branch_writes: Map::empty(),
        };
        let ghost allocs = set![new_root_addr@.au];
        proof {
            assert(access.wf());
            assert(access.only_betree());
            assert(access.reads().is_empty());
            assert_maps_equal!(
                access.reads(),
                Map::<Address, RawPage>::empty(),
                addr => {}
            );
            assert_maps_equal!(access.writes(), writes, addr => {});
            assert(Cache::State::next(
                prepared_cache,
                cache@,
                Cache::Label::Access {
                    reads: access.reads(),
                    writes: access.writes(),
                },
            ));
            assert(to_betree_nodes(writes)
                == crate::implementation::CachedBranchBetree_v::grow_writes(
                    pre_betree.root,
                    new_root_addr@,
                )) by {
                assert_maps_equal!(
                    to_betree_nodes(writes),
                    crate::implementation::CachedBranchBetree_v::grow_writes(
                        pre_betree.root,
                        new_root_addr@,
                    ),
                    addr => {}
                );
            }
            self.ownership.current_durable_matches_views(
                self.branch_likes@,
            );
            assert(self.ownership.current_durable_aus()
                == self.betree_i().durable_aus());
            access.cached_only_betree_shape();
            assert_maps_equal!(
                access.loaded_betree_reads(),
                Map::<
                    Address,
                    crate::betree::LinkedBetree_v::BetreeNode,
                >::empty(),
                addr => {}
            );
            assert(access.loaded_betree_writes() == to_betree_nodes(writes));
            assert(access.cached_access() == CachedBranchBetreeAccess {
                betree_writes: to_betree_nodes(writes),
                ..CachedBranchBetreeAccess::empty()
            });
            assert(CachedBranchBetree::State::grow(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs,
                    deallocs: Set::empty(),
                    access: access.cached_access(),
                },
                new_root_addr@,
                to_betree_nodes(writes),
            )) by {

            }
            assert(CachedBranchBetree::State::next_by(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs,
                    deallocs: Set::empty(),
                    access: access.cached_access(),
                },
                CachedBranchBetree::Step::grow(
                    new_root_addr@,
                    to_betree_nodes(writes),
                ),
            )) by {
                reveal(CachedBranchBetree::State::next_by);
            }
            assert(CachedBranchBetree::State::next(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs,
                    deallocs: Set::empty(),
                    access: access.cached_access(),
                },
            )) by {
                reveal(CachedBranchBetree::State::next);
            }
            assert(self.wf());
            assert(AtomicBranchBetreeState::State::next_by(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs,
                    deallocs: Set::empty(),
                    access,
                },
                AtomicBranchBetreeState::Step::grow(
                    self.betree_i(),
                    new_root_addr@,
                    to_betree_nodes(writes),
                ),
            )) by {
                reveal(AtomicBranchBetreeState::State::next_by);
            }
            assert(AtomicBranchBetreeState::State::next(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs,
                    deallocs: Set::empty(),
                    access,
                },
            )) by {
                reveal(AtomicBranchBetreeState::State::next);
            }
        }
        BranchBetreeGrowResult::Grew {
            new_root: new_root_addr,
            prepared_cache: Ghost(prepared_cache),
            access: Ghost(access),
            allocs: Ghost(allocs),
        }
    }

    #[verifier::rlimit(20)]
    pub fn split_with_cache(
        &mut self,
        cache: &mut FracCacheImpl,
        key: Key,
        target_depth: usize,
        fuel: usize,
        disk_page_count: crate::spec::ImplDisk_t::IPage,
        request: &IBetreeSplitRequest,
        left_addr: IAddress,
        right_addr: IAddress,
        parent_addr: IAddress,
        path_addrs: &Vec<IAddress>,
    ) -> (result: BranchBetreeSplitResult)
        requires
            old(self).wf(),
            old(self).control.metadata_loaded,
            old(self).root is Some,
            target_depth < fuel,
            disk_page_count as nat
                == crate::disk::GenericDisk_v::page_count(),
            path_addrs@.len() == target_depth,
            cached_betree_path_prefix_valid(
                old(cache)@,
                old(self).root.unwrap()@,
                key,
                fuel as nat,
                target_depth as nat,
                old(self).ownership.betree.active_aus(),
            ),
            cached_split_parent_wf(
                old(cache)@,
                old(self).root.unwrap()@,
                key,
                target_depth as nat,
                request.i(),
                left_addr@,
                right_addr@,
            ),
            left_addr@.wf(),
            right_addr@.wf(),
            parent_addr@.wf(),
            betree_node_addr(left_addr@),
            betree_node_addr(right_addr@),
            betree_node_addr(parent_addr@),
            forall |i: int| 0 <= i < path_addrs@.len()
                ==> (#[trigger] path_addrs@[i])@.wf(),
            forall |i: int| 0 <= i < path_addrs@.len()
                ==> betree_node_addr((#[trigger] path_addrs@[i])@),
            {
                let new_addrs = SplitAddrs {
                    left: left_addr@,
                    right: right_addr@,
                    parent: parent_addr@,
                };
                &&& new_addrs.addrs_in_disjoint_aus()
                &&& to_aus(new_addrs.repr()).disjoint(
                    crate::allocation_layer::AllocationBranchBetree_v::
                        seq_addrs_to_aus(iaddr_views(path_addrs@)),
                )
                &&& seq_addrs_disjoint_aus(iaddr_views(path_addrs@))
                &&& old(self).betree_i().is_fresh(
                    to_aus(new_addrs.repr())
                        + crate::allocation_layer::AllocationBranchBetree_v::
                            seq_addrs_to_aus(iaddr_views(path_addrs@)),
                )
                &&& old(self).ownership.betree.all_aus().disjoint(
                    to_aus(new_addrs.repr())
                        + crate::allocation_layer::AllocationBranchBetree_v::
                            seq_addrs_to_aus(iaddr_views(path_addrs@)),
                )
                &&& old(self).ownership.branches.all_summary_aus().disjoint(
                    to_aus(new_addrs.repr())
                        + crate::allocation_layer::AllocationBranchBetree_v::
                            seq_addrs_to_aus(iaddr_views(path_addrs@)),
                )
            },
            old(cache).wf(),
            old(cache)@.inv(),
        ensures
            self.wf(),
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            match result {
                BranchBetreeSplitResult::Split {
                    new_root,
                    reclaimed,
                    prepared_cache,
                    access,
                    allocs,
                    deallocs,
                } => {
                    let new_addrs = SplitAddrs {
                        left: left_addr@,
                        right: right_addr@,
                        parent: parent_addr@,
                    };
                    &&& new_root@ == self.betree_i().root.unwrap()
                    &&& allocs@ == to_aus(
                        new_addrs.repr() + iaddr_views(path_addrs@).to_set(),
                    )
                    &&& deallocs@ == old(self).betree_i().betree_aus.dom()
                        - self.betree_i().betree_aus.dom()
                    &&& unique_iau_seq(reclaimed@)
                    &&& iau_seq_set(reclaimed@) <= deallocs@
                    &&& prepared_cache@ == old(cache)@
                    &&& access@.wf()
                    &&& access@.only_betree()
                    &&& Cache::State::next(
                        prepared_cache@,
                        cache@,
                        Cache::Label::Access {
                            reads: access@.reads(),
                            writes: access@.writes(),
                        },
                    )
                    &&& AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: allocs@,
                            deallocs: deallocs@,
                            access: access@,
                        },
                    )
                },
                BranchBetreeSplitResult::NeedCacheLoad { addr, handle } => {
                    &&& self@ == old(self)@
                    &&& cache.entry_fetched(&addr)
                    &&& cache.valid_load_handle(&addr, handle)
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        crate::implementation::FracCacheImpl_v::cache_load_label(
                            &addr,
                        ),
                    )
                },
                BranchBetreeSplitResult::CacheFull
                | BranchBetreeSplitResult::Blocked
                | BranchBetreeSplitResult::InvalidPage => {
                    &&& self@ == old(self)@
                    &&& cache@ == old(cache)@
                },
            },
    {
        let ghost pre_state = self@;
        let ghost pre_impl = *self;
        let ghost pre_betree = self.betree_i();
        let ghost cache0 = *cache;
        let root = self.root.unwrap();
        let ghost betree_aus = self.ownership.betree.active_aus();
        let loaded = load_betree_path(
            cache,
            root,
            key,
            target_depth,
            fuel,
            disk_page_count,
            Ghost(betree_aus),
        );
        let (path, path_reads) = match loaded {
            BetreePathLoadResult::Loaded { workspace: path, reads } => (path, reads),
            BetreePathLoadResult::NeedCacheLoad { addr, handle } => {
                return BranchBetreeSplitResult::NeedCacheLoad { addr, handle };
            },
            BetreePathLoadResult::CacheFull => {
                return BranchBetreeSplitResult::CacheFull;
            },
            BetreePathLoadResult::Blocked => {
                return BranchBetreeSplitResult::Blocked;
            },
            BetreePathLoadResult::InvalidPage => {
                return BranchBetreeSplitResult::InvalidPage;
            },
        };
        let target_idx = path.nodes.len() - 1;
        let child_idx = request.child_idx();
        if child_idx >= path.nodes[target_idx].children.len() {
            return BranchBetreeSplitResult::Blocked;
        }
        let child_addr = match path.nodes[target_idx].children[child_idx] {
            Some(addr) => addr,
            None => return BranchBetreeSplitResult::Blocked,
        };
        let ghost cache_before_child = *cache;
        let child_handle = match cache.fetch(&child_addr, true) {
            FetchErrorCode::Success { slot_handle } => slot_handle,
            FetchErrorCode::LoadInitiate { slot_handle } => {
                proof {
                    FracCacheImpl::valid_load_handles_preserved_transitive(
                        cache0,
                        cache_before_child,
                        *cache,
                    );
                }
                return BranchBetreeSplitResult::NeedCacheLoad {
                    addr: child_addr,
                    handle: slot_handle,
                };
            },
            FetchErrorCode::CacheFull => {
                proof {
                    FracCacheImpl::valid_load_handles_preserved_transitive(
                        cache0,
                        cache_before_child,
                        *cache,
                    );
                }
                return BranchBetreeSplitResult::CacheFull;
            },
            FetchErrorCode::Awaiting | FetchErrorCode::NotPresent => {
                proof {
                    FracCacheImpl::valid_load_handles_preserved_transitive(
                        cache0,
                        cache_before_child,
                        *cache,
                    );
                }
                return BranchBetreeSplitResult::Blocked;
            },
        };
        let ghost child_raw = child_handle.rec@;
        let ghost child_slot = child_handle.idx;
        let fmt = BetreeNodePageFmt::new();
        let all_slice = Slice::all(&child_handle.rec);
        let parsed = fmt.try_parse(&all_slice, &child_handle.rec);
        proof {
            if parsed is Some {
                assert(fmt == BetreeNodePageFmt::spec_new());
                assert(all_slice@.i(child_handle.rec@) == child_raw);
                assert(parsed.unwrap().parsedv() == fmt.parse(child_raw));
                assert(raw_page_to_betree_node(child_raw)
                    == parsed.unwrap()@);
            }
        }
        let ghost cache_borrowed = *cache;
        cache.handle_release(&child_addr, child_handle);
        proof {
            assert(cache@ == cache_before_child@);
            assert(cache_before_child@ == cache0@);
            FracCacheImpl::valid_load_handles_preserved_transitive(
                cache_before_child,
                cache_borrowed,
                *cache,
            );
            FracCacheImpl::valid_load_handles_preserved_transitive(
                cache0,
                cache_before_child,
                *cache,
            );
        }
        let child = match parsed {
            Some(node) => node,
            None => return BranchBetreeSplitResult::InvalidPage,
        };
        proof {
            betree_path_receipt_edges(&path);
            assert(path.receipt@.root == root@);
            assert(path.receipt@.key == key);
            assert(path.receipt@.depth() == target_depth as nat);
            assert(cached_split_parent_wf(
                cache0@,
                path.receipt@.root,
                path.receipt@.key,
                path.receipt@.depth(),
                request.i(),
                left_addr@,
                right_addr@,
            ));
            assert forall |addr: Address|
                #[trigger] path_reads@.contains_key(addr)
                implies cache0@.valid_read(addr, path_reads@[addr]) by {
                Cache::State::access_read_valid(
                    cache0@,
                    cache_before_child@,
                    path_reads@,
                    Map::empty(),
                    addr,
                );
            }
            assert(cache0@.valid_read(child_addr@, child_raw));
            assert(raw_page_to_betree_node(child_raw) == child@);
            assert(path.nodes@[target_idx as int]@
                == path.receipt@.target().node);
            assert(request.i().get_child_idx() == child_idx as nat);
            assert(path.receipt@.target().node.valid_child_index(
                request.i().get_child_idx(),
            ));
            assert(path.receipt@.target().node.children[
                request.i().get_child_idx() as int
            ] == Some(child_addr@));
            cached_split_selected_child_wf(
                cache0@,
                path.receipt@,
                path_reads@,
                request.i(),
                left_addr@,
                right_addr@,
                child_addr@,
                child_raw,
            );
            assert(child@.wf());
        }
        if !request.valid_for_child(&child) {
            return BranchBetreeSplitResult::Blocked;
        }
        proof {
            assert(split_parent_view(
                path.receipt@.target().node,
                child@,
                request.i(),
                left_addr@,
                right_addr@,
            ).wf());
            disjoint_au_views_are_unique(path_addrs@);
            crate::disk::GenericDisk_v::to_aus_domain(
                SplitAddrs {
                    left: left_addr@,
                    right: right_addr@,
                    parent: parent_addr@,
                }.repr(),
            );
            crate::disk::GenericDisk_v::to_aus_domain(
                iaddr_views(path_addrs@).to_set(),
            );
            assert(iaddr_views(path_addrs@).to_set().disjoint(
                set![left_addr@, right_addr@, parent_addr@],
            )) by {
                assert forall |addr: Address|
                    #[trigger] iaddr_views(path_addrs@).to_set().contains(addr)
                    implies !set![left_addr@, right_addr@, parent_addr@]
                        .contains(addr) by {
                    if set![left_addr@, right_addr@, parent_addr@]
                        .contains(addr)
                    {
                        assert(crate::allocation_layer::AllocationBranchBetree_v::
                            seq_addrs_to_aus(iaddr_views(path_addrs@))
                            .contains(addr.au));
                        assert(to_aus(SplitAddrs {
                            left: left_addr@,
                            right: right_addr@,
                            parent: parent_addr@,
                        }.repr()).contains(addr.au));
                    }
                }
            }
        }
        let built = match build_split_write_batch(
            &path,
            child_addr,
            &child,
            request,
            left_addr,
            right_addr,
            parent_addr,
            path_addrs,
        ) {
            Some(built) => built,
            None => return BranchBetreeSplitResult::InvalidPage,
        };
        let destinations = split_destination_addrs(
            left_addr,
            right_addr,
            parent_addr,
            path_addrs,
        );
        let ghost cache_before_prepare = *cache;
        match prepare_cache_write_addrs(cache, &destinations) {
            CacheWritePrepareResult::Ready => {
                proof {
                    FracCacheImpl::valid_load_handles_preserved_transitive(
                        cache0,
                        cache_before_prepare,
                        *cache,
                    );
                }
            },
            CacheWritePrepareResult::NeedCacheLoad { addr, handle } => {
                proof {
                    FracCacheImpl::valid_load_handles_preserved_transitive(
                        cache0,
                        cache_before_prepare,
                        *cache,
                    );
                }
                return BranchBetreeSplitResult::NeedCacheLoad { addr, handle };
            },
            CacheWritePrepareResult::CacheFull => {
                proof {
                    FracCacheImpl::valid_load_handles_preserved_transitive(
                        cache0,
                        cache_before_prepare,
                        *cache,
                    );
                }
                return BranchBetreeSplitResult::CacheFull;
            },
            CacheWritePrepareResult::Blocked => {
                proof {
                    FracCacheImpl::valid_load_handles_preserved_transitive(
                        cache0,
                        cache_before_prepare,
                        *cache,
                    );
                }
                return BranchBetreeSplitResult::Blocked;
            },
        }

        let old_addresses = append_address(&path.addrs, child_addr);
        let old_aus = iaddress_aus(&old_addresses);
        let new_aus = iaddress_aus(&destinations);
        if !crate::implementation::BranchBetreeOwnershipImpl_v::iau_vec_unique(
            &old_aus,
        ) || !crate::implementation::BranchBetreeOwnershipImpl_v::iau_vec_unique(
            &new_aus,
        ) {
            return BranchBetreeSplitResult::Blocked;
        }
        let mut old_index = 0usize;
        while old_index < old_aus.len()
            invariant
                self.wf(),
                self@ == pre_state,
                old_index <= old_aus.len(),
                forall |i: int| 0 <= i < old_index
                    ==> self.ownership.betree.active_aus().contains(
                        (#[trigger] old_aus@[i]) as nat,
                    ),
            decreases old_aus.len() - old_index,
        {
            if !self.ownership.betree.contains_active(old_aus[old_index]) {
                return BranchBetreeSplitResult::Blocked;
            }
            old_index += 1;
        }
        let mut new_index = 0usize;
        while new_index < new_aus.len()
            invariant
                self.wf(),
                self@ == pre_state,
                new_index <= new_aus.len(),
                forall |i: int| 0 <= i < new_index ==> {
                    &&& !self.ownership.betree.all_aus().contains(
                        (#[trigger] new_aus@[i]) as nat,
                    )
                    &&& !self.ownership.branches.all_summary_aus().contains(
                        new_aus@[i] as nat,
                    )
                },
            decreases new_aus.len() - new_index,
        {
            let au = new_aus[new_index];
            if self.ownership.betree.contains_owned_au(au)
                || self.ownership.branches.contains_owned_au(au)
            {
                return BranchBetreeSplitResult::Blocked;
            }
            new_index += 1;
        }
        let branch_adds = iaddress_aus(&child.buffers);
        let mut branch_index = 0usize;
        while branch_index < branch_adds.len()
            invariant
                self.wf(),
                self@ == pre_state,
                branch_index <= branch_adds.len(),
                forall |i: int| 0 <= i < branch_index
                    ==> self.branch_likes@.contains(
                        (#[trigger] branch_adds@[i]) as nat,
                    ),
            decreases branch_adds.len() - branch_index,
        {
            if !self.branch_likes.contains(branch_adds[branch_index]) {
                return BranchBetreeSplitResult::Blocked;
            }
            branch_index += 1;
        }
        let branch_removes = Vec::<IAU>::new();
        match self.branch_likes.apply_delta(&branch_removes, &branch_adds) {
            AuLikesUpdateResult::Applied { became_zero: _ } => {},
            AuLikesUpdateResult::Noop => {
                return BranchBetreeSplitResult::Blocked;
            },
        }
        let reclaimed = match self.ownership.replace_betree_aus(
            &old_aus,
            &new_aus,
        ) {
            BetreeOwnershipUpdateResult::Applied { reclaimed } => reclaimed,
            BetreeOwnershipUpdateResult::Noop => {
                proof { assert(false); }
                return BranchBetreeSplitResult::Blocked;
            },
        };
        let ghost prepared_cache = cache@;
        let ghost entries_view = built.entries@;
        let ghost writes = betree_raw_writes(entries_view);
        let new_root = built.new_root;
        proof {
            crate::betree::Utils_v::lemma_to_set_distributes_over_plus(
                seq![left_addr, right_addr, parent_addr],
                path_addrs@,
            );
            assert(destinations@.to_set()
                == set![left_addr, right_addr, parent_addr]
                    + path_addrs@.to_set());
            crate::implementation::BetreeWriteBatchImpl_v::
                betree_raw_writes_dom(entries_view);
            assert forall |i: int| 0 <= i < entries_view.len()
                implies cache.entry_available_for_fetch(
                    &(#[trigger] entries_view[i]).addr,
                ) by {
                assert(writes.dom().contains(entries_view[i].addr@));
                assert(destinations@.to_set().contains(
                    entries_view[i].addr,
                ));
                let j = choose |j: int| 0 <= j < destinations@.len()
                    && #[trigger] destinations@[j]
                        == entries_view[i].addr;
                assert(cache.entry_available_for_fetch(
                    &destinations@[j],
                ));
            }
        }
        let ghost cache_before_write = *cache;
        write_betree_pages(cache, built.entries);
        proof {
            FracCacheImpl::valid_load_handles_preserved_transitive(
                cache0,
                cache_before_write,
                *cache,
            );
        }
        self.root = Some(new_root);

        let ghost reads = path_reads@.insert(child_addr@, child_raw);
        let ghost access = PageAccess {
            betree_reads: reads,
            branch_reads: Map::empty(),
            betree_writes: writes,
            branch_writes: Map::empty(),
        };
        let ghost allocs = to_aus(
            SplitAddrs {
                left: left_addr@,
                right: right_addr@,
                parent: parent_addr@,
            }.repr() + iaddr_views(path_addrs@).to_set(),
        );
        let ghost deallocs = pre_betree.betree_aus.dom()
            - self.betree_i().betree_aus.dom();
        proof {
            assert(prepared_cache == cache0@);
            assert forall |addr: Address| #[trigger] reads.contains_key(addr)
                implies prepared_cache.valid_read(addr, reads[addr]) by {
                if addr == child_addr@ {
                    assert(reads[addr] == child_raw);
                    assert(cache0@.valid_read(child_addr@, child_raw));
                } else {
                    assert(path_reads@.contains_key(addr));
                    Cache::State::access_read_valid(
                        cache0@,
                        cache_before_child@,
                        path_reads@,
                        Map::empty(),
                        addr,
                    );
                }
            }
            Cache::State::access_add_reads(
                prepared_cache,
                cache@,
                reads,
                writes,
            );
            assert(Cache::State::next(
                prepared_cache,
                cache@,
                Cache::Label::Access { reads, writes },
            ));
            assert(access.wf());
            assert(access.only_betree());
            path_valid_after_child_read(
                cache0@,
                path.receipt@,
                path_reads@,
                child_addr@,
                child_raw,
            );
            assert(iaddr_views(path.addrs@) == path.receipt@.path_addrs()) by {
                assert_seqs_equal!(
                    iaddr_views(path.addrs@),
                    path.receipt@.path_addrs(),
                    i => {}
                );
            }
            split_discard_au_likes(
                path.addrs@,
                child_addr,
                old_addresses@,
                old_aus@,
            );
            split_added_au_likes(
                left_addr,
                right_addr,
                parent_addr,
                path_addrs@,
                destinations@,
                new_aus@,
            );
            iaddress_aus_likes(child.buffers@, branch_adds@);
            assert(iaddr_views(child.buffers@)
                == child@.buffers.addrs) by {
                assert_seqs_equal!(
                    iaddr_views(child.buffers@),
                    child@.buffers.addrs,
                    i => {}
                );
            }
            assert(self.ownership.betree@
                == pre_betree.betree_aus.sub(
                    to_au_likes(
                        crate::implementation::CachedBranchBetree_v::
                            path_discard_likes(path.receipt@).insert(child_addr@),
                    ),
                ).add(
                    to_au_likes(
                        crate::implementation::CachedBranchBetree_v::
                            added_path_likes(
                                SplitAddrs {
                                    left: left_addr@,
                                    right: right_addr@,
                                    parent: parent_addr@,
                                },
                                iaddr_views(path_addrs@),
                            ),
                    ),
                ));
            assert(self.branch_likes@
                == pre_betree.branch_aus.add(
                    to_au_likes(
                        crate::implementation::CachedBranchBetree_v::
                            direct_buffer_likes(child@),
                    ),
                ));
            crate::implementation::AuLikesImpl_v::seq_to_au_likes_dom(
                branch_adds@,
            );
            assert(iau_seq_set(branch_adds@)
                <= pre_betree.branch_aus.dom()) by {
                assert forall |au: AU|
                    #[trigger] iau_seq_set(branch_adds@).contains(au)
                    implies pre_betree.branch_aus.dom().contains(au) by {
                    let i = choose |i: int| 0 <= i < branch_adds@.len()
                        && branch_adds@[i] as nat == au;
                    assert(pre_betree.branch_aus.contains(
                        branch_adds@[i] as nat,
                    ));
                }
            }
            assert(self.branch_likes@.dom()
                == pre_betree.branch_aus.dom()) by {
                assert_multisets_equal!(
                    self.branch_likes@,
                    pre_betree.branch_aus.add(
                        crate::implementation::AuLikesImpl_v::
                            seq_to_au_likes(branch_adds@),
                    ),
                    au => {}
                );
                assert forall |au: AU|
                    #[trigger] self.branch_likes@.dom().contains(au)
                    <==> pre_betree.branch_aus.dom().contains(au) by {
                    if self.branch_likes@.dom().contains(au)
                        && !pre_betree.branch_aus.dom().contains(au)
                    {
                        assert(crate::implementation::AuLikesImpl_v::
                            seq_to_au_likes(branch_adds@).dom().contains(au));
                    }
                }
            }
            assert(self.ownership.branches.active_summary_map().dom()
                == pre_betree.branch_summary.dom());
            assert(self.branch_likes@.dom()
                == self.ownership.branches.active_summary_map().dom());
            self.ownership.current_durable_matches_views(
                self.branch_likes@,
            );
            assert(self.ownership.current_durable_aus()
                == self.betree_i().durable_aus());
            assert(self.wf());
            access.cached_only_betree_shape();
            assert(access.loaded_betree_reads() == to_betree_nodes(reads));
            assert(access.loaded_betree_writes() == to_betree_nodes(writes));
            assert(access.cached_access() == CachedBranchBetreeAccess {
                betree_reads: to_betree_nodes(reads),
                betree_writes: to_betree_nodes(writes),
                ..CachedBranchBetreeAccess::empty()
            });
            assert(CachedBranchBetree::State::split(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access: access.cached_access(),
                },
                path.receipt@,
                request.i(),
                SplitAddrs {
                    left: left_addr@,
                    right: right_addr@,
                    parent: parent_addr@,
                },
                iaddr_views(path_addrs@),
                to_betree_nodes(reads),
                to_betree_nodes(writes),
            )) by {

            }
            assert(CachedBranchBetree::State::next_by(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access: access.cached_access(),
                },
                CachedBranchBetree::Step::split(
                    path.receipt@,
                    request.i(),
                    SplitAddrs {
                        left: left_addr@,
                        right: right_addr@,
                        parent: parent_addr@,
                    },
                    iaddr_views(path_addrs@),
                    to_betree_nodes(reads),
                    to_betree_nodes(writes),
                ),
            )) by {
                reveal(CachedBranchBetree::State::next_by);
            }
            assert(CachedBranchBetree::State::next(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access: access.cached_access(),
                },
            )) by {
                reveal(CachedBranchBetree::State::next);
            }
            assert(iau_seq_set(reclaimed@) <= deallocs);
            assert(AtomicBranchBetreeState::State::split(
                pre_state,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access: access,
                },
                self.betree_i(),
                path.receipt@,
                request.i(),
                SplitAddrs {
                    left: left_addr@,
                    right: right_addr@,
                    parent: parent_addr@,
                },
                iaddr_views(path_addrs@),
                to_betree_nodes(reads),
                to_betree_nodes(writes),
            )) by {

            }
            assert(AtomicBranchBetreeState::State::next_by(
                pre_state,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access,
                },
                AtomicBranchBetreeState::Step::split(
                    self.betree_i(),
                    path.receipt@,
                    request.i(),
                    SplitAddrs {
                        left: left_addr@,
                        right: right_addr@,
                        parent: parent_addr@,
                    },
                    iaddr_views(path_addrs@),
                    to_betree_nodes(reads),
                    to_betree_nodes(writes),
                ),
            )) by {
                reveal(AtomicBranchBetreeState::State::next_by);
            }
            assert(AtomicBranchBetreeState::State::next(
                pre_state,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access,
                },
            )) by {
                reveal(AtomicBranchBetreeState::State::next);
            }
            assert(access.reads() == reads);
            assert(access.writes() == writes);
            assert(access.loaded_betree_writes()
                == to_betree_nodes(writes));
        }
        BranchBetreeSplitResult::Split {
            new_root,
            reclaimed,
            prepared_cache: Ghost(prepared_cache),
            access: Ghost(access),
            allocs: Ghost(allocs),
            deallocs: Ghost(deallocs),
        }
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(32)]
    pub fn flush_child_with_cache(
        &mut self,
        cache: &mut FracCacheImpl,
        key: Key,
        target_depth: usize,
        fuel: usize,
        disk_page_count: crate::spec::ImplDisk_t::IPage,
        child_idx: usize,
        buffer_gc: usize,
        parent_addr: IAddress,
        new_child_addr: IAddress,
        path_addrs: &Vec<IAddress>,
    ) -> (result: BranchBetreeChildFlushResult)
        requires
            old(self).wf(),
            old(self).control.metadata_loaded,
            old(self).root is Some,
            target_depth < fuel,
            disk_page_count as nat
                == crate::disk::GenericDisk_v::page_count(),
            path_addrs@.len() == target_depth,
            cached_betree_path_prefix_valid(
                old(cache)@,
                old(self).root.unwrap()@,
                key,
                fuel as nat,
                target_depth as nat,
                old(self).ownership.betree.active_aus(),
            ),
            cached_flush_parent_wf(
                old(cache)@,
                old(self).root.unwrap()@,
                key,
                target_depth as nat,
                child_idx as nat,
                buffer_gc as nat,
                new_child_addr@,
            ),
            parent_addr@.wf(),
            new_child_addr@.wf(),
            betree_node_addr(parent_addr@),
            betree_node_addr(new_child_addr@),
            forall |i: int| 0 <= i < path_addrs@.len()
                ==> (#[trigger] path_addrs@[i])@.wf(),
            forall |i: int| 0 <= i < path_addrs@.len()
                ==> betree_node_addr((#[trigger] path_addrs@[i])@),
            {
                let new_addrs = TwoAddrs {
                    addr1: parent_addr@,
                    addr2: new_child_addr@,
                };
                &&& new_addrs.addrs_in_disjoint_aus()
                &&& to_aus(new_addrs.repr()).disjoint(
                    crate::allocation_layer::AllocationBranchBetree_v::
                        seq_addrs_to_aus(iaddr_views(path_addrs@)),
                )
                &&& seq_addrs_disjoint_aus(iaddr_views(path_addrs@))
                &&& old(self).betree_i().is_fresh(
                    to_aus(new_addrs.repr())
                        + crate::allocation_layer::AllocationBranchBetree_v::
                            seq_addrs_to_aus(iaddr_views(path_addrs@)),
                )
                &&& old(self).ownership.betree.all_aus().disjoint(
                    to_aus(new_addrs.repr())
                        + crate::allocation_layer::AllocationBranchBetree_v::
                            seq_addrs_to_aus(iaddr_views(path_addrs@)),
                )
                &&& old(self).ownership.branches.all_summary_aus().disjoint(
                    to_aus(new_addrs.repr())
                        + crate::allocation_layer::AllocationBranchBetree_v::
                            seq_addrs_to_aus(iaddr_views(path_addrs@)),
                )
            },
            old(cache).wf(),
            old(cache)@.inv(),
        ensures
            self.wf(),
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            match result {
                BranchBetreeChildFlushResult::Flushed {
                    new_root,
                    betree_reclaimed,
                    branch_reclaimed,
                    prepared_cache,
                    access,
                    allocs,
                    deallocs,
                } => {
                    let new_addrs = TwoAddrs {
                        addr1: parent_addr@,
                        addr2: new_child_addr@,
                    };
                    &&& new_root@ == self.betree_i().root.unwrap()
                    &&& allocs@ == to_aus(
                        new_addrs.repr() + iaddr_views(path_addrs@).to_set(),
                    )
                    &&& unique_iau_seq(betree_reclaimed@)
                    &&& unique_iau_seq(branch_reclaimed@)
                    &&& prepared_cache@ == old(cache)@
                    &&& access@.wf()
                    &&& access@.only_betree()
                    &&& Cache::State::next(
                        prepared_cache@,
                        cache@,
                        Cache::Label::Access {
                            reads: access@.reads(),
                            writes: access@.writes(),
                        },
                    )
                    &&& AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: allocs@,
                            deallocs: deallocs@,
                            access: access@,
                        },
                    )
                },
                BranchBetreeChildFlushResult::NeedCacheLoad { addr, handle } => {
                    &&& self@ == old(self)@
                    &&& cache.entry_fetched(&addr)
                    &&& cache.valid_load_handle(&addr, handle)
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        crate::implementation::FracCacheImpl_v::cache_load_label(
                            &addr,
                        ),
                    )
                },
                BranchBetreeChildFlushResult::CacheFull
                | BranchBetreeChildFlushResult::Blocked
                | BranchBetreeChildFlushResult::InvalidPage => {
                    &&& self@ == old(self)@
                    &&& cache@ == old(cache)@
                },
            },
    {
        if self.compactors.len() != 0 {
            return BranchBetreeChildFlushResult::Blocked;
        }
        let ghost pre_state = self@;
        let ghost pre_betree = self.betree_i();
        let ghost cache0 = *cache;
        let root = self.root.unwrap();
        let ghost betree_aus = self.ownership.betree.active_aus();
        let loaded = load_betree_path(
            cache,
            root,
            key,
            target_depth,
            fuel,
            disk_page_count,
            Ghost(betree_aus),
        );
        let (path, path_reads) = match loaded {
            BetreePathLoadResult::Loaded { workspace: path, reads } => (path, reads),
            BetreePathLoadResult::NeedCacheLoad { addr, handle } => {
                return BranchBetreeChildFlushResult::NeedCacheLoad {
                    addr,
                    handle,
                };
            },
            BetreePathLoadResult::CacheFull => {
                return BranchBetreeChildFlushResult::CacheFull;
            },
            BetreePathLoadResult::Blocked => {
                return BranchBetreeChildFlushResult::Blocked;
            },
            BetreePathLoadResult::InvalidPage => {
                return BranchBetreeChildFlushResult::InvalidPage;
            },
        };
        let target_idx = path.nodes.len() - 1;
        if child_idx >= path.nodes[target_idx].children.len() {
            return BranchBetreeChildFlushResult::Blocked;
        }
        let child_addr = match path.nodes[target_idx].children[child_idx] {
            Some(addr) => addr,
            None => return BranchBetreeChildFlushResult::Blocked,
        };
        if buffer_gc > path.nodes[target_idx].buffers.len() {
            return BranchBetreeChildFlushResult::Blocked;
        }
        let ghost cache_before_child = *cache;
        let child_handle = match cache.fetch(&child_addr, true) {
            FetchErrorCode::Success { slot_handle } => slot_handle,
            FetchErrorCode::LoadInitiate { slot_handle } => {
                proof {
                    FracCacheImpl::valid_load_handles_preserved_transitive(
                        cache0,
                        cache_before_child,
                        *cache,
                    );
                }
                return BranchBetreeChildFlushResult::NeedCacheLoad {
                    addr: child_addr,
                    handle: slot_handle,
                };
            },
            FetchErrorCode::CacheFull => {
                proof {
                    FracCacheImpl::valid_load_handles_preserved_transitive(
                        cache0,
                        cache_before_child,
                        *cache,
                    );
                }
                return BranchBetreeChildFlushResult::CacheFull;
            },
            FetchErrorCode::Awaiting | FetchErrorCode::NotPresent => {
                proof {
                    FracCacheImpl::valid_load_handles_preserved_transitive(
                        cache0,
                        cache_before_child,
                        *cache,
                    );
                }
                return BranchBetreeChildFlushResult::Blocked;
            },
        };
        let ghost child_raw = child_handle.rec@;
        let fmt = BetreeNodePageFmt::new();
        let all_slice = Slice::all(&child_handle.rec);
        let parsed = fmt.try_parse(&all_slice, &child_handle.rec);
        proof {
            if parsed is Some {
                assert(fmt == BetreeNodePageFmt::spec_new());
                assert(all_slice@.i(child_handle.rec@) == child_raw);
                assert(parsed.unwrap().parsedv() == fmt.parse(child_raw));
                assert(raw_page_to_betree_node(child_raw)
                    == parsed.unwrap()@);
            }
        }
        let ghost cache_borrowed = *cache;
        cache.handle_release(&child_addr, child_handle);
        proof {
            assert(cache@ == cache_before_child@);
            assert(cache_before_child@ == cache0@);
            FracCacheImpl::valid_load_handles_preserved_transitive(
                cache_before_child,
                cache_borrowed,
                *cache,
            );
            FracCacheImpl::valid_load_handles_preserved_transitive(
                cache0,
                cache_before_child,
                *cache,
            );
        }
        let child = match parsed {
            Some(node) => node,
            None => return BranchBetreeChildFlushResult::InvalidPage,
        };
        let target = &path.nodes[target_idx];
        let mut offset_idx = 0usize;
        while offset_idx < target.flushed.len()
            invariant
                path.wf(),
                offset_idx <= target.flushed.len(),
                forall |i: int| #![trigger target.flushed@[i]]
                    0 <= i < offset_idx ==> {
                    let source = if i == child_idx as int {
                        target.buffers.len() as nat
                    } else {
                        (#[trigger] target.flushed@[i]) as nat
                    };
                    source >= buffer_gc as nat
                },
            decreases target.flushed.len() - offset_idx,
        {
            let source = if offset_idx == child_idx {
                target.buffers.len() as u64
            } else {
                target.flushed[offset_idx]
            };
            if source < buffer_gc as u64 {
                return BranchBetreeChildFlushResult::Blocked;
            }
            offset_idx += 1;
        }
        proof {
            betree_path_receipt_edges(&path);
            assert(path.nodes@[target_idx as int]@ == path.receipt@.target().node);
            assert(path.receipt@.target().node.valid_child_index(child_idx as nat));
            assert(path.receipt@.target().node.children[child_idx as int]
                == Some(child_addr@));
            assert(path.receipt@.target().node.flushed.update(
                child_idx as int,
                path.receipt@.target().node.buffers.len(),
            ).all_gte(buffer_gc as nat));
            assert forall |addr: Address|
                #[trigger] path_reads@.contains_key(addr)
                implies cache0@.valid_read(addr, path_reads@[addr]) by {
                Cache::State::access_read_valid(
                    cache0@,
                    cache_before_child@,
                    path_reads@,
                    Map::empty(),
                    addr,
                );
            }
            assert(cache0@.valid_read(child_addr@, child_raw));
            assert(cached_flush_parent_wf(
                cache0@,
                path.receipt@.root,
                path.receipt@.key,
                path.receipt@.depth(),
                child_idx as nat,
                buffer_gc as nat,
                new_child_addr@,
            ));
            assert(child@.wf());
            assert(crate::implementation::BetreeStructuralPageImpl_v::
                flush_parent_view(
                    path.receipt@.target().node,
                    child_idx as nat,
                    buffer_gc as nat,
                    new_child_addr@,
                ).wf());
            assert(crate::implementation::BetreeStructuralPageImpl_v::
                flush_child_view(
                    path.receipt@.target().node,
                    child@,
                    child_idx as nat,
                ).wf());
            disjoint_au_views_are_unique(path_addrs@);
            crate::disk::GenericDisk_v::to_aus_domain(
                TwoAddrs {
                    addr1: parent_addr@,
                    addr2: new_child_addr@,
                }.repr(),
            );
            crate::disk::GenericDisk_v::to_aus_domain(
                iaddr_views(path_addrs@).to_set(),
            );
            assert(iaddr_views(path_addrs@).to_set().disjoint(
                set![parent_addr@, new_child_addr@],
            )) by {
                assert forall |addr: Address|
                    #[trigger] iaddr_views(path_addrs@).to_set().contains(addr)
                    implies !set![parent_addr@, new_child_addr@]
                        .contains(addr) by {
                    if set![parent_addr@, new_child_addr@].contains(addr) {
                        assert(crate::allocation_layer::AllocationBranchBetree_v::
                            seq_addrs_to_aus(iaddr_views(path_addrs@))
                            .contains(addr.au));
                        assert(to_aus(TwoAddrs {
                            addr1: parent_addr@,
                            addr2: new_child_addr@,
                        }.repr()).contains(addr.au));
                    }
                }
            }
        }
        let built = match build_flush_write_batch(
            &path,
            child_addr,
            &child,
            child_idx,
            buffer_gc,
            parent_addr,
            new_child_addr,
            path_addrs,
        ) {
            Some(built) => built,
            None => return BranchBetreeChildFlushResult::InvalidPage,
        };
        let destinations = flush_destination_addrs(
            parent_addr,
            new_child_addr,
            path_addrs,
        );
        let ghost cache_before_prepare = *cache;
        match prepare_cache_write_addrs(cache, &destinations) {
            CacheWritePrepareResult::Ready => {
                proof {
                    FracCacheImpl::valid_load_handles_preserved_transitive(
                        cache0,
                        cache_before_prepare,
                        *cache,
                    );
                }
            },
            CacheWritePrepareResult::NeedCacheLoad { addr, handle } => {
                proof {
                    FracCacheImpl::valid_load_handles_preserved_transitive(
                        cache0,
                        cache_before_prepare,
                        *cache,
                    );
                }
                return BranchBetreeChildFlushResult::NeedCacheLoad {
                    addr,
                    handle,
                };
            },
            CacheWritePrepareResult::CacheFull => {
                proof {
                    FracCacheImpl::valid_load_handles_preserved_transitive(
                        cache0,
                        cache_before_prepare,
                        *cache,
                    );
                }
                return BranchBetreeChildFlushResult::CacheFull;
            },
            CacheWritePrepareResult::Blocked => {
                proof {
                    FracCacheImpl::valid_load_handles_preserved_transitive(
                        cache0,
                        cache_before_prepare,
                        *cache,
                    );
                }
                return BranchBetreeChildFlushResult::Blocked;
            },
        }

        let old_addresses = append_address(&path.addrs, child_addr);
        let old_aus = iaddress_aus(&old_addresses);
        let new_aus = iaddress_aus(&destinations);
        if !crate::implementation::BranchBetreeOwnershipImpl_v::iau_vec_unique(
            &old_aus,
        ) || !crate::implementation::BranchBetreeOwnershipImpl_v::iau_vec_unique(
            &new_aus,
        ) {
            return BranchBetreeChildFlushResult::Blocked;
        }
        let mut old_index = 0usize;
        while old_index < old_aus.len()
            invariant
                self.wf(),
                self@ == pre_state,
                old_index <= old_aus.len(),
                forall |i: int| 0 <= i < old_index
                    ==> self.ownership.betree.active_aus().contains(
                        (#[trigger] old_aus@[i]) as nat,
                    ),
            decreases old_aus.len() - old_index,
        {
            if !self.ownership.betree.contains_active(old_aus[old_index]) {
                return BranchBetreeChildFlushResult::Blocked;
            }
            old_index += 1;
        }
        let mut new_index = 0usize;
        while new_index < new_aus.len()
            invariant
                self.wf(),
                self@ == pre_state,
                new_index <= new_aus.len(),
                forall |i: int| 0 <= i < new_index ==> {
                    &&& !self.ownership.betree.all_aus().contains(
                        (#[trigger] new_aus@[i]) as nat,
                    )
                    &&& !self.ownership.branches.all_summary_aus().contains(
                        new_aus@[i] as nat,
                    )
                },
            decreases new_aus.len() - new_index,
        {
            let au = new_aus[new_index];
            if self.ownership.betree.contains_owned_au(au)
                || self.ownership.branches.contains_owned_au(au)
            {
                return BranchBetreeChildFlushResult::Blocked;
            }
            new_index += 1;
        }

        let branch_remove_addrs = clone_addr_subrange(
            &target.buffers,
            0,
            buffer_gc,
        );
        let flushed_ofs = target.flushed[child_idx] as usize;
        let branch_add_addrs = clone_addr_subrange(
            &target.buffers,
            flushed_ofs,
            target.buffers.len(),
        );
        let branch_removes = iaddress_aus(&branch_remove_addrs);
        let branch_adds = iaddress_aus(&branch_add_addrs);
        let mut branch_index = 0usize;
        while branch_index < branch_adds.len()
            invariant
                self.wf(),
                self@ == pre_state,
                branch_index <= branch_adds.len(),
                forall |i: int| 0 <= i < branch_index
                    ==> self.branch_likes@.contains(
                        (#[trigger] branch_adds@[i]) as nat,
                    ),
            decreases branch_adds.len() - branch_index,
        {
            if !self.branch_likes.contains(branch_adds[branch_index]) {
                return BranchBetreeChildFlushResult::Blocked;
            }
            branch_index += 1;
        }
        let became_zero = match self.branch_likes.apply_delta(
            &branch_removes,
            &branch_adds,
        ) {
            AuLikesUpdateResult::Applied { became_zero } => became_zero,
            AuLikesUpdateResult::Noop => {
                return BranchBetreeChildFlushResult::Blocked;
            },
        };
        let branch_reclaimed = match self.ownership.branches.retire_many(
            &became_zero,
        ) {
            BranchOwnershipUpdateResult::Applied { reclaimed } => reclaimed,
            BranchOwnershipUpdateResult::Noop => {
                proof { assert(false); }
                return BranchBetreeChildFlushResult::Blocked;
            },
        };
        proof {
            assert(self.ownership.wf()) by {
                assert(self.ownership.betree.all_aus().disjoint(
                    self.ownership.branches.all_summary_aus(),
                )) by {
                    assert(self.ownership.branches.all_summary_aus()
                        <= old(self).ownership.branches.all_summary_aus());
                }
            }
        }
        let betree_reclaimed = match self.ownership.replace_betree_aus(
            &old_aus,
            &new_aus,
        ) {
            BetreeOwnershipUpdateResult::Applied { reclaimed } => reclaimed,
            BetreeOwnershipUpdateResult::Noop => {
                proof { assert(false); }
                return BranchBetreeChildFlushResult::Blocked;
            },
        };

        let ghost prepared_cache = cache@;
        let ghost entries_view = built.entries@;
        let ghost writes = betree_raw_writes(entries_view);
        let new_root = built.new_root;
        proof {
            crate::betree::Utils_v::lemma_to_set_distributes_over_plus(
                seq![parent_addr, new_child_addr],
                path_addrs@,
            );
            crate::implementation::BetreeWriteBatchImpl_v::
                betree_raw_writes_dom(entries_view);
            assert forall |i: int| 0 <= i < entries_view.len()
                implies cache.entry_available_for_fetch(
                    &(#[trigger] entries_view[i]).addr,
                ) by {
                assert(writes.dom().contains(entries_view[i].addr@));
                assert(destinations@.to_set().contains(entries_view[i].addr));
                let j = choose |j: int| 0 <= j < destinations@.len()
                    && #[trigger] destinations@[j] == entries_view[i].addr;
                assert(cache.entry_available_for_fetch(&destinations@[j]));
            }
        }
        let ghost cache_before_write = *cache;
        write_betree_pages(cache, built.entries);
        proof {
            FracCacheImpl::valid_load_handles_preserved_transitive(
                cache0,
                cache_before_write,
                *cache,
            );
        }
        self.root = Some(new_root);

        let ghost reads = path_reads@.insert(child_addr@, child_raw);
        let ghost access = PageAccess {
            betree_reads: reads,
            branch_reads: Map::empty(),
            betree_writes: writes,
            branch_writes: Map::empty(),
        };
        let ghost allocs = to_aus(
            TwoAddrs {
                addr1: parent_addr@,
                addr2: new_child_addr@,
            }.repr() + iaddr_views(path_addrs@).to_set(),
        );
        let ghost branch_deallocs = pre_betree.branch_aus.dom()
            - self.betree_i().branch_aus.dom();
        let ghost deallocs = (
            pre_betree.betree_aus.dom() - self.betree_i().betree_aus.dom()
        ) + summary_aus(pre_betree.branch_summary.restrict(branch_deallocs));
        proof {
            assert(prepared_cache == cache0@);
            path_valid_after_child_read(
                cache0@,
                path.receipt@,
                path_reads@,
                child_addr@,
                child_raw,
            );
            assert forall |addr: Address| #[trigger] reads.contains_key(addr)
                implies prepared_cache.valid_read(addr, reads[addr]) by {
                if addr == child_addr@ {
                    assert(reads[addr] == child_raw);
                } else {
                    assert(path_reads@.contains_key(addr));
                }
            }
            Cache::State::access_add_reads(
                prepared_cache,
                cache@,
                reads,
                writes,
            );
            assert(access.wf());
            assert(access.only_betree());
            assert(iaddr_views(path.addrs@) == path.receipt@.path_addrs()) by {
                assert_seqs_equal!(
                    iaddr_views(path.addrs@),
                    path.receipt@.path_addrs(),
                    i => {}
                );
            }
            split_discard_au_likes(
                path.addrs@,
                child_addr,
                old_addresses@,
                old_aus@,
            );
            two_added_au_likes(
                parent_addr,
                new_child_addr,
                path_addrs@,
                destinations@,
                new_aus@,
            );
            iaddress_aus_likes(branch_remove_addrs@, branch_removes@);
            iaddress_aus_likes(branch_add_addrs@, branch_adds@);
            crate::implementation::AuLikesImpl_v::seq_to_au_likes_dom(
                branch_adds@,
            );
            assert(iau_seq_set(branch_adds@)
                <= pre_betree.branch_aus.dom()) by {
                assert forall |au: AU|
                    #[trigger] iau_seq_set(branch_adds@).contains(au)
                    implies pre_betree.branch_aus.dom().contains(au) by {
                    let i = choose |i: int| 0 <= i < branch_adds@.len()
                        && branch_adds@[i] as nat == au;
                    assert(pre_betree.branch_aus.contains(
                        branch_adds@[i] as nat,
                    ));
                }
            }
            assert(Parsedview::<Seq<Address>>::parsedv(&branch_remove_addrs)
                == path.receipt@.target().node.buffers.slice(
                    0,
                    buffer_gc as int,
                ).addrs);
            assert(iaddr_views(branch_remove_addrs@)
                == Parsedview::<Seq<Address>>::parsedv(
                    &branch_remove_addrs,
                )) by {
                assert_seqs_equal!(
                    iaddr_views(branch_remove_addrs@),
                    Parsedview::<Seq<Address>>::parsedv(
                        &branch_remove_addrs,
                    ),
                    i => {}
                );
            }
            assert(Parsedview::<Seq<Address>>::parsedv(&branch_add_addrs)
                == path.receipt@.target().node.buffers.slice(
                    path.receipt@.target().node.flushed.offsets[
                        child_idx as int
                    ] as int,
                    path.receipt@.target().node.buffers.len() as int,
                ).addrs);
            assert(iaddr_views(branch_add_addrs@)
                == Parsedview::<Seq<Address>>::parsedv(
                    &branch_add_addrs,
                )) by {
                assert_seqs_equal!(
                    iaddr_views(branch_add_addrs@),
                    Parsedview::<Seq<Address>>::parsedv(
                        &branch_add_addrs,
                    ),
                    i => {}
                );
            }
            assert(self.ownership.betree@
                == pre_betree.betree_aus.sub(
                    to_au_likes(
                        crate::implementation::CachedBranchBetree_v::
                            path_discard_likes(path.receipt@).insert(child_addr@),
                    ),
                ).add(
                    to_au_likes(
                        crate::implementation::CachedBranchBetree_v::
                            added_path_likes(
                                TwoAddrs {
                                    addr1: parent_addr@,
                                    addr2: new_child_addr@,
                                },
                                iaddr_views(path_addrs@),
                            ),
                    ),
                ));
            assert_multisets_equal!(
                self.branch_likes@,
                pre_betree.branch_aus.sub(
                    to_au_likes(
                        path.receipt@.target().node.buffers.slice(
                            0,
                            buffer_gc as int,
                        ).addrs.to_multiset(),
                    ),
                ).add(
                    to_au_likes(
                        path.receipt@.target().node.buffers.slice(
                            path.receipt@.target().node.flushed.offsets[
                                child_idx as int
                            ] as int,
                            path.receipt@.target().node.buffers.len() as int,
                        ).addrs.to_multiset(),
                    ),
                ),
                au => {}
            );
            assert(iau_seq_set(became_zero@)
                =~= pre_betree.branch_aus.dom()
                    - self.branch_likes@.dom());
            assert(self.branch_likes@.dom()
                <= pre_betree.branch_aus.dom()) by {
                assert forall |au: AU|
                    #[trigger] self.branch_likes@.dom().contains(au)
                    implies pre_betree.branch_aus.dom().contains(au) by {
                    if !pre_betree.branch_aus.dom().contains(au) {
                        assert(crate::implementation::AuLikesImpl_v::
                            seq_to_au_likes(branch_adds@).dom().contains(au));
                    }
                }
            }
            assert(self.ownership.branches.active_summary_map()
                == pre_betree.branch_summary.remove_keys(
                    iau_seq_set(became_zero@),
                ));
            assert(pre_betree.compactors.len() == 0);
            assert(read_ref_aus(pre_betree.compactors)
                =~= Set::<AU>::empty()) by {



            }
            assert_sets_equal!(
                branch_deallocs,
                iau_seq_set(became_zero@),
                au => {}
            );
            assert_maps_equal!(
                self.betree_i().branch_summary,
                pre_betree.branch_summary.remove_keys(branch_deallocs),
                au => {}
            );
            assert(self.branch_likes@.dom()
                == self.ownership.branches.active_summary_map().dom()) by {
                assert forall |au: AU|
                    #[trigger] self.branch_likes@.dom().contains(au)
                    <==> self.ownership.branches.active_summary_map().dom()
                        .contains(au) by {
                    assert(pre_betree.branch_aus.dom()
                        == pre_betree.branch_summary.dom());
                    if self.branch_likes@.dom().contains(au) {
                        assert(pre_betree.branch_aus.dom().contains(au));
                        assert(!iau_seq_set(became_zero@).contains(au));
                        assert(pre_betree.branch_summary.remove_keys(
                            iau_seq_set(became_zero@),
                        ).contains_key(au));
                    }
                }
            }
            self.ownership.current_durable_matches_views(
                self.branch_likes@,
            );
            assert(self.ownership.current_durable_aus()
                == self.betree_i().durable_aus());
            assert(to_betree_nodes(writes)
                == crate::implementation::CachedBranchBetree_v::
                    substitute_writes(
                        path.receipt@,
                        parent_addr@,
                        crate::implementation::CachedBranchBetree_v::
                            flush_replacement(
                                path.receipt@,
                                to_betree_nodes(reads),
                                child_idx as nat,
                                buffer_gc as nat,
                                TwoAddrs {
                                    addr1: parent_addr@,
                                    addr2: new_child_addr@,
                                },
                            ),
                        iaddr_views(path_addrs@),
                    ));
            let ghost model_branch_deallocs = (
                pre_betree.branch_aus.dom()
                    - self.betree_i().branch_aus.dom()
            ) - read_ref_aus(pre_betree.compactors);
            assert_sets_equal!(
                model_branch_deallocs,
                branch_deallocs,
                au => {}
            );
            assert_maps_equal!(
                self.betree_i().branch_summary,
                pre_betree.branch_summary.remove_keys(
                    model_branch_deallocs,
                ),
                au => {}
            );
            let ghost model_deallocated_summary =
                pre_betree.branch_summary.restrict(
                    model_branch_deallocs,
                );
            let ghost model_deallocs = (
                pre_betree.betree_aus.dom()
                    - self.betree_i().betree_aus.dom()
            ) + summary_aus(model_deallocated_summary);
            assert_sets_equal!(deallocs, model_deallocs, au => {});
            assert(self.wf());
            access.cached_only_betree_shape();
            assert(access.loaded_betree_reads() == to_betree_nodes(reads));
            assert(access.loaded_betree_writes() == to_betree_nodes(writes));
            assert(access.cached_access() == CachedBranchBetreeAccess {
                betree_reads: to_betree_nodes(reads),
                betree_writes: to_betree_nodes(writes),
                ..CachedBranchBetreeAccess::empty()
            });
            assert(CachedBranchBetree::State::flush(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access: access.cached_access(),
                },
                path.receipt@,
                child_idx as nat,
                buffer_gc as nat,
                TwoAddrs {
                    addr1: parent_addr@,
                    addr2: new_child_addr@,
                },
                iaddr_views(path_addrs@),
                to_betree_nodes(reads),
                to_betree_nodes(writes),
            )) by {

            }
            assert(CachedBranchBetree::State::next_by(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access: access.cached_access(),
                },
                CachedBranchBetree::Step::flush(
                    path.receipt@,
                    child_idx as nat,
                    buffer_gc as nat,
                    TwoAddrs {
                        addr1: parent_addr@,
                        addr2: new_child_addr@,
                    },
                    iaddr_views(path_addrs@),
                    to_betree_nodes(reads),
                    to_betree_nodes(writes),
                ),
            )) by {
                reveal(CachedBranchBetree::State::next_by);
            }
            assert(CachedBranchBetree::State::next(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access: access.cached_access(),
                },
            )) by {
                reveal(CachedBranchBetree::State::next);
            }
            assert(AtomicBranchBetreeState::State::flush(
                pre_state,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access: access,
                },
                self.betree_i(),
                path.receipt@,
                child_idx as nat,
                buffer_gc as nat,
                TwoAddrs {
                    addr1: parent_addr@,
                    addr2: new_child_addr@,
                },
                iaddr_views(path_addrs@),
                to_betree_nodes(reads),
                to_betree_nodes(writes),
            )) by {

            }
            assert(AtomicBranchBetreeState::State::next_by(
                pre_state,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access,
                },
                AtomicBranchBetreeState::Step::flush(
                    self.betree_i(),
                    path.receipt@,
                    child_idx as nat,
                    buffer_gc as nat,
                    TwoAddrs {
                        addr1: parent_addr@,
                        addr2: new_child_addr@,
                    },
                    iaddr_views(path_addrs@),
                    to_betree_nodes(reads),
                    to_betree_nodes(writes),
                ),
            )) by {
                reveal(AtomicBranchBetreeState::State::next_by);
            }
            assert(AtomicBranchBetreeState::State::next(
                pre_state,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access,
                },
            )) by {
                reveal(AtomicBranchBetreeState::State::next);
            }
            assert(Cache::State::next(
                prepared_cache,
                cache@,
                Cache::Label::Access { reads, writes },
            ));
            assert(access.reads() == reads);
            assert(access.writes() == writes);
            assert(access.loaded_betree_writes()
                == to_betree_nodes(writes));
        }
        BranchBetreeChildFlushResult::Flushed {
            new_root,
            betree_reclaimed,
            branch_reclaimed,
            prepared_cache: Ghost(prepared_cache),
            access: Ghost(access),
            allocs: Ghost(allocs),
            deallocs: Ghost(deallocs),
        }
    }

    pub fn compact_begin_with_cache(
        &mut self,
        cache: &mut FracCacheImpl,
        expected_target_addr: IAddress,
        key: Key,
        target_depth: usize,
        fuel: usize,
        disk_page_count: crate::spec::ImplDisk_t::IPage,
        start: usize,
        end: usize,
    ) -> (result: BranchBetreeCompactBeginResult)
        requires
            old(self).wf(),
            old(self).control.metadata_loaded,
            old(self).root is Some,
            target_depth < fuel,
            disk_page_count as nat
                == crate::disk::GenericDisk_v::page_count(),
            cached_betree_path_prefix_valid(
                old(cache)@,
                old(self).root.unwrap()@,
                key,
                fuel as nat,
                target_depth as nat,
                old(self).ownership.betree.active_aus(),
            ),
            old(cache).wf(),
            old(cache)@.inv(),
        ensures
            self.wf(),
            cache.wf(),
            self.root == old(self).root,
            self.ownership == old(self).ownership,
            self.branch_likes == old(self).branch_likes,
            self.memtable == old(self).memtable,
            self.control == old(self).control,
            cache.valid_load_handles_preserved(*old(cache)),
            match result {
                BranchBetreeCompactBeginResult::Began {
                    input_idx,
                    access,
                } => {
                    &&& input_idx == old(self).compactors@.len()
                    &&& self.compactors@.len()
                        == old(self).compactors@.len() + 1
                    &&& self.compactors@[input_idx as int].merge is None
                    &&& read_ref_aus(compactor_views(self.compactors@))
                        <= self.branch_likes@.dom()
                    &&& self.wip_branches@ == old(self).wip_branches@
                    &&& access@.wf()
                    &&& access@.only_betree()
                    &&& access@.writes().is_empty()
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        Cache::Label::Access {
                            reads: access@.reads(),
                            writes: access@.writes(),
                        },
                    )
                    &&& exists |path: crate::implementation::CachedBranchBetree_v::LoadedBetreePath|
                        AtomicBranchBetreeState::State::compact_begin(
                            old(self)@,
                            self@,
                            AtomicBranchBetreeState::Label::InternalAccess {
                                access: access@,
                            },
                            self.betree_i(),
                            path,
                            start as nat,
                            end as nat,
                            access@.loaded_betree_reads(),
                        )
                    &&& AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAccess {
                            access: access@,
                        },
                    )
                },
                BranchBetreeCompactBeginResult::NeedCacheLoad { addr, handle } => {
                    &&& self@ == old(self)@
                    &&& self.compactors@ == old(self).compactors@
                    &&& self.wip_branches@ == old(self).wip_branches@
                    &&& old(self).ownership.betree.active_aus()
                        .contains(addr@.au)
                    &&& cache.entry_fetched(&addr)
                    &&& cache.valid_load_handle(&addr, handle)
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        crate::implementation::FracCacheImpl_v::cache_load_label(
                            &addr,
                        ),
                    )
                },
                BranchBetreeCompactBeginResult::Stale
                | BranchBetreeCompactBeginResult::CacheFull
                | BranchBetreeCompactBeginResult::Blocked
                | BranchBetreeCompactBeginResult::InvalidPage => {
                    &&& self@ == old(self)@
                    &&& self.compactors@ == old(self).compactors@
                    &&& self.wip_branches@ == old(self).wip_branches@
                    &&& cache@ == old(cache)@
                },
            },
    {
        let root = self.root.unwrap();
        let ghost betree_aus = self.ownership.betree.active_aus();
        let loaded = load_betree_path(
            cache,
            root,
            key,
            target_depth,
            fuel,
            disk_page_count,
            Ghost(betree_aus),
        );
        let (path, reads) = match loaded {
            BetreePathLoadResult::Loaded { workspace: path, reads } => (path, reads),
            BetreePathLoadResult::NeedCacheLoad { addr, handle } => {
                return BranchBetreeCompactBeginResult::NeedCacheLoad {
                    addr,
                    handle,
                };
            },
            BetreePathLoadResult::CacheFull => {
                return BranchBetreeCompactBeginResult::CacheFull;
            },
            BetreePathLoadResult::Blocked => {
                return BranchBetreeCompactBeginResult::Blocked;
            },
            BetreePathLoadResult::InvalidPage => {
                return BranchBetreeCompactBeginResult::InvalidPage;
            },
        };
        let target_idx = path.nodes.len() - 1;
        if path.addrs[target_idx].au != expected_target_addr.au
            || path.addrs[target_idx].page != expected_target_addr.page
        {
            return BranchBetreeCompactBeginResult::Stale;
        }
        let target = &path.nodes[target_idx];
        if start >= end || end > target.buffers.len() {
            return BranchBetreeCompactBeginResult::Blocked;
        }
        let ghost offset_map = path.receipt@.target().node.make_offset_map()
            .decrement(start as nat);
        let filter = CompactionFilterImpl::from_target(target, start, end);
        let input_buffers = clone_addr_subrange(
            &target.buffers,
            start,
            end,
        );
        let ghost input = CompactorInput {
            input_buffers: path.receipt@.target().node.buffers.slice(
                start as int,
                end as int,
            ),
            offset_map,
        };
        let input_idx = self.compactors.len();
        self.compactors.push(CompactorImpl {
            input_buffers,
            input_nodes: Ghost(Map::empty()),
            input_aus: Ghost(Set::empty()),
            input_summaries: Ghost(Map::empty()),
            offset_map: Ghost(offset_map),
            filter,
            merge: None,
            merge_done: false,
        });
        if !compactor_refs_are_live(&self.compactors, &self.branch_likes) {
            self.compactors.pop();
            return BranchBetreeCompactBeginResult::Blocked;
        }
        let ghost access = PageAccess {
            betree_reads: reads@,
            branch_reads: Map::empty(),
            betree_writes: Map::empty(),
            branch_writes: Map::empty(),
        };
        proof {
            assert(path.nodes@[target_idx as int]@ == path.receipt@.target().node);
            assert(start < end <= path.receipt@.target().node.buffers.len());
            assert(self.compactors@[input_idx as int].filter.wf());
            assert(self.compactors@[input_idx as int].filter.target@
                == path.receipt@.target().node);
            assert(Parsedview::<Seq<Address>>::parsedv(
                &self.compactors@[input_idx as int].input_buffers,
            ) == path.receipt@.target().node.buffers.addrs.subrange(
                start as int,
                end as int,
            ));
            assert(path.receipt@.target().node.buffers.slice(
                start as int,
                end as int,
            ).addrs == path.receipt@.target().node.buffers.addrs.subrange(
                start as int,
                end as int,
            ));
            assert(self.compactors@[input_idx as int].input_buffers@.len()
                == end - start);
            assert(self.compactors@[input_idx as int].input_buffers@
                == path.nodes@[target_idx as int].buffers@.subrange(
                    start as int,
                    end as int,
                ));
            assert forall |i: int| 0 <= i
                < self.compactors@[input_idx as int].input_buffers@.len()
                implies (#[trigger] self.compactors@[input_idx as int]
                    .input_buffers@[i])@
                    == self.compactors@[input_idx as int].filter.target@
                        .buffers.addrs[start as int + i] by {
                assert(self.compactors@[input_idx as int]
                    .input_buffers@[i]
                    == path.nodes@[target_idx as int].buffers@[
                        start as int + i]);
                assert(self.compactors@[input_idx as int]
                    .input_buffers@[i]@
                    == path.receipt@.target().node.buffers.addrs[
                        start as int + i]);
            }
            assert(self.compactors@[input_idx as int].offset_map@
                == self.compactors@[input_idx as int].filter.target@
                    .make_offset_map().decrement(start as nat));
            assert(self.compactors@[input_idx as int]@ == input);
            assert(self.compactors@[input_idx as int].wf());
            assert(access.wf());
            assert(access.only_betree());
            assert_maps_equal!(access.reads(), reads@, addr => {});
            assert_maps_equal!(
                access.loaded_betree_reads(),
                to_betree_nodes(reads@),
                addr => {}
            );
            assert_maps_equal!(
                access.writes(),
                Map::<Address, RawPage>::empty(),
                addr => {}
            );
            assert(access.writes().is_empty());
            assert(compactor_views(self.compactors@)
                == compactor_views(old(self).compactors@).push(input));
            assert(compactor_receipt_views(self.compactors@)
                == compactor_receipt_views(old(self).compactors@)
                    .push(Map::empty())) by {
                assert_seqs_equal!(
                    compactor_receipt_views(self.compactors@),
                    compactor_receipt_views(old(self).compactors@)
                        .push(Map::empty()),
                    i => {
                        if i == old(self).compactors@.len() {
                            assert(self.compactors@[i].input_nodes@
                                == Map::<Address, BranchNode>::empty());
                        } else {
                            assert(self.compactors@[i]
                                == old(self).compactors@[i]);
                        }
                    }
                );
            }
            compactor_model_alignment_push_uninitialized(
                old(self).compactors@,
                self.ownership.branches.active_summary_map(),
                self.compactors@[input_idx as int],
            );
            assert_maps_equal!(
                access.loaded_branch_reads(),
                Map::empty(),
                addr => {}
            );
            assert_maps_equal!(
                access.loaded_betree_writes(),
                Map::empty(),
                addr => {}
            );
            assert_maps_equal!(
                access.loaded_branch_writes(),
                Map::empty(),
                addr => {}
            );
            assert(access.cached_access() == CachedBranchBetreeAccess {
                betree_reads: to_betree_nodes(reads@),
                ..CachedBranchBetreeAccess::empty()
            });
            assert(CachedBranchBetree::State::compact_begin(
                old(self).betree_i(),
                self.betree_i(),
                CachedBranchBetree::Label::InternalAccess {
                    access: access.cached_access(),
                },
                path.receipt@,
                start as nat,
                end as nat,
                to_betree_nodes(reads@),
            )) by {

            }
            assert(CachedBranchBetree::State::next_by(
                old(self).betree_i(),
                self.betree_i(),
                CachedBranchBetree::Label::InternalAccess {
                    access: access.cached_access(),
                },
                CachedBranchBetree::Step::compact_begin(
                    path.receipt@,
                    start as nat,
                    end as nat,
                    to_betree_nodes(reads@),
                ),
            )) by {
                reveal(CachedBranchBetree::State::next_by);
            }
            assert(CachedBranchBetree::State::next(
                old(self).betree_i(),
                self.betree_i(),
                CachedBranchBetree::Label::InternalAccess {
                    access: access.cached_access(),
                },
            )) by {
                reveal(CachedBranchBetree::State::next);
            }
            assert(self.wf());
            assert(AtomicBranchBetreeState::State::compact_begin(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::InternalAccess {
                    access,
                },
                self.betree_i(),
                path.receipt@,
                start as nat,
                end as nat,
                to_betree_nodes(reads@),
            )) by {

            }
            assert(exists |candidate: crate::implementation::CachedBranchBetree_v::LoadedBetreePath|
                AtomicBranchBetreeState::State::compact_begin(
                    old(self)@,
                    self@,
                    AtomicBranchBetreeState::Label::InternalAccess {
                        access,
                    },
                    self.betree_i(),
                    candidate,
                    start as nat,
                    end as nat,
                    access.loaded_betree_reads(),
                )) by {
                assert(AtomicBranchBetreeState::State::compact_begin(
                    old(self)@,
                    self@,
                    AtomicBranchBetreeState::Label::InternalAccess {
                        access,
                    },
                    self.betree_i(),
                    path.receipt@,
                    start as nat,
                    end as nat,
                    access.loaded_betree_reads(),
                ));
            }
            assert(AtomicBranchBetreeState::State::next_by(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::InternalAccess { access },
                AtomicBranchBetreeState::Step::compact_begin(
                    self.betree_i(),
                    path.receipt@,
                    start as nat,
                    end as nat,
                    access.loaded_betree_reads(),
                ),
            )) by {
                reveal(AtomicBranchBetreeState::State::next_by);
            }
            assert(AtomicBranchBetreeState::State::next(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::InternalAccess { access },
            )) by {
                reveal(AtomicBranchBetreeState::State::next);
            }
        }
        BranchBetreeCompactBeginResult::Began {
            input_idx,
            access: Ghost(access),
        }
    }

    pub fn compact_initialize_cursors(
        &mut self,
        cache: &FracCacheImpl,
        input_idx: usize,
        sources: Ghost<Seq<crate::betree::LinkedBranch_v::LinkedBranch<
            crate::allocation_layer::BranchTypes_v::Summary,
        >>>,
    )
        requires
            old(self).wf(),
            cache.wf(),
            input_idx < old(self).compactors.len(),
            old(self).compactors@[input_idx as int].merge is None,
            sources@.len()
                == old(self).compactors@[input_idx as int].input_buffers@.len(),
            forall |i: int| 0 <= i < sources@.len() ==> {
                let source = #[trigger] sources@[i];
                &&& source.valid_sealed_branch()
                &&& source.tight_disk_view_with_summary()
                &&& source.root
                    == old(self).compactors@[input_idx as int]
                        .input_buffers@[i]@
                &&& source.get_summary() <= compactor_owned_input_aus(
                    old(self).compactors@[input_idx as int],
                    old(self).ownership.branches.active_summary_map(),
                )
                &&& old(self).ownership.branches.active_summary_map()
                    .contains_key(source.root.au)
                &&& source.get_summary()
                    == old(self).ownership.branches.active_summary_map()[
                        source.root.au]
                &&& cached_branch_scan_valid(cache@, source)
            },
            forall |left: int, right: int, addr: Address|
                0 <= left < sources@.len()
                && 0 <= right < sources@.len()
                && sources@[left].disk_view.entries.contains_key(addr)
                && sources@[right].disk_view.entries.contains_key(addr)
                ==> sources@[left].disk_view.entries[addr]
                    == sources@[right].disk_view.entries[addr],
            forall |left: int, right: int|
                0 <= left < sources@.len()
                && 0 <= right < sources@.len()
                && sources@[left].root == sources@[right].root
                ==> sources@[left] == sources@[right],
            set_addrs_disjoint_aus(
                Parsedview::<Seq<Address>>::parsedv(
                    &old(self).compactors@[input_idx as int].input_buffers,
                ).to_set(),
            ),
        ensures
            self.wf(),
            self@ == old(self)@,
            self.root == old(self).root,
            self.ownership == old(self).ownership,
            self.branch_likes@ == old(self).branch_likes@,
            self.memtable == old(self).memtable,
            self.control == old(self).control,
            self.wip_branches@ == old(self).wip_branches@,
            compactor_views(self.compactors@)
                == compactor_views(old(self).compactors@),
            self.compactors@.len() == old(self).compactors@.len(),
            self.compactors@[input_idx as int].merge is Some,
            !self.compactors@[input_idx as int].merge_done,
            self.compactors@[input_idx as int].cache_inv(cache@),
            self.compactors@[input_idx as int].merge->0.output@.len() == 0,
    {
        let ghost selected_input_aus = compactor_owned_input_aus(
            self.compactors@[input_idx as int],
            self.ownership.branches.active_summary_map(),
        );
        proof {
            assert(self.control.metadata_loaded) by {
                if !self.control.metadata_loaded {
                    assert(self.betree_i() == empty_cached_betree());
                    assert(self.betree_i().compactors.len() == 0);
                    assert(compactor_views(self.compactors@).len()
                        == self.compactors@.len());
                    assert(false);
                }
            }
        }
        let mut cursors = Vec::<BranchScanCursor>::new();
        proof {
            establish_compactor_source_disks_agree(cursors@);
        }
        let mut cursor_idx = 0usize;
        while cursor_idx < self.compactors[input_idx].input_buffers.len()
            invariant
                self.wf(),
                input_idx < self.compactors.len(),
                self.compactors@[input_idx as int].merge is None,
                sources@.len()
                    == self.compactors@[input_idx as int].input_buffers@.len(),
                cursor_idx as int
                    <= self.compactors@[input_idx as int]
                        .input_buffers@.len(),
                cursors@.len() == cursor_idx,
                forall |i: int| 0 <= i < sources@.len() ==> {
                    let source = #[trigger] sources@[i];
                    &&& source.valid_sealed_branch()
                    &&& source.tight_disk_view_with_summary()
                    &&& source.root
                        == self.compactors@[input_idx as int]
                            .input_buffers@[i]@
                    &&& source.get_summary()
                        <= selected_input_aus
                    &&& self.ownership.branches.active_summary_map()
                        .contains_key(source.root.au)
                    &&& source.get_summary()
                        == self.ownership.branches.active_summary_map()[
                            source.root.au]
                    &&& cached_branch_scan_valid(cache@, source)
                },
                forall |i: int| 0 <= i < cursors@.len() ==> {
                    &&& (#[trigger] cursors@[i]).wf()
                    &&& cursors@[i].receipt_wf()
                    &&& cursors@[i].emitted@.len() == 0
                    &&& cursors@[i].scanned@.is_empty()
                    &&& crate::implementation::BranchScanCursorImpl_v::
                        branch_scan_entries_strictly_sorted(
                            cursors@[i].remaining(),
                        )
                    &&& cursors@[i].source@ == sources@[i]
                    &&& cursors@[i].source@.root
                        == self.compactors@[input_idx as int]
                            .filter.target@.buffers.addrs[
                                self.compactors@[input_idx as int]
                                    .filter.start as int + i]
                    &&& cursors@[i].source@.get_summary()
                        <= selected_input_aus
                    &&& self.ownership.branches.active_summary_map()
                        .contains_key(
                            cursors@[i].source@.root.au,
                        )
                    &&& cursors@[i].source@.get_summary()
                        == self.ownership.branches.active_summary_map()[
                                cursors@[i].source@.root.au]
                    &&& cursors@[i].cache_inv(cache@)
                },
                compactor_source_disks_agree(cursors@),
            decreases self.compactors@[input_idx as int]
                .input_buffers@.len() - cursor_idx as int,
        {
            let root = self.compactors[input_idx]
                .input_buffers[cursor_idx];
            let cursor = BranchScanCursor::new(
                root,
                Ghost(sources@[cursor_idx as int]),
            );
            proof {
                assert(cursor.cache_inv(cache@));
                assert(root@
                    == self.compactors@[input_idx as int]
                        .filter.target@.buffers.addrs[
                            self.compactors@[input_idx as int]
                                .filter.start as int + cursor_idx as int]);
                assert(cursor.source@.root
                    == self.compactors@[input_idx as int]
                        .filter.target@.buffers.addrs[
                            self.compactors@[input_idx as int]
                                .filter.start as int + cursor_idx as int]);
            }
            cursors.push(cursor);
            proof {
                assert forall |left: int, right: int, addr: Address|
                    0 <= left < cursors@.len()
                    && 0 <= right < cursors@.len()
                    && cursors@[left].source@.disk_view.entries
                        .contains_key(addr)
                    && cursors@[right].source@.disk_view.entries
                        .contains_key(addr)
                    implies cursors@[left].source@.disk_view.entries[addr]
                        == cursors@[right].source@.disk_view.entries[addr] by {
                    assert(cursors@[left].source@ == sources@[left]);
                    assert(cursors@[right].source@ == sources@[right]);
                }
                assert forall |left: int, right: int|
                    0 <= left < cursors@.len()
                    && 0 <= right < cursors@.len()
                    && cursors@[left].source@.root
                        == cursors@[right].source@.root
                    implies cursors@[left].source@
                        == cursors@[right].source@ by {
                    assert(cursors@[left].source@ == sources@[left]);
                    assert(cursors@[right].source@ == sources@[right]);
                }
                establish_compactor_source_disks_agree(cursors@);
            }
            cursor_idx += 1;
        }
        let filter = self.compactors[input_idx].filter.clone_checked();
        proof {
            assert(filter.target@
                == self.compactors@[input_idx as int].filter.target@);
            assert(filter.start
                == self.compactors@[input_idx as int].filter.start);
            assert(filter.end
                == self.compactors@[input_idx as int].filter.end);
            assert(cursors@.len() == filter.end - filter.start);
            assert forall |i: int| 0 <= i < cursors@.len()
                implies (#[trigger] cursors@[i]).scanned@.is_empty() by { }
            assert forall |i: int| 0 <= i < cursors@.len()
                implies crate::implementation::CompactorMergeCursorImpl_v::
                    keyed_entries_strictly_sorted(
                        (#[trigger] cursors@[i]).remaining(),
                    ) by {
                assert forall |left: int, right: int|
                    0 <= left < right < cursors@[i].remaining().len()
                    implies Key::lt(
                        (#[trigger] cursors@[i].remaining()[left]).key,
                        (#[trigger] cursors@[i].remaining()[right]).key,
                    ) by {
                    assert(crate::implementation::BranchScanCursorImpl_v::
                        branch_scan_entries_strictly_sorted(
                            cursors@[i].remaining(),
                        ));
                }
            }
        }
        let merge = CompactorMergeCursor::new(cursors, filter);
        proof {
            assert(merge.source_aus()
                <= selected_input_aus) by {
                assert forall |au: AU|
                    #[trigger] merge.source_aus().contains(au)
                    implies selected_input_aus.contains(au) by {
                    let i = choose |i: int|
                        0 <= i < merge.cursors@.len()
                        && merge.cursors@[i]
                            .source@.get_summary().contains(au);
                    assert(merge.cursors@[i].source@.get_summary()
                        <= selected_input_aus);
                }
            }
            assert(merge.cache_inv(cache@)) by {
                assert forall |i: int| 0 <= i < merge.cursors@.len()
                    implies (#[trigger] merge.cursors@[i]).cache_inv(cache@) by {
                    assert(merge.cursors@[i].cache_inv(cache@));
                }
            }
        }
        let ghost old_compactors = self.compactors@;
        let mut compactor = self.compactors.remove(input_idx);
        compactor.input_aus = Ghost(selected_input_aus);
        compactor.input_summaries = Ghost(
            self.ownership.branches.active_summary_map().restrict(
                compactor_input_root_aus(compactor),
            ),
        );
        compactor.input_nodes = Ghost(merge.scanned_nodes());
        compactor.merge = Some(merge);
        compactor.merge_done = false;
        self.compactors.insert(input_idx, compactor);
        proof {
            assert(self.compactors@ == old_compactors.update(
                input_idx as int,
                self.compactors@[input_idx as int],
            ));
            let current = self.compactors@[input_idx as int];
            assert(map_with_disjoint_values(current.input_summaries@)) by {
                assert forall |left: AU, right: AU|
                    #[trigger] current.input_summaries@.contains_key(left)
                    && #[trigger] current.input_summaries@.contains_key(right)
                    && left != right
                    implies current.input_summaries@[left].disjoint(
                        current.input_summaries@[right],
                    ) by {
                    assert(self.ownership.branches.active@
                        .contains_key(left));
                    assert(self.ownership.branches.active@
                        .contains_key(right));
                    assert(self.ownership.branches.records()
                        .contains_key(left));
                    assert(self.ownership.branches.records()
                        .contains_key(right));
                    assert(self.ownership.branches.records()[left].summary
                        == self.ownership.branches.active_summary_map()[left]);
                    assert(self.ownership.branches.records()[right].summary
                        == self.ownership.branches.active_summary_map()[right]);
                    assert(self.ownership.branches.summaries_pairwise_disjoint());
                }
            }
            assert(compactor_input_root_aus(current)
                <= self.ownership.branches.active_summary_map().dom()) by {
                assert forall |au: AU|
                    #[trigger] compactor_input_root_aus(current).contains(au)
                    implies self.ownership.branches.active_summary_map()
                        .contains_key(au) by {
                    let root = crate::disk::GenericDisk_v::to_aus_get_addr(
                        Parsedview::<Seq<Address>>::parsedv(
                            &current.input_buffers,
                        ).to_set(),
                        au,
                    );
                    let i = choose |i: int|
                        0 <= i < current.input_buffers@.len()
                        && current.input_buffers@[i]@ == root;
                    assert(current.merge->0.cursors@[i].source@.root == root);
                    assert(self.ownership.branches.active_summary_map()
                        .contains_key(root.au));
                }
            }
            assert forall |i: int|
                0 <= i < current.merge->0.cursors@.len()
                implies {
                    let source = (#[trigger] current.merge->0.cursors@[i]).source@;
                    &&& current.input_summaries@.contains_key(source.root.au)
                    &&& source.get_summary()
                        == current.input_summaries@[source.root.au]
                } by {
                let source = current.merge->0.cursors@[i].source@;
                assert(source.root
                    == current.input_buffers@[i]@);
                let roots = Parsedview::<Seq<Address>>::parsedv(
                    &current.input_buffers,
                ).to_set();
                assert(Parsedview::<Seq<Address>>::parsedv(
                    &current.input_buffers,
                )[i] == source.root);
                assert(exists |j: int| 0 <= j < Parsedview::<Seq<Address>>::parsedv(
                    &current.input_buffers,
                ).len() && Parsedview::<Seq<Address>>::parsedv(
                    &current.input_buffers,
                )[j] == source.root);
                assert(roots.contains(source.root));
                crate::disk::GenericDisk_v::to_aus_domain(roots);
                assert(compactor_input_root_aus(current)
                    .contains(source.root.au));
                assert(current.input_summaries@[source.root.au]
                    == self.ownership.branches.active_summary_map()[
                        source.root.au]);
            }
            assert(current.input_nodes@ == current.merge->0.scanned_nodes());
            assert(self.compactors@[input_idx as int].wf());
            assert(self.compactors@[input_idx as int].cache_inv(cache@)) by {
                assert forall |i: int|
                    0 <= i < self.compactors@[input_idx as int]
                        .merge->0.cursors@.len()
                    implies (#[trigger] self.compactors@[input_idx as int]
                        .merge->0.cursors@[i]).cache_inv(cache@) by {
                    assert(self.compactors@[input_idx as int]
                        .merge->0.cursors@[i].cache_inv(cache@));
                }
            }
            assert forall |i: int| 0 <= i < self.compactors@.len()
                implies (#[trigger] self.compactors@[i]).wf() by {
                if i != input_idx as int {
                    assert(self.compactors@[i]
                        == old(self).compactors@[i]);
                }
            }
            assert(compactor_views(self.compactors@)
                == compactor_views(old(self).compactors@)) by {
                assert forall |i: int| 0 <= i < self.compactors@.len()
                    implies #[trigger] compactor_views(self.compactors@)[i]
                        == compactor_views(old(self).compactors@)[i] by {
                    assert(self.compactors@[i]@
                        == old(self).compactors@[i]@);
                }
            }
            assert(self.compactors@[input_idx as int].input_aus@
                == compactor_owned_input_aus(
                    self.compactors@[input_idx as int],
                    self.ownership.branches.active_summary_map(),
                ));
            assert(compactor_input_root_aus(
                self.compactors@[input_idx as int],
            ) <= self.ownership.branches.active_summary_map().dom());
            assert(self.compactors@[input_idx as int].input_summaries@
                == self.ownership.branches.active_summary_map().restrict(
                    compactor_input_root_aus(
                        self.compactors@[input_idx as int],
                    ),
                ));
            compactor_model_alignment_update(
                old_compactors,
                self.ownership.branches.active_summary_map(),
                input_idx as int,
                self.compactors@[input_idx as int],
            );
            assert(self.wf());
            assert(self.compactors@[input_idx as int].input_nodes@
                == old(self).compactors@[input_idx as int].input_nodes@);
            assert(compactor_receipt_views(self.compactors@)
                == compactor_receipt_views(old(self).compactors@)) by {
                assert_seqs_equal!(
                    compactor_receipt_views(self.compactors@),
                    compactor_receipt_views(old(self).compactors@),
                    i => {
                        if i != input_idx as int {
                            assert(self.compactors@[i]
                                == old(self).compactors@[i]);
                        }
                    }
                );
            }
            assert(self@ == old(self)@);
        }
    }

    pub fn compact_stream_step(
        &mut self,
        cache: &mut FracCacheImpl,
        input_idx: usize,
        branch_idx: usize,
    ) -> (result: BranchBetreeCompactStreamResult)
        requires
            old(self).wf(),
            old(cache).wf(),
            input_idx < old(self).compactors.len(),
            branch_idx < old(self).wip_branches.len(),
            old(self).compactors@[input_idx as int].merge is Some,
            !old(self).compactors@[input_idx as int].merge_done,
            old(self).compactors@[input_idx as int]
                .cache_inv(old(cache)@),
            old(self).wip_branches@[branch_idx as int]
                .has_streaming_builder(),
            old(self).wip_branches@[branch_idx as int]
                .streaming_builder().phase is Reading,
            old(self).wip_branches@[branch_idx as int]
                .cache_inv(old(cache)@),
            old(self).wip_branches@[branch_idx as int]
                .streaming_builder().pending is None,
            old(self).wip_branches@[branch_idx as int]
                .streaming_builder().deferred is None,
            old(self).wip_branches@[branch_idx as int]
                .streaming_builder().source_entries@
                == compact_stream_entries(
                    old(self).compactors@[input_idx as int]
                        .merge->0.output@,
                ),
        ensures
            self.wf(),
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            self.root == old(self).root,
            self.ownership == old(self).ownership,
            self.branch_likes == old(self).branch_likes,
            self.memtable == old(self).memtable,
            self.control == old(self).control,
            compactor_views(self.compactors@)
                == compactor_views(old(self).compactors@),
            self.compactors@.len() == old(self).compactors@.len(),
            self.wip_branches@.len() == old(self).wip_branches@.len(),
            self.wip_branches@[branch_idx as int].mini_allocator
                == old(self).wip_branches@[branch_idx as int]
                    .mini_allocator,
            self.wip_branches@[branch_idx as int].cache_inv(cache@),
            forall |i: int| 0 <= i < self.compactors@.len()
                && i != input_idx as int
                ==> self.compactors@[i] == old(self).compactors@[i],
            forall |i: int| 0 <= i < self.wip_branches@.len()
                && i != branch_idx as int
                ==> self.wip_branches@[i] == old(self).wip_branches@[i],
            self.compactors@[input_idx as int].merge is Some,
            self.compactors@[input_idx as int].cache_inv(cache@),
            self.wip_branches@[branch_idx as int]
                .has_streaming_builder(),
            self.wip_branches@[branch_idx as int]
                .streaming_builder().phase is Reading,
            self.wip_branches@[branch_idx as int]
                .streaming_builder().source_entries@
                == compact_stream_entries(
                    self.compactors@[input_idx as int].merge->0.output@,
                ),
            match result {
                BranchBetreeCompactStreamResult::ReadAdvanced { reads } => {
                    &&& cache@ == old(cache)@
                    &&& reads@.len() == 1
                    &&& AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAccess {
                            access: PageAccess {
                                betree_reads: Map::empty(),
                                branch_reads: reads@,
                                betree_writes: Map::empty(),
                                branch_writes: Map::empty(),
                            },
                        },
                    )
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        Cache::Label::Access {
                            reads: reads@,
                            writes: Map::empty(),
                        },
                    )
                },
                BranchBetreeCompactStreamResult::ItemAccepted => {
                    &&& cache@ == old(cache)@
                    &&& self.wip_branches@[branch_idx as int]
                        .streaming_builder().pending is None
                },
                BranchBetreeCompactStreamResult::PageReady => {
                    &&& cache@ == old(cache)@
                    &&& self.wip_branches@[branch_idx as int]
                        .streaming_builder().pending is Some
                },
                BranchBetreeCompactStreamResult::Skipped
                    => {
                    cache@ == old(cache)@
                },
                BranchBetreeCompactStreamResult::Done => {
                    &&& cache@ == old(cache)@
                    &&& self.compactors@[input_idx as int].merge_done
                },
                BranchBetreeCompactStreamResult::NeedCacheLoad {
                    addr,
                    handle,
                } => {
                    &&& old(self).compactors@[input_idx as int]
                        .input_aus@.contains(addr@.au)
                    &&& old(self).compactors@[input_idx as int]
                        .input_aus@
                        <= old(self).ownership.branches
                            .active_summary_aus()
                    &&& cache.entry_fetched(&addr)
                    &&& cache.valid_load_handle(&addr, handle)
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        crate::implementation::FracCacheImpl_v::cache_load_label(
                            &addr,
                        ),
                    )
                },
                BranchBetreeCompactStreamResult::CacheFull
                | BranchBetreeCompactStreamResult::Blocked
                | BranchBetreeCompactStreamResult::InvalidPage => {
                    cache@ == old(cache)@
                },
            },
            !(result is Done) ==>
                !self.compactors@[input_idx as int].merge_done,
            match result {
                BranchBetreeCompactStreamResult::ReadAdvanced { .. } => true,
                _ => self@ == old(self)@,
            },
    {
        proof {
            expose_compactor_model_alignment(
                self.compactors@,
                self.ownership.branches.active_summary_map(),
            );
            self.ownership.branches.active_summary_projection();
            compactor_owned_input_aus_subset_summary(
                self.compactors@[input_idx as int],
                self.ownership.branches.active_summary_map(),
            );
            assert(self.compactors@[input_idx as int].input_aus@
                <= self.ownership.branches.active_summary_aus());
            assert(self.control.metadata_loaded) by {
                if !self.control.metadata_loaded {
                    assert(self.betree_i() == empty_cached_betree());
                    assert(self.betree_i().compactors.len() == 0);
                    assert(compactor_views(self.compactors@).len()
                        == self.compactors@.len());
                    assert(false);
                }
            }
        }
        let ghost old_compactors = self.compactors@;
        let mut compactor = self.compactors.remove(input_idx);
        let merge_opt = compactor.merge.take();
        let mut merge = merge_opt.unwrap();
        let ghost filter_buffers = merge.filter.target@.buffers.addrs;
        let ghost filter_pivots = merge.filter.target@.pivots.pivots;
        let ghost filter_flushed = merge.filter.target@.flushed.offsets;
        proof {
            assert(filter_buffers
                == compactor.filter.target@.buffers.addrs);
            assert(filter_pivots
                == compactor.filter.target@.pivots.pivots);
            assert(filter_flushed
                == compactor.filter.target@.flushed.offsets);
        }
        let merge_result = merge.step(cache);
        proof {
            assert(merge.filter.target@.buffers.addrs == filter_buffers);
            assert(merge.filter.target@.pivots.pivots == filter_pivots);
            assert(merge.filter.target@.flushed.offsets == filter_flushed);
            assert(merge.filter.target@.buffers.addrs
                == compactor.filter.target@.buffers.addrs);
            assert(merge.filter.target@.pivots.pivots
                == compactor.filter.target@.pivots.pivots);
            assert(merge.filter.target@.flushed.offsets
                == compactor.filter.target@.flushed.offsets);
            old(self).wip_branches@[branch_idx as int]
                .cache_inv_preserved_by_valid_reads(
                    old(cache)@,
                    cache@,
                );
        }
        if merge_result.is_done() {
            compactor.merge_done = true;
        }
        compactor.input_nodes = Ghost(merge.scanned_nodes());
        compactor.merge = Some(merge);
        self.compactors.insert(input_idx, compactor);
        proof {
            assert(self.compactors@ == old_compactors.update(
                input_idx as int,
                self.compactors@[input_idx as int],
            ));
            let current = self.compactors@[input_idx as int];
            let previous = old_compactors[input_idx as int];
            assert(compactor_input_root_aus(current)
                == compactor_input_root_aus(previous));
            assert(compactor_input_root_aus(current)
                <= self.ownership.branches.active_summary_map().dom());
            assert(current.input_summaries@
                == self.ownership.branches.active_summary_map().restrict(
                    compactor_input_root_aus(current),
                ));
            assert forall |i: int|
                0 <= i < current.merge->0.cursors@.len()
                implies {
                    let source = (#[trigger] current.merge->0.cursors@[i]).source@;
                    &&& current.input_summaries@.contains_key(source.root.au)
                    &&& source.get_summary()
                        == current.input_summaries@[source.root.au]
                } by {
                assert(current.merge->0.cursors@[i].source@
                    == previous.merge->0.cursors@[i].source@);
            }
            assert(current.wf());
            assert forall |i: int| 0 <= i < self.compactors@.len()
                implies (#[trigger] self.compactors@[i]).wf() by {
                if i != input_idx as int {
                    assert(self.compactors@[i] == old_compactors[i]);
                }
            }
            assert(compactor_views(self.compactors@)
                == compactor_views(old_compactors)) by {
                assert forall |i: int| 0 <= i < self.compactors@.len()
                    implies #[trigger] compactor_views(self.compactors@)[i]
                        == compactor_views(old_compactors)[i] by {
                    if i != input_idx as int {
                        assert(self.compactors@[i] == old_compactors[i]);
                    }
                }
            }
            assert(self.compactors@[input_idx as int].input_aus@
                == compactor_owned_input_aus(
                    self.compactors@[input_idx as int],
                    self.ownership.branches.active_summary_map(),
                )) by {
                assert(old_compactors[input_idx as int].input_aus@
                    == compactor_owned_input_aus(
                        old_compactors[input_idx as int],
                        self.ownership.branches.active_summary_map(),
                    ));
                assert(self.compactors@[input_idx as int].input_buffers@
                    == old_compactors[input_idx as int].input_buffers@);
            }
            compactor_model_alignment_update(
                old_compactors,
                self.ownership.branches.active_summary_map(),
                input_idx as int,
                self.compactors@[input_idx as int],
            );
            assert(self.wf());
            if merge_result is ReadAdvanced {
                let reads = merge_result->reads@;
                assert(self.compactors@[input_idx as int].input_nodes@
                    == old(self).compactors@[input_idx as int]
                        .input_nodes@.union_prefer_right(
                            to_branch_nodes(reads),
                        ));
            } else {
                assert(self@ == old(self)@);
            }
        }
        match merge_result {
            CompactorMergeStepResult::ReadAdvanced { reads } => {
                proof {
                    assert(self.compactors@[input_idx as int].input_nodes@
                        == old(self).compactors@[input_idx as int]
                            .input_nodes@.union_prefer_right(
                                to_branch_nodes(reads@),
                            ));
                    assert(reads@.dom() <= addresses_in_aus(
                        old(self).compactors@[input_idx as int].input_aus@,
                    )) by {
                        assert(reads@.dom() <= addresses_in_aus(
                            self.compactors@[input_idx as int]
                                .merge->0.source_aus(),
                        ));
                        assert(self.compactors@[input_idx as int]
                            .merge->0.source_aus()
                            <= self.compactors@[input_idx as int]
                                .input_aus@);
                    }
                    assert(old(self).compactors@[input_idx as int].input_aus@
                        == old(self).betree_i().compactor_input_aus(
                            input_idx as int,
                        ));
                    assert(to_branch_nodes(reads@).dom()
                        <= addresses_in_aus(
                            old(self).betree_i().compactor_input_aus(
                                input_idx as int,
                            ),
                        )) by {
                        assert(to_branch_nodes(reads@).dom() == reads@.dom());
                    }
                    assert(to_branch_nodes(reads@).dom() == reads@.dom()) by {
                        assert_sets_equal!(
                            to_branch_nodes(reads@).dom(),
                            reads@.dom(),
                            addr => {}
                        );
                    }
                    assert(to_branch_nodes(reads@).dom().finite());
                    assert(to_branch_nodes(reads@).len() == reads@.len());
                    assert(compactor_views(self.compactors@)
                        == old(self).betree_i().compactors) by {
                        assert_seqs_equal!(
                            compactor_views(self.compactors@),
                            old(self).betree_i().compactors,
                            i => {
                                if i == input_idx as int {
                                    assert(self.compactors@[i]@
                                        == old(self).compactors@[i]@);
                                } else {
                                    assert(self.compactors@[i]
                                        == old(self).compactors@[i]);
                                }
                            }
                        );
                    }
                    assert(compactor_receipt_views(self.compactors@)
                        == old(self).betree_i().compactor_receipts.update(
                            input_idx as int,
                            old(self).betree_i().compactor_receipts[
                                input_idx as int].union_prefer_right(
                                    to_branch_nodes(reads@),
                                ),
                        )) by {
                        assert_seqs_equal!(
                            compactor_receipt_views(self.compactors@),
                            old(self).betree_i().compactor_receipts.update(
                                input_idx as int,
                                old(self).betree_i().compactor_receipts[
                                    input_idx as int].union_prefer_right(
                                        to_branch_nodes(reads@),
                                    ),
                            ),
                            i => {
                                if i != input_idx as int {
                                    assert(self.compactors@[i]
                                        == old(self).compactors@[i]);
                                }
                            }
                        );
                    }
                    let ghost scan_access = PageAccess {
                        betree_reads: Map::empty(),
                        branch_reads: reads@,
                        betree_writes: Map::empty(),
                        branch_writes: Map::empty(),
                    };
                    assert(scan_access.only_branch());
                    assert(scan_access.read_only());
                    scan_access.cached_branch_read_only_shape();
                    assert(scan_access.loaded_branch_reads()
                        == to_branch_nodes(reads@));
                    assert(CachedBranchBetree::State::compact_scan_page(
                        old(self).betree_i(),
                        self.betree_i(),
                        CachedBranchBetree::Label::InternalAccess {
                            access: PageAccess {
                                betree_reads: Map::empty(),
                                branch_reads: reads@,
                                betree_writes: Map::empty(),
                                branch_writes: Map::empty(),
                            }.cached_access(),
                        },
                        input_idx as int,
                        to_branch_nodes(reads@),
                    )) by {
                    }
                    assert(CachedBranchBetree::State::next_by(
                        old(self).betree_i(),
                        self.betree_i(),
                        CachedBranchBetree::Label::InternalAccess {
                            access: scan_access.cached_access(),
                        },
                        CachedBranchBetree::Step::compact_scan_page(
                            input_idx as int,
                            to_branch_nodes(reads@),
                        ),
                    )) by {
                        reveal(CachedBranchBetree::State::next_by);
                    }
                    assert(CachedBranchBetree::State::next(
                        old(self).betree_i(),
                        self.betree_i(),
                        CachedBranchBetree::Label::InternalAccess {
                            access: scan_access.cached_access(),
                        },
                    )) by {
                        reveal(CachedBranchBetree::State::next);
                    }
                    assert(self.compactors@[input_idx as int].input_aus@
                        == compactor_owned_input_aus(
                            self.compactors@[input_idx as int],
                            self.ownership.branches.active_summary_map(),
                        ));
                    assert(self.wf());
                    assert(AtomicBranchBetreeState::State::compact_scan_page(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAccess {
                            access: PageAccess {
                                betree_reads: Map::empty(),
                                branch_reads: reads@,
                                betree_writes: Map::empty(),
                                branch_writes: Map::empty(),
                            },
                        },
                        self.betree_i(),
                        input_idx as int,
                        to_branch_nodes(reads@),
                    )) by {
                    }
                    assert(AtomicBranchBetreeState::State::next_by(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAccess {
                            access: PageAccess {
                                betree_reads: Map::empty(),
                                branch_reads: reads@,
                                betree_writes: Map::empty(),
                                branch_writes: Map::empty(),
                            },
                        },
                        AtomicBranchBetreeState::Step::compact_scan_page(
                            self.betree_i(),
                            input_idx as int,
                            to_branch_nodes(reads@),
                        ),
                    )) by {
                        reveal(AtomicBranchBetreeState::State::next_by);
                    }
                    assert(AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAccess {
                            access: PageAccess {
                                betree_reads: Map::empty(),
                                branch_reads: reads@,
                                betree_writes: Map::empty(),
                                branch_writes: Map::empty(),
                            },
                        },
                    )) by {
                        reveal(AtomicBranchBetreeState::State::next);
                    }
                }
                BranchBetreeCompactStreamResult::ReadAdvanced { reads }
            },
            CompactorMergeStepResult::Item { item } => {
                let ghost old_branches = self.wip_branches@;
                let mut branch = self.wip_branches.remove(branch_idx);
                let entry = MemtableEntry {
                    key: item.key,
                    message: item.message,
                };
                proof {
                    assert forall |i: int| 0 <= i
                        < branch.streaming_builder().source_entries@.len()
                        implies (#[trigger]
                            branch.streaming_builder().source_entries@[i])
                                .key.0 < entry.key.0 by {
                        let ghost old_output = old_compactors[
                            input_idx as int].merge->0.output@;
                        let ghost new_output = self.compactors[
                            input_idx as int].merge->0.output@;
                        assert(self.compactors@[input_idx as int]
                            .merge->0.output@
                            == old_output.push(item));
                        compact_stream_entries_index(old_output, i);
                        assert(branch.streaming_builder()
                            .source_entries@[i].key == old_output[i].key);
                        assert(crate::implementation::CompactorMergeCursorImpl_v::
                            keyed_entries_strictly_sorted(
                                new_output,
                            ));
                        assert(new_output[i] == old_output[i]);
                        assert(new_output.last() == item);
                        assert(Key::lt(new_output[i].key, item.key));
                    }
                }
                let push_result = branch.push_streaming_entry(entry);
                self.wip_branches.insert(branch_idx, branch);
                proof {
                    assert(self.wip_branches@ == old_branches.update(
                        branch_idx as int,
                        self.wip_branches@[branch_idx as int],
                    ));
                    assert(bulk_branch_views(self.wip_branches@)
                        == bulk_branch_views(old_branches)) by {
                        assert forall |i: int| 0 <= i
                            < self.wip_branches@.len()
                            implies #[trigger]
                                self.wip_branches@[i]@ == old_branches[i]@ by {
                            if i != branch_idx as int {
                                assert(self.wip_branches@[i]
                                    == old_branches[i]);
                            }
                        }
                    }
                    assert(bulk_builders_wf(
                        self.wip_branches@,
                        &self.memtable,
                    )) by {
                        assert forall |i: int| 0 <= i
                            < self.wip_branches@.len()
                            implies (#[trigger] self.wip_branches@[i])
                                .bulk_builder_wf(&self.memtable) by {
                            if i != branch_idx as int {
                                assert(self.wip_branches@[i]
                                    == old_branches[i]);
                            }
                        }
                    }
                    compact_stream_entries_push(
                        old_compactors[input_idx as int].merge->0.output@,
                        item,
                    );
                    assert(self.wip_branches@[branch_idx as int]
                        .streaming_builder().source_entries@
                        == compact_stream_entries(
                            self.compactors@[input_idx as int]
                                .merge->0.output@,
                        ));
                    assert(self.wf());
                    assert(self@ == old(self)@);
                }
                match push_result {
                    crate::implementation::StreamingBranchBuilderImpl_v::
                        StreamingBuilderInputResult::Accepted => {
                        BranchBetreeCompactStreamResult::ItemAccepted
                    },
                    crate::implementation::StreamingBranchBuilderImpl_v::
                        StreamingBuilderInputResult::PageReady => {
                        BranchBetreeCompactStreamResult::PageReady
                    },
                }
            },
            CompactorMergeStepResult::Skipped => {
                BranchBetreeCompactStreamResult::Skipped
            },
            CompactorMergeStepResult::Done => {
                proof {
                    assert(self.compactors@[input_idx as int].merge_done);
                }
                BranchBetreeCompactStreamResult::Done
            },
            CompactorMergeStepResult::NeedCacheLoad { addr, handle } => {
                proof {
                    assert(old_compactors[input_idx as int]
                        .merge->0.source_aus().contains(addr@.au));
                    assert(old_compactors[input_idx as int]
                        .merge->0.source_aus()
                        <= old_compactors[input_idx as int].input_aus@);
                }
                BranchBetreeCompactStreamResult::NeedCacheLoad {
                    addr,
                    handle,
                }
            },
            CompactorMergeStepResult::CacheFull => {
                BranchBetreeCompactStreamResult::CacheFull
            },
            CompactorMergeStepResult::Blocked => {
                BranchBetreeCompactStreamResult::Blocked
            },
            CompactorMergeStepResult::InvalidPage => {
                BranchBetreeCompactStreamResult::InvalidPage
            },
        }
    }

    pub fn compact_finish_streaming_input(
        &mut self,
        input_idx: usize,
        branch_idx: usize,
    ) -> (result: StreamingFinishInputResult)
        requires
            old(self).wf(),
            input_idx < old(self).compactors.len(),
            branch_idx < old(self).wip_branches.len(),
            old(self).compactors@[input_idx as int].merge is Some,
            old(self).compactors@[input_idx as int].merge_done,
            old(self).wip_branches@[branch_idx as int]
                .has_streaming_builder(),
            old(self).wip_branches@[branch_idx as int]
                .streaming_builder().phase is Reading,
            old(self).wip_branches@[branch_idx as int]
                .streaming_builder().pending is None,
            old(self).wip_branches@[branch_idx as int]
                .streaming_builder().deferred is None,
            old(self).wip_branches@[branch_idx as int]
                .streaming_builder().source_entries@
                == compact_stream_entries(
                    old(self).compactors@[input_idx as int]
                        .merge->0.output@,
                ),
        ensures
            self.wf(),
            self@ == old(self)@,
            self.root == old(self).root,
            self.ownership == old(self).ownership,
            self.branch_likes == old(self).branch_likes,
            self.memtable == old(self).memtable,
            self.recovery == old(self).recovery,
            self.control == old(self).control,
            self.compactors@ == old(self).compactors@,
            self.wip_branches@.len() == old(self).wip_branches@.len(),
            self.wip_branches@[branch_idx as int].mini_allocator
                == old(self).wip_branches@[branch_idx as int]
                    .mini_allocator,
            forall |cache: Cache::State|
                self.wip_branches@[branch_idx as int].cache_inv(cache)
                    == old(self).wip_branches@[branch_idx as int]
                        .cache_inv(cache),
            self.wip_branches@[branch_idx as int]
                .has_streaming_builder(),
            self.wip_branches@[branch_idx as int]
                .streaming_builder().source_entries@
                == compact_stream_entries(
                    self.compactors@[input_idx as int].merge->0.output@,
                ),
            match result {
                StreamingFinishInputResult::Empty => {
                    self.wip_branches@[branch_idx as int]
                        .streaming_builder().phase is Empty
                },
                StreamingFinishInputResult::RootReady => {
                    self.wip_branches@[branch_idx as int]
                        .streaming_builder().phase is ReadyLeafRoot
                },
                StreamingFinishInputResult::Continue => {
                    self.wip_branches@[branch_idx as int]
                        .streaming_builder().phase is Finishing
                },
            },
    {
        let ghost old_branches = self.wip_branches@;
        let mut branch = self.wip_branches.remove(branch_idx);
        let result = branch.finish_streaming_input();
        let ghost post_phase = branch.streaming_builder().phase;
        let ghost finish_wf = match result {
            StreamingFinishInputResult::Empty => post_phase is Empty,
            StreamingFinishInputResult::RootReady => {
                post_phase is ReadyLeafRoot
            },
            StreamingFinishInputResult::Continue => post_phase is Finishing,
        };
        let ghost post_branch = branch;
        self.wip_branches.insert(branch_idx, branch);
        proof {
            assert(finish_wf);
            assert(self.wip_branches@[branch_idx as int] == post_branch);
            assert(self.wip_branches@[branch_idx as int]
                .streaming_builder().phase == post_phase);
            assert(self.wip_branches@ == old_branches.update(
                branch_idx as int,
                self.wip_branches@[branch_idx as int],
            ));
            assert(bulk_branch_views(self.wip_branches@)
                == bulk_branch_views(old_branches)) by {
                assert forall |i: int| 0 <= i < self.wip_branches@.len()
                    implies #[trigger] self.wip_branches@[i]@
                        == old_branches[i]@ by {
                    if i != branch_idx as int {
                        assert(self.wip_branches@[i] == old_branches[i]);
                    }
                }
            }
            assert(bulk_builders_wf(
                self.wip_branches@,
                &self.memtable,
            )) by {
                assert forall |i: int| 0 <= i < self.wip_branches@.len()
                    implies (#[trigger] self.wip_branches@[i])
                        .bulk_builder_wf(&self.memtable) by {
                    if i != branch_idx as int {
                        assert(self.wip_branches@[i] == old_branches[i]);
                    }
                }
            }
            assert(self.wf());
            assert(self@ == old(self)@);
        }
        match result {
            StreamingFinishInputResult::Empty => {
                proof {
                    assert(self.wip_branches@[branch_idx as int]
                        .streaming_builder().phase is Empty);
                }
                StreamingFinishInputResult::Empty
            },
            StreamingFinishInputResult::RootReady => {
                proof {
                    assert(self.wip_branches@[branch_idx as int]
                        .streaming_builder().phase is ReadyLeafRoot);
                }
                StreamingFinishInputResult::RootReady
            },
            StreamingFinishInputResult::Continue => {
                proof {
                    assert(self.wip_branches@[branch_idx as int]
                        .streaming_builder().phase is Finishing);
                }
                StreamingFinishInputResult::Continue
            },
        }
    }

    pub fn compact_finish_streaming_level(
        &mut self,
        input_idx: usize,
        branch_idx: usize,
    ) -> (result: StreamingFinishLevelResult)
        requires
            old(self).wf(),
            input_idx < old(self).compactors.len(),
            branch_idx < old(self).wip_branches.len(),
            old(self).compactors@[input_idx as int].merge is Some,
            old(self).compactors@[input_idx as int].merge_done,
            old(self).wip_branches@[branch_idx as int]
                .has_streaming_builder(),
            old(self).wip_branches@[branch_idx as int]
                .streaming_builder().phase is Finishing,
            old(self).wip_branches@[branch_idx as int]
                .streaming_builder().pending is None,
            old(self).wip_branches@[branch_idx as int]
                .streaming_builder().deferred is None,
            old(self).wip_branches@[branch_idx as int]
                .streaming_builder().source_entries@
                == compact_stream_entries(
                    old(self).compactors@[input_idx as int]
                        .merge->0.output@,
                ),
        ensures
            self.wf(),
            self@ == old(self)@,
            self.root == old(self).root,
            self.ownership == old(self).ownership,
            self.branch_likes == old(self).branch_likes,
            self.memtable == old(self).memtable,
            self.recovery == old(self).recovery,
            self.control == old(self).control,
            self.compactors@ == old(self).compactors@,
            self.wip_branches@.len() == old(self).wip_branches@.len(),
            self.wip_branches@[branch_idx as int].mini_allocator
                == old(self).wip_branches@[branch_idx as int]
                    .mini_allocator,
            forall |cache: Cache::State|
                self.wip_branches@[branch_idx as int].cache_inv(cache)
                    == old(self).wip_branches@[branch_idx as int]
                        .cache_inv(cache),
            self.wip_branches@[branch_idx as int]
                .has_streaming_builder(),
            self.wip_branches@[branch_idx as int]
                .streaming_builder().source_entries@
                == compact_stream_entries(
                    self.compactors@[input_idx as int].merge->0.output@,
                ),
            match result {
                StreamingFinishLevelResult::Empty => {
                    self.wip_branches@[branch_idx as int]
                        .streaming_builder().phase is Empty
                },
                StreamingFinishLevelResult::Advanced
                | StreamingFinishLevelResult::PagesReady => {
                    self.wip_branches@[branch_idx as int]
                        .streaming_builder().phase is Finishing
                },
                StreamingFinishLevelResult::RootReady => {
                    self.wip_branches@[branch_idx as int]
                        .streaming_builder().phase is ReadyIndexRoot
                },
            },
    {
        let ghost old_branches = self.wip_branches@;
        let mut branch = self.wip_branches.remove(branch_idx);
        let result = branch.finish_streaming_level();
        let ghost post_phase = branch.streaming_builder().phase;
        let ghost finish_wf = match result {
            StreamingFinishLevelResult::Empty => post_phase is Empty,
            StreamingFinishLevelResult::Advanced
            | StreamingFinishLevelResult::PagesReady => {
                post_phase is Finishing
            },
            StreamingFinishLevelResult::RootReady => {
                post_phase is ReadyIndexRoot
            },
        };
        let ghost post_branch = branch;
        self.wip_branches.insert(branch_idx, branch);
        proof {
            assert(finish_wf);
            assert(self.wip_branches@[branch_idx as int] == post_branch);
            assert(self.wip_branches@[branch_idx as int]
                .streaming_builder().phase == post_phase);
            assert(self.wip_branches@ == old_branches.update(
                branch_idx as int,
                self.wip_branches@[branch_idx as int],
            ));
            assert(bulk_branch_views(self.wip_branches@)
                == bulk_branch_views(old_branches)) by {
                assert forall |i: int| 0 <= i < self.wip_branches@.len()
                    implies #[trigger] self.wip_branches@[i]@
                        == old_branches[i]@ by {
                    if i != branch_idx as int {
                        assert(self.wip_branches@[i] == old_branches[i]);
                    }
                }
            }
            assert(bulk_builders_wf(
                self.wip_branches@,
                &self.memtable,
            )) by {
                assert forall |i: int| 0 <= i < self.wip_branches@.len()
                    implies (#[trigger] self.wip_branches@[i])
                        .bulk_builder_wf(&self.memtable) by {
                    if i != branch_idx as int {
                        assert(self.wip_branches@[i] == old_branches[i]);
                    }
                }
            }
            assert(self.wf());
            assert(self@ == old(self)@);
        }
        match result {
            StreamingFinishLevelResult::Empty => {
                proof {
                    assert(self.wip_branches@[branch_idx as int]
                        .streaming_builder().phase is Empty);
                }
                StreamingFinishLevelResult::Empty
            },
            StreamingFinishLevelResult::Advanced => {
                proof {
                    assert(self.wip_branches@[branch_idx as int]
                        .streaming_builder().phase is Finishing);
                }
                StreamingFinishLevelResult::Advanced
            },
            StreamingFinishLevelResult::PagesReady => {
                proof {
                    assert(self.wip_branches@[branch_idx as int]
                        .streaming_builder().phase is Finishing);
                }
                StreamingFinishLevelResult::PagesReady
            },
            StreamingFinishLevelResult::RootReady => {
                proof {
                    assert(self.wip_branches@[branch_idx as int]
                        .streaming_builder().phase is ReadyIndexRoot);
                }
                StreamingFinishLevelResult::RootReady
            },
        }
    }

    pub fn compact_abort(
        &mut self,
        input_idx: usize,
    ) -> (result: BranchBetreeCompactAbortResult)
        requires
            old(self).wf(),
            old(self).control.metadata_loaded,
            read_ref_aus(compactor_views(old(self).compactors@))
                <= old(self).branch_likes@.dom(),
        ensures
            self.wf(),
            input_idx < old(self).compactors@.len()
                ==> result is Aborted,
            match result {
                BranchBetreeCompactAbortResult::Aborted { deallocs } => {
                    &&& deallocs@.is_empty()
                    &&& self.root == old(self).root
                    &&& self.ownership == old(self).ownership
                    &&& self.branch_likes == old(self).branch_likes
                    &&& self.memtable == old(self).memtable
                    &&& self.control == old(self).control
                    &&& self.wip_branches@ == old(self).wip_branches@
                    &&& self.compactors@
                        == old(self).compactors@.remove(input_idx as int)
                    &&& AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: deallocs@,
                            access: PageAccess::empty(),
                        },
                    )
                },
                BranchBetreeCompactAbortResult::Noop => {
                    self@ == old(self)@
                },
            },
    {
        if input_idx >= self.compactors.len() {
            return BranchBetreeCompactAbortResult::Noop;
        }
        let ghost pre_state = self@;
        let ghost pre_betree = self.betree_i();
        let ghost pre_compactors = compactor_views(self.compactors@);
        self.compactors.remove(input_idx);
        let ghost deallocs = Set::<AU>::empty();
        proof {
            assert(compactor_views(self.compactors@)
                == pre_compactors.remove(input_idx as int)) by {
                assert_seqs_equal!(
                    compactor_views(self.compactors@),
                    pre_compactors.remove(input_idx as int),
                    i => {
                        if i < input_idx as int {
                            assert(self.compactors@[i]
                                == old(self).compactors@[i]);
                        } else {
                            assert(self.compactors@[i]
                                == old(self).compactors@[i + 1]);
                        }
                    }
                );
            }
            assert(compactor_receipt_views(self.compactors@)
                == pre_betree.compactor_receipts.remove(
                    input_idx as int,
                )) by {
                assert_seqs_equal!(
                    compactor_receipt_views(self.compactors@),
                    pre_betree.compactor_receipts.remove(
                        input_idx as int,
                    ),
                    i => {
                        if i < input_idx as int {
                            assert(self.compactors@[i]
                                == old(self).compactors@[i]);
                        } else {
                            assert(self.compactors@[i]
                                == old(self).compactors@[i + 1]);
                        }
                    }
                );
            }
            CompactorInput::input_roots_remove_subset(
                pre_compactors,
                input_idx as int,
            );
            crate::disk::GenericDisk_v::to_aus_preserves_lte(
                CompactorInput::input_roots(
                    compactor_views(self.compactors@),
                ),
                CompactorInput::input_roots(pre_compactors),
            );
            assert(read_ref_aus(compactor_views(self.compactors@))
                <= read_ref_aus(pre_compactors));
            let ghost released = read_ref_aus(pre_compactors)
                - read_ref_aus(compactor_views(self.compactors@));
            assert(released <= pre_betree.branch_aus.dom());
            let ghost branch_deallocs = released
                - pre_betree.branch_aus.dom();
            assert_sets_equal!(
                branch_deallocs,
                Set::<AU>::empty(),
                au => {}
            );
            assert_maps_equal!(
                pre_betree.branch_summary.remove_keys(branch_deallocs),
                pre_betree.branch_summary,
                root => {}
            );
            let ghost deallocated_summary =
                pre_betree.branch_summary.restrict(branch_deallocs);
            assert_maps_equal!(
                deallocated_summary,
                Map::<AU, Set<AU>>::empty(),
                au => {}
            );
            assert_sets_equal!(
                summary_aus(deallocated_summary),
                Set::<AU>::empty(),
                au => {
                    if summary_aus(deallocated_summary).contains(au) {
                        assert(deallocated_summary.values().is_empty());


                    }
                }
            );
            PageAccess::empty_cached_access_is_empty();
            assert(CachedBranchBetree::State::compact_abort(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs,
                    access: PageAccess::empty().cached_access(),
                },
                input_idx as int,
            )) by {

            }
            assert(CachedBranchBetree::State::next_by(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs,
                    access: PageAccess::empty().cached_access(),
                },
                CachedBranchBetree::Step::compact_abort(
                    input_idx as int,
                ),
            )) by {
                reveal(CachedBranchBetree::State::next_by);
            }
            assert(CachedBranchBetree::State::next(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs,
                    access: PageAccess::empty().cached_access(),
                },
            )) by {
                reveal(CachedBranchBetree::State::next);
            }
            assert(self.wf());
            assert(AtomicBranchBetreeState::State::compact_abort(
                pre_state,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs,
                    access: PageAccess::empty(),
                },
                self.betree_i(),
                input_idx as int,
            )) by {

            }
            assert(AtomicBranchBetreeState::State::next_by(
                pre_state,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs,
                    access: PageAccess::empty(),
                },
                AtomicBranchBetreeState::Step::compact_abort(
                    self.betree_i(),
                    input_idx as int,
                ),
            )) by {
                reveal(AtomicBranchBetreeState::State::next_by);
            }
            assert(AtomicBranchBetreeState::State::next(
                pre_state,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs,
                    access: PageAccess::empty(),
                },
            )) by {
                reveal(AtomicBranchBetreeState::State::next);
            }
        }
        BranchBetreeCompactAbortResult::Aborted {
            deallocs: Ghost(deallocs),
        }
    }

    pub fn compact_complete_with_cache(
        &mut self,
        cache: &mut FracCacheImpl,
        input_idx: usize,
        branch_idx: usize,
        key: Key,
        target_depth: usize,
        fuel: usize,
        disk_page_count: crate::spec::ImplDisk_t::IPage,
        expected_target_addr: IAddress,
        start: usize,
        end: usize,
        new_node_addr: IAddress,
        path_addrs: &Vec<IAddress>,
    ) -> (result: BranchBetreeCompactCompleteResult)
        requires
            old(self).wf(),
            old(self).control.metadata_loaded,
            old(self).root is Some,
            old(self).compactors@.len() == 1,
            input_idx == 0,
            old(self).compactors@[input_idx as int].merge is Some,
            old(self).compactors@[input_idx as int].merge_done,
            branch_idx < old(self).wip_branches.len(),
            old(self).wip_branches@[branch_idx as int].sealed,
            old(self).wip_branches@[branch_idx as int].root is Some,
            old(self).wip_branches@[branch_idx as int]
                .sealed_branch@ is Some,
            old(self).wip_branches@[branch_idx as int].sealed_source@
                == Some(MemtableBucket::entries_map(
                    compact_stream_entries(
                        old(self).compactors@[input_idx as int]
                            .merge->0.output@,
                    ),
                )),
            old(self).wip_branches@[branch_idx as int].cache_inv(old(cache)@),
            old(self).ownership.betree.all_aus().disjoint(
                old(self).wip_branches@[branch_idx as int]
                    .mini_allocator.i().all_aus(),
            ),
            old(self).ownership.branches.all_summary_aus().disjoint(
                old(self).wip_branches@[branch_idx as int]
                    .mini_allocator.i().all_aus(),
            ),
            target_depth < fuel,
            disk_page_count as nat
                == crate::disk::GenericDisk_v::page_count(),
            cached_betree_path_prefix_valid(
                old(cache)@,
                old(self).root.unwrap()@,
                key,
                fuel as nat,
                target_depth as nat,
                old(self).ownership.betree.active_aus(),
            ),
            new_node_addr@.wf(),
            betree_node_addr(new_node_addr@),
            forall |i: int| 0 <= i < path_addrs@.len()
                ==> (#[trigger] path_addrs@[i])@.wf(),
            forall |i: int| 0 <= i < path_addrs@.len()
                ==> betree_node_addr((#[trigger] path_addrs@[i])@),
            seq_addrs_disjoint_aus(iaddr_views(path_addrs@)),
            !crate::allocation_layer::AllocationBranchBetree_v::
                seq_addrs_to_aus(iaddr_views(path_addrs@))
                .contains(new_node_addr@.au),
            old(self).betree_i().is_fresh(to_aus(
                iaddr_views(path_addrs@).to_set(),
            ).insert(new_node_addr@.au)),
            old(self).wip_branches@[branch_idx as int]
                .mini_allocator.i().all_aus().disjoint(
                    to_aus(iaddr_views(path_addrs@).to_set())
                        .insert(new_node_addr@.au),
                ),
            old(cache).wf(),
            old(cache)@.inv(),
        ensures
            self.wf(),
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            match result {
                BranchBetreeCompactCompleteResult::Completed {
                    new_root,
                    betree_reclaimed,
                    branch_reclaimed,
                    prepared_cache,
                    access,
                    allocs,
                    deallocs,
                } => {
                    &&& new_root@ == self.betree_i().root.unwrap()
                    &&& self.compactors@
                        == old(self).compactors@.remove(input_idx as int)
                    &&& self.wip_branches@
                        == old(self).wip_branches@.remove(branch_idx as int)
                    &&& self.memtable == old(self).memtable
                    &&& self.control == old(self).control
                    &&& self.ownership.betree.all_aus()
                        <= old(self).ownership.betree.all_aus() + allocs@
                    &&& self.ownership.branches.all_summary_aus()
                        <= old(self).ownership.branches.all_summary_aus()
                            + old(self).wip_branches@[branch_idx as int]
                                .mini_allocator.i().all_aus()
                    &&& unique_iau_seq(betree_reclaimed@)
                    &&& unique_iau_seq(branch_reclaimed@)
                    &&& iau_seq_set(betree_reclaimed@)
                        <= deallocs@
                    &&& iau_seq_set(branch_reclaimed@)
                        <= deallocs@
                    &&& allocs@ =~= to_aus(
                        iaddr_views(path_addrs@).to_set(),
                    ).insert(new_node_addr@.au)
                    &&& deallocs@ <= old(self).betree_i().durable_aus()
                    &&& iau_seq_set(betree_reclaimed@).disjoint(
                        iau_seq_set(branch_reclaimed@),
                    )
                    &&& iau_seq_set(betree_reclaimed@)
                            + iau_seq_set(branch_reclaimed@)
                        == old(self).control_i().reclaimable(deallocs@)
                    &&& access@.wf()
                    &&& access@.branch_writes.is_empty()
                    &&& Cache::State::next(
                        old(cache)@,
                        prepared_cache@,
                        Cache::Label::Internal,
                    )
                    &&& Cache::State::next(
                        prepared_cache@,
                        cache@,
                        Cache::Label::Access {
                            reads: access@.reads(),
                            writes: access@.writes(),
                        },
                    )
                    &&& AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: allocs@,
                            deallocs: deallocs@,
                            access: access@,
                        },
                    )
                },
                BranchBetreeCompactCompleteResult::NeedCacheLoad {
                    addr,
                    handle,
                } => {
                    &&& self@ == old(self)@
                    &&& self.same_exec_state(old(self))
                    &&& self.wip_branches@[branch_idx as int]
                        .cache_inv(cache@)
                    &&& (old(self).ownership.betree.active_aus()
                        + to_aus(iaddr_views(path_addrs@).to_set())
                            .insert(new_node_addr@.au))
                        .contains(addr@.au)
                    &&& cache.entry_fetched(&addr)
                    &&& cache.valid_load_handle(&addr, handle)
                    &&& Cache::State::next(
                        old(cache)@,
                        cache@,
                        crate::implementation::FracCacheImpl_v::cache_load_label(
                            &addr,
                        ),
                    )
                },
                BranchBetreeCompactCompleteResult::Stale
                | BranchBetreeCompactCompleteResult::CacheFull
                | BranchBetreeCompactCompleteResult::Blocked
                | BranchBetreeCompactCompleteResult::InvalidPage => {
                    &&& self@ == old(self)@
                    &&& self.same_exec_state(old(self))
                    &&& cache@ == old(cache)@
                },
            },
    {
        let ghost pre_state = self@;
        let ghost pre_impl = *self;
        let ghost pre_betree = self.betree_i();
        let ghost pre_branch_likes = self.branch_likes@;
        let ghost pre_ownership = self.ownership;
        let ghost pre_wip_seq = self.wip_branches@;
        let ghost pre_compactors = self.compactors@;
        let ghost completion_compactor = self.compactors@[input_idx as int];
        let ghost completion_output_branch = self.wip_branches@[
            branch_idx as int
        ].sealed_branch@.unwrap();
        let ghost cache0 = *cache;
        let ghost pre_active_betree = self.ownership.betree.active_aus();
        let ghost pre_all_branches = self.ownership.branches.all_summary_aus();
        let output_root = self.wip_branches[branch_idx].root.unwrap();
        let ghost output_summary = self.wip_branches@[branch_idx as int]
            .mini_allocator.i().all_aus();
        proof {
            self.ownership.betree.view_domain_matches_active();
            assert(pre_active_betree =~= pre_betree.betree_aus.dom());
            self.ownership.branches.active_summary_projection();
            assert(pre_betree.branch_summary.dom().finite());
            assert(pre_betree.branch_summary.values().finite());
            assert(map_with_disjoint_values(pre_betree.branch_summary)) by {
                assert forall |left: AU, right: AU|
                    #[trigger] pre_betree.branch_summary.contains_key(left)
                    && #[trigger] pre_betree.branch_summary.contains_key(right)
                    && left != right
                    implies pre_betree.branch_summary[left].disjoint(
                        pre_betree.branch_summary[right],
                    ) by {
                    assert(self.ownership.branches.active@
                        .contains_key(left));
                    assert(self.ownership.branches.active@
                        .contains_key(right));
                    assert(self.ownership.branches.records()
                        .contains_key(left));
                    assert(self.ownership.branches.records()
                        .contains_key(right));
                    assert(self.ownership.branches.records()[left].summary
                        == pre_betree.branch_summary[left]);
                    assert(self.ownership.branches.records()[right].summary
                        == pre_betree.branch_summary[right]);
                    assert(self.ownership.branches.summaries_pairwise_disjoint());
                }
            }
            expose_compactor_model_alignment(
                self.compactors@,
                pre_betree.branch_summary,
            );
            self.compactors@[input_idx as int].completed_receipt_valid(
                pre_betree.branch_summary,
            );
            let output_branch = self.wip_branches@[branch_idx as int]
                .sealed_branch@.unwrap();
            assert(output_branch.i().i().map
                == MemtableBucket::entries_map(compact_stream_entries(
                    self.compactors@[input_idx as int].merge->0.output@,
                )));
            self.compactors@[input_idx as int].sealed_output_valid(
                pre_betree.branch_summary,
                output_branch,
            );
            assert(valid_loaded_sealed_branches(
                pre_betree.compactors[input_idx as int]
                    .input_buffers.addrs.to_set(),
                pre_betree.branch_summary,
                pre_betree.compactor_receipts[input_idx as int],
            ));
        }

        let root = self.root.unwrap();
        let ghost betree_aus = self.ownership.betree.active_aus();
        let loaded = load_betree_path(
            cache,
            root,
            key,
            target_depth,
            fuel,
            disk_page_count,
            Ghost(betree_aus),
        );
        let (path, path_reads) = match loaded {
            BetreePathLoadResult::Loaded { workspace: path, reads } => (path, reads),
            BetreePathLoadResult::NeedCacheLoad { addr, handle } => {
                proof {
                    assert forall |read_addr: Address, data: RawPage|
                        cache0@.valid_read(read_addr, data)
                        implies cache@.valid_read(read_addr, data) by {
                        Cache::State::load_request_preserves_valid_read(
                            cache0@,
                            cache@,
                            addr@,
                            read_addr,
                            data,
                        );
                    }
                    pre_impl.wip_branches@[branch_idx as int]
                        .cache_inv_preserved_by_valid_reads(
                            cache0@,
                            cache@,
                        );
                }
                return BranchBetreeCompactCompleteResult::NeedCacheLoad {
                    addr,
                    handle,
                };
            },
            BetreePathLoadResult::CacheFull => {
                return BranchBetreeCompactCompleteResult::CacheFull;
            },
            BetreePathLoadResult::Blocked => {
                return BranchBetreeCompactCompleteResult::Blocked;
            },
            BetreePathLoadResult::InvalidPage => {
                return BranchBetreeCompactCompleteResult::InvalidPage;
            },
        };
        let target_idx = path.nodes.len() - 1;
        if path.addrs[target_idx].au != expected_target_addr.au
            || path.addrs[target_idx].page != expected_target_addr.page
        {
            return BranchBetreeCompactCompleteResult::Stale;
        }
        let target = &path.nodes[target_idx];
        if start >= end || end > target.buffers.len() {
            return BranchBetreeCompactCompleteResult::Stale;
        }
        if !self.compactors[input_idx].matches_completion_target(
            target,
            start,
            end,
        ) {
            return BranchBetreeCompactCompleteResult::Stale;
        }
        proof {
            let output_branch = self.wip_branches@[branch_idx as int]
                .sealed_branch@.unwrap();
            assert(self.compactors@[input_idx as int]
                .filter.target@.buffers.slice(
                    start as int,
                    end as int,
                ) == target@.buffers.slice(
                    start as int,
                    end as int,
                ));
            crate::implementation::CompactorCompletionSemantics_v::
                sealed_output_valid_for_target(
                    &self.compactors@[input_idx as int],
                    pre_betree.branch_summary,
                    output_branch,
                    target@,
                    start as nat,
                    end as nat,
                );
        }
        if path_addrs.len() != path.addrs.len() - 1 {
            return BranchBetreeCompactCompleteResult::Blocked;
        }

        /* Legacy singleton completion reread both branch roots and compared
         * leaf contents at runtime. The streaming completion certificate now
         * validates arbitrary sealed input/output branches without rereads.
        let ghost cache_before_input = *cache;
        let mut input_handle = match cache.fetch(&input_root, false) {
            FetchErrorCode::Success { slot_handle } => slot_handle,
            FetchErrorCode::LoadInitiate { slot_handle } => {
                return BranchBetreeCompactCompleteResult::NeedCacheLoad {
                    addr: input_root,
                    handle: slot_handle,
                };
            },
            FetchErrorCode::CacheFull => {
                return BranchBetreeCompactCompleteResult::CacheFull;
            },
            FetchErrorCode::Awaiting | FetchErrorCode::NotPresent => {
                return BranchBetreeCompactCompleteResult::Blocked;
            },
        };
        let ghost input_raw = input_handle.rec@;
        let input_slot = input_handle.idx;
        let fmt = BranchNodePageFmt::new();
        let input_slice = Slice::all(&input_handle.rec);
        let parsed_input = fmt.try_parse(&input_slice, &input_handle.rec);
        proof {
            if parsed_input is Some {
                assert(fmt == BranchNodePageFmt::spec_new());
                assert(input_slice@.i(input_handle.rec@) == input_raw);
                assert(parsed_input.unwrap().parsedv() == fmt.parse(input_raw));
                assert(raw_page_to_branch_node(input_raw)
                    == parsed_input.unwrap()@);
            }
        }
        let input_node = match parsed_input {
            Some(node) => node,
            None => {
                cache.handle_release(&input_root, input_handle);
                return BranchBetreeCompactCompleteResult::InvalidPage;
            },
        };
        cache.handle_release(&input_root, input_handle);
        proof {
            assert(cache@ == cache_before_input@) by {
                assert(cache@.entries == cache_before_input@.entries);
                assert(cache@.lookup_map == cache_before_input@.lookup_map);
                assert(cache@.status_map == cache_before_input@.status_map);
            }
        }
        let output_reads = match self.wip_branches[branch_idx]
            .read_sealed_leaf(cache)
        {
            BulkBranchReadResult::Read { reads } => reads,
            BulkBranchReadResult::CacheFull => {
                return BranchBetreeCompactCompleteResult::CacheFull;
            },
            BulkBranchReadResult::Blocked => {
                return BranchBetreeCompactCompleteResult::Blocked;
            },
            BulkBranchReadResult::InvalidPage => {
                return BranchBetreeCompactCompleteResult::InvalidPage;
            },
        };
        let output_node = self.wip_branches[branch_idx]
            .root_node.as_ref().unwrap();
        if !input_node.leaf_contents_equal(output_node) {
            return BranchBetreeCompactCompleteResult::Blocked;
        }
        let ghost input_reads = map![input_root@ => input_raw];
        let ghost output_raw = output_reads@[output_root@];
        let ghost branch_raw_reads = input_reads.union_prefer_right(output_reads@);
        proof {
            assert(cache@ == cache0@);
            assert(cache0@.valid_read(input_root@, input_raw));
            assert(output_reads@ == map![output_root@ => output_raw]) by {
                assert_maps_equal!(
                    output_reads@,
                    map![output_root@ => output_raw],
                    addr => {}
                );
            }
            Cache::State::access_read_valid(
                cache0@,
                cache0@,
                output_reads@,
                Map::empty(),
                output_root@,
            );
            assert(cache0@.valid_read(output_root@, output_raw));
            assert(to_branch_nodes(output_reads@)[output_root@]
                == output_node@);
            assert(raw_page_to_branch_node(output_raw) == output_node@);
            assert(raw_page_to_branch_node(input_raw) == input_node@);
            assert(input_node@ == output_node@);
            assert(raw_page_to_branch_node(input_raw) is Leaf);
            assert(path.nodes@[target_idx as int]@ == path.receipt@.target().node);
            assert(end == start + 1);
            assert(target.buffers@.subrange(start as int, end as int)
                == seq![input_root]) by {
                assert(target.buffers@[start as int] == input_root);
                assert_seqs_equal!(
                    target.buffers@.subrange(start as int, end as int),
                    seq![input_root],
                    i => {}
                );
            }
            assert(path.receipt@.target().node.buffers.slice(
                start as int,
                end as int,
            ).addrs == seq![input_root@]);
            assert forall |addr: Address|
                #[trigger] path_reads@.contains_key(addr)
                implies cache0@.valid_read(addr, path_reads@[addr]) by {
                Cache::State::access_read_valid(
                    cache0@,
                    cache0@,
                    path_reads@,
                    Map::empty(),
                    addr,
                );
            }
            assert(cached_single_leaf_compaction_valid(
                cache0@,
                root@,
                key,
                target_depth as nat,
                start as nat,
                end as nat,
                input_root@,
                output_root@,
                output_summary,
                pre_betree.branch_summary,
                pre_betree.compactors[input_idx as int],
            ));
            assert(cached_single_leaf_compaction_match(
                cache0@,
                root@,
                key,
                target_depth as nat,
                start as nat,
                end as nat,
                input_root@,
                output_root@,
                output_summary,
                pre_betree.branch_summary,
                pre_betree.compactors[input_idx as int],
                path.receipt@,
                path_reads@,
                input_raw,
                output_raw,
            ));
            cached_single_leaf_compaction_valid_apply(
                cache0@,
                root@,
                key,
                target_depth as nat,
                start as nat,
                end as nat,
                input_root@,
                output_root@,
                output_summary,
                pre_betree.branch_summary,
                pre_betree.compactors[input_idx as int],
                path.receipt@,
                path_reads@,
                input_raw,
                output_raw,
            );
            disjoint_au_views_are_unique(path_addrs@);
            crate::disk::GenericDisk_v::to_aus_domain(
                iaddr_views(path_addrs@).to_set(),
            );
            assert(!iaddr_views(path_addrs@).to_set()
                .contains(new_node_addr@)) by {
                if iaddr_views(path_addrs@).to_set()
                    .contains(new_node_addr@)
                {
                    assert(crate::allocation_layer::AllocationBranchBetree_v::
                        seq_addrs_to_aus(iaddr_views(path_addrs@))
                        .contains(new_node_addr@.au));
                }
            }
        }
        */
        proof {
            disjoint_au_views_are_unique(path_addrs@);
            crate::disk::GenericDisk_v::to_aus_domain(
                iaddr_views(path_addrs@).to_set(),
            );
            assert(!iaddr_views(path_addrs@).to_set()
                .contains(new_node_addr@)) by {
                if iaddr_views(path_addrs@).to_set()
                    .contains(new_node_addr@)
                {
                    assert(crate::allocation_layer::AllocationBranchBetree_v::
                        seq_addrs_to_aus(iaddr_views(path_addrs@))
                        .contains(new_node_addr@.au));
                }
            }
        }

        let built = match build_compact_write_batch(
            &path,
            start,
            end,
            output_root,
            new_node_addr,
            path_addrs,
        ) {
            Some(built) => built,
            None => return BranchBetreeCompactCompleteResult::InvalidPage,
        };
        let destinations = compact_destination_addrs(
            new_node_addr,
            path_addrs,
        );
        let ghost cache_before_prepare = *cache;
        match prepare_cache_write_addrs(cache, &destinations) {
            CacheWritePrepareResult::Ready => {
                proof {
                    FracCacheImpl::valid_load_handles_preserved_transitive(
                        cache0,
                        cache_before_prepare,
                        *cache,
                    );
                }
            },
            CacheWritePrepareResult::NeedCacheLoad { addr, handle } => {
                proof {
                    FracCacheImpl::valid_load_handles_preserved_transitive(
                        cache0,
                        cache_before_prepare,
                        *cache,
                    );
                    let i = choose |i: int|
                        0 <= i < destinations@.len()
                            && addr == destinations@[i];
                    assert(destinations@ == seq![new_node_addr] + path_addrs@);
                    if i == 0 {
                        assert(addr@.au == new_node_addr@.au);
                    } else {
                        assert(addr == path_addrs@[i - 1]);
                        assert(iaddr_views(path_addrs@)[i - 1] == addr@);
                        assert(iaddr_views(path_addrs@).to_set()
                            .contains(addr@));
                        assert(to_aus(iaddr_views(path_addrs@).to_set())
                            .contains(addr@.au));
                    }
                    assert forall |read_addr: Address, data: RawPage|
                        cache0@.valid_read(read_addr, data)
                        implies cache@.valid_read(read_addr, data) by {
                        assert(cache_before_prepare@ == cache0@);
                        Cache::State::load_request_preserves_valid_read(
                            cache_before_prepare@,
                            cache@,
                            addr@,
                            read_addr,
                            data,
                        );
                    }
                    pre_impl.wip_branches@[branch_idx as int]
                        .cache_inv_preserved_by_valid_reads(
                            cache0@,
                            cache@,
                        );
                }
                return BranchBetreeCompactCompleteResult::NeedCacheLoad {
                    addr,
                    handle,
                };
            },
            CacheWritePrepareResult::CacheFull => {
                return BranchBetreeCompactCompleteResult::CacheFull;
            },
            CacheWritePrepareResult::Blocked => {
                return BranchBetreeCompactCompleteResult::Blocked;
            },
        }

        let old_aus = iaddress_aus(&path.addrs);
        let new_aus = iaddress_aus(&destinations);
        if !crate::implementation::BranchBetreeOwnershipImpl_v::iau_vec_unique(
            &old_aus,
        ) || !crate::implementation::BranchBetreeOwnershipImpl_v::iau_vec_unique(
            &new_aus,
        ) {
            return BranchBetreeCompactCompleteResult::Blocked;
        }
        let mut old_index = 0usize;
        while old_index < old_aus.len()
            invariant
                self.wf(),
                self@ == pre_state,
                old_index <= old_aus.len(),
                forall |i: int| 0 <= i < old_index
                    ==> self.ownership.betree.active_aus().contains(
                        (#[trigger] old_aus@[i]) as nat,
                    ),
            decreases old_aus.len() - old_index,
        {
            if !self.ownership.betree.contains_active(old_aus[old_index]) {
                return BranchBetreeCompactCompleteResult::Blocked;
            }
            old_index += 1;
        }
        let mut new_index = 0usize;
        while new_index < new_aus.len()
            invariant
                self.wf(),
                self@ == pre_state,
                new_index <= new_aus.len(),
                forall |i: int| 0 <= i < new_index ==> {
                    &&& !self.ownership.betree.all_aus().contains(
                        (#[trigger] new_aus@[i]) as nat,
                    )
                    &&& !self.ownership.branches.all_summary_aus().contains(
                        new_aus@[i] as nat,
                    )
                },
            decreases new_aus.len() - new_index,
        {
            let au = new_aus[new_index];
            if self.ownership.betree.contains_owned_au(au)
                || self.ownership.branches.contains_owned_au(au)
            {
                return BranchBetreeCompactCompleteResult::Blocked;
            }
            new_index += 1;
        }
        proof {
            assert(iau_seq_set(old_aus@)
                <= self.ownership.betree.active_aus());
            assert(self.ownership.betree.all_aus().disjoint(
                iau_seq_set(new_aus@),
            ));
            assert(self.ownership.branches.all_summary_aus().disjoint(
                iau_seq_set(new_aus@),
            ));
            assert(iau_seq_set(new_aus@)
                <= to_aus(iaddr_views(path_addrs@).to_set())
                    .insert(new_node_addr@.au)) by {
                assert forall |au: AU|
                    #[trigger] iau_seq_set(new_aus@).contains(au)
                    implies (to_aus(iaddr_views(path_addrs@).to_set())
                        .insert(new_node_addr@.au)).contains(au) by {
                    let i = choose |i: int| 0 <= i < new_aus@.len()
                        && new_aus@[i] as nat == au;
                    assert(new_aus@[i] as nat == destinations@[i]@.au);
                    if i == 0 {
                        assert(destinations@[i] == new_node_addr);
                    } else {
                        assert(destinations@[i] == path_addrs@[i - 1]);
                        assert(iaddr_views(path_addrs@)[i - 1]
                            == destinations@[i]@);
                        assert(iaddr_views(path_addrs@).to_set()
                            .contains(destinations@[i]@));
                        crate::disk::GenericDisk_v::to_aus_domain(
                            iaddr_views(path_addrs@).to_set(),
                        );
                    }
                }
            }
            assert(output_summary.disjoint(iau_seq_set(new_aus@)));
        }
        /* Legacy singleton ownership update. Multi-branch completion applies
         * the full selected root multiset below.
        if self.branch_likes.count(input_root.au) != 1
            || self.branch_likes.contains(output_root.au)
        {
            return BranchBetreeCompactCompleteResult::Blocked;
        }
        proof {
            self.ownership.branches.active_summary_map_dom();
            self.ownership.branches.active_summary_projection();
            assert(pre_betree.branch_aus.dom().contains(input_root@.au));
            assert(pre_betree.branch_summary.contains_key(input_root@.au));
            self.ownership.branches.root_record_is_owned(input_root@.au);
            assert(summary_aus(pre_betree.branch_summary)
                .contains(input_root@.au)) by {
                assert(summary_aus(pre_betree.branch_summary)
                    =~= self.ownership.branches.active_summary_aus());
                assert(self.ownership.branches.active_summary_aus()
                    .contains(input_root@.au));
            }
            assert(active_components_disjoint) by {
                assert(self.ownership.betree.all_aus().disjoint(
                    self.ownership.branches.all_summary_aus(),
                ));
                assert(pre_betree.betree_aus.dom()
                    <= self.ownership.betree.all_aus()) by {
                    self.ownership.betree.view_domain_matches_active();
                    self.ownership.betree.ownership_sets_bounded();
                }
                assert(summary_aus(pre_betree.branch_summary)
                    <= self.ownership.branches.all_summary_aus()) by {
                    self.ownership.branches.active_summary_projection();
                    self.ownership.branches.ownership_sets_bounded();
                }
            }
        }

        let summary = self.wip_branches[branch_idx]
            .mini_allocator.all_aus_vec();
        proof {
            assert(unique_iau_seq(summary@));
            assert(iau_seq_set(summary@) =~= output_summary);
            assert(iau_seq_set(summary@).contains(output_root@.au));
            assert(self.ownership.branches.all_summary_aus().disjoint(
                iau_seq_set(summary@),
            ));
            assert(self.ownership.betree.all_aus().disjoint(
                iau_seq_set(summary@),
            ));
        }
        let added = self.ownership.add_ephemeral_branch(
            output_root.au,
            summary,
        );
        match added {
            BranchOwnershipUpdateResult::Applied { reclaimed: _ } => {},
            BranchOwnershipUpdateResult::Noop => {
                proof { assert(false); }
                return BranchBetreeCompactCompleteResult::Blocked;
            },
        }
        let removes = vec![input_root.au];
        let adds = vec![output_root.au];
        proof {
            self.branch_likes.view_counts_bounded();
            crate::implementation::AuLikesImpl_v::seq_to_au_likes_push(
                Seq::<IAU>::empty(),
                input_root.au,
            );
            crate::implementation::AuLikesImpl_v::seq_to_au_likes_push(
                Seq::<IAU>::empty(),
                output_root.au,
            );
            assert(removes@ == Seq::<IAU>::empty().push(input_root.au));
            assert(adds@ == Seq::<IAU>::empty().push(output_root.au));
            assert(seq_to_au_likes(removes@)
                == Multiset::singleton(input_root@.au));
            assert(seq_to_au_likes(adds@)
                == Multiset::singleton(output_root@.au));
            assert(au_likes_delta_applicable(
                pre_branch_likes,
                removes@,
                adds@,
            )) by {

                assert(seq_to_au_likes(removes@) <= pre_branch_likes) by {
                    assert forall |au: AU|
                        seq_to_au_likes(removes@).count(au)
                            <= pre_branch_likes.count(au) by {
                    }
                }
                assert forall |au: AU| #[trigger]
                    pre_branch_likes.sub(seq_to_au_likes(removes@))
                        .add(seq_to_au_likes(adds@)).count(au)
                        <= u64::MAX as nat by {
                    if au == output_root@.au {
                        assert(pre_branch_likes.count(au) == 0);
                    } else {
                        assert(seq_to_au_likes(adds@).count(au) == 0);
                    }
                }
            }
        }
        let became_zero = match self.branch_likes.apply_delta(&removes, &adds) {
            AuLikesUpdateResult::Applied { became_zero } => became_zero,
            AuLikesUpdateResult::Noop => {
                proof { assert(false); }
                return BranchBetreeCompactCompleteResult::Blocked;
            },
        };
        proof {
            self.ownership.branches.active_summary_map_dom();
            assert(self.ownership.branches.active_summary_map()
                == pre_betree.branch_summary.insert(
                    output_root@.au,
                    output_summary,
                ));
            assert(self.ownership.branches.active@
                .contains_key(input_root@.au));
        }
        let ghost before_branch_retire = self.ownership.branches;
        let branch_reclaimed = match self.ownership.branches.retire(
            input_root.au,
        ) {
            BranchOwnershipUpdateResult::Applied { reclaimed } => reclaimed,
            BranchOwnershipUpdateResult::Noop => {
                proof { assert(false); }
                return BranchBetreeCompactCompleteResult::Blocked;
            },
        };
        proof {
            assert(before_branch_retire.active_summary_map()
                == pre_betree.branch_summary.insert(
                    output_root@.au,
                    output_summary,
                ));
            assert(before_branch_retire.active_summary_map()
                .contains_key(input_root@.au));
            assert(before_branch_retire.active@
                .contains_key(input_root@.au));
            assert(before_branch_retire.active_summary_map()[input_root@.au]
                == before_branch_retire.active@[input_root@.au].summary);
            assert(before_branch_retire.active@[input_root@.au].summary
                == pre_betree.branch_summary[input_root@.au]);
            assert(iau_seq_set(branch_reclaimed@)
                <= pre_betree.branch_summary[input_root@.au]) by {
                assert forall |au: AU|
                    #[trigger] iau_seq_set(branch_reclaimed@).contains(au)
                    implies pre_betree.branch_summary[input_root@.au]
                        .contains(au) by {
                }
            }
            assert(self.ownership.wf()) by {
                assert(self.ownership.betree.all_aus().disjoint(
                    self.ownership.branches.all_summary_aus(),
                ));
            }
            self.ownership.betree.view_domain_matches_active();
            assert(self.ownership.betree@ == pre_betree.betree_aus);
            assert(self.ownership.betree.active_aus()
                =~= pre_active_betree);
            assert(self.ownership.branches.all_summary_aus()
                <= pre_all_branches + output_summary);
        }
        */

        let input_buffers = self.compactors[input_idx].input_buffers.clone();
        let removes = iaddress_aus(&input_buffers);
        let adds = vec![output_root.au];
        if self.branch_likes.contains(output_root.au) {
            return BranchBetreeCompactCompleteResult::Blocked;
        }
        let became_zero = match self.branch_likes.apply_delta(&removes, &adds) {
            AuLikesUpdateResult::Applied { became_zero } => became_zero,
            AuLikesUpdateResult::Noop => {
                return BranchBetreeCompactCompleteResult::Blocked;
            },
        };

        let summary = self.wip_branches[branch_idx]
            .mini_allocator.all_aus_vec();
        proof {
            assert(unique_iau_seq(summary@));
            assert(iau_seq_set(summary@) =~= output_summary);
            assert(iau_seq_set(summary@).contains(output_root@.au));
            assert(self.ownership.branches.all_summary_aus().disjoint(
                iau_seq_set(summary@),
            ));
            assert(self.ownership.betree.all_aus().disjoint(
                iau_seq_set(summary@),
            ));
        }
        match self.ownership.add_ephemeral_branch(
            output_root.au,
            summary,
        ) {
            BranchOwnershipUpdateResult::Applied { reclaimed: _ } => {},
            BranchOwnershipUpdateResult::Noop => {
                proof { assert(false); }
                return BranchBetreeCompactCompleteResult::Blocked;
            },
        }

        self.compactors.remove(input_idx);
        let ghost before_branch_retire = self.ownership.branches;
        let branch_reclaimed = match self.ownership.branches.retire_many(
            &became_zero,
        ) {
            BranchOwnershipUpdateResult::Applied { reclaimed } => reclaimed,
            BranchOwnershipUpdateResult::Noop => {
                proof { assert(false); }
                return BranchBetreeCompactCompleteResult::Blocked;
            },
        };
        let ghost after_branch_retire = self.ownership.branches;
        proof {
            assert(self.ownership.wf()) by {
                assert(self.ownership.betree.all_aus().disjoint(
                    self.ownership.branches.all_summary_aus(),
                ));
            }
            self.ownership.betree.view_domain_matches_active();
            assert(self.ownership.betree@ == pre_betree.betree_aus);
            assert(self.ownership.betree.active_aus()
                =~= pre_active_betree);
            assert(self.ownership.branches.all_summary_aus()
                <= pre_all_branches + output_summary);
        }
        proof {
            assert(betree_batch_replace_applicable(
                self.ownership,
                old_aus@,
                new_aus@,
            )) by {
                assert(unique_iau_seq(old_aus@));
                assert(unique_iau_seq(new_aus@));
                assert(iau_seq_set(old_aus@)
                    <= self.ownership.betree.active_aus());
                assert(self.ownership.betree.all_aus().disjoint(
                    iau_seq_set(new_aus@),
                ));
                assert(self.ownership.branches.all_summary_aus().disjoint(
                    iau_seq_set(new_aus@),
                )) by {
                    assert(self.ownership.branches.all_summary_aus()
                        <= pre_all_branches + output_summary);
                    assert(output_summary.disjoint(iau_seq_set(new_aus@)));
                }
            }
        }
        let betree_reclaimed = match self.ownership.replace_betree_aus(
            &old_aus,
            &new_aus,
        ) {
            BetreeOwnershipUpdateResult::Applied { reclaimed } => reclaimed,
            BetreeOwnershipUpdateResult::Noop => {
                proof { assert(false); }
                return BranchBetreeCompactCompleteResult::Blocked;
            },
        };
        self.wip_branches.remove(branch_idx);

        let ghost prepared_cache = cache@;
        let ghost entries_view = built.entries@;
        let ghost writes = betree_raw_writes(entries_view);
        let new_root = built.new_root;
        proof {
            assert(cache@ == cache0@);
            assert(destinations@ == seq![new_node_addr] + path_addrs@);
            crate::betree::Utils_v::lemma_to_set_distributes_over_plus(
                seq![new_node_addr],
                path_addrs@,
            );
            crate::implementation::BetreeWriteBatchImpl_v::
                betree_raw_writes_dom(entries_view);
            assert(writes.dom()
                <= set![new_node_addr@]
                    + iaddr_views(path_addrs@).to_set());
            assert forall |i: int| 0 <= i < entries_view.len()
                implies cache.entry_available_for_fetch(
                    &(#[trigger] entries_view[i]).addr,
                ) by {
                assert(writes.dom().contains(entries_view[i].addr@));
                let addr = entries_view[i].addr@;
                assert((set![new_node_addr@]
                    + iaddr_views(path_addrs@).to_set()).contains(addr));
                let j = if addr == new_node_addr@ {
                    0int
                } else {
                    let k = choose |k: int| 0 <= k < path_addrs@.len()
                        && #[trigger] path_addrs@[k]@ == addr;
                    k + 1
                };
                assert(0 <= j < destinations@.len());
                assert(destinations@[j]@ == addr);
                assert(destinations@[j] == entries_view[i].addr) by {
                    assert(destinations@[j].au == entries_view[i].addr.au);
                    assert(destinations@[j].page == entries_view[i].addr.page);
                }
                assert(cache.entry_available_for_fetch(&destinations@[j]));
            }
        }
        let ghost cache_before_write = *cache;
        write_betree_pages(cache, built.entries);
        proof {
            FracCacheImpl::valid_load_handles_preserved_transitive(
                cache0,
                cache_before_write,
                *cache,
            );
        }
        self.root = Some(new_root);

        let ghost betree_reads = path_reads@;
        let ghost access = PageAccess {
            betree_reads,
            branch_reads: Map::empty(),
            betree_writes: writes,
            branch_writes: Map::empty(),
        };
        let ghost allocs = to_aus(iaddr_views(path_addrs@).to_set())
            .insert(new_node_addr@.au);
        let ghost branch_deallocs = iau_seq_set(became_zero@);
        let ghost deallocs = (
            pre_betree.betree_aus.dom() - self.betree_i().betree_aus.dom()
        ) + summary_aus(pre_betree.branch_summary.restrict(branch_deallocs));
        proof {
            assert forall |addr: Address|
                #[trigger] path_reads@.contains_key(addr)
                implies prepared_cache.valid_read(addr, path_reads@[addr]) by {
                Cache::State::access_read_valid(
                    cache0@,
                    cache0@,
                    path_reads@,
                    Map::empty(),
                    addr,
                );
            }
            assert_maps_equal!(
                access.reads(),
                path_reads@,
                addr => {}
            );
            assert forall |addr: Address|
                #[trigger] access.reads().contains_key(addr)
                implies prepared_cache.valid_read(addr, access.reads()[addr]) by {
            }
            Cache::State::access_add_reads(
                prepared_cache,
                cache@,
                access.reads(),
                writes,
            );
            assert(access.wf());
            assert(iaddr_views(path.addrs@) == path.receipt@.path_addrs()) by {
                assert_seqs_equal!(
                    iaddr_views(path.addrs@),
                    path.receipt@.path_addrs(),
                    i => {}
                );
            }
            iaddress_aus_likes(path.addrs@, old_aus@);
            iaddress_aus_likes(destinations@, new_aus@);
            assert_multisets_equal!(
                seq_to_au_likes(old_aus@),
                to_au_likes(
                    crate::implementation::CachedBranchBetree_v::
                        path_discard_likes(path.receipt@),
                ),
                au => {}
            );
            assert(iaddr_views(destinations@)
                == seq![new_node_addr@] + iaddr_views(path_addrs@)) by {
                assert_seqs_equal!(
                    iaddr_views(destinations@),
                    seq![new_node_addr@] + iaddr_views(path_addrs@),
                    i => {}
                );
            }
            let ghost compact_prefix = seq![new_node_addr@];
            let ghost compact_tail = iaddr_views(path_addrs@);
            let ghost empty_compact_prefix = Seq::<Address>::empty();
            empty_compact_prefix.to_multiset_ensures();
            vstd::seq_lib::to_multiset_build(
                empty_compact_prefix,
                new_node_addr@,
            );
            assert(compact_prefix
                == empty_compact_prefix.push(new_node_addr@));
            assert_multisets_equal!(
                compact_prefix.to_multiset(),
                Multiset::singleton(new_node_addr@),
                addr => {}
            );
            vstd::seq_lib::lemma_multiset_commutative(
                compact_prefix,
                compact_tail,
            );
            vstd::seq_lib::to_multiset_build(
                compact_tail,
                new_node_addr@,
            );
            assert(compact_tail + compact_prefix
                == compact_tail.push(new_node_addr@));
            let ghost model_added = compact_tail.to_multiset()
                .insert(new_node_addr@);
            broadcast use vstd::multiset::group_multiset_axioms;
            assert_multisets_equal!(
                iaddr_views(destinations@).to_multiset(),
                model_added,
                addr => {}
            );
            assert_multisets_equal!(
                seq_to_au_likes(new_aus@),
                to_au_likes(model_added),
                au => {}
            );
            let ghost model_new_betree_aus = pre_betree.betree_aus.sub(
                to_au_likes(
                    crate::implementation::CachedBranchBetree_v::
                        path_discard_likes(path.receipt@),
                ),
            ).add(to_au_likes(model_added));
            assert_multisets_equal!(
                self.ownership.betree@,
                model_new_betree_aus,
                au => {}
            );
            assert(compactor_views(self.compactors@)
                == pre_betree.compactors.remove(input_idx as int)) by {
                assert(self.compactors@ == pre_compactors.remove(input_idx as int));
                assert_seqs_equal!(
                    compactor_views(self.compactors@),
                    pre_betree.compactors.remove(input_idx as int),
                    i => {}
                );
            }
            assert(compactor_receipt_views(self.compactors@)
                == pre_betree.compactor_receipts.remove(
                    input_idx as int,
                )) by {
                assert(self.compactors@
                    == pre_compactors.remove(input_idx as int));
                assert_seqs_equal!(
                    compactor_receipt_views(self.compactors@),
                    pre_betree.compactor_receipts.remove(
                        input_idx as int,
                    ),
                    i => {}
                );
            }
            assert(bulk_branch_views(self.wip_branches@)
                == pre_betree.wip_branches.remove(branch_idx as int)) by {
                assert(self.wip_branches@ == pre_wip_seq.remove(branch_idx as int));
                assert_seqs_equal!(
                    bulk_branch_views(self.wip_branches@),
                    pre_betree.wip_branches.remove(branch_idx as int),
                    i => {}
                );
            }
            iaddress_aus_likes(input_buffers@, removes@);
            crate::implementation::AuLikesImpl_v::seq_to_au_likes_push(
                Seq::<IAU>::empty(),
                output_root.au,
            );
            assert(adds@ == Seq::<IAU>::empty().push(output_root.au));
            assert(seq_to_au_likes(adds@)
                == Multiset::singleton(output_root@.au));
            let ghost model_discarded_branches = path.receipt@.target().node
                .buffers.slice(start as int, end as int).addrs.to_multiset();
            assert(iaddr_views(input_buffers@)
                == path.receipt@.target().node.buffers.slice(
                    start as int,
                    end as int,
                ).addrs) by {
                assert(completion_compactor@
                    == pre_betree.compactors[input_idx as int]);
            }
            assert_multisets_equal!(
                iaddr_views(input_buffers@).to_multiset(),
                model_discarded_branches,
                addr => {}
            );
            assert_multisets_equal!(
                seq_to_au_likes(removes@),
                to_au_likes(model_discarded_branches),
                au => {}
            );
            assert(self.branch_likes@
                == pre_branch_likes
                    .sub(seq_to_au_likes(removes@))
                    .add(seq_to_au_likes(adds@)));
            let ghost model_new_branch_aus = pre_betree.branch_aus.sub(
                to_au_likes(model_discarded_branches),
            ).insert(output_root@.au);
            assert_multisets_equal!(
                self.branch_likes@,
                model_new_branch_aus,
                au => {}
            );
            crate::implementation::AuLikesImpl_v::seq_to_au_likes_dom(
                removes@,
            );
            crate::implementation::AuLikesImpl_v::seq_to_au_likes_dom(adds@);
            assert(iau_seq_set(became_zero@)
                =~= pre_branch_likes.dom() - self.branch_likes@.dom());
            assert(self.ownership.branches.active_summary_map()
                == pre_betree.branch_summary.insert(
                    output_root@.au,
                    output_summary,
                ).remove_keys(branch_deallocs));
            self.ownership.branches.active_summary_map_dom();
            assert(self.branch_likes@.dom()
                == self.ownership.branches.active_summary_map().dom()) by {
                assert(pre_betree.branch_aus.dom()
                    == pre_betree.branch_summary.dom());
                assert(!pre_betree.branch_aus.dom().contains(
                    output_root@.au,
                ));
                assert_sets_equal!(
                    self.branch_likes@.dom(),
                    self.ownership.branches.active_summary_map().dom(),
                    au => {}
                );
            }
            self.ownership.current_durable_matches_views(self.branch_likes@);
            assert(self.ownership.current_durable_aus()
                == self.betree_i().durable_aus());
            assert(self.wf());
            assert forall |addr: Address|
                #[trigger] path_reads@.contains_key(addr)
                implies cache0@.valid_read(addr, path_reads@[addr]) by {
                Cache::State::access_read_valid(
                    cache0@,
                    cache0@,
                    path_reads@,
                    Map::empty(),
                    addr,
                );
            }
            assert(pre_betree.is_fresh(allocs));
            assert(!crate::allocation_layer::AllocationBranchBetree_v::
                seq_addrs_to_aus(iaddr_views(path_addrs@))
                .contains(new_node_addr@.au));
            assert(seq_addrs_disjoint_aus(iaddr_views(path_addrs@)));
            assert(0 <= input_idx as int
                && (input_idx as int) < pre_betree.compactors.len());
            assert(0 <= branch_idx as int
                && (branch_idx as int) < pre_betree.wip_branches.len());
            assert(pre_betree.wip_branches[branch_idx as int].is_sealed());
            assert(pre_betree.wip_branches[branch_idx as int]
                == pre_wip_seq[branch_idx as int]@);
            assert(pre_wip_seq[branch_idx as int].sealed_branch@ is Some);
            assert(pre_wip_seq[branch_idx as int]
                .sealed_branch@.unwrap().root == output_root@);
            assert(pre_wip_seq[branch_idx as int]@.sealed_root()
                == pre_wip_seq[branch_idx as int]
                    .sealed_branch@.unwrap().root);
            assert(pre_betree.wip_branches[branch_idx as int]
                .sealed_root() == output_root@);
            assert(path.receipt@.valid_for(
                pre_betree.root,
                to_betree_nodes(path_reads@),
            ));
            assert(iaddr_views(path_addrs@).len() == path.receipt@.depth());
            assert((start as nat) < end as nat
                && (end as nat) <= path.receipt@.target().node.buffers.len());
            assert(pre_betree.compactors[input_idx as int]
                == CompactorInput {
                    input_buffers: path.receipt@.target().node.buffers.slice(
                        start as int,
                        end as int,
                    ),
                    offset_map: path.receipt@.target().node.make_offset_map()
                        .decrement(start as nat),
                });
            assert(to_betree_nodes(writes)
                == crate::implementation::CachedBranchBetree_v::
                    substitute_writes(
                        path.receipt@,
                        new_node_addr@,
                        crate::implementation::CachedBranchBetree_v::
                            compact_replacement(
                                path.receipt@,
                                start as nat,
                                end as nat,
                                output_root@,
                                crate::betree::LinkedBetree_v::TwoAddrs {
                                    addr1: new_node_addr@,
                                    addr2: output_root@,
                                },
                            ),
                        iaddr_views(path_addrs@),
                    ));
            assert(to_betree_nodes(writes).dom()
                <= Set::new(|addr: Address| addr.wf()));
            assert(allocs == to_aus(iaddr_views(path_addrs@).to_set())
                .insert(new_node_addr@.au));
            let ghost model_new_compactors = pre_betree.compactors.remove(
                input_idx as int,
            );
            assert(model_new_compactors == Seq::<CompactorInput>::empty()) by {
                assert(pre_betree.compactors.len() == 1);
                assert(input_idx == 0);
                assert_seqs_equal!(
                    model_new_compactors,
                    Seq::<CompactorInput>::empty(),
                    i => {}
                );
            }
            assert(read_ref_aus(model_new_compactors).is_empty());
            let ghost model_branch_deallocs = pre_betree.branch_summary.dom()
                - model_new_branch_aus.dom()
                - read_ref_aus(model_new_compactors);
            assert_sets_equal!(
                model_branch_deallocs,
                branch_deallocs,
                au => {
                    assert(pre_betree.branch_summary.dom()
                        == pre_branch_likes.dom());
                    assert(read_ref_aus(model_new_compactors).is_empty());
                }
            );
            let ghost model_with_new_summary = pre_betree.branch_summary
                .insert(output_root@.au, output_summary);
            let ghost model_new_branch_summary = model_with_new_summary
                .remove_keys(model_branch_deallocs);
            assert_maps_equal!(
                self.betree_i().branch_summary,
                model_new_branch_summary,
                au => {}
            );
            let ghost model_deallocated_summary = pre_betree.branch_summary
                .restrict(model_branch_deallocs);
            assert(model_deallocated_summary.dom()
                <= pre_betree.branch_summary.dom());
            crate::betree::Utils_v::lemma_subset_finite(
                pre_betree.branch_summary.dom(),
                model_deallocated_summary.dom(),
            );
            vstd::map_lib::lemma_values_finite(model_deallocated_summary);
            let ghost retired_summaries = before_branch_retire
                .active_summary_map().restrict(branch_deallocs);
            assert(before_branch_retire.active_summary_map()
                == pre_betree.branch_summary.insert(
                    output_root@.au,
                    output_summary,
                ));
            assert(!branch_deallocs.contains(output_root@.au));
            assert_maps_equal!(
                retired_summaries,
                model_deallocated_summary,
                au => {}
            );
            pre_ownership.branches.active_summary_restrict_subset(
                model_branch_deallocs,
            );
            assert(model_deallocated_summary
                == pre_ownership.branches.active_summary_map().restrict(
                    model_branch_deallocs,
                ));
            assert(summary_aus(model_deallocated_summary)
                <= pre_ownership.branches.active_summary_aus());
            assert(iau_seq_set(branch_reclaimed@)
                <= summary_aus(model_deallocated_summary)) by {
                assert(iau_seq_set(branch_reclaimed@)
                    <= summary_aus(retired_summaries));
            }
            let ghost model_deallocs = (
                pre_betree.betree_aus.dom()
                    - self.betree_i().betree_aus.dom()
            ) + summary_aus(model_deallocated_summary);
            assert_sets_equal!(deallocs, model_deallocs, au => {});
            let ghost betree_deallocs = pre_betree.betree_aus.dom()
                - self.betree_i().betree_aus.dom();
            let ghost summary_deallocs =
                summary_aus(model_deallocated_summary);
            assert({
                &&& iau_seq_set(branch_reclaimed@) <= deallocs
                &&& iau_seq_set(betree_reclaimed@).disjoint(
                    iau_seq_set(branch_reclaimed@),
                )
                &&& iau_seq_set(betree_reclaimed@)
                        + iau_seq_set(branch_reclaimed@)
                    =~= pre_state.control.reclaimable(deallocs)
            }) by {
                BranchSummaryOwnershipImpl::retire_many_reclaimed_exact(
                    before_branch_retire,
                    after_branch_retire,
                    became_zero@,
                    branch_reclaimed@,
                );
                pre_impl.protected_aus_match_ownership();
                assert(iau_seq_set(branch_reclaimed@) <= deallocs);
                assert(betree_deallocs =~= iau_seq_set(old_aus@));
                assert(iau_seq_set(betree_reclaimed@)
                    =~= betree_deallocs
                        - pre_ownership.betree.persistent_aus()
                        - pre_ownership.betree.frozen_aus());
                assert(before_branch_retire.persistent_aus()
                    =~= pre_ownership.branches.persistent_aus());
                assert(before_branch_retire.frozen_aus()
                    =~= pre_ownership.branches.frozen_aus());
                assert(before_branch_retire.active_summary_map().restrict(
                    iau_seq_set(became_zero@),
                ) == retired_summaries) by {
                    assert_sets_equal!(
                        iau_seq_set(became_zero@),
                        branch_deallocs,
                        au => {}
                    );
                }
                assert(iau_seq_set(branch_reclaimed@)
                    =~= summary_deallocs
                        - pre_ownership.branches.persistent_aus()
                        - pre_ownership.branches.frozen_aus());
                assert(betree_deallocs
                    <= pre_ownership.betree.active_aus());
                assert(summary_deallocs
                    <= pre_ownership.branches.active_summary_aus());
                ownership_reclaims_compose(
                    pre_ownership,
                    betree_deallocs,
                    summary_deallocs,
                    iau_seq_set(betree_reclaimed@),
                    iau_seq_set(branch_reclaimed@),
                );
            }
            let ghost model_input_dv = BufferDisk::<BranchNode> {
                entries: pre_betree.compactor_receipts[input_idx as int],
            };
            let ghost model_output_dv = BufferDisk::<BranchNode> {
                entries: completion_output_branch.disk_view.entries,
            };
            assert(pre_betree.compactor_receipts[input_idx as int]
                == completion_compactor.input_nodes@);
            assert(pre_betree.wip_branches[branch_idx as int]
                .sealed_branch() == completion_output_branch);
            assert forall |candidate: Key|
                completion_output_branch.root().linked_contains(
                    model_output_dv,
                    completion_output_branch.root,
                    candidate,
                ) <==> model_input_dv.valid_compact_key_domain(
                    path.receipt@.target().node,
                    start as nat,
                    end as nat,
                    candidate,
                ) by {
            }
            assert forall |candidate: Key|
                completion_output_branch.root().linked_contains(
                    model_output_dv,
                    completion_output_branch.root,
                    candidate,
                ) implies completion_output_branch.root().linked_query(
                    model_output_dv,
                    completion_output_branch.root,
                    candidate,
                ) == model_input_dv.compact_key_value(
                    path.receipt@.target().node,
                    start as nat,
                    end as nat,
                    candidate,
                ) by {
            }
            assert_maps_equal!(
                to_branch_nodes(Map::<Address, RawPage>::empty()),
                Map::empty(),
                addr => {}
            );
            assert(access.cached_access() == CachedBranchBetreeAccess {
                betree_reads: to_betree_nodes(path_reads@),
                betree_writes: to_betree_nodes(writes),
                ..CachedBranchBetreeAccess::empty()
            });
            assert(CachedBranchBetree::State::compact_complete(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access: access.cached_access(),
                },
                input_idx as int,
                branch_idx as int,
                path.receipt@,
                start as nat,
                end as nat,
                new_node_addr@,
                iaddr_views(path_addrs@),
                to_betree_nodes(path_reads@),
                to_betree_nodes(writes),
            )) by {

            }
            assert(CachedBranchBetree::State::next_by(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access: access.cached_access(),
                },
                CachedBranchBetree::Step::compact_complete(
                    input_idx as int,
                    branch_idx as int,
                    path.receipt@,
                    start as nat,
                    end as nat,
                    new_node_addr@,
                    iaddr_views(path_addrs@),
                    to_betree_nodes(path_reads@),
                    to_betree_nodes(writes),
                ),
            )) by {
                reveal(CachedBranchBetree::State::next_by);
            }
            assert(CachedBranchBetree::State::next(
                pre_betree,
                self.betree_i(),
                CachedBranchBetree::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access: access.cached_access(),
                },
            )) by {
                reveal(CachedBranchBetree::State::next);
            }
            assert(AtomicBranchBetreeState::State::compact_complete(
                pre_state,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access,
                },
                self.betree_i(),
                input_idx as int,
                branch_idx as int,
                path.receipt@,
                start as nat,
                end as nat,
                new_node_addr@,
                iaddr_views(path_addrs@),
                to_betree_nodes(path_reads@),
                to_betree_nodes(writes),
            )) by {

            }
            assert(AtomicBranchBetreeState::State::next_by(
                pre_state,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access,
                },
                AtomicBranchBetreeState::Step::compact_complete(
                    self.betree_i(),
                    input_idx as int,
                    branch_idx as int,
                    path.receipt@,
                    start as nat,
                    end as nat,
                    new_node_addr@,
                    iaddr_views(path_addrs@),
                    to_betree_nodes(path_reads@),
                    to_betree_nodes(writes),
                ),
            )) by {
                reveal(AtomicBranchBetreeState::State::next_by);
            }
            assert(AtomicBranchBetreeState::State::next(
                pre_state,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access,
                },
            )) by {
                reveal(AtomicBranchBetreeState::State::next);
            }
            assert(iau_seq_set(betree_reclaimed@).disjoint(
                iau_seq_set(branch_reclaimed@),
            ));
            assert(iau_seq_set(betree_reclaimed@)
                    + iau_seq_set(branch_reclaimed@)
                == pre_state.control.reclaimable(deallocs));
            assert(prepared_cache == cache0@);
            assert(Cache::State::next_by(
                cache0@,
                cache0@,
                Cache::Label::Internal,
                Cache::Step::noop(),
            )) by {
                reveal(Cache::State::next_by);
            }
            assert(Cache::State::next(
                cache0@,
                prepared_cache,
                Cache::Label::Internal,
            )) by {
                reveal(Cache::State::next);
            }
            assert(access.reads() == path_reads@);
            assert(access.writes() == writes);
            assert(access.loaded_betree_writes()
                == to_betree_nodes(writes));
            assert(Cache::State::next(
                prepared_cache,
                cache@,
                Cache::Label::Access {
                    reads: access.reads(),
                    writes: access.writes(),
                },
            ));
            assert(AtomicBranchBetreeState::State::next(
                pre_state,
                self@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs,
                    deallocs,
                    access,
                },
            ));
        }
        BranchBetreeCompactCompleteResult::Completed {
            new_root,
            betree_reclaimed,
            branch_reclaimed,
            prepared_cache: Ghost(prepared_cache),
            access: Ghost(access),
            allocs: Ghost(allocs),
            deallocs: Ghost(deallocs),
        }
    }

    pub fn put_batch(
        &mut self,
        puts: &Vec<KeyedMessage>,
    ) -> (result: BranchBetreePutResult)
        requires
            old(self).wf(),
            old(self).control.metadata_loaded,
        ensures
            self.wf(),
            self.compactors@ == old(self).compactors@,
            self.root == old(self).root,
            self.ownership == old(self).ownership,
            self.branch_likes == old(self).branch_likes,
            self.wip_branches@ == old(self).wip_branches@,
            self.control == old(self).control,
            match result {
                BranchBetreePutResult::Applied => {
                    let history = MemtableImpl::history_from_seq(
                        old(self).memtable.seq_end as nat,
                        puts@,
                    );
                    AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::Put {puts: history},
                    )
                },
                BranchBetreePutResult::Noop => self@ == old(self)@,
            },
    {
        if self.wip_branches.len() != 0 {
            return BranchBetreePutResult::Noop;
        }
        let start_lsn = self.memtable.seq_end;
        match self.memtable.apply_puts(start_lsn, puts) {
            MemtableUpdateResult::Noop => BranchBetreePutResult::Noop,
            MemtableUpdateResult::Applied => {
                proof {
                    let history = MemtableImpl::history_from_seq(
                        start_lsn as nat,
                        puts@,
                    );
                    MemtableImpl::history_from_seq_wf(
                        start_lsn as nat,
                        puts@,
                    );
                    assert(history.can_follow(
                        old(self).betree_i().memtable.seq_end,
                    ));
                    assert(CachedBranchBetree::State::put(
                        old(self).betree_i(),
                        self.betree_i(),
                        CachedBranchBetree::Label::Put { puts: history },
                    )) by {

                    }
                    assert(CachedBranchBetree::State::next_by(
                        old(self).betree_i(),
                        self.betree_i(),
                        CachedBranchBetree::Label::Put { puts: history },
                        CachedBranchBetree::Step::put(),
                    )) by {
                        reveal(CachedBranchBetree::State::next_by);
                    }
                    assert(CachedBranchBetree::State::next(
                        old(self).betree_i(),
                        self.betree_i(),
                        CachedBranchBetree::Label::Put { puts: history },
                    )) by {
                        reveal(CachedBranchBetree::State::next);
                    }
                    assert(AtomicBranchBetreeState::State::next_by(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::Put { puts: history },
                        AtomicBranchBetreeState::Step::put(self.betree_i()),
                    )) by {
                        reveal(AtomicBranchBetreeState::State::next_by);
                    }
                    assert(AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::Put { puts: history },
                    )) by {
                        reveal(AtomicBranchBetreeState::State::next);
                    }
                    assert(self.wf());

                }
                BranchBetreePutResult::Applied
            },
        }
    }

    pub fn commit_start(&mut self) -> (result: BranchBetreeCommitResult)
        requires
            old(self).wf(),
            old(self).control.metadata_loaded,
            old(self).wip_branches@.len() == 0,
            old(self).compactors@.len() == 0,
        ensures
            self.wf(),
            match result {
                BranchBetreeCommitResult::Applied => {
                    let image = FrozenBranchBetree {
                        root: old(self).betree_i().root,
                        seq_end: old(self).betree_i().memtable.seq_end,
                    };
                    &&& AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::CommitStart { image },
                    )
                    &&& self@ == AtomicBranchBetreeState::State {
                        control: AtomicBranchBetreeControl {
                            frozen: Some(FrozenCachingDiskBranchBetree {
                                metadata: CachingDiskBranchBetreeMetadata {
                                    root: old(self)@.betree.root,
                                    seq_end: old(self)@.betree.memtable.seq_end,
                                },
                                aus: old(self)@.betree.durable_aus(),
                            }),
                            ..old(self)@.control
                        },
                        ..old(self)@
                    }
                    &&& self.root == old(self).root
                    &&& self.memtable == old(self).memtable
                    &&& self.wip_branches@ == old(self).wip_branches@
                    &&& self.compactors@ == old(self).compactors@
                    &&& self.ownership.betree.active_aus()
                        == old(self).ownership.betree.active_aus()
                    &&& self.ownership.branches.active_summary_aus()
                        == old(self).ownership.branches.active_summary_aus()
                    &&& self.ownership.current_durable_aus()
                        == old(self).ownership.current_durable_aus()
                    &&& self.ownership.betree.all_aus()
                        == old(self).ownership.betree.all_aus()
                    &&& self.ownership.branches.all_summary_aus()
                        == old(self).ownership.branches.all_summary_aus()
                    &&& self.ownership.frozen_aus()
                        == self.ownership.current_durable_aus()
                },
                BranchBetreeCommitResult::Noop => *self == *old(self),
            },
    {
        if self.control.frozen_metadata.is_some() {
            return BranchBetreeCommitResult::Noop;
        }
        if !self.memtable.is_empty() {
            return BranchBetreeCommitResult::Noop;
        }
        let frozen_metadata = BetreeMetadataImpl {
            root: self.root,
            seq_end: self.memtable.seq_end,
        };
        self.ownership.freeze_current();
        self.control.frozen_metadata = Some(frozen_metadata);
        proof {
            let image = FrozenBranchBetree {
                root: old(self).betree_i().root,
                seq_end: old(self).betree_i().memtable.seq_end,
            };
            assert(CachedBranchBetree::State::freeze_as(
                old(self).betree_i(),
                old(self).betree_i(),
                CachedBranchBetree::Label::FreezeAs { image },
            )) by {

            }
            assert(CachedBranchBetree::State::next_by(
                old(self).betree_i(),
                old(self).betree_i(),
                CachedBranchBetree::Label::FreezeAs { image },
                CachedBranchBetree::Step::freeze_as(),
            )) by {
                reveal(CachedBranchBetree::State::next_by);
            }
            assert(CachedBranchBetree::State::next(
                old(self).betree_i(),
                old(self).betree_i(),
                CachedBranchBetree::Label::FreezeAs { image },
            )) by {
                reveal(CachedBranchBetree::State::next);
            }
            assert(self.betree_i() == old(self).betree_i());
            assert(self.ownership.frozen_aus()
                == old(self).betree_i().durable_aus());
            assert(self.frozen_i() == Some(FrozenCachingDiskBranchBetree {
                metadata: CachingDiskBranchBetreeMetadata {
                    root: old(self).betree_i().root,
                    seq_end: old(self).betree_i().memtable.seq_end,
                },
                aus: old(self).betree_i().durable_aus(),
            }));
            assert(self@ == AtomicBranchBetreeState::State {
                control: AtomicBranchBetreeControl {
                    frozen: Some(FrozenCachingDiskBranchBetree {
                        metadata: CachingDiskBranchBetreeMetadata {
                            root: old(self)@.betree.root,
                            seq_end: old(self)@.betree.memtable.seq_end,
                        },
                        aus: old(self)@.betree.durable_aus(),
                    }),
                    ..old(self)@.control
                },
                ..old(self)@
            });
            assert(self.wf());
            assert(AtomicBranchBetreeState::State::next_by(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::CommitStart { image },
                AtomicBranchBetreeState::Step::commit_start(),
            )) by {
                reveal(AtomicBranchBetreeState::State::next_by);
            }
            assert(AtomicBranchBetreeState::State::next(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::CommitStart { image },
            )) by {
                reveal(AtomicBranchBetreeState::State::next);
            }
        }
        BranchBetreeCommitResult::Applied
    }

    pub proof fn commit_prepared_step(&self)
        requires
            self.wf(),
            self.control.frozen_metadata is Some,
        ensures
            AtomicBranchBetreeState::State::next(
                self@,
                self@,
                AtomicBranchBetreeState::Label::CommitPrepared,
            ),
    {
        assert(AtomicBranchBetreeState::State::next_by(
            self@,
            self@,
            AtomicBranchBetreeState::Label::CommitPrepared,
            AtomicBranchBetreeState::Step::commit_prepared(),
        )) by {
            reveal(AtomicBranchBetreeState::State::next_by);
        }
        assert(AtomicBranchBetreeState::State::next(
            self@,
            self@,
            AtomicBranchBetreeState::Label::CommitPrepared,
        )) by {
            reveal(AtomicBranchBetreeState::State::next);
        }
    }

    pub fn commit_complete(
        &mut self,
    ) -> (result: BranchBetreeCommitCompleteResult)
        requires old(self).wf(),
        ensures
            self.wf(),
            old(self).control.frozen_metadata is Some
                ==> result is Applied,
            old(self).control.frozen_metadata is None
                ==> result is Noop,
            match result {
                BranchBetreeCommitCompleteResult::Applied { reclaimed } => {
                    &&& AtomicBranchBetreeState::State::next(
                        old(self)@,
                        self@,
                        AtomicBranchBetreeState::Label::CommitComplete,
                    )
                    &&& self@ == AtomicBranchBetreeState::State {
                        control: AtomicBranchBetreeControl {
                            metadata: old(self)@.control.frozen
                                .unwrap().metadata,
                            persistent_aus: old(self)@.control.frozen
                                .unwrap().aus,
                            frozen: None,
                            ..old(self)@.control
                        },
                        ..old(self)@
                    }
                    &&& unique_iau_seq(reclaimed@)
                    &&& iau_seq_set(reclaimed@)
                        == old(self).ownership.persistent_aus()
                            - old(self).ownership.frozen_aus()
                            - old(self).ownership.current_durable_aus()
                    &&& old(self).wip_branches@.len() == 0 ==> {
                        iau_seq_set(reclaimed@)
                            == old(self)@.control.persistent_aus
                                - old(self)@.control.frozen.unwrap().aus
                                - old(self)@.betree.owned_aus()
                    }
                    &&& self.root == old(self).root
                    &&& self.memtable == old(self).memtable
                    &&& self.wip_branches@ == old(self).wip_branches@
                    &&& self.compactors@ == old(self).compactors@
                    &&& self.control.metadata
                        == old(self).control.frozen_metadata.unwrap()
                    &&& self.control.frozen_metadata is None
                    &&& self.ownership.betree.all_aus()
                        <= old(self).ownership.betree.all_aus()
                    &&& self.ownership.branches.all_summary_aus()
                        <= old(self).ownership.branches.all_summary_aus()
                },
                BranchBetreeCommitCompleteResult::Noop => self@ == old(self)@,
            },
    {
        let frozen_metadata = match self.control.frozen_metadata {
            Some(metadata) => metadata,
            None => return BranchBetreeCommitCompleteResult::Noop,
        };
        let reclaimed = self.ownership.commit_complete();
        self.control.metadata = frozen_metadata;
        self.control.frozen_metadata = None;
        proof {
            assert(self.betree_i() == old(self).betree_i());
            assert(self.control_i().persistent_aus
                == old(self).control_i().frozen.unwrap().aus);
            assert(self.control_i().frozen is None);
            assert(self@ == AtomicBranchBetreeState::State {
                control: AtomicBranchBetreeControl {
                    metadata: old(self)@.control.frozen.unwrap().metadata,
                    persistent_aus: old(self)@.control.frozen.unwrap().aus,
                    frozen: None,
                    ..old(self)@.control
                },
                ..old(self)@
            });
            if old(self).wip_branches@.len() == 0 {
                old(self).ownership.current_durable_matches_views(
                    old(self).branch_likes@,
                );
                assert(old(self).ownership.current_durable_aus()
                    == old(self).betree_i().durable_aus());
                assert(old(self).betree_i().wip_branches.len() == 0);
                assert(old(self).betree_i().owned_aus()
                    == old(self).betree_i().durable_aus()) by {



                }
            }
            assert(self.wf());
            assert(AtomicBranchBetreeState::State::next_by(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::CommitComplete,
                AtomicBranchBetreeState::Step::commit_complete(),
            )) by {
                reveal(AtomicBranchBetreeState::State::next_by);
            }
            assert(AtomicBranchBetreeState::State::next(
                old(self)@,
                self@,
                AtomicBranchBetreeState::Label::CommitComplete,
            )) by {
                reveal(AtomicBranchBetreeState::State::next);
            }
        }
        BranchBetreeCommitCompleteResult::Applied { reclaimed }
    }
}

impl View for BranchBetreeImpl {
    type V = AtomicBranchBetreeState::State;

    open spec fn view(&self) -> Self::V {
        self.i()
    }
}

#[allow(dead_code)]
fn verify_empty_branch_betree_impl() {
    let mut branch = BranchBetreeImpl::new(2, 4);
    proof {
        assert(branch.wf());
        assert(branch@ == AtomicBranchBetreeState::State::empty());
    }
    let metadata = BetreeMetadataImpl::empty();
    branch.initialize_from_metadata(metadata);
    let ghost pre = branch@;
    let begun = branch.recovery_begin();
    proof {
        assert(begun is Applied);
        assert(AtomicBranchBetreeState::State::next(
            pre,
            branch@,
            AtomicBranchBetreeState::Label::Internal,
        ));
    }
}

} // verus!
