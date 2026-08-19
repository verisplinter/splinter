// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;

use crate::allocation_layer::AllocationBranchBetree_v::map_with_disjoint_values;
use crate::allocation_layer::BranchTypes_v::{BranchNode, Summary};
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::Buffer_v::Buffer;
use crate::betree::LinkedBetree_v::BetreeNode;
use crate::betree::LinkedBranch_v::LinkedBranch;
use crate::disk::GenericDisk_v::AU;
use crate::implementation::BranchBetreeImpl_v::{
    CompactorImpl, compact_stream_entries, compactor_input_root_aus,
};
use crate::implementation::BranchScanSemantics_v::{
    keyed_entries_contains, keyed_entries_query,
    sealed_branch_refines_buffer,
};
use crate::implementation::CompactorMergeCursorImpl_v::keyed_entries_strictly_sorted;
use crate::implementation::MemtableImpl_v::{MemtableBucket, MemtableEntry};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::Message;

verus! {

proof fn compact_stream_entries_index(
    entries: Seq<crate::abstract_system::MsgHistory_v::KeyedMessage>,
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

proof fn compact_stream_entries_map_refines(
    entries: Seq<crate::abstract_system::MsgHistory_v::KeyedMessage>,
)
    requires keyed_entries_strictly_sorted(entries),
    ensures
        MemtableBucket::strictly_sorted(compact_stream_entries(entries)),
        MemtableBucket::unique_keys(compact_stream_entries(entries)),
        forall |key: Key|
            MemtableBucket::entries_map(compact_stream_entries(entries))
                .contains_key(key)
                <==> keyed_entries_contains(entries, key),
        forall |key: Key|
            keyed_entries_contains(entries, key)
                ==> MemtableBucket::entries_map(
                    compact_stream_entries(entries),
                )[key] == keyed_entries_query(entries, key),
{
    let converted = compact_stream_entries(entries);
    assert(MemtableBucket::strictly_sorted(converted)) by {
        assert forall |i: int, j: int| 0 <= i < j < converted.len()
            implies converted[i].key.0 < converted[j].key.0 by {
            compact_stream_entries_index(entries, i);
            compact_stream_entries_index(entries, j);
            assert(Key::lt(entries[i].key, entries[j].key));
        }
    }
    assert(MemtableBucket::unique_keys(converted)) by {
        assert forall |i: int, j: int|
            #![trigger converted[i].key, converted[j].key]
            0 <= i < converted.len()
            && 0 <= j < converted.len()
            && converted[i].key == converted[j].key
            implies i == j by {
            if i < j {
                assert(converted[i].key.0 < converted[j].key.0);
                assert(false);
            }
            if j < i {
                assert(converted[j].key.0 < converted[i].key.0);
                assert(false);
            }
        }
    }
    assert forall |key: Key|
        MemtableBucket::entries_map(converted).contains_key(key)
            <==> keyed_entries_contains(entries, key) by {
        if keyed_entries_contains(entries, key) {
            let i = choose |i: int| 0 <= i < entries.len()
                && entries[i].key == key;
            compact_stream_entries_index(entries, i);
            MemtableBucket::entries_map_index(converted, i);
        }
        if MemtableBucket::entries_map(converted).contains_key(key) {
            let i = MemtableBucket::entries_map_index_for_key(converted, key);
            compact_stream_entries_index(entries, i);
            assert(entries[i].key == key);
        }
    }
    assert forall |key: Key|
        keyed_entries_contains(entries, key)
            implies MemtableBucket::entries_map(converted)[key]
                == keyed_entries_query(entries, key) by {
        let i = choose |i: int| 0 <= i < entries.len()
            && entries[i].key == key;
        compact_stream_entries_index(entries, i);
        MemtableBucket::entries_map_index(converted, i);
        crate::implementation::BranchScanSemantics_v::keyed_entries_query_index(
            entries,
            i,
        );
    }
}

proof fn compact_target_semantics_equal(
    disk: BufferDisk<BranchNode>,
    left: BetreeNode,
    right: BetreeNode,
    start: nat,
    end: nat,
    key: Key,
)
    requires
        left.wf(),
        right.wf(),
        left.buffers.slice(start as int, end as int)
            == right.buffers.slice(start as int, end as int),
        left.pivots.pivots == right.pivots.pivots,
        left.flushed.offsets == right.flushed.offsets,
        start < end <= left.buffers.len(),
        end <= right.buffers.len(),
    ensures
        disk.valid_compact_key_domain(left, start, end, key)
            == disk.valid_compact_key_domain(right, start, end, key),
        disk.compact_key_value(left, start, end, key)
            == disk.compact_key_value(right, start, end, key),
{
    assert(left.key_in_domain(key) == right.key_in_domain(key));
    let left_slice = left.buffers.slice(start as int, end as int);
    let right_slice = right.buffers.slice(start as int, end as int);
    let left_offsets = left.make_offset_map().decrement(start);
    let right_offsets = right.make_offset_map().decrement(start);
    assert(left_slice == right_slice);
    if left.key_in_domain(key) {
        assert(left.pivots.route(key) == right.pivots.route(key));
        assert(left.flushed_ofs(key) == right.flushed_ofs(key));
        assert(left.make_offset_map().offsets[key]
            == right.make_offset_map().offsets[key]);
        assert(left_offsets.offsets[key] == right_offsets.offsets[key]);
        assert forall |idx: int|
            disk.key_in_buffer_filtered(
                left_slice,
                left_offsets,
                0,
                key,
                idx,
            ) == disk.key_in_buffer_filtered(
                right_slice,
                right_offsets,
                0,
                key,
                idx,
            ) by {
        }
    }
}

pub proof fn completed_output_valid(
    compactor: &CompactorImpl,
    branch_summary: Map<AU, Set<AU>>,
)
    requires
        compactor.wf(),
        compactor.merge is Some,
        compactor.merge_done,
        map_with_disjoint_values(branch_summary),
        compactor_input_root_aus(*compactor) <= branch_summary.dom(),
        compactor.input_summaries@ == branch_summary.restrict(
            compactor_input_root_aus(*compactor),
        ),
    ensures ({
        let disk = BufferDisk::<BranchNode> {
            entries: compactor.input_nodes@,
        };
        let target = compactor.filter.target@;
        let output = compactor.merge->0.output@;
        &&& forall |key: Key|
            keyed_entries_contains(output, key)
                <==> disk.valid_compact_key_domain(
                    target,
                    compactor.filter.start as nat,
                    compactor.filter.end as nat,
                    key,
                )
        &&& forall |key: Key|
            keyed_entries_contains(output, key)
                ==> keyed_entries_query(output, key)
                    == disk.compact_key_value(
                        target,
                        compactor.filter.start as nat,
                        compactor.filter.end as nat,
                        key,
                    )
    }),
{
    let merge = compactor.merge->0;
    merge.source_roots_match_filter();
    assert(merge.source_roots()
        == crate::marshalling::Marshalling_v::Parsedview::<
            Seq<crate::disk::GenericDisk_v::Address>
        >::parsedv(&compactor.input_buffers).to_set());
    assert(crate::disk::GenericDisk_v::set_addrs_disjoint_aus(
        merge.source_roots(),
    ));
    assert forall |i: int| 0 <= i < merge.cursors@.len()
        implies {
            let source = (#[trigger] merge.cursors@[i]).source@;
            &&& branch_summary.contains_key(source.root.au)
            &&& branch_summary[source.root.au] == source.get_summary()
        } by {
        let source = merge.cursors@[i].source@;
        assert(compactor.input_summaries@.contains_key(source.root.au));
        assert(compactor_input_root_aus(*compactor)
            .contains(source.root.au)) by {
            let roots = crate::marshalling::Marshalling_v::Parsedview::<
                Seq<crate::disk::GenericDisk_v::Address>
            >::parsedv(&compactor.input_buffers).to_set();
            assert(roots.contains(source.root));
            crate::disk::GenericDisk_v::to_aus_domain(roots);
        }
        assert(compactor.input_summaries@[source.root.au]
            == branch_summary[source.root.au]);
    }
    merge.completed_output_refines_receipt(branch_summary);
    assert(compactor.input_nodes@ == merge.scanned_nodes());
    let disk = BufferDisk::<BranchNode> {
        entries: compactor.input_nodes@,
    };
    let target = compactor.filter.target@;
    assert(merge.filter.target@.buffers == target.buffers);
    assert(merge.filter.target@.pivots.pivots == target.pivots.pivots);
    assert(merge.filter.target@.flushed.offsets == target.flushed.offsets);
    assert forall |key: Key|
        keyed_entries_contains(merge.output@, key)
            <==> disk.valid_compact_key_domain(
                target,
                compactor.filter.start as nat,
                compactor.filter.end as nat,
                key,
            ) by {
        compact_target_semantics_equal(
            disk,
            merge.filter.target@,
            target,
            compactor.filter.start as nat,
            compactor.filter.end as nat,
            key,
        );
    }
    assert forall |key: Key|
        keyed_entries_contains(merge.output@, key)
            implies keyed_entries_query(merge.output@, key)
                == disk.compact_key_value(
                    target,
                    compactor.filter.start as nat,
                    compactor.filter.end as nat,
                    key,
                ) by {
        compact_target_semantics_equal(
            disk,
            merge.filter.target@,
            target,
            compactor.filter.start as nat,
            compactor.filter.end as nat,
            key,
        );
    }
}

pub proof fn sealed_output_valid(
    compactor: &CompactorImpl,
    branch_summary: Map<AU, Set<AU>>,
    output_branch: LinkedBranch<Summary>,
)
    requires
        compactor.wf(),
        compactor.merge is Some,
        compactor.merge_done,
        map_with_disjoint_values(branch_summary),
        compactor_input_root_aus(*compactor) <= branch_summary.dom(),
        compactor.input_summaries@ == branch_summary.restrict(
            compactor_input_root_aus(*compactor),
        ),
        output_branch.valid_sealed_branch(),
        output_branch.tight_disk_view_with_summary(),
        output_branch.i().i().map
            == MemtableBucket::entries_map(compact_stream_entries(
                compactor.merge->0.output@,
            )),
    ensures ({
        let input_disk = BufferDisk::<BranchNode> {
            entries: compactor.input_nodes@,
        };
        let output_disk = BufferDisk::<BranchNode> {
            entries: output_branch.disk_view.entries,
        };
        let target = compactor.filter.target@;
        &&& forall |key: Key|
            output_branch.root().linked_contains(
                output_disk,
                output_branch.root,
                key,
            ) <==> input_disk.valid_compact_key_domain(
                target,
                compactor.filter.start as nat,
                compactor.filter.end as nat,
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
                compactor.filter.start as nat,
                compactor.filter.end as nat,
                key,
            )
    }),
{
    let merge = compactor.merge->0;
    completed_output_valid(compactor, branch_summary);
    compact_stream_entries_map_refines(merge.output@);
    let input_disk = BufferDisk::<BranchNode> {
        entries: compactor.input_nodes@,
    };
    let output_disk = BufferDisk::<BranchNode> {
        entries: output_branch.disk_view.entries,
    };
    let converted = compact_stream_entries(merge.output@);
    assert forall |key: Key|
        output_branch.root().linked_contains(
            output_disk,
            output_branch.root,
            key,
        ) <==> input_disk.valid_compact_key_domain(
            compactor.filter.target@,
            compactor.filter.start as nat,
            compactor.filter.end as nat,
            key,
        ) by {
        sealed_branch_refines_buffer(output_branch, key);
        assert(output_branch.i().i().map
            == MemtableBucket::entries_map(converted));
        assert(MemtableBucket::entries_map(converted).contains_key(key)
            <==> keyed_entries_contains(merge.output@, key));
    }
    assert forall |key: Key|
        output_branch.root().linked_contains(
            output_disk,
            output_branch.root,
            key,
        ) implies output_branch.root().linked_query(
            output_disk,
            output_branch.root,
            key,
        ) == input_disk.compact_key_value(
            compactor.filter.target@,
            compactor.filter.start as nat,
            compactor.filter.end as nat,
            key,
        ) by {
        sealed_branch_refines_buffer(output_branch, key);
        assert(output_branch.i().i().map.contains_key(key));
        assert(output_branch.i().i().map
            == MemtableBucket::entries_map(converted));
        assert(MemtableBucket::entries_map(converted)[key]
            == keyed_entries_query(merge.output@, key));
        assert(output_branch.i().i().query(key)
            == output_branch.i().i().map[key]);
    }
}

pub proof fn sealed_output_valid_for_target(
    compactor: &CompactorImpl,
    branch_summary: Map<AU, Set<AU>>,
    output_branch: LinkedBranch<Summary>,
    target: BetreeNode,
    start: nat,
    end: nat,
)
    requires
        compactor.wf(),
        compactor.merge is Some,
        compactor.merge_done,
        map_with_disjoint_values(branch_summary),
        compactor_input_root_aus(*compactor) <= branch_summary.dom(),
        compactor.input_summaries@ == branch_summary.restrict(
            compactor_input_root_aus(*compactor),
        ),
        output_branch.valid_sealed_branch(),
        output_branch.tight_disk_view_with_summary(),
        output_branch.i().i().map
            == MemtableBucket::entries_map(compact_stream_entries(
                compactor.merge->0.output@,
            )),
        target.wf(),
        start < end <= target.buffers.len(),
        compactor.filter.start as nat == start,
        compactor.filter.end as nat == end,
        compactor.filter.target@.buffers.slice(start as int, end as int)
            == target.buffers.slice(start as int, end as int),
        compactor.filter.target@.pivots.pivots == target.pivots.pivots,
        compactor.filter.target@.flushed.offsets == target.flushed.offsets,
    ensures ({
        let input_disk = BufferDisk::<BranchNode> {
            entries: compactor.input_nodes@,
        };
        let output_disk = BufferDisk::<BranchNode> {
            entries: output_branch.disk_view.entries,
        };
        &&& forall |key: Key|
            output_branch.root().linked_contains(
                output_disk,
                output_branch.root,
                key,
            ) <==> input_disk.valid_compact_key_domain(
                target,
                start,
                end,
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
            ) == input_disk.compact_key_value(target, start, end, key)
    }),
{
    sealed_output_valid(compactor, branch_summary, output_branch);
    let input_disk = BufferDisk::<BranchNode> {
        entries: compactor.input_nodes@,
    };
    assert forall |key: Key|
        output_branch.root().linked_contains(
            BufferDisk::<BranchNode> {
                entries: output_branch.disk_view.entries,
            },
            output_branch.root,
            key,
        ) <==> input_disk.valid_compact_key_domain(
            target,
            start,
            end,
            key,
        ) by {
        compact_target_semantics_equal(
            input_disk,
            compactor.filter.target@,
            target,
            start,
            end,
            key,
        );
    }
    assert forall |key: Key|
        output_branch.root().linked_contains(
            BufferDisk::<BranchNode> {
                entries: output_branch.disk_view.entries,
            },
            output_branch.root,
            key,
        ) implies output_branch.root().linked_query(
            BufferDisk::<BranchNode> {
                entries: output_branch.disk_view.entries,
            },
            output_branch.root,
            key,
        ) == input_disk.compact_key_value(target, start, end, key) by {
        compact_target_semantics_equal(
            input_disk,
            compactor.filter.target@,
            target,
            start,
            end,
            key,
        );
    }
}

}
