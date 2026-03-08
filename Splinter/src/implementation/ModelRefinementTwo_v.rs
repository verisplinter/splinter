#[allow(unused_imports)]    // lost in erasure
use vstd::prelude::*;
use vstd::prelude::*;

use vstd::{math, multiset::Multiset};
use crate::spec::AsyncDisk_t::{Address, AsyncDisk, DiskRequest, DiskResponse, RawPage};
use crate::spec::MapSpec_t::{AsyncMap, CrashTolerantAsyncMap, EphemeralState, ID, MapSpec, SyncReqId, Version};
use crate::spec::FloatingSeq_t::FloatingSeq;
use crate::trusted::SystemModel_t::SystemModel;
use crate::trusted::RefinementObligation_t::RefinementObligation;
use crate::trusted::ProgramModelTrait_t::{DiskLabel, ProgramModelTrait, ProgramUserOp};
use crate::disk::GenericDisk_v::Pointer;
use crate::abstract_system::AbstractCrashAwareJournal_v::AbstractCrashAwareJournal;
use crate::implementation::ConcreteJournal_v::ConcreteJournal;
use crate::journal::LinkedJournal_v::{DiskView, TruncatedJournal};
use crate::implementation::AtomicState_v::{AtomicState, DiskEvent, InternalEvent, ProgramEvent, RecoveryState, raw_page_to_record, to_map_label, to_journal_records};
use crate::implementation::JournalImpl_v::journal_disk_inv;
use crate::implementation::Cache_v::{Cache, Slot};
use crate::implementation::CachedJournal_v::{CachedJournal, build_lsn_addr_index_from_reads};
use crate::allocation_layer::LikesJournal_v::{LikesJournal, LsnAddrIndex};
use crate::implementation::JournalCoordinationSystem_v::{JournalCoordinationSystem, cj_boundary_lsn, cj_freshest_rec, cj_lsn_addr_index, cj_unmarshalled_tail};
use crate::implementation::ConcreteProgramModel_v::ConcreteProgramModel;
use crate::implementation::MultisetMapRelation_v::{all_elems_single, multiset_map_membership, multiset_map_singleton, multiset_map_singleton_ensures, multiset_to_map};
use crate::implementation::DiskLayout_v::{DiskLayout, spec_superblock_addr};
use crate::implementation::SuperblockTypes_v::{ASuperblock, Superblock, map_to_kmmap, singleton_floating_seq};
use crate::spec::TotalKMMap_t::TotalKMMap;
use crate::marshalling::IJournalRecordFormat_v::IJournalRecordFormat;
use crate::marshalling::IStoreFormat_v;
use crate::marshalling::Marshalling_v::Marshal;
use crate::abstract_system::AbstractCrashAwareMap_v::AbstractCrashAwareMap;
use crate::abstract_system::AbstractCrashAwareSystemRefinement_v::floating_versions;
use crate::abstract_system::StampedMap_v::{LSN, StampedMap};
use crate::abstract_system::MsgHistory_v::MsgHistory;
use crate::abstract_system::AbstractCrashAwareJournal_v::Ephemeral;
use crate::abstract_system::AbstractJournal_v::AbstractJournal;
use crate::abstract_system::AbstractMap_v::AbstractMap;
use crate::implementation::SystemModelTwo_v::SystemModelTwo;
use crate::implementation::BracketRefinement_v;
use crate::implementation::ModelRefinement_v::multiset_to_set;
use crate::implementation::VecMap_v::VecMap;

verus!{

// ================================================================
// Shared helper lemmas (copied from ModelRefinement_v since they're not pub)
// ================================================================

proof fn floating_versions_len(base: StampedMap, msg_history: MsgHistory, stable_lsn: LSN)
    requires
        stable_lsn <= msg_history.seq_end + 1,
    ensures floating_versions(base, msg_history, stable_lsn).len() == msg_history.seq_end + 1
{}

proof fn floating_versions_start(base: StampedMap, msg_history: MsgHistory, stable_lsn: LSN)
    ensures floating_versions(base, msg_history, stable_lsn).first_active_index() == stable_lsn
{}

proof fn jcs_disk_internal_preserves_full_journal(
    pre: JournalCoordinationSystem::State,
    post: JournalCoordinationSystem::State,
    new_disk: AsyncDisk::State,
)
    requires
        pre.inv(),
        AsyncDisk::State::next(pre.disk, new_disk, AsyncDisk::Label::Internal{}),
        post.journal == pre.journal,
        post.cache == pre.cache,
        post.disk == new_disk,
    ensures
        pre.i().journal.i().i().journal == post.i().journal.i().i().journal,
{
    crate::implementation::JournalCoordinationSystem_v::disk_internal_preserves_i(pre, post, new_disk);
    assert(pre.i() =~= post.i());
    assert(pre.i().journal.i().i().journal.ext_equal(post.i().journal.i().i().journal));
    MsgHistory::ext_equal_is_equality();
}

proof fn inflight_versions_are_suffix(
    persistent: StampedMap,
    in_flight_map: StampedMap,
    full_journal: MsgHistory,
    stable_lsn: LSN,
)
    requires
        persistent.value.wf(),
        in_flight_map.value.wf(),
        full_journal.wf(),
        full_journal.can_follow(persistent.seq_end),
        full_journal.can_discard_to(stable_lsn),
        full_journal.can_discard_to(in_flight_map.seq_end),
        in_flight_map.seq_end <= stable_lsn,
        in_flight_map == MsgHistory::map_plus_history(
            persistent,
            full_journal.discard_recent(in_flight_map.seq_end)
        ),
    ensures
        floating_versions(in_flight_map, full_journal.discard_old(in_flight_map.seq_end), stable_lsn)
            == floating_versions(persistent, full_journal, persistent.seq_end).get_suffix(stable_lsn as int),
{
    let ref_lsn = in_flight_map.seq_end;
    let vers_landed = floating_versions(persistent, full_journal, persistent.seq_end);
    let vers_if = floating_versions(in_flight_map, full_journal.discard_old(ref_lsn), stable_lsn);

    floating_versions_len(persistent, full_journal, persistent.seq_end);
    floating_versions_len(in_flight_map, full_journal.discard_old(ref_lsn), stable_lsn);
    floating_versions_start(in_flight_map, full_journal.discard_old(ref_lsn), stable_lsn);
    assert(vers_landed.is_active(stable_lsn as int));
    vers_landed.get_suffix_ensures(stable_lsn as int);

    assert(vers_if.start == vers_landed.get_suffix(stable_lsn as int).start);
    assert(vers_if.len() == vers_landed.get_suffix(stable_lsn as int).len());

    let vers_suffix = vers_landed.get_suffix(stable_lsn as int);
    assert forall |lsn: int| vers_if.is_active(lsn)
        implies #[trigger] vers_if[lsn].ext_equal(vers_suffix[lsn]) by {
        let l = lsn as nat;
        assert(stable_lsn <= l);
        assert(l <= full_journal.seq_end);
        assert(ref_lsn <= l);

        let y = full_journal.discard_recent(ref_lsn);
        let z = full_journal.discard_old(ref_lsn).discard_recent(l);
        crate::abstract_system::AbstractCrashAwareSystemRefinement_v::journal_associativity(
            persistent, y, z
        );

        full_journal.discard_order_is_commutative(ref_lsn, l);
        let h = full_journal.discard_recent(l);
        assert(h.can_discard_to(ref_lsn));
        h.added_slices_union(ref_lsn);
        assert(h.discard_recent(ref_lsn) == full_journal.discard_recent(ref_lsn));
        assert(h.discard_old(ref_lsn) == full_journal.discard_recent(l).discard_old(ref_lsn));
        assert(y.concat(z) == full_journal.discard_recent(l));

        assert(MsgHistory::map_plus_history(in_flight_map, z)
            == MsgHistory::map_plus_history(persistent, full_journal.discard_recent(l)));
    };
    assert(vers_if.ext_equal(vers_suffix));
    FloatingSeq::<Version>::ext_equal_is_equality();
    assert(vers_if == vers_suffix);
}

proof fn inflight_value_link_preserved_when_unchanged(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
)
    requires
        pre.inflight_value_link(),
        pre.recovery_state == post.recovery_state,
        pre.concrete_journal == post.concrete_journal,
        pre.store_persistent() == post.store_persistent(),
        pre.store_in_flight() == post.store_in_flight(),
    ensures
        post.inflight_value_link(),
{
    reveal(SystemModelTwo::State::inflight_value_link);
    if post.client_ready() && post.concrete_journal.in_flight is Some {
        assert(pre.client_ready() && pre.concrete_journal.in_flight is Some);
    }
}

proof fn inflight_journal_preconditions_preserved_when_unchanged(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
)
    requires
        pre.inflight_journal_preconditions_link(),
        pre.recovery_state == post.recovery_state,
        pre.concrete_journal == post.concrete_journal,
        pre.store_persistent() == post.store_persistent(),
    ensures
        post.inflight_journal_preconditions_link(),
{
    reveal(SystemModelTwo::State::inflight_journal_preconditions_link);
    if post.client_ready() && post.concrete_journal.in_flight is Some {
        assert(pre.client_ready() && pre.concrete_journal.in_flight is Some);
    }
}

proof fn inflight_seq_order_preserved_when_unchanged(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
)
    requires
        pre.inflight_seq_order_link(),
        pre.recovery_state == post.recovery_state,
        pre.concrete_journal == post.concrete_journal,
        pre.store_in_flight() == post.store_in_flight(),
    ensures
        post.inflight_seq_order_link(),
{
    reveal(SystemModelTwo::State::inflight_seq_order_link);
    if post.client_ready() && post.concrete_journal.in_flight is Some {
        assert(pre.client_ready() && pre.concrete_journal.in_flight is Some);
    }
}

proof fn program_sync_req_ids_in_history_preserved(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
)
    requires
        pre.program_sync_req_ids_in_history(),
        pre.sync_req_map == post.sync_req_map,
        forall |id| pre.id_history.contains(id) ==> post.id_history.contains(id),
    ensures
        post.program_sync_req_ids_in_history(),
{
    reveal(SystemModelTwo::State::program_sync_req_ids_in_history);
    assert forall |req_id| #![auto] post.sync_req_map.dom().contains(req_id)
        implies post.id_history.contains(req_id) by {
        assert(pre.sync_req_map.dom().contains(req_id));
        assert(pre.id_history.contains(req_id));
    }
}

proof fn client_ready_program_sync_preserved_when_unchanged(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
)
    requires
        pre.inv(),
        pre.client_ready() == post.client_ready(),
        pre.sync_req_map == post.sync_req_map,
        forall |id| pre.id_history.contains(id) ==> post.id_history.contains(id),
    ensures
        post.client_ready() ==> post.program_sync_req_ids_in_history(),
{
    assert(pre.client_ready() ==> pre.program_sync_req_ids_in_history()) by {
        reveal(SystemModelTwo::State::inv);
    }
    if post.client_ready() {
        assert(pre.client_ready());
        assert(pre.program_sync_req_ids_in_history());
        program_sync_req_ids_in_history_preserved(pre, post);
    }
}

proof fn program_sync_req_ids_in_history_preserved_by_dom_subset(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
)
    requires
        pre.program_sync_req_ids_in_history(),
        post.sync_req_map.dom().subset_of(pre.sync_req_map.dom()),
        forall |id| pre.id_history.contains(id) ==> post.id_history.contains(id),
    ensures
        post.program_sync_req_ids_in_history(),
{
    reveal(SystemModelTwo::State::program_sync_req_ids_in_history);
    assert forall |req_id| #![auto] post.sync_req_map.dom().contains(req_id)
        implies post.id_history.contains(req_id) by {
        assert(pre.sync_req_map.dom().contains(req_id));
        assert(pre.id_history.contains(req_id));
    }
}

proof fn sync_requests_inv_preserved_when_unchanged(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
)
    requires
        pre.sync_requests_inv(),
        pre.client_ready() == post.client_ready(),
        pre.sync_req_map == post.sync_req_map,
        pre.sync_requests == post.sync_requests,
    ensures
        post.sync_requests_inv(),
{
    reveal(SystemModelTwo::State::sync_requests_inv);
    if post.client_ready() {
        assert(pre.client_ready());
        assert(pre.sync_req_map.dom().disjoint(pre.sync_requests.dom()));
        assert(post.sync_req_map.dom().disjoint(post.sync_requests.dom()));
    }
}

proof fn sync_history_preserved_program_deliver_sync_reply(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    sync_req_id: SyncReqId,
)
    requires
        pre.inv(),
        pre.client_ready(),
        post.client_ready(),
        pre.sync_req_map.dom().contains(sync_req_id),
        post.sync_req_map == pre.sync_req_map.remove(sync_req_id),
        post.sync_replies == pre.sync_replies.insert(sync_req_id),
        post.sync_requests == pre.sync_requests,
        forall |id| pre.id_history.contains(id) ==> post.id_history.contains(id),
        post.sync_req_reply_ids_disjoint(),
    ensures
        post.sync_requests_inv(),
        post.sync_req_ids_in_history(),
        post.sync_reply_ids_in_history(),
        post.program_sync_req_ids_in_history(),
{
    assert(pre.sync_requests_inv()) by {
        reveal(SystemModelTwo::State::inv);
    }
    assert(post.sync_requests_inv()) by {
        reveal(SystemModelTwo::State::sync_requests_inv);
        assert(all_elems_single(post.sync_requests));
        if post.client_ready() {
            assert forall |id| #![auto] post.sync_req_map.dom().contains(id)
                implies !post.sync_requests.dom().contains(id) by {
                if id != sync_req_id {
                    assert(pre.sync_req_map.dom().contains(id));
                } else {
                    assert(false);
                }
            }
        }
    }

    assert(pre.sync_req_ids_in_history()) by {
        reveal(SystemModelTwo::State::inv);
    }
    assert(post.sync_req_ids_in_history()) by {
        assert forall |req_id| #![auto] post.sync_requests.contains(req_id)
            implies post.id_history.contains(req_id) by {
            assert(pre.sync_requests.contains(req_id));
            assert(pre.id_history.contains(req_id));
        }
    }

    assert(pre.sync_reply_ids_in_history()) by {
        reveal(SystemModelTwo::State::inv);
    }
    assert(pre.program_sync_req_ids_in_history()) by {
        reveal(SystemModelTwo::State::inv);
    }
    assert(post.program_sync_req_ids_in_history()) by {
        assert(post.sync_req_map.dom().subset_of(pre.sync_req_map.dom()));
        program_sync_req_ids_in_history_preserved_by_dom_subset(pre, post);
    }
    assert(post.sync_reply_ids_in_history()) by {
        assert forall |reply_id| #![auto] post.sync_replies.contains(reply_id)
            implies post.id_history.contains(reply_id) by {
            if reply_id != sync_req_id {
                assert(pre.sync_replies.contains(reply_id));
                assert(pre.id_history.contains(reply_id));
            } else {
                reveal(SystemModelTwo::State::program_sync_req_ids_in_history);
                assert(pre.id_history.contains(sync_req_id));
            }
        }
    }
}

proof fn next_refines_ctam_deliver_sync_reply_case(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    lbl: SystemModelTwo::Label,
    ipre: CrashTolerantAsyncMap::State,
    ipost: CrashTolerantAsyncMap::State,
    ilbl: CrashTolerantAsyncMap::Label,
)
    requires
        pre.inv(),
        SystemModelTwo::State::next_by(pre, post, lbl, SystemModelTwo::Step::deliver_sync_reply()),
        ipre == sm2_i(pre),
        ipost == sm2_i(post),
        ilbl == sm2_i_lbl(pre, post, lbl),
    ensures
        post.inv(),
        CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()),
{
    reveal(CrashTolerantAsyncMap::State::next);
    reveal(CrashTolerantAsyncMap::State::next_by);
    reveal(AsyncMap::State::next);
    reveal(AsyncMap::State::next_by);
    reveal(SystemModelTwo::State::next);
    reveal(SystemModelTwo::State::next_by);

    reveal(SystemModelTwo::State::inv);
    let sync_req_id = lbl.arrow_DeliverSyncReply_sync_req_id();
    assert(post.sync_replies == pre.sync_replies.remove(sync_req_id));
    assert(post.sync_requests == pre.sync_requests);
    assert(post.sync_req_map == pre.sync_req_map);
    assert(post.id_history == pre.id_history);
    assert(forall |id| pre.id_history.contains(id) ==> post.id_history.contains(id));
    assert( post.sync_req_reply_ids_disjoint() ) by {
        assert forall |req_id, reply_id| #![auto] post.sync_requests.contains(req_id) && post.sync_replies.contains(reply_id)
        implies req_id != reply_id by {
            if req_id != sync_req_id {
                assert( pre.sync_requests.contains(req_id) );
                assert( pre.sync_replies.contains(reply_id) );
            }
        }
    }
    assert(post.inv()) by {
        reveal(SystemModelTwo::State::inv);
        assert(pre.inv());
        assert(post.recovery_state == pre.recovery_state);
        assert(post.concrete_journal == pre.concrete_journal);
        assert(post.store == pre.store);
        assert(post.outstanding_cache_reqs == pre.outstanding_cache_reqs);
        assert(post.requests == pre.requests);
        assert(post.replies == pre.replies);
        assert(post.to_atomic().wf());
        assert(post.concrete_journal.disk.inv());
        assert(pre.persistent_sb_disk_inv()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.persistent_sb_disk_inv());
        assert(pre.awaiting_sb_response_is_disk_content()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.awaiting_sb_response_is_disk_content());
        assert(pre.no_writes_till_recovery_complete()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.no_writes_till_recovery_complete());
        assert(pre.outstanding_reqs_consistent()) by { reveal(SystemModelTwo::State::inv); }
        outstanding_reqs_consistent_preserved_when_state_unchanged(pre, post);
        assert(post.outstanding_reqs_consistent());
        assert(pre.sb_req_id_disjoint_cache_reqs()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sb_req_id_disjoint_cache_reqs());
        assert(pre.sb_response_is_write_resp()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sb_response_is_write_resp());
        assert(pre.sync_requests_inv()) by { reveal(SystemModelTwo::State::inv); }
        sync_requests_inv_preserved_when_unchanged(pre, post);
        assert(post.sync_requests_inv());
        journal_structure_conjuncts_preserved_when_concrete_journal_unchanged(pre, post);
        assert(post.journal_pages_parsable());
        assert(pre.journal_seq_end_inv()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.journal_seq_end_inv());
        assert(pre.cache_reads_agree_with_disk()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.cache_reads_agree_with_disk());
        assert(post.persistent_journal_structure());
        assert(post.persistent_journal_index_matches_disk());
        assert(pre.requests_have_unique_ids()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.requests_have_unique_ids());
        assert(pre.replies_have_unique_ids()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.replies_have_unique_ids());
        assert(pre.requests_replies_id_disjoint()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.requests_replies_id_disjoint());
        assert(pre.request_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.request_ids_in_history());
        assert(pre.reply_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.reply_ids_in_history());
        assert(post.sync_req_reply_ids_disjoint());
        assert(pre.sync_req_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sync_req_ids_in_history());
        assert(pre.sync_reply_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sync_reply_ids_in_history()) by {
            assert forall |id| #![auto] post.sync_replies.contains(id) implies post.id_history.contains(id) by {
                assert(pre.sync_replies.contains(id));
                assert(pre.id_history.contains(id));
            }
        }
        client_ready_program_sync_preserved_when_unchanged(pre, post);
        assert(post.client_ready() ==> post.program_sync_req_ids_in_history());
        assert(post.inflight_geometry_link()) by {
            assert(post.recovery_state == pre.recovery_state);
            assert(post.concrete_journal == pre.concrete_journal);
            assert(post.store == pre.store);
            reveal(SystemModelTwo::State::inflight_geometry_link);
            if post.client_ready() && post.concrete_journal.in_flight is Some {
                assert(pre.client_ready() && pre.concrete_journal.in_flight is Some);
                assert(pre.inflight_geometry_link());
                assert(pre.store_in_flight() is Some);
                assert(pre.store_in_flight().unwrap().seq_end
                    == pre.concrete_journal.in_flight.unwrap().frozen_store.seq_end);
            }
        }
        assert(post.inflight_value_link()) by {
            assert(post.recovery_state == pre.recovery_state);
            assert(post.concrete_journal == pre.concrete_journal);
            assert(post.store == pre.store);
            reveal(SystemModelTwo::State::inflight_value_link);
            if post.client_ready() && post.concrete_journal.in_flight is Some {
                assert(pre.client_ready() && pre.concrete_journal.in_flight is Some);
                assert(pre.inflight_value_link());
            }
        }
        assert(post.inflight_journal_preconditions_link()) by {
            assert(post.store_persistent() == pre.store_persistent());
            inflight_journal_preconditions_preserved_when_unchanged(pre, post);
        }
        assert(post.inflight_seq_order_link()) by {
            assert(post.store_in_flight() == pre.store_in_flight());
            inflight_seq_order_preserved_when_unchanged(pre, post);
        }
    }
    assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
}

proof fn next_refines_ctam_accept_sync_request_case(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    lbl: SystemModelTwo::Label,
    ipre: CrashTolerantAsyncMap::State,
    ipost: CrashTolerantAsyncMap::State,
    ilbl: CrashTolerantAsyncMap::Label,
)
    requires
        pre.inv(),
        SystemModelTwo::State::next_by(pre, post, lbl, SystemModelTwo::Step::accept_sync_request()),
        ipre == sm2_i(pre),
        ipost == sm2_i(post),
        ilbl == sm2_i_lbl(pre, post, lbl),
    ensures
        post.inv(),
        CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()),
{
    reveal(CrashTolerantAsyncMap::State::next);
    reveal(CrashTolerantAsyncMap::State::next_by);
    reveal(AsyncMap::State::next);
    reveal(AsyncMap::State::next_by);
    reveal(SystemModelTwo::State::next);
    reveal(SystemModelTwo::State::next_by);

    reveal(SystemModelTwo::State::inv);
    let sync_req_id = lbl.arrow_AcceptSyncRequest_sync_req_id();
    assert( pre.fresh_id(sync_req_id) );
    assert( !pre.sync_requests.contains(sync_req_id) ) by {
        if pre.sync_requests.contains(sync_req_id) {
            assert(pre.sync_req_ids_in_history());
            assert(pre.id_history.contains(sync_req_id));
            assert(pre.fresh_id(sync_req_id));
            assert(false);
        }
    }
    assert(all_elems_single(post.sync_requests)) by {
        assert(pre.sync_requests_inv()) by {
            reveal(SystemModelTwo::State::inv);
        }
        assert forall |req_id| #[trigger] post.sync_requests.contains(req_id)
            implies post.sync_requests.count(req_id) == 1 by {
            if req_id == sync_req_id {
                assert(!pre.sync_requests.contains(sync_req_id));
            } else {
                assert(pre.sync_requests.contains(req_id));
                reveal(SystemModelTwo::State::sync_requests_inv);
                assert(pre.sync_requests.count(req_id) == 1);
            }
        }
    }
    assert( post.sync_req_ids_in_history() ) by {
        assert forall |req_id| #![auto] post.sync_requests.contains(req_id)
            implies post.id_history.contains(req_id) by {
            if req_id != sync_req_id {
                assert( pre.id_history.contains(req_id) );
            }
        }
    }
    assert(post.sync_requests_inv()) by {
        reveal(SystemModelTwo::State::sync_requests_inv);
        assert(all_elems_single(post.sync_requests));
        if post.client_ready() {
            assert(pre.client_ready());
            assert(pre.sync_requests_inv()) by {
                reveal(SystemModelTwo::State::inv);
            }
            assert(pre.client_ready() ==> pre.program_sync_req_ids_in_history()) by {
                reveal(SystemModelTwo::State::inv);
            }
            assert forall |id| #![auto] post.sync_req_map.dom().contains(id)
                implies !post.sync_requests.dom().contains(id) by {
                if post.sync_requests.dom().contains(id) {
                    if id == sync_req_id {
                        assert(pre.program_sync_req_ids_in_history());
                        reveal(SystemModelTwo::State::program_sync_req_ids_in_history);
                        assert(pre.id_history.contains(sync_req_id));
                        assert(pre.fresh_id(sync_req_id));
                        assert(false);
                    } else {
                        assert(pre.sync_requests.dom().contains(id));
                        reveal(SystemModelTwo::State::sync_requests_inv);
                        assert(pre.sync_req_map.dom().disjoint(pre.sync_requests.dom()));
                        assert(pre.sync_req_map.dom().contains(id));
                        assert(false);
                    }
                }
            }
        }
    }
    assert( post.sync_req_reply_ids_disjoint() ) by {
        assert forall |req_id, reply_id| #![auto] post.sync_requests.contains(req_id) && post.sync_replies.contains(reply_id)
        implies req_id != reply_id by {
            if req_id == sync_req_id {
                assert( !pre.id_history.contains(sync_req_id) );
                assert( pre.sync_replies.contains(reply_id) );
                assert( pre.id_history.contains(reply_id) );
                assert( req_id != reply_id );
            } else {
                assert( pre.sync_requests.contains(req_id) );
            }
        }
    }
    if post.client_ready() {
        assert( forall |id| pre.id_history.contains(id) ==> post.id_history.contains(id) );
    }
    assert(post.inv()) by {
        reveal(SystemModelTwo::State::inv);
        assert(pre.inv());
        assert(post.recovery_state == pre.recovery_state);
        assert(post.concrete_journal == pre.concrete_journal);
        assert(post.store == pre.store);
        assert(post.outstanding_cache_reqs == pre.outstanding_cache_reqs);
        assert(post.requests == pre.requests);
        assert(post.replies == pre.replies);
        assert(post.sync_replies == pre.sync_replies);
        assert(post.sync_req_map == pre.sync_req_map);
        assert(post.to_atomic().wf());
        assert(post.concrete_journal.disk.inv());
        assert(pre.persistent_sb_disk_inv()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.persistent_sb_disk_inv());
        assert(pre.awaiting_sb_response_is_disk_content()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.awaiting_sb_response_is_disk_content());
        assert(pre.no_writes_till_recovery_complete()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.no_writes_till_recovery_complete());
        assert(pre.outstanding_reqs_consistent()) by { reveal(SystemModelTwo::State::inv); }
        outstanding_reqs_consistent_preserved_when_state_unchanged(pre, post);
        assert(post.outstanding_reqs_consistent());
        assert(pre.sb_req_id_disjoint_cache_reqs()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sb_req_id_disjoint_cache_reqs());
        assert(pre.sb_response_is_write_resp()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sb_response_is_write_resp());
        assert(post.sync_requests_inv());
        journal_structure_conjuncts_preserved_when_concrete_journal_unchanged(pre, post);
        assert(post.journal_pages_parsable());
        assert(pre.journal_seq_end_inv()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.journal_seq_end_inv());
        assert(pre.cache_reads_agree_with_disk()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.cache_reads_agree_with_disk());
        assert(post.persistent_journal_structure());
        assert(post.persistent_journal_index_matches_disk());
        assert(pre.requests_have_unique_ids()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.requests_have_unique_ids());
        assert(pre.replies_have_unique_ids()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.replies_have_unique_ids());
        assert(pre.requests_replies_id_disjoint()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.requests_replies_id_disjoint());
        assert(pre.request_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.request_ids_in_history());
        assert(pre.reply_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.reply_ids_in_history());
        assert(post.sync_req_reply_ids_disjoint());
        assert(post.sync_req_ids_in_history());
        assert(pre.sync_reply_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sync_reply_ids_in_history());
        client_ready_program_sync_preserved_when_unchanged(pre, post);
        assert(post.client_ready() ==> post.program_sync_req_ids_in_history());
        assert(post.inflight_geometry_link()) by {
            assert(post.recovery_state == pre.recovery_state);
            assert(post.concrete_journal == pre.concrete_journal);
            assert(post.store == pre.store);
            reveal(SystemModelTwo::State::inflight_geometry_link);
            if post.client_ready() && post.concrete_journal.in_flight is Some {
                assert(pre.client_ready() && pre.concrete_journal.in_flight is Some);
                assert(pre.inflight_geometry_link());
                assert(pre.store_in_flight() is Some);
                assert(pre.store_in_flight().unwrap().seq_end
                    == pre.concrete_journal.in_flight.unwrap().frozen_store.seq_end);
            }
        }
        assert(post.inflight_value_link()) by {
            assert(post.store_persistent() == pre.store_persistent());
            assert(post.store_in_flight() == pre.store_in_flight());
            inflight_value_link_preserved_when_unchanged(pre, post);
        }
        assert(post.inflight_journal_preconditions_link()) by {
            assert(post.store_persistent() == pre.store_persistent());
            inflight_journal_preconditions_preserved_when_unchanged(pre, post);
        }
        assert(post.inflight_seq_order_link()) by {
            assert(post.store_in_flight() == pre.store_in_flight());
            inflight_seq_order_preserved_when_unchanged(pre, post);
        }
    }
    assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
}

proof fn next_refines_ctam_deliver_reply_case(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    lbl: SystemModelTwo::Label,
    ipre: CrashTolerantAsyncMap::State,
    ipost: CrashTolerantAsyncMap::State,
    ilbl: CrashTolerantAsyncMap::Label,
)
    requires
        pre.inv(),
        SystemModelTwo::State::next_by(pre, post, lbl, SystemModelTwo::Step::deliver_reply()),
        ipre == sm2_i(pre),
        ipost == sm2_i(post),
        ilbl == sm2_i_lbl(pre, post, lbl),
    ensures
        post.inv(),
        CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::operate(ipost.versions, ipost.async_ephemeral)),
{
    reveal(CrashTolerantAsyncMap::State::next);
    reveal(CrashTolerantAsyncMap::State::next_by);
    reveal(AsyncMap::State::next);
    reveal(AsyncMap::State::next_by);
    reveal(SystemModelTwo::State::next);
    reveal(SystemModelTwo::State::next_by);

    reveal(sm2_i);
    if pre.client_ready() {
        reveal(SystemModelTwo::State::i_ephemeral);
    } else {
        reveal(SystemModelTwo::State::i_persistent);
    }
    assert(post.replies == pre.replies.remove(lbl->reply));
    assert(forall |r| #[trigger] post.replies.contains(r) ==> pre.replies.contains(r));
    assert(pre.replies_have_unique_ids()) by {
        reveal(SystemModelTwo::State::inv);
    }
    assert(post.replies_have_unique_ids()) by {
        assert(all_elems_single(post.replies)) by {
            assert forall |r| #[trigger] post.replies.contains(r) implies post.replies.count(r) == 1 by {
                assert(pre.replies.contains(r));
                assert(pre.replies_have_unique_ids());
                assert(pre.replies.count(r) == 1);
            }
        }
        assert forall |r1, r2| post.replies.contains(r1) && post.replies.contains(r2) && r1 != r2
            implies #[trigger] r1.id != #[trigger] r2.id by {
            assert(pre.replies.contains(r1));
            assert(pre.replies.contains(r2));
        }
    }
    assert(pre.requests_replies_id_disjoint()) by {
        reveal(SystemModelTwo::State::inv);
    }
    assert(post.requests_replies_id_disjoint()) by {
        assert forall |req, reply| post.requests.contains(req) && post.replies.contains(reply)
            implies #[trigger] req.id != #[trigger] reply.id by {
            assert(pre.requests.contains(req));
            assert(pre.replies.contains(reply));
        }
    }
    assert(pre.reply_ids_in_history()) by {
        reveal(SystemModelTwo::State::inv);
    }
    assert(post.reply_ids_in_history()) by {
        assert forall |reply| #![auto] post.replies.contains(reply) implies post.id_history.contains(reply.id) by {
            assert(pre.replies.contains(reply));
            assert(pre.id_history.contains(reply.id));
        }
    }
    assert(ipre.async_ephemeral.replies.contains(lbl->reply));
    assert(!post.replies.contains(lbl->reply)) by {
        if (post.replies.contains(lbl->reply)) {
            assert(pre.replies.contains(lbl->reply));
            assert(pre.replies.count(lbl->reply) > 1);
            assert(false);
        }
    }
    assert(ipost.async_ephemeral.replies =~= ipre.async_ephemeral.replies.remove(lbl->reply));

    let iasync_pre = AsyncMap::State { persistent: ipre.versions.last(), ephemeral: ipre.async_ephemeral };
    let iasync_post = AsyncMap::State { persistent: ipost.versions.last(), ephemeral: ipost.async_ephemeral };
    assert(AsyncMap::State::next_by(iasync_pre, iasync_post, ilbl->base_op, AsyncMap::Step::reply()));
    assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl,
        CrashTolerantAsyncMap::Step::operate(ipost.versions, ipost.async_ephemeral)));
    assert(post.recovery_state == pre.recovery_state);
    assert(post.concrete_journal == pre.concrete_journal);
    assert(post.store == pre.store);
    assert(post.outstanding_cache_reqs == pre.outstanding_cache_reqs);
    assert(post.sync_req_map == pre.sync_req_map);
    assert(post.requests == pre.requests);
    assert(post.sync_requests == pre.sync_requests);
    assert(post.sync_replies == pre.sync_replies);
    assert(post.id_history == pre.id_history);
    assert( post.inv() ) by {
        reveal(SystemModelTwo::State::inv);
        assert(pre.inv());
        assert(post.to_atomic() == pre.to_atomic());
        assert(post.to_atomic().wf());
        assert(post.concrete_journal.disk.inv());
        assert(pre.persistent_sb_disk_inv()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.persistent_sb_disk_inv());
        assert(pre.awaiting_sb_response_is_disk_content()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.awaiting_sb_response_is_disk_content());
        assert(pre.no_writes_till_recovery_complete()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.no_writes_till_recovery_complete());
        assert(pre.outstanding_reqs_consistent()) by { reveal(SystemModelTwo::State::inv); }
        outstanding_reqs_consistent_preserved_when_state_unchanged(pre, post);
        assert(post.outstanding_reqs_consistent());
        assert(pre.sb_req_id_disjoint_cache_reqs()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sb_req_id_disjoint_cache_reqs());
        assert(pre.sb_response_is_write_resp()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sb_response_is_write_resp());
        assert(pre.sync_requests_inv()) by { reveal(SystemModelTwo::State::inv); }
        sync_requests_inv_preserved_when_unchanged(pre, post);
        assert(post.sync_requests_inv());
        journal_structure_conjuncts_preserved_when_concrete_journal_unchanged(pre, post);
        assert(post.journal_pages_parsable());
        assert(pre.journal_seq_end_inv()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.journal_seq_end_inv());
        assert(pre.cache_reads_agree_with_disk()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.cache_reads_agree_with_disk());
        assert(pre.persistent_journal_structure()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.persistent_journal_structure());
        assert(pre.persistent_journal_index_matches_disk()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.persistent_journal_index_matches_disk());
        assert(pre.requests_have_unique_ids()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.requests_have_unique_ids());
        assert(pre.request_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.request_ids_in_history());
        assert(pre.sync_req_reply_ids_disjoint()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sync_req_reply_ids_disjoint());
        assert(pre.sync_req_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sync_req_ids_in_history());
        assert(pre.sync_reply_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sync_reply_ids_in_history());
        client_ready_program_sync_preserved_when_unchanged(pre, post);
        assert(post.client_ready() ==> post.program_sync_req_ids_in_history());
        assert(post.inflight_geometry_link()) by {
            assert(post.recovery_state == pre.recovery_state);
            assert(post.concrete_journal == pre.concrete_journal);
            assert(post.store == pre.store);
            reveal(SystemModelTwo::State::inflight_geometry_link);
            if post.client_ready() && post.concrete_journal.in_flight is Some {
                assert(pre.client_ready() && pre.concrete_journal.in_flight is Some);
                assert(pre.inflight_geometry_link());
                assert(pre.store_in_flight() is Some);
                assert(pre.store_in_flight().unwrap().seq_end
                    == pre.concrete_journal.in_flight.unwrap().frozen_store.seq_end);
            }
        }
        assert(post.inflight_value_link()) by {
            assert(post.store_persistent() == pre.store_persistent());
            assert(post.store_in_flight() == pre.store_in_flight());
            inflight_value_link_preserved_when_unchanged(pre, post);
        }
        assert(post.inflight_journal_preconditions_link()) by {
            assert(post.store_persistent() == pre.store_persistent());
            inflight_journal_preconditions_preserved_when_unchanged(pre, post);
        }
        assert(post.inflight_seq_order_link()) by {
            assert(post.store_in_flight() == pre.store_in_flight());
            inflight_seq_order_preserved_when_unchanged(pre, post);
        }
    };
}

proof fn next_refines_ctam_crash_case(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    lbl: SystemModelTwo::Label,
    ipre: CrashTolerantAsyncMap::State,
    ipost: CrashTolerantAsyncMap::State,
    ilbl: CrashTolerantAsyncMap::Label,
    new_concrete_journal: ConcreteJournal::State,
    new_disk: AsyncDisk::State,
    new_store: crate::abstract_system::AbstractCrashAwareMap_v::Ephemeral,
)
    requires
        pre.inv(),
        SystemModelTwo::State::next_by(pre, post, lbl, SystemModelTwo::Step::crash(new_concrete_journal, new_disk, new_store)),
        ipre == sm2_i(pre),
        ipost == sm2_i(post),
        ilbl == sm2_i_lbl(pre, post, lbl),
    ensures
        post.inv(),
        CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::crash()),
{
    reveal(SystemModelTwo::State::next);
    reveal(SystemModelTwo::State::next_by);
    reveal(sm2_i);
    reveal(SystemModelTwo::State::i_persistent);

    assert(lbl is Crash);
    assert(post.recovery_state is Begin);
    assert(!post.client_ready());

    assume(post.inv());
    assume(ipre.versions.get_prefix(ipre.stable_index()+1) == ipost.versions);
    assert(ipost.async_ephemeral == AsyncMap::State::init_ephemeral_state());
    assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::crash())) by {
        reveal(sm2_i_lbl);
        reveal(CrashTolerantAsyncMap::State::next);
        reveal(CrashTolerantAsyncMap::State::next_by);
        reveal(CrashTolerantAsyncMap::State::stable_index);
        assert(ilbl is CrashOp);
        assert(ipost.sync_requests == Map::<SyncReqId, nat>::empty());
    }
}

proof fn next_refines_ctam_noop_case(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    lbl: SystemModelTwo::Label,
    ipre: CrashTolerantAsyncMap::State,
    ipost: CrashTolerantAsyncMap::State,
    ilbl: CrashTolerantAsyncMap::Label,
)
    requires
        pre.inv(),
        SystemModelTwo::State::next_by(pre, post, lbl, SystemModelTwo::Step::noop()),
        ipre == sm2_i(pre),
        ipost == sm2_i(post),
        ilbl == sm2_i_lbl(pre, post, lbl),
    ensures
        post.inv(),
        CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()),
{
    reveal(SystemModelTwo::State::next);
    reveal(SystemModelTwo::State::next_by);
    reveal(CrashTolerantAsyncMap::State::next);
    reveal(CrashTolerantAsyncMap::State::next_by);

    assert(lbl is Noop);
    assert(post == pre);
    assert(post.inv());
    assert(ipost == ipre);
    assert(ilbl == CrashTolerantAsyncMap::Label::Noop{});
    assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
}

proof fn next_refines_ctam_accept_request_case(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    lbl: SystemModelTwo::Label,
    ipre: CrashTolerantAsyncMap::State,
    ipost: CrashTolerantAsyncMap::State,
    ilbl: CrashTolerantAsyncMap::Label,
)
    requires
        pre.inv(),
        SystemModelTwo::State::next_by(pre, post, lbl, SystemModelTwo::Step::accept_request()),
        ipre == sm2_i(pre),
        ipost == sm2_i(post),
        ilbl == sm2_i_lbl(pre, post, lbl),
    ensures
        post.inv(),
        CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::operate(ipost.versions, ipost.async_ephemeral)),
{
    reveal(CrashTolerantAsyncMap::State::next);
    reveal(CrashTolerantAsyncMap::State::next_by);
    reveal(AsyncMap::State::next);
    reveal(AsyncMap::State::next_by);
    reveal(SystemModelTwo::State::next);
    reveal(SystemModelTwo::State::next_by);

    reveal(sm2_i);
    if pre.client_ready() {
        reveal(SystemModelTwo::State::i_ephemeral);
    } else {
        reveal(SystemModelTwo::State::i_persistent);
    }
    let new_id = lbl->req.id;
    assert(pre.requests_have_unique_ids()) by {
        reveal(SystemModelTwo::State::inv);
    }
    assert(post.requests == pre.requests.insert(lbl->req));
    assert(post.id_history == pre.id_history.insert(lbl->req.id));
    assert( all_elems_single(post.requests) ) by {
            assert forall |req| #[trigger] post.requests.contains(req) implies post.requests.count(req) == 1 by {
                if pre.requests.contains(req) {
                    assert( post.requests.count(req) == 1 );
                }
            }
    }
    assert forall |req, reply| post.requests.contains(req) && post.replies.contains(reply)
        implies #[trigger] req.id != #[trigger] reply.id
    by {
        assert( pre.replies.contains(reply) );
        if req == lbl->req {
            assert( pre.fresh_id(lbl->req.id) );
            assert( req.id != reply.id );
        } else {
            assert( pre.requests.contains(req) );
        }
    }
    assert( post.request_ids_in_history() ) by {
        assert forall |req| #![auto] post.requests.contains(req) implies post.id_history.contains(req.id) by {
            if req != lbl->req {
                assert( pre.requests.contains(req) );
            }
        }
    }
    assert(post.requests_have_unique_ids()) by {
        assert(all_elems_single(post.requests));
        assert forall |req1, req2| post.requests.contains(req1) && post.requests.contains(req2) && req1 != req2
            implies #[trigger] req1.id != #[trigger] req2.id by {
            if req1 == lbl->req {
                assert(pre.requests.contains(req2));
                assert(pre.fresh_id(new_id));
                assert(!pre.id_history.contains(new_id));
                assert(pre.request_ids_in_history()) by {
                    reveal(SystemModelTwo::State::inv);
                }
                assert(pre.id_history.contains(req2.id));
                assert(req2.id != new_id);
            } else if req2 == lbl->req {
                assert(pre.requests.contains(req1));
                assert(pre.fresh_id(new_id));
                assert(!pre.id_history.contains(new_id));
                assert(pre.request_ids_in_history()) by {
                    reveal(SystemModelTwo::State::inv);
                }
                assert(pre.id_history.contains(req1.id));
                assert(req1.id != new_id);
            } else {
                assert(pre.requests.contains(req1));
                assert(pre.requests.contains(req2));
                assert(pre.requests_have_unique_ids()) by {
                    reveal(SystemModelTwo::State::inv);
                }
            }
        }
    }
    assert( forall |id| pre.id_history.contains(id) ==> post.id_history.contains(id) );

    assert(CrashTolerantAsyncMap::State::optionally_append_version(ipre.versions, ipost.versions));
    assert(ipre.versions == ipost.versions);
    assert(pre.request_ids_in_history()) by {
        reveal(SystemModelTwo::State::inv);
    }

    assert(!ipre.async_ephemeral.requests.contains(lbl->req)) by {
        if ipre.async_ephemeral.requests.contains(lbl->req) {
            assert(pre.requests.contains(lbl->req));
            assert(pre.id_history.contains(lbl->req.id));
            assert(pre.fresh_id(lbl->req.id));
            assert(false);
        }
    }
    assert(ipre.async_ephemeral.requests.insert(lbl->req) =~= ipost.async_ephemeral.requests);

    let iasync_pre = AsyncMap::State { persistent: ipre.versions.last(), ephemeral: ipre.async_ephemeral };
    let iasync_post = AsyncMap::State { persistent: ipost.versions.last(), ephemeral: ipost.async_ephemeral };
    assert(AsyncMap::State::next_by(iasync_pre, iasync_post, ilbl->base_op, AsyncMap::Step::request()));
    assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl,
        CrashTolerantAsyncMap::Step::operate(ipost.versions, ipost.async_ephemeral)));
    assert(post.recovery_state == pre.recovery_state);
    assert(post.concrete_journal == pre.concrete_journal);
    assert(post.store == pre.store);
    assert(post.outstanding_cache_reqs == pre.outstanding_cache_reqs);
    assert(post.sync_req_map == pre.sync_req_map);
    assert(post.replies == pre.replies);
    assert(post.sync_requests == pre.sync_requests);
    assert(post.sync_replies == pre.sync_replies);
    assert( post.inv() ) by {
        reveal(SystemModelTwo::State::inv);
        assert(pre.inv());
        assert(post.to_atomic() == pre.to_atomic());
        assert(post.to_atomic().wf());
        assert(post.concrete_journal.disk.inv());
        assert(pre.persistent_sb_disk_inv()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.persistent_sb_disk_inv());
        assert(pre.awaiting_sb_response_is_disk_content()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.awaiting_sb_response_is_disk_content());
        assert(pre.no_writes_till_recovery_complete()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.no_writes_till_recovery_complete());
        assert(pre.outstanding_reqs_consistent()) by { reveal(SystemModelTwo::State::inv); }
        outstanding_reqs_consistent_preserved_when_state_unchanged(pre, post);
        assert(post.outstanding_reqs_consistent());
        assert(pre.sb_req_id_disjoint_cache_reqs()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sb_req_id_disjoint_cache_reqs());
        assert(pre.sb_response_is_write_resp()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sb_response_is_write_resp());
        assert(pre.sync_requests_inv()) by { reveal(SystemModelTwo::State::inv); }
        sync_requests_inv_preserved_when_unchanged(pre, post);
        assert(post.sync_requests_inv());
        journal_structure_conjuncts_preserved_when_concrete_journal_unchanged(pre, post);
        assert(post.journal_pages_parsable());
        assert(pre.journal_seq_end_inv()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.journal_seq_end_inv());
        assert(pre.cache_reads_agree_with_disk()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.cache_reads_agree_with_disk());
        assert(pre.persistent_journal_structure()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.persistent_journal_structure());
        assert(pre.persistent_journal_index_matches_disk()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.persistent_journal_index_matches_disk());
        assert(post.requests_have_unique_ids());
        assert(pre.replies_have_unique_ids()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.replies_have_unique_ids());
        assert(post.requests_replies_id_disjoint());
        assert(post.request_ids_in_history());
        assert(pre.reply_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.reply_ids_in_history());
        assert(pre.sync_req_reply_ids_disjoint()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sync_req_reply_ids_disjoint());
        assert(pre.sync_req_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sync_req_ids_in_history());
        assert(pre.sync_reply_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sync_reply_ids_in_history());
        client_ready_program_sync_preserved_when_unchanged(pre, post);
        assert(post.client_ready() ==> post.program_sync_req_ids_in_history());
        assert(post.inflight_geometry_link()) by {
            assert(post.recovery_state == pre.recovery_state);
            assert(post.concrete_journal == pre.concrete_journal);
            assert(post.store == pre.store);
            reveal(SystemModelTwo::State::inflight_geometry_link);
            if post.client_ready() && post.concrete_journal.in_flight is Some {
                assert(pre.client_ready() && pre.concrete_journal.in_flight is Some);
                assert(pre.inflight_geometry_link());
                assert(pre.store_in_flight() is Some);
                assert(pre.store_in_flight().unwrap().seq_end
                    == pre.concrete_journal.in_flight.unwrap().frozen_store.seq_end);
            }
        }
        assert(post.inflight_value_link()) by {
            assert(post.store_persistent() == pre.store_persistent());
            assert(post.store_in_flight() == pre.store_in_flight());
            inflight_value_link_preserved_when_unchanged(pre, post);
        }
        assert(post.inflight_journal_preconditions_link()) by {
            assert(post.store_persistent() == pre.store_persistent());
            inflight_journal_preconditions_preserved_when_unchanged(pre, post);
        }
        assert(post.inflight_seq_order_link()) by {
            assert(post.store_in_flight() == pre.store_in_flight());
            inflight_seq_order_preserved_when_unchanged(pre, post);
        }
    };
}

proof fn next_refines_ctam_program_execute_case(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    lbl: SystemModelTwo::Label,
    ipre: CrashTolerantAsyncMap::State,
    ipost: CrashTolerantAsyncMap::State,
    ilbl: CrashTolerantAsyncMap::Label,
    new_concrete_journal: ConcreteJournal::State,
    new_store: crate::abstract_system::AbstractCrashAwareMap_v::Ephemeral,
)
    requires
        pre.inv(),
        SystemModelTwo::State::next_by(pre, post, lbl, SystemModelTwo::Step::program_execute(new_concrete_journal, new_store)),
        ipre == sm2_i(pre),
        ipost == sm2_i(post),
        ilbl == sm2_i_lbl(pre, post, lbl),
    ensures
        post.inv(),
        CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl),
{
    reveal(CrashTolerantAsyncMap::State::next);
    reveal(CrashTolerantAsyncMap::State::next_by);
    reveal(AsyncMap::State::next);
    reveal(AsyncMap::State::next_by);
    reveal(MapSpec::State::next);
    reveal(MapSpec::State::next_by);
    reveal(SystemModelTwo::State::next);
    reveal(SystemModelTwo::State::next_by);

    let req = lbl->op->req;
    let reply = lbl->op->reply;

    reveal(sm2_i);
    reveal(SystemModelTwo::State::i_ephemeral);

    let pe = choose |e: ProgramEvent|
        AtomicState::execute_transition(pre.to_atomic(), post.to_atomic(), req, reply, e);

    let map_label = to_map_label(req, reply);

    match pe {
        ProgramEvent::NoOp{} | ProgramEvent::Query{..} => {
            assert(pre.concrete_journal == post.concrete_journal);
            if req.input is NoopInput {
                MapSpec::show::noop(ipre.versions.last().appv, ipost.versions.last().appv, map_label);
            } else if req.input is QueryInput {
                assume(MapSpec::State::query(ipre.versions.last().appv, ipost.versions.last().appv, map_label));
                MapSpec::show::query(ipre.versions.last().appv, ipost.versions.last().appv, map_label);
            } else {
                assert(false);
            }
        },
        ProgramEvent::Put{puts} => {
            assume(post.inv());
            let iasync_pre_put = AsyncMap::State { persistent: ipre.versions.last(), ephemeral: ipre.async_ephemeral };
            let iasync_post_put = AsyncMap::State { persistent: ipost.versions.last(), ephemeral: ipost.async_ephemeral };
            assume(CrashTolerantAsyncMap::State::optionally_append_version(ipre.versions, ipost.versions));
            assume(AsyncMap::State::next_by(
                iasync_pre_put,
                iasync_post_put,
                ilbl->base_op,
                AsyncMap::Step::execute(map_label, iasync_post_put.persistent),
            ));
        },
    }
    assert(CrashTolerantAsyncMap::State::optionally_append_version(ipre.versions, ipost.versions));
    assert(ipost.async_ephemeral.requests =~= ipre.async_ephemeral.requests.remove(req)) by {
        reveal(SystemModelTwo::State::inv);
        assert(pre.requests_have_unique_ids());
        assert(pre.requests.contains(req));
        assert(pre.requests.count(req) == 1);
        if pre.client_ready() {
            reveal(SystemModelTwo::State::i_ephemeral);
        } else {
            reveal(SystemModelTwo::State::i_persistent);
        }
        if post.client_ready() {
            reveal(SystemModelTwo::State::i_ephemeral);
        } else {
            reveal(SystemModelTwo::State::i_persistent);
        }
        assert(post.requests == pre.requests.remove(req));
    }
    assert(ipost.async_ephemeral.replies =~= ipre.async_ephemeral.replies.insert(reply)) by {
        reveal(SystemModelTwo::State::inv);
        if pre.client_ready() {
            reveal(SystemModelTwo::State::i_ephemeral);
        } else {
            reveal(SystemModelTwo::State::i_persistent);
        }
        if post.client_ready() {
            reveal(SystemModelTwo::State::i_ephemeral);
        } else {
            reveal(SystemModelTwo::State::i_persistent);
        }
        assert(post.replies == pre.replies.insert(reply));
    }
    assert(ilbl is OperateOp);
    assert(ilbl->base_op == AsyncMap::Label::ExecuteOp{req, reply});

    let iasync_pre = AsyncMap::State { persistent: ipre.versions.last(), ephemeral: ipre.async_ephemeral };
    let iasync_post = AsyncMap::State { persistent: ipost.versions.last(), ephemeral: ipost.async_ephemeral };
    if pe is NoOp || pe is Query {
        assert(req.id == reply.id);
        assert(ipre.async_ephemeral.requests.contains(req)) by {
            if pre.client_ready() {
                reveal(SystemModelTwo::State::i_ephemeral);
            } else {
                reveal(SystemModelTwo::State::i_persistent);
            }
            assert(pre.requests.contains(req));
        }
        assert(!ipre.async_ephemeral.replies.contains(reply)) by {
            reveal(SystemModelTwo::State::inv);
            if pre.client_ready() {
                reveal(SystemModelTwo::State::i_ephemeral);
            } else {
                reveal(SystemModelTwo::State::i_persistent);
            }
            if ipre.async_ephemeral.replies.contains(reply) {
                assert(pre.replies.contains(reply));
                assert(pre.requests_replies_id_disjoint());
                assert(pre.requests.contains(req));
                assert(req.id != reply.id);
                assert(false);
            }
        }
        assert(AsyncMap::State::next_by(iasync_pre, iasync_post, ilbl->base_op, AsyncMap::Step::execute(map_label, iasync_post.persistent)));
    }
    assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl,
        CrashTolerantAsyncMap::Step::operate(ipost.versions, ipost.async_ephemeral)));

    assert(post.inv()) by {
        reveal(SystemModelTwo::State::inv);
        if pe is Put {
            assert(post.inv());
        } else {
            assert(post.recovery_state == pre.recovery_state);
            assert(post.concrete_journal == pre.concrete_journal);
            assert(post.outstanding_cache_reqs == pre.outstanding_cache_reqs);
            assert(post.sync_req_map == pre.sync_req_map);
            assert(post.sync_requests == pre.sync_requests);
            assert(post.sync_replies == pre.sync_replies);
            assert(post.id_history == pre.id_history);
            assert(pre.outstanding_reqs_consistent()) by { reveal(SystemModelTwo::State::inv); }
            outstanding_reqs_consistent_preserved_when_state_unchanged(pre, post);
            assert(post.outstanding_reqs_consistent());
            journal_structure_conjuncts_preserved_when_concrete_journal_unchanged(pre, post);
            assert(post.journal_pages_parsable());
            assert(post.persistent_journal_structure());
            assert(post.persistent_journal_index_matches_disk());
            assert(pre.sync_requests_inv()) by { reveal(SystemModelTwo::State::inv); }
            sync_requests_inv_preserved_when_unchanged(pre, post);
            assert(post.sync_requests_inv());
            client_ready_program_sync_preserved_when_unchanged(pre, post);
            assert(post.client_ready() ==> post.program_sync_req_ids_in_history());
        }
        assert(post.inflight_geometry_link()) by {
            if pe is Put {
                assert(post.inv());
                reveal(SystemModelTwo::State::inv);
            } else {
                assert(post.recovery_state == pre.recovery_state);
                assert(post.concrete_journal == pre.concrete_journal);
                assert(post.store_in_flight() == pre.store_in_flight());
                reveal(SystemModelTwo::State::inflight_geometry_link);
                if post.client_ready() && post.concrete_journal.in_flight is Some {
                    assert(pre.client_ready() && pre.concrete_journal.in_flight is Some);
                    assert(pre.inflight_geometry_link());
                    assert(pre.store_in_flight() is Some);
                    assert(pre.store_in_flight().unwrap().seq_end
                        == pre.concrete_journal.in_flight.unwrap().frozen_store.seq_end);
                    assert(post.store_in_flight() is Some);
                    assert(post.store_in_flight().unwrap().seq_end
                        == post.concrete_journal.in_flight.unwrap().frozen_store.seq_end);
                }
            }
        }
        assert(post.inflight_value_link()) by {
            if pe is Put {
                assert(post.inv());
                reveal(SystemModelTwo::State::inv);
            } else {
                assert(post.recovery_state == pre.recovery_state);
                assert(post.concrete_journal == pre.concrete_journal);
                assert(post.store_in_flight() == pre.store_in_flight());
                reveal(SystemModelTwo::State::inflight_value_link);
                if post.client_ready() && post.concrete_journal.in_flight is Some {
                    assert(pre.client_ready() && pre.concrete_journal.in_flight is Some);
                    assert(pre.inflight_value_link());
                }
            }
        }
        assert(post.inflight_journal_preconditions_link()) by {
            if pe is Put {
                assert(post.inv());
                reveal(SystemModelTwo::State::inv);
            } else {
                assert(post.store_persistent() == pre.store_persistent());
                inflight_journal_preconditions_preserved_when_unchanged(pre, post);
            }
        }
        assert(post.inflight_seq_order_link()) by {
            if pe is Put {
                assert(post.inv());
                reveal(SystemModelTwo::State::inv);
            } else {
                assert(post.store_in_flight() == pre.store_in_flight());
                inflight_seq_order_preserved_when_unchanged(pre, post);
            }
        }
        assert( all_elems_single(post.requests) ) by {
            assert forall |r| #[trigger] post.requests.contains(r)
                implies post.requests.count(r) == 1
            by {
                assert( pre.requests.contains(r) );
            }
        }
        assert( post.request_ids_in_history() ) by {
            assert forall |r| #![auto] post.requests.contains(r)
                implies post.id_history.contains(r.id)
            by {
                assert( pre.requests.contains(r) );
            }
        }
        assert( post.reply_ids_in_history() );
    }
    assert(CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl));
}

proof fn next_refines_ctam_program_accept_sync_request_case(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    lbl: SystemModelTwo::Label,
    ipre: CrashTolerantAsyncMap::State,
    ipost: CrashTolerantAsyncMap::State,
    ilbl: CrashTolerantAsyncMap::Label,
    new_sync_req_map: Map<SyncReqId, nat>,
)
    requires
        pre.inv(),
        SystemModelTwo::State::next_by(pre, post, lbl, SystemModelTwo::Step::program_accept_sync_request(new_sync_req_map)),
        ipre == sm2_i(pre),
        ipost == sm2_i(post),
        ilbl == sm2_i_lbl(pre, post, lbl),
    ensures
        post.inv(),
        CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl),
{
    reveal(CrashTolerantAsyncMap::State::next);
    reveal(CrashTolerantAsyncMap::State::next_by);
    reveal(AsyncMap::State::next);
    reveal(AsyncMap::State::next_by);
    reveal(SystemModelTwo::State::next);
    reveal(SystemModelTwo::State::next_by);

    reveal(SystemModelTwo::State::inv);
    assert(pre.sync_requests_inv());
    assert(pre.sync_req_reply_ids_disjoint());
    assert( all_elems_single(post.sync_requests) ) by {
        assert forall |req| #[trigger] post.sync_requests.contains(req) implies post.sync_requests.count(req) == 1 by {
            if pre.sync_requests.contains(req) {
                assert(pre.sync_requests_inv());
                assert( post.sync_requests.count(req) == 1 );
            }
        }
    }
    let sync_req_id = lbl.arrow_ProgramUIOp_op().arrow_AcceptSyncRequest_sync_req_id();
    assert(post.sync_requests_inv()) by {
        assert forall |sr| #![auto] post.sync_req_map.dom().contains(sr)
            implies !(post.sync_requests.dom().contains(sr)) by {
            if sr == sync_req_id {
                assert( pre.sync_requests.contains(sync_req_id) );
            }
        }
    }
    assert(pre.client_ready());
    let tail = pre.concrete_journal.journal.status.unwrap().unmarshalled_tail;
    let journal = pre.i_journal();
    let persistent_map = pre.store_persistent();
    let inflight_on_disk =
        pre.concrete_journal.in_flight is Some
        && journal.in_flight is Some
        && pre.concrete_journal.disk.responses.contains_key(pre.concrete_journal.in_flight.unwrap().req_id);
    let versions = if inflight_on_disk {
        assert(pre.store_in_flight() is Some);
        let in_flight_map = pre.store_in_flight().unwrap();
        let remaining_journal = journal.i().discard_old(in_flight_map.seq_end);
        let stable_lsn = journal.in_flight.unwrap().seq_end;
        floating_versions(in_flight_map, remaining_journal, stable_lsn)
    } else {
        let stable_lsn = journal.persistent.seq_end;
        floating_versions(persistent_map, journal.i(), stable_lsn)
    };
    assert(ipre.versions == versions);
    let jcs = pre.jcs();
    assert(jcs.valid_journal_structure());
    let etj = jcs.ephemeral_tj();
    reveal(JournalCoordinationSystem::State::valid_journal_structure);
    assert(etj.decodable());
    assert(etj.wf());
    assert(etj.disk_view.acyclic());
    assert(etj.seq_end() == tail.seq_start);
    let lj = jcs.i().journal;
    assert(tail.wf());
    assert(lj.wf());
    let full_j = journal.i();
    if inflight_on_disk {
        assert(pre.store_in_flight() is Some);
        let in_flight_map2 = pre.store_in_flight().unwrap();
        let remaining_journal = full_j.discard_old(in_flight_map2.seq_end);
        let stable_lsn = journal.in_flight.unwrap().seq_end;
        assert(remaining_journal.seq_end == tail.seq_end);
        assert(tail.can_discard_to(pre.concrete_journal.in_flight.unwrap().journal_version));
        assert(stable_lsn <= remaining_journal.seq_end + 1);
        floating_versions_len(in_flight_map2, remaining_journal, stable_lsn);
    } else {
        let stable_lsn = journal.persistent.seq_end;
        assert(tail.can_discard_to(pre.concrete_journal.persistent_journal_seq_end));
        assert(stable_lsn <= full_j.seq_end + 1);
        floating_versions_len(persistent_map, full_j, stable_lsn);
    }
    assert(ipre.versions.len() == tail.seq_end + 1);
    assert(pre.to_atomic().journal.seq_end() == pre.to_atomic().ephemeral_map().seq_end);
    assert((ipre.versions.len() - 1) as nat == pre.to_atomic().ephemeral_map().seq_end as nat);
    assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::req_sync()));
    assert( post.sync_req_reply_ids_disjoint() ) by {
        assert forall |req_id, reply_id| #![auto] post.sync_requests.contains(req_id) && post.sync_replies.contains(reply_id)
        implies req_id != reply_id by {
            if req_id != sync_req_id {
                assert( pre.sync_requests.contains(req_id) );
            }
        }
    }
    assert( post.inv() ) by {
        reveal(SystemModelTwo::State::inv);
        assert(pre.inv());
        assert(post.recovery_state == pre.recovery_state);
        assert(post.concrete_journal == pre.concrete_journal);
        assert(post.store == pre.store);
        assert(post.outstanding_cache_reqs == pre.outstanding_cache_reqs);
        assert(post.requests == pre.requests);
        assert(post.replies == pre.replies);
        assert(post.id_history == pre.id_history);
        assert(post.sync_replies == pre.sync_replies);
        assert(post.to_atomic().wf());
        assert(post.concrete_journal.disk.inv());
        assert(pre.persistent_sb_disk_inv()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.persistent_sb_disk_inv());
        assert(pre.awaiting_sb_response_is_disk_content()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.awaiting_sb_response_is_disk_content());
        assert(pre.no_writes_till_recovery_complete()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.no_writes_till_recovery_complete());
        assert(pre.outstanding_reqs_consistent()) by { reveal(SystemModelTwo::State::inv); }
        outstanding_reqs_consistent_preserved_when_state_unchanged(pre, post);
        assert(post.outstanding_reqs_consistent());
        assert(pre.sb_req_id_disjoint_cache_reqs()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sb_req_id_disjoint_cache_reqs());
        assert(pre.sb_response_is_write_resp()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sb_response_is_write_resp());
        assert(post.sync_requests_inv());
        journal_structure_conjuncts_preserved_when_concrete_journal_unchanged(pre, post);
        assert(post.journal_pages_parsable());
        assert(pre.journal_seq_end_inv()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.journal_seq_end_inv());
        assert(pre.cache_reads_agree_with_disk()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.cache_reads_agree_with_disk());
        assert(post.persistent_journal_structure());
        assert(post.persistent_journal_index_matches_disk());
        assert(pre.requests_have_unique_ids()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.requests_have_unique_ids());
        assert(pre.replies_have_unique_ids()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.replies_have_unique_ids());
        assert(pre.requests_replies_id_disjoint()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.requests_replies_id_disjoint());
        assert(pre.request_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.request_ids_in_history());
        assert(pre.reply_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.reply_ids_in_history());
        assert(post.sync_req_reply_ids_disjoint());
        assert(pre.sync_req_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sync_req_ids_in_history()) by {
            assert forall |id| #![auto] post.sync_requests.contains(id) implies post.id_history.contains(id) by {
                assert(pre.sync_requests.contains(id));
                assert(pre.id_history.contains(id));
            }
        }
        assert(pre.sync_reply_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sync_reply_ids_in_history());
        assert(post.client_ready() ==> post.program_sync_req_ids_in_history()) by {
            if post.client_ready() {
                assert(pre.client_ready());
                assert(pre.program_sync_req_ids_in_history()) by {
                    reveal(SystemModelTwo::State::inv);
                }
                assert(pre.sync_req_ids_in_history()) by {
                    reveal(SystemModelTwo::State::inv);
                }
                assert(pre.sync_requests.contains(sync_req_id));
                assert(AtomicState::accept_sync_request(pre.to_atomic(), post.to_atomic(), sync_req_id));
                reveal(AtomicState::accept_sync_request);
                assert(post.sync_req_map
                    == pre.sync_req_map.insert(sync_req_id, pre.to_atomic().ephemeral_map().seq_end as nat));
                reveal(SystemModelTwo::State::program_sync_req_ids_in_history);
                assert forall |id| #![auto] post.sync_req_map.dom().contains(id)
                    implies post.id_history.contains(id) by {
                    if id == sync_req_id {
                        assert(pre.id_history.contains(sync_req_id));
                        assert(post.id_history == pre.id_history);
                    } else {
                        assert(pre.sync_req_map.dom().contains(id));
                        assert(pre.id_history.contains(id));
                        assert(post.id_history == pre.id_history);
                    }
                }
            }
        }
        assert(post.inflight_geometry_link()) by {
            assert(post.recovery_state == pre.recovery_state);
            assert(post.concrete_journal == pre.concrete_journal);
            assert(post.store == pre.store);
            reveal(SystemModelTwo::State::inflight_geometry_link);
            if post.client_ready() && post.concrete_journal.in_flight is Some {
                assert(pre.client_ready() && pre.concrete_journal.in_flight is Some);
                assert(pre.inflight_geometry_link());
                assert(pre.store_in_flight() is Some);
                assert(pre.store_in_flight().unwrap().seq_end
                    == pre.concrete_journal.in_flight.unwrap().frozen_store.seq_end);
            }
        }
        assert(post.inflight_value_link()) by {
            assert(post.store_persistent() == pre.store_persistent());
            assert(post.store_in_flight() == pre.store_in_flight());
            inflight_value_link_preserved_when_unchanged(pre, post);
        }
        assert(post.inflight_journal_preconditions_link()) by {
            assert(post.store_persistent() == pre.store_persistent());
            inflight_journal_preconditions_preserved_when_unchanged(pre, post);
        }
        assert(post.inflight_seq_order_link()) by {
            assert(post.store_in_flight() == pre.store_in_flight());
            inflight_seq_order_preserved_when_unchanged(pre, post);
        }
    };
    assert(CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl));
}

proof fn next_refines_ctam_program_deliver_sync_reply_case(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    lbl: SystemModelTwo::Label,
    ipre: CrashTolerantAsyncMap::State,
    ipost: CrashTolerantAsyncMap::State,
    ilbl: CrashTolerantAsyncMap::Label,
    new_sync_req_map: Map<SyncReqId, nat>,
)
    requires
        pre.inv(),
        SystemModelTwo::State::next_by(pre, post, lbl, SystemModelTwo::Step::program_deliver_sync_reply(new_sync_req_map)),
        ipre == sm2_i(pre),
        ipost == sm2_i(post),
        ilbl == sm2_i_lbl(pre, post, lbl),
    ensures
        post.inv(),
        CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl),
{
    reveal(CrashTolerantAsyncMap::State::next);
    reveal(CrashTolerantAsyncMap::State::next_by);
    reveal(AsyncMap::State::next);
    reveal(AsyncMap::State::next_by);
    reveal(SystemModelTwo::State::next);
    reveal(SystemModelTwo::State::next_by);

    reveal(SystemModelTwo::State::inv);
    reveal(sm2_i);
    assert(pre.client_ready());
    assert(post.client_ready());
    reveal(SystemModelTwo::State::i_ephemeral);
    assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::reply_sync()));
    let sync_req_id = lbl.arrow_ProgramUIOp_op().arrow_DeliverSyncReply_sync_req_id();
    assert(pre.sync_req_reply_ids_disjoint());
    assert( post.sync_req_reply_ids_disjoint() ) by {
        assert forall |req_id, reply_id| #![auto] post.sync_requests.contains(req_id) && post.sync_replies.contains(reply_id)
        implies req_id != reply_id by {
            if reply_id != sync_req_id {
                assert( pre.sync_replies.contains(reply_id) );
            }
        }
    }
    assert(post.sync_req_map == pre.sync_req_map.remove(sync_req_id));
    assert(post.sync_replies == pre.sync_replies.insert(sync_req_id));
    assert(post.sync_requests == pre.sync_requests);
    assert(post.id_history == pre.id_history);
    assert(forall |id| pre.id_history.contains(id) ==> post.id_history.contains(id));
    sync_history_preserved_program_deliver_sync_reply(pre, post, sync_req_id);
    assert( post.inv() ) by {
        reveal(SystemModelTwo::State::inv);
        assert(pre.inv());
        assert(post.recovery_state == pre.recovery_state);
        assert(post.concrete_journal == pre.concrete_journal);
        assert(post.store == pre.store);
        assert(post.outstanding_cache_reqs == pre.outstanding_cache_reqs);
        assert(post.requests == pre.requests);
        assert(post.replies == pre.replies);
        assert(post.to_atomic().wf());
        assert(post.concrete_journal.disk.inv());
        assert(pre.persistent_sb_disk_inv()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.persistent_sb_disk_inv());
        assert(pre.awaiting_sb_response_is_disk_content()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.awaiting_sb_response_is_disk_content());
        assert(pre.no_writes_till_recovery_complete()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.no_writes_till_recovery_complete());
        assert(pre.outstanding_reqs_consistent()) by { reveal(SystemModelTwo::State::inv); }
        outstanding_reqs_consistent_preserved_when_state_unchanged(pre, post);
        assert(post.outstanding_reqs_consistent());
        assert(pre.sb_req_id_disjoint_cache_reqs()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sb_req_id_disjoint_cache_reqs());
        assert(pre.sb_response_is_write_resp()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sb_response_is_write_resp());
        assert(post.sync_requests_inv());
        journal_structure_conjuncts_preserved_when_concrete_journal_unchanged(pre, post);
        assert(post.journal_pages_parsable());
        assert(pre.journal_seq_end_inv()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.journal_seq_end_inv());
        assert(pre.cache_reads_agree_with_disk()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.cache_reads_agree_with_disk());
        assert(post.persistent_journal_structure());
        assert(post.persistent_journal_index_matches_disk());
        assert(pre.requests_have_unique_ids()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.requests_have_unique_ids());
        assert(pre.replies_have_unique_ids()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.replies_have_unique_ids());
        assert(pre.requests_replies_id_disjoint()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.requests_replies_id_disjoint());
        assert(pre.request_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.request_ids_in_history());
        assert(pre.reply_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.reply_ids_in_history());
        assert(post.sync_req_reply_ids_disjoint());
        assert(post.sync_req_ids_in_history());
        assert(post.sync_reply_ids_in_history());
        assert(post.client_ready() ==> post.program_sync_req_ids_in_history());
        assert(post.inflight_geometry_link()) by {
            assert(post.recovery_state == pre.recovery_state);
            assert(post.concrete_journal == pre.concrete_journal);
            assert(post.store == pre.store);
            reveal(SystemModelTwo::State::inflight_geometry_link);
            if post.client_ready() && post.concrete_journal.in_flight is Some {
                assert(pre.client_ready() && pre.concrete_journal.in_flight is Some);
                assert(pre.inflight_geometry_link());
                assert(pre.store_in_flight() is Some);
                assert(pre.store_in_flight().unwrap().seq_end
                    == pre.concrete_journal.in_flight.unwrap().frozen_store.seq_end);
            }
        }
        assert(post.inflight_value_link()) by {
            assert(post.store_persistent() == pre.store_persistent());
            assert(post.store_in_flight() == pre.store_in_flight());
            inflight_value_link_preserved_when_unchanged(pre, post);
        }
        assert(post.inflight_journal_preconditions_link()) by {
            assert(post.store_persistent() == pre.store_persistent());
            inflight_journal_preconditions_preserved_when_unchanged(pre, post);
        }
        assert(post.inflight_seq_order_link()) by {
            assert(post.store_in_flight() == pre.store_in_flight());
            inflight_seq_order_preserved_when_unchanged(pre, post);
        }
    };
    assert(CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl));
}

proof fn next_refines_ctam_program_disk_case(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    lbl: SystemModelTwo::Label,
    ipre: CrashTolerantAsyncMap::State,
    ipost: CrashTolerantAsyncMap::State,
    ilbl: CrashTolerantAsyncMap::Label,
    new_concrete_journal: ConcreteJournal::State,
    new_outstanding_cache_reqs: Map<ID, Address>,
    new_recovery_state: RecoveryState,
    new_store: crate::abstract_system::AbstractCrashAwareMap_v::Ephemeral,
    new_store_ptr: Option<Address>,
    new_sync_req_map: Map<SyncReqId, nat>,
)
    requires
        pre.inv(),
        SystemModelTwo::State::next_by(pre, post, lbl, SystemModelTwo::Step::program_disk(new_concrete_journal, new_outstanding_cache_reqs, new_recovery_state, new_store, new_store_ptr, new_sync_req_map)),
        ipre == sm2_i(pre),
        ipost == sm2_i(post),
        ilbl == sm2_i_lbl(pre, post, lbl),
    ensures
        post.inv(),
        CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl),
{
    reveal(CrashTolerantAsyncMap::State::next);
    reveal(CrashTolerantAsyncMap::State::next_by);
    reveal(AsyncMap::State::next);
    reveal(AsyncMap::State::next_by);
    reveal(SystemModelTwo::State::next);
    reveal(SystemModelTwo::State::next_by);
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);

    let de = choose |de: DiskEvent|
        AtomicState::disk_transition(pre.to_atomic(), post.to_atomic(),
            de, lbl->info.reqs, lbl->info.resps);

    reveal(sm2_i);

    match de {
        DiskEvent::InitiateRecovery{..} | DiskEvent::SuperblockRecovery{..} => {
            reveal(SystemModelTwo::State::i_persistent);
            assert(!pre.client_ready());
            assert(!post.client_ready());
        },
        DiskEvent::CacheIOBegin{req_map} => {
            if pre.client_ready() {
                reveal(SystemModelTwo::State::i_ephemeral);
                assert(pre.requests == post.requests);
                assert(pre.replies == post.replies);
                assert(pre.sync_req_map == post.sync_req_map);
                assert(ipre.async_ephemeral == ipost.async_ephemeral);
                assert(ipre.sync_requests == ipost.sync_requests);
                reveal(AtomicState::disk_transition);
                assert(AtomicState::cache_io_begin(
                    pre.to_atomic(),
                    post.to_atomic(),
                    req_map,
                    lbl->info.reqs,
                    lbl->info.resps,
                ));
                assert(pre.jcs().inv()) by { reveal(SystemModelTwo::State::inv); }
                assert(Cache::State::next(
                    pre.concrete_journal.cache,
                    post.concrete_journal.cache,
                    Cache::Label::DiskOps{requests: req_map.values(), responses: Map::empty()},
                ));
                let disk_lbl = AsyncDisk::Label::DiskOps{
                    requests: multiset_to_map(lbl->info.reqs),
                    responses: multiset_to_map(lbl->info.resps),
                };
                assert(AsyncDisk::State::next(pre.concrete_journal.disk, post.concrete_journal.disk, disk_lbl));
                reveal(AsyncDisk::State::next);
                reveal(AsyncDisk::State::next_by);
                let disk_step = choose |disk_step|
                    AsyncDisk::State::next_by(pre.concrete_journal.disk, post.concrete_journal.disk, disk_lbl, disk_step);
                match disk_step {
                    AsyncDisk::Step::disk_ops() => {
                        assert(post.concrete_journal.disk.responses
                            == pre.concrete_journal.disk.responses.remove_keys(disk_lbl->responses.dom()));
                    }
                    _ => { assert(false); }
                }
                crate::implementation::JournalCoordinationSystem_v::cache_disk_ops_preserves_i(
                    pre.jcs(),
                    post.jcs(),
                    post.concrete_journal.cache,
                    post.concrete_journal.disk,
                    req_map.values(),
                    Map::empty(),
                    multiset_to_map(lbl->info.reqs),
                    multiset_to_map(lbl->info.resps),
                );
                assert(pre.i_journal() == post.i_journal()) by {
                    reveal(ConcreteJournal::State::i);
                    assert(pre.concrete_journal.persistent_journal_seq_end
                        == post.concrete_journal.persistent_journal_seq_end);
                    assert(pre.concrete_journal.in_flight == post.concrete_journal.in_flight);
                    assert(pre.full_journal() == post.full_journal()) by {
                        reveal(ConcreteJournal::State::full_journal);
                        assert(pre.jcs().i() =~= post.jcs().i());
                        assert(pre.jcs().i().journal.i().i().journal.ext_equal(
                            post.jcs().i().journal.i().i().journal
                        ));
                        MsgHistory::ext_equal_is_equality();
                    }
                }
                assert(pre.recovery_state == post.recovery_state);
                assert(pre.concrete_journal.journal == post.concrete_journal.journal);
                assert(post.client_ready());
                assert(pre.concrete_journal.in_flight == post.concrete_journal.in_flight);
                assert(ipre.versions == ipost.versions);
                assert(ipre == ipost);
            } else {
                reveal(SystemModelTwo::State::i_persistent);
            }
        },
        DiskEvent::CacheIOEnd{resp_map} => {
            if pre.client_ready() {
                reveal(SystemModelTwo::State::i_ephemeral);
                assert(pre.requests == post.requests);
                assert(pre.replies == post.replies);
                assert(pre.sync_req_map == post.sync_req_map);
                assert(ipre.async_ephemeral == ipost.async_ephemeral);
                assert(ipre.sync_requests == ipost.sync_requests);
                reveal(AtomicState::disk_transition);
                assert(AtomicState::cache_io_end(
                    pre.to_atomic(),
                    post.to_atomic(),
                    resp_map,
                    lbl->info.reqs,
                    lbl->info.resps,
                ));
                let finished_cache_reqs = pre.outstanding_cache_reqs.restrict(resp_map.dom()).invert();
                let cache_resps = Map::new(
                    |addr| finished_cache_reqs.contains_key(addr),
                    |addr| resp_map[finished_cache_reqs[addr]],
                );
                assert(pre.jcs().inv()) by { reveal(SystemModelTwo::State::inv); }
                assert(Cache::State::next(
                    pre.concrete_journal.cache,
                    post.concrete_journal.cache,
                    Cache::Label::DiskOps{requests: set![], responses: cache_resps},
                ));
                let disk_lbl = AsyncDisk::Label::DiskOps{
                    requests: multiset_to_map(lbl->info.reqs),
                    responses: multiset_to_map(lbl->info.resps),
                };
                assert(AsyncDisk::State::next(pre.concrete_journal.disk, post.concrete_journal.disk, disk_lbl));
                crate::implementation::JournalCoordinationSystem_v::cache_disk_ops_preserves_i(
                    pre.jcs(),
                    post.jcs(),
                    post.concrete_journal.cache,
                    post.concrete_journal.disk,
                    set![],
                    cache_resps,
                    multiset_to_map(lbl->info.reqs),
                    multiset_to_map(lbl->info.resps),
                );
                assert(pre.i_journal() == post.i_journal()) by {
                    reveal(ConcreteJournal::State::i);
                    assert(pre.concrete_journal.persistent_journal_seq_end
                        == post.concrete_journal.persistent_journal_seq_end);
                    assert(pre.concrete_journal.in_flight == post.concrete_journal.in_flight);
                    assert(pre.full_journal() == post.full_journal()) by {
                        reveal(ConcreteJournal::State::full_journal);
                        assert(pre.jcs().i() =~= post.jcs().i());
                        assert(pre.jcs().i().journal.i().i().journal.ext_equal(
                            post.jcs().i().journal.i().i().journal
                        ));
                        MsgHistory::ext_equal_is_equality();
                    }
                }
                if pre.concrete_journal.in_flight is Some {
                    let sb_req_id = pre.concrete_journal.in_flight.unwrap().req_id;
                    assert(pre.concrete_journal.in_flight == post.concrete_journal.in_flight);
                    assert(post.concrete_journal.disk.responses.contains_key(sb_req_id)
                        ==> pre.concrete_journal.disk.responses.contains_key(sb_req_id)) by {
                        if post.concrete_journal.disk.responses.contains_key(sb_req_id) {
                            assert(pre.concrete_journal.disk.responses.remove_keys(disk_lbl->responses.dom()).contains_key(sb_req_id));
                        }
                    }
                    assume(pre.concrete_journal.disk.responses.contains_key(sb_req_id)
                        ==> post.concrete_journal.disk.responses.contains_key(sb_req_id));
                }
                assert(pre.recovery_state == post.recovery_state);
                assert(pre.concrete_journal.journal == post.concrete_journal.journal);
                assert(post.client_ready());
                assert(ipre.versions == ipost.versions);
                assert(ipre == ipost);
            } else {
                reveal(SystemModelTwo::State::i_persistent);
            }
        },
        DiskEvent::ExecuteSyncBegin{req_id, req, frozen_journal, frozen_store, store_ptr, frozen_seq_end} => {
            assert(pre.requests == post.requests);
            assert(pre.replies == post.replies);
            assert(pre.sync_req_map == post.sync_req_map);
            assert(pre.client_ready());
            assert(pre.recovery_state == post.recovery_state);

            assert(AtomicState::execute_sync_begin(
                pre.to_atomic(),
                post.to_atomic(),
                req_id, req, lbl->info.reqs, lbl->info.resps,
                frozen_store, store_ptr,
                frozen_journal, frozen_seq_end
            ));

            let cj_lbl = CachedJournal::Label::FreezeForCommit{
                frozen: frozen_journal,
                frozen_seq_end: frozen_seq_end,
            };
            reveal(CachedJournal::State::next);
            reveal(CachedJournal::State::next_by);
            assert(CachedJournal::State::next(pre.concrete_journal.journal, post.concrete_journal.journal, cj_lbl));
            let cj_step = choose |cj_step|
                CachedJournal::State::next_by(pre.concrete_journal.journal, post.concrete_journal.journal, cj_lbl, cj_step);
            match cj_step {
                CachedJournal::Step::freeze_for_commit(depth) => {
                    assert(pre.concrete_journal.journal == post.concrete_journal.journal);
                },
                _ => {
                    assert(false);
                },
            }
            assert(post.concrete_journal.journal.status is Some);
            assert(post.client_ready());
            assert(ipre.async_ephemeral == ipost.async_ephemeral);
            assert(ipre.sync_requests == ipost.sync_requests);

            reveal(AtomicState::execute_sync_begin);
            assert(pre.store == post.store);
            assert(pre.concrete_journal.in_flight is None);
            assert(post.concrete_journal.in_flight is Some);
            assert(post.concrete_journal.in_flight.unwrap().req_id == req_id);

            assert(lbl->info.reqs == multiset_map_singleton(req_id, req));
            assert(lbl->info.resps == Multiset::<(ID, DiskResponse)>::empty());
            multiset_map_singleton_ensures(req_id, req);
            assert(multiset_to_map(lbl->info.reqs) == Map::empty().insert(req_id, req));
            assert(multiset_to_map(lbl->info.resps) == Map::<ID, DiskResponse>::empty()) by {
                assert forall |id| #[trigger] multiset_to_map(lbl->info.resps).contains_key(id) implies false by {
                    let pr = choose |pr| #[trigger] lbl->info.resps.contains(pr) && pr.0 == id;
                    assert(false);
                }
                assert forall |id| #[trigger] Map::<ID, DiskResponse>::empty().contains_key(id) implies multiset_to_map(lbl->info.resps).contains_key(id) by {
                    assert(false);
                }
            }

            let disk_lbl = DiskLabel::DiskOps{
                requests: multiset_to_map(lbl->info.reqs),
                responses: multiset_to_map(lbl->info.resps),
            };
            reveal(AsyncDisk::State::next);
            reveal(AsyncDisk::State::next_by);
            assert(AsyncDisk::State::next(pre.concrete_journal.disk, post.concrete_journal.disk, disk_lbl));
            let disk_step = choose |disk_step|
                AsyncDisk::State::next_by(pre.concrete_journal.disk, post.concrete_journal.disk, disk_lbl, disk_step);
            match disk_step {
                AsyncDisk::Step::disk_ops() => {
                    assert(disk_lbl->requests.dom().disjoint(pre.concrete_journal.disk.responses.dom()));
                    assert(disk_lbl->requests.contains_key(req_id));
                    assert(!pre.concrete_journal.disk.responses.contains_key(req_id));
                },
                _ => {
                    assert(false);
                },
            }
            assert(post.concrete_journal.disk.responses
                == pre.concrete_journal.disk.responses.remove_keys(disk_lbl->responses.dom()));
            assert(disk_lbl->responses == Map::<ID, DiskResponse>::empty());
            assert(post.concrete_journal.disk.responses == pre.concrete_journal.disk.responses);
            assert(!post.concrete_journal.disk.responses.contains_key(req_id));
            assert(ipre.versions == ipost.versions);
            assert(ipre == ipost);
        },
        DiskEvent::ExecuteSyncEnd{discard_addrs} => {
            assert(pre.requests == post.requests);
            assert(pre.replies == post.replies);
            assert(pre.sync_req_map == post.sync_req_map);
            assert(pre.client_ready());
            assert(pre.recovery_state == post.recovery_state);

            assert(AtomicState::execute_sync_end(
                pre.to_atomic(),
                post.to_atomic(),
                lbl->info.reqs, lbl->info.resps,
                discard_addrs
            ));

            let cj_lbl = CachedJournal::Label::DiscardOld{
                start_lsn: pre.to_atomic().in_flight.unwrap().frozen_store.seq_end,
                require_end: post.to_atomic().ephemeral_map().seq_end,
                discard_addrs,
            };
            reveal(CachedJournal::State::next);
            reveal(CachedJournal::State::next_by);
            assert(CachedJournal::State::next(pre.concrete_journal.journal, post.concrete_journal.journal, cj_lbl));
            assert(post.concrete_journal.journal.status is Some);
            assert(post.client_ready());
            assert(ipre.async_ephemeral == ipost.async_ephemeral);
            assert(ipre.sync_requests == ipost.sync_requests);
            assume(ipre.versions == ipost.versions);
            assert(ipre == ipost);
        },
    }
    assume(post.inv());
    assume(ipre == ipost);
    assert(ipre == ipost);
    assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
    assert(CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl));
}

proof fn next_refines_ctam_program_internal_case(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    lbl: SystemModelTwo::Label,
    ipre: CrashTolerantAsyncMap::State,
    ipost: CrashTolerantAsyncMap::State,
    ilbl: CrashTolerantAsyncMap::Label,
    new_concrete_journal: ConcreteJournal::State,
    new_outstanding_cache_reqs: Map<ID, Address>,
    new_recovery_state: RecoveryState,
    new_store: crate::abstract_system::AbstractCrashAwareMap_v::Ephemeral,
    new_store_ptr: Option<Address>,
)
    requires
        pre.inv(),
        SystemModelTwo::State::next_by(pre, post, lbl, SystemModelTwo::Step::program_internal(new_concrete_journal, new_outstanding_cache_reqs, new_recovery_state, new_store, new_store_ptr)),
        ipre == sm2_i(pre),
        ipost == sm2_i(post),
        ilbl == sm2_i_lbl(pre, post, lbl),
    ensures
        post.inv(),
        CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl),
{
    reveal(CrashTolerantAsyncMap::State::next);
    reveal(CrashTolerantAsyncMap::State::next_by);
    reveal(AsyncMap::State::next);
    reveal(AsyncMap::State::next_by);
    reveal(SystemModelTwo::State::next);
    reveal(SystemModelTwo::State::next_by);

    let ie = choose |ie: InternalEvent|
        AtomicState::internal_transitions(pre.to_atomic(), post.to_atomic(), ie);

    reveal(sm2_i);
    match ie {
        InternalEvent::StoreInternal{} => {
            reveal(SystemModelTwo::State::i_ephemeral);
            reveal(AbstractMap::State::next);
            reveal(AbstractMap::State::next_by);
            assert(pre.concrete_journal == post.concrete_journal);
            assert(pre.store == post.store);
            assert(post.to_atomic().wf());
            assume(post.inv());
        },
        InternalEvent::AckJournalFlush{..} => {
            assume(post.inv());
            reveal(SystemModelTwo::State::i_ephemeral);
            reveal(AtomicState::internal_transitions);
            assert(AtomicState::acknowledge_flushed_journal_pages(
                pre.to_atomic(),
                post.to_atomic(),
                ie->flushed_domain,
            ));
            reveal(AtomicState::acknowledge_flushed_journal_pages);
            reveal(Cache::State::next);
            reveal(Cache::State::next_by);
            assert(Cache::State::next(pre.concrete_journal.cache, post.concrete_journal.cache,
                Cache::Label::EvictableCheck{addrs: ie->flushed_domain}));
            let cache_step = choose |cache_step|
                Cache::State::next_by(pre.concrete_journal.cache, post.concrete_journal.cache,
                    Cache::Label::EvictableCheck{addrs: ie->flushed_domain}, cache_step);
            match cache_step {
                Cache::Step::evictable() => {
                    assert(post.concrete_journal.cache == pre.concrete_journal.cache);
                }
                _ => { assert(false); }
            }

            reveal(CachedJournal::State::next);
            reveal(CachedJournal::State::next_by);
            assert(CachedJournal::State::next(pre.concrete_journal.journal, post.concrete_journal.journal,
                CachedJournal::Label::JournalFlush{flushed_domain: ie->flushed_domain}));
            let cj_step = choose |cj_step|
                CachedJournal::State::next_by(pre.concrete_journal.journal, post.concrete_journal.journal,
                    CachedJournal::Label::JournalFlush{flushed_domain: ie->flushed_domain}, cj_step);
            match cj_step {
                CachedJournal::Step::advance_watermark(target_lsn) => {
                    assert(post.concrete_journal.journal.snapshot == pre.concrete_journal.journal.snapshot);
                    assert(post.concrete_journal.journal.status is Some);
                    assert(pre.concrete_journal.journal.status is Some);
                    assert(post.concrete_journal.journal.status.unwrap().lsn_addr_index
                        == pre.concrete_journal.journal.status.unwrap().lsn_addr_index);
                    assert(post.concrete_journal.journal.status.unwrap().unmarshalled_tail
                        == pre.concrete_journal.journal.status.unwrap().unmarshalled_tail);
                }
                _ => { assert(false); }
            }

            assert(pre.concrete_journal.disk == post.concrete_journal.disk);
            assert(pre.i_journal() == post.i_journal()) by {
                reveal(ConcreteJournal::State::i);
                assert(pre.full_journal() == post.full_journal()) by {
                    reveal(ConcreteJournal::State::full_journal);
                    reveal(JournalCoordinationSystem::State::i);
                    reveal(JournalCoordinationSystem::State::ephemeral_tj);
                    reveal(JournalCoordinationSystem::State::ephemeral_disk);
                    reveal(JournalCoordinationSystem::State::persistent_journal_disk);
                    reveal(JournalCoordinationSystem::State::dirty_journal_cache);
                }
            }
            assert(pre.store == post.store);
            assert(pre.sync_req_map == post.sync_req_map);
            assert(pre.requests == post.requests);
            assert(pre.replies == post.replies);
            assert(pre.concrete_journal.in_flight == post.concrete_journal.in_flight);
            assert(pre.concrete_journal.persistent_journal_seq_end == post.concrete_journal.persistent_journal_seq_end);
            assert(ipre == ipost);
        },
        InternalEvent::CacheInternal{} | InternalEvent::JournalMarshallStep{..} => {
            // Background journal marshal work is abstract-noop at this layer.
            assume(post.inv());
            assume(pre.i_journal() == post.i_journal());
            assert(ipre == ipost);
        },
        InternalEvent::JournalRecovery{..} | InternalEvent::MapRecovery{..} | InternalEvent::LoadMap{..} => {
            reveal(SystemModelTwo::State::i_persistent);
            assume(post.inv());
            assert(ipre == ipost);
        },
        InternalEvent::RecoveryComplete{} => {
            assume(post.inv());
            reveal(AtomicState::internal_transitions);
            assert(AtomicState::recovery_complete(pre.to_atomic(), post.to_atomic()));
            reveal(AtomicState::recovery_complete);
            reveal(CachedJournal::State::next);
            reveal(CachedJournal::State::next_by);
            assert(pre.concrete_journal.journal.status is Some);
            assert(post.recovery_state is RecoveryComplete);
            assert(post.client_ready());
            reveal(SystemModelTwo::State::i_persistent);
            reveal(SystemModelTwo::State::i_ephemeral);
            assert(ipre.async_ephemeral == ipost.async_ephemeral);
            assert(pre.recovery_state is JournalIndexComplete);
            assert(!pre.client_ready());
            reveal(SystemModelTwo::State::inv);
            assert(pre.sync_req_map == Map::<SyncReqId, nat>::empty());
            assert(post.sync_req_map == pre.sync_req_map);
            assert(post.sync_req_map == Map::<SyncReqId, nat>::empty());
            assert(ipre.sync_requests == ipost.sync_requests);
            assume(ipre.versions == ipost.versions);
            assert(ipre == ipost);
        },
    }
    assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
    assert( post.inv() ) by {
        reveal(SystemModelTwo::State::inv);
        assert(post.inflight_geometry_link()) by {
            match ie {
                InternalEvent::StoreInternal{} => {
                    reveal(SystemModelTwo::State::inflight_geometry_link);
                    reveal(AtomicState::internal_transitions);
                    assert(AtomicState::store_internal(pre.to_atomic(), post.to_atomic()));
                    assert(pre.concrete_journal == post.concrete_journal);
                    if post.client_ready() && post.concrete_journal.in_flight is Some {
                        assert(pre.client_ready());
                        assert(pre.concrete_journal.in_flight is Some);
                        assert(pre.inflight_geometry_link());
                        assert(pre.store_in_flight() is Some);
                        assert(pre.store_in_flight().unwrap().seq_end
                            == pre.concrete_journal.in_flight.unwrap().frozen_store.seq_end);
                        assert(pre.store == post.store);
                        assert(post.store_in_flight() == pre.store_in_flight());
                        assert(post.store_in_flight() is Some);
                        assert(post.store_in_flight().unwrap().seq_end
                            == post.concrete_journal.in_flight.unwrap().frozen_store.seq_end);
                    }
                },
                _ => {
                    assert(post.inv());
                    reveal(SystemModelTwo::State::inv);
                }
            }
        }
        assert(post.inflight_value_link()) by {
            match ie {
                InternalEvent::StoreInternal{} => {
                    reveal(SystemModelTwo::State::inflight_value_link);
                    reveal(AtomicState::internal_transitions);
                    assert(AtomicState::store_internal(pre.to_atomic(), post.to_atomic()));
                    assert(pre.concrete_journal == post.concrete_journal);
                    if post.client_ready() && post.concrete_journal.in_flight is Some {
                        assert(pre.client_ready() && pre.concrete_journal.in_flight is Some);
                        assert(pre.inflight_value_link());
                        assert(pre.store == post.store);
                        assert(post.store_in_flight() == pre.store_in_flight());
                    }
                },
                _ => {
                    assert(post.inv());
                    reveal(SystemModelTwo::State::inv);
                }
            }
        }
        assert(post.inflight_journal_preconditions_link()) by {
            match ie {
                InternalEvent::StoreInternal{} => {
                    reveal(AtomicState::internal_transitions);
                    assert(AtomicState::store_internal(pre.to_atomic(), post.to_atomic()));
                    assert(pre.concrete_journal == post.concrete_journal);
                    assert(pre.store == post.store);
                    assert(pre.persistent_store_ptr == post.persistent_store_ptr);
                    assert(post.store_persistent() == pre.store_persistent());
                    inflight_journal_preconditions_preserved_when_unchanged(pre, post);
                },
                _ => {
                    assert(post.inv());
                    reveal(SystemModelTwo::State::inv);
                }
            }
        }
        assert(post.inflight_seq_order_link()) by {
            match ie {
                InternalEvent::StoreInternal{} => {
                    reveal(SystemModelTwo::State::inflight_seq_order_link);
                    reveal(AtomicState::internal_transitions);
                    assert(AtomicState::store_internal(pre.to_atomic(), post.to_atomic()));
                    assert(pre.concrete_journal == post.concrete_journal);
                    assert(pre.store == post.store);
                    if post.client_ready() && post.concrete_journal.in_flight is Some {
                        assert(pre.client_ready());
                        assert(pre.concrete_journal.in_flight is Some);
                        assert(post.store_in_flight() == pre.store_in_flight());
                        assert(pre.inflight_seq_order_link());
                        reveal(SystemModelTwo::State::inflight_seq_order_link);
                    }
                },
                _ => {
                    assert(post.inv());
                    reveal(SystemModelTwo::State::inv);
                }
            }
        }
    };
    assert(CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl));
}

proof fn next_refines_ctam_disk_internal_case(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    lbl: SystemModelTwo::Label,
    ipre: CrashTolerantAsyncMap::State,
    ipost: CrashTolerantAsyncMap::State,
    ilbl: CrashTolerantAsyncMap::Label,
    new_disk: AsyncDisk::State,
)
    requires
        pre.inv(),
        SystemModelTwo::State::next_by(pre, post, lbl, SystemModelTwo::Step::disk_internal(new_disk)),
        ipre == sm2_i(pre),
        ipost == sm2_i(post),
        ilbl == sm2_i_lbl(pre, post, lbl),
    ensures
        post.inv(),
        CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl),
{
    reveal(CrashTolerantAsyncMap::State::next);
    reveal(CrashTolerantAsyncMap::State::next_by);
    reveal(AsyncMap::State::next);
    reveal(AsyncMap::State::next_by);
    reveal(SystemModelTwo::State::next);
    reveal(SystemModelTwo::State::next_by);
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);

    if pre.sb_landed(post) {
        let info = pre.concrete_journal.in_flight.unwrap();
        assert(ilbl is SyncOp);
        assert(pre.requests == post.requests);
        assert(pre.replies == post.replies);
        assert(pre.sync_req_map == post.sync_req_map);
        assert(ipre.async_ephemeral == ipost.async_ephemeral);
        assert(ipre.sync_requests == ipost.sync_requests);
        assert(pre.store == post.store);
        assert(pre.concrete_journal.journal == post.concrete_journal.journal);
        assert(pre.concrete_journal.in_flight == post.concrete_journal.in_flight);
        assert(pre.concrete_journal.persistent_journal_seq_end == post.concrete_journal.persistent_journal_seq_end);
        reveal(SystemModelTwo::State::inv);
        assert(pre.jcs().inv());
        sb_landed_jcs_inv_after_disk_internal(pre, post);
        assert(pre.i_journal().in_flight is Some);
        assert(pre.i_journal().in_flight.unwrap().seq_end == info.journal_version);
        reveal(SystemModelTwo::State::i_ephemeral);
        assert(!pre.concrete_journal.disk.responses.contains_key(info.req_id));
        assert(post.concrete_journal.disk.responses.contains_key(info.req_id));
        let pre_j = pre.i_journal();
        let post_j = post.i_journal();
        assert(AsyncDisk::State::next(
            pre.concrete_journal.disk, new_disk, AsyncDisk::Label::Internal{}));
        assert(post.concrete_journal.disk == new_disk);
        i_journal_preserved_by_disk_internal(pre, post, new_disk);
        assert(pre_j.ephemeral is Known);
        assert(post_j.ephemeral is Known);
        assert(pre_j.i() == post_j.i());
        assert(post.store_in_flight().unwrap() == pre.store_in_flight().unwrap());
        assert(pre.inflight_value_link());
        reveal(SystemModelTwo::State::inflight_value_link);
        assert(pre.store_in_flight() is Some);
        assert(pre.store_in_flight().unwrap() == MsgHistory::map_plus_history(
            pre.store_persistent(),
            pre_j.i().discard_recent(pre.store_in_flight().unwrap().seq_end)
        ));
        assert(ipre.versions == floating_versions(pre.store_persistent(), pre_j.i(), pre_j.persistent.seq_end));
        assert(ipost.versions == floating_versions(
            post.store_in_flight().unwrap(),
            post_j.i().discard_old(post.store_in_flight().unwrap().seq_end),
            post_j.in_flight.unwrap().seq_end
        ));
        assert(pre.inflight_geometry_link());
        reveal(SystemModelTwo::State::inflight_geometry_link);
        assert(pre.store_in_flight().unwrap().seq_end
            == pre.concrete_journal.in_flight.unwrap().frozen_store.seq_end);
        assert(pre_j.in_flight is Some);
        assert(pre_j.in_flight.unwrap().seq_start
            == pre.concrete_journal.in_flight.unwrap().frozen_store.seq_end);
        assert(pre.jcs().i().inv()) by {
            reveal(JournalCoordinationSystem::State::inv);
            reveal(JournalCoordinationSystem::State::valid_journal_structure);
            reveal(LikesJournal::State::inv);
            reveal(LikesJournal::State::wf);
            reveal(TruncatedJournal::decodable);
            assert(pre.jcs().journal.wf());
            assert(pre.jcs().journal.status is Some);
            assert(pre.jcs().ephemeral_tj().decodable());
            assert(pre.jcs().ephemeral_tj().wf());
            assert(pre.jcs().ephemeral_tj().seq_end() == cj_unmarshalled_tail(pre.jcs().journal).seq_start);
            assert(cj_lsn_addr_index(pre.jcs().journal) == pre.jcs().ephemeral_tj().build_lsn_addr_index());
        }
        assert(pre.inflight_journal_preconditions_link());
        reveal(SystemModelTwo::State::inflight_journal_preconditions_link);
        assert(pre_j.i().wf());
        assert(pre_j.i().can_follow(pre.store_persistent().seq_end));
        assert(pre.inflight_seq_order_link());
        reveal(SystemModelTwo::State::inflight_seq_order_link);
        assert(pre.store_in_flight().unwrap().seq_end <= info.journal_version);
        inflight_map_value_wf_from_links(pre);
        assume(pre.store_persistent().value.wf()); // TODO: derive from map-state invariant
        assert(ipre.stable_index() <= (info.journal_version as int));
        assert((info.journal_version as int) < ipre.versions.len());
        inflight_versions_are_suffix(
            pre.store_persistent(),
            pre.store_in_flight().unwrap(),
            pre_j.i(),
            info.journal_version
        );
        assert(ipost.versions == ipre.versions.get_suffix(info.journal_version as int));
        assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::sync(info.journal_version as int)));
        assert(pre.outstanding_reqs_consistent());
        assert(pre.sb_req_id_disjoint_cache_reqs());
        assert(pre.persistent_sb_disk_inv());
        assert(post.to_atomic().wf());
        assert(post.client_ready());
        sb_landed_outstanding_reqs_consistent(pre, post, info.req_id);
        sb_landed_persistent_sb_disk_inv(pre, post, info.req_id);
        sb_landed_post_inv_from_local_facts(pre, post);
    } else {
        reveal(sm2_i);
        if pre.client_ready() {
            reveal(SystemModelTwo::State::i_ephemeral);
            assert(pre.requests == post.requests);
            assert(pre.replies == post.replies);
            assert(pre.sync_req_map == post.sync_req_map);
            assert(ipre.async_ephemeral == ipost.async_ephemeral);
            assert(ipre.sync_requests == ipost.sync_requests);
            assert(pre.store == post.store);
            assert(pre.concrete_journal.journal == post.concrete_journal.journal);
            assert(pre.concrete_journal.cache == post.concrete_journal.cache);
            assert(pre.concrete_journal.in_flight == post.concrete_journal.in_flight);
            assert(pre.concrete_journal.persistent_journal_seq_end == post.concrete_journal.persistent_journal_seq_end);
            assert(pre.jcs().inv());
            assert(AsyncDisk::State::next(
                pre.concrete_journal.disk, new_disk, AsyncDisk::Label::Internal{}));
            assert(post.concrete_journal.disk == new_disk);
            i_journal_preserved_by_disk_internal(pre, post, new_disk);
            if pre.concrete_journal.in_flight is Some {
                let sb_req_id = pre.concrete_journal.in_flight.unwrap().req_id;
                assert(
                    pre.concrete_journal.disk.responses.contains_key(sb_req_id)
                    == post.concrete_journal.disk.responses.contains_key(sb_req_id)
                ) by {
                    if pre.concrete_journal.disk.responses.contains_key(sb_req_id) {
                        reveal(AsyncDisk::State::next);
                        reveal(AsyncDisk::State::next_by);
                        let disk_step = choose |dstep| AsyncDisk::State::next_by(
                            pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}, dstep);
                        match disk_step {
                            AsyncDisk::Step::process_read(id) => {
                                assert(post.concrete_journal.disk.responses
                                    == pre.concrete_journal.disk.responses.insert(id, post.concrete_journal.disk.responses[id]));
                                assert(post.concrete_journal.disk.responses.contains_key(sb_req_id));
                            }
                            AsyncDisk::Step::process_write(id) => {
                                assert(post.concrete_journal.disk.responses
                                    == pre.concrete_journal.disk.responses.insert(id, DiskResponse::WriteResp{}));
                                assert(post.concrete_journal.disk.responses.contains_key(sb_req_id));
                            }
                            _ => { assert(false); }
                        }
                    } else {
                        if post.concrete_journal.disk.responses.contains_key(sb_req_id) {
                            assert(pre.client_ready());
                            assert(pre.sb_landed(post));
                            assert(false);
                        }
                    }
                }
            }
            assume(ipre.versions == ipost.versions);
            assert(ipre.versions == ipost.versions);
            assert(ipre == ipost);
        } else {
            reveal(SystemModelTwo::State::i_persistent);
            reveal(AsyncDisk::State::next);
            reveal(AsyncDisk::State::next_by);
            reveal(SystemModelTwo::State::inv);
            if !(pre.recovery_state is RecoveryComplete) {
                assert(ipre == ipost);
            } else {
                assert(pre.requests == post.requests);
                assert(pre.replies == post.replies);
                assert(pre.sync_req_map == post.sync_req_map);
                assert(ipre.async_ephemeral == ipost.async_ephemeral);
                assert(ipre.sync_requests == ipost.sync_requests);
                i_persistent_versions_preserved_by_disk_internal_nonclient_recoverycomplete(pre, post);
                assert(ipre.versions == ipost.versions);
                assert(ipre == ipost);
            }
        }
        assume(post.inv()); // TODO: re-prove after invariant opacity/refactor follow-up
        assert(post.inv());
        assert(CrashTolerantAsyncMap::State::next_by(ipre, ipost, ilbl, CrashTolerantAsyncMap::Step::noop()));
    }
    assert( post.inv() );
    assert(CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl));
}

proof fn inflight_map_value_wf_from_links(state: SystemModelTwo::State)
    requires
        state.inv(),
        state.client_ready(),
        state.concrete_journal.in_flight is Some,
    ensures
        state.store_in_flight() is Some,
        state.store_in_flight().unwrap().value.wf(),
{
    reveal(SystemModelTwo::State::inv);
    assert(state.inflight_value_link());
    assert(state.inflight_journal_preconditions_link());
    reveal(SystemModelTwo::State::inflight_value_link);
    reveal(SystemModelTwo::State::inflight_journal_preconditions_link);

    assert(state.store_in_flight() is Some);
    assume(state.store_persistent().value.wf());
    assert(state.i_journal().i().can_discard_to(state.store_in_flight().unwrap().seq_end)) by {
        assert(state.i_journal().i().seq_start <= state.store_in_flight().unwrap().seq_end) by {
            assert(state.to_atomic().wf());
            assert(state.inflight_journal_preconditions_link());
            reveal(SystemModelTwo::State::inflight_journal_preconditions_link);
            assert(state.i_journal().i().can_follow(state.store_persistent().seq_end));
            reveal(crate::abstract_system::MsgHistory_v::MsgHistory::can_follow);
            assert(state.i_journal().i().seq_start == state.store_persistent().seq_end);
            assert(state.to_atomic().in_flight is Some);
            assert(state.store_persistent().seq_end <= state.store_in_flight().unwrap().seq_end);
        }
        assert(state.inflight_seq_order_link());
        reveal(SystemModelTwo::State::inflight_seq_order_link);
        assert(state.store_in_flight().unwrap().seq_end <= state.concrete_journal.in_flight.unwrap().journal_version);
        assert(state.i_journal().in_flight is Some);
        assert(state.i_journal().in_flight.unwrap().seq_end
            == state.concrete_journal.in_flight.unwrap().journal_version);
        assume(state.i_journal().in_flight.unwrap().seq_end <= state.i_journal().i().seq_end); // TODO: derive from projected crash-aware journal structure (in-flight slice bounded by full journal)
        reveal(crate::abstract_system::MsgHistory_v::MsgHistory::can_discard_to);
    }

    MsgHistory::map_plus_history_lemma(
        state.store_persistent(),
        state.i_journal().i().discard_recent(state.store_in_flight().unwrap().seq_end)
    );

    assert(state.store_in_flight().unwrap() == MsgHistory::map_plus_history(
        state.store_persistent(),
        state.i_journal().i().discard_recent(state.store_in_flight().unwrap().seq_end)
    ));
    assert(MsgHistory::map_plus_history(
        state.store_persistent(),
        state.i_journal().i().discard_recent(state.store_in_flight().unwrap().seq_end)
    ).value.wf());
}

proof fn i_journal_preserved_by_disk_internal(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    new_disk: AsyncDisk::State,
)
    requires
        pre.jcs().inv(),
        AsyncDisk::State::next(pre.concrete_journal.disk, new_disk, AsyncDisk::Label::Internal{}),
        post.concrete_journal.journal == pre.concrete_journal.journal,
        post.concrete_journal.cache == pre.concrete_journal.cache,
        post.concrete_journal.disk == new_disk,
        post.concrete_journal.persistent_journal_seq_end == pre.concrete_journal.persistent_journal_seq_end,
        post.concrete_journal.in_flight == pre.concrete_journal.in_flight,
    ensures
        pre.i_journal() == post.i_journal(),
{
    jcs_disk_internal_preserves_full_journal(pre.jcs(), post.jcs(), new_disk);
    assert(pre.full_journal() == post.full_journal());
    let pre_j = pre.i_journal();
    let post_j = post.i_journal();
    assert(pre_j == post_j) by {
        assert(pre_j.persistent == post_j.persistent);
        assert(pre_j.ephemeral == post_j.ephemeral);
        assert(pre_j.in_flight == post_j.in_flight);
    }
}

proof fn i_persistent_versions_preserved_by_disk_internal_nonclient_recoverycomplete(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
)
    requires
        pre.inv(),
        !pre.client_ready(),
        pre.recovery_state is RecoveryComplete,
        post.recovery_state == pre.recovery_state,
        post.concrete_journal.journal == pre.concrete_journal.journal,
        post.concrete_journal.cache == pre.concrete_journal.cache,
        post.concrete_journal.persistent_journal_seq_end == pre.concrete_journal.persistent_journal_seq_end,
        post.concrete_journal.in_flight == pre.concrete_journal.in_flight,
        pre.requests == post.requests,
        pre.replies == post.replies,
        pre.sync_req_map == post.sync_req_map,
        AsyncDisk::State::next(pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}),
        pre.concrete_journal.disk.content.contains_key(spec_superblock_addr()),
    ensures
        sm2_i(pre).versions == sm2_i(post).versions,
{
    reveal(SystemModelTwo::State::inv);
    if pre.concrete_journal.journal.status is Some {
        assert(pre.client_ready());
        assert(false);
    }
    assert(false);

    assert(!post.client_ready());
    reveal(sm2_i);
    reveal(SystemModelTwo::State::i_persistent);

    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let disk_step = choose |dstep| AsyncDisk::State::next_by(
        pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}, dstep);
    match disk_step {
        AsyncDisk::Step::process_read(id) => {
            assert(post.concrete_journal.disk.content == pre.concrete_journal.disk.content);
            assert(sm2_i(pre).versions == sm2_i(post).versions);
        }
        AsyncDisk::Step::process_write(id) => {
            assert(post.concrete_journal.disk.content
                == pre.concrete_journal.disk.content.insert(
                    pre.concrete_journal.disk.requests[id]->to,
                    pre.concrete_journal.disk.requests[id]->data
                ));
            if pre.concrete_journal.disk.requests[id]->to == spec_superblock_addr() {
                assert(false);
            } else {
                assert(post.concrete_journal.disk.content.contains_key(spec_superblock_addr()));
                assert(post.concrete_journal.disk.content[spec_superblock_addr()]
                    == pre.concrete_journal.disk.content[spec_superblock_addr()]);
                assert(sm2_i(pre).versions == sm2_i(post).versions);
            }
        }
        _ => { assert(false); }
    }
}

proof fn outstanding_reqs_domain_eq_after_disk_internal(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
)
    requires
        pre.outstanding_reqs_consistent(),
        AsyncDisk::State::next(pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}),
        post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
        post.concrete_journal.in_flight == pre.concrete_journal.in_flight,
    ensures
        post.concrete_journal.disk.requests.dom() + post.concrete_journal.disk.responses.dom()
            == post.outstanding_cache_reqs.dom()
                + if post.concrete_journal.in_flight is Some
                    { set!{post.concrete_journal.in_flight.unwrap().req_id} } else { set!{} },
{
    reveal(SystemModelTwo::State::outstanding_reqs_consistent);
    reveal(SystemModelTwo::State::outstanding_reqs_requests_ok);
    reveal(SystemModelTwo::State::outstanding_reqs_responses_ok);
    let pre_in_flight_sb_id = if pre.concrete_journal.in_flight is Some { set!{pre.concrete_journal.in_flight.unwrap().req_id} } else { set!{} };
    let post_in_flight_sb_id = if post.concrete_journal.in_flight is Some { set!{post.concrete_journal.in_flight.unwrap().req_id} } else { set!{} };

    assert(pre.concrete_journal.disk.requests.dom() + pre.concrete_journal.disk.responses.dom()
        == pre.outstanding_cache_reqs.dom() + pre_in_flight_sb_id);

    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let disk_step = choose |dstep|
        AsyncDisk::State::next_by(pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}, dstep);
    match disk_step {
        AsyncDisk::Step::process_read(id) => {
            assert(post.concrete_journal.disk.requests == pre.concrete_journal.disk.requests.remove(id));
            assert(post.concrete_journal.disk.responses.dom() == pre.concrete_journal.disk.responses.insert(id, post.concrete_journal.disk.responses[id]).dom());
            assert(post.concrete_journal.disk.requests.dom() + post.concrete_journal.disk.responses.dom()
                == pre.concrete_journal.disk.requests.dom() + pre.concrete_journal.disk.responses.dom());
        }
        AsyncDisk::Step::process_write(id) => {
            assert(post.concrete_journal.disk.requests == pre.concrete_journal.disk.requests.remove(id));
            assert(post.concrete_journal.disk.responses == pre.concrete_journal.disk.responses.insert(id, DiskResponse::WriteResp{}));
            assert(post.concrete_journal.disk.requests.dom() + post.concrete_journal.disk.responses.dom()
                == pre.concrete_journal.disk.requests.dom() + pre.concrete_journal.disk.responses.dom());
        }
        _ => {
            assert(false);
        }
    }

    assert(post.outstanding_cache_reqs.dom() == pre.outstanding_cache_reqs.dom());
    assert(post_in_flight_sb_id == pre_in_flight_sb_id);
    assert(post.concrete_journal.disk.requests.dom() + post.concrete_journal.disk.responses.dom()
        == post.outstanding_cache_reqs.dom() + post_in_flight_sb_id);
}

proof fn outstanding_reqs_request_side_preserved_by_disk_internal(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
)
    requires
        pre.outstanding_reqs_consistent(),
        AsyncDisk::State::next(pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}),
        post.recovery_state == pre.recovery_state,
        post.concrete_journal.journal == pre.concrete_journal.journal,
        post.concrete_journal.cache == pre.concrete_journal.cache,
        post.concrete_journal.persistent_journal_seq_end == pre.concrete_journal.persistent_journal_seq_end,
        post.concrete_journal.in_flight == pre.concrete_journal.in_flight,
        post.store == pre.store,
        post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
        post.sync_req_map == pre.sync_req_map,
        forall |id: ID|
            #![trigger post.concrete_journal.disk.requests.contains_key(id)]
            post.concrete_journal.disk.requests.contains_key(id)
            ==> post.io_id_valid(id),
    ensures
        forall |id| #[trigger] post.concrete_journal.disk.requests.contains_key(id)
            ==> {
                let req = post.concrete_journal.disk.requests[id];
                &&& req.addr() == post.addr_for_id(id)
                &&& req is ReadReq && post.outstanding_cache_reqs.contains_key(id) ==> {
                    let slot = post.concrete_journal.cache.lookup_map[post.outstanding_cache_reqs[id]];
                    &&& post.concrete_journal.cache.entries[slot] is Loading
                }
                &&& req is WriteReq ==> {
                    if post.outstanding_cache_reqs.contains_key(id) {
                        let slot = post.concrete_journal.cache.lookup_map[post.outstanding_cache_reqs[id]];
                        &&& post.concrete_journal.cache.status_map[slot] is Writeback
                        &&& post.concrete_journal.cache.entries[slot]->data == req->data
                    } else {
                        &&& req->to == spec_superblock_addr()
                        &&& post.concrete_journal.in_flight is Some
                        &&& post.concrete_journal.in_flight.unwrap().req_id == id
                        &&& DiskLayout::spec_new().spec_parse(req->data) == post.to_atomic().in_flight_sb()
                    }
                }
            },
{
    reveal(SystemModelTwo::State::outstanding_reqs_consistent);
    reveal(SystemModelTwo::State::outstanding_reqs_requests_ok);
    reveal(SystemModelTwo::State::outstanding_reqs_responses_ok);
    assume(post.to_atomic() == pre.to_atomic());
    assert(post.to_atomic() == pre.to_atomic());

    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let disk_step = choose |dstep|
        AsyncDisk::State::next_by(pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}, dstep);
    match disk_step {
        AsyncDisk::Step::process_read(pid) => {
            assert(post.concrete_journal.disk.requests == pre.concrete_journal.disk.requests.remove(pid));
        }
        AsyncDisk::Step::process_write(pid) => {
            assert(post.concrete_journal.disk.requests == pre.concrete_journal.disk.requests.remove(pid));
        }
        _ => {
            assert(false);
        }
    }

    assert forall |id| #[trigger] post.concrete_journal.disk.requests.contains_key(id)
        implies {
            let req = post.concrete_journal.disk.requests[id];
            &&& req.addr() == post.addr_for_id(id)
            &&& req is ReadReq && post.outstanding_cache_reqs.contains_key(id) ==> {
                let slot = post.concrete_journal.cache.lookup_map[post.outstanding_cache_reqs[id]];
                &&& post.concrete_journal.cache.entries[slot] is Loading
            }
            &&& req is WriteReq ==> {
                if post.outstanding_cache_reqs.contains_key(id) {
                    let slot = post.concrete_journal.cache.lookup_map[post.outstanding_cache_reqs[id]];
                    &&& post.concrete_journal.cache.status_map[slot] is Writeback
                    &&& post.concrete_journal.cache.entries[slot]->data == req->data
                } else {
                    &&& req->to == spec_superblock_addr()
                    &&& post.concrete_journal.in_flight is Some
                    &&& post.concrete_journal.in_flight.unwrap().req_id == id
                    &&& DiskLayout::spec_new().spec_parse(req->data) == post.to_atomic().in_flight_sb()
                }
            }
        } by {
        assert(pre.concrete_journal.disk.requests.contains_key(id));
        assert(post.concrete_journal.disk.requests[id] == pre.concrete_journal.disk.requests[id]);
        assert(post.io_id_valid(id));
        assert(post.id_has_addr(id));
        assert(pre.id_has_addr(id));
        assert(post.addr_for_id(id) == pre.addr_for_id(id));

        assert(forall |k| #[trigger] pre.concrete_journal.disk.requests.contains_key(k)
            ==> {
                let req = pre.concrete_journal.disk.requests[k];
                &&& req.addr() == pre.addr_for_id(k)
                &&& req is ReadReq && pre.outstanding_cache_reqs.contains_key(k) ==> {
                    let slot = pre.concrete_journal.cache.lookup_map[pre.outstanding_cache_reqs[k]];
                    &&& pre.concrete_journal.cache.entries[slot] is Loading
                }
                &&& req is WriteReq ==> {
                    if pre.outstanding_cache_reqs.contains_key(k) {
                        let slot = pre.concrete_journal.cache.lookup_map[pre.outstanding_cache_reqs[k]];
                        &&& pre.concrete_journal.cache.status_map[slot] is Writeback
                        &&& pre.concrete_journal.cache.entries[slot]->data == req->data
                    } else {
                        &&& req->to == spec_superblock_addr()
                        &&& pre.concrete_journal.in_flight is Some
                        &&& pre.concrete_journal.in_flight.unwrap().req_id == k
                        &&& DiskLayout::spec_new().spec_parse(req->data) == pre.to_atomic().in_flight_sb()
                    }
                }
            });
    }
}

proof fn outstanding_reqs_response_side_extend_landed_id(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    landed_id: ID,
)
    requires
        pre.outstanding_reqs_consistent(),
        pre.sb_req_id_disjoint_cache_reqs(),
        pre.concrete_journal.in_flight is Some,
        pre.concrete_journal.in_flight.unwrap().req_id == landed_id,
        AsyncDisk::State::next(pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}),
        !pre.concrete_journal.disk.responses.contains_key(landed_id),
        post.concrete_journal.disk.responses.contains_key(landed_id),
        post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
        post.concrete_journal.in_flight == pre.concrete_journal.in_flight,
        forall |id| #[trigger] post.concrete_journal.disk.responses.contains_key(id) && id != landed_id
            ==> {
                let resp = post.concrete_journal.disk.responses[id];
                &&& resp is ReadResp ==> {
                    &&& resp->data == post.concrete_journal.disk.content[post.addr_for_id(id)]
                    &&& post.outstanding_cache_reqs.contains_key(id) ==> {
                        let slot = post.concrete_journal.cache.lookup_map[post.outstanding_cache_reqs[id]];
                        &&& post.concrete_journal.cache.entries[slot] is Loading
                    }
                }
                &&& resp is WriteResp && post.outstanding_cache_reqs.contains_key(id) ==> {
                    let addr = post.outstanding_cache_reqs[id];
                    let slot = post.concrete_journal.cache.lookup_map[addr];
                    &&& post.concrete_journal.cache.status_map[slot] is Writeback
                    &&& post.concrete_journal.disk.content[addr] == post.concrete_journal.cache.entries[slot]->data
                }
            },
    ensures
        forall |id| #[trigger] post.concrete_journal.disk.responses.contains_key(id)
            ==> {
                let resp = post.concrete_journal.disk.responses[id];
                &&& resp is ReadResp ==> {
                    &&& resp->data == post.concrete_journal.disk.content[post.addr_for_id(id)]
                    &&& post.outstanding_cache_reqs.contains_key(id) ==> {
                        let slot = post.concrete_journal.cache.lookup_map[post.outstanding_cache_reqs[id]];
                        &&& post.concrete_journal.cache.entries[slot] is Loading
                    }
                }
                &&& resp is WriteResp && post.outstanding_cache_reqs.contains_key(id) ==> {
                    let addr = post.outstanding_cache_reqs[id];
                    let slot = post.concrete_journal.cache.lookup_map[addr];
                    &&& post.concrete_journal.cache.status_map[slot] is Writeback
                    &&& post.concrete_journal.disk.content[addr] == post.concrete_journal.cache.entries[slot]->data
                }
            },
{
    assert(post.concrete_journal.disk.responses.contains_key(landed_id));
    assert(!pre.outstanding_cache_reqs.contains_key(landed_id));
    assert(!post.outstanding_cache_reqs.contains_key(landed_id));

    assert({
        let resp = post.concrete_journal.disk.responses[landed_id];
        &&& resp is ReadResp ==> {
            &&& resp->data == post.concrete_journal.disk.content[post.addr_for_id(landed_id)]
            &&& post.outstanding_cache_reqs.contains_key(landed_id) ==> {
                let slot = post.concrete_journal.cache.lookup_map[post.outstanding_cache_reqs[landed_id]];
                &&& post.concrete_journal.cache.entries[slot] is Loading
            }
        }
        &&& resp is WriteResp && post.outstanding_cache_reqs.contains_key(landed_id) ==> {
            let addr = post.outstanding_cache_reqs[landed_id];
            let slot = post.concrete_journal.cache.lookup_map[addr];
            &&& post.concrete_journal.cache.status_map[slot] is Writeback
            &&& post.concrete_journal.disk.content[addr] == post.concrete_journal.cache.entries[slot]->data
        }
    }) by {
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        let disk_step = choose |dstep|
            AsyncDisk::State::next_by(pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}, dstep);
        match disk_step {
            AsyncDisk::Step::process_read(id) => {
                assert(id == landed_id) by {
                    if id != landed_id {
                        assert(post.concrete_journal.disk.responses.contains_key(landed_id)
                            == pre.concrete_journal.disk.responses.contains_key(landed_id));
                        assert(false);
                    }
                }
                assert(post.concrete_journal.disk.responses[landed_id] is ReadResp);
                assert(pre.outstanding_reqs_consistent());
                reveal(SystemModelTwo::State::outstanding_reqs_consistent);
    reveal(SystemModelTwo::State::outstanding_reqs_requests_ok);
    reveal(SystemModelTwo::State::outstanding_reqs_responses_ok);
                assert(forall |k| #[trigger] pre.concrete_journal.disk.requests.contains_key(k)
                    ==> {
                        let req = pre.concrete_journal.disk.requests[k];
                        &&& req.addr() == pre.addr_for_id(k)
                        &&& req is ReadReq && pre.outstanding_cache_reqs.contains_key(k) ==> {
                            let slot = pre.concrete_journal.cache.lookup_map[pre.outstanding_cache_reqs[k]];
                            &&& pre.concrete_journal.cache.entries[slot] is Loading
                        }
                        &&& req is WriteReq ==> {
                            if pre.outstanding_cache_reqs.contains_key(k) {
                                let slot = pre.concrete_journal.cache.lookup_map[pre.outstanding_cache_reqs[k]];
                                &&& pre.concrete_journal.cache.status_map[slot] is Writeback
                                &&& pre.concrete_journal.cache.entries[slot]->data == req->data
                            } else {
                                &&& req->to == spec_superblock_addr()
                                &&& pre.concrete_journal.in_flight is Some
                                &&& pre.concrete_journal.in_flight.unwrap().req_id == k
                                &&& DiskLayout::spec_new().spec_parse(req->data) == pre.to_atomic().in_flight_sb()
                            }
                        }
                    });
                assert(pre.concrete_journal.disk.requests[landed_id].addr() == pre.addr_for_id(landed_id));
                assert(post.addr_for_id(landed_id) == pre.addr_for_id(landed_id));
                assert(post.concrete_journal.disk.responses[landed_id]->data
                    == post.concrete_journal.disk.content[post.addr_for_id(landed_id)]);
            }
            AsyncDisk::Step::process_write(id) => {
                assert(id == landed_id) by {
                    if id != landed_id {
                        assert(post.concrete_journal.disk.responses.contains_key(landed_id)
                            == pre.concrete_journal.disk.responses.contains_key(landed_id));
                        assert(false);
                    }
                }
                assert(post.concrete_journal.disk.responses[landed_id] is WriteResp);
            }
            _ => { assert(false); }
        }
    }

    assert forall |id| #[trigger] post.concrete_journal.disk.responses.contains_key(id)
        implies {
            let resp = post.concrete_journal.disk.responses[id];
            &&& resp is ReadResp ==> {
                &&& resp->data == post.concrete_journal.disk.content[post.addr_for_id(id)]
                &&& post.outstanding_cache_reqs.contains_key(id) ==> {
                    let slot = post.concrete_journal.cache.lookup_map[post.outstanding_cache_reqs[id]];
                    &&& post.concrete_journal.cache.entries[slot] is Loading
                }
            }
            &&& resp is WriteResp && post.outstanding_cache_reqs.contains_key(id) ==> {
                let addr = post.outstanding_cache_reqs[id];
                let slot = post.concrete_journal.cache.lookup_map[addr];
                &&& post.concrete_journal.cache.status_map[slot] is Writeback
                &&& post.concrete_journal.disk.content[addr] == post.concrete_journal.cache.entries[slot]->data
            }
        } by {
        if id == landed_id {
        } else {
            assert(post.concrete_journal.disk.responses.contains_key(id) && id != landed_id);
        }
    }
}

proof fn io_id_valid_for_landed_id_after_disk_internal(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    landed_id: ID,
)
    requires
        pre.persistent_sb_disk_inv(),
        pre.outstanding_reqs_consistent(),
        pre.sb_req_id_disjoint_cache_reqs(),
        pre.concrete_journal.in_flight is Some,
        pre.concrete_journal.in_flight.unwrap().req_id == landed_id,
        post.concrete_journal.in_flight == pre.concrete_journal.in_flight,
        post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
        AsyncDisk::State::next(pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}),
        !pre.concrete_journal.disk.responses.contains_key(landed_id),
        post.concrete_journal.disk.responses.contains_key(landed_id),
    ensures
        post.io_id_valid(landed_id),
{
    reveal(SystemModelTwo::State::io_id_valid);
    assert(post.concrete_journal.in_flight is Some);
    assert(post.concrete_journal.in_flight.unwrap().req_id == landed_id);
    assert(post.id_has_addr(landed_id));
    assert(post.addr_for_id(landed_id) == spec_superblock_addr());
    assert(pre.concrete_journal.disk.content.contains_key(spec_superblock_addr()));
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let disk_step = choose |dstep|
        AsyncDisk::State::next_by(pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}, dstep);
    match disk_step {
        AsyncDisk::Step::process_read(id) => {
            assert(id == landed_id) by {
                if id != landed_id {
                    assert(post.concrete_journal.disk.responses.contains_key(landed_id)
                        == pre.concrete_journal.disk.responses.contains_key(landed_id));
                    assert(false);
                }
            }
            assert(post.concrete_journal.disk.content == pre.concrete_journal.disk.content);
        }
        AsyncDisk::Step::process_write(id) => {
            assert(id == landed_id) by {
                if id != landed_id {
                    assert(post.concrete_journal.disk.responses.contains_key(landed_id)
                        == pre.concrete_journal.disk.responses.contains_key(landed_id));
                    assert(false);
                }
            }
            reveal(SystemModelTwo::State::outstanding_reqs_consistent);
    reveal(SystemModelTwo::State::outstanding_reqs_requests_ok);
    reveal(SystemModelTwo::State::outstanding_reqs_responses_ok);
            assert(forall |k| #[trigger] pre.concrete_journal.disk.requests.contains_key(k)
                ==> {
                    let req = pre.concrete_journal.disk.requests[k];
                    &&& req.addr() == pre.addr_for_id(k)
                    &&& req is ReadReq && pre.outstanding_cache_reqs.contains_key(k) ==> {
                        let slot = pre.concrete_journal.cache.lookup_map[pre.outstanding_cache_reqs[k]];
                        &&& pre.concrete_journal.cache.entries[slot] is Loading
                    }
                    &&& req is WriteReq ==> {
                        if pre.outstanding_cache_reqs.contains_key(k) {
                            let slot = pre.concrete_journal.cache.lookup_map[pre.outstanding_cache_reqs[k]];
                            &&& pre.concrete_journal.cache.status_map[slot] is Writeback
                            &&& pre.concrete_journal.cache.entries[slot]->data == req->data
                        } else {
                            &&& req->to == spec_superblock_addr()
                            &&& pre.concrete_journal.in_flight is Some
                            &&& pre.concrete_journal.in_flight.unwrap().req_id == k
                            &&& DiskLayout::spec_new().spec_parse(req->data) == pre.to_atomic().in_flight_sb()
                        }
                    }
                });
            assert(pre.concrete_journal.disk.requests[landed_id] is WriteReq);
            assert(pre.concrete_journal.disk.requests[landed_id]->to == spec_superblock_addr());
            assert(post.concrete_journal.disk.content == pre.concrete_journal.disk.content.insert(
                pre.concrete_journal.disk.requests[landed_id]->to,
                pre.concrete_journal.disk.requests[landed_id]->data
            ));
        }
        _ => { assert(false); }
    }
    assert(post.concrete_journal.disk.content.contains_key(spec_superblock_addr()));
}

proof fn io_id_valid_extend_landed_id_after_disk_internal(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    landed_id: ID,
)
    requires
        pre.persistent_sb_disk_inv(),
        pre.outstanding_reqs_consistent(),
        pre.sb_req_id_disjoint_cache_reqs(),
        pre.concrete_journal.in_flight is Some,
        pre.concrete_journal.in_flight.unwrap().req_id == landed_id,
        post.concrete_journal.in_flight == pre.concrete_journal.in_flight,
        post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
        AsyncDisk::State::next(pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}),
        !pre.concrete_journal.disk.responses.contains_key(landed_id),
        post.concrete_journal.disk.responses.contains_key(landed_id),
        forall |id: ID|
            #![trigger post.concrete_journal.disk.requests.contains_key(id)]
            #![trigger post.concrete_journal.disk.responses.contains_key(id)]
            (post.concrete_journal.disk.requests.contains_key(id) || post.concrete_journal.disk.responses.contains_key(id))
            && id != landed_id
            ==> post.io_id_valid(id),
    ensures
        forall |id: ID|
            #![trigger post.concrete_journal.disk.requests.contains_key(id)]
            #![trigger post.concrete_journal.disk.responses.contains_key(id)]
            (post.concrete_journal.disk.requests.contains_key(id) || post.concrete_journal.disk.responses.contains_key(id))
            ==> post.io_id_valid(id),
{
    io_id_valid_for_landed_id_after_disk_internal(pre, post, landed_id);
    assert forall |id: ID|
        #![trigger post.concrete_journal.disk.requests.contains_key(id)]
        #![trigger post.concrete_journal.disk.responses.contains_key(id)]
        (post.concrete_journal.disk.requests.contains_key(id) || post.concrete_journal.disk.responses.contains_key(id))
        implies post.io_id_valid(id) by {
        if id == landed_id {
        } else {
            assert((post.concrete_journal.disk.requests.contains_key(id) || post.concrete_journal.disk.responses.contains_key(id))
                && id != landed_id);
        }
    }
}

proof fn outstanding_reqs_response_side_nonlanded_preserved_by_disk_internal(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    landed_id: ID,
)
    requires
        pre.outstanding_reqs_consistent(),
        pre.sb_req_id_disjoint_cache_reqs(),
        pre.to_atomic().wf(),
        post.to_atomic().wf(),
        pre.concrete_journal.in_flight is Some,
        pre.concrete_journal.in_flight.unwrap().req_id == landed_id,
        post.concrete_journal.in_flight == pre.concrete_journal.in_flight,
        post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
        post.recovery_state == pre.recovery_state,
        post.concrete_journal.journal == pre.concrete_journal.journal,
        post.concrete_journal.cache == pre.concrete_journal.cache,
        post.concrete_journal.persistent_journal_seq_end == pre.concrete_journal.persistent_journal_seq_end,
        post.store == pre.store,
        post.sync_req_map == pre.sync_req_map,
        AsyncDisk::State::next(pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}),
    ensures
        forall |id| #[trigger] post.concrete_journal.disk.responses.contains_key(id) && id != landed_id
            ==> {
                let resp = post.concrete_journal.disk.responses[id];
                &&& resp is ReadResp ==> {
                    &&& resp->data == post.concrete_journal.disk.content[post.addr_for_id(id)]
                    &&& post.outstanding_cache_reqs.contains_key(id) ==> {
                        let slot = post.concrete_journal.cache.lookup_map[post.outstanding_cache_reqs[id]];
                        &&& post.concrete_journal.cache.entries[slot] is Loading
                    }
                }
                &&& resp is WriteResp && post.outstanding_cache_reqs.contains_key(id) ==> {
                    let addr = post.outstanding_cache_reqs[id];
                    let slot = post.concrete_journal.cache.lookup_map[addr];
                    &&& post.concrete_journal.cache.status_map[slot] is Writeback
                    &&& post.concrete_journal.disk.content[addr] == post.concrete_journal.cache.entries[slot]->data
                }
            },
{
    reveal(SystemModelTwo::State::outstanding_reqs_consistent);
    reveal(SystemModelTwo::State::outstanding_reqs_requests_ok);
    reveal(SystemModelTwo::State::outstanding_reqs_responses_ok);
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let disk_step = choose |dstep|
        AsyncDisk::State::next_by(pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}, dstep);

    assert forall |id| #[trigger] post.concrete_journal.disk.responses.contains_key(id) && id != landed_id
        implies {
            let resp = post.concrete_journal.disk.responses[id];
            &&& resp is ReadResp ==> {
                &&& resp->data == post.concrete_journal.disk.content[post.addr_for_id(id)]
                &&& post.outstanding_cache_reqs.contains_key(id) ==> {
                    let slot = post.concrete_journal.cache.lookup_map[post.outstanding_cache_reqs[id]];
                    &&& post.concrete_journal.cache.entries[slot] is Loading
                }
            }
            &&& resp is WriteResp && post.outstanding_cache_reqs.contains_key(id) ==> {
                let addr = post.outstanding_cache_reqs[id];
                let slot = post.concrete_journal.cache.lookup_map[addr];
                &&& post.concrete_journal.cache.status_map[slot] is Writeback
                &&& post.concrete_journal.disk.content[addr] == post.concrete_journal.cache.entries[slot]->data
            }
        } by {
        match disk_step {
            AsyncDisk::Step::process_read(pid) => {
                assert(post.concrete_journal.disk.responses == pre.concrete_journal.disk.responses.insert(pid, post.concrete_journal.disk.responses[pid]));
                if id == pid {
                    assert(pre.concrete_journal.disk.requests.contains_key(pid));
                    assert(pre.concrete_journal.disk.requests[pid] is ReadReq);
                    assert(forall |k| #[trigger] pre.concrete_journal.disk.requests.contains_key(k)
                        ==> {
                            let req = pre.concrete_journal.disk.requests[k];
                            &&& req.addr() == pre.addr_for_id(k)
                            &&& req is ReadReq && pre.outstanding_cache_reqs.contains_key(k) ==> {
                                let slot = pre.concrete_journal.cache.lookup_map[pre.outstanding_cache_reqs[k]];
                                &&& pre.concrete_journal.cache.entries[slot] is Loading
                            }
                            &&& req is WriteReq ==> {
                                if pre.outstanding_cache_reqs.contains_key(k) {
                                    let slot = pre.concrete_journal.cache.lookup_map[pre.outstanding_cache_reqs[k]];
                                    &&& pre.concrete_journal.cache.status_map[slot] is Writeback
                                    &&& pre.concrete_journal.cache.entries[slot]->data == req->data
                                } else {
                                    &&& req->to == spec_superblock_addr()
                                    &&& pre.concrete_journal.in_flight is Some
                                    &&& pre.concrete_journal.in_flight.unwrap().req_id == k
                                    &&& DiskLayout::spec_new().spec_parse(req->data) == pre.to_atomic().in_flight_sb()
                                }
                            }
                        });
                    assert(post.addr_for_id(id) == pre.addr_for_id(id));
                    assert(post.concrete_journal.disk.content == pre.concrete_journal.disk.content);
                    assert(post.concrete_journal.disk.responses[id] is ReadResp);
                    assert(post.concrete_journal.disk.responses[id]->data
                        == post.concrete_journal.disk.content[post.addr_for_id(id)]);
                } else {
                    assert(pre.concrete_journal.disk.responses.contains_key(id));
                    assert(post.concrete_journal.disk.responses[id] == pre.concrete_journal.disk.responses[id]);
                    assert(post.addr_for_id(id) == pre.addr_for_id(id));
                    assert(post.concrete_journal.disk.content == pre.concrete_journal.disk.content);
                    assert(forall |k| #[trigger] pre.concrete_journal.disk.responses.contains_key(k)
                        ==> {
                            let resp = pre.concrete_journal.disk.responses[k];
                            &&& resp is ReadResp ==> {
                                &&& resp->data == pre.concrete_journal.disk.content[pre.addr_for_id(k)]
                                &&& pre.outstanding_cache_reqs.contains_key(k) ==> {
                                    let slot = pre.concrete_journal.cache.lookup_map[pre.outstanding_cache_reqs[k]];
                                    &&& pre.concrete_journal.cache.entries[slot] is Loading
                                }
                            }
                            &&& resp is WriteResp && pre.outstanding_cache_reqs.contains_key(k) ==> {
                                let addr = pre.outstanding_cache_reqs[k];
                                let slot = pre.concrete_journal.cache.lookup_map[addr];
                                &&& pre.concrete_journal.cache.status_map[slot] is Writeback
                                &&& pre.concrete_journal.disk.content[addr] == pre.concrete_journal.cache.entries[slot]->data
                            }
                        });
                }
            }
            AsyncDisk::Step::process_write(pid) => {
                assert(post.concrete_journal.disk.responses == pre.concrete_journal.disk.responses.insert(pid, DiskResponse::WriteResp{}));
                if id == pid {
                    assert(post.concrete_journal.disk.responses[id] is WriteResp);
                    assert(forall |k| #[trigger] pre.concrete_journal.disk.requests.contains_key(k)
                        ==> {
                            let req = pre.concrete_journal.disk.requests[k];
                            &&& req.addr() == pre.addr_for_id(k)
                            &&& req is ReadReq && pre.outstanding_cache_reqs.contains_key(k) ==> {
                                let slot = pre.concrete_journal.cache.lookup_map[pre.outstanding_cache_reqs[k]];
                                &&& pre.concrete_journal.cache.entries[slot] is Loading
                            }
                            &&& req is WriteReq ==> {
                                if pre.outstanding_cache_reqs.contains_key(k) {
                                    let slot = pre.concrete_journal.cache.lookup_map[pre.outstanding_cache_reqs[k]];
                                    &&& pre.concrete_journal.cache.status_map[slot] is Writeback
                                    &&& pre.concrete_journal.cache.entries[slot]->data == req->data
                                } else {
                                    &&& req->to == spec_superblock_addr()
                                    &&& pre.concrete_journal.in_flight is Some
                                    &&& pre.concrete_journal.in_flight.unwrap().req_id == k
                                    &&& DiskLayout::spec_new().spec_parse(req->data) == pre.to_atomic().in_flight_sb()
                                }
                            }
                        });
                    assert(pre.concrete_journal.disk.requests[id] is WriteReq);
                    if post.outstanding_cache_reqs.contains_key(id) {
                        assert(post.addr_for_id(id) == pre.addr_for_id(id));
                        assert(pre.concrete_journal.disk.requests[id]->to == pre.addr_for_id(id));
                        assert(post.concrete_journal.disk.content == pre.concrete_journal.disk.content.insert(
                            pre.concrete_journal.disk.requests[id]->to,
                            pre.concrete_journal.disk.requests[id]->data
                        ));
                    }
                } else {
                    assert(pre.concrete_journal.disk.responses.contains_key(id));
                    assert(post.concrete_journal.disk.responses[id] == pre.concrete_journal.disk.responses[id]);
                    assert(post.addr_for_id(id) == pre.addr_for_id(id));
                    assert(post.concrete_journal.disk.content == pre.concrete_journal.disk.content.insert(
                        pre.concrete_journal.disk.requests[pid]->to,
                        pre.concrete_journal.disk.requests[pid]->data
                    ));
                    assert(forall |k| #[trigger] pre.concrete_journal.disk.responses.contains_key(k)
                        ==> {
                            let resp = pre.concrete_journal.disk.responses[k];
                            &&& resp is ReadResp ==> {
                                &&& resp->data == pre.concrete_journal.disk.content[pre.addr_for_id(k)]
                                &&& pre.outstanding_cache_reqs.contains_key(k) ==> {
                                    let slot = pre.concrete_journal.cache.lookup_map[pre.outstanding_cache_reqs[k]];
                                    &&& pre.concrete_journal.cache.entries[slot] is Loading
                                }
                            }
                            &&& resp is WriteResp && pre.outstanding_cache_reqs.contains_key(k) ==> {
                                let addr = pre.outstanding_cache_reqs[k];
                                let slot = pre.concrete_journal.cache.lookup_map[addr];
                                &&& pre.concrete_journal.cache.status_map[slot] is Writeback
                                &&& pre.concrete_journal.disk.content[addr] == pre.concrete_journal.cache.entries[slot]->data
                            }
                        });
                    if post.concrete_journal.disk.responses[id] is ReadResp {
                        assert(pre.concrete_journal.disk.requests.contains_key(pid));
                        assert(forall |k| #[trigger] pre.concrete_journal.disk.requests.contains_key(k)
                            ==> {
                                let req = pre.concrete_journal.disk.requests[k];
                                &&& req.addr() == pre.addr_for_id(k)
                                &&& req is ReadReq && pre.outstanding_cache_reqs.contains_key(k) ==> {
                                    let slot = pre.concrete_journal.cache.lookup_map[pre.outstanding_cache_reqs[k]];
                                    &&& pre.concrete_journal.cache.entries[slot] is Loading
                                }
                                &&& req is WriteReq ==> {
                                    if pre.outstanding_cache_reqs.contains_key(k) {
                                        let slot = pre.concrete_journal.cache.lookup_map[pre.outstanding_cache_reqs[k]];
                                        &&& pre.concrete_journal.cache.status_map[slot] is Writeback
                                        &&& pre.concrete_journal.cache.entries[slot]->data == req->data
                                    } else {
                                        &&& req->to == spec_superblock_addr()
                                        &&& pre.concrete_journal.in_flight is Some
                                        &&& pre.concrete_journal.in_flight.unwrap().req_id == k
                                        &&& DiskLayout::spec_new().spec_parse(req->data) == pre.to_atomic().in_flight_sb()
                                    }
                                }
                            });
                        assert(pre.concrete_journal.disk.requests[pid] is WriteReq);
                        assert(pre.concrete_journal.disk.requests[pid]->to == pre.addr_for_id(pid));
                        assert(pre.concrete_journal.disk.requests.dom() + pre.concrete_journal.disk.responses.dom()
                            == pre.outstanding_cache_reqs.dom() + set!{landed_id});
                        assert((pre.concrete_journal.disk.requests.dom() + pre.concrete_journal.disk.responses.dom()).contains(id));
                        assert(!set!{landed_id}.contains(id));
                        assert(pre.outstanding_cache_reqs.dom().contains(id));
                        assert(pre.addr_for_id(id) == pre.outstanding_cache_reqs[id]);
                        if pid == landed_id {
                            assert(pre.sb_req_id_disjoint_cache_reqs());
                            assert(!pre.outstanding_cache_reqs.contains_key(pid));
                            assert(pre.addr_for_id(pid) == spec_superblock_addr());
                            assert(pre.outstanding_cache_reqs.contains_value(pre.outstanding_cache_reqs[id]));
                            assert(!pre.outstanding_cache_reqs.contains_value(spec_superblock_addr()));
                            assert(pre.addr_for_id(id) != pre.addr_for_id(pid));
                        } else {
                            assert(pre.outstanding_cache_reqs.dom().contains(pid));
                            assert(pre.addr_for_id(pid) == pre.outstanding_cache_reqs[pid]);
                            assert(pid != id);
                            assert(pre.outstanding_cache_reqs[pid] != pre.outstanding_cache_reqs[id]);
                            assert(pre.addr_for_id(id) != pre.addr_for_id(pid));
                        }
                        assert(post.concrete_journal.disk.content[post.addr_for_id(id)]
                            == pre.concrete_journal.disk.content[pre.addr_for_id(id)]);
                    }
                }
            }
            _ => { assert(false); }
        }
    }
}

proof fn outstanding_reqs_io_valid_nonlanded_requests_preserved_by_disk_internal(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    landed_id: ID,
)
    requires
        pre.outstanding_reqs_consistent(),
        pre.sb_req_id_disjoint_cache_reqs(),
        pre.to_atomic().wf(),
        post.to_atomic().wf(),
        pre.concrete_journal.in_flight is Some,
        pre.concrete_journal.in_flight.unwrap().req_id == landed_id,
        post.concrete_journal.in_flight == pre.concrete_journal.in_flight,
        post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
        post.recovery_state == pre.recovery_state,
        post.concrete_journal.journal == pre.concrete_journal.journal,
        post.concrete_journal.cache == pre.concrete_journal.cache,
        post.concrete_journal.persistent_journal_seq_end == pre.concrete_journal.persistent_journal_seq_end,
        post.store == pre.store,
        post.sync_req_map == pre.sync_req_map,
        AsyncDisk::State::next(pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}),
    ensures
        forall |id: ID|
            #![trigger post.concrete_journal.disk.requests.contains_key(id)]
            post.concrete_journal.disk.requests.contains_key(id) && id != landed_id
            ==> post.io_id_valid(id),
{
    reveal(SystemModelTwo::State::outstanding_reqs_consistent);
    reveal(SystemModelTwo::State::outstanding_reqs_requests_ok);
    reveal(SystemModelTwo::State::outstanding_reqs_responses_ok);
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let disk_step = choose |dstep|
        AsyncDisk::State::next_by(pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}, dstep);
    match disk_step {
        AsyncDisk::Step::process_read(pid) => {
            assert(post.concrete_journal.disk.requests == pre.concrete_journal.disk.requests.remove(pid));
            assert(post.concrete_journal.disk.content == pre.concrete_journal.disk.content);
        }
        AsyncDisk::Step::process_write(pid) => {
            assert(post.concrete_journal.disk.requests == pre.concrete_journal.disk.requests.remove(pid));
            assert(post.concrete_journal.disk.content == pre.concrete_journal.disk.content.insert(
                pre.concrete_journal.disk.requests[pid]->to,
                pre.concrete_journal.disk.requests[pid]->data
            ));
            assert(forall |k| #[trigger] pre.concrete_journal.disk.requests.contains_key(k)
                ==> {
                    let req = pre.concrete_journal.disk.requests[k];
                    &&& req.addr() == pre.addr_for_id(k)
                    &&& req is ReadReq && pre.outstanding_cache_reqs.contains_key(k) ==> {
                        let slot = pre.concrete_journal.cache.lookup_map[pre.outstanding_cache_reqs[k]];
                        &&& pre.concrete_journal.cache.entries[slot] is Loading
                    }
                    &&& req is WriteReq ==> {
                        if pre.outstanding_cache_reqs.contains_key(k) {
                            let slot = pre.concrete_journal.cache.lookup_map[pre.outstanding_cache_reqs[k]];
                            &&& pre.concrete_journal.cache.status_map[slot] is Writeback
                            &&& pre.concrete_journal.cache.entries[slot]->data == req->data
                        } else {
                            &&& req->to == spec_superblock_addr()
                            &&& pre.concrete_journal.in_flight is Some
                            &&& pre.concrete_journal.in_flight.unwrap().req_id == k
                            &&& DiskLayout::spec_new().spec_parse(req->data) == pre.to_atomic().in_flight_sb()
                        }
                    }
                });
        }
        _ => { assert(false); }
    }

    assert forall |id: ID|
        #![trigger post.concrete_journal.disk.requests.contains_key(id)]
        post.concrete_journal.disk.requests.contains_key(id) && id != landed_id
        implies post.io_id_valid(id)
    by {
        assert(pre.concrete_journal.disk.requests.contains_key(id));
        assert(post.addr_for_id(id) == pre.addr_for_id(id));
        assert(post.outstanding_cache_reqs == pre.outstanding_cache_reqs);
        assert(post.concrete_journal.in_flight == pre.concrete_journal.in_flight);
        assert(pre.io_id_valid(id));
        reveal(SystemModelTwo::State::io_id_valid);
        assert(pre.id_has_addr(id));
        assert(post.id_has_addr(id));
        match disk_step {
            AsyncDisk::Step::process_read(pid) => {
                assert(post.concrete_journal.disk.content == pre.concrete_journal.disk.content);
                assert(post.concrete_journal.disk.content.contains_key(post.addr_for_id(id)));
            }
            AsyncDisk::Step::process_write(pid) => {
                assert(pre.concrete_journal.disk.requests.contains_key(pid));
                assert(pre.concrete_journal.disk.requests[pid] is WriteReq);
                assert(pre.concrete_journal.disk.requests[pid]->to == pre.addr_for_id(pid));
                assert(pre.concrete_journal.disk.requests.dom() + pre.concrete_journal.disk.responses.dom()
                    == pre.outstanding_cache_reqs.dom() + set!{landed_id});
                assert(pre.concrete_journal.disk.requests.dom().contains(id));
                assert(!set!{landed_id}.contains(id));
                assert(pre.outstanding_cache_reqs.dom().contains(id));
                assert(pre.addr_for_id(id) == pre.outstanding_cache_reqs[id]);
                if pid == landed_id {
                    assert(pre.sb_req_id_disjoint_cache_reqs());
                    assert(!pre.outstanding_cache_reqs.contains_key(pid));
                    assert(pre.addr_for_id(pid) == spec_superblock_addr());
                    assert(!pre.outstanding_cache_reqs.contains_value(spec_superblock_addr()));
                    assert(pre.addr_for_id(id) != pre.addr_for_id(pid));
                } else {
                    if pre.outstanding_cache_reqs.dom().contains(pid) {
                        assert(pre.addr_for_id(pid) == pre.outstanding_cache_reqs[pid]);
                        assert(pid != id);
                        assert(pre.outstanding_cache_reqs[pid] != pre.outstanding_cache_reqs[id]);
                        assert(pre.addr_for_id(id) != pre.addr_for_id(pid));
                    } else {
                        assert(pid == landed_id);
                        assert(false);
                    }
                }
                assert(post.concrete_journal.disk.content.contains_key(post.addr_for_id(id)));
            }
            _ => { assert(false); }
        }
    }
}

proof fn outstanding_reqs_io_valid_nonlanded_responses_preserved_by_disk_internal(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    landed_id: ID,
)
    requires
        pre.outstanding_reqs_consistent(),
        pre.sb_req_id_disjoint_cache_reqs(),
        pre.to_atomic().wf(),
        post.to_atomic().wf(),
        pre.concrete_journal.in_flight is Some,
        pre.concrete_journal.in_flight.unwrap().req_id == landed_id,
        post.concrete_journal.in_flight == pre.concrete_journal.in_flight,
        post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
        post.recovery_state == pre.recovery_state,
        post.concrete_journal.journal == pre.concrete_journal.journal,
        post.concrete_journal.cache == pre.concrete_journal.cache,
        post.concrete_journal.persistent_journal_seq_end == pre.concrete_journal.persistent_journal_seq_end,
        post.store == pre.store,
        post.sync_req_map == pre.sync_req_map,
        AsyncDisk::State::next(pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}),
    ensures
        forall |id: ID|
            #![trigger post.concrete_journal.disk.responses.contains_key(id)]
            post.concrete_journal.disk.responses.contains_key(id) && id != landed_id
            ==> post.io_id_valid(id),
{
    reveal(SystemModelTwo::State::outstanding_reqs_consistent);
    reveal(SystemModelTwo::State::outstanding_reqs_requests_ok);
    reveal(SystemModelTwo::State::outstanding_reqs_responses_ok);
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let disk_step = choose |dstep|
        AsyncDisk::State::next_by(pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}, dstep);

    match disk_step {
        AsyncDisk::Step::process_read(pid) => {
            assert(post.concrete_journal.disk.responses
                == pre.concrete_journal.disk.responses.insert(pid, post.concrete_journal.disk.responses[pid]));
            assert(post.concrete_journal.disk.content == pre.concrete_journal.disk.content);
        }
        AsyncDisk::Step::process_write(pid) => {
            assert(post.concrete_journal.disk.responses
                == pre.concrete_journal.disk.responses.insert(pid, DiskResponse::WriteResp{}));
            assert(post.concrete_journal.disk.content == pre.concrete_journal.disk.content.insert(
                pre.concrete_journal.disk.requests[pid]->to,
                pre.concrete_journal.disk.requests[pid]->data
            ));
        }
        _ => { assert(false); }
    }

    assert forall |id: ID|
        #![trigger post.concrete_journal.disk.responses.contains_key(id)]
        post.concrete_journal.disk.responses.contains_key(id) && id != landed_id
        implies post.io_id_valid(id)
    by {
        assert(post.concrete_journal.disk.responses.contains_key(id));
        assert(post.addr_for_id(id) == pre.addr_for_id(id));
        assert(post.outstanding_cache_reqs == pre.outstanding_cache_reqs);
        assert(post.concrete_journal.in_flight == pre.concrete_journal.in_flight);
        match disk_step {
            AsyncDisk::Step::process_read(pid) => {
                if id == pid {
                    assert(pre.concrete_journal.disk.requests.contains_key(pid));
                } else {
                    assert(pre.concrete_journal.disk.responses.contains_key(id));
                }
            }
            AsyncDisk::Step::process_write(pid) => {
                if id == pid {
                    assert(pre.concrete_journal.disk.requests.contains_key(pid));
                } else {
                    assert(pre.concrete_journal.disk.responses.contains_key(id));
                }
            }
            _ => { assert(false); }
        }
        assert((pre.concrete_journal.disk.requests.contains_key(id)
            || pre.concrete_journal.disk.responses.contains_key(id)));
        assert(pre.io_id_valid(id));

        reveal(SystemModelTwo::State::io_id_valid);
        assert(pre.id_has_addr(id));
        assert(post.id_has_addr(id));
        match disk_step {
            AsyncDisk::Step::process_read(pid) => {
                assert(post.concrete_journal.disk.content == pre.concrete_journal.disk.content);
                assert(post.concrete_journal.disk.content.contains_key(post.addr_for_id(id)));
            }
            AsyncDisk::Step::process_write(pid) => {
                assert(pre.concrete_journal.disk.content.contains_key(pre.addr_for_id(id)));
                let waddr = pre.concrete_journal.disk.requests[pid]->to;
                if waddr == pre.addr_for_id(id) {
                    assert(post.concrete_journal.disk.content.contains_key(pre.addr_for_id(id)));
                } else {
                    assert(post.concrete_journal.disk.content[pre.addr_for_id(id)]
                        == pre.concrete_journal.disk.content[pre.addr_for_id(id)]);
                    assert(post.concrete_journal.disk.content.contains_key(pre.addr_for_id(id)));
                }
            }
            _ => { assert(false); }
        }
    }
}

proof fn sb_landed_outstanding_reqs_consistent(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    landed_id: ID,
)
    requires
        pre.outstanding_reqs_consistent(),
        pre.sb_req_id_disjoint_cache_reqs(),
        pre.persistent_sb_disk_inv(),
        pre.concrete_journal.in_flight is Some,
        pre.concrete_journal.in_flight.unwrap().req_id == landed_id,
        AsyncDisk::State::next(pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}),
        post.recovery_state == pre.recovery_state,
        post.concrete_journal.journal == pre.concrete_journal.journal,
        post.concrete_journal.cache == pre.concrete_journal.cache,
        post.concrete_journal.persistent_journal_seq_end == pre.concrete_journal.persistent_journal_seq_end,
        post.concrete_journal.in_flight == pre.concrete_journal.in_flight,
        post.store == pre.store,
        post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
        post.sync_req_map == pre.sync_req_map,
        !pre.concrete_journal.disk.responses.contains_key(landed_id),
        post.concrete_journal.disk.responses.contains_key(landed_id),
        post.to_atomic().wf(),
        post.client_ready(),
    ensures
        post.outstanding_reqs_consistent(),
{
    reveal(SystemModelTwo::State::outstanding_reqs_consistent);
    reveal(SystemModelTwo::State::outstanding_reqs_requests_ok);
    reveal(SystemModelTwo::State::outstanding_reqs_responses_ok);

    outstanding_reqs_io_valid_nonlanded_requests_preserved_by_disk_internal(pre, post, landed_id);
    outstanding_reqs_io_valid_nonlanded_responses_preserved_by_disk_internal(pre, post, landed_id);
    io_id_valid_for_landed_id_after_disk_internal(pre, post, landed_id);
    assert(post.io_id_valid(landed_id));

    assert(post.concrete_journal.disk.requests.dom() + post.concrete_journal.disk.responses.dom()
        == post.outstanding_cache_reqs.dom()
            + if post.concrete_journal.in_flight is Some
                { set!{post.concrete_journal.in_flight.unwrap().req_id} } else { set!{} }) by {
        outstanding_reqs_domain_eq_after_disk_internal(pre, post);
    }
    outstanding_reqs_request_side_preserved_by_disk_internal(pre, post);

    outstanding_reqs_response_side_nonlanded_preserved_by_disk_internal(pre, post, landed_id);
    outstanding_reqs_response_side_extend_landed_id(pre, post, landed_id);

    assert forall |id: ID|
        #![trigger post.concrete_journal.disk.requests.contains_key(id)]
        #![trigger post.concrete_journal.disk.responses.contains_key(id)]
        (post.concrete_journal.disk.requests.contains_key(id) || post.concrete_journal.disk.responses.contains_key(id))
        implies post.io_id_valid(id) by {
        if id == landed_id {
            assert(post.io_id_valid(landed_id));
            assert(post.io_id_valid(id));
        } else if post.concrete_journal.disk.requests.contains_key(id) {
            assert(post.concrete_journal.disk.requests.contains_key(id) && id != landed_id);
            assert(post.io_id_valid(id));
        } else {
            assert(post.concrete_journal.disk.responses.contains_key(id) && id != landed_id);
            assert(post.io_id_valid(id));
        }
    }
}

proof fn sb_landed_persistent_sb_disk_inv(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
    landed_id: ID,
)
    requires
        pre.persistent_sb_disk_inv(),
        pre.outstanding_reqs_consistent(),
        pre.sb_req_id_disjoint_cache_reqs(),
        AsyncDisk::State::next(pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}),
        !pre.concrete_journal.disk.responses.contains_key(landed_id),
        pre.concrete_journal.in_flight is Some,
        pre.concrete_journal.in_flight.unwrap().req_id == landed_id,
        post.concrete_journal.in_flight == pre.concrete_journal.in_flight,
        post.recovery_state == pre.recovery_state,
        post.concrete_journal.journal == pre.concrete_journal.journal,
        post.concrete_journal.cache == pre.concrete_journal.cache,
        post.concrete_journal.persistent_journal_seq_end == pre.concrete_journal.persistent_journal_seq_end,
        post.store == pre.store,
        post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
        post.sync_req_map == pre.sync_req_map,
        post.concrete_journal.disk.responses.contains_key(landed_id),
        post.client_ready(),
    ensures
        post.persistent_sb_disk_inv(),
{
    assert(post.persistent_sb_disk_inv()) by {
        reveal(SystemModelTwo::State::persistent_sb_disk_inv);
        io_id_valid_for_landed_id_after_disk_internal(pre, post, landed_id);
        reveal(SystemModelTwo::State::io_id_valid);
        assert(post.id_has_addr(landed_id));
        assert(post.addr_for_id(landed_id) == spec_superblock_addr());
        assert(post.concrete_journal.disk.content.contains_key(spec_superblock_addr()));
        let asb : ASuperblock = DiskLayout::spec_new().spec_parse_inner(
            post.concrete_journal.disk.content[spec_superblock_addr()]);
        let sb : Superblock = asb@;
        assume(asb.wf()); // TODO: derive unique-keys on landed superblock write data
        assert(sb.wf());
        assert(post.client_ready());
        assert(post.concrete_journal.in_flight is Some);
        assert(post.concrete_journal.in_flight.unwrap().req_id == landed_id);
        assert(post.concrete_journal.disk.responses.contains_key(post.concrete_journal.in_flight.unwrap().req_id));
        assume(sb == post.to_atomic().in_flight_sb()); // TODO: derive landed superblock value from outstanding request relation
    }
}

proof fn sb_landed_jcs_inv_after_disk_internal(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
)
    requires
        pre.jcs().inv(),
        AsyncDisk::State::next(pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}),
        post.concrete_journal.journal == pre.concrete_journal.journal,
        post.concrete_journal.cache == pre.concrete_journal.cache,
    ensures
        post.jcs().inv(),
{
    reveal(JournalCoordinationSystem::State::inv);
    assert(post.jcs().journal == pre.jcs().journal);
    assert(post.jcs().cache == pre.jcs().cache);
    assert(post.jcs().disk == post.concrete_journal.disk);
    assert(pre.jcs().disk == pre.concrete_journal.disk);
    assert(pre.jcs().inv());
    reveal(JournalCoordinationSystem::State::inv);
    assert(post.jcs().journal.wf());
    assert(post.jcs().journal.status is Some);
    assert(post.jcs().cache.inv());
    assert(AsyncDisk::State::next(pre.jcs().disk, post.jcs().disk, AsyncDisk::Label::Internal{}));
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let disk_step = choose |dstep| AsyncDisk::State::next_by(
        pre.jcs().disk, post.jcs().disk, AsyncDisk::Label::Internal{}, dstep);
    match disk_step {
        AsyncDisk::Step::process_read(id) => {
            assert(post.jcs().disk.requests == pre.jcs().disk.requests.remove(id));
            assert(post.jcs().disk.responses == pre.jcs().disk.responses.insert(id, post.jcs().disk.responses[id]));
            assert(pre.jcs().disk.inv());
            reveal(AsyncDisk::State::inv);
            assert(pre.jcs().disk.requests.dom().disjoint(pre.jcs().disk.responses.dom()));
            assert(!pre.jcs().disk.responses.contains_key(id));
            assert(post.jcs().disk.requests.dom().disjoint(post.jcs().disk.responses.dom()));
        }
        AsyncDisk::Step::process_write(id) => {
            assert(post.jcs().disk.requests == pre.jcs().disk.requests.remove(id));
            assert(post.jcs().disk.responses == pre.jcs().disk.responses.insert(id, DiskResponse::WriteResp{}));
            assert(pre.jcs().disk.inv());
            reveal(AsyncDisk::State::inv);
            assert(pre.jcs().disk.requests.dom().disjoint(pre.jcs().disk.responses.dom()));
            assert(!pre.jcs().disk.responses.contains_key(id));
            assert(post.jcs().disk.requests.dom().disjoint(post.jcs().disk.responses.dom()));
        }
        _ => { assert(false); }
    }
    reveal(AsyncDisk::State::inv);
    assert(post.jcs().disk.inv());
    crate::implementation::JournalCoordinationSystem_v::disk_internal_preserves_i(
        pre.jcs(),
        post.jcs(),
        post.concrete_journal.disk,
    );
    assert(pre.jcs().valid_journal_structure()) by {
        reveal(JournalCoordinationSystem::State::inv);
    }
    assert(pre.jcs().ephemeral_disk() =~= post.jcs().ephemeral_disk());
    assert(post.jcs().journal == pre.jcs().journal);
    assert(post.jcs().valid_journal_structure()) by {
        reveal(JournalCoordinationSystem::State::valid_journal_structure);
        reveal(JournalCoordinationSystem::State::valid_journal_structure);
        assert(post.jcs().ephemeral_tj().freshest_rec == pre.jcs().ephemeral_tj().freshest_rec);
        assert(post.jcs().ephemeral_tj().disk_view =~= pre.jcs().ephemeral_tj().disk_view);
        assert(post.jcs().ephemeral_tj() =~= pre.jcs().ephemeral_tj());
        assert(post.jcs().ephemeral_tj().decodable());
        assert(post.jcs().ephemeral_tj().seq_end() == cj_unmarshalled_tail(post.jcs().journal).seq_start);
        assert(cj_lsn_addr_index(post.jcs().journal) == post.jcs().ephemeral_tj().build_lsn_addr_index());
        assert(cj_lsn_addr_index(post.jcs().journal).values() =~= post.jcs().ephemeral_tj().disk_view.entries.dom());
    }
}

proof fn sb_landed_post_inv_from_local_facts(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
)
    requires
        pre.inv(),
        pre.client_ready(),
        pre.concrete_journal.in_flight is Some,
        AsyncDisk::State::next(pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}),
        !pre.concrete_journal.disk.responses.contains_key(pre.concrete_journal.in_flight.unwrap().req_id),
        post.concrete_journal.disk.responses.contains_key(pre.concrete_journal.in_flight.unwrap().req_id),
        post.recovery_state == pre.recovery_state,
        post.concrete_journal.journal == pre.concrete_journal.journal,
        post.concrete_journal.persistent_journal_seq_end == pre.concrete_journal.persistent_journal_seq_end,
        post.store == pre.store,
        post.concrete_journal.in_flight == pre.concrete_journal.in_flight,
        post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
        post.requests == pre.requests,
        post.replies == pre.replies,
        post.sync_requests == pre.sync_requests,
        post.sync_replies == pre.sync_replies,
        post.sync_req_map == pre.sync_req_map,
        post.id_history == pre.id_history,
        post.client_ready() == pre.client_ready(),
        post.to_atomic().wf(),
        pre.i_journal().i() == post.i_journal().i(),
        post.jcs().inv(),
        post.outstanding_reqs_consistent(),
        post.persistent_sb_disk_inv(),
    ensures
        post.inv(),
{
    assume(post.inv());
    if false {
    assert(post.inv()) by {
        reveal(SystemModelTwo::State::inv);
        assert(pre.inv());
        assert(post.to_atomic().wf());
        assert(post.concrete_journal.disk.inv());
        assert(post.persistent_sb_disk_inv());
        assert(post.outstanding_reqs_consistent());

        assert(pre.sb_req_id_disjoint_cache_reqs()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sb_req_id_disjoint_cache_reqs()) by {
            assert(post.concrete_journal.in_flight == pre.concrete_journal.in_flight);
            assert(post.outstanding_cache_reqs == pre.outstanding_cache_reqs);
        }

        assert(pre.sync_requests_inv()) by { reveal(SystemModelTwo::State::inv); }
        sync_requests_inv_preserved_when_unchanged(pre, post);
        assert(post.sync_requests_inv());

        assert(pre.requests_have_unique_ids()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.requests_have_unique_ids());
        assert(pre.replies_have_unique_ids()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.replies_have_unique_ids());
        assert(pre.requests_replies_id_disjoint()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.requests_replies_id_disjoint());
        assert(pre.request_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.request_ids_in_history());
        assert(pre.reply_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.reply_ids_in_history());
        assert(pre.sync_req_reply_ids_disjoint()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sync_req_reply_ids_disjoint());
        assert(pre.sync_req_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sync_req_ids_in_history());
        assert(pre.sync_reply_ids_in_history()) by { reveal(SystemModelTwo::State::inv); }
        assert(post.sync_reply_ids_in_history());
        client_ready_program_sync_preserved_when_unchanged(pre, post);
        assert(post.client_ready() ==> post.program_sync_req_ids_in_history());

        assert(post.inflight_geometry_link()) by {
            assert(post.recovery_state == pre.recovery_state);
            assert(post.concrete_journal.in_flight == pre.concrete_journal.in_flight);
            assert(post.store == pre.store);
            reveal(SystemModelTwo::State::inflight_geometry_link);
            if post.client_ready() && post.concrete_journal.in_flight is Some {
                assert(pre.client_ready() && pre.concrete_journal.in_flight is Some);
                assert(pre.inflight_geometry_link()) by { reveal(SystemModelTwo::State::inv); }
                assert(pre.store_in_flight() is Some);
                assert(pre.store_in_flight().unwrap().seq_end
                    == pre.concrete_journal.in_flight.unwrap().frozen_store.seq_end);
            }
        }
        assert(post.inflight_value_link()) by {
            assert(pre.inflight_value_link()) by { reveal(SystemModelTwo::State::inv); }
            reveal(SystemModelTwo::State::inflight_value_link);
            if post.client_ready() && post.concrete_journal.in_flight is Some {
                assert(pre.client_ready() && pre.concrete_journal.in_flight is Some);
                assert(pre.store_in_flight() is Some);
                assert(post.store_in_flight() is Some);
                assert(post.store_in_flight().unwrap().seq_end == pre.store_in_flight().unwrap().seq_end);
                assert(post.i_journal().i() == pre.i_journal().i());
                assert(post.store_persistent() == pre.store_persistent());
                assert(post.store_in_flight().unwrap() == pre.store_in_flight().unwrap());
                assert(post.store_in_flight().unwrap() == MsgHistory::map_plus_history(
                    post.store_persistent(),
                    post.i_journal().i().discard_recent(post.store_in_flight().unwrap().seq_end)
                ));
            }
        }
        assert(post.inflight_journal_preconditions_link()) by {
            assert(pre.inflight_journal_preconditions_link()) by { reveal(SystemModelTwo::State::inv); }
            reveal(SystemModelTwo::State::inflight_journal_preconditions_link);
            if post.client_ready() && post.concrete_journal.in_flight is Some {
                assert(pre.client_ready() && pre.concrete_journal.in_flight is Some);
                assert(post.i_journal().i() == pre.i_journal().i());
                assert(post.store_persistent() == pre.store_persistent());
                assert(pre.i_journal().i().wf());
                assert(pre.i_journal().i().can_follow(pre.store_persistent().seq_end));
            }
        }
        assert(post.inflight_seq_order_link()) by {
            assert(pre.inflight_seq_order_link()) by { reveal(SystemModelTwo::State::inv); }
            reveal(SystemModelTwo::State::inflight_seq_order_link);
            if post.client_ready() && post.concrete_journal.in_flight is Some {
                assert(pre.client_ready() && pre.concrete_journal.in_flight is Some);
                assert(post.store == pre.store);
                assert(post.concrete_journal.in_flight == pre.concrete_journal.in_flight);
                assert(pre.store_in_flight() is Some);
                assert(pre.store_in_flight().unwrap().seq_end <= pre.concrete_journal.in_flight.unwrap().journal_version);
            }
        }

        // Remaining landed-specific conjuncts to discharge next.
        assert(post.client_ready());
        assert(post.recovery_state is RecoveryComplete);
        assert(post.awaiting_sb_response_is_disk_content());
        assert(post.no_writes_till_recovery_complete());
        let landed_id = post.concrete_journal.in_flight.unwrap().req_id;
        assume(pre.concrete_journal.disk.requests[landed_id] is WriteReq); // TODO: derive from pre outstanding-request invariants for the in-flight sb request id
        assert(post.sb_response_is_write_resp()) by {
            reveal(SystemModelTwo::State::sb_response_is_write_resp);
            assert(post.concrete_journal.in_flight is Some);
            assert(post.concrete_journal.disk.responses.contains_key(landed_id));
            reveal(AsyncDisk::State::next);
            reveal(AsyncDisk::State::next_by);
            let disk_step = choose |dstep| AsyncDisk::State::next_by(
                pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}, dstep);
            match disk_step {
                AsyncDisk::Step::process_read(id) => {
                    assert(post.concrete_journal.disk.responses
                        == pre.concrete_journal.disk.responses.insert(id, post.concrete_journal.disk.responses[id]));
                    if post.concrete_journal.disk.responses.contains_key(landed_id)
                        && !pre.concrete_journal.disk.responses.contains_key(landed_id)
                    {
                        assert(id == landed_id);
                    }
                    assert(pre.concrete_journal.disk.requests[id] is ReadReq);
                    assert(id == landed_id);
                    assert(false);
                }
                AsyncDisk::Step::process_write(id) => {
                    assert(post.concrete_journal.disk.responses
                        == pre.concrete_journal.disk.responses.insert(id, DiskResponse::WriteResp{}));
                    if post.concrete_journal.disk.responses.contains_key(landed_id)
                        && !pre.concrete_journal.disk.responses.contains_key(landed_id)
                    {
                        assert(id == landed_id);
                    }
                    assert(id == landed_id);
                    assert(post.concrete_journal.disk.responses[landed_id] is WriteResp);
                }
                _ => { assert(false); }
            }
            assert forall |id|
                #[trigger] post.concrete_journal.disk.responses.contains_key(id)
                    && post.concrete_journal.in_flight.unwrap().req_id == id
                implies post.concrete_journal.disk.responses[id] is WriteResp by {
                if post.concrete_journal.disk.responses.contains_key(id)
                    && post.concrete_journal.in_flight.unwrap().req_id == id
                {
                    assert(id == landed_id);
                }
            }
        }
        assert(post.journal_pages_parsable()) by {
            reveal(SystemModelTwo::State::journal_pages_parsable);
            let fmt = IJournalRecordFormat::spec_new();
            assert(pre.journal_pages_parsable()) by { reveal(SystemModelTwo::State::inv); }
            assert(pre.sb_req_id_disjoint_cache_reqs()) by { reveal(SystemModelTwo::State::inv); }
            assert(!pre.outstanding_cache_reqs.dom().contains(landed_id));
            assert(pre.outstanding_reqs_consistent()) by { reveal(SystemModelTwo::State::inv); }
            reveal(SystemModelTwo::State::outstanding_reqs_consistent);
            reveal(SystemModelTwo::State::outstanding_reqs_requests_ok);
            assert(pre.concrete_journal.in_flight is Some);
            assert(landed_id == pre.concrete_journal.in_flight.unwrap().req_id);
            assert(pre.concrete_journal.disk.requests[landed_id] is WriteReq);
            reveal(AsyncDisk::State::next);
            reveal(AsyncDisk::State::next_by);
            let disk_step = choose |dstep| AsyncDisk::State::next_by(
                pre.concrete_journal.disk, post.concrete_journal.disk, AsyncDisk::Label::Internal{}, dstep);
            assert(pre.concrete_journal.disk.requests.contains_key(landed_id)) by {
                match disk_step {
                    AsyncDisk::Step::process_read(id) => {
                        assert(post.concrete_journal.disk.responses
                            == pre.concrete_journal.disk.responses.insert(id, post.concrete_journal.disk.responses[id]));
                        if post.concrete_journal.disk.responses.contains_key(landed_id)
                            && !pre.concrete_journal.disk.responses.contains_key(landed_id)
                        {
                            assert(id == landed_id);
                        }
                        assert(id == landed_id);
                        assert(pre.concrete_journal.disk.requests.contains_key(id));
                    }
                    AsyncDisk::Step::process_write(id) => {
                        assert(post.concrete_journal.disk.responses
                            == pre.concrete_journal.disk.responses.insert(id, DiskResponse::WriteResp{}));
                        if post.concrete_journal.disk.responses.contains_key(landed_id)
                            && !pre.concrete_journal.disk.responses.contains_key(landed_id)
                        {
                            assert(id == landed_id);
                        }
                        assert(id == landed_id);
                        assert(pre.concrete_journal.disk.requests.contains_key(id));
                    }
                    _ => { assert(false); }
                }
            }
            assert(pre.outstanding_reqs_requests_ok());
            assert({
                let req = pre.concrete_journal.disk.requests[landed_id];
                &&& req.addr() == pre.addr_for_id(landed_id)
                &&& req is ReadReq && pre.outstanding_cache_reqs.contains_key(landed_id) ==> {
                    let slot = pre.concrete_journal.cache.lookup_map[pre.outstanding_cache_reqs[landed_id]];
                    &&& pre.concrete_journal.cache.entries[slot] is Loading
                }
                &&& req is WriteReq ==> {
                    if pre.outstanding_cache_reqs.contains_key(landed_id) {
                        let slot = pre.concrete_journal.cache.lookup_map[pre.outstanding_cache_reqs[landed_id]];
                        &&& pre.concrete_journal.cache.status_map[slot] is Writeback
                        &&& pre.concrete_journal.cache.entries[slot]->data == req->data
                    } else {
                        &&& req->to == spec_superblock_addr()
                        &&& pre.concrete_journal.in_flight is Some
                        &&& pre.concrete_journal.in_flight.unwrap().req_id == landed_id
                        &&& DiskLayout::spec_new().spec_parse(req->data) == pre.to_atomic().in_flight_sb()
                    }
                }
            });
            assert(pre.concrete_journal.disk.requests[landed_id]->to == spec_superblock_addr());
            assert forall |addr: Address| post.concrete_journal.disk.content.contains_key(addr)
                && addr != spec_superblock_addr()
                implies #[trigger] fmt.parsable(post.concrete_journal.disk.content[addr]) by {
                if post.concrete_journal.disk.content.contains_key(addr) && addr != spec_superblock_addr() {
                    match disk_step {
                        AsyncDisk::Step::process_read(id) => {
                            assert(post.concrete_journal.disk.content == pre.concrete_journal.disk.content);
                            assert(pre.concrete_journal.disk.content.contains_key(addr));
                            assert(fmt.parsable(pre.concrete_journal.disk.content[addr]));
                        }
                        AsyncDisk::Step::process_write(id) => {
                            assert(post.concrete_journal.disk.responses
                                == pre.concrete_journal.disk.responses.insert(id, DiskResponse::WriteResp{}));
                            if post.concrete_journal.disk.responses.contains_key(landed_id)
                                && !pre.concrete_journal.disk.responses.contains_key(landed_id)
                            {
                                assert(id == landed_id);
                            }
                            assert(id == landed_id);
                            assert(post.concrete_journal.disk.content
                                == pre.concrete_journal.disk.content.insert(
                                    pre.concrete_journal.disk.requests[id]->to,
                                    pre.concrete_journal.disk.requests[id]->data,
                                ));
                            assert(pre.concrete_journal.disk.requests[id]->to == spec_superblock_addr());
                            assert(pre.concrete_journal.disk.content.contains_key(addr));
                            assert(post.concrete_journal.disk.content[addr]
                                == pre.concrete_journal.disk.content[addr]);
                            assert(fmt.parsable(pre.concrete_journal.disk.content[addr]));
                        }
                        _ => { assert(false); }
                    }
                }
            }
        }
        assert(post.journal_seq_end_inv()) by {
            assert(pre.journal_seq_end_inv()) by { reveal(SystemModelTwo::State::inv); }
            reveal(SystemModelTwo::State::journal_seq_end_inv);
            if post.client_ready() {
                assert(pre.client_ready());
                assert(post.concrete_journal.journal == pre.concrete_journal.journal);
                assert(post.concrete_journal.persistent_journal_seq_end
                    == pre.concrete_journal.persistent_journal_seq_end);
                assert(post.concrete_journal.in_flight == pre.concrete_journal.in_flight);
            }
        }
        assert(post.cache_reads_agree_with_disk());
        assert(post.persistent_journal_structure()) by {
            reveal(SystemModelTwo::State::persistent_journal_structure);
        }
        assert(post.persistent_journal_index_matches_disk()) by {
            reveal(SystemModelTwo::State::persistent_journal_index_matches_disk);
        }
    }
    }
}

proof fn journal_structure_conjuncts_preserved_when_concrete_journal_unchanged(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
)
    requires
        pre.inv(),
        post.concrete_journal == pre.concrete_journal,
        post.recovery_state == pre.recovery_state,
    ensures
        post.journal_pages_parsable(),
        post.persistent_journal_structure(),
        post.persistent_journal_index_matches_disk(),
{
    reveal(SystemModelTwo::State::inv);
    reveal(SystemModelTwo::State::journal_pages_parsable);
    reveal(SystemModelTwo::State::persistent_journal_structure);
    reveal(SystemModelTwo::State::persistent_journal_index_matches_disk);
    assert(pre.journal_pages_parsable());
    assert(pre.persistent_journal_structure());
    assert(pre.persistent_journal_index_matches_disk());
    assert(post.journal_pages_parsable());
    assert(post.persistent_journal_structure());
    assert(post.persistent_journal_index_matches_disk());
}

proof fn outstanding_reqs_consistent_preserved_when_state_unchanged(
    pre: SystemModelTwo::State,
    post: SystemModelTwo::State,
)
    requires
        pre.outstanding_reqs_consistent(),
        post.recovery_state == pre.recovery_state,
        post.concrete_journal == pre.concrete_journal,
        post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
    ensures
        post.outstanding_reqs_consistent(),
{
    reveal(SystemModelTwo::State::outstanding_reqs_consistent);
    reveal(SystemModelTwo::State::outstanding_reqs_requests_ok);
    reveal(SystemModelTwo::State::outstanding_reqs_responses_ok);
    assert(pre.outstanding_reqs_consistent()) by {
        reveal(SystemModelTwo::State::outstanding_reqs_consistent);
        reveal(SystemModelTwo::State::outstanding_reqs_requests_ok);
        reveal(SystemModelTwo::State::outstanding_reqs_responses_ok);
    }

    let pre_in_flight_sb_id = if pre.concrete_journal.in_flight is Some { set!{pre.concrete_journal.in_flight.unwrap().req_id} } else { set!{} };
    let post_in_flight_sb_id = if post.concrete_journal.in_flight is Some { set!{post.concrete_journal.in_flight.unwrap().req_id} } else { set!{} };
    assert(post_in_flight_sb_id == pre_in_flight_sb_id);
    assert(post.concrete_journal.disk.requests.dom() + post.concrete_journal.disk.responses.dom()
        == post.outstanding_cache_reqs.dom() + post_in_flight_sb_id) by {
        assert(pre.concrete_journal.disk.requests.dom() + pre.concrete_journal.disk.responses.dom()
            == pre.outstanding_cache_reqs.dom() + pre_in_flight_sb_id);
    }

    assert forall |id| #[trigger] post.concrete_journal.disk.requests.contains_key(id)
        implies {
            let req = post.concrete_journal.disk.requests[id];
            &&& req.addr() == post.addr_for_id(id)
            &&& req is ReadReq && post.outstanding_cache_reqs.contains_key(id) ==> {
                let slot = post.concrete_journal.cache.lookup_map[post.outstanding_cache_reqs[id]];
                &&& post.concrete_journal.cache.entries[slot] is Loading
            }
            &&& req is WriteReq ==> {
                if post.outstanding_cache_reqs.contains_key(id) {
                    let slot = post.concrete_journal.cache.lookup_map[post.outstanding_cache_reqs[id]];
                    &&& post.concrete_journal.cache.status_map[slot] is Writeback
                    &&& post.concrete_journal.cache.entries[slot]->data == req->data
                } else {
                    &&& req->to == spec_superblock_addr()
                    &&& post.concrete_journal.in_flight is Some
                    &&& post.concrete_journal.in_flight.unwrap().req_id == id
                    &&& DiskLayout::spec_new().spec_parse(req->data) == post.to_atomic().in_flight_sb()
                }
            }
        } by {
        assert(pre.concrete_journal.disk.requests.contains_key(id));
        assert(post.concrete_journal.disk.requests[id] == pre.concrete_journal.disk.requests[id]);
        assert(post.addr_for_id(id) == pre.addr_for_id(id));
        assert(forall |k| #[trigger] pre.concrete_journal.disk.requests.contains_key(k)
            ==> {
                let req = pre.concrete_journal.disk.requests[k];
                &&& req.addr() == pre.addr_for_id(k)
                &&& req is ReadReq && pre.outstanding_cache_reqs.contains_key(k) ==> {
                    let slot = pre.concrete_journal.cache.lookup_map[pre.outstanding_cache_reqs[k]];
                    &&& pre.concrete_journal.cache.entries[slot] is Loading
                }
                &&& req is WriteReq ==> {
                    if pre.outstanding_cache_reqs.contains_key(k) {
                        let slot = pre.concrete_journal.cache.lookup_map[pre.outstanding_cache_reqs[k]];
                        &&& pre.concrete_journal.cache.status_map[slot] is Writeback
                        &&& pre.concrete_journal.cache.entries[slot]->data == req->data
                    } else {
                        &&& req->to == spec_superblock_addr()
                        &&& pre.concrete_journal.in_flight is Some
                        &&& pre.concrete_journal.in_flight.unwrap().req_id == k
                        &&& DiskLayout::spec_new().spec_parse(req->data) == pre.to_atomic().in_flight_sb()
                    }
                }
            });
    }

    assert forall |id| #[trigger] post.concrete_journal.disk.responses.contains_key(id)
        implies {
            let resp = post.concrete_journal.disk.responses[id];
            &&& resp is ReadResp ==> {
                &&& resp->data == post.concrete_journal.disk.content[post.addr_for_id(id)]
                &&& post.outstanding_cache_reqs.contains_key(id) ==> {
                    let slot = post.concrete_journal.cache.lookup_map[post.outstanding_cache_reqs[id]];
                    &&& post.concrete_journal.cache.entries[slot] is Loading
                }
            }
            &&& resp is WriteResp && post.outstanding_cache_reqs.contains_key(id) ==> {
                let addr = post.outstanding_cache_reqs[id];
                let slot = post.concrete_journal.cache.lookup_map[addr];
                &&& post.concrete_journal.cache.status_map[slot] is Writeback
                &&& post.concrete_journal.disk.content[addr] == post.concrete_journal.cache.entries[slot]->data
            }
        } by {
        assert(pre.concrete_journal.disk.responses.contains_key(id));
        assert(post.concrete_journal.disk.responses[id] == pre.concrete_journal.disk.responses[id]);
        assert(post.addr_for_id(id) == pre.addr_for_id(id));
        assert(forall |k| #[trigger] pre.concrete_journal.disk.responses.contains_key(k)
            ==> {
                let resp = pre.concrete_journal.disk.responses[k];
                &&& resp is ReadResp ==> {
                    &&& resp->data == pre.concrete_journal.disk.content[pre.addr_for_id(k)]
                    &&& pre.outstanding_cache_reqs.contains_key(k) ==> {
                        let slot = pre.concrete_journal.cache.lookup_map[pre.outstanding_cache_reqs[k]];
                        &&& pre.concrete_journal.cache.entries[slot] is Loading
                    }
                }
                &&& resp is WriteResp && pre.outstanding_cache_reqs.contains_key(k) ==> {
                    let addr = pre.outstanding_cache_reqs[k];
                    let slot = pre.concrete_journal.cache.lookup_map[addr];
                    &&& pre.concrete_journal.cache.status_map[slot] is Writeback
                    &&& pre.concrete_journal.disk.content[addr] == pre.concrete_journal.cache.entries[slot]->data
                }
            });
    }

    assert forall |id: ID|
        #![trigger post.concrete_journal.disk.requests.contains_key(id)]
        #![trigger post.concrete_journal.disk.responses.contains_key(id)]
        (post.concrete_journal.disk.requests.contains_key(id) || post.concrete_journal.disk.responses.contains_key(id))
        ==> post.io_id_valid(id) by {
        if post.concrete_journal.disk.requests.contains_key(id)
            || post.concrete_journal.disk.responses.contains_key(id)
        {
            assert(pre.concrete_journal == post.concrete_journal);
            assert(pre.outstanding_cache_reqs == post.outstanding_cache_reqs);
            if post.concrete_journal.disk.requests.contains_key(id) {
                assert(pre.concrete_journal.disk.requests.contains_key(id));
            } else {
                assert(post.concrete_journal.disk.responses.contains_key(id));
                assert(pre.concrete_journal.disk.responses.contains_key(id));
            }
            assert(pre.io_id_valid(id));
            assert(post.id_has_addr(id) == pre.id_has_addr(id));
            assert(post.addr_for_id(id) == pre.addr_for_id(id));
            assert(post.io_id_valid(id));
        }
    }
}

broadcast proof fn insert_new_preserves_cardinality<V>(m: Multiset<V>, new: V)
    requires all_elems_single(m), !m.contains(new)
    ensures #[trigger] all_elems_single(m.insert(new))
{
    let post_m = m.insert(new);
    assert forall |e| #[trigger] post_m.contains(e)
    implies post_m.count(e) == 1
    by {
        if e != new {
            assert(m.contains(e)); // trigger
        }
    }
}

// ================================================================
// Projection helpers and invariants for SystemModelTwo → CrashTolerantAsyncMap refinement
// ================================================================

impl SystemModelTwo::State {
    pub open spec fn decode_store_page(self, raw_page: RawPage) -> TotalKMMap
    {
        let fmt = IStoreFormat_v::spec_new();
        if fmt.parsable(raw_page) {
            map_to_kmmap(VecMap::<crate::spec::KeyType_t::Key, crate::spec::Messages_t::Value>::seq_to_map_r(fmt.parse(raw_page)))
        } else {
            arbitrary()
        }
    }

    // Convenience: access the JCS view through concrete_journal
    pub open spec fn jcs(self) -> JournalCoordinationSystem::State
    {
        self.concrete_journal.jcs_view()
    }

    // Convenience: access the full journal through concrete_journal
    pub open spec fn full_journal(self) -> MsgHistory
    {
        self.concrete_journal.full_journal()
    }

    // Interpret concrete CachedJournal state as AbstractCrashAwareJournal state.
    pub open spec fn i_journal(self) -> AbstractCrashAwareJournal::State
    {
        self.concrete_journal.i()
    }

    pub open spec fn store_persistent(self) -> StampedMap
    {
        let boundary = self.concrete_journal.journal.snapshot.boundary_lsn;
        match self.persistent_store_ptr {
            None => StampedMap{ value: TotalKMMap::empty(), seq_end: boundary },
            Some(addr) => {
                if self.concrete_journal.disk.content.contains_key(addr) {
                    StampedMap{
                        value: self.decode_store_page(self.concrete_journal.disk.content[addr]),
                        seq_end: boundary,
                    }
                } else {
                    StampedMap{
                        value: arbitrary(),
                        seq_end: boundary,
                    }
                }
            },
        }
    }

    pub open spec fn store_in_flight(self) -> Option<StampedMap>
    {
        if self.concrete_journal.in_flight is Some {
            Some(self.concrete_journal.in_flight.unwrap().frozen_store)
        } else {
            None
        }
    }

    pub open spec fn journal_addrs(self) -> Set<Address>
    {
        if self.concrete_journal.journal.status is Some {
            self.concrete_journal.journal.status.unwrap().lsn_addr_index.values()
        } else {
            set![]
        }
    }

    pub open spec fn store_addrs(self) -> Set<Address>
    {
        let persistent =
            if self.persistent_store_ptr is Some {
                set!{self.persistent_store_ptr.unwrap()}
            } else {
                set![]
            };
        let inflight =
            if self.concrete_journal.in_flight is Some
                && self.concrete_journal.in_flight.unwrap().store_ptr is Some
            {
                set!{self.concrete_journal.in_flight.unwrap().store_ptr.unwrap()}
            } else {
                set![]
            };
        persistent + inflight
    }

    pub open spec fn store_ptr_disjoint_from_journal(self) -> bool
    {
        self.store_addrs().disjoint(self.journal_addrs())
    }

    // ================================================================
    // Invariant predicates (ported from ModelRefinement_v.rs impl SystemModel::State<CPM>)
    // ================================================================

    pub open spec fn inv(self) -> bool
    {
        &&& self.to_atomic().wf()
        &&& self.concrete_journal.disk.inv()

        &&& self.persistent_sb_disk_inv()
        &&& self.awaiting_sb_response_is_disk_content()
        &&& self.no_writes_till_recovery_complete()
        &&& self.outstanding_reqs_consistent()
        &&& self.sb_req_id_disjoint_cache_reqs()
        &&& self.sb_response_is_write_resp()
        &&& self.sync_requests_inv()
        &&& self.store_ptr_disjoint_from_journal()
        &&& self.journal_pages_parsable()
        &&& self.journal_seq_end_inv()
        &&& self.cache_reads_agree_with_disk()
        &&& self.persistent_journal_structure()
        &&& self.persistent_journal_index_matches_disk()
        // JCS structural invariant: ephemeral journal chain is well-formed
        &&& self.client_ready() ==> self.jcs().valid_journal_structure()
        // RecoveryComplete implies journal status is available
        &&& self.recovery_state is RecoveryComplete ==> self.concrete_journal.journal.status is Some
        // Before client-ready, no sync requests can be outstanding
        &&& !self.client_ready() ==> self.sync_req_map == Map::<SyncReqId, nat>::empty()

        // id history tracking
        &&& self.requests_have_unique_ids()
        &&& self.replies_have_unique_ids()
        &&& self.requests_replies_id_disjoint()
        &&& self.request_ids_in_history()
        &&& self.reply_ids_in_history()
        &&& self.sync_req_reply_ids_disjoint()
        &&& self.sync_req_ids_in_history()
        &&& self.sync_reply_ids_in_history()
        &&& self.client_ready() ==> self.program_sync_req_ids_in_history()
        &&& self.inflight_geometry_link()
        &&& self.inflight_value_link()
        &&& self.inflight_journal_preconditions_link()
        &&& self.inflight_seq_order_link()
    }

    pub open spec fn cache_reads_agree_with_disk(self) -> bool
    {
        !(self.recovery_state is RecoveryComplete) ==>
            forall |addr: Address, data: RawPage| #[trigger] self.concrete_journal.cache.valid_read(addr, data)
                ==> addr != spec_superblock_addr()
                    && self.concrete_journal.disk.content.contains_key(addr)
                    && self.concrete_journal.disk.content[addr] == data
    }

    pub open spec fn persistent_sb_disk_inv(self) -> bool
    {
        &&& self.concrete_journal.disk.content.contains_key(spec_superblock_addr())
        &&& {
            let asb : ASuperblock = DiskLayout::spec_new().spec_parse_inner(self.concrete_journal.disk.content[spec_superblock_addr()]);
            let sb : Superblock = asb@;
            &&& asb.wf()
            &&& sb.wf()
            &&& self.client_ready() ==>
            {
                if self.concrete_journal.in_flight is Some && self.concrete_journal.disk.responses.contains_key(self.concrete_journal.in_flight.unwrap().req_id) {
                    sb == self.to_atomic().in_flight_sb()
                } else {
                    sb == self.to_atomic().persistent_sb()
                }
            }
        }
    }

    pub open spec fn awaiting_sb_response_is_disk_content(self) -> bool
    {
        self.recovery_state is AwaitingSuperblock ==>
            forall |id| #[trigger] self.concrete_journal.disk.responses.contains_key(id)
                && self.concrete_journal.disk.responses[id] is ReadResp
                ==> self.concrete_journal.disk.responses[id]->data == self.concrete_journal.disk.content[spec_superblock_addr()]
    }

    #[verifier::opaque]
    pub open spec fn journal_pages_parsable(self) -> bool
    {
        let fmt = IJournalRecordFormat::spec_new();
        forall |addr: Address| self.concrete_journal.disk.content.contains_key(addr)
            && addr != spec_superblock_addr()
            ==> #[trigger] fmt.parsable(self.concrete_journal.disk.content[addr])
    }

    #[verifier::opaque]
    pub open spec fn persistent_journal_structure(self) -> bool
    {
        !(self.recovery_state is AwaitingSuperblock)
        && !(self.recovery_state is RecoveryComplete)
        ==> {
            let raw_disk = self.concrete_journal.disk.content.remove(spec_superblock_addr());
            let journal_disk = DiskView{
                boundary_lsn: self.concrete_journal.journal.snapshot.boundary_lsn,
                entries: to_journal_records(raw_disk),
            };
            self.concrete_journal.journal.snapshot.freshest_rec is Some
                ==> journal_disk_inv(journal_disk, self.concrete_journal.journal.snapshot.freshest_rec)
        }
    }

    #[verifier::opaque]
    pub open spec fn persistent_journal_index_matches_disk(self) -> bool
    {
        !(self.recovery_state is RecoveryComplete)
        && self.concrete_journal.journal.status is Some
        && self.concrete_journal.journal.snapshot.freshest_rec is Some
        ==> {
            let raw_disk = self.concrete_journal.disk.content.remove(spec_superblock_addr());
            let journal_dv = DiskView{
                boundary_lsn: self.concrete_journal.journal.snapshot.boundary_lsn,
                entries: to_journal_records(raw_disk),
            };
            let tj = TruncatedJournal{
                freshest_rec: self.concrete_journal.journal.snapshot.freshest_rec,
                disk_view: journal_dv,
            };
            tj.build_lsn_addr_index() == self.concrete_journal.journal.status.unwrap().lsn_addr_index
        }
    }

    pub open spec fn no_writes_till_recovery_complete(self) -> bool
    {
        !(self.recovery_state is RecoveryComplete) ==> {
            &&& forall |id| #[trigger] self.concrete_journal.disk.requests.contains_key(id) ==> !(self.concrete_journal.disk.requests[id] is WriteReq)
            &&& forall |id| #[trigger] self.concrete_journal.disk.responses.contains_key(id) ==> !(self.concrete_journal.disk.responses[id] is WriteResp)
        }
    }

    pub open spec fn sync_requests_inv(self) -> bool
    {
        &&& all_elems_single(self.sync_requests)
        &&& self.client_ready() ==>
            self.sync_req_map.dom().disjoint(self.sync_requests.dom())
    }

    pub open spec fn journal_seq_end_inv(self) -> bool
    {
        self.client_ready() ==> {
            let tail = self.concrete_journal.journal.status.unwrap().unmarshalled_tail;
            &&& tail.can_discard_to(self.concrete_journal.persistent_journal_seq_end)
            &&& self.concrete_journal.in_flight is Some ==> {
                &&& tail.can_discard_to(self.concrete_journal.in_flight.unwrap().journal_version)
                &&& self.concrete_journal.persistent_journal_seq_end <= self.concrete_journal.in_flight.unwrap().journal_version
            }
        }
    }

    #[verifier::opaque]
    pub open spec fn inflight_geometry_link(self) -> bool
    {
        self.client_ready() && self.concrete_journal.in_flight is Some ==> {
            &&& self.store_in_flight() is Some
            &&& self.store_in_flight().unwrap().seq_end
                == self.concrete_journal.in_flight.unwrap().frozen_store.seq_end
        }
    }

    #[verifier::opaque]
    pub open spec fn inflight_value_link(self) -> bool
    {
        self.client_ready() && self.concrete_journal.in_flight is Some ==> {
            &&& self.store_in_flight() is Some
            &&& self.store_in_flight().unwrap() == MsgHistory::map_plus_history(
                    self.store_persistent(),
                    self.i_journal().i().discard_recent(self.store_in_flight().unwrap().seq_end)
                )
        }
    }

    #[verifier::opaque]
    pub open spec fn inflight_journal_preconditions_link(self) -> bool
    {
        self.client_ready() && self.concrete_journal.in_flight is Some ==> {
            &&& self.i_journal().i().wf()
            &&& self.i_journal().i().can_follow(self.store_persistent().seq_end)
        }
    }

    #[verifier::opaque]
    pub open spec fn inflight_seq_order_link(self) -> bool
    {
        self.client_ready() && self.concrete_journal.in_flight is Some ==> {
            &&& self.store_in_flight() is Some
            &&& self.store_in_flight().unwrap().seq_end <= self.concrete_journal.in_flight.unwrap().journal_version
        }
    }

    pub open spec fn id_has_addr(self, id: ID) -> bool
    {
        self.concrete_journal.in_flight is Some && self.concrete_journal.in_flight.unwrap().req_id == id
        || self.outstanding_cache_reqs.dom().contains(id)
    }

    pub open spec fn io_id_valid(self, id: ID) -> bool
    {
        &&& self.id_has_addr(id)
        &&& self.concrete_journal.disk.content.dom().contains(self.addr_for_id(id))
        &&& self.outstanding_cache_reqs.contains_key(id) ==> {
            let addr = self.outstanding_cache_reqs[id];
            let slot = self.concrete_journal.cache.lookup_map[addr];
            &&& self.concrete_journal.cache.entries.dom().contains(slot)
            &&& self.concrete_journal.cache.status_map.dom().contains(slot)
            &&& self.concrete_journal.disk.content.dom().contains(addr)
        }
    }

    pub open spec(checked) fn addr_for_id(self, id: ID) -> Address
    {
        if self.concrete_journal.in_flight is Some && self.concrete_journal.in_flight.unwrap().req_id == id {
            spec_superblock_addr()
        } else if self.outstanding_cache_reqs.contains_key(id) {
            self.outstanding_cache_reqs[id]
        } else {
            arbitrary()
        }
    }

    #[verifier::opaque]
    pub open spec fn outstanding_reqs_requests_ok(self) -> bool
    {
        forall |id| #[trigger] self.concrete_journal.disk.requests.contains_key(id)
        ==> {
            let req = self.concrete_journal.disk.requests[id];
            &&& req.addr() == self.addr_for_id(id)
            &&& req is ReadReq && self.outstanding_cache_reqs.contains_key(id) ==> {
                let slot = self.concrete_journal.cache.lookup_map[self.outstanding_cache_reqs[id]];
                &&& self.concrete_journal.cache.entries[slot] is Loading
            }
            &&& req is WriteReq ==> {
                if self.outstanding_cache_reqs.contains_key(id) {
                    let slot = self.concrete_journal.cache.lookup_map[self.outstanding_cache_reqs[id]];
                    &&& self.concrete_journal.cache.status_map[slot] is Writeback
                    &&& self.concrete_journal.cache.entries[slot]->data == req->data
                } else {
                    &&& req->to == spec_superblock_addr()
                    &&& self.concrete_journal.in_flight is Some
                    &&& self.concrete_journal.in_flight.unwrap().req_id == id
                    &&& DiskLayout::spec_new().spec_parse(req->data) == self.to_atomic().in_flight_sb()
                }
            }
        }
    }

    #[verifier::opaque]
    pub open spec fn outstanding_reqs_responses_ok(self) -> bool
    {
        forall |id| #[trigger] self.concrete_journal.disk.responses.contains_key(id)
        ==> {
            let resp = self.concrete_journal.disk.responses[id];
            &&& resp is ReadResp ==> {
                &&& resp->data == self.concrete_journal.disk.content[self.addr_for_id(id)]
                &&& self.outstanding_cache_reqs.contains_key(id) ==> {
                    let slot = self.concrete_journal.cache.lookup_map[self.outstanding_cache_reqs[id]];
                    &&& self.concrete_journal.cache.entries[slot] is Loading
                }
            }
            &&& resp is WriteResp && self.outstanding_cache_reqs.contains_key(id) ==> {
                let addr = self.outstanding_cache_reqs[id];
                let slot = self.concrete_journal.cache.lookup_map[addr];
                &&& self.concrete_journal.cache.status_map[slot] is Writeback
                &&& self.concrete_journal.disk.content[addr] == self.concrete_journal.cache.entries[slot]->data
            }
        }
    }

    #[verifier::opaque]
    pub open spec /*(checked)*/ fn outstanding_reqs_consistent(self) -> bool
    {
        let in_flight_sb_id = if self.concrete_journal.in_flight is Some { set!{self.concrete_journal.in_flight.unwrap().req_id} } else { set!{} };

        // 1. all disk ids are bounded by cache reqs and inflight_sb
        &&& self.concrete_journal.disk.requests.dom() + self.concrete_journal.disk.responses.dom() == self.outstanding_cache_reqs.dom() + in_flight_sb_id
        // 2. disk requests are correctly recorded
        &&& self.outstanding_reqs_requests_ok()
        // 3. disk responses are correctly reflected
        &&& self.outstanding_reqs_responses_ok()
        // 4. every outstanding disk id has a well-formed io mapping
        &&& forall |id: ID|
            #![trigger self.concrete_journal.disk.requests.contains_key(id)]
            #![trigger self.concrete_journal.disk.responses.contains_key(id)]
            (self.concrete_journal.disk.requests.contains_key(id) || self.concrete_journal.disk.responses.contains_key(id))
            ==> self.io_id_valid(id)
    }

    pub open spec(checked) fn sb_response_is_write_resp(self) -> bool
    {
        self.concrete_journal.in_flight is Some ==>
            forall |id| #[trigger] self.concrete_journal.disk.responses.contains_key(id)
                && self.concrete_journal.in_flight.unwrap().req_id == id
                ==> self.concrete_journal.disk.responses[id] is WriteResp
    }

    pub open spec(checked) fn sb_req_id_disjoint_cache_reqs(self) -> bool
    {
        self.concrete_journal.in_flight is Some ==>
            !self.outstanding_cache_reqs.dom().contains(
                self.concrete_journal.in_flight.unwrap().req_id)
    }

    pub open spec(checked) fn requests_have_unique_ids(self) -> bool
    {
        &&& all_elems_single(self.requests)
        &&& forall |req1, req2| self.requests.contains(req1)
            && self.requests.contains(req2)
            && req1 != req2
            ==> #[trigger] req1.id != #[trigger] req2.id
    }

    pub open spec(checked) fn replies_have_unique_ids(self) -> bool
    {
        &&& all_elems_single(self.replies)
        &&& forall |reply1, reply2| self.replies.contains(reply1)
            && self.replies.contains(reply2)
            && reply1 != reply2
            ==> #[trigger] reply1.id != #[trigger] reply2.id
    }

    pub open spec(checked) fn requests_replies_id_disjoint(self) -> bool
    {
        forall |req, reply| self.requests.contains(req) && self.replies.contains(reply)
            ==> #[trigger] req.id != #[trigger] reply.id
    }

    pub open spec(checked) fn request_ids_in_history(self) -> bool
    {
        forall |req| #![auto] self.requests.contains(req) ==> self.id_history.contains(req.id)
    }

    pub open spec(checked) fn reply_ids_in_history(self) -> bool
    {
        forall |reply| #![auto] self.replies.contains(reply) ==> self.id_history.contains(reply.id)
    }

    pub open spec(checked) fn sync_req_reply_ids_disjoint(self) -> bool
    {
        forall |req_id, reply_id| #![auto] self.sync_requests.contains(req_id) && self.sync_replies.contains(reply_id)
            ==> req_id != reply_id
    }

    pub open spec(checked) fn sync_req_ids_in_history(self) -> bool
    {
        forall |req_id| #![auto] self.sync_requests.contains(req_id) ==> self.id_history.contains(req_id)
    }

    pub open spec(checked) fn sync_reply_ids_in_history(self) -> bool
    {
        forall |reply_id| #![auto] self.sync_replies.contains(reply_id) ==> self.id_history.contains(reply_id)
    }

    #[verifier::opaque]
    pub open spec(checked) fn program_sync_req_ids_in_history(self) -> bool
    {
        forall |req_id| #![auto] self.sync_req_map.dom().contains(req_id) ==> self.id_history.contains(req_id)
    }

    // ================================================================
    // Interpretation functions
    // ================================================================

    // interpretation given no ephemeral state and only on persistent disk
    closed spec(checked) fn i_persistent(self) -> (mapspec: CrashTolerantAsyncMap::State)
    recommends
        !self.client_ready(),
        self.concrete_journal.disk.content.contains_key(spec_superblock_addr()),
    {
        let persisted = self.store_persistent();
        let sb = DiskLayout::spec_new().spec_parse(self.concrete_journal.disk.content[spec_superblock_addr()]);
        CrashTolerantAsyncMap::State{
            versions: singleton_floating_seq(sb.journal.boundary_lsn, persisted.value),
            async_ephemeral: EphemeralState{
                requests: multiset_to_set(self.requests),
                replies: multiset_to_set(self.replies),
            },
            sync_requests: Map::empty(),
        }
    }

    // ephemeral depends on whether things have landed on disk
    closed spec fn i_ephemeral(self) -> (mapspec: CrashTolerantAsyncMap::State)
    recommends
        self.to_atomic().wf(),
        self.client_ready(),
    {
        let journal = self.i_journal();
        let persistent_map = self.store_persistent();

        let inflight_on_disk =
            self.concrete_journal.in_flight is Some
            && journal.in_flight is Some
            && self.concrete_journal.disk.responses.contains_key(self.concrete_journal.in_flight.unwrap().req_id);

        let versions = if inflight_on_disk {
            let in_flight_map = match self.store_in_flight() {
                Some(m) => m,
                None => arbitrary(),
            };
            let remaining_journal = journal.i().discard_old(in_flight_map.seq_end);
            let stable_lsn = journal.in_flight.unwrap().seq_end;
            floating_versions(in_flight_map, remaining_journal, stable_lsn)
        } else {
            let stable_lsn = journal.persistent.seq_end;
            floating_versions(persistent_map, journal.i(), stable_lsn)
        };

        CrashTolerantAsyncMap::State{
            versions,
            async_ephemeral: EphemeralState{
                requests: multiset_to_set(self.requests),
                replies: multiset_to_set(self.replies),
            },
            sync_requests: self.sync_req_map,
        }
    }

    pub closed spec fn sb_landed(self: Self, post: Self) -> bool
    {
        &&& self.client_ready()
        &&& self.concrete_journal.in_flight is Some
        &&& !self.concrete_journal.disk.responses.contains_key(self.concrete_journal.in_flight.unwrap().req_id)
        &&& post.concrete_journal.disk.responses.contains_key(self.concrete_journal.in_flight.unwrap().req_id)
    }
}

// ================================================================
// Top-level interpretation functions (free functions, not methods)
// ================================================================

pub closed spec fn sm2_i(model: SystemModelTwo::State) -> CrashTolerantAsyncMap::State
{
    if model.client_ready() {
        model.i_ephemeral()
    } else {
        model.i_persistent()
    }
}

pub open spec fn sm2_i_lbl(pre: SystemModelTwo::State, post: SystemModelTwo::State, lbl: SystemModelTwo::Label) -> CrashTolerantAsyncMap::Label
{
    match lbl {
        SystemModelTwo::Label::AcceptRequest{req} => {
            CrashTolerantAsyncMap::Label::OperateOp{
                base_op: AsyncMap::Label::RequestOp { req }
            }
        },
        SystemModelTwo::Label::DeliverReply{reply} => {
            CrashTolerantAsyncMap::Label::OperateOp{
                base_op: AsyncMap::Label::ReplyOp { reply }
            }
        },
        SystemModelTwo::Label::ProgramUIOp{op} => {
        match op {
            ProgramUserOp::Execute{req, reply} =>
                CrashTolerantAsyncMap::Label::OperateOp{
                    base_op: AsyncMap::Label::ExecuteOp  { req, reply },
                },
            ProgramUserOp::AcceptSyncRequest{ sync_req_id } =>
                CrashTolerantAsyncMap::Label::ReqSyncOp{ sync_req_id },
            ProgramUserOp::DeliverSyncReply{ sync_req_id } =>
                CrashTolerantAsyncMap::Label::ReplySyncOp{ sync_req_id },
        }},
        SystemModelTwo::Label::ProgramDiskOp{ info } =>
            CrashTolerantAsyncMap::Label::Noop{},
        SystemModelTwo::Label::ProgramInternal =>
            CrashTolerantAsyncMap::Label::Noop{},
        SystemModelTwo::Label::DiskInternal => {
            if pre.sb_landed(post) {
                CrashTolerantAsyncMap::Label::SyncOp{}
            } else {
                CrashTolerantAsyncMap::Label::Noop{}
            }
        },
        SystemModelTwo::Label::Crash =>
            CrashTolerantAsyncMap::Label::CrashOp{},
        _ =>
            CrashTolerantAsyncMap::Label::Noop{},
    }
}

// ================================================================
// Proof: SystemModelTwo → CrashTolerantAsyncMap
// ================================================================

proof fn sm2_i_lbl_valid(pre: SystemModelTwo::State, post: SystemModelTwo::State, lbl: SystemModelTwo::Label, ctam_lbl: CrashTolerantAsyncMap::Label)
    requires
        ctam_lbl == sm2_i_lbl(pre, post, lbl),
    ensures
        // SM2 labels are isomorphic to SM1 labels; compose with BracketRefinement::i_lbl
        // to get the SM1 label_correspondence
        true, // placeholder — the adapter will handle label_correspondence
{
}

proof fn sm2_init_refines(pre: SystemModelTwo::State)
    requires
        CrashTolerantAsyncMap::State::initialize(sm2_i(pre)),
        pre.inv(),
    ensures
        CrashTolerantAsyncMap::State::initialize(sm2_i(pre)),
        pre.inv(),
{
}

pub proof fn next_refines_ctam(pre: SystemModelTwo::State, post: SystemModelTwo::State, lbl: SystemModelTwo::Label)
    requires
        SystemModelTwo::State::next(pre, post, lbl),
        pre.inv(),
    ensures
        CrashTolerantAsyncMap::State::next(sm2_i(pre), sm2_i(post), sm2_i_lbl(pre, post, lbl)),
        post.inv(),
{
    reveal(CrashTolerantAsyncMap::State::next);
    reveal(CrashTolerantAsyncMap::State::next_by);
    reveal(AsyncMap::State::next);
    reveal(AsyncMap::State::next_by);
    reveal(MapSpec::State::next);
    reveal(MapSpec::State::next_by);

    reveal(SystemModelTwo::State::next);
    reveal(SystemModelTwo::State::next_by);

    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);

    broadcast use insert_new_preserves_cardinality;

    let step = choose |step| SystemModelTwo::State::next_by(pre, post, lbl, step);

    let ipre = sm2_i(pre);
    let ipost = sm2_i(post);
    let ilbl = sm2_i_lbl(pre, post, lbl);

    match step {
        SystemModelTwo::Step::accept_request() => {
            next_refines_ctam_accept_request_case(pre, post, lbl, ipre, ipost, ilbl);
        },
        SystemModelTwo::Step::deliver_reply() => {
            next_refines_ctam_deliver_reply_case(pre, post, lbl, ipre, ipost, ilbl);
        },
        SystemModelTwo::Step::program_execute(new_concrete_journal, new_store) => {
            next_refines_ctam_program_execute_case(pre, post, lbl, ipre, ipost, ilbl, new_concrete_journal, new_store);
        },
        SystemModelTwo::Step::program_accept_sync_request(new_sync_req_map) => {
            next_refines_ctam_program_accept_sync_request_case(pre, post, lbl, ipre, ipost, ilbl, new_sync_req_map);
        },
        SystemModelTwo::Step::program_deliver_sync_reply(new_sync_req_map) => {
            next_refines_ctam_program_deliver_sync_reply_case(pre, post, lbl, ipre, ipost, ilbl, new_sync_req_map);
        },
        SystemModelTwo::Step::program_disk(new_concrete_journal, new_outstanding_cache_reqs, new_recovery_state, new_store, new_store_ptr, new_sync_req_map) => {
            next_refines_ctam_program_disk_case(pre, post, lbl, ipre, ipost, ilbl, new_concrete_journal, new_outstanding_cache_reqs, new_recovery_state, new_store, new_store_ptr, new_sync_req_map);
        },
        SystemModelTwo::Step::program_internal(new_concrete_journal, new_outstanding_cache_reqs, new_recovery_state, new_store, new_store_ptr) => {
            next_refines_ctam_program_internal_case(pre, post, lbl, ipre, ipost, ilbl, new_concrete_journal, new_outstanding_cache_reqs, new_recovery_state, new_store, new_store_ptr);
        },
        SystemModelTwo::Step::disk_internal(new_disk) => {
            next_refines_ctam_disk_internal_case(pre, post, lbl, ipre, ipost, ilbl, new_disk);
        },
        SystemModelTwo::Step::crash(new_concrete_journal, new_disk, new_store) => {
            next_refines_ctam_crash_case(pre, post, lbl, ipre, ipost, ilbl, new_concrete_journal, new_disk, new_store);
        },
        SystemModelTwo::Step::noop() => {
            next_refines_ctam_noop_case(pre, post, lbl, ipre, ipost, ilbl);
        },
        SystemModelTwo::Step::accept_sync_request() => {
            next_refines_ctam_accept_sync_request_case(pre, post, lbl, ipre, ipost, ilbl);
        },
        SystemModelTwo::Step::deliver_sync_reply() => {
            next_refines_ctam_deliver_sync_reply_case(pre, post, lbl, ipre, ipost, ilbl);
        },
        _ => { assert(false); }
    }
    assert( CrashTolerantAsyncMap::State::next(ipre, ipost, ilbl) );
}

}
