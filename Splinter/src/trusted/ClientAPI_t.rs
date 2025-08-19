// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use std::sync::atomic::{AtomicU64, Ordering};
use vstd::{prelude::*};
use vstd::tokens::InstanceId;

use crate::spec::MapSpec_t::{ID};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::Value;
// use crate::spec::AsyncDisk_t;
use crate::spec::ImplDisk_t::*;

use crate::implementation::MultisetMapRelation_v::*;    // TODO move to _t, I guess

use crate::trusted::ReqReply_t::*;
use crate::trusted::KVStoreTokenized_t::*;
use crate::trusted::ProgramModelTrait_t::*;

use std::fs::*;
use std::path::*;
use std::os::unix::fs::FileExt;
use std::sync::Arc;
use std::sync::mpsc;
use std::sync::mpsc::*;
use std::collections::HashSet;
use std::{thread, time};

// The message that rides on the channel from worker threads back to the ClientAPI main thread.
pub struct ChannelResponse {
    id: ID,
    value: IDiskResponse,
}

// The shared object on which threads make IO calls and deliver their responses back through
// a shared channel.
pub struct DiskWorker {
    file: File,
    sender: Sender<ChannelResponse>,
}

impl DiskWorker {
    fn write_work(&self, block: u64, payload: Vec<u8>) {
        match self.file.write_all_at(&payload, BLOCK_SIZE as u64 * block) {
            Err(why) => panic!("Write failed: {}", why),
            Ok(()) => (),
        };
    }

    fn read_at(&self, block: u64) -> Vec<u8> {
        let mut rv = vec![0; BLOCK_SIZE as usize];
        match self.file.read_exact_at(&mut rv, BLOCK_SIZE as u64 * block) {
            Err(why) => panic!("Read failed: {}", why),
            Ok(()) => (),
        };
        rv
    }

    fn deliver_response(&self, response: ChannelResponse) {
        self.sender.send(response).unwrap();
    }
}

// The object that's uniquely owned by the ClientAPI thread.
pub struct TheDisk {
    disk_worker: Arc<DiskWorker>,
    receiver: Receiver<ChannelResponse>,
}

verus! {
pub const BLOCK_SIZE: usize = 1000;
}

impl TheDisk {
    fn new() -> Self
    {
        let path = Path::new("storage.bin");
        let file = match OpenOptions::new().read(true).write(true).open(&path) {
            Err(why) => panic!("Couldn't open {}: {}", path.display(), why),
            Ok(file) => file,
        };
        let (sender, receiver) = mpsc::channel();
        TheDisk{ disk_worker: Arc::new(DiskWorker{file, sender}), receiver}
    }
}

struct WriteReq {
    disk: Arc<DiskWorker>,
    id: ID,
    block: u64,
    payload: Vec<u8>,
}

impl WriteReq {
    fn run(self) {
        self.disk.write_work(self.block, self.payload);
        self.disk.deliver_response(ChannelResponse{id: self.id, value: IDiskResponse::WriteResp{}});
    }
}

struct ReadReq {
    disk: Arc<DiskWorker>,
    id: ID,
    block: u64,
}

impl ReadReq {
    fn run(&self) {
        let v = self.disk.read_at(self.block);
        self.disk.deliver_response(ChannelResponse{id: self.id,
            value: IDiskResponse::ReadResp{ data: v } });
    }
}

verus! {

// defines the set of allowable externally visible calls by the implementer program
// right now this is tightly integrated with the implementer's tokenized state machine 
// definition but ideally we want to provide a composed SM consisted of a trusted
// request & reply tokenized SM & a tokenized program SM

// external body to prevent unprotected construction
#[verifier::external_body]
#[verifier::reject_recursive_types(ProgramModel)]
pub struct ClientAPI<ProgramModel: ProgramModelTrait>{
    pub id: AtomicU64,
    pub inputs: Vec<Input>,
    pub outstanding_request_ids: HashSet<ID>,
    pub the_disk: TheDisk,
    pub _p: std::marker::PhantomData<(ProgramModel,)>,
}

pub struct PollResult {
    pub user_input_ready: bool,
    pub disk_response_ready: bool,
}

pub struct UserRequestRecord<ProgramModel: ProgramModelTrait> {
    pub request: Request,
    pub token: Tracked<KVStoreTokenized::requests<ProgramModel>>,
}

pub struct DiskResponseRecord<ProgramModel: ProgramModelTrait> {
    pub id: ID,
    pub disk_response: IDiskResponse,
    pub token: Tracked<KVStoreTokenized::disk_responses_multiset<ProgramModel>>,
}

impl<ProgramModel: ProgramModelTrait> ClientAPI<ProgramModel>{
    #[verifier::external_body]
    pub fn new(instance: Ghost<InstanceId>, script_phase: Option<usize>) -> (out: Self)
        ensures out.instance_id() == instance
    {
        let inputs =
            match script_phase {
                None => vec![],
                Some(0) => vec![
                    Input::NoopInput{},
                    Input::PutInput{key: Key(1), value: Value(11)},
                    Input::QueryInput{key: Key(1)},
                    Input::QueryInput{key: Key(0)},
                    Input::QueryInput{key: Key(3)},
                    Input::PutInput{key: Key(3), value: Value(33)},
                    Input::QueryInput{key: Key(3)},
                    Input::SyncInput{},
                    Input::QueryInput{key: Key(3)},
                    Input::SimulateCrash,
                ],
                Some(1) => vec![
                    Input::QueryInput{key: Key(1)},
                    Input::QueryInput{key: Key(3)},
                ],
                _ => panic!(),
            };

        Self{
            id: AtomicU64::new(0),
            inputs,
            outstanding_request_ids: HashSet::new(),
            the_disk: TheDisk::new(),
            _p: std::marker::PhantomData
        }
    }
    
    #[verifier::external_body]
    pub uninterp spec fn instance_id(&self) -> InstanceId;

    // right now this is a tightly coupled API, we cannot ensure that the result is 
    // comes from the tokenized state machine instance transition due to it being in proof mode
    // we want (out.1, out.2) == self.instance_id().request(KVStoreTokenized::Label::RequestOp{req})
    // but this ensure is rolling out the result of the ensure
    #[verifier::external_body]
    pub fn receive_request(&mut self, print: bool) -> (out: Option<UserRequestRecord<ProgramModel>>)
    ensures
        self.instance_id() == old(self).instance_id(),
        match out {
            None => true,
            Some(rec) => {
                &&& rec.token@.instance_id() == self.instance_id()
                &&& rec.token@.element() == rec.request
            }
        }
    {
        // Special case the control flow for the case where the next step is SimulateCrash;
        // this is the only case where we delay replying.
        if 0 < self.inputs.len() && match self.inputs[0] { Input::SimulateCrash => true, _ => false } {
            if !self.outstanding_request_ids.is_empty() {
                // Don't want to crash (in this scripty mode) until all the outstanding requests have been retired
                println!("SimulateCrash waiting for {:?}", self.outstanding_request_ids);
                return None;
            }
            // okay, now we can fall through, consume the input token, and tell the impl to exit its main loop.
        }

        let id = self.id.fetch_add(1, Ordering::SeqCst);
        let input = if 0 < self.inputs.len() {
            self.inputs.remove(0)
        } else {
            return None;
        };

        let request = Request {input, id};
        if print {
            println!("request input {:?}", request);
        }
        self.outstanding_request_ids.insert(id);

        Some(UserRequestRecord{request, token: Tracked::assume_new()})
    }

    #[verifier::external_body]
    pub fn receive_noop_request(&mut self) -> (out: (Request, Tracked<KVStoreTokenized::requests<ProgramModel>>))
    ensures
        self.instance_id() == old(self).instance_id(),
        out.1@.instance_id() == self.instance_id(),
        out.1@.element() == out.0,
        (out.0.input == Input::NoopInput{}),
    {
        let id = self.id.fetch_add(1, Ordering::SeqCst);
        let input = Input::NoopInput{};
        let request = Request {input, id};
        (request, Tracked::assume_new())
    }


    // NOTE: corresponds to a tokenized state machine reply step, consumes the reply shard
    #[verifier::external_body]
    pub fn send_reply(&mut self, reply: Reply,  reply_shard: Tracked<KVStoreTokenized::replies<ProgramModel>>, print: bool)
        requires 
            reply_shard@.instance_id() == old(self).instance_id(),
            reply_shard@.element() == reply
        ensures self.instance_id() == old(self).instance_id(),
    {
        self.outstanding_request_ids.remove(&reply.id);
        if print {
            println!("   reply {:?}", reply);
            println!("");
        }
    }

    #[verifier::external_body]
    pub proof fn send_disk_request_predict_id(&self) -> (tracked out: ID)
    {
        //Tracked::assume_new()
        let Tracked(out) = Tracked::assume_new(); out
    }

    pub fn i_page_count() -> (out: u64)
        ensures out as nat == 7
        // ensures out as nat == AsyncDisk_t::page_count()
        // well that's difficult to ensure since the abstract page_count() is uninterp
    {
        7
    }
    
    pub fn block_num(ia: &IAddress) -> u64
    {
        ia.au as u64 * Self::i_page_count() + ia.page as u64
    }

    #[verifier::external_body]
    pub fn send_disk_request(&mut self, disk_req: IDiskRequest, id_perm: Tracked<ID>, 
        disk_request_tokens: Tracked<KVStoreTokenized::disk_requests_multiset<ProgramModel>>) -> (out: ID)
    requires
        disk_request_tokens@.multiset() == multiset_map_singleton(id_perm@, disk_req@),
    ensures
        self.instance_id() == old(self).instance_id(),
        out == id_perm@,
    {
        let id = self.id.fetch_add(1, Ordering::SeqCst);
        let disk = self.the_disk.disk_worker.clone();
        let req = match disk_req {
            IDiskRequest::ReadReq{from} => {
                thread::spawn(move ||
                    ReadReq{ disk, id, block: Self::block_num(&from) }.run())
            },
            IDiskRequest::WriteReq{to, data} => {
                thread::spawn(move ||
                    WriteReq{ disk, id, block: Self::block_num(&to), payload: data }.run())
            },
        };
        
        id
    }

    // TODO make this async or polling Option or maybe a cheap proof-free way to poll whether a
    // response is waiting?
    #[verifier::external_body]
    pub fn receive_disk_response(&mut self)
        -> (out: Option<DiskResponseRecord<ProgramModel>>)
    ensures
        self.instance_id() == old(self).instance_id(),
        match out {
            None => true,
            Some(rec) => {
                &&& rec.token@.instance_id() == self.instance_id()
                &&& rec.token@.multiset() == multiset_map_singleton(rec.id, rec.disk_response@)
            }
        }
    {
        match self.the_disk.receiver.try_recv() {
            Err(TryRecvError::Empty) => { None },
            Err(TryRecvError::Disconnected) => { panic!("disconnected!?") },
            Ok(ChannelResponse{id, value}) => {
                return Some(DiskResponseRecord{id, disk_response: value, token: Tracked::assume_new()})
            }
        }
    }

    // Convenience wrapper for the very special case of recover, which is the only place we expect
    // to make blocking calls.
    #[verifier::exec_allows_no_decreases_clause]    // main loop doesn't terminate
    pub fn blocking_receive_disk_response(&mut self)
        -> (rec: DiskResponseRecord<ProgramModel>)
    ensures
        self.instance_id() == old(self).instance_id(),
        rec.token@.instance_id() == self.instance_id(),
        rec.token@.multiset() == multiset_map_singleton(rec.id, rec.disk_response@),
    {
        let mut t = 0;
        loop
            invariant self.instance_id() == old(self).instance_id(),
        {
            if t > 10 {
                self.log("...io...");
                t = 0;
            }
            match self.receive_disk_response() {
                None => { self.sleep_a_little(); t += 1 },
                Some(rec) => { return rec; }
            }
        }
    }

    #[verifier::external_body]
    pub fn sleep_a_little(&self) {
        thread::sleep(time::Duration::from_millis(100));
    }

    #[verifier::external_body]
    pub fn log(&self, s: &str) {
        println!("{}", s)
    }


    // Seems like it should always be okay to brew up a token containing an empty multiset (an empty shard).
    // Yeah, MultisetToken::empty() does that.
//     #[verifier::external_body]
//     pub proof fn receive_disk_nothing(&self) -> (out: KVStoreTokenized::disk_requests_multiset)
//     ensures
//         out@.instance_id() == self.instance_id(),
//     {
//         Tracked::assume_new()
//     }

}

} 

