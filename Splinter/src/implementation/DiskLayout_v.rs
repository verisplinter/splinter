// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
// use vstd::hash_map::*;
use crate::spec::MapSpec_t::*;
use crate::spec::AsyncDisk_t::*;
use crate::spec::ImplDisk_t::*;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::spec::TotalKMMap_t::*;
use crate::spec::FloatingSeq_t::*;
use crate::abstract_system::MsgHistory_v::{MsgHistory, KeyedMessage};
use crate::abstract_system::StampedMap_v::*;
use crate::implementation::VecMap_v::*;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::Marshalling_v::{Marshal, Deepview};
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::StaticallySized_v::StaticallySized;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::UniformPairFormat_v::UniformPairMarshal;
use crate::marshalling::KeyedMessageFormat_v::KeyedMessageFormat;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;

verus! {

pub type ILsn = u64;

pub open spec(checked) fn singleton_floating_seq(at_index: nat, kmmap: TotalKMMap) -> FloatingSeq<Version>
{
    FloatingSeq::new(at_index, at_index+1,
          |i| Version{ appv: MapSpec::State{ kmmap } } )
}

pub open spec(checked) fn view_store_as_kmmap(store: VecMap<Key, Value>) -> TotalKMMap
{
    TotalKMMap(Map::new(
            |k: Key| true,
            |k: Key| if store@.contains_key(k@) { Message::Define{value: store@[k@]} }
                     else { Message::empty() }))
}

pub open spec(checked) fn view_store_as_singleton_floating_seq(at_index: nat, store: VecMap<Key, Value>) -> FloatingSeq<Version>
{
    singleton_floating_seq(at_index, view_store_as_kmmap(store))
}

pub struct Superblock {
    pub store: PersistentState, // mapspec
    // need version so recovery knows the shape of the (mostly-empty) history to reconstruct (the LSN)
    pub version_index: nat,
}

// An "abstract journal" is a hop between the impl Journal type and the abstract MsgHistory it
// represents.
pub struct AJournal {
    pub msg_history: Seq<KeyedMessage>,
    pub seq_start: ILsn,
}

impl View for AJournal
{
    type V = MsgHistory;

    open spec fn view(&self) -> Self::V
    {
        let seq_start = self.seq_start as nat;
        let seq_end = (self.msg_history.len() + seq_start) as nat;
        let msgs = Map::new(
            |k: LSN| seq_start <= k < seq_end,
            |k: LSN| self.msg_history[k - seq_start]
        );
        MsgHistory{msgs, seq_start, seq_end}
    }
}

pub struct Journal {
    pub msg_history: Vec<KeyedMessage>,
    pub seq_start: ILsn,
}

impl View for Journal {
    type V = MsgHistory;

    open spec fn view(&self) -> Self::V
    {
        self.deepv()@
    }
}

// The deepview only takes us up to AJournal, so that the marshalling spec fns talk
// about Seq<KeyedMessage>, not the Map-shaped MsgHistory object.
impl Deepview<AJournal> for Journal {
    open spec fn deepv(&self) -> AJournal {
        AJournal{msg_history: self.msg_history@, seq_start: self.seq_start}
    }
}

pub struct ISuperblock {
    pub journal: Journal,
    pub store: VecMap<Key, Value>,
    // need version so recovery knows the shape of the (mostly-empty) history to reconstruct (the LSN)
    pub version_index: u64,
}

impl View for ISuperblock {
    type V = Superblock;

    open spec fn view(&self) -> Self::V
    {
        let map = self.journal.to_stamped_map();
        Superblock{
            store: PersistentState{ appv: MapSpec::State{ kmmap: map.value}},
            version_index: map.seq_end
        }
    }
}

// TODO move marshalling into its own file
struct JournalMarshal {
    ilsn_fmt: IntFormat::<ILsn>,
    msg_history_fmt: ResizableUniformSizedElementSeqFormat<KeyedMessageFormat, u8>,
}

impl JournalMarshal {
    fn new() -> Self
    {
        JournalMarshal{
            ilsn_fmt: IntFormat::new(),
            // TODO hardcoded total size
            msg_history_fmt: ResizableUniformSizedElementSeqFormat::new(
                KeyedMessageFormat::new(),
                IntFormat::<u8>::new(),
                200),
        }
    }
}

impl Marshal for JournalMarshal {
    type DV = AJournal;
    type U = Journal;

    closed spec fn valid(&self) -> bool {
        self.msg_history_fmt.valid()
    }

    closed spec fn parsable(&self, data: Seq<u8>) -> bool
    {
        &&& ILsn::uniform_size() <= data.len()
        &&& self.msg_history_fmt.parsable(
            data.subrange(ILsn::uniform_size() as int, data.len() as int))
    }

    closed spec fn parse(&self, data: Seq<u8>) -> Self::DV
    {
        let bdy0 = ILsn::uniform_size() as int;
        let bdy1 = data.len() as int;
        let seq_start = self.ilsn_fmt.parse(data.subrange(0, bdy0)) as ILsn;
        let msg_history = self.msg_history_fmt.parse(data.subrange(bdy0, bdy1));
        AJournal{seq_start, msg_history}
    }

    exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
    {
        if slice.len() < ILsn::exec_uniform_size() {
            // Not enough slice for the format
            None
        } else if data.len() < slice.end {
            // Not enough data for the slice
            None
        } else {
            let seq_start_slice = slice.subslice(0, ILsn::exec_uniform_size());
            let seq_start = self.ilsn_fmt.exec_parse(&seq_start_slice, data);
            let skip = ILsn::exec_uniform_size();
            let msg_history_slice = slice.subslice(skip, slice.len());
            proof {
                let ghost idata = slice@.i(data@);
                assert( idata.subrange(ILsn::uniform_size() as int, idata.len() as int)
                    == msg_history_slice@.i(data@) ); // extn
            }
            let msg_history = match self.msg_history_fmt.try_parse(&msg_history_slice, data) {
                None => {
                    return None;
                }
                Some(msg_history) => msg_history
            };
            let out = Journal{msg_history, seq_start};

            proof {
                // extn: subrange transitivity
                let bdy0 = ILsn::uniform_size() as int;
                let bdy1 = slice@.len() as int;
                let idata = slice@.i(data@);
                assert( idata.subrange(0, bdy0) == seq_start_slice@.i(data@) );   // extn
                assert( seq_start == self.parse(idata).seq_start );
                assert( msg_history@ == self.parse(idata).msg_history );
                assert( out.deepv() == self.parse(idata) );   // extn
            }
            Some(out)
        }
    }
    
    closed spec fn marshallable(&self, value: Self::DV) -> bool
    {
        &&& ILsn::uniform_size() + self.msg_history_fmt.spec_size(value.msg_history) <= usize::MAX 
        &&& self.msg_history_fmt.marshallable(value.msg_history)
    }
        
    closed spec fn spec_size(&self, value: Self::DV) -> usize
    {
        (ILsn::uniform_size() + self.msg_history_fmt.spec_size(value.msg_history)) as usize
    }

    exec fn exec_size(&self, value: &Self::U) -> (sz: usize)
    {
        ILsn::exec_uniform_size() + self.msg_history_fmt.exec_size(&value.msg_history)
    }

    exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
    {
        let send = self.ilsn_fmt.exec_marshall(&value.seq_start, data, start);

        assert( self.ilsn_fmt.parse(data@.subrange(start as int, send as int)) == value.seq_start );
        let ghost mid_data = data@;
        let end = self.msg_history_fmt.exec_marshall(&value.msg_history, data, send);
        proof {
            // extn: second exec_marshall didn't stomp first
            assert( mid_data.subrange(start as int, send as int) == data@.subrange(start as int, send as int) );

            // extn: subrange transitivity
            let bdy0 = ILsn::uniform_size() as int;
            let bdy1 = (end - start) as int;
            assert( data@.subrange(start as int, end as int).subrange(0, bdy0)
                    == data@.subrange(start as int, send as int) ); // extn

            assert( data@.subrange(start as int, end as int).subrange(bdy0, bdy1)
                    == data@.subrange(send as int, end as int) );
            assert( self.parse(data@.subrange(start as int, end as int)).seq_start == value.seq_start );
            assert( self.parse(data@.subrange(start as int, end as int)).msg_history == value.msg_history@ );
            assert( self.parse(data@.subrange(start as int, end as int)) == value.deepv() );
        }
        end
    }
    
}

// struct ISuperblockMarshal {
//     version_fmt: IntFormat::<u64>;
//     journal_fmt: JournalMarshal,
//     store_fmt: ResizableUniformSizedElementSeqFormat<KeyValueMarshal, u8>,
// }
// 
// impl ISuperblockMarshal {
//     fn new() -> Self
//     {
//         ISuperblockMarshal {
//             version_fmt: IntFormat::new(),
//             // TODO hardcoded total size
//             journal_fmt: JournalMarshal::new(),
//             store_fmt: ResizableUniformSizedElementSeqFormat::new(
//                 KeyValueFormat::new(),
//                 IntFormat::<u8>::new(),
//                 200),
//         }
//     }
// }
// 
// pub struct ASuperblock {
//     pub journal: AJournal,
//     pub store: Seq(VecMap<Key, Value>,
//     // need version so recovery knows the shape of the (mostly-empty) history to reconstruct (the LSN)
//     pub version_index: u64,
// }
// impl Marshal for ISuperblockMarshal {
//     type DV = AJournal;
//     type U = ISuperblock;
// 
//     closed spec fn valid(&self) -> bool {
//         self.msg_history_fmt.valid()
//     }
// 
//     closed spec fn parsable(&self, data: Seq<u8>) -> bool
//     {
//         &&& ILsn::uniform_size() <= data.len()
//         &&& self.msg_history_fmt.parsable(
//             data.subrange(ILsn::uniform_size() as int, data.len() as int))
//     }
// 
//     closed spec fn parse(&self, data: Seq<u8>) -> Self::DV
//     {
//         let bdy0 = ILsn::uniform_size() as int;
//         let bdy1 = data.len() as int;
//         let seq_start = self.ilsn_fmt.parse(data.subrange(0, bdy0)) as ILsn;
//         let msg_history = self.msg_history_fmt.parse(data.subrange(bdy0, bdy1));
//         AJournal{seq_start, msg_history}
//     }
// 
//     exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
//     {
//         if slice.len() < ILsn::exec_uniform_size() {
//             // Not enough slice for the format
//             None
//         } else if data.len() < slice.end {
//             // Not enough data for the slice
//             None
//         } else {
//             let seq_start_slice = slice.subslice(0, ILsn::exec_uniform_size());
//             let seq_start = self.ilsn_fmt.exec_parse(&seq_start_slice, data);
//             let skip = ILsn::exec_uniform_size();
//             let msg_history_slice = slice.subslice(skip, slice.len());
//             proof {
//                 let ghost idata = slice@.i(data@);
//                 assert( idata.subrange(ILsn::uniform_size() as int, idata.len() as int)
//                     == msg_history_slice@.i(data@) ); // extn
//             }
//             let msg_history = match self.msg_history_fmt.try_parse(&msg_history_slice, data) {
//                 None => {
//                     return None;
//                 }
//                 Some(msg_history) => msg_history
//             };
//             let out = Journal{msg_history, seq_start};
// 
//             proof {
//                 // extn: subrange transitivity
//                 let bdy0 = ILsn::uniform_size() as int;
//                 let bdy1 = slice@.len() as int;
//                 let idata = slice@.i(data@);
//                 assert( idata.subrange(0, bdy0) == seq_start_slice@.i(data@) );   // extn
//                 assert( seq_start == self.parse(idata).seq_start );
//                 assert( msg_history@ == self.parse(idata).msg_history );
//                 assert( out.deepv() == self.parse(idata) );   // extn
//             }
//             Some(out)
//         }
//     }
//     
//     closed spec fn marshallable(&self, value: Self::DV) -> bool
//     {
//         &&& ILsn::uniform_size() + self.msg_history_fmt.spec_size(value.msg_history) <= usize::MAX 
//         &&& self.msg_history_fmt.marshallable(value.msg_history)
//     }
//         
//     closed spec fn spec_size(&self, value: Self::DV) -> usize
//     {
//         (ILsn::uniform_size() + self.msg_history_fmt.spec_size(value.msg_history)) as usize
//     }
// 
//     exec fn exec_size(&self, value: &Self::U) -> (sz: usize)
//     {
//         ILsn::exec_uniform_size() + self.msg_history_fmt.exec_size(&value.msg_history)
//     }
// 
//     exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize)
//     {
//         let send = self.ilsn_fmt.exec_marshall(&value.seq_start, data, start);
// 
//         assert( self.ilsn_fmt.parse(data@.subrange(start as int, send as int)) == value.seq_start );
//         let ghost mid_data = data@;
//         let end = self.msg_history_fmt.exec_marshall(&value.msg_history, data, send);
//         proof {
//             // extn: second exec_marshall didn't stomp first
//             assert( mid_data.subrange(start as int, send as int) == data@.subrange(start as int, send as int) );
// 
//             // extn: subrange transitivity
//             let bdy0 = ILsn::uniform_size() as int;
//             let bdy1 = (end - start) as int;
//             assert( data@.subrange(start as int, end as int).subrange(0, bdy0)
//                     == data@.subrange(start as int, send as int) ); // extn
// 
//             assert( data@.subrange(start as int, end as int).subrange(bdy0, bdy1)
//                     == data@.subrange(send as int, end as int) );
//             assert( self.parse(data@.subrange(start as int, end as int)).seq_start == value.seq_start );
//             assert( self.parse(data@.subrange(start as int, end as int)).msg_history == value.msg_history@ );
//             assert( self.parse(data@.subrange(start as int, end as int)) == value.deepv() );
//         }
//         end
//     }
//     
// }


pub closed spec fn spec_marshall(superblock: Superblock) -> (out: RawPage)
{
    arbitrary()
}

pub closed spec fn spec_parse(raw_page: RawPage) -> (out: Superblock)
{
    arbitrary()
}

pub fn marshall(sb: &ISuperblock) -> (out: IPageData)
ensures
    out@ == spec_marshall(sb@)
{
    assume( false ); // TODO
    unreached()
}

pub fn parse(raw_page: &IPageData) -> (out: ISuperblock)
ensures
    out@ == spec_parse(raw_page@)
{
    assume( false ); // TODO
    unreached()
}

pub open spec fn spec_superblock_addr() -> Address {
    Address{au: 0, page: 0}
}

pub fn superblock_addr() -> (out: IAddress)
ensures out@ == spec_superblock_addr()
{
    IAddress{au: 0, page: 0}
}

pub open spec fn mkfs(disk: Disk) -> bool
{
    &&& disk.contains_key(spec_superblock_addr())
    &&& disk[spec_superblock_addr()] ==
        spec_marshall(Superblock{
            store: PersistentState{ appv: my_init() },
            version_index: 0,
        })
}

}//verus!
