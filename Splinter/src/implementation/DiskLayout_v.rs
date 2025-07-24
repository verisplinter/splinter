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
use crate::implementation::VecMap_v::*;
use crate::implementation::SuperblockTypes_v::*;

verus! {

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
