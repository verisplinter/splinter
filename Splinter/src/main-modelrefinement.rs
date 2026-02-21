#![verifier::loop_isolation(false)]
#![allow(non_snake_case)]

#[path = "spec"]
pub mod spec {
    pub mod AsyncDisk_t;
    pub mod FloatingSeq_t;
    pub mod ImplDisk_t;
    pub mod KeyType_t;
    pub mod MapSpec_t;
    pub mod Messages_t;
    pub mod TotalKMMap_t;
    pub mod injective_t;
}

#[path = "abstract_system"]
pub mod abstract_system {
    pub mod AbstractCrashAwareJournal_v;
    pub mod AbstractCrashAwareMap_v;
    pub mod AbstractCrashAwareSystem_v;
    pub mod AbstractCrashAwareSystemRefinement_v;
    pub mod AbstractJournal_v;
    pub mod AbstractMap_v;
    pub mod MsgHistory_v;
    pub mod StampedMap_v;
}

#[path = "disk"]
pub mod disk {
    pub mod GenericDisk_v;
}

#[path = "journal"]
pub mod journal {
    pub mod LinkedJournal_v;
    pub mod LinkedJournalRefinement_v;
    pub mod PagedJournal_v;
    pub mod PagedJournalRefinement_v;
}

#[path = "marshalling"]
pub mod marshalling {
    #[macro_use]
    pub mod StructMarshalMacro_v;
    pub mod IAddressFormat_v;
    pub mod IJournalRecordFormat_v;
    pub mod IJournalSnapshotFormat_v;
    pub mod ISuperblockFormat_v;
    pub mod IntegerMarshalling_v;
    pub mod KeyFormat_v;
    pub mod KeyValueFormat_v;
    pub mod KeyedMessageFormat_v;
    pub mod Marshalling_v;
    pub mod MessageFormat_v;
    pub mod NatFormat_v;
    pub mod OptionFormat_v;
    pub mod ResizableUniformSizedSeq_v;
    pub mod SeqMarshalling_v;
    pub mod Slice_v;
    pub mod StaticallySized_v;
    pub mod UniformPairFormat_v;
    pub mod UniformSized_v;
    pub mod UniformSizedMarshal_v;
    pub mod WF_v;
    pub mod Wrappable_v;
    pub mod math_v;
}

#[path = "allocation_layer"]
pub mod allocation_layer {
    pub mod LikesJournal_v;
    pub mod LikesJournalRefinement_v;
}

#[path = "trusted"]
pub mod trusted {
    pub mod ClientAPI_t;
    pub mod KVStoreTokenized_t;
    pub mod ProgramModelTrait_t;
    pub mod RefinementObligation_t;
    pub mod ReqReply_t;
    pub mod SystemModel_t;
}

#[path = "implementation"]
pub mod implementation {
    pub mod AtomicState_v;
    pub mod Cache_v;
    pub mod CachedJournal_v;
    pub mod ConcreteProgramModel_v;
    pub mod DiskLayout_v;
    pub mod FracCacheImpl_v;
    pub mod ILsnAddrIndex_v;
    pub mod JournalImpl_v;
    pub mod JournalTypes_v;
    pub mod BracketRefinement_v;
    pub mod ConcreteJournal_v;
    pub mod ConcreteJournalRefinement_v;
    pub mod JournalCoordinationRefinement_v;
    pub mod JournalCoordinationSystem_v;
    pub mod ModelRefinement_v;
    pub mod ModelRefinementTwo_v;
    pub mod MultisetMapRelation_v;
    pub mod SystemModelTwo_v;
    pub mod OverflowFiction_v;
    pub mod SuperblockTypes_v;
    pub mod VecMap_v;
}

fn main() {}
