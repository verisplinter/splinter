// Temporarily keep the root crate off the AtomicState/SM1 adapter path so
// AtomicState_v.rs can evolve independently of the CrashAwareCachingDiskSystem refinement proof.
// pub mod ConcreteProgramModel_v;
// Temporarily disabled while AllocationJournal_v is refactored away from
// the old embedded LinkedJournal state shape.
// pub mod ModelRefinement_v;
// pub mod Implementation_v;
pub mod MultisetMapRelation_v;
// pub mod AtomicState_v;
// pub mod AnotherAtomicState_v;
// pub mod AnotherAtomicJournalRefinement_v;
// pub mod AnotherAtomicBranchRefinement_v;
// pub mod AnotherProgramModel_v;
pub mod AbstractSuperblock_v;
// pub mod RecoveryState_v;
pub mod DiskLayout_v;
pub mod Cache_v;
pub mod FracCacheImpl_v;
pub mod CachingDisk_v;
// pub mod CachingDiskAdapterRefinement_v;
pub mod CachingDiskJournal_v;
pub mod CachingDiskJournalRefinement_v;
pub mod CachingDiskBranch_v;
pub mod CachingDiskBranchRefinement_v;
pub mod CrashAwareCachingDiskBranch_v;
pub mod CrashAwareCachingDiskBranchRefinement_v;
pub mod CrashAwareCachingDiskJournal_v;
pub mod CrashAwareCachingDiskJournalRefinement_v;
pub mod CachedJournal_v;
pub mod ILsnAddrIndex_v;
pub mod JournalImpl_v; // copy of LikesJournal_v
pub mod CachedBranch_v;
pub mod AllocationBranchStack_v;
pub mod AllocationBranchStackRefinement_v;
pub mod CrashAwareAllocationBranchStack_v;
pub mod CrashAwareAllocationBranchStackRefinement_v;
pub mod IBranchNode_v;
pub mod CrashAwareCachingDiskSystem_v;
// pub mod BracketRefinement_v;
pub mod CrashAwareCachingDiskSystemRefinement_v;
pub mod VecMap_v;
pub mod JournalTypes_v;
pub mod SuperblockTypes_v;
pub mod OverflowFiction_v;
pub mod PageAllocator_v;
// pub mod StoreImpl_v;
