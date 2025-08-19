use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*; // needed for Ghost, but that gets erased.

use crate::trusted::KVStoreTrait_t::*;
use crate::trusted::ClientAPI_t::*;

// Provides an entry point that enforces application of the KVStoreTrait,
// which is how we ensure the implementation calling the API corresponds
// to the refinement proof that belongs with it.

verus!{
    pub fn entry<KVStore: KVStoreTrait>() {
        // This is the "real" clean main loop
//         let mut kvstore = KVStore::new();
//         let api = ClientAPI::new(Ghost(kvstore.instance_id()), None);
//         kvstore.kvstore_main(api);

        // This is our debug driver that lets us see a whole cross-crash interaction
        // Ask impl to mkfs (no contract on this yet, though there should be
        let mut kvstore = KVStore::new();
        let api = ClientAPI::new(Ghost(kvstore.instance_id()), None);
        kvstore.kvstore_mkfs(api);

        // Let the impl run through a script of requests "Phase 0".
        let mut kvstore = KVStore::new();
        let api = ClientAPI::new(Ghost(kvstore.instance_id()), Some(0));
        kvstore.kvstore_main(api);

        // Let the impl run through a script of requests "Phase 1".
        let mut kvstore = KVStore::new();
        let api = ClientAPI::new(Ghost(kvstore.instance_id()), Some(1));
        kvstore.kvstore_main(api);
    }
}

