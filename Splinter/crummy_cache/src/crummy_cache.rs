use vstd::prelude::*;

verus! {

const REC_SIZE_BYTES: usize = 10;
const CACHE_SIZE_RECS: usize = 1000;

pub type Rec = Vec<u8>;

#[verifier::external_body]
pub fn print_rec(rec: &Rec) {
    println!("rec value {:?}", rec);
}

pub struct ImmHandle {
    idx: usize,
    rec: Rec
}

impl ImmHandle {
    pub fn borrow(&self) -> &Rec
    {
        &self.rec
    }
}

pub struct NakedHandle {
    pub idx: usize,
    pub rec: Rec
}

pub struct MutHandle {
    idx: usize,
    rec: Rec
}

impl MutHandle {
    pub fn take(&mut self) -> (rec: Rec)
        ensures rec.len() == REC_SIZE_BYTES,
        !self.releasable(),
    {
        let mut dummy = vec![];
        std::mem::swap(&mut dummy, &mut self.rec);
        dummy
    }

    spec fn releasable(self) -> bool {
    }

    pub fn replace(&mut self, rec: Rec)
    requires
        rec.len() == REC_SIZE_BYTES,
        !self.releasable(),
    ensures
        self.releasable(),
    {
        self.rec = rec
    }
}

#[derive(Debug)]
pub struct Cache {
    ary: Vec<Option<Rec>>,
}

impl Cache {
    #[verifier::external_body]
    pub fn new() -> Self
    {
        let ary: [Option<Rec>; CACHE_SIZE_RECS] = std::array::from_fn(|_| Some(vec![0; REC_SIZE_BYTES]));
        Self{
            ary: ary.to_vec()
        }
    }

    pub fn get_ro(&mut self, idx: usize) -> Option<ImmHandle>
    {
        self.ary.push(None);
        assume( idx < self.ary.len() );
        let mut taken = self.ary.swap_remove(idx);
        match taken {
            None => None,   // Somebody beat you to it
            Some(rec) => Some(ImmHandle{ idx, rec }),
        }
    }

    pub fn get(&mut self, idx: usize) -> Option<MutHandle>
    {
        self.ary.push(None);
        assume( idx < self.ary.len() );
        let mut taken = self.ary.swap_remove(idx);
        match taken {
            None => None,   // Somebody beat you to it
            Some(rec) => Some(MutHandle{ idx, rec }),
        }
    }

    pub fn get_mut(&mut self, idx: usize) -> Option<MutHandle>
    {
        self.ary.push(None);
        assume( idx < self.ary.len() );
        let mut taken = self.ary.swap_remove(idx);
        match taken {
            None => None,   // Somebody beat you to it
            Some(rec) => Some(MutHandle{ idx, rec }),
        }
    }

    pub fn release_imm(&mut self, hdl: ImmHandle)
    {
        assume( hdl.idx < self.ary.len() );
        self.ary[hdl.idx] = Some(hdl.rec)
    }

    pub fn release_mut(&mut self, hdl: MutHandle)
        requires hdl.releasable()
    {
        // we'd like to assert that self.ary[hdl.idx] is None right now; an invariant
        // about outstanding Handles
        assume( hdl.idx < self.ary.len() );
        self.ary[hdl.idx] = Some(hdl.rec)
    }
}

}
