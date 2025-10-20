use vstd::prelude::*;

verus! {

pub const REC_SIZE_BYTES: usize = 10;
pub const CACHE_SIZE_RECS: usize = 1000;

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
    pub closed spec fn inv(self) -> bool {
        &&& self.idx < CACHE_SIZE_RECS
        &&& self.rec.len() == REC_SIZE_BYTES
    }

    pub fn borrow(&self) -> &Rec
    {
        &self.rec
    }
}

pub struct MutHandle {
    idx: usize,
    rec: Rec,
    _releasable: Ghost<bool>,
}

impl MutHandle {
    pub closed spec fn releasable(self) -> bool {
        self._releasable@
    }

    pub closed spec fn inv(self) -> bool {
        &&& self.idx < CACHE_SIZE_RECS
        &&& self._releasable@ ==> self.rec.len() == REC_SIZE_BYTES
    }

    pub fn take(&mut self) -> (rec: Rec)
        requires
            old(self).inv(),
            old(self).releasable(),
        ensures rec.len() == REC_SIZE_BYTES,
            self.inv(),
            !self.releasable(),
    {
        let mut dummy = vec![];
        std::mem::swap(&mut dummy, &mut self.rec);
        self._releasable = Ghost(false);
        assert( dummy.len() == old(self).rec.len() );
        dummy
    }

    pub fn replace(&mut self, rec: Rec)
    requires
        rec.len() == REC_SIZE_BYTES,
        old(self).inv(),
        !old(self).releasable(),
    ensures
        self.inv(),
        self.releasable(),
    {
        self.rec = rec;
        self._releasable = Ghost(true);
    }
}

#[derive(Debug)]
pub struct Cache {
    ary: Vec<Option<Rec>>,
}

impl Cache {
    #[verifier::external_body]
    pub fn new() -> (out: Self)
    ensures
        out.inv(),
        out.outstanding_handles().is_empty()
    {
        let ary: [Option<Rec>; CACHE_SIZE_RECS] = std::array::from_fn(|_| Some(vec![0; REC_SIZE_BYTES]));
        Self{
            ary: ary.to_vec()
        }
    }

    pub closed spec fn inv(self) -> bool
    {
        &&& self.ary.len() == CACHE_SIZE_RECS
        &&& forall |i| #![auto] 0<=i<CACHE_SIZE_RECS && self.ary[i] is Some
            ==> self.ary[i].unwrap().len() == REC_SIZE_BYTES
    }

    pub closed spec fn outstanding_handles(self) -> Set<int>
    {
        Set::new(|i| 0<=i<CACHE_SIZE_RECS && self.ary[i] is None)
    }

    pub fn get_ro(&mut self, idx: usize) -> (hdl: ImmHandle)
    requires
        old(self).inv(),
        0 <= idx < CACHE_SIZE_RECS,
        !old(self).outstanding_handles().contains(idx as int),
    ensures
        self.inv(),
        self.outstanding_handles() == old(self).outstanding_handles().insert(idx as int)
    {
        self.ary.push(None);
        let mut taken = self.ary.swap_remove(idx);
        assert( taken is Some );
        ImmHandle{ idx, rec: taken.unwrap() }
    }


    pub fn maybe_get_ro(&mut self, idx: usize) -> (hdl: Option<ImmHandle>)
    requires
        old(self).inv(),
        0 <= idx < CACHE_SIZE_RECS,
    ensures
        self.inv(),
        match hdl {
            None => {
                &&& old(self).outstanding_handles().contains(idx as int)
                &&& self.outstanding_handles() == old(self).outstanding_handles()
            },
            Some(hdl) => {
                &&& self.outstanding_handles() == old(self).outstanding_handles().insert(idx as int)
            },
        },
    {
        self.ary.push(None);
        let mut taken = self.ary.swap_remove(idx);
        match taken {
            None => None,   // Somebody beat you to it
            Some(rec) => Some(ImmHandle{ idx, rec }),
        }
    }

    pub fn get_mut(&mut self, idx: usize) -> (out: Option<MutHandle>)
    requires
        old(self).inv(),
        0 <= idx < CACHE_SIZE_RECS,
    ensures
        self.inv(),
        match out { Some(hdl) => hdl.inv() && hdl.releasable(), _ => true },
    {
        self.ary.push(None);
        let mut taken = self.ary.swap_remove(idx);
        match taken {
            None => None,   // Somebody beat you to it
            Some(rec) => Some(MutHandle{ idx, rec, _releasable: Ghost(true) }),
        }
    }

    pub fn release_imm(&mut self, hdl: ImmHandle)
    requires
        old(self).inv(),
        hdl.inv(),
    ensures
        self.inv(),
    {
        self.ary[hdl.idx] = Some(hdl.rec)
    }

    pub fn release_mut(&mut self, hdl: MutHandle)
    requires
        old(self).inv(),
        hdl.inv(),
        hdl.releasable(),
    ensures
        self.inv(),
    {
        // we'd like to assert that self.ary[hdl.idx] is None right now; an invariant
        // about outstanding Handles
        self.ary[hdl.idx] = Some(hdl.rec)
    }
}

}
