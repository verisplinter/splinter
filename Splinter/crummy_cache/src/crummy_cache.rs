use vstd::prelude::*;

verus! {

pub const REC_SIZE_BYTES: usize = 10;
pub const CACHE_SIZE_RECS: usize = 1000;

pub type ARec = Seq<u8>;
pub type Rec = Vec<u8>;

#[verifier::external_body]
pub fn print_rec(rec: &Rec) {
    println!("rec value {:?}", rec);
}

pub struct Handle {
    idx: usize,
    rec: Rec,
    _releasable: Ghost<bool>,
}

impl Handle {
    pub closed spec fn releasable(self) -> bool {
        self._releasable@
    }

    pub closed spec fn value(self) -> ARec
    recommends 
        self.inv(),
        self.releasable(),
    {
        self.rec@
    }

    pub closed spec fn index(self) -> int
    {
        self.idx as int
    }

    pub fn borrow(&self) -> &Rec
    requires self.releasable(),
    {
        &self.rec
    }

    pub closed spec fn inv(self) -> bool {
        &&& self.idx < CACHE_SIZE_RECS
        &&& self._releasable@ ==> self.rec.len() == REC_SIZE_BYTES
    }

    // Mutable stuff

    pub fn take(&mut self) -> (rec: Rec)
        requires
            old(self).inv(),
            old(self).releasable(),
        ensures rec.len() == REC_SIZE_BYTES,
            self.inv(),
            !self.releasable(),
            rec@ == old(self).value(),
            self.index() == old(self).index(),
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
        self.value() == rec@,
        self.index() == old(self).index(),
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

    pub fn get(&mut self, idx: usize) -> (hdl: Handle)
    requires
        old(self).inv(),
        0 <= idx < CACHE_SIZE_RECS,
        !old(self).outstanding_handles().contains(idx as int),
    ensures
        self.inv(),
        hdl.inv(),
        hdl.releasable(),
        hdl.index() == idx as int,
        self.outstanding_handles() == old(self).outstanding_handles().insert(hdl.index()),
    {
        match self.maybe_get(idx) {
            None => { assert(false); unreached() }
            Some(hdl) => hdl,
        }
//         self.ary.push(None);
//         let mut taken = self.ary.swap_remove(idx);
//         assert( taken is Some );
//         Handle{ idx, rec: taken.unwrap(), _releasable: Ghost(true) }
    }


    // None means the index is already outstanding in another handle.
    // I don't think our actual code will need this path.
    pub fn maybe_get(&mut self, idx: usize) -> (res: Option<Handle>)
    requires
        old(self).inv(),
        0 <= idx < CACHE_SIZE_RECS,
    ensures
        self.inv(),
        match res {
            None => {
                &&& old(self).outstanding_handles().contains(idx as int)
                &&& self.outstanding_handles() == old(self).outstanding_handles()
            },
            Some(hdl) => {
                &&& hdl.index() == idx as int
                &&& hdl.inv()
                &&& hdl.releasable()
                &&& self.outstanding_handles() == old(self).outstanding_handles().insert(hdl.index())
            },
        },
    {
        self.ary.push(None);
        let mut taken = self.ary.swap_remove(idx);
        match taken {
            None => None,   // Somebody beat you to it
            Some(rec) => Some(Handle{ idx, rec, _releasable: Ghost(true) }),
        }
    }

    pub fn release(&mut self, hdl: Handle)
    requires
        old(self).inv(),
        hdl.inv(),
        hdl.releasable(),
    ensures
        self.inv(),
        self.outstanding_handles() == old(self).outstanding_handles().remove(hdl.index())
    {
        self.ary[hdl.idx] = Some(hdl.rec)
    }
}

}
