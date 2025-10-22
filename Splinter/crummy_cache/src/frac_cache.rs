use vstd::prelude::*;
use vstd::pcm::Loc;
use vstd::tokens::frac::*;
use vstd::pervasive::unreached;

verus! {

pub const REC_SIZE_BYTES: usize = 10;
pub const CACHE_SIZE_RECS: usize = 1000;

pub type Rec = Vec<u8>;
pub type Slot = usize;
pub type Perm = Frac<Slot,2>;

pub struct MutHandle {
    pub token: Tracked<Perm>,
    pub idx: Slot,
    pub rec: Rec,
}

impl MutHandle {
    pub closed spec fn inv(&self) -> bool
    {
        &&& self.token@.resource() == self.idx
        &&& self.rec.len() == REC_SIZE_BYTES
    }
}

pub struct Cache {
    perms: Tracked<Seq<Perm>>,
    entries: Vec<Option<Rec>>,
}

impl View for Cache {
    type V = Seq<Seq<u8>>;

    closed spec fn view(&self) -> Self::V
    {
        Seq::new( self.entries.len() as nat, 
            |i: int| if self.entries[i] is None { arbitrary() } else { self.entries[i].unwrap()@ } )
    }
}

impl Cache {
    pub open spec fn count(self) -> usize
    {
        CACHE_SIZE_RECS
    }

    pub closed spec fn entry_present(self, idx: usize) -> bool
    {
        &&& idx < self.count()
        &&& self.entries[idx as int] is Some
    }

    pub closed spec(checked) fn entry_token_id(self, idx: usize) -> Loc
        recommends self.inv(), idx < self.count(),
    {
        self.perms@[idx as int].id()
    }

    // NOTE: we might need to include the entry token id doesn't change
    pub open spec(checked) fn entries_same_except(self, other: Self, idx: usize) -> bool
        recommends idx < self.count(), self.count() == other.count(),
    {
        forall |i| 0 <= i < self.count() && i != idx ==> 
            self.entry_present(i) == other.entry_present(i)
    }

    pub open spec(checked) fn valid_handle(self, handle: MutHandle) -> bool
        recommends self.inv()
    {
        &&& handle.inv()
        &&& handle.idx < self.count()
        &&& handle.token@.frac() == 1
        &&& handle.token@.id() == self.entry_token_id(handle.idx)
    }

    pub closed spec fn inv(&self) -> bool
    {
        &&& self.count() == self.entries.len()
        &&& self.entries.len() == self.perms@.len()
        &&& forall |i: int| 0 <= i < self.count()
        ==> {
            &&& (#[trigger] self.perms@[i]).resource() == i
            &&& (#[trigger] self.entries[i]) is Some ==> self.entries[i].unwrap().len() == REC_SIZE_BYTES
            &&& self.entries[i] is Some <==> self.perms@[i].frac() == 2
            &&& self.entries[i] is None <==> self.perms@[i].frac() == 1
        }
    }

    pub fn new() -> (out: Self)
        ensures 
            out.inv(),
            out@ == Seq::new(out.count() as nat, |i| seq![0u8; REC_SIZE_BYTES as nat]),
            forall |i| 0 <= i < out.count() ==> #[trigger] out.entry_present(i),
    {
        let mut i = 0;
        let mut entries = Vec::<Option<Rec>>::with_capacity(CACHE_SIZE_RECS);
        let tracked mut perms = Seq::<Perm>::tracked_empty();

        while i < CACHE_SIZE_RECS
        invariant 
            i <= CACHE_SIZE_RECS,
            entries.len() == i,
            perms.len() == entries.len(),
            forall |j: int| 0 <= j < i ==> #[trigger] entries[j] is Some && entries[j].unwrap()@ == seq![0u8; REC_SIZE_BYTES as nat],
            forall |j: int| 0 <= j < i ==> #[trigger] perms[j].resource() == j && perms[j].frac() == 2,
        decreases CACHE_SIZE_RECS - i,
        {
            entries.push(Some(vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]));
            proof {
                let tracked(perm) = Frac::new(i);
                perms.tracked_push(perm);
            }
            i = i + 1;
        }

        assert forall |j| 0 <= j < entries.len()
        implies #[trigger] perms[j].frac() == 2
        by {
            assert(perms[j].resource() == j) // trigger
        }

        Self{perms: Tracked(perms), entries}
    }

    pub fn get(&mut self, idx: usize) -> (out: MutHandle)
        requires 
            old(self).inv(),
            old(self).entry_present(idx),
        ensures 
            self.inv(),
            self.valid_handle(out),
            self.entries_same_except(*old(self), idx),
            old(self)@ == self@.update(idx as int, out.rec@),
    {
        assert(idx < self.entries.len());
        self.entries.push(None);
        let mut taken = self.entries.swap_remove(idx);

        match taken {
            None => { assert(false); unreached() },
            Some(rec) => {
                let tracked perm = self.perms.borrow_mut().tracked_remove(idx as int);
                let tracked handle_perm = perm.split(1);
                proof {
                    self.perms.borrow_mut().tracked_insert(idx as int, perm);
                }
                MutHandle{
                    token: Tracked(handle_perm),
                    idx,
                    rec,
                }
            }
        }
    }

    pub fn release(&mut self, handle: MutHandle)
        requires 
            old(self).inv(),
            old(self).valid_handle(handle)
        ensures 
            self.inv(),
            self.entry_present(handle.idx),
            self.entries_same_except(*old(self), handle.idx),
            self@ == old(self)@.update(handle.idx as int, handle.rec@),
    {
        let MutHandle{token, idx, rec} = handle;
        proof {
            let tracked(handle_perm) = token.get();
            let tracked mut perm = self.perms.borrow_mut().tracked_remove(idx as int);
            perm.agree(&handle_perm);
            perm.combine(handle_perm);
            perm.bounded();
            assert(self.entries[idx as int] is None);
            assert(perm.frac() == 2);
            self.perms.borrow_mut().tracked_insert(idx as int, perm);
        }
        self.entries[idx] = Some(rec);
    }
}
}
