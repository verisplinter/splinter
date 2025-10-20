use vstd::prelude::*;
use vstd::cell::*;

verus! {

// I tried making a RefCell that did runtime counting, but there's
// no borrow_mut in vstd/cell.rs, and that's a bit of a showstopper.
// I think we're gonna just have to go to unverified? 😬
//
// struct RefCell<T> {
//     cell: PCell<T>,
//     perm: Option<Tracked<PointsTo<T>>>,
// }
// 
// struct RefCellHandle<T>(Tracked<PointsTo<T>>);
// 
// impl<T> RefCellHandle<T>{
//     fn borrow(&
// }
// 
// impl<T> RefCell<T> {
//     fn new(t: T) -> Self
//     {
//         let (cell, perm) = PCell::new(t);
//         Self{ cell, perm: Some(perm) }
//     }
// 
//     fn borrow_mut(&mut self) -> Option<RefCellHandle<T>>
//     {
//         let perm = self.perm.take();
//         match perm {
//             None => None,
//             Some(perm) => {
//                 Some(RefCellHandle(perm))
//             }
//         }
//     }
// }

type Page = [u8; 1000];

struct Rec {
    page: Page,
}

impl Rec {
    fn new() -> Self
    {
        Self{ page: [0; 1000] }
    }
}

// struct RecHandle<'a> {
//     cell: &'a RefCell<Rec>,
// }

pub const CACHE_COUNT: usize = 1000;

struct CacheHandle {
    page: PCell<Rec>,
    perm: Tracked<PointsTo<Rec>>,
}

#[verifier::external_body]
struct Cache {
    pages: [PCell<Rec>; CACHE_COUNT],
    perms: [Option<Tracked<PointsTo<Rec>>>; CACHE_COUNT],
}

impl Cache {
    #[verifier::external_body]
    fn new() -> Self
    {
        let mut pages = vec![];
        let mut perms_vec = vec![];
        let mut i = 0usize;
        while i < CACHE_COUNT {
            let (page, perm) = PCell::empty();
            pages.push(page);
            perms_vec.push(Some(perm));
            i += 1;
        }

        let pages: [PCell<Rec>; CACHE_COUNT] = pages.try_into().ok().expect("pages should have CACHE_COUNT elements");
        let perms: [Option<Tracked<PointsTo<Rec>>>; CACHE_COUNT] = perms_vec.try_into().ok().expect("perms should have CACHE_COUNT elements");

        Self{ pages, perms }
    }

    // This is a single-threaded cache, I guess; we'll modify the cache
    // to mark the slot taken. we're doing the runtime implementation
    // of a std::cell::RefCell by using the exec Option field as the
    // mutably-borrowe counter.
    // well, no, self can't be &mut, because we want to give back a handle
    // whose lifetime is dominated by &mut self, so we wouldn't be able
    // to get twice.
    // Argh. WTF. I should just use the contiguous cache and mark it trusted.
    // There's simply not enough machinery yet to do this right.
    fn get_mut(&mut self, slot: usize) -> (out: Option<CacheHandle>) {
        let perm = self.perms[slot].take();
        match perm {
            None => None,
            Some(perm) => {
                Some(CacheHandle{
                    page: imple.pages[slot].clone(),
                    perm
                })
            }
        }
    }

//     fn get<'a>(&'a self, idx: usize) -> RecHandle<'a>
//     {
//         RecHandle{ cell: &self.ary[idx] }
//     }
}


fn main() {
    assert(1 == 0 + 1);
}

} // verus!
