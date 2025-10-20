use vstd::prelude::*;
use vstd::cell::*;

mod crummy_cache;
use crummy_cache::*;

verus! {

fn marshall7u8(rec: &mut Rec, start: usize) -> (end: usize)
    requires start + 1 < old(rec).len()
    ensures rec.len() == old(rec).len()
{
    rec[start] = 7;
    start + 1
}

fn main() {
    let mut cache = Cache::new();

    let h5 = cache.get(5);

    let mut h6 = cache.get(6);
    let mut rec6 = h6.take();
    print_rec(&rec6);
    marshall7u8(&mut rec6, 3);
    print_rec(&rec6);
    h6.replace(rec6);
    cache.release(h6);  // Now required to do next get

    let mut h6 = cache.get(6);
    let rec6 = h6.take();
    print_rec(&rec6);

    print_rec(&h5.borrow());

//     // try borrow then take: should fail
//     let mut h4 = cache.get(4);
//     let r = &h4.borrow();
//     let x = h4.take();
// //     print_rec(r);
}

} // verus!
