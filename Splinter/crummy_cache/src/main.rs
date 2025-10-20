use vstd::prelude::*;
use vstd::cell::*;

mod crummy_cache;
use crummy_cache::*;

verus! {

fn marshall7u8(rec: &mut Rec, start: usize) -> (end: usize)
    requires start + 1 < old(rec).len()
{
    rec[start] = 7;
    start + 1
}

fn main() {
    let mut cache = Cache::new();

    let h5 = cache.get_ro(5);

//     ih = cache.get_imm(5);
//     // cache borrow must outlive ih

    let h6 = cache.get_mut(6);
    assume( h6 is Some );
    let mut h6 = h6.unwrap();
    let mut rec6 = h6.take();
    assume( 3 + 1 < rec6.len() );
    print_rec(&rec6);
    marshall7u8(&mut rec6, 3);
    print_rec(&rec6);
//     h6.replace(rec6);   // how do we enforce this?
    cache.release_mut(h6);

    let h6 = cache.get_mut(6);
    assume( h6 is Some );
    let mut h6 = h6.unwrap();
    let rec6 = h6.take();
    assume( 3 + 1 < rec6.len() );
    print_rec(&rec6);

    assume( h5 is Some );
    print_rec(&h5.unwrap().borrow());
}

} // verus!
