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

    let h5 = cache.get_ro(5);

    let h6 = cache.get_mut(6);
    assume( h6 is Some );
    let mut h6 = h6.unwrap();
    let mut rec6 = h6.take();
    print_rec(&rec6);
    marshall7u8(&mut rec6, 3);
    print_rec(&rec6);
    h6.replace(rec6);
    cache.release_mut(h6);

    let h6 = cache.get_mut(6);
    assume( h6 is Some );
    let mut h6 = h6.unwrap();
    let rec6 = h6.take();
    print_rec(&rec6);

    print_rec(&h5.borrow());
}

} // verus!
