use vstd::prelude::*;
use vstd::cell::*;

mod crummy_cache;
use crummy_cache::*;

verus! {

spec fn parse(rec: ARec) -> u8
recommends
    rec.len() == REC_SIZE_BYTES,
{
    rec[0]
}

fn exec_parse(rec: &Rec) -> (out: u8)
requires
    rec.len() == REC_SIZE_BYTES,
ensures
    out == parse(rec@),
{
    rec[0]
}

fn exec_marshall(rec: &mut Rec, v: u8)
requires
    old(rec).len() == REC_SIZE_BYTES,
ensures
    rec.len() == REC_SIZE_BYTES,
    parse(rec@) == v,
{
    rec[0] = v
}

fn marshall7u8(rec: &mut Rec, start: usize) -> (end: usize)
    requires start + 1 < old(rec).len()
    ensures rec.len() == old(rec).len()
{
    rec[start] = 7;
    start + 1
}

fn transition(cache: &mut Cache)
requires
    old(cache).inv(),
    old(cache).outstanding_handles().is_empty(),
    parse(old(cache).value_at(2)) + parse(old(cache).value_at(3)) <= u8::MAX,
ensures
    cache.inv(),
    cache.outstanding_handles().is_empty(),
    forall |i| 0<=i<CACHE_SIZE_RECS && i!=4
        ==> cache.value_at(i) == old(cache).value_at(i),
    parse(cache.value_at(4)) == parse(old(cache).value_at(2)) + parse(old(cache).value_at(3)),
{
    let h2 = cache.get(2);
    let v2 = exec_parse(h2.borrow());

    let h3 = cache.get(3);
    let v3 = exec_parse(h3.borrow());

    let mut h4 = cache.get(4);
    let mut r4 = h4.take();
    exec_marshall(&mut r4, v2 + v3);

    h4.replace(r4);
    cache.release(h4);
    cache.release(h3);
    cache.release(h2);
}

fn main() {
    let mut cache = Cache::new();
    let ghost empty_cache = cache;

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
    h6.replace(rec6);

    print_rec(&h5.borrow());

    // clean up!
    cache.release(h5);
    cache.release(h6);

    // Put some interesting numbers into the operand slots for transition
    let mut h2 = cache.get(2);
    let mut r = h2.take();
    exec_marshall(&mut r, 27);
    h2.replace(r);
    cache.release(h2);

    let mut h3 = cache.get(3);
    let mut r = h3.take();
    exec_marshall(&mut r, 13);
    h3.replace(r);
    cache.release(h3);

//     assert( cache.value_at(2) == empty_cache.value_at(2) );
//     assert( cache.value_at(2) == Cache::empty_rec() );
//     assert( parse(cache.value_at(2)) == 0 );
    transition(&mut cache);

    let h2 = cache.get(2);
    print_rec(&h2.borrow());
    let h3 = cache.get(3);
    print_rec(&h3.borrow());
    let h4 = cache.get(4);
    print_rec(&h4.borrow());
}

} // verus!
