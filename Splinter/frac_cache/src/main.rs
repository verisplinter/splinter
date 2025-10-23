use vstd::prelude::*;
use vstd::cell::*;

mod frac_cache;
use frac_cache::*;

verus! {

#[verifier::external_body]
pub fn print_rec(rec: &Rec) {
    println!("rec value {:?}", rec);
}

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

// fn transition(cache: &mut Cache, idx1: usize, idx2: usize, idx3: usize)
// requires
//     old(cache).inv(),
//     old(cache).entry_present(idx1),
//     old(cache).entry_present(idx2),
//     old(cache).entry_present(idx3),
//     idx1 != idx2,
//     idx2 != idx3,
//     idx3 != idx1,
// ensures
//     cache.inv(),
//     // cache@ == old(cache)@.update(idx3 as int, parse(old(cache)@[idx1 as int]) + parse(old(cache)@[idx2 as int])),
//     forall |i| true ==> old(cache).entry_present(i) == cache.entry_present(i),
// {
    // parse(cache.value_at(4)) == parse(old(cache).value_at(2)) + parse(old(cache).value_at(3)),

    // let h1 = cache.get(idx1);
    // let h2 = cache.get(idx2);

    // let v1 = exec_parse(&h1.rec);
    // let v2 = exec_parse(&h2.rec);

    // let mut h3 = cache.get(idx3);
    // assume(v1 + v2 <= u8::MAX);
    // exec_marshall(&mut h3.rec, v1 + v2);

    // let ghost tmp_cache = cache;

    // rec.len() == REC_SIZE_BYTES,
    // doesn't exec_marshall doesn't say anything about the value otherwise
    // parse(rec@) == v

    // one round of interp plus another
    // exec marshall just promises that the resulting update is x parse v


//     cache.release(h3);

//     assert(cache@ == tmp_cache@.update(idx3, v1+v2));

//     assume(false);

//     cache.release(h2);
//     cache.release(h1);
// }

fn main() {
    let mut cache = Cache::new();

    let h5 = cache.get(5);
    let mut h6 = cache.get(6);
    print_rec(&h6.rec);

    assert(cache.valid_handle(h5));

    marshall7u8(&mut h6.rec, 3);
    print_rec(&h6.rec);
    assert(cache.valid_handle(h5));

    assert(h6.idx == 6);
    cache.release(h6);  // Now required to do next get
    assert(cache.entry_present(6));
    assert(cache.valid_handle(h5));

    // how do we know that entry is present 
    let mut h6 = cache.get(6);
    print_rec(&h6.rec); 
    print_rec(&h5.rec);

    // clean up!
    cache.release(h5);
    cache.release(h6);

    // Put some interesting numbers into the operand slots for transition
    let mut h2 = cache.get(2);
    exec_marshall(&mut h2.rec, 27);
    cache.release(h2);

    let mut h3 = cache.get(3);
    exec_marshall(&mut h3.rec, 13);
    cache.release(h3);

    // transition(&mut cache, 2, 3, 4);

    let h2 = cache.get(2);
    print_rec(&h2.rec);
    let h3 = cache.get(3);
    print_rec(&h3.rec);
    let h4 = cache.get(4);
    print_rec(&h4.rec);
}

} // verus!
