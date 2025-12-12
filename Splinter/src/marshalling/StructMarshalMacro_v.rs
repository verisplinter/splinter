// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(macro_expanded_macro_exports_accessed_by_absolute_paths)]

//! Macro for generating struct marshallers
//!
//! This macro generates all the boilerplate for implementing Marshal and UniformSized
//! for a 2-field struct, given the formatters for each field.
//!
//! Key design principle: The formatter types must match the struct field types EXACTLY.
//! If you need type conversions (e.g., IntFormat<u64> for a Key field), create a wrapper
//! formatter (e.g., KeyFormat) that handles the conversion internally.
//!
//! Limitations:
//! - Only supports 2-field structs (can be extended to N fields)

use vstd::prelude::*;
use crate::marshalling::Marshalling_v::{Marshal, Parsedview};
use crate::marshalling::UniformSized_v::UniformSized;
use crate::marshalling::WF_v::WF;

verus! {

/// Identity conversion function (no-op)
/// This is now primarily for documentation - the macro doesn't use conversion functions anymore
pub open spec fn identity<T>(v: T) -> T {
    v
}

#[verifier::external_body]
pub fn identity_exec<T>(v: T) -> (result: T)
    ensures result == v
{
    v
}

} // verus!

// Macro for generating a two-field struct marshaller
#[macro_export]
macro_rules! struct_marshaller_2 {
    (
        format_name: $format_name:ident,
        impl_type: $impl_type:ty,
        spec_type: $spec_type:ty,
        wf_proof: $wf_proof:expr,
        postcondition_proof: $postcondition_proof:expr,
        field1: {
            impl_field: $impl_field1:ident,
            spec_field: $spec_field1:ident,
            formatter_type: $fmt_type1:ty,
            formatter_spec_new: $fmt_spec_new1:expr,
            formatter_new: $fmt_new1:expr,
        },
        field2: {
            impl_field: $impl_field2:ident,
            spec_field: $spec_field2:ident,
            formatter_type: $fmt_type2:ty,
            formatter_spec_new: $fmt_spec_new2:expr,
            formatter_new: $fmt_new2:expr,
        }
    ) => {
        verus! {

        pub struct $format_name {
            pub field1_fmt: $fmt_type1,
            pub field2_fmt: $fmt_type2,
        }

        impl $format_name {
            pub open spec fn spec_new() -> Self {
                $format_name {
                    field1_fmt: $fmt_spec_new1,
                    field2_fmt: $fmt_spec_new2,
                }
            }

            pub fn new() -> (out: Self)
                ensures
                    out == Self::spec_new(),
                    out.valid(),
            {
                $format_name {
                    field1_fmt: $fmt_new1,
                    field2_fmt: $fmt_new2,
                }
            }
        }

        impl UniformSized for $format_name {
            open spec fn us_valid(&self) -> bool {
                &&& self.field1_fmt.us_valid()
                &&& self.field2_fmt.us_valid()
                &&& self.field1_fmt.uniform_size() as int + self.field2_fmt.uniform_size() as int <= usize::MAX
            }

            open spec fn uniform_size(&self) -> usize {
                (self.field1_fmt.uniform_size() + self.field2_fmt.uniform_size()) as usize
            }

            proof fn uniform_size_ensures(&self)
                ensures 0 < self.uniform_size()
            {
                self.field1_fmt.uniform_size_ensures();
                self.field2_fmt.uniform_size_ensures();
            }

            exec fn exec_uniform_size(&self) -> (sz: usize)
                ensures sz == self.uniform_size()
            {
                self.field1_fmt.exec_uniform_size() + self.field2_fmt.exec_uniform_size()
            }
        }

        impl Marshal for $format_name {
            type DV = $spec_type;
            type U = $impl_type;

            open spec fn valid(&self) -> bool {
                &&& self.field1_fmt.valid()
                &&& self.field2_fmt.valid()
                &&& self.us_valid()
            }

            open spec fn parsable(&self, data: Seq<u8>) -> bool {
                let field1_end = self.field1_fmt.uniform_size() as int;
                let field2_end = field1_end + self.field2_fmt.uniform_size() as int;

                &&& field2_end <= data.len()
                &&& self.field1_fmt.parsable(data.subrange(0, field1_end))
                &&& self.field2_fmt.parsable(data.subrange(field1_end, field2_end))
            }

            open spec fn parse(&self, data: Seq<u8>) -> Self::DV {
                let field1_end = self.field1_fmt.uniform_size() as int;
                let field2_end = field1_end + self.field2_fmt.uniform_size() as int;

                $spec_type {
                    $spec_field1: self.field1_fmt.parse(data.subrange(0, field1_end)),
                    $spec_field2: self.field2_fmt.parse(data.subrange(field1_end, field2_end)),
                }
            }

            exec fn try_parse(&self, slice: &Slice, data: &Vec<u8>) -> (ov: Option<Self::U>)
            {
                let total_size = self.exec_uniform_size();

                if slice.len() < total_size {
                    assert( !self.parsable(slice@.i(data@)) );
                    return None;
                }
                if data.len() < slice.end {
                    assert( !self.parsable(slice@.i(data@)) );
                    return None;
                }

                let field1_size = self.field1_fmt.exec_uniform_size();
                let field1_slice = slice.subslice(0, field1_size);
                let field1_value = match self.field1_fmt.try_parse(&field1_slice, data) {
                    None => {
                        proof {
                            assert(!self.field1_fmt.parsable(field1_slice@.i(data@)));
                            assert(!self.parsable(slice@.i(data@)));
                        }
                        assert( !self.parsable(slice@.i(data@)) );
                        return None;
                    }
                    Some(v) => v,
                };

                let field2_start = field1_size;
                let field2_end = field1_size + self.field2_fmt.exec_uniform_size();
                let field2_slice = slice.subslice(field2_start, field2_end);
                let field2_value = match self.field2_fmt.try_parse(&field2_slice, data) {
                    None => {
                        proof {
                            let idata = slice@.i(data@);
                            let f1_size = self.field1_fmt.uniform_size() as int;
                            let f2_size = self.field2_fmt.uniform_size() as int;
                            assert(field2_slice@.i(data@) == idata.subrange(f1_size, f1_size + f2_size));
                            assert(!self.field2_fmt.parsable(idata.subrange(f1_size, f1_size + f2_size)));
                            assert(!self.parsable(idata));
                        }
                        return None;
                    }
                    Some(v) => v,
                };

                let result = $impl_type {
                    $impl_field1: field1_value,
                    $impl_field2: field2_value,
                };

                proof {
                    // Prove parsability from the fact that both fields parsed successfully
                    let idata = slice@.i(data@);
                    let f1_end = self.field1_fmt.uniform_size() as int;
                    let f2_end = f1_end + self.field2_fmt.uniform_size() as int;

                    // Show field slices are the right subranges
                    assert(field1_slice@.i(data@) == idata.subrange(0, f1_end));
                    assert(field2_slice@.i(data@) == idata.subrange(f1_end, f2_end));

                    // We successfully parsed both fields, so struct is parsable
                    assert(self.parsable(idata));

                    // Call user-provided postcondition proof to establish:
                    // - result.parsedv() == self.parse(slice@.i(data@))
                    // - result.wf()
                    $postcondition_proof(
                        self,
                        slice,
                        data,
                        &field1_slice,
                        field1_value,
                        &field2_slice,
                        field2_value,
                        result
                    );
                }

                Some(result)
            }

            open spec fn marshallable(&self, value: Self::DV) -> bool {
                &&& self.field1_fmt.marshallable(value.$spec_field1)
                &&& self.field2_fmt.marshallable(value.$spec_field2)
            }

            open spec fn impl_marshallable(&self, impl_value: Self::U) -> bool {
                &&& self.field1_fmt.impl_marshallable(impl_value.$impl_field1)
                &&& self.field2_fmt.impl_marshallable(impl_value.$impl_field2)
            }

            open spec fn spec_size(&self, v: Self::DV) -> usize {
                (self.field1_fmt.uniform_size() + self.field2_fmt.uniform_size()) as usize
            }

            exec fn exec_size(&self, val: &Self::U) -> (sz: usize) {
                let field1_size = self.field1_fmt.exec_size(&val.$impl_field1);
                let field2_size = self.field2_fmt.exec_size(&val.$impl_field2);
                field1_size + field2_size
            }

            exec fn exec_marshall(&self, value: &Self::U, data: &mut Vec<u8>, start: usize) -> (end: usize) {
                let field1_end = self.field1_fmt.exec_marshall(&value.$impl_field1, data, start);

                let ghost mid_data = data@;
                let field2_end = self.field2_fmt.exec_marshall(&value.$impl_field2, data, field1_end);

                proof {
                    let f1_size = self.field1_fmt.uniform_size() as int;
                    let f2_size = self.field2_fmt.uniform_size() as int;
                    let subr = data@.subrange(start as int, field2_end as int);

                    assert(mid_data.subrange(start as int, field1_end as int)
                           == data@.subrange(start as int, field1_end as int));

                    assert(subr.subrange(0, f1_size)
                           == data@.subrange(start as int, field1_end as int));
                    assert(subr.subrange(f1_size, f1_size + f2_size)
                           == data@.subrange(field1_end as int, field2_end as int));

                    assert(self.field1_fmt.parsable(subr.subrange(0, f1_size)));
                    assert(self.field2_fmt.parsable(subr.subrange(f1_size, f1_size + f2_size)));
                    assert(self.parsable(subr));

                    // Note: Can't use .parsedv() on fields directly due to potential ambiguity
                    // The extensionality assertions below are sufficient for verification
                    // Help extensionality for struct field matching
                    assert(self.parse(subr).$spec_field1 == value.parsedv().$spec_field1);
                    assert(self.parse(subr).$spec_field2 == value.parsedv().$spec_field2);

                    assert(field2_end == start + self.spec_size(value.parsedv()));
                }

                field2_end
            }
        }

        impl UniformSizedMarshal for $format_name {
            proof fn uniform_size_matches_spec_size(self: &Self) {
                assert forall |value: $spec_type| #[trigger] self.spec_size(value) == self.uniform_size() by { }
            }
        }

        } // verus!
    };
}
