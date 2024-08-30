pub trait CmovAnd<T> {
    /// Moves `other` into `self` if `value & TEST == 0`.
    fn cmov_if_and_imm_zero<const TEST: u8>(&mut self, other: &Self, value_to_test: T);

    /// Moves `other` into `self` if `value & TEST != 0`.
    fn cmov_if_and_imm_nonzero<const TEST: u8>(&mut self, other: &Self, value_to_test: T);
}

#[cfg(not(miri))]
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
mod impls_x86 {
    use std::arch::asm;

    use super::CmovAnd;

    macro_rules! x86_impl {
        ($ty:ty) => {
            impl CmovAnd<u8> for $ty {
                fn cmov_if_and_imm_zero<const TEST: u8>(&mut self, other: &Self, value_to_test: u8) {
                    unsafe {
                        asm! {
                            "test {value}, {test}",
                            "cmovz {dest}, {src}",

                            value = in(reg_byte) value_to_test,
                            test = const TEST,
                            dest = inlateout(reg) *self,
                            src = in(reg) *other,
                            options(pure, nomem, nostack),
                        }
                    }
                }

                fn cmov_if_and_imm_nonzero<const TEST: u8>(&mut self, other: &Self, value_to_test: u8) {
                    unsafe {
                        asm! {
                            "test {value}, {test}",
                            "cmovnz {dest}, {src}",

                            value = in(reg_byte) value_to_test,
                            test = const TEST,
                            dest = inlateout(reg) *self,
                            src = in(reg) *other,
                            options(pure, nomem, nostack),
                        }
                    }
                }
            }
        };
    }

    x86_impl!(u64);
    x86_impl!(i64);
}

#[cfg(any(not(any(target_arch = "x86", target_arch = "x86_64")), miri))]
mod impls_generic {
    use super::CmovAnd;

    impl CmovAnd<u8> for u64 {
        fn cmov_if_and_imm_zero<const TEST: u8>(&mut self, other: &Self, value_to_test: u8) {
            if value_to_test & TEST == 0 {
                *self = *other;
            }
        }

        fn cmov_if_and_imm_nonzero<const TEST: u8>(&mut self, other: &Self, value_to_test: u8) {
            if value_to_test & TEST != 0 {
                *self = *other;
            }
        }
    }
}
