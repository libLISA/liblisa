use liblisa::semantics::default::Expr;
pub mod delta_vec;

pub const fn concat_exprs<'a, const A: usize, const B: usize>(a: [Expr<'a>; A], b: [Expr<'a>; B]) -> [Expr<'a>; A + B] {
    let mut whole: [Expr; A + B] = [Expr::const_default(); A + B];
    let mut whole_index = 0;
    let mut index = 0;
    while index < A {
        whole[whole_index] = a[index];
        index += 1;
        whole_index += 1;
    }

    let mut index = 0;
    while index < B {
        whole[whole_index] = b[index];
        index += 1;
        whole_index += 1;
    }

    whole
}
