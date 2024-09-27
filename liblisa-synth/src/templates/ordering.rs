use std::iter::repeat;

use liblisa::semantics::default::ops::Op;
use liblisa::semantics::default::Expr;
use liblisa::utils::bitmap::{Bitmap, BitmapSlice, FixedBitmapU64};

/// An ordering describes which holes in an Expr can be freely exchanged.
/// Consider an expression like `(A + B) - C`.
/// In this expression, A and B can be swapped without affecting the computation.
///
/// When doing enumerative synthesis, we want to try and pick one canonical form for an expression.
/// We can do this by imposing an ordering on holes that can be freely exchanged.
/// For example, for `(A + B) - C` we can require `A < B` to eliminate duplicate forms.
///
/// Note that A and B refer to holes in an Expr, not to concrete numbers.
/// So this ordering is also applied to terms, not numbers.
/// For `(A + B) - C` with ordering `A < B` we might accept `(arg(0) + arg(1)) - arg(2)`,
/// but not `(arg(1) + arg(0)) - arg(2)`, because we consider `arg(0) < arg(1)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ordering {
    groups: Vec<FixedBitmapU64<1>>,
}

#[derive(Clone, Debug, PartialEq)]
struct Path(Vec<(usize, Option<Op>)>);

struct PathScanner<'a>(&'a [(usize, Option<Op>)]);

impl<'a> PathScanner<'a> {
    fn next(&mut self) -> Option<&'a (usize, Option<Op>)> {
        self.0.first().map(|result| {
            self.0 = &self.0[1..];
            result
        })
    }

    fn skip_while(&mut self, pred: impl FnMut(&&(usize, Option<Op>)) -> bool) {
        let num_to_skip = self.0.iter().take_while(pred).count();
        self.0 = &self.0[num_to_skip..];
    }
}

impl Path {
    fn ops_match(lop: &Option<Op>, rop: &Option<Op>) -> bool {
        match (lop, rop) {
            (Some(Op::Hole(_)), Some(Op::Hole(_))) => true,
            (lop, rop) => lop == rop,
        }
    }

    fn matches(&self, other: &Path) -> bool {
        // We can accept different depths if the operations are in the same order.
        // For example: we can have [A, +, +, +] and [A, +] match, because both are commutative
        // There can be other operators as well: [A, +, (0, -), *, +, +, +] and [A, +, +, (0, -), *, +] also match.

        let mut lhs = PathScanner(&self.0);
        let mut rhs = PathScanner(&other.0);
        while let Some((lchoice, lop)) = lhs.next() {
            if let Some((rchoice, rop)) = rhs.next() {
                if !Self::ops_match(lop, rop) {
                    return false;
                }

                if let Some(lop) = lop {
                    if lop.is_associative() {
                        if lop.is_commutative() {
                            lhs.skip_while(|(_, next_op)| Self::ops_match(rop, next_op));
                            rhs.skip_while(|(_, next_op)| Self::ops_match(rop, next_op));
                        }
                    } else if lchoice != rchoice {
                        return false;
                    }
                }
            } else {
                return false;
            }
        }

        lhs.next().is_none() && rhs.next().is_none()
    }

    fn hole_index(&self) -> Option<usize> {
        if let Some((_, Some(Op::Hole(index)))) = self.0.first() {
            Some(*index as usize)
        } else {
            None
        }
    }
}

impl Ordering {
    fn compute_paths(ops: &[Op]) -> Vec<Path> {
        let mut paths_stack: Vec<Vec<Path>> = vec![vec![]];
        for &op in ops.iter() {
            if op.num_args() == 0 {
                paths_stack.push(vec![Path(vec![(0, Some(op))])]);
            } else {
                let new_paths = paths_stack
                    .drain(paths_stack.len() - op.num_args()..)
                    .enumerate()
                    .map(|(index, mut paths)| {
                        for path in paths.iter_mut() {
                            if !op.is_commutative() {
                                path.0.extend(repeat((0, None)).take(index));
                            }

                            path.0.push((index, Some(op)))
                        }

                        paths
                    })
                    .flat_map(|paths| paths.into_iter())
                    .collect::<Vec<_>>();
                paths_stack.push(new_paths);
            }
        }

        paths_stack.pop().unwrap()
    }

    fn ordering_from_groups(mut groups: Vec<FixedBitmapU64>) -> Ordering {
        loop {
            let mut modified = false;
            for index in (0..groups.len()).rev() {
                let group = groups[index].clone();
                if group.is_all_zeros() {
                    groups.remove(index);
                } else if let Some(other_group) = groups
                    .iter_mut()
                    .find(|other_group| **other_group != group && !other_group.anded_with(&group).is_all_zeros())
                {
                    let shared = {
                        let mut o = other_group.clone();
                        o.and_with(&group);
                        o
                    };

                    other_group.and_with(&shared.flipped());
                    groups[index].and_with(&shared.flipped());
                    groups.push(shared);
                    modified = true;
                    break;
                }
            }

            if !modified {
                break;
            }
        }
        groups.sort();
        groups.dedup();

        Ordering {
            groups,
        }
    }

    pub fn of(expr: &Expr<'_>) -> Ordering {
        let mut paths = Self::compute_paths(expr.ops());
        let mut groups = Vec::new();

        while let Some(path) = paths.pop() {
            let mut group = Vec::new();
            if path.hole_index().is_some() {
                paths.retain(|other| {
                    if path.matches(other) {
                        group.push(other.clone());
                        false
                    } else {
                        true
                    }
                });

                group.push(path);

                let hole_indices = group.iter().flat_map(|path| path.hole_index()).collect::<FixedBitmapU64<1>>();

                groups.push(hole_indices);
            }
        }

        Self::ordering_from_groups(groups)
    }

    pub fn iter(&self) -> impl Iterator<Item = FixedBitmapU64<1>> + '_ {
        self.groups.iter().cloned()
    }
}

#[cfg(test)]
mod tests {
    use liblisa::semantics::default::ops::Op;
    use liblisa::semantics::default::Expr;
    use liblisa::utils::bitmap::FixedBitmapU64;

    use super::Ordering;
    use crate::templates::ordering::Path;

    #[test]
    pub fn test_paths_match() {
        assert!(Path(vec![(0, Some(Op::Hole(0)))]).matches(&Path(vec![(0, Some(Op::Hole(0)))])));
        assert!(Path(vec![(0, Some(Op::Hole(0))), (0, Some(Op::Add))])
            .matches(&Path(vec![(0, Some(Op::Hole(1))), (1, Some(Op::Add))])));
    }

    #[test]
    pub fn test_compute_paths_commutative() {
        assert_eq!(
            Ordering::compute_paths(&[Op::Hole(0)]),
            vec![Path(vec![(0, Some(Op::Hole(0)))]),]
        );

        assert_eq!(
            Ordering::compute_paths(&[Op::Hole(0), Op::Hole(1), Op::Add]),
            vec![
                Path(vec![(0, Some(Op::Hole(0))), (0, Some(Op::Add))]),
                Path(vec![(0, Some(Op::Hole(1))), (1, Some(Op::Add))]),
            ]
        );
    }

    #[test]
    pub fn test_compute_paths_not_commutative() {
        assert_eq!(
            Ordering::compute_paths(&[Op::Hole(0), Op::Hole(1), Op::Sub]),
            vec![
                Path(vec![(0, Some(Op::Hole(0))), (0, Some(Op::Sub))]),
                Path(vec![(0, Some(Op::Hole(1))), (0, None), (1, Some(Op::Sub))]),
            ]
        );
    }

    #[test]
    pub fn compute_ordering() {
        assert_eq!(
            Ordering::of(&Expr::new(&[Op::Hole(0), Op::Hole(1), Op::Add])),
            Ordering {
                groups: vec![FixedBitmapU64::<1>::from([0, 1]),]
            }
        );

        assert_eq!(
            Ordering::of(&Expr::new(&[Op::Hole(0), Op::Hole(1), Op::Sub])),
            Ordering {
                groups: vec![FixedBitmapU64::<1>::from([0]), FixedBitmapU64::<1>::from([1]),]
            }
        );

        assert_eq!(
            Ordering::of(&Expr::new(&[
                Op::Hole(0),
                Op::Hole(1),
                Op::Add,
                Op::Hole(0),
                Op::Hole(1),
                Op::Sub,
                Op::Add
            ])),
            Ordering {
                groups: vec![FixedBitmapU64::<1>::from([0]), FixedBitmapU64::<1>::from([1]),]
            }
        );

        assert_eq!(
            Ordering::of(&Expr::new(&[
                Op::Hole(0),
                Op::Hole(1),
                Op::Add,
                Op::Hole(2),
                Op::Hole(1),
                Op::Hole(0),
                Op::Add,
                Op::Add,
                Op::Add
            ])),
            Ordering {
                groups: vec![FixedBitmapU64::<1>::from([0, 1, 2]),]
            }
        );

        assert_eq!(
            Ordering::of(&Expr::new(&[
                Op::Hole(0),
                Op::Hole(1),
                Op::Add,
                Op::Hole(0),
                Op::Hole(1),
                Op::Hole(2),
                Op::Add,
                Op::Add,
                Op::Add
            ])),
            Ordering {
                groups: vec![FixedBitmapU64::<1>::from([0, 1, 2]),]
            }
        );
    }

    #[test]
    pub fn compute_ordering_complex() {
        assert_eq!(
            Ordering::of(&Expr::new(&[Op::Hole(0), Op::Parity, Op::Hole(1), Op::Parity, Op::Add])),
            Ordering {
                groups: vec![FixedBitmapU64::<1>::from([0, 1]),]
            }
        );

        assert_eq!(
            Ordering::of(&Expr::new(&[
                Op::Hole(0),
                Op::Parity,
                Op::Hole(1),
                Op::Parity,
                Op::Add,
                Op::Hole(2),
                Op::Parity,
                Op::Add
            ])),
            Ordering {
                groups: vec![FixedBitmapU64::<1>::from([0, 1, 2]),]
            }
        );
    }

    #[test]
    pub fn compute_ordering_shld() {
        // (B << 20) | ((A << 20) >> 32)
        let ops = [
            Op::Hole(1),
            Op::Hole(2),
            Op::Shl,
            Op::Hole(0),
            Op::Hole(2),
            Op::Shl,
            Op::Hole(3),
            Op::Shr,
            Op::Or,
        ];

        assert_eq!(
            Ordering::of(&Expr::new(&ops)),
            Ordering {
                groups: vec![
                    FixedBitmapU64::<1>::from([0]),
                    FixedBitmapU64::<1>::from([1]),
                    FixedBitmapU64::<1>::from([2]),
                    FixedBitmapU64::<1>::from([3]),
                ]
            }
        );
    }
}
