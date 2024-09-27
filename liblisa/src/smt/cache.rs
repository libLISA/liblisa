use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::marker::PhantomData;
use std::ops::{Add, BitAnd, BitOr, BitXor, Mul, Not, Sub};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use sha1::{Digest, Sha1};

use super::solver::SolverProvider;
use super::tree::{BinOp, ConstId, Tree, UnOp};
use crate::smt::{Dynamic, SatResult, SmtBV, SmtBool, SmtInt, SmtModel, SmtModelRef, SmtSolver};

/// A hash for a set of assertions executed on a solver.
/// Used as the key for the solver cache.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AssertionHash([u8; 20]);

impl AssertionHash {
    /// Creates an assertion hash from the provided bytes.
    pub fn from_bytes(data: [u8; 20]) -> Self {
        Self(data)
    }

    /// Returns a slice with the contents of the hash.
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

/// A cached SAT solver result
#[derive(Clone, Debug)]
pub enum CacheResult {
    /// The assertions were unsatisfiable.
    Unsat,

    /// A timeout occurred.
    Unknown,

    /// The assertions were satisfiable.
    Sat,
}

/// Methods that allow the type to be used as a cache for SMT solver assertions.
pub trait SolverCache {
    /// Reads an entry from the solver cache.
    fn get(&mut self, hash: &AssertionHash) -> Option<CacheResult>;

    /// Inserts a new entry into the solver cache.
    fn insert(&mut self, hash: AssertionHash, result: CacheResult);
}

/// A solver cache backed by a [`HashMap`].
#[derive(Default)]
pub struct MemoryCache {
    map: HashMap<AssertionHash, CacheResult>,
}

impl MemoryCache {
    /// Creates a new, empty, [`MemoryCache`].
    pub fn new() -> Self {
        Self::default()
    }
}

impl SolverCache for MemoryCache {
    fn get(&mut self, hash: &AssertionHash) -> Option<CacheResult> {
        self.map.get(hash).cloned()
    }

    fn insert(&mut self, hash: AssertionHash, result: CacheResult) {
        self.map.insert(hash, result);
    }
}

/// A solver cache wrapped in a [`Mutex`].
pub struct SharedCache<C> {
    inner: Mutex<C>,
}

impl<C> SharedCache<C> {
    /// Creates a new [`SharedCache`] that wraps `inner`.
    pub fn new(inner: C) -> Self {
        Self {
            inner: Mutex::new(inner),
        }
    }
}

impl<C: SolverCache> SolverCache for SharedCache<C> {
    fn get(&mut self, hash: &AssertionHash) -> Option<CacheResult> {
        <&Self as SolverCache>::get(&mut &*self, hash)
    }

    fn insert(&mut self, hash: AssertionHash, result: CacheResult) {
        <&Self as SolverCache>::insert(&mut &*self, hash, result)
    }
}

impl<'r, C: SolverCache> SolverCache for &'r SharedCache<C> {
    fn get(&mut self, hash: &AssertionHash) -> Option<CacheResult> {
        self.inner.lock().unwrap().get(hash)
    }

    fn insert(&mut self, hash: AssertionHash, result: CacheResult) {
        self.inner.lock().unwrap().insert(hash, result)
    }
}

/// A solver provider that returns [`CachedSolver`]s.
pub struct CachedSolverProvider<C: SolverCache, I: SolverProvider> {
    cache: C,
    inner: I,
}

impl<C: SolverCache, I: SolverProvider> CachedSolverProvider<C, I> {
    /// See [`CachedSolver`].
    pub fn new(cache: C, inner: I) -> Self {
        Self {
            cache,
            inner,
        }
    }
}

impl<C: SolverCache + Send + Sync + Copy, I: SolverProvider> SolverProvider for CachedSolverProvider<C, I>
where
    for<'a> I::Solver<'a>: 'a,
{
    type Solver<'a> = CachedSolver<'a, I::Solver<'a>, C>;

    fn with_solver<T>(&self, f: impl FnOnce(Self::Solver<'_>) -> T) -> T {
        self.inner.with_solver(|solver| {
            let cached_solver = CachedSolver::new(solver, self.cache);
            f(cached_solver)
        })
    }
}

/// A solver that uses caching.
pub struct CachedSolver<'ctx, S: SmtSolver<'ctx>, C: SolverCache> {
    inner: S,
    cache: C,
    const_id_counter: u64,
    _phantom: PhantomData<&'ctx ()>,
}

impl<'ctx, S: SmtSolver<'ctx>, C: SolverCache> CachedSolver<'ctx, S, C> {
    /// Creates a new [`CachedSolver`].
    ///
    /// The [`CachedSolver`] first checks `cache` if there is a cached assertion result.
    /// If there is not, it invokes `inner` to solve the assertions.
    pub fn new(inner: S, cache: C) -> Self {
        Self {
            inner,
            cache,
            const_id_counter: 0,
            _phantom: PhantomData,
        }
    }
}

impl<'ctx, S: SmtSolver<'ctx>, C: SolverCache> Debug for CachedSolver<'ctx, S, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CachedSolver").finish()
    }
}

/// Cacheable SMT BV type.
pub struct CacheBV<'ctx, S: SmtSolver<'ctx>> {
    inner: S::BV,
    tree: Tree,
}

/// Cacheable SMT Int type.
pub struct CacheInt<'ctx, S: SmtSolver<'ctx>> {
    inner: S::Int,
    tree: Tree,
}

/// Cacheable SMT Bool type.
pub struct CacheBool<'ctx, S: SmtSolver<'ctx>> {
    inner: S::Bool,
    tree: Tree,
}

/// Cacheable SMT model that is returned when the assertions are satisfiable.
pub struct CacheModel<'ctx, S: SmtSolver<'ctx>>(S::Model);

impl<'ctx, S: SmtSolver<'ctx> + 'ctx, C: SolverCache> SmtModel<'ctx, CachedSolver<'ctx, S, C>> for CacheModel<'ctx, S> {
    fn get_const_interp(&self, name: &CacheBV<'ctx, S>) -> Option<CacheBV<'ctx, S>> {
        self.0.get_const_interp(&name.inner).map(|inner| CacheBV {
            inner,
            tree: Tree::ConstInterp,
        })
    }
}

impl<'ctx, S: SmtSolver<'ctx>> Debug for CacheModel<'ctx, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("CacheModel").finish()
    }
}

/// A reference to a [`CacheModel`].
pub struct CacheModelRef<'r, 'ctx, S: SmtSolver<'ctx> + 'r>(Option<S::ModelRef<'r>>);

impl<'r, 'ctx, S: SmtSolver<'ctx>> Debug for CacheModelRef<'r, 'ctx, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(r) = self.0.as_ref() {
            Debug::fmt(r, f)
        } else {
            f.debug_tuple("CacheModelRef").finish()
        }
    }
}

impl<'r, 'ctx, S: SmtSolver<'ctx> + 'r + 'ctx, C: SolverCache> SmtModelRef<'ctx, CachedSolver<'ctx, S, C>>
    for CacheModelRef<'r, 'ctx, S>
{
    fn to_model(&self) -> Option<CacheModel<'ctx, S>> {
        self.0.as_ref().and_then(|m| m.to_model()).map(CacheModel)
    }
}

impl<'ctx, S: SmtSolver<'ctx> + 'ctx, C: SolverCache> CachedSolver<'ctx, S, C> {
    fn next_const_id(&mut self) -> ConstId {
        let result = ConstId::from(self.const_id_counter);
        self.const_id_counter += 1;
        result
    }
}

impl<'ctx, S: SmtSolver<'ctx> + 'ctx, C: SolverCache> SmtSolver<'ctx> for CachedSolver<'ctx, S, C> {
    type BV = CacheBV<'ctx, S>;
    type Int = CacheInt<'ctx, S>;
    type Bool = CacheBool<'ctx, S>;

    type ModelRef<'r>
        = CacheModelRef<'r, 'ctx, S>
    where
        Self: 'r,
        S: 'r;

    type Model = CacheModel<'ctx, S>;

    fn bv_from_i64(&mut self, val: i64, size: u32) -> Self::BV {
        CacheBV {
            inner: self.inner.bv_from_i64(val, size),
            tree: Tree::FixedBV {
                val: val as u64,
                size,
            },
        }
    }

    fn bv_from_u64(&mut self, val: u64, size: u32) -> Self::BV {
        CacheBV {
            inner: self.inner.bv_from_u64(val, size),
            tree: Tree::FixedBV {
                val,
                size,
            },
        }
    }

    fn bv_from_int(&mut self, int: Self::Int, size: u32) -> Self::BV {
        CacheBV {
            inner: self.inner.bv_from_int(int.inner, size),
            tree: Tree::UnOp {
                op: UnOp::BvFromInt,
                arg: Box::new(int.tree),
            },
        }
    }

    fn new_bv_const(&mut self, name: impl AsRef<str>, size: u32) -> Self::BV {
        CacheBV {
            inner: self.inner.new_bv_const(name, size),
            tree: Tree::BV {
                id: self.next_const_id(),
                size,
            },
        }
    }

    fn new_bool_const(&mut self, name: impl AsRef<str>) -> Self::Bool {
        CacheBool {
            inner: self.inner.new_bool_const(name),
            tree: Tree::Bool(self.next_const_id()),
        }
    }

    fn int_from_i64(&mut self, val: i64) -> Self::Int {
        CacheInt {
            inner: self.inner.int_from_i64(val),
            tree: Tree::FixedInt {
                val: val as u64,
            },
        }
    }

    fn int_from_u64(&mut self, val: u64) -> Self::Int {
        CacheInt {
            inner: self.inner.int_from_u64(val),
            tree: Tree::FixedInt {
                val,
            },
        }
    }

    fn int_from_bv(&mut self, bv: Self::BV, signed: bool) -> Self::Int {
        CacheInt {
            inner: self.inner.int_from_bv(bv.inner, signed),
            tree: Tree::UnOp {
                op: UnOp::IntFromBv,
                arg: Box::new(bv.tree),
            },
        }
    }

    fn bool_from_bool(&mut self, val: bool) -> Self::Bool {
        CacheBool {
            inner: self.inner.bool_from_bool(val),
            tree: Tree::FixedBool {
                val,
            },
        }
    }

    fn forall_const(&mut self, vals: &[Dynamic<'ctx, Self>], condition: Self::Bool) -> Self::Bool {
        let bounds = vals
            .iter()
            .map(|val| match val {
                Dynamic::BV(v) => v.inner.clone().into_dynamic(),
                Dynamic::Int(v) => v.inner.clone().into_dynamic(),
                Dynamic::Bool(v) => v.inner.clone().into_dynamic(),
            })
            .collect::<Vec<_>>();
        CacheBool {
            inner: self.inner.forall_const(&bounds, condition.inner),
            tree: Tree::ForAll {
                bounds: vals
                    .iter()
                    .map(|b| match b {
                        Dynamic::BV(v) => v.tree.clone(),
                        Dynamic::Int(v) => v.tree.clone(),
                        Dynamic::Bool(v) => v.tree.clone(),
                    })
                    .collect::<Vec<_>>(),
                condition: Box::new(condition.tree),
            },
        }
    }

    fn check_assertions<'me>(&'me mut self, assertions: &[Self::Bool]) -> SatResult<Self::ModelRef<'me>> {
        let mut map = HashMap::new();

        // Ensure the assertions are in a well-defined order
        let mut assertions = assertions.to_vec();
        assertions.sort_by(|a, b| a.tree.cmp(&b.tree));

        // Generate hashes for the assertions
        let mut bytes = assertions
            .iter()
            .map(|b| {
                let bytes = b.tree.to_bytes(&mut map);
                let mut hasher = Sha1::new();
                hasher.update(&bytes);
                let hash: [u8; 20] = hasher.finalize().as_slice().try_into().unwrap();
                hash
            })
            .collect::<Vec<_>>();

        // Ensure the hashes are in a well-defined order as well
        bytes.sort();

        // Hash the hashes
        let mut hasher = Sha1::new();
        for bytes in bytes.iter() {
            hasher.update(bytes);
        }
        let hash = AssertionHash::from_bytes(hasher.finalize().as_slice().try_into().unwrap());

        if let Some(entry) = self.cache.get(&hash) {
            match entry {
                CacheResult::Unsat => SatResult::Unsat,
                CacheResult::Sat => SatResult::Sat(CacheModelRef(None)),
                CacheResult::Unknown => SatResult::Unknown,
            }
        } else {
            let assertions = assertions.iter().map(|b| b.inner.clone()).collect::<Vec<_>>();

            match self.inner.check_assertions(&assertions) {
                SatResult::Unknown => {
                    self.cache.insert(hash, CacheResult::Unknown);
                    SatResult::Unknown
                },
                SatResult::Sat(m) => {
                    self.cache.insert(hash, CacheResult::Sat);
                    SatResult::Sat(CacheModelRef(Some(m)))
                },
                SatResult::Unsat => {
                    self.cache.insert(hash, CacheResult::Unsat);
                    SatResult::Unsat
                },
            }
        }
    }
}

impl<'ctx, S: SmtSolver<'ctx> + 'ctx, C: SolverCache> SmtBV<'ctx, CachedSolver<'ctx, S, C>> for CacheBV<'ctx, S> {
    fn is_identical(&self, other: &Self) -> bool {
        self.inner.is_identical(&other.inner)
    }

    fn concat(self, other: Self) -> Self {
        CacheBV {
            inner: self.inner.concat(other.inner),
            tree: Tree::BinOp {
                op: BinOp::Concat,
                args: Box::new([self.tree, other.tree]),
            },
        }
    }

    fn extract(self, hi: u32, lo: u32) -> Self {
        Self {
            inner: self.inner.extract(hi, lo),
            tree: Tree::UnOp {
                op: UnOp::Extract(hi, lo),
                arg: Box::new(self.tree),
            },
        }
    }

    fn zero_ext(self, num: u32) -> Self {
        Self {
            inner: self.inner.zero_ext(num),
            tree: Tree::UnOp {
                op: UnOp::ZeroExt(num),
                arg: Box::new(self.tree),
            },
        }
    }

    fn sign_ext(self, num: u32) -> Self {
        Self {
            inner: self.inner.sign_ext(num),
            tree: Tree::UnOp {
                op: UnOp::SignExt(num),
                arg: Box::new(self.tree),
            },
        }
    }

    fn bvshl(self, count: Self) -> Self {
        Self {
            inner: self.inner.bvshl(count.inner),
            tree: Tree::BinOp {
                op: BinOp::BvShl,
                args: Box::new([self.tree, count.tree]),
            },
        }
    }

    fn bvlshr(self, count: Self) -> Self {
        Self {
            inner: self.inner.bvlshr(count.inner),
            tree: Tree::BinOp {
                op: BinOp::BvLShr,
                args: Box::new([self.tree, count.tree]),
            },
        }
    }

    fn bvashr(self, count: Self) -> Self {
        Self {
            inner: self.inner.bvashr(count.inner),
            tree: Tree::BinOp {
                op: BinOp::BvAShr,
                args: Box::new([self.tree, count.tree]),
            },
        }
    }

    fn bvurem(self, n: Self) -> Self {
        Self {
            inner: self.inner.bvurem(n.inner),
            tree: Tree::BinOp {
                op: BinOp::BvURem,
                args: Box::new([self.tree, n.tree]),
            },
        }
    }

    fn bvsrem(self, n: Self) -> Self {
        Self {
            inner: self.inner.bvsrem(n.inner),
            tree: Tree::BinOp {
                op: BinOp::BvSRem,
                args: Box::new([self.tree, n.tree]),
            },
        }
    }

    fn bvudiv(self, n: Self) -> Self {
        Self {
            inner: self.inner.bvudiv(n.inner),
            tree: Tree::BinOp {
                op: BinOp::BvUDiv,
                args: Box::new([self.tree, n.tree]),
            },
        }
    }

    fn bvsdiv(self, n: Self) -> Self {
        Self {
            inner: self.inner.bvsdiv(n.inner),
            tree: Tree::BinOp {
                op: BinOp::BvSDiv,
                args: Box::new([self.tree, n.tree]),
            },
        }
    }

    fn bvrotl(self, count: Self) -> Self {
        Self {
            inner: self.inner.bvrotl(count.inner),
            tree: Tree::BinOp {
                op: BinOp::BvRotL,
                args: Box::new([self.tree, count.tree]),
            },
        }
    }

    fn bvrotr(self, count: Self) -> Self {
        Self {
            inner: self.inner.bvrotr(count.inner),
            tree: Tree::BinOp {
                op: BinOp::BvRotR,
                args: Box::new([self.tree, count.tree]),
            },
        }
    }

    fn bvslt(self, other: Self) -> CacheBool<'ctx, S> {
        CacheBool {
            inner: self.inner.bvslt(other.inner),
            tree: Tree::BinOp {
                op: BinOp::BvSlt,
                args: Box::new([self.tree, other.tree]),
            },
        }
    }

    fn bvsge(self, other: Self) -> CacheBool<'ctx, S> {
        CacheBool {
            inner: self.inner.bvsge(other.inner),
            tree: Tree::BinOp {
                op: BinOp::BvSge,
                args: Box::new([self.tree, other.tree]),
            },
        }
    }

    fn bvsgt(self, other: Self) -> CacheBool<'ctx, S> {
        CacheBool {
            inner: self.inner.bvsgt(other.inner),
            tree: Tree::BinOp {
                op: BinOp::BvSgt,
                args: Box::new([self.tree, other.tree]),
            },
        }
    }

    fn bvugt(self, other: Self) -> CacheBool<'ctx, S> {
        CacheBool {
            inner: self.inner.bvugt(other.inner),
            tree: Tree::BinOp {
                op: BinOp::BvUgt,
                args: Box::new([self.tree, other.tree]),
            },
        }
    }

    fn bvult(self, other: Self) -> CacheBool<'ctx, S> {
        CacheBool {
            inner: self.inner.bvult(other.inner),
            tree: Tree::BinOp {
                op: BinOp::BvUlt,
                args: Box::new([self.tree, other.tree]),
            },
        }
    }

    fn bvule(self, other: Self) -> CacheBool<'ctx, S> {
        CacheBool {
            inner: self.inner.bvule(other.inner),
            tree: Tree::BinOp {
                op: BinOp::BvUle,
                args: Box::new([self.tree, other.tree]),
            },
        }
    }

    fn bvuge(self, other: Self) -> CacheBool<'ctx, S> {
        CacheBool {
            inner: self.inner.bvuge(other.inner),
            tree: Tree::BinOp {
                op: BinOp::BvUge,
                args: Box::new([self.tree, other.tree]),
            },
        }
    }

    fn _eq(self, other: Self) -> CacheBool<'ctx, S> {
        CacheBool {
            inner: self.inner._eq(other.inner),
            tree: Tree::BinOp {
                op: BinOp::Eq,
                args: Box::new([self.tree, other.tree]),
            },
        }
    }

    fn simplify(self) -> Self {
        Self {
            inner: self.inner.simplify(),
            tree: self.tree,
        }
    }

    fn get_size(&self) -> u32 {
        self.inner.get_size()
    }

    fn as_u64(&self) -> Option<u64> {
        self.inner.as_u64()
    }
}

impl<'ctx, S: SmtSolver<'ctx>> Display for CacheBV<'ctx, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.inner, f)
    }
}

impl<'ctx, S: SmtSolver<'ctx>> Debug for CacheBV<'ctx, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.inner, f)
    }
}

impl<'ctx, S: SmtSolver<'ctx>> Clone for CacheBV<'ctx, S> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            tree: self.tree.clone(),
        }
    }
}

impl<'ctx, S: SmtSolver<'ctx>> Add for CacheBV<'ctx, S> {
    type Output = CacheBV<'ctx, S>;

    fn add(self, rhs: Self) -> Self::Output {
        CacheBV {
            inner: self.inner + rhs.inner,
            tree: Tree::BinOp {
                op: BinOp::Add,
                args: Box::new([self.tree, rhs.tree]),
            },
        }
    }
}

impl<'ctx, S: SmtSolver<'ctx>> Sub for CacheBV<'ctx, S> {
    type Output = CacheBV<'ctx, S>;

    fn sub(self, rhs: Self) -> Self::Output {
        CacheBV {
            inner: self.inner - rhs.inner,
            tree: Tree::BinOp {
                op: BinOp::Sub,
                args: Box::new([self.tree, rhs.tree]),
            },
        }
    }
}

impl<'ctx, S: SmtSolver<'ctx>> Mul for CacheBV<'ctx, S> {
    type Output = CacheBV<'ctx, S>;

    fn mul(self, rhs: Self) -> Self::Output {
        CacheBV {
            inner: self.inner * rhs.inner,
            tree: Tree::BinOp {
                op: BinOp::Mul,
                args: Box::new([self.tree, rhs.tree]),
            },
        }
    }
}

impl<'ctx, S: SmtSolver<'ctx>> BitOr for CacheBV<'ctx, S> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        CacheBV {
            inner: self.inner | rhs.inner,
            tree: Tree::BinOp {
                op: BinOp::Or,
                args: Box::new([self.tree, rhs.tree]),
            },
        }
    }
}

impl<'ctx, S: SmtSolver<'ctx>> BitAnd for CacheBV<'ctx, S> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        CacheBV {
            inner: self.inner & rhs.inner,
            tree: Tree::BinOp {
                op: BinOp::And,
                args: Box::new([self.tree, rhs.tree]),
            },
        }
    }
}

impl<'ctx, S: SmtSolver<'ctx>> BitXor for CacheBV<'ctx, S> {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        CacheBV {
            inner: self.inner ^ rhs.inner,
            tree: Tree::BinOp {
                op: BinOp::Xor,
                args: Box::new([self.tree, rhs.tree]),
            },
        }
    }
}

impl<'ctx, S: SmtSolver<'ctx>> Not for CacheBV<'ctx, S> {
    type Output = Self;

    fn not(self) -> Self::Output {
        CacheBV {
            inner: self.inner.not(),
            tree: Tree::UnOp {
                op: UnOp::Not,
                arg: Box::new(self.tree),
            },
        }
    }
}

impl<'ctx, S: SmtSolver<'ctx>> Display for CacheInt<'ctx, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.inner, f)
    }
}

impl<'ctx, S: SmtSolver<'ctx>> Debug for CacheInt<'ctx, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.inner, f)
    }
}

impl<'ctx, S: SmtSolver<'ctx> + 'ctx, C: SolverCache> SmtInt<'ctx, CachedSolver<'ctx, S, C>> for CacheInt<'ctx, S> {
    fn is_identical(&self, other: &Self) -> bool {
        self.inner.is_identical(&other.inner)
    }

    fn _eq(self, other: Self) -> CacheBool<'ctx, S> {
        CacheBool {
            inner: self.inner._eq(other.inner),
            tree: Tree::BinOp {
                op: BinOp::Eq,
                args: Box::new([self.tree, other.tree]),
            },
        }
    }

    fn simplify(self) -> Self {
        Self {
            inner: self.inner.simplify(),
            tree: self.tree,
        }
    }

    fn as_u64(&self) -> Option<u64> {
        self.inner.as_u64()
    }
}

impl<'ctx, S: SmtSolver<'ctx>> Clone for CacheInt<'ctx, S> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            tree: self.tree.clone(),
        }
    }
}

impl<'ctx, S: SmtSolver<'ctx>> Add for CacheInt<'ctx, S> {
    type Output = CacheInt<'ctx, S>;

    fn add(self, rhs: Self) -> Self::Output {
        CacheInt {
            inner: self.inner + rhs.inner,
            tree: Tree::BinOp {
                op: BinOp::Add,
                args: Box::new([self.tree, rhs.tree]),
            },
        }
    }
}

impl<'ctx, S: SmtSolver<'ctx>> Sub for CacheInt<'ctx, S> {
    type Output = CacheInt<'ctx, S>;

    fn sub(self, rhs: Self) -> Self::Output {
        CacheInt {
            inner: self.inner - rhs.inner,
            tree: Tree::BinOp {
                op: BinOp::Sub,
                args: Box::new([self.tree, rhs.tree]),
            },
        }
    }
}

impl<'ctx, S: SmtSolver<'ctx>> Mul for CacheInt<'ctx, S> {
    type Output = CacheInt<'ctx, S>;

    fn mul(self, rhs: Self) -> Self::Output {
        CacheInt {
            inner: self.inner * rhs.inner,
            tree: Tree::BinOp {
                op: BinOp::Mul,
                args: Box::new([self.tree, rhs.tree]),
            },
        }
    }
}

impl<'ctx, S: SmtSolver<'ctx> + 'ctx, C: SolverCache> SmtBool<'ctx, CachedSolver<'ctx, S, C>> for CacheBool<'ctx, S> {
    fn is_identical(&self, other: &Self) -> bool {
        self.inner.is_identical(&other.inner)
    }

    fn _eq(self, other: Self) -> CacheBool<'ctx, S> {
        CacheBool {
            inner: self.inner._eq(other.inner),
            tree: Tree::BinOp {
                op: BinOp::Eq,
                args: Box::new([self.tree, other.tree]),
            },
        }
    }

    fn simplify(self) -> Self {
        Self {
            inner: self.inner.simplify(),
            tree: self.tree,
        }
    }

    fn ite_bv(self, lhs: CacheBV<'ctx, S>, rhs: CacheBV<'ctx, S>) -> CacheBV<'ctx, S> {
        CacheBV {
            inner: self.inner.ite_bv(lhs.inner, rhs.inner),
            tree: Tree::Ite(Box::new([self.tree, lhs.tree, rhs.tree])),
        }
    }

    fn ite_int(self, lhs: CacheInt<'ctx, S>, rhs: CacheInt<'ctx, S>) -> CacheInt<'ctx, S> {
        CacheInt {
            inner: self.inner.ite_int(lhs.inner, rhs.inner),
            tree: Tree::Ite(Box::new([self.tree, lhs.tree, rhs.tree])),
        }
    }

    fn ite_bool(self, lhs: CacheBool<'ctx, S>, rhs: CacheBool<'ctx, S>) -> CacheBool<'ctx, S> {
        CacheBool {
            inner: self.inner.ite_bool(lhs.inner, rhs.inner),
            tree: Tree::Ite(Box::new([self.tree, lhs.tree, rhs.tree])),
        }
    }

    fn as_bool(&self) -> Option<bool> {
        self.inner.as_bool()
    }
}

impl<'ctx, S: SmtSolver<'ctx>> Clone for CacheBool<'ctx, S> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            tree: self.tree.clone(),
        }
    }
}

impl<'ctx, S: SmtSolver<'ctx>> Display for CacheBool<'ctx, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.inner, f)
    }
}

impl<'ctx, S: SmtSolver<'ctx>> Debug for CacheBool<'ctx, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.inner, f)
    }
}

impl<'ctx, S: SmtSolver<'ctx>> BitOr for CacheBool<'ctx, S> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        CacheBool {
            inner: self.inner | rhs.inner,
            tree: Tree::BinOp {
                op: BinOp::Or,
                args: Box::new([self.tree, rhs.tree]),
            },
        }
    }
}

impl<'ctx, S: SmtSolver<'ctx>> BitAnd for CacheBool<'ctx, S> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        CacheBool {
            inner: self.inner & rhs.inner,
            tree: Tree::BinOp {
                op: BinOp::And,
                args: Box::new([self.tree, rhs.tree]),
            },
        }
    }
}

impl<'ctx, S: SmtSolver<'ctx>> BitXor for CacheBool<'ctx, S> {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        CacheBool {
            inner: self.inner ^ rhs.inner,
            tree: Tree::BinOp {
                op: BinOp::Xor,
                args: Box::new([self.tree, rhs.tree]),
            },
        }
    }
}

impl<'ctx, S: SmtSolver<'ctx>> Not for CacheBool<'ctx, S> {
    type Output = Self;

    fn not(self) -> Self::Output {
        CacheBool {
            inner: self.inner.not(),
            tree: Tree::UnOp {
                op: UnOp::Not,
                arg: Box::new(self.tree),
            },
        }
    }
}

/// A wrapper around a [`SolverCache`] that counts the number of cache hits and misses.
pub struct CacheHitCounter<C> {
    inner: C,
    num_hits: Arc<AtomicUsize>,
    num_misses: Arc<AtomicUsize>,
}

impl<C> CacheHitCounter<C> {
    /// Wraps `inner` in a cache hit counter.
    pub fn new(inner: C) -> Self {
        Self {
            inner,
            num_hits: Arc::new(AtomicUsize::new(0)),
            num_misses: Arc::new(AtomicUsize::new(0)),
        }
    }

    /// Returns a reference to the number of cache hits.
    /// The referenced `AtomicUsize` will update whenever a cache hit occurs.
    /// This function only needs to be called once to obtain the reference.
    pub fn num_hits(&self) -> Arc<AtomicUsize> {
        self.num_hits.clone()
    }

    /// Returns a reference to the number of cache misses.
    /// The referenced `AtomicUsize` will update whenever a cache miss occurs.
    /// This function only needs to be called once to obtain the reference.
    pub fn num_misses(&self) -> Arc<AtomicUsize> {
        self.num_misses.clone()
    }
}

impl<C: SolverCache> SolverCache for CacheHitCounter<C> {
    fn get(&mut self, hash: &AssertionHash) -> Option<CacheResult> {
        let result = self.inner.get(hash);
        match &result {
            Some(_) => self.num_hits.fetch_add(1, Ordering::Relaxed),
            None => self.num_misses.fetch_add(1, Ordering::Relaxed),
        };

        result
    }

    fn insert(&mut self, hash: AssertionHash, result: CacheResult) {
        self.inner.insert(hash, result)
    }
}
