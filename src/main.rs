use std::collections::{BTreeSet, BTreeMap};
use std::str::FromStr;
use std::num::NonZeroUsize;
use std::io::{self, BufRead, BufReader};
use std::fmt::{self, Write};
use std::cmp::Ordering;
use std::fs::File;
use std::iter;
use std::mem;
use std::thread;
use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicUsize, Ordering as MemOrder};

use itertools::Itertools;
use clap::Parser;

use z3::{Context, Solver, Optimize, SatResult, Model};
use z3::ast::{Bool, Real, Int, Ast};

use num_rational::Rational64;

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(grammar);

#[derive(Debug)]
enum BoolExpr {
    Constant { value: bool },

    Not { value: Box<BoolExpr> },

    Less { left: Box<NumericExpr>, right: Box<NumericExpr> },
    LessEq { left: Box<NumericExpr>, right: Box<NumericExpr> },
    Eq { left: Box<NumericExpr>, right: Box<NumericExpr> },
    Neq { left: Box<NumericExpr>, right: Box<NumericExpr> },

    And { left: Box<BoolExpr>, right: Box<BoolExpr> },
    Xor { left: Box<BoolExpr>, right: Box<BoolExpr> },
    Or { left: Box<BoolExpr>, right: Box<BoolExpr> },
}
#[derive(Debug)]
enum NumericExpr {
    Constant { value: Rational64 },

    DetectorValue { vertex: String },
    DetectorValueSum,

    DominationNumber { vertex: String },
    Share { vertex: String },

    Neg { value: Box<NumericExpr> },

    Mul { left: Box<NumericExpr>, right: Box<NumericExpr> },
    Div { left: Box<NumericExpr>, right: Box<NumericExpr> },

    Add { left: Box<NumericExpr>, right: Box<NumericExpr> },
    Sub { left: Box<NumericExpr>, right: Box<NumericExpr> },
}
#[derive(Debug)]
enum GraphExpr {
    Path { size: usize },
    Cycle { size: usize },
    File { path: String },
    CartesianProduct { left: Box<GraphExpr>, right: Box<GraphExpr> },
    KingCartesianProduct { left: Box<GraphExpr>, right: Box<GraphExpr> },
}

impl fmt::Display for BoolExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BoolExpr::Constant { value } => write!(f, "{value}"),

            BoolExpr::Not { value } => write!(f, "(not {value})"),

            BoolExpr::Less { left, right } => write!(f, "({left} < {right})"),
            BoolExpr::LessEq { left, right } => write!(f, "({left} <= {right})"),
            BoolExpr::Eq { left, right } => write!(f, "({left} == {right})"),
            BoolExpr::Neq { left, right } => write!(f, "({left} != {right})"),

            BoolExpr::And { left, right } => write!(f, "({left} and {right})"),
            BoolExpr::Xor { left, right } => write!(f, "({left} xor {right})"),
            BoolExpr::Or { left, right } => write!(f, "({left} or {right})"),
        }
    }
}
impl fmt::Display for NumericExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NumericExpr::Constant { value } => write!(f, "{value}"),

            NumericExpr::DetectorValueSum => write!(f, "sum(S)"),

            NumericExpr::DetectorValue { vertex } => write!(f, "S({vertex})"),
            NumericExpr::DominationNumber { vertex } => write!(f, "dom({vertex})"),
            NumericExpr::Share { vertex } => write!(f, "sh({vertex})"),

            NumericExpr::Neg { value } => write!(f, "-{value}"),

            NumericExpr::Mul { left, right } => write!(f, "({left} * {right})"),
            NumericExpr::Div { left, right } => write!(f, "({left} / {right})"),

            NumericExpr::Add { left, right } => write!(f, "({left} + {right})"),
            NumericExpr::Sub { left, right } => write!(f, "({left} - {right})"),
        }
    }
}

type Adj<'a, P> = dyn 'a + Sync + Fn(P) -> BTreeSet<P>;
type Counter<'ctx, P> = dyn 'ctx + Fn(&BTreeSet<P>) -> Real<'ctx>;

trait Point: Copy + Ord {}
impl Point for (i32, i32) {}
impl Point for usize {}

struct Verbose<'a>(&'a Rational64);
impl fmt::Display for Verbose<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (p, q) = (*self.0.numer(), *self.0.denom());
        write!(f, "{}/{} = {}", p, q, p as f64 / q as f64)
    }
}

fn adj_k(p: (i32, i32)) -> BTreeSet<(i32, i32)> {
    [
        (p.0 - 1, p.1 - 1), (p.0 - 1, p.1), (p.0 - 1, p.1 + 1),
        (p.0,     p.1 - 1),                 (p.0,     p.1 + 1),
        (p.0 + 1, p.1 - 1), (p.0 + 1, p.1), (p.0 + 1, p.1 + 1),
    ].into_iter().collect()
}
fn adj_sq(p: (i32, i32)) -> BTreeSet<(i32, i32)> {
    [(p.0 - 1, p.1), (p.0, p.1 - 1), (p.0, p.1 + 1), (p.0 + 1, p.1)].into_iter().collect()
}
fn adj_tri(p: (i32, i32)) -> BTreeSet<(i32, i32)> {
    [(p.0 - 1, p.1 - 1), (p.0 - 1, p.1), (p.0, p.1 - 1), (p.0, p.1 + 1), (p.0 + 1, p.1), (p.0 + 1, p.1 + 1)].into_iter().collect()
}
fn adj_hex(p: (i32, i32)) -> BTreeSet<(i32, i32)> {
    if (p.0 + p.1) % 2 == 0 {
        [(p.0 - 1, p.1), (p.0, p.1 - 1), (p.0, p.1 + 1)].into_iter().collect()
    } else {
        [(p.0 + 1, p.1), (p.0, p.1 - 1), (p.0, p.1 + 1)].into_iter().collect()
    }
}

fn rect(rows: usize, cols: usize) -> BTreeSet<(i32, i32)> {
    let mut res = BTreeSet::new();
    for r in 0..rows as i32 {
        for c in 0..cols as i32 {
            res.insert((r, c));
        }
    }
    res
}
fn get_size(shape: &BTreeSet<(i32, i32)>) -> (usize, usize) {
    if shape.is_empty() { return (0, 0); }

    let (mut min_r, mut max_r) = (i32::MAX, i32::MIN);
    let (mut min_c, mut max_c) = (i32::MAX, i32::MIN);
    for (r, c) in shape.iter().copied() {
        min_r = min_r.min(r);
        max_r = max_r.max(r);
        min_c = min_c.min(c);
        max_c = max_c.max(c);
    }
    ((max_r - min_r) as usize + 1, (max_c - min_c) as usize + 1)
}
#[test]
fn test_get_size() {
    for r in 0..16 {
        for c in 0..16 {
            assert_eq!(get_size(&rect(r, c)), if r == 0 || c == 0 { (0, 0) } else { (r, c) });
        }
    }
}
fn print_shape(shape: &BTreeSet<(i32, i32)>, detectors: &BTreeMap<(i32, i32), Rational64>) {
    let (rows, cols) = get_size(shape);
    let mut table = vec![vec![String::new(); cols]; rows];

    for (r, c) in shape.iter().copied() {
        table[r as usize][c as usize] = match detectors.get(&(r, c)).copied() {
            Some(v) => if *v.numer() == *v.denom() { '1'.into() } else if *v.numer() == 0 { '0'.into() } else { format!("({v})") },
            None => '.'.into(),
        };
    }

    let col_widths: Vec<_> = (0..cols).map(|c| table.iter().map(|row| row[c].len()).max().unwrap_or(0)).collect();

    for row in table.iter() {
        for (value, &width) in iter::zip(row, &col_widths) {
            debug_assert!(value.len() <= width);
            let h = (width - value.len()) / 2;
            for _ in 0..h { print!(" ") }
            print!("{value}");
            for _ in h..(width - value.len()) { print!(" ") }
        }
        println!();
    }
}

struct Shells<'a, 'b, P: Point> {
    expanded: BTreeSet<P>,
    frontier: BTreeSet<P>,
    adj: &'b Adj<'a, P>,
}
impl<'a, 'b, P: Point> Shells<'a, 'b, P> {
    fn new(shape: &BTreeSet<P>, adj: &'b Adj<'a, P>) -> Self {
        Self {
            expanded: shape.clone(),
            frontier: shape.clone(),
            adj,
        }
    }
}
impl<'a, 'b, 'c, P: Point> Iterator for Shells<'a, 'b, P> {
    type Item = BTreeSet<P>;
    fn next(&mut self) -> Option<Self::Item> {
        for p in mem::take(&mut self.frontier) {
            self.frontier.extend((self.adj)(p).into_iter().filter(|q| !self.expanded.contains(q)));
        }
        self.expanded.extend(self.frontier.iter().copied());
        Some(self.frontier.clone())
    }
}
#[test]
fn test_shells() {
    let mut shells = Shells::new(&[(0,0)].into_iter().collect(), &adj_k);
    assert_eq!(shells.next().unwrap().len(), 8);
    assert_eq!(shells.next().unwrap().len(), 16);
    assert_eq!(shells.next().unwrap().len(), 24);
    assert_eq!(shells.next().unwrap().len(), 32);
}

fn inflate<P: Point>(shape: &BTreeSet<P>, adj: &Adj<P>, radius: usize) -> BTreeSet<P> {
    let mut res = shape.clone();
    for mut shell in Shells::new(shape, adj).take(radius) {
        res.append(&mut shell);
    }
    res
}
fn get_interior<P: Point>(shape: &BTreeSet<P>, adj: &Adj<P>) -> BTreeSet<P> {
    shape.iter().copied().filter(|u| adj(*u).into_iter().all(|v| shape.contains(&v))).collect()
}

#[test]
fn test_inflate() {
    assert_eq!(inflate(&[(0, 0)].into_iter().collect(), &adj_k, 0).len(), 1);
    assert_eq!(inflate(&[(0, 0)].into_iter().collect(), &adj_k, 1).len(), 9);
    assert_eq!(inflate(&[(0, 0)].into_iter().collect(), &adj_k, 2).len(), 25);
    assert_eq!(inflate(&[(0, 0)].into_iter().collect(), &adj_k, 3).len(), 49);
    assert_eq!(inflate(&[(0, 0)].into_iter().collect(), &adj_k, 200).len(), 160801);

    assert_eq!(inflate(&(0..=35).map(|x| (x, 0)).collect(), &adj_k, 3).len(), 294);
    assert_eq!(inflate(&(0..=200).map(|x| (x, 0)).collect(), &adj_k, 3).len(), 1449);

    assert_eq!(inflate(&(0..=35).map(|x| (x, 0)).collect(), &adj_hex, 3).len(), 266);
    assert_eq!(inflate(&(0..=200).map(|x| (x, 0)).collect(), &adj_hex, 3).len(), 1419);
}

struct Distances<P: Point>(BTreeMap<(P, P), usize>);
impl<P: Point> Distances<P> {
    fn within_shape(shape: &BTreeSet<P>, adj: &Adj<P>) -> Self {
        let mut res = BTreeMap::default();
        for p in shape.iter().copied() {
            let mut targets: BTreeSet<_> = shape.range(p..).copied().skip(1).collect();
            let mut shells = Shells::new(&[p].into_iter().collect(), adj);
            let mut dist = 0;
            while !targets.is_empty() {
                dist += 1;
                for q in shells.next().unwrap() {
                    if targets.remove(&q) {
                        res.insert((p, q), dist);
                    }
                }
            }
        }
        Self(res)
    }
    fn get(&self, p: P, q: P) -> usize {
        match p.cmp(&q) {
            Ordering::Equal => 0,
            Ordering::Less => self.0[&(p, q)],
            Ordering::Greater => self.0[&(q, p)],
        }
    }
}
#[test]
fn test_distances() {
    assert_eq!(Distances::within_shape(&[(0,0)].into_iter().collect(), &adj_k).0, [].into_iter().collect());
    assert_eq!(Distances::within_shape(&[(0,0),(0,1)].into_iter().collect(), &adj_k).0, [(((0,0),(0,1)),1)].into_iter().collect());
    assert_eq!(Distances::within_shape(&[(0,0),(0,1),(0,2)].into_iter().collect(), &adj_k).0, [(((0,0),(0,1)),1), (((0,0),(0,2)),2), (((0,1),(0,2)),1)].into_iter().collect());

    assert_eq!(Distances::within_shape(&(0..100).map(|x| (x, 0)).collect(), &adj_k).0.len(), (100 * 100 - 100) / 2);
    assert_eq!(Distances::within_shape(&(0..200).map(|x| (x, 0)).collect(), &adj_k).0.len(), (200 * 200 - 200) / 2);

    let shape = (-20..=20).cartesian_product(-20..=20).into_iter().collect();
    let d = Distances::within_shape(&shape, &adj_sq);
    for p in shape.iter().copied() {
        for q in shape.iter().copied() {
            assert_eq!(d.get(p, q), (p.0 - q.0).abs() as usize + (p.1 - q.1).abs() as usize);
        }
    }
}

fn get_tilings_baseline_impl(shape: &BTreeSet<(i32, i32)>, search_size_mults: (u32, u32), tile_radius: i32) -> Vec<(BTreeMap<(i32, i32), (i32, i32)>, (i32, i32), (i32, i32))> {
    let inflated = inflate(shape, &adj_k, 3);
    let size = get_size(shape);

    let dr_range = -(search_size_mults.0 as i32) * size.0 as i32 ..= search_size_mults.1 as i32 * size.0 as i32;
    let dc_range = -(search_size_mults.0 as i32) * size.1 as i32 ..= search_size_mults.1 as i32 * size.1 as i32;

    let mut tilings: BTreeMap<BTreeMap<(i32, i32), (i32, i32)>, ((i32, i32), (i32, i32))> = Default::default();
    for dr1 in dr_range.clone() {
        for dc1 in dc_range.clone() {
            for dr2 in dr_range.clone() {
                'skip: for dc2 in dc_range.clone() {
                    let (b1, b2) = ((dr1, dc1), (dr2, dc2));
                    let mut res: BTreeMap<(i32, i32), (i32, i32)> = Default::default();
                    for m1 in -tile_radius..=tile_radius {
                        for m2 in -tile_radius..=tile_radius {
                            for (r, c) in shape.iter().copied() {
                                let p = (r + m1 * b1.0 + m2 * b2.0, c + m1 * b1.1 + m2 * b2.1);
                                if res.insert(p, (r, c)).is_some() { continue 'skip; }
                            }
                        }
                    }
                    for p in inflated.iter() {
                        if !res.contains_key(p) { continue 'skip; }
                    }
                    res.retain(|p, _| inflated.contains(p));
                    tilings.entry(res).or_insert((b1, b2));
                }
            }
        }
    }
    tilings.into_iter().map(|(tiling, (b1, b2))| (tiling, b1, b2)).collect()
}
fn get_tilings_fast_impl(shape: &BTreeSet<(i32, i32)>, search_size_mults: (u32, u32), tile_radius: i32) -> Vec<(BTreeMap<(i32, i32), (i32, i32)>, (i32, i32), (i32, i32))> {
    let inflated = inflate(shape, &adj_k, 3);
    let size = get_size(shape);

    let dr_range = -(search_size_mults.0 as i32) * size.0 as i32 ..= search_size_mults.1 as i32 * size.0 as i32;
    let dc_range = -(search_size_mults.0 as i32) * size.1 as i32 ..= search_size_mults.1 as i32 * size.1 as i32;
    let mut m_range = (-tile_radius..=tile_radius).collect::<Vec<_>>();
    m_range.sort_by_key(|x| x.abs());

    let mut basis_candidates = vec![];
    for dr in dr_range {
        'skip: for dc in dc_range.clone() {
            let mut res: BTreeMap<(i32, i32), (i32, i32)> = Default::default();
            for (r, c) in shape.iter().copied() {
                for m in m_range.iter().copied() {
                    let p = (r + m * dr, c + m * dc);
                    if res.insert(p, (r, c)).is_some() { continue 'skip; }
                }
            }
            basis_candidates.push((dr, dc));
        }
    }

    let mut tilings: BTreeMap<BTreeMap<(i32, i32), (i32, i32)>, ((i32, i32), (i32, i32))> = Default::default();
    for b1 in basis_candidates.iter().copied() {
        'skip: for b2 in basis_candidates.iter().copied() {
            let mut res: BTreeMap<(i32, i32), (i32, i32)> = BTreeMap::new();
            for (r, c) in shape.iter().copied() {
                for m1 in m_range.iter().copied() {
                    for m2 in m_range.iter().copied() {
                        let p = (r + m1 * b1.0 + m2 * b2.0, c + m1 * b1.1 + m2 * b2.1);
                        if res.insert(p, (r, c)).is_some() { continue 'skip; }
                    }
                }
            }
            for p in inflated.iter() {
                if !res.contains_key(p) { continue 'skip; }
            }
            res.retain(|p, _| inflated.contains(p));
            tilings.entry(res).or_insert((b1, b2));
        }
    }
    tilings.into_iter().map(|(tiling, (b1, b2))| (tiling, b1, b2)).collect()
}
fn get_tilings(shape: &BTreeSet<(i32, i32)>) -> Vec<(BTreeMap<(i32, i32), (i32, i32)>, (i32, i32), (i32, i32))> {
    get_tilings_fast_impl(shape, (1, 1), 5)
}

#[test]
fn test_get_tilings() {
    macro_rules! check {
        ($shape:expr => $search_size_mult:expr, $tile_radius:expr) => {{
            let shape = $shape;
            let a = get_tilings_baseline_impl(&shape, $search_size_mult, $tile_radius).into_iter().map(|x| x.0).collect::<BTreeSet<_>>();
            let b = get_tilings(&shape).into_iter().map(|x| x.0).collect::<BTreeSet<_>>();
            if a != b {
                panic!("{} vs {}\n{shape:?}", a.len(), b.len());
            }
        }};
    }

    const N: (usize, usize) = (3, 3);
    for size in 1..=N.0 * N.1 {
        for shape in (0..N.0 as i32).cartesian_product(0..N.1 as i32).combinations(size).map(|x| x.into_iter().collect()) {
            check!(shape => (2, 2), 6);
        }
    }
}

enum MergedSolver<'ctx> {
    Solver(z3::Solver<'ctx>),
    Optimize(z3::Optimize<'ctx>),
}
impl<'ctx> MergedSolver<'ctx> {
    fn assert(&self, constraint: &Bool<'ctx>) {
        match self {
            MergedSolver::Solver(s) => s.assert(constraint),
            MergedSolver::Optimize(s) => s.assert(constraint),
        }
    }
    fn check(&self) -> SatResult {
        match self {
            MergedSolver::Solver(s) => s.check(),
            MergedSolver::Optimize(s) => s.check(&[]),
        }
    }
    fn get_model(&self) -> Option<Model<'ctx>> {
        match self {
            MergedSolver::Solver(s) => s.get_model(),
            MergedSolver::Optimize(s) => s.get_model(),
        }
    }
}

fn sum<'ctx, I>(context: &'ctx Context, iter: I) -> Real<'ctx> where I: Iterator<Item = Real<'ctx>> {
    let mut res = Real::from_real(context, 0, 1);
    for v in iter {
        res += v;
    }
    res
}
fn count<'ctx, 'a, I>(context: &'ctx Context, iter: I) -> Int<'ctx> where 'ctx: 'a, I: Iterator<Item = Bool<'ctx>> {
    let zero = Int::from_u64(context, 0);
    let one = Int::from_u64(context, 1);
    let mut res = one.clone();
    for v in iter {
        res += v.ite(&one, &zero);
    }
    res
}

fn build_numeric_expr<'ctx, P: Point>(context: &(&'ctx Context, &BTreeMap<&str, P>, &BTreeMap<P, Real<'ctx>>, &Adj<'_, P>, &Param), expr: &NumericExpr) -> Real<'ctx> {
    let dom = |p: P| sum(context.0, context.4.dom_region(p, context.3).iter().copied().map(|x| context.2[&x].clone()));
    match expr {
        NumericExpr::Constant { value } => Real::from_real(context.0, *value.numer() as i32, *value.denom() as i32),
        NumericExpr::DetectorValue { vertex } => context.2[&context.1[vertex.as_str()]].clone(),
        NumericExpr::DetectorValueSum => sum(context.0, context.2.values().cloned()),
        NumericExpr::DominationNumber { vertex } => dom(context.1[vertex.as_str()]),
        NumericExpr::Share { vertex } => {
            let p: P = context.1[vertex.as_str()];
            let det_val: &Real = &context.2[&p];
            sum(context.0, context.4.dom_region(p, context.3).iter().copied().map(|pp| det_val / dom(pp)))
        },

        NumericExpr::Neg { value } => -build_numeric_expr(context, value),

        NumericExpr::Mul { left, right } => build_numeric_expr(context, left) * build_numeric_expr(context, right),
        NumericExpr::Div { left, right } => build_numeric_expr(context, left) / build_numeric_expr(context, right),

        NumericExpr::Add { left, right } => build_numeric_expr(context, left) + build_numeric_expr(context, right),
        NumericExpr::Sub { left, right } => build_numeric_expr(context, left) - build_numeric_expr(context, right),
    }
}
fn build_bool_expr<'ctx, P: Point>(context: &(&'ctx Context, &BTreeMap<&str, P>, &BTreeMap<P, Real<'ctx>>, &Adj<'_, P>, &Param), expr: &BoolExpr) -> Bool<'ctx> {
    match expr {
        BoolExpr::Constant { value } => Bool::from_bool(context.0, *value),

        BoolExpr::Not { value } => build_bool_expr(context, value).not(),

        BoolExpr::Less { left, right } => build_numeric_expr(context, left).lt(&build_numeric_expr(context, right)),
        BoolExpr::LessEq { left, right } => build_numeric_expr(context, left).le(&build_numeric_expr(context, right)),
        BoolExpr::Eq { left, right } => build_numeric_expr(context, left)._eq(&build_numeric_expr(context, right)),
        BoolExpr::Neq { left, right } => build_numeric_expr(context, left)._eq(&build_numeric_expr(context, right)).not(),

        BoolExpr::And { left, right } => build_bool_expr(context, left) & build_bool_expr(context, right),
        BoolExpr::Xor { left, right } => build_bool_expr(context, left) ^ build_bool_expr(context, right),
        BoolExpr::Or { left, right } => build_bool_expr(context, left) | build_bool_expr(context, right),
    }
}

#[derive(Clone, Copy)]
struct Grid {
    name: &'static str,
    adj: &'static Adj<'static, (i32, i32)>,
}
impl FromStr for Grid {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, String> {
        Ok(match s.trim().to_lowercase().as_str() {
            "k" | "king"    => Grid { name: "K",   adj: &adj_k   },
            "sq" | "square" => Grid { name: "SQ",  adj: &adj_sq  },
            "tri"           => Grid { name: "TRI", adj: &adj_tri },
            "hex"           => Grid { name: "HEX", adj: &adj_hex },
            _ => return Err(format!("unknown grid type: '{}'", s)),
        })
    }
}

#[derive(Clone, Copy)]
enum DomKind {
    Open,
    Closed,
}

#[derive(Clone, Copy)]
enum DistyKind {
    Symmetric, // |(A - B) + (B - A)| >= k
    Sharp,     // |A - B| >= k or |B - A| >= k
    BiSharp,   // |A - B| >= k and |B - A| >= k
}

#[derive(Clone, Copy)]
struct BasicParam {
    name: &'static str,
    dom_kind: DomKind,
    disty_kind: DistyKind,
    dom: usize,
    disty: usize,
    add_self: bool,
}
#[derive(Clone, Copy)]
struct Param {
    basic: BasicParam,
    fractional: bool,
    efficient: bool,
}
impl Param {
    fn get_name(&self) -> String {
        let mut res = String::with_capacity(self.basic.name.len() + 3);
        if self.efficient { res.push('E'); }
        if self.fractional { res.push('F'); }
        if !res.is_empty() { res.push(':'); }
        res.push_str(self.basic.name);
        res
    }
    fn neighborhood<P: Point>(&self, p: P, adj: &Adj<P>) -> BTreeSet<P> {
        let mut res = adj(p);
        match self.basic.dom_kind {
            DomKind::Open => assert!(!res.contains(&p)),
            DomKind::Closed => assert!(res.insert(p)),
        }
        res
    }
    fn dom_region<P: Point>(&self, p: P, adj: &Adj<P>) -> BTreeSet<P> {
        let mut res = self.neighborhood(p, adj);
        if self.basic.add_self {
            res.insert(p);
        }
        res
    }
    fn check_dom<'ctx, P: Point>(&self, context: &'ctx Context, p: (P, &Real<'ctx>), adj: &Adj<P>, counter: &Counter<'ctx, P>) -> Option<Bool<'ctx>> {
        if self.basic.dom == 0 { return None }
        let value = counter(&self.dom_region(p.0, adj));
        let req = Real::from_real(context, self.basic.dom as i32, 1);
        Some(if self.efficient { value._eq(&req) } else { value.ge(&req) })
    }
    fn check_disty<'ctx, P: Point>(&self, context: &'ctx Context, p: (P, &Real<'ctx>), q: (P, &Real<'ctx>), adj: &Adj<P>, distances: &Distances<P>, counter: &Counter<'ctx, P>) -> Option<Bool<'ctx>> {
        if self.basic.disty == 0 || distances.get(p.0, q.0) >= 3 { return None }
        let regions = (self.neighborhood(p.0, adj), self.neighborhood(q.0, adj));
        let req = Real::from_real(context, self.basic.disty as i32, 1);
        let mut r1: BTreeSet<P> = &regions.0 - &regions.1;
        let mut r2: BTreeSet<P> = &regions.1 - &regions.0;
        if self.basic.add_self {
            r1.insert(p.0);
            r1.insert(q.0);

            r2.insert(p.0);
            r2.insert(q.0);
        }
        Some(match self.basic.disty_kind {
            DistyKind::Symmetric => counter(&r1.union(&r2).copied().collect()).ge(&req),
            DistyKind::Sharp => counter(&r1).ge(&req) | counter(&r2).ge(&req),
            DistyKind::BiSharp => counter(&r1).ge(&req) & counter(&r2).ge(&req),
        })
    }
}
impl FromStr for Param {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        fn parse_basic(s: &str) -> Option<BasicParam> {
            Some(match s.trim().to_lowercase().as_str() {
                "odom"                           => BasicParam { name: "ODOM",    dom_kind: DomKind::Open,   disty_kind: DistyKind::Symmetric, dom: 1, disty: 0, add_self: false },
                "old"                            => BasicParam { name: "OLD",     dom_kind: DomKind::Open,   disty_kind: DistyKind::Symmetric, dom: 1, disty: 1, add_self: false },
                "red:old" | "red-old" | "redold" => BasicParam { name: "RED:OLD", dom_kind: DomKind::Open,   disty_kind: DistyKind::Symmetric, dom: 2, disty: 2, add_self: false },
                "det:old" | "det-old" | "detold" => BasicParam { name: "DET:OLD", dom_kind: DomKind::Open,   disty_kind: DistyKind::Sharp,     dom: 2, disty: 2, add_self: false },
                "err:old" | "err-old" | "errold" => BasicParam { name: "ERR:OLD", dom_kind: DomKind::Open,   disty_kind: DistyKind::Symmetric, dom: 3, disty: 3, add_self: false },
                "dom"                            => BasicParam { name: "DOM",     dom_kind: DomKind::Closed, disty_kind: DistyKind::Symmetric, dom: 1, disty: 0, add_self: false },
                "ic"                             => BasicParam { name: "IC",      dom_kind: DomKind::Closed, disty_kind: DistyKind::Symmetric, dom: 1, disty: 1, add_self: false },
                "red:ic"  | "red-ic"  | "redic"  => BasicParam { name: "RED:IC",  dom_kind: DomKind::Closed, disty_kind: DistyKind::Symmetric, dom: 2, disty: 2, add_self: false },
                "det:ic"  | "det-ic"  | "detic"  => BasicParam { name: "DET:IC",  dom_kind: DomKind::Closed, disty_kind: DistyKind::Sharp,     dom: 2, disty: 2, add_self: false },
                "rsp:ic"  | "rsp-ic"  | "rspic"  => BasicParam { name: "RSP:IC",  dom_kind: DomKind::Closed, disty_kind: DistyKind::Symmetric, dom: 2, disty: 3, add_self: false },
                "err:ic"  | "err-ic"  | "erric"  => BasicParam { name: "ERR:IC",  dom_kind: DomKind::Closed, disty_kind: DistyKind::Symmetric, dom: 3, disty: 3, add_self: false },
                "ld"                             => BasicParam { name: "LD",      dom_kind: DomKind::Open,   disty_kind: DistyKind::Symmetric, dom: 1, disty: 1, add_self: true  },
                "red:ld"  | "red-ld"  | "redld"  => BasicParam { name: "RED:LD",  dom_kind: DomKind::Open,   disty_kind: DistyKind::Symmetric, dom: 2, disty: 2, add_self: true  },
                "det:ld"  | "det-ld"  | "detld"  => BasicParam { name: "DET:LD",  dom_kind: DomKind::Open,   disty_kind: DistyKind::Sharp,     dom: 2, disty: 2, add_self: true  },
                "err:ld"  | "err-ld"  | "errld"  => BasicParam { name: "ERR:LD",  dom_kind: DomKind::Open,   disty_kind: DistyKind::Symmetric, dom: 3, disty: 3, add_self: true  },
                "sic"                            => BasicParam { name: "SIC",     dom_kind: DomKind::Closed, disty_kind: DistyKind::BiSharp,   dom: 1, disty: 1, add_self: false },
                _ => return None,
            })
        }

        let mut fractional = false;
        let mut efficient = false;
        let mut ss = s;
        loop {
            if let Some(basic) = parse_basic(ss) {
                return Ok(Param { basic, fractional, efficient })
            }

            let ch = ss.chars().next().unwrap_or('\0').to_ascii_lowercase();
            if !fractional && ch == 'f' {
                ss = &ss[1..];
                fractional = true;
            } else if !efficient && ch == 'e' {
                ss = &ss[1..];
                efficient = true;
            } else {
                return Err(format!("unknown param type: {s:?}"));
            }

            let br = ss.chars().next().unwrap_or('\0');
            if br == ':' || br == '-' {
                ss = &ss[1..];
            }
        }
    }
}

fn test_graph(graph: &Graph, param: &Param, exhaustive: bool, log: bool, omit_isomorphic: bool, optimize: bool, constraint: &BoolExpr) -> Vec<BTreeMap<usize, Rational64>> {
    let petgraph_graph: petgraph::Graph<usize, ()> = {
        let mut g = petgraph::Graph::new();
        let mut nodes = Vec::with_capacity(graph.verts.len());
        for i in 0..graph.verts.len() {
            nodes.push(g.add_node(i));
        }
        for (i, (_, adj)) in graph.verts.iter().enumerate() {
            for other in adj.iter() {
                g.add_edge(nodes[i], nodes[*other], ());
            }
        }
        g
    };
    let is_isomorphic_solution = |s1: &BTreeMap<usize, Rational64>, s2: &BTreeMap<usize, Rational64>| {
        petgraph::algo::is_isomorphic_matching(&petgraph_graph, &petgraph_graph, |u, v| s1.get(u).copied().unwrap_or_default() == s2.get(v).copied().unwrap_or_default(), |_, _| true)
    };

    let n = graph.verts.len();
    let adj = |p: usize| graph.verts[p].1.iter().copied().collect();
    let distances = Distances::within_shape(&(0..n).collect(), &adj);

    let vert_name_to_idx = graph.verts.iter().enumerate().map(|(i, v)| (v.0.as_str(), i)).collect::<BTreeMap<_,_>>();

    let context = Context::new(&Default::default());
    let verts: BTreeMap<usize, Real> = (0..n).map(|p| (p, Real::new_const(&context, format!("v{p}")))).collect();

    let zero = Real::from_real(&context, 0, 1);
    let one = Real::from_real(&context, 1, 1);

    let s = match optimize {
        true => {
            let s = Optimize::new(&context);
            s.minimize(&sum(&context, verts.values().cloned()));
            if param.fractional {
                s.minimize(&count(&context, verts.values().map(|x| x.gt(&zero))));
            }
            MergedSolver::Optimize(s)
        }
        false => MergedSolver::Solver(Solver::new(&context)),
    };

    for (i, v) in verts.iter() {
        match param.fractional {
            true => s.assert(&(v.ge(&zero) & v.le(&one))),
            false => {
                let flag = Bool::new_const(&context, format!("v{i}f")); // vastly faster than (v == 0 || v == 1)
                s.assert(&v._eq(&flag.ite(&one, &zero)));
            }
        }
    }

    let count_det = |points: &BTreeSet<usize>| -> Real {
        sum(&context, points.iter().copied().map(|p| verts[&p].clone()))
    };

    for p in 0..n {
        if let Some(req) = param.check_dom(&context, (p, &verts[&p]), &adj, &|group| count_det(group)) {
            s.assert(&req);
        }
    }
    for pq in (0..n).combinations(2) {
        let (p, q) = (pq[0], pq[1]);
        if let Some(req) = param.check_disty(&context, (p, &verts[&p]), (q, &verts[&q]), &adj, &distances, &|group| count_det(group)) {
            s.assert(&req);
        }
    }

    s.assert(&build_bool_expr(&(&context, &vert_name_to_idx, &verts, &adj, param), constraint));

    fn solution_string<I: Iterator<Item = (usize, Rational64)>>(graph: &Graph, verts: I) -> String {
        let mut names: Vec<_> = verts.map(|v| (graph.verts[v.0].0.as_str(), v.1)).collect();
        names.sort_by(|a, b| numeric_sort::cmp(a.0, b.0));
        let mut res = String::new();
        res.push('{');
        for (name, v) in names {
            if *v.numer() != 0 {
                res.push(' ');
                res.push_str(name);
                if *v.numer() != *v.denom() {
                    write!(res, "({v})").unwrap();
                }
            }
        }
        res.push_str(" }");
        res
    }

    let mut solutions: Vec<BTreeMap<usize, Rational64>> = vec![];
    let mut minimum_value = None;
    loop {
        match s.check() {
            SatResult::Sat => {
                let model = s.get_model().unwrap();
                let detectors: BTreeMap<usize, Rational64> = verts.iter().map(|v| (*v.0, model.eval(v.1, false).unwrap().as_real().unwrap())).map(|(i, (p, q))| (i, Rational64::new(p, q))).collect();

                let value = detectors.values().sum::<Rational64>();
                match &minimum_value {
                    None => minimum_value = Some(value),
                    Some(prev_min) => match optimize {
                        true => {
                            assert!(*prev_min <= value);
                            if *prev_min < value { break }
                        }
                        false => if value < *prev_min {
                            minimum_value = Some(value);
                        }
                    }
                }

                let mut different_answer = Bool::from_bool(&context, false);
                for (i, v) in verts.iter() {
                    let value = detectors.get(&i).copied().unwrap();
                    different_answer |= v._eq(&Real::from_real(&context, *value.numer() as i32, *value.denom() as i32)).not();
                }
                s.assert(&different_answer);

                if omit_isomorphic && solutions.iter().any(|s1| is_isomorphic_solution(s1, &detectors)) {
                    continue
                }

                if log {
                    let s = solution_string(graph, detectors.iter().map(|x| (*x.0, *x.1)));
                    let s_bar = solution_string(graph, detectors.iter().filter(|x| *x.1.numer() == 0).map(|x| (*x.0, Rational64::new(1, 1))));
                    println!("solution {}: sum(S) = {value}, S = {s}, !S = {s_bar}", solutions.len() + 1);
                }

                solutions.push(detectors);
                if !exhaustive {
                    break
                }
            }
            SatResult::Unsat => break,
            SatResult::Unknown => panic!("z3 reported unknown satisfiability - consider disabling optimization mode"),
        }
    }

    if log {
        match &minimum_value {
            Some(value) => match (exhaustive, omit_isomorphic) {
                (false, _) => println!("\nfound a {}solution of size {}", if optimize { "minimum " } else { "" }, Verbose(value)),
                (true, true) => println!("\nexhausted all {} non-isomorphic {}solutions of size {}", solutions.len(), if optimize { "minimum " } else { "" }, Verbose(value)),
                (true, false) => {
                    println!("\nexhausted all {} {}solutions of size {}\n", solutions.len(), if optimize { "minimum " } else { "" }, Verbose(value));

                    let mut always_detectors = vec![true; n];
                    let mut never_detectors = vec![true; n];
                    for solution in solutions.iter() {
                        for i in 0..n {
                            let is_detector = *solution.get(&i).unwrap().numer() != 0;
                            if is_detector { never_detectors[i] = false; }
                            else { always_detectors[i] = false; }
                        }
                    }
                    let sometimes_detectors: Vec<_> = iter::zip(&always_detectors, &never_detectors).map(|(a, b)| !a && !b).collect();

                    println!("always    detectors: {}", solution_string(graph,    always_detectors.iter().enumerate().filter(|x| *x.1).map(|x| (x.0, Rational64::new(1, 1)))));
                    println!("never     detectors: {}", solution_string(graph,     never_detectors.iter().enumerate().filter(|x| *x.1).map(|x| (x.0, Rational64::new(1, 1)))));
                    println!("sometimes detectors: {}", solution_string(graph, sometimes_detectors.iter().enumerate().filter(|x| *x.1).map(|x| (x.0, Rational64::new(1, 1)))));
                }
            }
            None => println!("no solution"),
        }
    }

    solutions
}
fn test_tiling(shape: &BTreeSet<(i32, i32)>, grid: &Grid, param: &Param, log: bool) -> Option<(BTreeMap<(i32, i32), Rational64>, (i32, i32), (i32, i32), usize)> {
    if log {
        println!("tile shape:");
        print_shape(&shape, &Default::default());
    }

    let inflated = inflate(&shape, grid.adj, 2);
    let interior = get_interior(&shape, grid.adj);
    let distances = Distances::within_shape(&inflated, grid.adj);
    let tilings = get_tilings(&shape);

    if log {
        println!("\nfound {} tilings...", tilings.len());
    }
    if tilings.is_empty() {
        return None;
    }

    let context = Context::new(&Default::default());
    let verts: BTreeMap<(i32, i32), Real> = shape.iter().copied().map(|p| (p, Real::new_const(&context, format!("v{},{}", p.0, p.1)))).collect();
    let tiling_index = Int::new_const(&context, "tidx");

    let zero = Real::from_real(&context, 0, 1);
    let one = Real::from_real(&context, 1, 1);

    let s = Optimize::new(&context);
    s.minimize(&sum(&context, verts.values().cloned()));
    if param.fractional {
        s.minimize(&count(&context, verts.values().map(|x| x.gt(&zero))));
    }

    for (p, v) in verts.iter() {
        match param.fractional {
            true => s.assert(&(v.ge(&zero) & v.le(&one))),
            false => {
                let flag = Bool::new_const(&context, format!("v{},{}f", p.0, p.1)); // vastly faster than (v == 0 || v == 1)
                s.assert(&v._eq(&flag.ite(&one, &zero)));
            }
        }
    }

    let count_det = |points: &BTreeSet<(i32, i32)>, tiling: &BTreeMap<(i32, i32), (i32, i32)>| -> Real {
        sum(&context, points.iter().map(|p| verts[&tiling[p]].clone()))
    };

    let identity_map = shape.iter().copied().map(|p| (p, p)).collect();
    for p in interior.iter().copied() {
        if let Some(req) = param.check_dom(&context, (p, &verts[&p]), &grid.adj, &|group| count_det(group, &identity_map)) {
            s.assert(&req);
        }
    }
    for pq in interior.iter().copied().combinations(2) {
        let (p, q) = (pq[0], pq[1]);
        if let Some(req) = param.check_disty(&context, (p, &verts[&p]), (q, &verts[&q]), &grid.adj, &distances, &|group| count_det(group, &identity_map)) {
            s.assert(&req);
        }
    }
    drop(identity_map);

    let mut any_solution = Bool::from_bool(&context, false);
    for (i, (tiling, _, _)) in tilings.iter().enumerate() {
        let mut solution = Bool::from_bool(&context, true);
        for p in inflated.iter().copied() {
            if !interior.contains(&p) {
                if let Some(req) = param.check_dom(&context, (p, &verts[&tiling[&p]]), &grid.adj, &|group| count_det(group, tiling)) {
                    solution &= &req;
                }
            }
        }
        for pq in inflated.iter().copied().combinations(2) {
            let (p, q) = (pq[0], pq[1]);
            if !interior.contains(&p) || !interior.contains(&q) {
                if let Some(req) = param.check_disty(&context, (p, &verts[&tiling[&p]]), (q, &verts[&tiling[&q]]), &grid.adj, &distances, &|group| count_det(group, tiling)) {
                    solution &= &req;
                }
            }
        }
        solution &= tiling_index._eq(&Int::from_u64(&context, i as u64));
        any_solution |= solution;
    }
    s.assert(&any_solution);

    if log {
        println!("checking {} tilings...\n", tilings.len());
    }

    match s.check(&[]) {
        SatResult::Sat => {
            let model = s.get_model().unwrap();
            let detectors = verts.iter().map(|(p, v)| (*p, model.eval(v, false).unwrap().as_real().unwrap())).map(|(p, v)| (p, Rational64::new(v.0, v.1))).collect();
            let tidx = model.eval(&tiling_index, false).unwrap().as_u64().unwrap() as usize;
            Some((detectors, tilings[tidx].1, tilings[tidx].2, tidx))
        }
        SatResult::Unsat => None,
        SatResult::Unknown => unreachable!(),
    }
}
fn print_result(shape: &BTreeSet<(i32, i32)>, res: &Option<(BTreeMap<(i32, i32), Rational64>, (i32, i32), (i32, i32), usize)>) {
    match res {
        Some((detectors, b1, b2, tidx)) => {
            println!("found minimum:");
            print_shape(&shape, detectors);
            let total = detectors.iter().map(|x| x.1).sum::<Rational64>();
            let value = total / Rational64::new(shape.len() as i64, 1);
            println!("\n{}", Verbose(&value));
            println!("basis: {:?} {:?} (tiling index {})", b1, b2, tidx);
        }
        None => println!("no solution"),
    }
}

#[allow(dead_code)]
#[derive(Debug)]
enum GraphParseError {
    IO { error: io::Error },
    MissingColon { token: String },
    EmptyVertName { token: String },
    Loop { vert: String },
}
impl From<io::Error> for GraphParseError { fn from(error: io::Error) -> Self { Self::IO { error } } }

#[derive(Default, Debug, Clone)]
struct Graph {
    verts: Vec<(String, BTreeSet<usize>)>,
}
impl Graph {
    fn read(src: &mut dyn BufRead) -> Result<Graph, GraphParseError> {
        let mut name_to_index: BTreeMap<String, usize> = Default::default();
        let mut verts: Vec<(String, BTreeSet<usize>)> = Default::default();

        let mut get_vert_index = move |verts: &mut Vec<(String, BTreeSet<usize>)>, name: String| -> usize {
            debug_assert_eq!(name_to_index.len(), verts.len());

            let n = name_to_index.len();
            let index = *name_to_index.entry(name.clone()).or_insert(n);
            if index == n { verts.push((name, Default::default())) }

            debug_assert_eq!(name_to_index.len(), verts.len());
            index
        };

        for line in src.lines() {
            for token in line?.split_whitespace() {
                let p = token.find(':').ok_or_else(|| GraphParseError::MissingColon { token: token.to_owned() })?;
                if p == 0 || p == token.len() - 1 { return Err(GraphParseError::EmptyVertName { token: token.to_owned() }) }
                let u = get_vert_index(&mut verts, token[..p].to_owned());
                let v = get_vert_index(&mut verts, token[p+1..].to_owned());
                if u == v { return Err(GraphParseError::Loop { vert: verts.into_iter().nth(u).unwrap().0 }) }
                verts[u].1.insert(v);
                verts[v].1.insert(u);
            }
        }

        Ok(Graph { verts })
    }
    fn build(expr: &GraphExpr) -> Result<Graph, GraphParseError> {
        match expr {
            GraphExpr::Path { size } => Ok(Graph::by_adj(&(0..*size).collect::<Vec<_>>(), |&x| format!("{x}"), |&x, &y| x.abs_diff(y) == 1)),
            GraphExpr::Cycle { size } => Ok(Graph::by_adj(&(0..*size).collect::<Vec<_>>(), |&x| format!("{x}"), |&x, &y| x.abs_diff(y) == 1 || x.abs_diff(y) == *size - 1)),
            GraphExpr::File { path } => Graph::read(&mut BufReader::new(File::open(path).unwrap())),
            GraphExpr::CartesianProduct { left, right } => Ok(Graph::build(left)?.cartesian_product(&Graph::build(right)?)),
            GraphExpr::KingCartesianProduct { left, right } => Ok(Graph::build(left)?.king_cartesian_product(&Graph::build(right)?)),
        }
    }
    fn by_adj<T, N, A>(points: &[T], namer: N, is_adj: A) -> Self where N: Fn(&T) -> String, A: Fn(&T, &T) -> bool {
        let mut verts = Vec::with_capacity(points.len());
        for (i, v) in points.iter().enumerate() {
            let mut v_adj = BTreeSet::new();
            for (j, u) in points.iter().enumerate() {
                if i == j { continue }
                let adj = is_adj(v, u);
                debug_assert_eq!(adj, is_adj(u, v));
                if adj { v_adj.insert(j); }
            }
            verts.push((namer(v), v_adj));
        }
        Self { verts }
    }
    fn cartesian_product(&self, other: &Self) -> Self {
        Self::by_adj(
            &self.verts.iter().enumerate().cartesian_product(other.verts.iter().enumerate()).collect::<Vec<_>>(),
            |x| format!("{},{}", x.0.1.0, x.1.1.0),
            |x, y| (x.0.0 == y.0.0 && other.verts[x.1.0].1.contains(&y.1.0)) || (x.1.0 == y.1.0 && self.verts[x.0.0].1.contains(&y.0.0)),
        )
    }
    fn king_cartesian_product(&self, other: &Self) -> Self {
        Self::by_adj(
            &self.verts.iter().enumerate().cartesian_product(other.verts.iter().enumerate()).collect::<Vec<_>>(),
            |x| format!("{},{}", x.0.1.0, x.1.1.0),
            |x, y| (x.0.0 == y.0.0 && other.verts[x.1.0].1.contains(&y.1.0)) || (x.1.0 == y.1.0 && self.verts[x.0.0].1.contains(&y.0.0)) || (other.verts[x.1.0].1.contains(&y.1.0) && self.verts[x.0.0].1.contains(&y.0.0)),
        )
    }
}
impl fmt::Display for Graph {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut tokens = vec![];
        for (v_name, adj) in self.verts.iter() {
            for &u in adj.iter() {
                let u_name = &self.verts[u].0;
                if numeric_sort::cmp(v_name, u_name) == Ordering::Less {
                    tokens.push(format!("{}:{}", v_name, u_name));
                }
            }
        }
        numeric_sort::sort(&mut tokens);
        write!(f, "{{")?;
        for token in tokens.iter() {
            write!(f, " {}", token)?;
        }
        write!(f, " }}")
    }
}

/// Compute various minimum values for general detection systems.
#[derive(Parser)]
enum Mode {
    /// Minimum value for a rectangular tiling on an infinite grid.
    Rect {
        /// Number of rows in the rectangular tile.
        rows: NonZeroUsize,
        /// Number of columns in the rectangular tile.
        cols: NonZeroUsize,
        /// The graph parameter to check; e.g., old, ic, red:old, red:ic, etc.
        param: Param,
        /// The type of infinite grid; e.g., k, sq, tri, etc.
        grid: Grid,
    },
    /// Minimum value for an unknown tiling on an infinite grid.
    Entropy {
        /// Number of rows in the bounding rectangle.
        rows: NonZeroUsize,
        /// Number of columns in the bounding rectangle.
        cols: NonZeroUsize,
        /// The size of the enclosed tile whose shape is unknown.
        size: NonZeroUsize,
        ///Tje graph parameter to check; e.g., old, ic, red:old, red:ic, etc.
        param: Param,
        /// The type of infinite grid; e.g., k, sq, tri, etc.
        grid: Grid,

        /// The number of threads to use for iterating geometries.
        #[clap(short, long, default_value_t = NonZeroUsize::new(num_cpus::get()).unwrap())]
        threads: NonZeroUsize,
    },
    /// Minimum value for a finite graph.
    Finite {
        /// The graph expression to operate on.
        /// This supports the syntax Pn and Cn for paths and cycles on n vertices.
        /// The * operator denotes the cartesian product of graphs, while ** denotes the king cartesian product.
        /// The syntax file(<path>) allows loading a graph from a file,
        /// which should be a whitespace-separated sequence of a:b tokens denoting edges (and implicitly vertices) in the graph.
        graph: String,
        /// The graph parameter to check; e.g., old, ic, red:old, red:ic, etc.
        param: Param,

        /// Exhaustively generate all solutions
        #[clap(short, long)]
        all: bool,

        /// Include isomorphic solutions in output
        #[clap(long)]
        include_iso: bool,

        /// Make the solver output only optimal solutions
        #[clap(long)]
        include_suboptimal: bool,

        /// Extra constraint on output solutions
        #[clap(long, default_value_t = String::from("true"))]
        constraint: String,
    },
}

fn main() {
    match Mode::parse() {
        Mode::Rect { rows, cols, grid, param } => {
            let shape = rect(rows.get(), cols.get());
            println!("checking {} {}\n", param.get_name(), grid.name);
            print_result(&shape, &test_tiling(&shape, &grid, &param, true))
        }
        Mode::Entropy { rows, cols, size, grid, param, threads } => {
            let best_total = Arc::new(Mutex::new(None));
            let shapes = Arc::new(Mutex::new((0..rows.get() as i32).cartesian_product(0..cols.get() as i32).combinations(size.get()).map(|x| x.into_iter().collect::<BTreeSet<_>>()).fuse()));
            let shapes_total = Arc::new(AtomicUsize::new(0));

            let threads = (0..threads.get()).map(|_| {
                let best_total = best_total.clone();
                let shapes = shapes.clone();
                let shapes_total = shapes_total.clone();
                thread::spawn(move || loop {
                    let shape = match shapes.lock().unwrap().next() {
                        Some(x) => x,
                        None => break,
                    };
                    shapes_total.fetch_add(1, MemOrder::Relaxed);
                    if let Some(res) = test_tiling(&shape, &grid, &param, false) {
                        let total: Rational64 = res.0.values().sum();
                        let mut best_total = best_total.lock().unwrap();
                        if best_total.map(|x| total > x).unwrap_or(true) {
                            *best_total = Some(total);
                            println!("\nnew current best:");
                            print_result(&shape, &Some(res));
                        }
                    }
                })
            }).collect::<Vec<_>>();
            for thread in threads {
                thread.join().unwrap();
            }

            println!("\ntested {} geometries", shapes_total.load(MemOrder::Relaxed));
        }
        Mode::Finite { graph, param, all, include_iso, include_suboptimal, constraint } => {
            let graph = Graph::build(&grammar::GraphExprParser::new().parse(&graph).unwrap()).unwrap();
            let constraint = grammar::BoolExprParser::new().parse(&constraint).unwrap();

            println!("checking {}\nG = {}\nn = {}\ne = {}\n\nsubject to constraint: {constraint}\n", param.get_name(), graph, graph.verts.len(), graph.verts.iter().map(|x| x.1.len()).sum::<usize>() / 2);
            test_graph(&graph, &param, all, true, !include_iso, !include_suboptimal, &constraint);
        }
    }
}
