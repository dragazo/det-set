use std::collections::{BTreeSet, BTreeMap};
use std::str::FromStr;
use std::num::NonZeroUsize;
use std::io::{self, BufRead, BufReader};
use std::fmt::{self, Write};
use std::cmp::Ordering;
use std::fs::File;
use std::iter;

use itertools::Itertools;
use clap::Parser;

use z3::{Context, Optimize, SatResult};
use z3::ast::{Bool, Real, Int, Ast};

use num_rational::Rational64;

type Adj<'a, P> = dyn 'a + Fn(P) -> BTreeSet<P>;
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

fn inflate<P: Point>(shape: &BTreeSet<P>, adj: &Adj<P>, radius: usize) -> BTreeSet<P> {
    let mut res = shape.clone();
    for _ in 0..radius {
        let mut new_res = res.clone();
        for p in res.iter().copied() {
            new_res.append(&mut adj(p));
        }
        res = new_res;
    }
    res
}
fn get_interior<P: Point>(shape: &BTreeSet<P>, adj: &Adj<P>) -> BTreeSet<P> {
    shape.iter().copied().filter(|u| adj(*u).into_iter().all(|v| shape.contains(&v))).collect()
}

struct Distances<P: Point>(BTreeMap<(P, P), usize>);
impl<P: Point> Distances<P> {
    fn within_shape(shape: &BTreeSet<P>, adj: &Adj<P>) -> Self {
        let mut res = BTreeMap::default();
        for points in shape.iter().combinations_with_replacement(2) {
            let (p, q) = (*points[0], *points[1]);
            let mut region = BTreeSet::new();
            region.insert(p);
            let mut dist = 0;
            while !region.contains(&q) {
                region = inflate(&region, adj, 1);
                dist += 1;
            }
            res.insert((p, q), dist);
            res.insert((q, p), dist);
        }
        Self(res)
    }
    fn get(&self, p: P, q: P) -> usize {
        self.0[&(p, q)]
    }
}

const TILE_RADIUS: i32 = 3;
fn get_tilings(shape: &BTreeSet<(i32, i32)>) -> Vec<(BTreeMap<(i32, i32), (i32, i32)>, (i32, i32), (i32, i32))> {
    let inflated = inflate(shape, &adj_k, 3);
    let size = get_size(shape);
    let mut tilings: BTreeMap<BTreeMap<(i32, i32), (i32, i32)>, ((i32, i32), (i32, i32))> = Default::default();
    for dr1 in 0..=2*size.0 as i32 {
        for dc1 in 0..=2*size.1 as i32 {
            for dr2 in 0..=2*size.0 as i32 {
                'skip: for dc2 in 0..=2*size.1 as i32 {
                    let (b1, b2) = ((dr1, dc1), (dr2, dc2));
                    let mut res: BTreeMap<(i32, i32), (i32, i32)> = Default::default();
                    for m1 in -TILE_RADIUS..=TILE_RADIUS {
                        for m2 in -TILE_RADIUS..=TILE_RADIUS {
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

fn max<'ctx>(a: &Real<'ctx>, b: &Real<'ctx>) -> Real<'ctx> {
    a.ge(b).ite(a, b)
}
fn sum<'ctx, 'a, I>(context: &'ctx Context, iter: I) -> Real<'ctx> where 'ctx: 'a, I: Iterator<Item = &'a Real<'ctx>> {
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

struct Param {
    name: &'static str,
    open_dom: bool,
    dom: usize,
    disty: usize,
    sharp_disty: bool,
    disty_dist_limit: usize,
    fractional: bool,
    efficient: bool,
}
impl Param {
    fn dom_region<P: Point>(&self, p: P, adj: &Adj<P>) -> BTreeSet<P> {
        let mut res = adj(p);
        if !self.open_dom { assert!(res.insert(p)); }
        else { assert!(!res.contains(&p)); }
        res
    }
    fn check_dom<'ctx, P: Point>(&self, context: &'ctx Context, p: (P, &Real<'ctx>), adj: &Adj<P>, counter: &Counter<'ctx, P>) -> Option<Bool<'ctx>> {
        if self.dom == 0 { return None }
        let value = counter(&self.dom_region(p.0, adj));
        let min = Real::from_real(context, self.dom as i32, 1);
        Some(if self.efficient { value._eq(&min) } else { value.ge(&min) })
    }
    fn check_disty<'ctx, P: Point>(&self, context: &'ctx Context, p: (P, &Real<'ctx>), q: (P, &Real<'ctx>), adj: &Adj<P>, distances: &Distances<P>, counter: &Counter<'ctx, P>) -> Option<Bool<'ctx>> {
        if self.disty == 0 || distances.get(p.0, q.0) >= self.disty_dist_limit { return None }
        let regions = (self.dom_region(p.0, adj), self.dom_region(q.0, adj));
        Some(match self.sharp_disty {
            false => counter(&regions.0.symmetric_difference(&regions.1).copied().collect()).ge(&Real::from_real(context, self.disty as i32, 1)),
            true => max(&counter(&(&regions.0 - &regions.1)), &counter(&(&regions.1 - &regions.0))).ge(&Real::from_real(context, self.disty as i32, 1)),
        })
    }
}
impl FromStr for Param {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s.trim().to_lowercase().as_str() {
            "old"                            => Param { name: "OLD",     open_dom: true,  dom: 1, disty: 1, sharp_disty: false, disty_dist_limit: 3, fractional: false, efficient: false },
            "red:old" | "red-old" | "redold" => Param { name: "RED:OLD", open_dom: true,  dom: 2, disty: 2, sharp_disty: false, disty_dist_limit: 3, fractional: false, efficient: false },
            "det:old" | "det-old" | "detold" => Param { name: "DET:OLD", open_dom: true,  dom: 2, disty: 2, sharp_disty: true,  disty_dist_limit: 3, fractional: false, efficient: false },
            "err:old" | "err-old" | "errold" => Param { name: "ERR:OLD", open_dom: true,  dom: 3, disty: 3, sharp_disty: false, disty_dist_limit: 3, fractional: false, efficient: false },
            "ic"                             => Param { name: "IC",      open_dom: false, dom: 1, disty: 1, sharp_disty: false, disty_dist_limit: 3, fractional: false, efficient: false },
            "red:ic" | "red-ic" | "redic"    => Param { name: "RED:IC",  open_dom: false, dom: 2, disty: 2, sharp_disty: false, disty_dist_limit: 3, fractional: false, efficient: false },
            "det:ic" | "det-ic" | "detic"    => Param { name: "DET:IC",  open_dom: false, dom: 2, disty: 2, sharp_disty: true,  disty_dist_limit: 3, fractional: false, efficient: false },
            "err:ic" | "err-ic" | "erric"    => Param { name: "ERR:IC",  open_dom: false, dom: 3, disty: 3, sharp_disty: false, disty_dist_limit: 3, fractional: false, efficient: false },

            "f:old"     | "f-old"     | "fold"    => Param { name: "F:OLD",     open_dom: true,  dom: 1, disty: 1, sharp_disty: false, disty_dist_limit: 3, fractional: true, efficient: false },
            "f:red:old" | "f-red-old" | "fredold" => Param { name: "F:RED:OLD", open_dom: true,  dom: 2, disty: 2, sharp_disty: false, disty_dist_limit: 3, fractional: true, efficient: false },
            "f:det:old" | "f-det-old" | "fdetold" => Param { name: "F:DET:OLD", open_dom: true,  dom: 2, disty: 2, sharp_disty: true,  disty_dist_limit: 3, fractional: true, efficient: false },
            "f:err:old" | "f-err-old" | "ferrold" => Param { name: "F:ERR:OLD", open_dom: true,  dom: 3, disty: 3, sharp_disty: false, disty_dist_limit: 3, fractional: true, efficient: false },
            "f:ic"     | "f-ic"     | "fic"       => Param { name: "F:IC",      open_dom: false, dom: 1, disty: 1, sharp_disty: false, disty_dist_limit: 3, fractional: true, efficient: false },
            "f:red:ic" | "f-red-ic" | "fredic"    => Param { name: "F:RED:IC",  open_dom: false, dom: 2, disty: 2, sharp_disty: false, disty_dist_limit: 3, fractional: true, efficient: false },
            "f:det:ic" | "f-det-ic" | "fdetic"    => Param { name: "F:DET:IC",  open_dom: false, dom: 2, disty: 2, sharp_disty: true,  disty_dist_limit: 3, fractional: true, efficient: false },
            "f:err:ic" | "f-err-ic" | "ferric"    => Param { name: "F:ERR:IC",  open_dom: false, dom: 3, disty: 3, sharp_disty: false, disty_dist_limit: 3, fractional: true, efficient: false },

            "e:old"     | "e-old"     | "eold"    => Param { name: "E:OLD",     open_dom: true,  dom: 1, disty: 1, sharp_disty: false, disty_dist_limit: 3, fractional: false, efficient: true },
            "e:red:old" | "e-red-old" | "eredold" => Param { name: "E:RED:OLD", open_dom: true,  dom: 2, disty: 2, sharp_disty: false, disty_dist_limit: 3, fractional: false, efficient: true },
            "e:det:old" | "e-det-old" | "edetold" => Param { name: "E:DET:OLD", open_dom: true,  dom: 2, disty: 2, sharp_disty: true,  disty_dist_limit: 3, fractional: false, efficient: true },
            "e:err:old" | "e-err-old" | "eerrold" => Param { name: "E:ERR:OLD", open_dom: true,  dom: 3, disty: 3, sharp_disty: false, disty_dist_limit: 3, fractional: false, efficient: true },
            "e:ic"     | "e-ic"     | "eic"       => Param { name: "E:IC",      open_dom: false, dom: 1, disty: 1, sharp_disty: false, disty_dist_limit: 3, fractional: false, efficient: true },
            "e:red:ic" | "e-red-ic" | "eredic"    => Param { name: "E:RED:IC",  open_dom: false, dom: 2, disty: 2, sharp_disty: false, disty_dist_limit: 3, fractional: false, efficient: true },
            "e:det:ic" | "e-det-ic" | "edetic"    => Param { name: "E:DET:IC",  open_dom: false, dom: 2, disty: 2, sharp_disty: true,  disty_dist_limit: 3, fractional: false, efficient: true },
            "e:err:ic" | "e-err-ic" | "eerric"    => Param { name: "E:ERR:IC",  open_dom: false, dom: 3, disty: 3, sharp_disty: false, disty_dist_limit: 3, fractional: false, efficient: true },

            "ef:old"     | "ef-old"     | "efold"    => Param { name: "EF:OLD",     open_dom: true,  dom: 1, disty: 1, sharp_disty: false, disty_dist_limit: 3, fractional: true, efficient: true },
            "ef:red:old" | "ef-red-old" | "efredold" => Param { name: "EF:RED:OLD", open_dom: true,  dom: 2, disty: 2, sharp_disty: false, disty_dist_limit: 3, fractional: true, efficient: true },
            "ef:det:old" | "ef-det-old" | "efdetold" => Param { name: "EF:DET:OLD", open_dom: true,  dom: 2, disty: 2, sharp_disty: true,  disty_dist_limit: 3, fractional: true, efficient: true },
            "ef:err:old" | "ef-err-old" | "eferrold" => Param { name: "EF:ERR:OLD", open_dom: true,  dom: 3, disty: 3, sharp_disty: false, disty_dist_limit: 3, fractional: true, efficient: true },
            "ef:ic"     | "ef-ic"     | "efic"       => Param { name: "EF:IC",      open_dom: false, dom: 1, disty: 1, sharp_disty: false, disty_dist_limit: 3, fractional: true, efficient: true },
            "ef:red:ic" | "ef-red-ic" | "efredic"    => Param { name: "EF:RED:IC",  open_dom: false, dom: 2, disty: 2, sharp_disty: false, disty_dist_limit: 3, fractional: true, efficient: true },
            "ef:det:ic" | "ef-det-ic" | "efdetic"    => Param { name: "EF:DET:IC",  open_dom: false, dom: 2, disty: 2, sharp_disty: true,  disty_dist_limit: 3, fractional: true, efficient: true },
            "ef:err:ic" | "ef-err-ic" | "eferric"    => Param { name: "EF:ERR:IC",  open_dom: false, dom: 3, disty: 3, sharp_disty: false, disty_dist_limit: 3, fractional: true, efficient: true },

            _ => return Err(format!("unknown param type: '{}'", s)),
        })
    }
}

fn test_graph(graph: &Graph, param: &Param, exhaustive: bool, log: bool) -> Vec<BTreeMap<usize, Rational64>> {
    let n = graph.verts.len();
    let adj = |p: usize| graph.verts[p].1.iter().copied().collect();
    let distances = Distances::within_shape(&(0..n).collect(), &adj);

    let context = Context::new(&Default::default());
    let verts: Vec<Real> = (0..n).map(|p| Real::new_const(&context, format!("v{p}"))).collect();

    let zero = Real::from_real(&context, 0, 1);
    let one = Real::from_real(&context, 1, 1);

    let s = Optimize::new(&context);
    s.minimize(&sum(&context, verts.iter()));
    if param.fractional {
        s.minimize(&count(&context, verts.iter().map(|x| x.gt(&zero))));
    }

    for (i, v) in verts.iter().enumerate() {
        match param.fractional {
            true => s.assert(&(v.ge(&zero) & v.le(&one))),
            false => {
                let flag = Bool::new_const(&context, format!("v{i}f")); // vastly faster than (v == 0 || v == 1)
                s.assert(&v._eq(&flag.ite(&one, &zero)));
            }
        }
    }

    let count_det = |points: &BTreeSet<usize>| -> Real {
        sum(&context, points.iter().copied().map(|p| &verts[p]))
    };

    for p in 0..n {
        if let Some(req) = param.check_dom(&context, (p, &verts[p]), &adj, &|group| count_det(group)) {
            s.assert(&req);
        }
    }
    for pq in (0..n).combinations(2) {
        let (p, q) = (pq[0], pq[1]);
        if let Some(req) = param.check_disty(&context, (p, &verts[p]), (q, &verts[q]), &adj, &distances, &|group| count_det(group)) {
            s.assert(&req);
        }
    }

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
        match s.check(&[]) {
            SatResult::Sat => {
                let model = s.get_model().unwrap();
                let detectors: BTreeMap<usize, Rational64> = verts.iter().map(|v| model.eval(v, false).unwrap().as_real().unwrap()).map(|(p, q)| Rational64::new(p, q)).enumerate().collect();
                let value = detectors.iter().map(|x| x.1).sum::<Rational64>();

                match &minimum_value {
                    None => minimum_value = Some(value),
                    Some(min) => {
                        assert!(*min <= value);
                        if *min < value { break }
                    }
                }

                let mut different_answer = Bool::from_bool(&context, false);
                for (i, v) in verts.iter().enumerate() {
                    let value = detectors.get(&i).copied().unwrap();
                    different_answer |= v._eq(&Real::from_real(&context, *value.numer() as i32, *value.denom() as i32)).not();
                }
                s.assert(&different_answer);

                if log {
                    println!("solution {}: {}", solutions.len() + 1, solution_string(graph, detectors.iter().map(|x| (*x.0, *x.1))));
                }

                solutions.push(detectors);
                if !exhaustive { break }
            }
            SatResult::Unsat => break,
            SatResult::Unknown => unreachable!(),
        }
    }

    if log {
        match &minimum_value {
            Some(value) => match exhaustive {
                false => println!("\nfound a minimum solution of size {}", Verbose(value)),
                true => {
                    println!("\nexhausted all {} minimum solutions of size {}\n", solutions.len(), Verbose(value));

                    let mut always_detectors = vec![true; n];
                    let mut never_detectors = vec![true; n];
                    for solution in solutions.iter() {
                        for i in 0..n {
                            let is_detector = solution.contains_key(&i);
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

    let context = Context::new(&Default::default());
    let verts: BTreeMap<(i32, i32), Real> = shape.iter().copied().map(|p| (p, Real::new_const(&context, format!("v{},{}", p.0, p.1)))).collect();
    let tiling_index = Int::new_const(&context, "tidx");

    let zero = Real::from_real(&context, 0, 1);
    let one = Real::from_real(&context, 1, 1);

    let s = Optimize::new(&context);
    s.minimize(&sum(&context, verts.values()));
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
        sum(&context, points.iter().map(|p| &verts[&tiling[p]]))
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

#[derive(Default, Debug)]
struct Graph {
    verts: Vec<(String, Vec<usize>)>,
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

        Ok(Graph { verts: verts.into_iter().map(|(name, adj)| (name, adj.into_iter().collect())).collect() })
    }
    fn by_adj<T, N, A>(points: &[T], namer: N, is_adj: A) -> Self where N: Fn(&T) -> String, A: Fn(&T, &T) -> bool {
        let mut verts = Vec::with_capacity(points.len());
        for (i, v) in points.iter().enumerate() {
            let mut v_adj = vec![];
            for (j, u) in points.iter().enumerate() {
                if i == j { continue }
                let adj = is_adj(v, u);
                debug_assert_eq!(adj, is_adj(u, v));
                if adj { v_adj.push(j); }
            }
            verts.push((namer(v), v_adj));
        }
        Self { verts }
    }
    fn hypercube(dims: usize) -> Self {
        assert!(dims <= 30); // anything this big is unrealistic anyway
        let verts: Vec<usize> = (0..(1 << dims)).collect();
        Self::by_adj(&verts, |&x| format!("{x:b}"), |&a, &b| (a ^ b).is_power_of_two())
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
    /// Minimum value for a finite graph.
    Finite {
        /// Path to a file containing the finite graph encoded as a sequence of whitespace-separated u:v edges.
        /// Or "-" to read from stdin.
        src: String,
        /// The graph parameter to check; e.g., old, ic, red:old, red:ic, etc.
        param: Param,

        /// Generate all minimum-valued solutions.
        #[clap(short, long)]
        all: bool,
    },
}

fn main() {
    match Mode::parse() {
        Mode::Rect { rows, cols, grid, param } => {
            let shape = rect(rows.get(), cols.get());
            println!("checking {} {}\n", param.name, grid.name);
            print_result(&shape, &test_tiling(&shape, &grid, &param, true))
        }
        Mode::Finite { src, param, all } => {
            let graph = match src.as_str() {
                "-" => Graph::read(&mut BufReader::new(io::stdin())).unwrap(),
                x => {
                    let special = {
                        if !x.is_empty() && x.chars().next().unwrap().to_ascii_uppercase() == 'Q' {
                            if let Ok(n) = x[1..].parse() { Some(Graph::hypercube(n)) } else { None }
                        } else {
                            None
                        }
                    };
                    match special {
                        Some(x) => x,
                        None => Graph::read(&mut BufReader::new(File::open(x).unwrap())).unwrap(),
                    }
                }
            };

            println!("checking {}\nG = {}\nn = {}\ne = {}\n", param.name, graph, graph.verts.len(), graph.verts.iter().map(|x| x.1.len()).sum::<usize>() / 2);
            test_graph(&graph, &param, all, true);
        }
    }
}
