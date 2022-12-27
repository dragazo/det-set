use std::collections::{BTreeSet, BTreeMap};
use std::str::FromStr;
use std::num::NonZeroUsize;
use std::io::{self, BufRead, BufReader};
use std::cmp::Ordering;
use std::fs::File;
use std::{iter, fmt};

use itertools::Itertools;
use clap::Parser;

use z3::{Context, Optimize, SatResult};
use z3::ast::{Bool, Int, Ast};

type Adj<'a, P> = dyn 'a + Fn(P) -> BTreeSet<P>;
type Counter<'ctx, P> = dyn 'ctx + Fn(&BTreeSet<P>) -> Int<'ctx>;

trait Point: Copy + Ord {}
impl Point for (i32, i32) {}
impl Point for usize {}

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
fn print_shape(shape: &BTreeSet<(i32, i32)>, detectors: &BTreeSet<(i32, i32)>) {
    let (mut row, mut col) = (0, 0);
    for (r, c) in shape.iter().copied() {
        if r != row {
            println!();
            (row, col) = (r, 0);
        }
        for _ in 0..(c - col) {
            print!("{}", ' ');
        }
        print!("{}", if detectors.contains(&(r, c)) { '1' } else { '0' });
        col = c;
    }
    println!();
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

fn max<'ctx>(a: &Int<'ctx>, b: &Int<'ctx>) -> Int<'ctx> {
    a.ge(b).ite(a, b)
}
fn count<'ctx, 'a, I>(context: &'ctx Context, iter: I) -> Int<'ctx> where 'ctx: 'a, I: Iterator<Item = &'a Bool<'ctx>> {
    let (zero, one) = (Int::from_u64(context, 0), Int::from_u64(context, 1));
    let mut res = zero.clone();
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
}
impl Param {
    fn dom_region<P: Point>(&self, p: P, adj: &Adj<P>) -> BTreeSet<P> {
        let mut res = adj(p);
        if !self.open_dom { assert!(res.insert(p)); }
        else { assert!(!res.contains(&p)); }
        res
    }
    fn check_dom<'ctx, P: Point>(&self, context: &'ctx Context, p: (P, &Bool<'ctx>), adj: &Adj<P>, counter: &Counter<'ctx, P>) -> Option<Bool<'ctx>> {
        if self.dom == 0 { return None }
        Some(counter(&self.dom_region(p.0, adj)).ge(&Int::from_u64(context, self.dom as u64)))
    }
    fn check_disty<'ctx, P: Point>(&self, context: &'ctx Context, p: (P, &Bool<'ctx>), q: (P, &Bool<'ctx>), adj: &Adj<P>, distances: &Distances<P>, counter: &Counter<'ctx, P>) -> Option<Bool<'ctx>> {
        if self.disty == 0 || distances.get(p.0, q.0) >= self.disty_dist_limit { return None }
        let regions = (self.dom_region(p.0, adj), self.dom_region(q.0, adj));
        Some(match self.sharp_disty {
            false => counter(&regions.0.symmetric_difference(&regions.1).copied().collect()).ge(&Int::from_u64(context, self.disty as u64)),
            true => max(&counter(&(&regions.0 - &regions.1)), &counter(&(&regions.1 - &regions.0))).ge(&Int::from_u64(context, self.disty as u64)),
        })
    }
}
impl FromStr for Param {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s.trim().to_lowercase().as_str() {
            "old"                            => Param { name: "OLD",     open_dom: true,  dom: 1, disty: 1, sharp_disty: false, disty_dist_limit: 3 },
            "red:old" | "red-old" | "redold" => Param { name: "RED:OLD", open_dom: true,  dom: 2, disty: 2, sharp_disty: false, disty_dist_limit: 3 },
            "det:old" | "det-old" | "detold" => Param { name: "DET:OLD", open_dom: true,  dom: 2, disty: 2, sharp_disty: true,  disty_dist_limit: 3 },
            "err:old" | "err-old" | "errold" => Param { name: "ERR:OLD", open_dom: true,  dom: 3, disty: 3, sharp_disty: false, disty_dist_limit: 3 },
            "ic"                             => Param { name: "IC",      open_dom: false, dom: 1, disty: 1, sharp_disty: false, disty_dist_limit: 3 },
            "red:ic" | "red-ic" | "redic"    => Param { name: "RED:IC",  open_dom: false, dom: 2, disty: 2, sharp_disty: false, disty_dist_limit: 3 },
            "det:ic" | "det-ic" | "detic"    => Param { name: "DET:IC",  open_dom: false, dom: 2, disty: 2, sharp_disty: true,  disty_dist_limit: 3 },
            "err:ic" | "err-ic" | "erric"    => Param { name: "ERR:IC",  open_dom: false, dom: 3, disty: 3, sharp_disty: false, disty_dist_limit: 3 },
            _ => return Err(format!("unknown param type: '{}'", s)),
        })
    }
}

fn gcd(mut a: usize, mut b: usize) -> usize {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}
#[test]
fn test_gcd() {
    assert_eq!(gcd(6, 16), 2); assert_eq!(gcd(16, 6), 2);
    assert_eq!(gcd(8, 16), 8); assert_eq!(gcd(16, 8), 8);
    assert_eq!(gcd(64, 16), 16); assert_eq!(gcd(16, 64), 16);
    assert_eq!(gcd(1071, 462), 21); assert_eq!(gcd(462, 1071), 21);
}

fn test_graph(graph: &Graph, param: &Param, exhaustive: bool, log: bool) -> Vec<BTreeSet<usize>> {
    let n = graph.verts.len();
    let adj = |p: usize| graph.verts[p].1.iter().copied().collect();
    let distances = Distances::within_shape(&(0..n).collect(), &adj);

    let context = Context::new(&Default::default());
    let verts: Vec<Bool> = (0..n).map(|p| Bool::new_const(&context, format!("v{p}"))).collect();

    let s = Optimize::new(&context);
    let detector_count = count(&context, verts.iter());
    s.minimize(&detector_count);

    let count_det = |points: &BTreeSet<usize>| -> Int {
        count(&context, points.iter().copied().map(|p| &verts[p]))
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

    fn solution_string<I: Iterator<Item = usize>>(graph: &Graph, verts: I) -> String {
        let mut names: Vec<_> = verts.map(|v| graph.verts[v].0.as_str()).collect();
        numeric_sort::sort(&mut names);
        let mut res = String::new();
        res.push('{');
        for name in names {
            res.push(' ');
            res.push_str(name);
        }
        res.push_str(" }");
        res
    }

    let mut solutions: Vec<BTreeSet<usize>> = vec![];
    loop {
        match s.check(&[]) {
            SatResult::Sat => {
                let model = s.get_model().unwrap();
                let detectors: BTreeSet<usize> = verts.iter().enumerate().filter(|(_, v)| model.eval(*v, false).unwrap().as_bool().unwrap()).map(|(p, _)| p).collect();

                let prev_size = solutions.first().map(|s| s.len()).unwrap_or(detectors.len());
                assert!(prev_size <= detectors.len());
                if prev_size < detectors.len() { break }

                let mut different_answer = Bool::from_bool(&context, false);
                for (i, v) in verts.iter().enumerate() {
                    different_answer |= v._eq(&Bool::from_bool(&context, detectors.contains(&i))).not();
                }
                s.assert(&different_answer);

                if log {
                    println!("solution {}: {}", solutions.len() + 1, solution_string(graph, detectors.iter().copied()));
                }

                solutions.push(detectors);
                if !exhaustive { break }
            }
            SatResult::Unsat => break,
            SatResult::Unknown => unreachable!(),
        }
    }

    if log {
        match solutions.first() {
            Some(solution) => match exhaustive {
                false => println!("\nfound a minimum solution of size {}", solution.len()),
                true => {
                    println!("\nexhausted all {} minimum solutions of size {}\n", solutions.len(), solution.len());

                    let mut always_detectors = vec![true; n];
                    let mut never_detectors = vec![true; n];
                    for solution in solutions.iter() {
                        for i in 0..n {
                            let is_detector = solution.contains(&i);
                            if is_detector { never_detectors[i] = false; }
                            else { always_detectors[i] = false; }
                        }
                    }
                    let sometimes_detectors: Vec<_> = iter::zip(&always_detectors, &never_detectors).map(|(a, b)| !a && !b).collect();

                    println!("always    detectors: {}", solution_string(graph,    always_detectors.iter().enumerate().filter(|x| *x.1).map(|x| x.0)));
                    println!("never     detectors: {}", solution_string(graph,     never_detectors.iter().enumerate().filter(|x| *x.1).map(|x| x.0)));
                    println!("sometimes detectors: {}", solution_string(graph, sometimes_detectors.iter().enumerate().filter(|x| *x.1).map(|x| x.0)));
                }
            }
            None => println!("no solution"),
        }
    }

    solutions
}
fn test_tiling(shape: &BTreeSet<(i32, i32)>, grid: &Grid, param: &Param, log: bool) -> Option<(BTreeSet<(i32, i32)>, (i32, i32), (i32, i32), usize)> {
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
    let verts: BTreeMap<(i32, i32), Bool> = shape.iter().copied().map(|p| (p, Bool::new_const(&context, format!("v{},{}", p.0, p.1)))).collect();
    let tiling_index = Int::new_const(&context, "tidx");

    let s = Optimize::new(&context);
    let detector_count = count(&context, verts.values());
    s.minimize(&detector_count);

    let count_det = |points: &BTreeSet<(i32, i32)>, tiling: &BTreeMap<(i32, i32), (i32, i32)>| -> Int {
        count(&context, points.iter().map(|p| &verts[&tiling[p]]))
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
    s.assert(verts.iter().next().unwrap().1); // arbitrarily place the first detector at some vertex

    if log {
        println!("checking {} tilings...\n", tilings.len());
    }

    match s.check(&[]) {
        SatResult::Sat => {
            let model = s.get_model().unwrap();
            let detectors = verts.iter().filter(|(_, v)| model.eval(*v, false).unwrap().as_bool().unwrap()).map(|(p, _)| *p).collect();
            let tidx = model.eval(&tiling_index, false).unwrap().as_u64().unwrap() as usize;
            Some((detectors, tilings[tidx].1, tilings[tidx].2, tidx))
        }
        SatResult::Unsat => None,
        SatResult::Unknown => unreachable!(),
    }
}
fn print_result(shape: &BTreeSet<(i32, i32)>, res: &Option<(BTreeSet<(i32, i32)>, (i32, i32), (i32, i32), usize)>) {
    match res {
        Some((detectors, b1, b2, tidx)) => {
            println!("found minimum:");
            print_shape(&shape, detectors);
            let m = gcd(detectors.len(), shape.len());
            let (n, d) = (detectors.len() / m, shape.len() / m);
            println!("\n{}/{} = {}", n, d, n as f64 / d as f64);
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
