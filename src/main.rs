use std::collections::{BTreeSet, BTreeMap};
use std::str::FromStr;
use std::num::NonZeroUsize;
use std::io::{self, BufRead, BufReader};
use std::fs::File;

use itertools::Itertools;
use clap::Parser;

use z3::{Context, Optimize, SatResult};
use z3::ast::{Bool, Int, Ast};

trait Point: Copy + Ord {}
type Adj<'a, P> = dyn 'a + Fn(P) -> BTreeSet<P>;

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

fn dom_set<P: Point>(p: P, adj: &Adj<P>, open_dom: bool) -> BTreeSet<P> {
    let mut res = adj(p);
    if !open_dom { assert!(res.insert(p)); }
    else { assert!(!res.contains(&p)); }
    res
}
fn disty_set<P: Point>(p: P, q: P, adj: &Adj<P>, open_dom: bool) -> BTreeSet<P> {
    let dom_sets = (dom_set(p, adj, open_dom), dom_set(q, adj, open_dom));
    dom_sets.0.symmetric_difference(&dom_sets.1).copied().collect()
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

fn count<'ctx, 'a, I>(context: &'ctx Context, iter: I) -> Int<'ctx> where 'ctx: 'a, I: Iterator<Item = &'a Bool<'ctx>> {
    let (zero, one) = (Int::from_u64(context, 0), Int::from_u64(context, 1));
    let mut res = zero.clone();
    for v in iter {
        res += v.ite(&one, &zero);
    }
    res
}
fn count_det<'ctx>(context: &'ctx Context, verts: &[Bool<'ctx>], points: &BTreeSet<usize>) -> Int<'ctx> {
    count(context, points.iter().copied().map(|p| &verts[p]))
}
fn count_det_tiling<'ctx>(context: &'ctx Context, verts: &BTreeMap<(i32, i32), Bool<'ctx>>, points: &BTreeSet<(i32, i32)>, tiling: &BTreeMap<(i32, i32), (i32, i32)>) -> Int<'ctx> {
    count(context, points.iter().map(|p| &verts[&tiling[p]]))
}

struct Grid {
    name: &'static str,
    adj: &'static Adj<'static, (i32, i32)>,
}
impl FromStr for Grid {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, String> {
        Ok(match s.trim().to_lowercase().as_str() {
            "k" | "king" => Grid { name: "K", adj: &adj_k },
            "sq" | "square" => Grid { name: "SQ", adj: &adj_sq },
            "tri" => Grid { name: "TRI", adj: &adj_tri },
            "hex" => Grid { name: "HEX", adj: &adj_hex },
            _ => return Err(format!("unknown grid type: '{}'", s)),
        })
    }
}

struct Param {
    name: &'static str,
    open_dom: bool,
    dom: usize,
    disty: usize,
    disty_dist_limit: usize,
}
impl FromStr for Param {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s.trim().to_lowercase().as_str() {
            "old" => Param { name: "OLD", open_dom: true, dom: 1, disty: 1, disty_dist_limit: 3 },
            "red:old" | "red-old" | "redold" => Param { name: "RED:OLD", open_dom: true, dom: 2, disty: 2, disty_dist_limit: 3 },
            "err:old" | "err-old" | "errold" => Param { name: "ERR:OLD", open_dom: true, dom: 3, disty: 3, disty_dist_limit: 3 },
            "ic" => Param { name: "IC", open_dom: false, dom: 1, disty: 1, disty_dist_limit: 3 },
            "red:ic" | "red-ic" | "redic" => Param { name: "RED:IC", open_dom: false, dom: 2, disty: 2, disty_dist_limit: 3 },
            "err:ic" | "err-ic" | "erric" => Param { name: "ERR:IC", open_dom: false, dom: 3, disty: 3, disty_dist_limit: 3 },
            _ => return Err(format!("unknown param type: '{}'", s)),
        })
    }
}

#[derive(Parser)]
enum Mode {
    Rect {
        rows: NonZeroUsize,
        cols: NonZeroUsize,
        param: Param,
        grid: Grid,
    },
    Finite {
        src: String,
        param: Param,

        #[clap(short, long)]
        all: bool,
        #[clap(short, long, default_value_t = 1)]
        max_solutions: usize,
    },
}

fn test_graph(graph: &Graph, param: &Param, max_solutions: usize, log: bool) -> Vec<Vec<usize>> {
    let n = graph.verts.len();
    let adj = |p: usize| graph.verts[p].1.iter().copied().collect();
    let distances = Distances::within_shape(&(0..n).collect(), &adj);

    let context = Context::new(&Default::default());
    let verts: Vec<Bool> = (0..n).map(|p| Bool::new_const(&context, format!("v{p}"))).collect();
    let dom_int = Int::from_u64(&context, param.dom as u64);
    let disty_int = Int::from_u64(&context, param.disty as u64);

    let s = Optimize::new(&context);
    let detector_count = count(&context, verts.iter());
    s.minimize(&detector_count);

    for p in 0..n {
        s.assert(&count_det(&context, &verts, &dom_set(p, &adj, param.open_dom)).ge(&dom_int));
    }
    for pq in (0..n).combinations(2) {
        let (p, q) = (pq[0], pq[1]);
        if distances.get(p, q) < param.disty_dist_limit {
            s.assert(&count_det(&context, &verts, &disty_set(p, q, &adj, param.open_dom)).ge(&disty_int));
        }
    }

    let mut solutions = vec![];
    while solutions.len() < max_solutions {
        match s.check(&[]) {
            SatResult::Sat => {
                let model = s.get_model().unwrap();
                let detectors: BTreeSet<usize> = verts.iter().enumerate().filter(|(_, v)| model.eval(*v, false).unwrap().as_bool().unwrap()).map(|(p, _)| p).collect();

                let prev_size = solutions.first().map(|s: &Vec<usize>| s.len()).unwrap_or(detectors.len());
                assert!(prev_size <= detectors.len());
                if prev_size < detectors.len() { break }

                let mut different_answer = Bool::from_bool(&context, false);
                for (i, v) in verts.iter().enumerate() {
                    different_answer |= v._eq(&Bool::from_bool(&context, detectors.contains(&i))).not();
                }
                s.assert(&different_answer);

                if log {
                    let mut det_names: Vec<_> = detectors.iter().map(|&p| &graph.verts[p].0).collect();
                    det_names.sort();
                    println!("found solution ({}): {det_names:?}", detectors.len());
                }

                solutions.push(detectors.into_iter().collect());
            }
            SatResult::Unsat => break,
            SatResult::Unknown => unreachable!(),
        }
    }
    solutions
}
fn test_shape(shape: &BTreeSet<(i32, i32)>, grid: &Grid, param: &Param, log: bool) -> Option<(BTreeSet<(i32, i32)>, (i32, i32), (i32, i32), usize)> {
    if log {
        println!("tile shape:");
        print_shape(&shape, &Default::default());
    }

    let inflated = inflate(&shape, grid.adj, 2);
    let interior = get_interior(&shape, grid.adj);
    let identity_map = shape.iter().copied().map(|p| (p, p)).collect();
    let distances = Distances::within_shape(&inflated, grid.adj);
    let tilings = get_tilings(&shape);

    if log {
        println!("\nfound {} tilings...", tilings.len());
    }

    let context = Context::new(&Default::default());
    let verts: BTreeMap<(i32, i32), Bool> = shape.iter().copied().map(|p| (p, Bool::new_const(&context, format!("v{},{}", p.0, p.1)))).collect();
    let tiling_index = Int::new_const(&context, "tidx");
    let dom_int = Int::from_u64(&context, param.dom as u64);
    let disty_int = Int::from_u64(&context, param.disty as u64);

    let s = Optimize::new(&context);
    let detector_count = count(&context, verts.values());
    s.minimize(&detector_count);

    for p in interior.iter().copied() {
        s.assert(&count_det_tiling(&context, &verts, &dom_set(p, grid.adj, param.open_dom), &identity_map).ge(&dom_int));
    }
    for pq in interior.iter().copied().combinations(2) {
        let (p, q) = (pq[0], pq[1]);
        if distances.get(p, q) < param.disty_dist_limit {
            s.assert(&count_det_tiling(&context, &verts, &disty_set(p, q, grid.adj, param.open_dom), &identity_map).ge(&disty_int));
        }
    }

    let mut any_solution = Bool::from_bool(&context, false);
    for (i, (tiling, _, _)) in tilings.iter().enumerate() {
        let mut solution = Bool::from_bool(&context, true);
        for p in inflated.iter().copied() {
            if !interior.contains(&p) {
                solution &= count_det_tiling(&context, &verts, &dom_set(p, &grid.adj, param.open_dom), tiling).ge(&dom_int);
            }
        }
        for pq in inflated.iter().copied().combinations(2) {
            let (p, q) = (pq[0], pq[1]);
            if (!interior.contains(&p) || !interior.contains(&q)) && distances.get(p, q) < param.disty_dist_limit {
                solution &= count_det_tiling(&context, &verts, &disty_set(p, q, grid.adj, param.open_dom), tiling).ge(&disty_int);
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
            println!("\n{}/{} = {}", detectors.len(), shape.len(), detectors.len() as f64 / shape.len() as f64);
            println!("basis: {:?} {:?} (tiling index {})", b1, b2, tidx);
        }
        None => println!("no solution"),
    }
}

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
}

fn main() {
    match Mode::parse() {
        Mode::Rect { rows, cols, grid, param } => {
            let shape = rect(rows.get(), cols.get());
            println!("checking {} {}\n", param.name, grid.name);
            print_result(&shape, &test_shape(&shape, &grid, &param, true))
        }
        Mode::Finite { src, param, all, max_solutions } => {
            let graph = if src == "-" {
                Graph::read(&mut BufReader::new(io::stdin().lock())).unwrap()
            } else {
                Graph::read(&mut BufReader::new(File::open(src).unwrap())).unwrap()
            };
            test_graph(&graph, &param, if all { usize::MAX } else { max_solutions }, true);
        }
    }
}
