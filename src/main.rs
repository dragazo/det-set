use std::collections::{BTreeSet, BTreeMap};
use std::str::FromStr;
use std::num::NonZeroUsize;

use itertools::Itertools;
use clap::Parser;

use z3::{Context, Optimize, SatResult};
use z3::ast::{Bool, Int, Ast};

type Point = (i32, i32);
type Points = BTreeSet<Point>;
type PointMap<T> = BTreeMap<Point, T>;
type Adj = fn(Point) -> Points;

fn adj_k(p: Point) -> Points {
    [
        (p.0 - 1, p.1 - 1), (p.0 - 1, p.1), (p.0 - 1, p.1 + 1),
        (p.0,     p.1 - 1),                 (p.0,     p.1 + 1),
        (p.0 + 1, p.1 - 1), (p.0 + 1, p.1), (p.0 + 1, p.1 + 1),
    ].into_iter().collect()
}
fn adj_sq(p: Point) -> Points {
    [(p.0 - 1, p.1), (p.0, p.1 - 1), (p.0, p.1 + 1), (p.0 + 1, p.1)].into_iter().collect()
}
fn adj_tri(p: Point) -> Points {
    [(p.0 - 1, p.1 - 1), (p.0 - 1, p.1), (p.0, p.1 - 1), (p.0, p.1 + 1), (p.0 + 1, p.1), (p.0 + 1, p.1 + 1)].into_iter().collect()
}
fn adj_hex(p: Point) -> Points {
    if (p.0 + p.1) % 2 == 0 {
        [(p.0 - 1, p.1), (p.0, p.1 - 1), (p.0, p.1 + 1)].into_iter().collect()
    } else {
        [(p.0 + 1, p.1), (p.0, p.1 - 1), (p.0, p.1 + 1)].into_iter().collect()
    }
}

fn dom_set(p: Point, adj: Adj, open_dom: bool) -> Points {
    let mut res = adj(p);
    if !open_dom { assert!(res.insert(p)); }
    else { assert!(!res.contains(&p)); }
    res
}
fn disty_set(p: Point, q: Point, adj: Adj, open_dom: bool) -> Points {
    let dom_sets = (dom_set(p, adj, open_dom), dom_set(q, adj, open_dom));
    dom_sets.0.symmetric_difference(&dom_sets.1).copied().collect()
}

fn rect(rows: usize, cols: usize) -> Points {
    let mut res = Points::new();
    for r in 0..rows as i32 {
        for c in 0..cols as i32 {
            res.insert((r, c));
        }
    }
    res
}

fn print_shape(shape: &BTreeSet<Point>, detectors: &BTreeSet<Point>) {
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

fn inflate(shape: &Points, adj: Adj, radius: usize) -> Points {
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
fn get_interior(shape: &Points, adj: Adj) -> Points {
    shape.iter().copied().filter(|u| adj(*u).into_iter().all(|v| shape.contains(&v))).collect()
}

fn get_size(shape: &Points) -> (usize, usize) {
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

const TILE_RADIUS: i32 = 3;
fn get_tilings(shape: &Points) -> Vec<(PointMap<Point>, (i32, i32), (i32, i32))> {
    let inflated = inflate(shape, adj_k, 3);
    let size = get_size(shape);
    let mut tilings: BTreeMap<PointMap<Point>, ((i32, i32), (i32, i32))> = Default::default();
    for dr1 in 0..=2*size.0 as i32 {
        for dc1 in 0..=2*size.1 as i32 {
            for dr2 in 0..=2*size.0 as i32 {
                'skip: for dc2 in 0..=2*size.1 as i32 {
                    let (b1, b2) = ((dr1, dc1), (dr2, dc2));
                    let mut res: PointMap<Point> = Default::default();
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

struct Distances(BTreeMap<(Point, Point), usize>);
impl Distances {
    fn new(shape: &Points, adj: Adj) -> Self {
        let mut res = BTreeMap::default();
        for points in shape.iter().combinations_with_replacement(2) {
            let (p, q) = (*points[0], *points[1]);
            let mut region = Points::new();
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
    fn get(&self, p: Point, q: Point) -> usize {
        self.0[&(p, q)]
    }
}

fn count<'ctx, 'a, I>(context: &'ctx Context, iter: I) -> Int<'ctx> where 'ctx: 'a, I: Iterator<Item = &'a Bool<'ctx>> {
    let (zero, one) = (Int::from_u64(context, 0), Int::from_u64(context, 1));
    let mut res = zero.clone();
    for v in iter {
        res += v.ite(&one, &zero);
    }
    res
}
fn count_detectors<'ctx>(context: &'ctx Context, verts: &PointMap<Bool<'ctx>>, points: &Points, tiling: &PointMap<Point>) -> Int<'ctx> {
    count(context, points.iter().map(|p| &verts[&tiling[p]]))
}

struct Grid {
    name: &'static str,
    adj: Adj,
}
impl FromStr for Grid {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, String> {
        Ok(match s.trim().to_lowercase().as_str() {
            "k" | "king" => Grid { name: "K", adj: adj_k },
            "sq" | "square" => Grid { name: "SQ", adj: adj_sq },
            "tri" => Grid { name: "TRI", adj: adj_tri },
            "hex" => Grid { name: "HEX", adj: adj_hex },
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
    }
}

fn test_shape(shape: &Points, grid: &Grid, param: &Param, log: bool) -> Option<(Points, (i32, i32), (i32, i32), usize)> {
    if log {
        println!("tile shape:");
        print_shape(&shape, &Default::default());
    }

    let inflated = inflate(&shape, grid.adj, 2);
    let interior = get_interior(&shape, grid.adj);
    let identity_map = shape.iter().copied().map(|p| (p, p)).collect();
    let distances = Distances::new(&inflated, grid.adj);
    let tilings = get_tilings(&shape);

    if log {
        println!("\nfound {} tilings...", tilings.len());
    }

    let context = Context::new(&Default::default());
    let verts: PointMap<Bool> = shape.iter().copied().map(|p| (p, Bool::new_const(&context, format!("v{},{}", p.0, p.1)))).collect();
    let tiling_index = Int::new_const(&context, "tidx");
    let dom_int = Int::from_u64(&context, param.dom as u64);
    let disty_int = Int::from_u64(&context, param.disty as u64);

    let s = Optimize::new(&context);
    let detector_count = count(&context, verts.values());
    s.minimize(&detector_count);

    for p in interior.iter().copied() {
        s.assert(&count_detectors(&context, &verts, &dom_set(p, grid.adj, param.open_dom), &identity_map).ge(&dom_int));
    }
    for pq in interior.iter().copied().combinations(2) {
        let (p, q) = (pq[0], pq[1]);
        if distances.get(p, q) < param.disty_dist_limit {
            s.assert(&count_detectors(&context, &verts, &disty_set(p, q, grid.adj, param.open_dom), &identity_map).ge(&disty_int));
        }
    }

    let mut any_solution = Bool::from_bool(&context, false);
    for (i, (tiling, _, _)) in tilings.iter().enumerate() {
        let mut solution = Bool::from_bool(&context, true);
        for p in inflated.iter().copied() {
            if !interior.contains(&p) {
                solution &= count_detectors(&context, &verts, &dom_set(p, grid.adj, param.open_dom), tiling).ge(&dom_int);
            }
        }
        for pq in inflated.iter().copied().combinations(2) {
            let (p, q) = (pq[0], pq[1]);
            if (!interior.contains(&p) || !interior.contains(&q)) && distances.get(p, q) < param.disty_dist_limit {
                solution &= count_detectors(&context, &verts, &disty_set(p, q, grid.adj, param.open_dom), tiling).ge(&disty_int);
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
            let detectors: Points = verts.iter().filter(|(_, v)| model.eval(*v, false).unwrap().as_bool().unwrap()).map(|(p, _)| *p).collect();
            let tidx = model.eval(&tiling_index, false).unwrap().as_u64().unwrap() as usize;
            Some((detectors, tilings[tidx].1, tilings[tidx].2, tidx))
        }
        SatResult::Unsat => None,
        SatResult::Unknown => unreachable!(),
    }
}
fn print_result(shape: &Points, res: &Option<(Points, (i32, i32), (i32, i32), usize)>) {
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

fn main() {
    match Mode::parse() {
        Mode::Rect { rows, cols, grid, param } => {
            let shape = rect(rows.get(), cols.get());
            println!("checking {} {}\n", param.name, grid.name);
            print_result(&shape, &test_shape(&shape, &grid, &param, true))
        }
    }
}
