//! Exact product-block checker, any base g: a compiled port of
//! `experiments/mahler_product_block.py` (same algorithm, same verdicts; the Python file is the
//! reference and carries the math).  States are plain indices: the product state (v, s) of a
//! core node v and a carry s of the new channel is `v * m + s`.
//!
//! Channel (m, d): carry s in [0, m), label x (a digit of the irrational), next carry s2 with
//! m*x + s2 = g*s + r, emitted digit r != d.  CORE = nodes in an SCC with an internal edge;
//! COLLAPSE = every core SCC is a simple cycle (edges == vertices).
//!
//! Usage:
//!   mahler_block failing G m1,m2,... [--nosym] [--limit N]   count failing assignments
//!   mahler_block greedy G seed1,... SMALL_MAX BIG_LIST SAMPLE  greedy block search
//!       BIG_LIST: comma list of large candidate multipliers (e.g. Liouville-filter picks)

use rayon::prelude::*;
use std::env;

type Adj = Vec<Vec<(u8, u32)>>; // per node: (label, target)

fn root(g: u32) -> Adj {
    vec![(0..g).map(|x| (x as u8, 0u32)).collect()]
}

/// Tarjan SCC (iterative).  Returns comp id per node and component count.
fn scc(adj: &Adj) -> (Vec<u32>, usize) {
    let n = adj.len();
    const UNSEEN: u32 = u32::MAX;
    let mut idx = vec![UNSEEN; n];
    let mut low = vec![0u32; n];
    let mut onst = vec![false; n];
    let mut st: Vec<u32> = Vec::new();
    let mut comp = vec![UNSEEN; n];
    let mut counter = 0u32;
    let mut ncomp = 0usize;
    let mut work: Vec<(u32, usize)> = Vec::new();
    for r in 0..n {
        if idx[r] != UNSEEN {
            continue;
        }
        idx[r] = counter;
        low[r] = counter;
        counter += 1;
        st.push(r as u32);
        onst[r] = true;
        work.push((r as u32, 0));
        while let Some(&mut (v, ref mut i)) = work.last_mut() {
            let vu = v as usize;
            if *i < adj[vu].len() {
                let w = adj[vu][*i].1 as usize;
                *i += 1;
                if idx[w] == UNSEEN {
                    idx[w] = counter;
                    low[w] = counter;
                    counter += 1;
                    st.push(w as u32);
                    onst[w] = true;
                    work.push((w as u32, 0));
                } else if onst[w] {
                    low[vu] = low[vu].min(idx[w]);
                }
            } else {
                work.pop();
                if let Some(&(u, _)) = work.last() {
                    let uu = u as usize;
                    low[uu] = low[uu].min(low[vu]);
                }
                if low[vu] == idx[vu] {
                    loop {
                        let w = st.pop().unwrap() as usize;
                        onst[w] = false;
                        comp[w] = ncomp as u32;
                        if w == vu {
                            break;
                        }
                    }
                    ncomp += 1;
                }
            }
        }
    }
    (comp, ncomp)
}

/// Refine `core` by channel (m, d).  Returns (new core, collapsed).
fn refine(g: u32, core: &Adj, m: u32, d: u32) -> (Adj, bool) {
    let n = core.len();
    let mu = m as usize;
    let mut nadj: Adj = vec![Vec::new(); n * mu];
    for v in 0..n {
        for s in 0..m {
            let lst = &mut nadj[v * mu + s as usize];
            for &(x, w) in &core[v] {
                // m*x + s2 = g*s + r,  0 <= s2 < m,  r != d
                let base = (g * s) as i64 - (m as i64) * (x as i64);
                for r in 0..g {
                    if r == d {
                        continue;
                    }
                    let s2 = base + r as i64;
                    if s2 >= 0 && s2 < m as i64 {
                        lst.push((x, w * m + s2 as u32));
                    }
                }
            }
        }
    }
    let (comp, nc) = scc(&nadj);
    let mut verts = vec![0u32; nc];
    let mut edges = vec![0u32; nc];
    for v in 0..nadj.len() {
        let c = comp[v] as usize;
        verts[c] += 1;
        for &(_, w) in &nadj[v] {
            if comp[w as usize] as usize == c {
                edges[c] += 1;
            }
        }
    }
    let mut collapsed = true;
    let mut keep = vec![u32::MAX; nadj.len()];
    let mut k = 0u32;
    for v in 0..nadj.len() {
        let c = comp[v] as usize;
        if edges[c] > 0 {
            if edges[c] > verts[c] {
                collapsed = false;
            }
            keep[v] = k;
            k += 1;
        }
    }
    let mut out: Adj = Vec::with_capacity(k as usize);
    for v in 0..nadj.len() {
        if keep[v] != u32::MAX {
            out.push(
                nadj[v]
                    .iter()
                    .filter(|&&(_, w)| keep[w as usize] != u32::MAX)
                    .map(|&(x, w)| (x, keep[w as usize]))
                    .collect(),
            );
        }
    }
    (out, collapsed)
}

fn digits_for(g: u32, first: bool, sym: bool) -> std::ops::Range<u32> {
    if first && sym {
        0..(g + 1) / 2 // d -> g-1-d is x -> -x
    } else {
        0..g
    }
}

/// Failing full assignments of S (DFS, prefix collapse prunes).  Stops after `limit`.
fn failing(g: u32, s: &[u32], sym: bool, limit: usize) -> Vec<Vec<u32>> {
    let mut bad = Vec::new();
    fn rec(g: u32, s: &[u32], sym: bool, limit: usize, j: usize, core: &Adj, ds: &mut Vec<u32>,
           bad: &mut Vec<Vec<u32>>) {
        if bad.len() >= limit {
            return;
        }
        if j == s.len() {
            bad.push(ds.clone());
            return;
        }
        for d in digits_for(g, j == 0, sym) {
            let (nc, col) = refine(g, core, s[j], d);
            if col {
                continue;
            }
            ds.push(d);
            rec(g, s, sym, limit, j + 1, &nc, ds, bad);
            ds.pop();
        }
    }
    rec(g, s, sym, limit, 0, &root(g), &mut Vec::new(), &mut bad);
    bad
}

fn parse_list(t: &str) -> Vec<u32> {
    if t.is_empty() {
        return vec![];
    }
    t.split(',').map(|x| x.parse().unwrap()).collect()
}

/// Deterministic sample of `k` indices from 0..n (LCG; reproducible).
fn sample(n: usize, k: usize, seed: &mut u64) -> Vec<usize> {
    if n <= k {
        return (0..n).collect();
    }
    let mut v: Vec<usize> = (0..n).collect();
    for i in 0..k {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let j = i + (*seed >> 33) as usize % (n - i);
        v.swap(i, j);
    }
    v.truncate(k);
    v
}

fn greedy(g: u32, seed: Vec<u32>, small_max: u32, big: Vec<u32>, samp: usize) {
    let mut leaves: Vec<(Vec<u32>, Adj)> = vec![(vec![], root(g))];
    let mut s: Vec<u32> = Vec::new();
    let extend = |leaves: &Vec<(Vec<u32>, Adj)>, m: u32, first: bool| -> Vec<(Vec<u32>, Adj)> {
        leaves
            .par_iter()
            .flat_map_iter(|(ds, core)| {
                digits_for(g, first, true).filter_map(move |d| {
                    let (nc, col) = refine(g, core, m, d);
                    if col {
                        None
                    } else {
                        let mut e = ds.clone();
                        e.push(d);
                        Some((e, nc))
                    }
                })
            })
            .collect()
    };
    for m in seed {
        leaves = extend(&leaves, m, s.is_empty());
        s.push(m);
    }
    println!("seed {:?} failing {}", s, leaves.len());
    let mut cands: Vec<u32> = (1..=small_max).filter(|m| m % g != 0).collect();
    cands.extend(big.iter().copied().filter(|m| m % g != 0));
    let mut rng = 0x5eed_u64;
    while !leaves.is_empty() {
        let t = std::time::Instant::now();
        let first = s.is_empty();
        let idx = sample(leaves.len(), samp, &mut rng);
        let mut scores: Vec<(usize, u32)> = cands
            .par_iter()
            .filter(|m| !s.contains(m))
            .map(|&m| {
                let n: usize = idx
                    .iter()
                    .map(|&i| {
                        digits_for(g, first, true)
                            .filter(|&d| !refine(g, &leaves[i].1, m, d).1)
                            .count()
                    })
                    .sum();
                (n, m)
            })
            .collect();
        scores.sort();
        let m = scores[0].1;
        leaves = extend(&leaves, m, first);
        s.push(m);
        let mx = leaves.iter().map(|(_, c)| c.len()).max().unwrap_or(0);
        println!("add {} -> {:?} failing {} maxcore {} runners-up {:?} ({:.0}s)", m, s,
                 leaves.len(), mx, &scores[1..scores.len().min(4)], t.elapsed().as_secs_f64());
    }
    println!("BLOCK {:?}", s);
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let g: u32 = a[2].parse().unwrap();
    match a[1].as_str() {
        "failing" => {
            let s = parse_list(&a[3]);
            let sym = !a.iter().any(|x| x == "--nosym");
            let limit = a.iter().position(|x| x == "--limit")
                .map(|i| a[i + 1].parse().unwrap()).unwrap_or(usize::MAX);
            let b = failing(g, &s, sym, limit);
            println!("failing {} first {:?}", b.len(), b.first());
        }
        "greedy" => greedy(g, parse_list(&a[3]), a[4].parse().unwrap(), parse_list(&a[5]),
                           a[6].parse().unwrap()),
        _ => panic!("unknown command"),
    }
}
