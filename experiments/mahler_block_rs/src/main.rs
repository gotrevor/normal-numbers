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
//!   mahler_block swap21 G m1,m2,... CANDS                     try S - {a,b} + {c}; first block wins
//!   mahler_block minimize G m1,m2,...                         drop redundant members
//!       (tests every single deletion in parallel; drops the largest removable member; repeats)
//!   mahler_block lift G KIN KOUT m1,m2,... [--limit N]           failing assignments of a RUNG
//!   mahler_block rung G KIN KOUT MAXM SIZE                       all rungs T in [2,MAXM], |T|=SIZE
//!   mahler_block wfail G K m1,m2,... [--limit N]                 failing assignments, K-WORD block
//!   mahler_block wsearch G K MAXM SIZE                           all K-word blocks in [1,MAXM]
//!   mahler_block wgreedy G K CANDS SAMPLE                        greedy K-word block
//!   mahler_block wminimize G K m1,m2,...                         drop redundant members
//!   mahler_block wswap21 G K m1,m2,... CANDS                     repeated 2-for-1 swaps
//!   mahler_block runs KMAX SET   binary: some member has both 0^k and 1^k i.o., k = 1..KMAX;
//!       SET may use A = 2^k - 1 and B = 2^k + 1 (e.g. 1,A,B)
//!   mahler_block among G K m1,... w1,w2,...   members may avoid only the listed words
//!   mahler_block asearch G K MAXM SIZE w1,w2,...   all such blocks of a size
//!   mahler_block rgreedy K CANDS SAMPLE   greedy run-block
//!   mahler_block rsearch K MAXM SIZE   all odd run-blocks (0^K and 1^K) of a size in [1,MAXM]
//!
//! A K-WORD BLOCK: for every irrational x some m in S has every length-K base-G word i.o. in m*x
//! (K = 1 is a product block).  Channel (m, w): state (carry, last K-1 emitted digits), emitted
//! window != w.
//!
//! A RUNG (KIN -> KOUT): for every irrational y with at least KIN digits occurring i.o., some
//! n in T has at least KOUT digits i.o. in n*y.  Rungs compose: if S is a rung (a -> b) and T a
//! rung (b -> c) then S*T is a rung (a -> c), and a rung (2 -> g) is a product block.  The rung
//! checker refines with "n*y has digits only in M" (|M| = KOUT-1) and keeps only SCCs that could
//! carry an irrational y with >= KIN digits: not a simple cycle, and >= KIN input labels.  A path
//! is eventually inside one SCC, so dropping the others is sound; the carry automaton is a
//! superset of the true carries, so "no SCC survives" proves the rung.

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

/// Is S a block?  DFS in the GIVEN order (a greedy order prunes far better than ascending:
/// 92 s vs >12 min on the 17-member base-5 block), first failure exits.
fn is_block(g: u32, s: &[u32]) -> bool {
    failing(g, s, true, 1).is_empty()
}

fn minimize(g: u32, mut s: Vec<u32>) {
    // The input is assumed to be a verified block (checking it again costs a full DFS).
    loop {
        let t = std::time::Instant::now();
        let removable: Vec<u32> = s
            .par_iter()
            .filter(|&&m| {
                let rest: Vec<u32> = s.iter().copied().filter(|&x| x != m).collect();
                is_block(g, &rest)
            })
            .copied()
            .collect();
        println!("|S|={} removable {:?} ({:.0}s)", s.len(), removable, t.elapsed().as_secs_f64());
        match removable.iter().max() {
            None => break,
            Some(&m) => s.retain(|&x| x != m),
        }
    }
    s.sort();
    println!("MINIMAL (no single deletion) {:?} size {}", s, s.len());
}

fn swap21(g: u32, s: Vec<u32>, cands: Vec<u32>) {
    let mut moves: Vec<(u32, u32, u32)> = Vec::new();
    for i in 0..s.len() {
        for j in i + 1..s.len() {
            for &c in &cands {
                if c % g != 0 && !s.contains(&c) {
                    moves.push((s[i], s[j], c));
                }
            }
        }
    }
    println!("{} moves", moves.len());
    let t = std::time::Instant::now();
    let hit = moves.par_iter().find_any(|&&(a, b, c)| {
        // keep the greedy order; the new member goes where its size puts it among the large ones
        let mut rest: Vec<u32> = s.iter().copied().filter(|&x| x != a && x != b).collect();
        let pos = rest.iter().position(|&x| x > 40 && c <= 40).unwrap_or(rest.len());
        rest.insert(pos, c);
        is_block(g, &rest)
    });
    match hit {
        Some(&(a, b, c)) => {
            let mut r: Vec<u32> = s.iter().copied().filter(|&x| x != a && x != b).collect();
            r.push(c);
            r.sort();
            println!("SWAP -{} -{} +{} -> {:?} size {} ({:.0}s)", a, b, c, r, r.len(), t.elapsed().as_secs_f64());
        }
        None => println!("NO 2-for-1 swap ({:.0}s)", t.elapsed().as_secs_f64()),
    }
}

/// Refine `core` by channel (m, allowed emitted digits `allow`), keeping only SCCs that are not a
/// simple cycle and carry at least `kin` distinct input labels.  None when nothing survives.
fn refine_mask(g: u32, core: &Adj, m: u32, allow: u32, kin: u32) -> Option<Adj> {
    let n = core.len();
    let mu = m as usize;
    let mut nadj: Adj = vec![Vec::new(); n * mu];
    for v in 0..n {
        for s in 0..m {
            let lst = &mut nadj[v * mu + s as usize];
            for &(x, w) in &core[v] {
                let base = (g * s) as i64 - (m as i64) * (x as i64);
                for r in 0..g {
                    if allow >> r & 1 == 0 {
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
    let mut labels = vec![0u32; nc];
    for v in 0..nadj.len() {
        let c = comp[v] as usize;
        verts[c] += 1;
        for &(x, w) in &nadj[v] {
            if comp[w as usize] as usize == c {
                edges[c] += 1;
                labels[c] |= 1 << x;
            }
        }
    }
    let live: Vec<bool> = (0..nc)
        .map(|c| edges[c] > verts[c] && labels[c].count_ones() >= kin)
        .collect();
    let mut keep = vec![u32::MAX; nadj.len()];
    let mut k = 0u32;
    for v in 0..nadj.len() {
        if live[comp[v] as usize] {
            keep[v] = k;
            k += 1;
        }
    }
    if k == 0 {
        return None;
    }
    let mut out: Adj = Vec::with_capacity(k as usize);
    for v in 0..nadj.len() {
        if keep[v] != u32::MAX {
            let c = comp[v];
            out.push(
                nadj[v]
                    .iter()
                    .filter(|&&(_, w)| comp[w as usize] == c)
                    .map(|&(x, w)| (x, keep[w as usize]))
                    .collect(),
            );
        }
    }
    Some(out)
}

/// Digit masks of size `k`; with `sym`, one representative per reflection pair d -> g-1-d
/// (y -> -y reflects every channel at once and preserves digit counts).
fn masks(g: u32, k: u32, sym: bool) -> Vec<u32> {
    let refl = |m: u32| (0..g).filter(|&d| m >> d & 1 == 1).fold(0u32, |a, d| a | 1 << (g - 1 - d));
    (0u32..1 << g)
        .filter(|&m| m.count_ones() == k && (!sym || m <= refl(m)))
        .collect()
}

/// Failing assignments of the rung (kin -> kout) for T: per member, the digit set M
/// (|M| = kout - 1) that n*y stays inside.
fn lift_failing(g: u32, kin: u32, kout: u32, t: &[u32], limit: usize) -> Vec<Vec<u32>> {
    fn rec(g: u32, kin: u32, kout: u32, t: &[u32], limit: usize, j: usize, core: &Adj,
           ms: &mut Vec<u32>, bad: &mut Vec<Vec<u32>>) {
        if bad.len() >= limit {
            return;
        }
        if j == t.len() {
            bad.push(ms.clone());
            return;
        }
        for m in masks(g, kout - 1, j == 0) {
            if let Some(nc) = refine_mask(g, core, t[j], m, kin) {
                ms.push(m);
                rec(g, kin, kout, t, limit, j + 1, &nc, ms, bad);
                ms.pop();
            }
        }
    }
    let mut bad = Vec::new();
    rec(g, kin, kout, t, limit, 0, &root(g), &mut Vec::new(), &mut bad);
    bad
}

fn is_rung(g: u32, kin: u32, kout: u32, t: &[u32]) -> bool {
    lift_failing(g, kin, kout, t, 1).is_empty()
}

/// Every rung T of the given size inside [2, maxm] (no multiples of g: n*g*y has n*y's digits).
fn rung_search(g: u32, kin: u32, kout: u32, maxm: u32, size: usize) {
    let cands: Vec<u32> = (2..=maxm).filter(|m| m % g != 0).collect();
    let mut sets: Vec<Vec<u32>> = vec![vec![]];
    for _ in 0..size {
        let mut nx = Vec::new();
        for s in &sets {
            for &c in &cands {
                if s.last().map_or(true, |&l| c > l) {
                    let mut e = s.clone();
                    e.push(c);
                    nx.push(e);
                }
            }
        }
        sets = nx;
    }
    let t = std::time::Instant::now();
    // largest member first: it prunes hardest
    let hits: Vec<Vec<u32>> = sets
        .par_iter()
        .filter(|s| {
            let r: Vec<u32> = s.iter().rev().copied().collect();
            is_rung(g, kin, kout, &r)
        })
        .cloned()
        .collect();
    println!("rung {}->{} base {} size {} in [2,{}]: {} of {} sets ({:.0}s)", kin, kout, g, size,
             maxm, hits.len(), sets.len(), t.elapsed().as_secs_f64());
    for h in hits.iter().take(40) {
        println!("  {:?}", h);
    }
}

/// Refine `core` by channel (m, avoided word w of length k), keeping only non-cycle SCCs.
fn refine_word(g: u32, core: &Adj, m: u32, k: u32, w: u32) -> Option<Adj> {
    let n = core.len();
    let h = g.pow(k - 1); // histories
    let per = (m * h) as usize;
    let mut nadj: Adj = vec![Vec::new(); n * per];
    for v in 0..n {
        for s in 0..m {
            for hist in 0..h {
                let lst = &mut nadj[v * per + (s * h + hist) as usize];
                for &(x, t) in &core[v] {
                    let base = (g * s) as i64 - (m as i64) * (x as i64);
                    for r in 0..g {
                        let s2 = base + r as i64;
                        if s2 < 0 || s2 >= m as i64 {
                            continue;
                        }
                        let win = hist * g + r;
                        if win == w {
                            continue;
                        }
                        let h2 = win % h;
                        lst.push((x, t * (m * h) + s2 as u32 * h + h2));
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
        for &(_, t) in &nadj[v] {
            if comp[t as usize] as usize == c {
                edges[c] += 1;
            }
        }
    }
    let mut keep = vec![u32::MAX; nadj.len()];
    let mut kk = 0u32;
    for v in 0..nadj.len() {
        let c = comp[v] as usize;
        if edges[c] > verts[c] {
            keep[v] = kk;
            kk += 1;
        }
    }
    if kk == 0 {
        return None;
    }
    let mut out: Adj = Vec::with_capacity(kk as usize);
    for v in 0..nadj.len() {
        if keep[v] != u32::MAX {
            let c = comp[v];
            out.push(nadj[v].iter().filter(|&&(_, t)| comp[t as usize] == c)
                .map(|&(x, t)| (x, keep[t as usize])).collect());
        }
    }
    Some(out)
}

/// Words of length k; with `sym`, one per digit-complement pair (x -> -x complements every
/// emitted digit at once).
fn words(g: u32, k: u32, sym: bool) -> Vec<u32> {
    let comp = |w: u32| {
        let (mut a, mut c, mut p) = (w, 0u32, 1u32);
        for _ in 0..k {
            c += (g - 1 - a % g) * p;
            a /= g;
            p *= g;
        }
        c
    };
    (0..g.pow(k)).filter(|&w| !sym || w <= comp(w)).collect()
}

fn word_failing(g: u32, k: u32, t: &[u32], limit: usize) -> Vec<Vec<u32>> {
    fn rec(g: u32, k: u32, t: &[u32], limit: usize, j: usize, core: &Adj, ws: &mut Vec<u32>,
           bad: &mut Vec<Vec<u32>>) {
        if bad.len() >= limit {
            return;
        }
        if j == t.len() {
            bad.push(ws.clone());
            return;
        }
        for w in words(g, k, j == 0) {
            if let Some(nc) = refine_word(g, core, t[j], k, w) {
                ws.push(w);
                rec(g, k, t, limit, j + 1, &nc, ws, bad);
                ws.pop();
            }
        }
    }
    let mut bad = Vec::new();
    rec(g, k, t, limit, 0, &root(g), &mut Vec::new(), &mut bad);
    bad
}

fn word_search(g: u32, k: u32, maxm: u32, size: usize) {
    let cands: Vec<u32> = (1..=maxm).filter(|m| m % g != 0).collect();
    let mut sets: Vec<Vec<u32>> = vec![vec![]];
    for _ in 0..size {
        let mut nx = Vec::new();
        for s in &sets {
            for &c in &cands {
                if s.last().map_or(true, |&l| c > l) {
                    let mut e = s.clone();
                    e.push(c);
                    nx.push(e);
                }
            }
        }
        sets = nx;
    }
    let t = std::time::Instant::now();
    let hits: Vec<Vec<u32>> = sets.par_iter()
        .filter(|s| {
            let r: Vec<u32> = s.iter().rev().copied().collect();
            word_failing(g, k, &r, 1).is_empty()
        })
        .cloned().collect();
    println!("{}-word blocks base {} size {} in [1,{}]: {} of {} ({:.0}s)", k, g, size, maxm,
             hits.len(), sets.len(), t.elapsed().as_secs_f64());
    for h in hits.iter().take(40) {
        println!("  {:?}", h);
    }
}

/// Greedy K-word block: add the candidate leaving the fewest live (assignment, core) leaves.
fn word_greedy(g: u32, k: u32, cands: Vec<u32>, samp: usize) {
    word_greedy_among(g, k, cands, samp, None)
}

/// Greedy with the avoided words restricted to `only` (None: every word, symmetry-reduced).
fn word_greedy_among(g: u32, k: u32, cands: Vec<u32>, samp: usize, only: Option<Vec<u32>>) {
    let words = |g: u32, k: u32, first: bool| -> Vec<u32> {
        match &only {
            Some(v) => if first { vec![v[0]] } else { v.clone() },
            None => words(g, k, first),
        }
    };
    let mut leaves: Vec<Adj> = vec![root(g)];
    let mut s: Vec<u32> = Vec::new();
    let mut rng = 0x5eed_u64;
    while !leaves.is_empty() {
        let t = std::time::Instant::now();
        let first = s.is_empty();
        let idx = sample(leaves.len(), samp, &mut rng);
        let mut scores: Vec<(usize, u32)> = cands.par_iter().filter(|m| !s.contains(m))
            .map(|&m| {
                let n: usize = idx.iter().map(|&i| words(g, k, first).into_iter()
                    .filter(|&w| refine_word(g, &leaves[i], m, k, w).is_some()).count()).sum();
                (n, m)
            }).collect();
        scores.sort();
        let m = scores[0].1;
        leaves = leaves.par_iter().flat_map_iter(|c| words(g, k, first).into_iter()
            .filter_map(move |w| refine_word(g, c, m, k, w))).collect();
        s.push(m);
        let mx = leaves.iter().map(|c| c.len()).max().unwrap_or(0);
        println!("add {} -> {:?} failing {} maxcore {} runners-up {:?} ({:.0}s)", m, s,
                 leaves.len(), mx, &scores[1..scores.len().min(4)], t.elapsed().as_secs_f64());
    }
    println!("WORD BLOCK {:?}", s);
}

fn word_minimize(g: u32, k: u32, mut s: Vec<u32>) {
    loop {
        let t = std::time::Instant::now();
        let removable: Vec<u32> = s.par_iter().filter(|&&m| {
            let rest: Vec<u32> = s.iter().copied().filter(|&x| x != m).collect();
            word_failing(g, k, &rest, 1).is_empty()
        }).copied().collect();
        println!("|S|={} removable {:?} ({:.0}s)", s.len(), removable, t.elapsed().as_secs_f64());
        match removable.iter().max() {
            None => break,
            Some(&m) => s.retain(|&x| x != m),
        }
    }
    s.sort();
    println!("MINIMAL (no single deletion) {:?} size {}", s, s.len());
}

/// Repeated 2-for-1 swaps on a K-word block until none works.
fn word_swap21(g: u32, k: u32, mut s: Vec<u32>, cands: Vec<u32>) {
    loop {
        let mut moves: Vec<(u32, u32, u32)> = Vec::new();
        for i in 0..s.len() {
            for j in i + 1..s.len() {
                for &c in &cands {
                    if c % g != 0 && !s.contains(&c) {
                        moves.push((s[i], s[j], c));
                    }
                }
            }
        }
        let t = std::time::Instant::now();
        let hit = moves.par_iter().find_any(|&&(a, b, c)| {
            let mut rest: Vec<u32> = s.iter().copied().filter(|&x| x != a && x != b).collect();
            rest.push(c);
            rest.sort_by(|x, y| y.cmp(x));
            word_failing(g, k, &rest, 1).is_empty()
        });
        match hit {
            Some(&(a, b, c)) => {
                s.retain(|&x| x != a && x != b);
                s.push(c);
                s.sort();
                println!("SWAP -{} -{} +{} -> {:?} size {} ({:.0}s)", a, b, c, s, s.len(),
                         t.elapsed().as_secs_f64());
            }
            None => {
                println!("NO 2-for-1 swap from {:?} size {} ({:.0}s)", s, s.len(),
                         t.elapsed().as_secs_f64());
                break;
            }
        }
    }
}

/// Failing assignments when each member avoids one of the given words (e.g. 0^k and 1^k).
fn word_failing_among(g: u32, k: u32, t: &[u32], ws: &[u32], limit: usize) -> Vec<Vec<u32>> {
    fn rec(g: u32, k: u32, t: &[u32], ws: &[u32], limit: usize, j: usize, core: &Adj,
           cur: &mut Vec<u32>, bad: &mut Vec<Vec<u32>>) {
        if bad.len() >= limit {
            return;
        }
        if j == t.len() {
            bad.push(cur.clone());
            return;
        }
        for &w in ws {
            if let Some(nc) = refine_word(g, core, t[j], k, w) {
                cur.push(w);
                rec(g, k, t, ws, limit, j + 1, &nc, cur, bad);
                cur.pop();
            }
        }
    }
    let mut bad = Vec::new();
    rec(g, k, t, ws, limit, 0, &root(g), &mut Vec::new(), &mut bad);
    bad
}

/// Binary runs: does some member have both 0^k and 1^k i.o.?  Prints failing count per k.
fn runs(kmax: u32, sets: &str) {
    for k in 1..=kmax {
        let ones = (1u32 << k) - 1;
        let s: Vec<u32> = sets.replace("A", &((1u32 << k) - 1).to_string())
            .replace("B", &((1u32 << k) + 1).to_string())
            .split(',').map(|x| x.parse().unwrap()).collect();
        let t = std::time::Instant::now();
        let b = word_failing_among(2, k, &s, &[0, ones], 1);
        println!("k={} S={:?} {} ({:.1}s)", k, s, if b.is_empty() { "BLOCK".to_string() } else {
                 format!("fails, avoided {:?}", b[0].iter().map(|&w| if w == 0 { "0^k" } else { "1^k" }).collect::<Vec<_>>()) },
                 t.elapsed().as_secs_f64());
    }
}

fn runs_search(k: u32, maxm: u32, size: usize) {
    let cands: Vec<u32> = (1..=maxm).filter(|m| m % 2 == 1).collect();
    let mut sets: Vec<Vec<u32>> = vec![vec![]];
    for _ in 0..size {
        let mut nx = Vec::new();
        for s in &sets {
            for &c in &cands {
                if s.last().map_or(true, |&l| c > l) {
                    let mut e = s.clone();
                    e.push(c);
                    nx.push(e);
                }
            }
        }
        sets = nx;
    }
    let ones = (1u32 << k) - 1;
    let hits: Vec<Vec<u32>> = sets.par_iter().filter(|s| {
        let r: Vec<u32> = s.iter().rev().copied().collect();
        word_failing_among(2, k, &r, &[0, ones], 1).is_empty()
    }).cloned().collect();
    println!("runs k={} size {} in [1,{}]: {} of {}", k, size, maxm, hits.len(), sets.len());
    for h in hits.iter().take(30) {
        println!("  {:?}", h);
    }
}

/// All blocks of a size in [1, maxm] (no multiples of g) where members may avoid only `ws`.
fn among_search(g: u32, k: u32, maxm: u32, size: usize, ws: &[u32]) {
    let cands: Vec<u32> = (1..=maxm).filter(|m| m % g != 0).collect();
    let mut sets: Vec<Vec<u32>> = vec![vec![]];
    for _ in 0..size {
        let mut nx = Vec::new();
        for s in &sets {
            for &c in &cands {
                if s.last().map_or(true, |&l| c > l) {
                    let mut e = s.clone();
                    e.push(c);
                    nx.push(e);
                }
            }
        }
        sets = nx;
    }
    let hits: Vec<Vec<u32>> = sets.par_iter().filter(|s| {
        let r: Vec<u32> = s.iter().rev().copied().collect();
        word_failing_among(g, k, &r, ws, 1).is_empty()
    }).cloned().collect();
    println!("base {} k={} words {:?} size {} in [1,{}]: {} of {}", g, k, ws, size, maxm,
             hits.len(), sets.len());
    for h in hits.iter().take(12) {
        println!("  {:?}", h);
    }
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
        "minimize" => minimize(g, parse_list(&a[3])),
        "swap21" => swap21(g, parse_list(&a[3]), parse_list(&a[4])),
        "lift" => {
            let limit = a.iter().position(|x| x == "--limit")
                .map(|i| a[i + 1].parse().unwrap()).unwrap_or(usize::MAX);
            let b = lift_failing(g, a[3].parse().unwrap(), a[4].parse().unwrap(),
                                 &parse_list(&a[5]), limit);
            println!("failing {} first {:?}", b.len(), b.first().map(|v| v.iter()
                .map(|m| format!("{:b}", m)).collect::<Vec<_>>()));
        }
        "rung" => rung_search(g, a[3].parse().unwrap(), a[4].parse().unwrap(),
                              a[5].parse().unwrap(), a[6].parse().unwrap()),
        "wfail" => {
            let limit = a.iter().position(|x| x == "--limit")
                .map(|i| a[i + 1].parse().unwrap()).unwrap_or(usize::MAX);
            let k: u32 = a[3].parse().unwrap();
            let b = word_failing(g, k, &parse_list(&a[4]), limit);
            let fmt = |w: u32| (0..k).rev().map(|i| char::from_digit(w / g.pow(i) % g, 36).unwrap())
                .collect::<String>();
            println!("failing {} first {:?}", b.len(),
                     b.first().map(|v| v.iter().map(|&w| fmt(w)).collect::<Vec<_>>()));
        }
        "wsearch" => word_search(g, a[3].parse().unwrap(), a[4].parse().unwrap(),
                                 a[5].parse().unwrap()),
        "wgreedy" => word_greedy(g, a[3].parse().unwrap(), parse_list(&a[4]),
                                 a[5].parse().unwrap()),
        "wminimize" => word_minimize(g, a[3].parse().unwrap(), parse_list(&a[4])),
        "wswap21" => word_swap21(g, a[3].parse().unwrap(), parse_list(&a[4]), parse_list(&a[5])),
        "rsearch" => runs_search(a[2].parse().unwrap(), a[3].parse().unwrap(),
                                 a[4].parse().unwrap()),
        "rgreedy" => {
            let k: u32 = a[2].parse().unwrap();
            word_greedy_among(2, k, parse_list(&a[3]), a[4].parse().unwrap(),
                              Some(vec![0, (1 << k) - 1]))
        }
        "among" => {
            // among G K m1,... w1,w2,...: each member may avoid only one of the listed words
            let k: u32 = a[3].parse().unwrap();
            let b = word_failing_among(g, k, &parse_list(&a[4]), &parse_list(&a[5]), 1);
            println!("{} {:?}", if b.is_empty() { "BLOCK" } else { "fails" }, b.first());
        }
        "asearch" => among_search(g, a[3].parse().unwrap(), a[4].parse().unwrap(),
                                  a[5].parse().unwrap(), &parse_list(&a[6])),
        "runs" => runs(a[2].parse().unwrap(), &a[3]),
        _ => panic!("unknown command"),
    }
}
