# HANDOFF 2026-09-02 (autonomous): the prime-base upper bound, from `g^(k+1)` to a route at `g^(k+1)/4` 🧮

Branch `wip/adder-tower-c9`, HEAD `b5cf264`.  **Working tree clean; nothing
uncommitted.**  Six green commits this lap, every one gated by the pre-commit
`lake build`; `src/` sorry-free; every new theorem audits
`[propext, Classical.choice, Quot.sound]`.  `CFScheduleA.lean` untouched
(fenced), Comparator untouched, `DIRECTION.md` not edited.

`DIRECTION.md`'s CURRENT DIRECTIVE mandates the **prime-base upper bound** as
the crux and names the multi-scale invariant as the attack.  All six commits
are on that.

## What advanced

### 1. `M(7,1) = 9` exact (`c1b2d22`) — a second prime base pinned

Last lap's blocker (ambient `9! = 362880` would not `decide`; "needs the chunked
`checkEdgesOnA` path") was the **wrong fix**.  The multiplier is quantified
AFTER the digit, so for each `w` separately it suffices that *some* subset of
`{1,…,9}` collapses.  Per-digit minima: `{1..6,8}` (5760) for `w = 0,3,6`,
`{1,3,4,5,6,9}` (3240) for `w = 1,5`, `{1..6}` (720) for `w = 2,4` — total
ambient `25200` vs `2540160`, a **100× cut**, each digit a plain
`decide +kernel` of 18 s–2 min.  Files `MahlerBase7Cert0..6.lean` (one per
module: seven kernel decides in ONE `lean` process hit 7.4 GB and never
finish), `MahlerBase7Exact.lean`.  Emitters
`experiments/mahler_subset_hunt_perdigit.py`,
`experiments/mahler_collapse_cert_perdigit.py`.

### 2. `M(g,k) ≤ g^(k+1) − 2g + 3`, prime `g` (`2e29644`) — first strict cut

`MahlerPrimeUpper.lean`.  `q = 1` in the covering sweep means the orbit point is
within `g^(−k)` of an integer = a run of `k` zeros or `k` `(g−1)`s, which
`MahlerRunBranch` settles at `m ≤ gᵏ` (`orbit_run_of_den_one`).  So the sweep
starts at `q ≥ 2`; tight, since `M+1−2q ≥ g(Q−q)` reduces to `(q−2)(g−2) ≥ 0`.

### 3. `M(g,1) ≤ g(g+1)/2`, odd prime `g` (`911857d`) — the `g²` headline halved

`MahlerPrimeHalf.lean`.  The recorded wall was that *excluding* `q ≥ 2` is
unavailable.  The way past: **convert** instead.  If `x_n` is within
`g^(−k)/q` of `p/q` then `q x_n` is within `g^(−k)` of an integer, i.e. `qα`
has a `0ᵏ` (or `(g−1)ᵏ`) run — settled at `m' ≤ gᵏ`, and `m'(qα) = (m'q)α`.
So a small denominator costs only `q gᵏ` (`mahler_multiplier_near_grid`), with
no coprimality.  With a threshold `q₀`, `mahler_multiplier_prime_param`
balances `(q₀−1)gᵏ` against `g^(k+1) − q₀(g−2) − 1`; at `k = 1`,
`q₀ = (g+1)/2` makes both exactly `g(g+1)/2`.
(`6ad7e37` adds the `k ≥ 2` instance `q₀ = g`: `g^(k+1) − g(g−2) − 1`.)

⚠️ Sanity anchor: the halving CANNOT hold at composite bases —
`M(18,1) = 272 > 18·19/2 = 171` — and indeed the proof needs `g.Prime` through
the run branch.

### 4. **The denominator-jump engine, and a route to `g^(k+1)/4`** (`7be6ebf`, `b5cf264`)

`MahlerFarey.lean`.  This is the lap's real result; the full argument is in
`PENDING_WORK.md` §top.  Sketch, `Q = gᵏ`, `x` bad:

* `defect_pair_ge` — Farey separation: distinct `p/q, p'/q'` give
  `q'|qx−p| + q|q'x−p'| ≥ 1` (the integer `pq'−p'q` is nonzero and telescopes).
* `approx_unique` / `orbit_approx_unique` — so the quality-`1/(2Q)` shadow is a
  FUNCTION of `x`: constraints from different scales refer to one canonical
  rational and cannot be dodged.
* `defect_small_of_bad` — for bad `x` the Dirichlet approximation has defect
  `< 1/(2Q+1)`, not just `1/(Q+1)` (needs `M ≥ 4Q`).
* `den_jump_of_bad` — hence any other reduced `p/a`, `a ≤ Q`, has
  `σ.den·|ax−p| > 1/2`, i.e. `σ.den > 1/(2|ax−p|)`.

Run the shadow chain from denominator `a`; the defect `×g` each step; at the
first exit time `n*` the covering bound at `n*−1` gives
`E/g < (1−a/Q)/(M+1−2a)`, hence `σ.den > (M+1−2a)/(2g(1−a/Q))`: **the canonical
denominator jumps**.  Iterating, `a_{j+1} ≳ (M/g)/(1−a_j/Q)`, whose fixed point
needs `a(1−a/Q) = M/g` solvable, i.e. `M/g ≤ Q/4` (max at `a = Q/2`).  For
`M > gQ/4` no fixed point, the denominators grow by a fixed amount per stage
and must pass `Q` — contradiction.  Target **`M(g,k) ≤ (1/4+O(1/g))g^(k+1)`**.

The constant is the truth: `M(p,1) = 6, 9, 25, 64` at `p = 5, 7, 11, 17` vs
`(p−1)²/4 = 4, 9, 25, 64`.  And `a = Q/2` being the DOUBLE ROOT derives (rather
than observes) why the extremal witnesses sit at shadow denominator `q ≈ g/2`.

## Next lap: finish the multi-scale bound (bookkeeping, no new idea)

1. The exit time `n*` as a `Nat.find` on "shadow defect `≥ 1/Q`", and the
   shadow-defect recursion `E_{i+1} = g E_i` extracted from `orbit_escapes`
   (which currently proves the recursion and then discards it).
2. The stage iteration as an induction of `⌈1/(M/(gQ) − 1/4)⌉` steps on the
   denominator, each application of `den_jump_of_bad`.
3. Carry the `O(1/g)` loss (`a·(defect σ) ≤ Q/(2Q+1)`, not `1/2`) so the
   constant lands at `1/4 + O(1/g)` rather than `1/2`.
4. Then retire `mahler_multiplier_prime_half` to a corollary.

Side thread left running and unfinished: `experiments/mahler_subset_hunt_perdigit.py 11 25 300000`
(a third exact prime value `M(11,1) = 25`); it had produced no output at lap end
— either raise the cap or replace enumeration with a greedy peel.

## Environment gotcha found this lap (cost ~1 h)

A `lake build` killed mid-flight leaves **orphan `lean` workers** — three
accumulated here at 5–7 GB RSS each, ~60k fds apiece — and THEY are what
produces the box's "Too many open files".
`ps -eo pid,etimes,rss,args | grep "[l]ean "` and `kill -9` the strays before
blaming the environment.  Also: a target with 7 fresh Mathlib-importing modules
fans out to 7 parallel `lean`s and hits the same wall — build those one at a
time.  (The reference corpus's `lean-box-fd-exhaustion-is-mmap-not-nofile.md`
lists the mechanism as unknown; orphan workers are at least one real cause.)
