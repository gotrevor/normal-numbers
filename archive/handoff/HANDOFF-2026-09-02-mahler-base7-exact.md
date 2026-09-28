# HANDOFF 2026-09-02 (autonomous): `M(7,1) = 9` exact; prime upper bound cut to `g^(k+1) − 2g + 3` 🧮

Branch `wip/adder-tower-c9`, HEAD after two green commits (`c1b2d22`,
`2e29644`) plus this doc commit.  Working tree clean; every commit's
pre-commit hook ran the full `lake build` green; `src/` sorry-free; both new
headline theorems audit `[propext, Classical.choice, Quot.sound]`.
`CFScheduleA.lean` untouched (fenced), Comparator untouched.

## What advanced (the crux is the prime-base UPPER side; both items are on it)

### 1. `M(7,1) = 9` — a second exact Mahler constant at a prime base

Last lap's recorded blocker was that the base-7 upper half needed the chunked
`checkEdgesOnA` path because ambient `9! = 362880` would not `decide` in one
goal.  That turned out to be the wrong fix.  **The multiplier is quantified
after the digit**, so for each digit `w` separately it suffices that *some*
subset of `{1,…,9}` collapses — and the per-digit minimal subsets are tiny:
`{1,…,6,8}` (5760) for `w = 0,3,6`, `{1,3,4,5,6,9}` (3240) for `w = 1,5`,
`{1,…,6}` (720) for `w = 2,4`.  Total ambient `25200` instead of `2540160`, a
100× cut, and each digit is a plain `decide +kernel` of 18 s – 2 min.  The
earlier uniform-subset hunt (nothing under 30000) was not wrong, just
answering a stronger question.

Files: `MahlerBase7Cert0..6.lean` (one certificate each — seven kernel
`decide`s in ONE `lean` process exhaust memory at 7.4 GB and never finish),
`MahlerBase7Exact.lean` (`m7_mahler_upper`, `mahler_M_seven_eq_nine`).
Emitters: `experiments/mahler_subset_hunt_perdigit.py`,
`experiments/mahler_collapse_cert_perdigit.py` (the latter re-verifies
C1/C1'/C3' in Python before emitting).

### 2. `M(g,k) ≤ g^(k+1) − 2g + 3` for prime `g` — first strict cut on the headline

`MahlerPrimeUpper.lean` (new).  The covering sweep binds at the smallest
admissible shadow denominator `q`; `q = 1` means the orbit point is within
`g^(−k)` of an integer, i.e. a run of `k` zeros or `k` `(g−1)`s, which
`MahlerRunBranch` settles at `m ≤ gᵏ`.  `orbit_run_of_den_one` makes that
precise (the only integers in range are `0` and `1`, and their cells are
exactly those two blocks); `defect_contracts_of_bad_two` then runs the
contraction with `q ≥ 2`, tight because `M + 1 − 2q ≥ g(Q − q)` reduces to
`(q−2)(g−2) ≥ 0`.  `mahler_multiplier_prime` is the three-way case split.

This is the END of what the covering method can deliver (`q ≥ 3` is not
available — see `PENDING_WORK.md` §structural finding).

## Environment gotcha found this lap (cost ~1 h)

A `lake build` killed mid-flight (harness timeout, Ctrl-C) leaves **orphan
`lean` workers** running — three accumulated here at 5–7 GB RSS each, holding
~60k fds apiece, and they are what produces the box's "Too many open files"
error on the next build.  `ps -eo pid,etimes,rss,args | grep "[l]ean "` and
`kill -9` the strays BEFORE concluding the environment is at fault.  Also:
`lake build` of a target with 7 fresh Mathlib-importing modules fans out to 7
parallel `lean`s and hits the same wall — build such modules one at a time.
(The reference corpus's `lean-box-fd-exhaustion-is-mmap-not-nofile.md` calls
the mechanism unknown; orphan workers are at least one real cause.)

## Next attack

1. **The prime `Θ(g²)` upper side** — the standing crux.  Data:
   `M(p,1) = ⌊(p−1)²/4⌋ − δ`, `δ` small (`7→9`, `11→25`, `17→64` exact;
   `19→80` vs 81, `23→120` vs 121, `29→192` vs 196; `5→6` is above).  Needs
   Farey-hopping (two shadow denominators, hops between neighbouring Farey
   fractions), not a sharper covering constant.
2. `M(11,1) = 25` by a **greedy peel** of `{1,…,25}` (enumeration is `2²⁵`).
3. Uniform `B(g)` for a general prime lower-bound theorem.
4. Composite-`g` run theorem; B–B Thm 3.2.
