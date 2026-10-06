# Base 5 has no small `{2, 11}` 🧱

2026-10-05.  Operator prompt: *"for any irrational x, 2x or 11x contains all three ternary
digits i.o. - perhaps there's something similar for base 5?"*  Lean:
`src/NormalNumbers/MahlerProductBlock.lean`.  Probe: `experiments/mahler_product_block.py`
(tests: `experiments/test_mahler_product_block.py`).

**BLUF.**  A base-5 analogue exists (Mahler 1973 / B-B 1994 put one inside `[1, 2·5⁶]`) but it
is nowhere near as small as `{2, 11}`: **every base-5 product block contains a multiplier
`≥ 194`**, and inside `[1, 625]` it needs **at least five** multipliers.  The obstruction is
the Berend-Boshernitzan Liouville witness, which costs base 3 almost nothing (`12₃ = 5`) and
base 5 a lot (`1234₅ = 194`).

## Definitions

A **product block** in base `g` is a finite `S` with: for every irrational `x`, a *single*
`m ∈ S` has every base-`g` digit i.o. in `m·x` (`IsProductBlock`).  Contrast the per-digit
Mahler sets (`M(5,1) = 6`, `mahler_M_five_eq_six`), where the multiplier may depend on the
digit.  `{2, 11}` is a ternary block (`isProductBlock_three_two_eleven`, from C2).

## Prior art: Berend-Boshernitzan 1995 (Acta Math. Hungar. 66, 113-126) 📚

Read 2026-10-05 (the 08-30 citation sweep had not).  §3 defines **M_g-sets**: `A ⊆ ℕ` such that
for every irrational α and every base-g block B, some `m ∈ A` has B i.o. in `mα`.  Remark 3.1 is
the JOINT form (one `m` with every length-k block i.o.), and Lemma 3.1 is the `g^n` rescaling
(our "multiples of 5 are redundant").  An M_g-set must handle blocks of every length, so it is
necessarily infinite (their examples are lacunary sequences).  A product block is the finite,
`k = 1` object: same notion family, a different and explicit statement.  Novelty status of an
explicit finite joint set: still not found; zbMATH "cited by" for B-B 1994 is the open check.

### zbMATH forward citations (2026-10-05, Trevor's browser)

- B-B 1994 is cited by: Thangadurai-Tripathi 2025, Meher-Kumar-Thangadurai 2017, B-B 1995.
- Mahler 1973 is cited by: the same three, Bugeaud-Coons 2019, Alon-Peres 1992, Mahler 1982
  (memoir); reviews also cite Szüsz-Volkmann 1983 (not yet read).
- **Bugeaud-Coons 2019, *A Mahler miscellany*, Thm 7.1** states Mahler's theorem JOINTLY and
  adds "one can take `B(b,k) = bᵏ(b+1)`" (citing Bugeaud's book §8.6).  Jointly that is false:
  `b = 5, k = 1` gives `{1..30}`, and the Liouville cover needs some `m ≥ 194`
  (`not_isProductBlock_five_Icc_thirty`).  The bound is per-block.  Whether the slip is the
  survey's paraphrase or the book's own statement is unchecked (no Cornell route to Cambridge
  books).  Base 3 hides it: `B(3,1) = 12 ≥ 11 = 102₃`.
- **Szüsz-Volkmann 1983** (Crelle 339, 199-206; read 2026-10-05, PDF in `papers/`): the JOINT
  bound sharpened to `C₂(N,g) = 12·g^(gᴺ+N)` (`g = 5, N = 1`: 187,500).  No small sets, no
  lower bounds.
- No explicit finite joint set found anywhere in this graph.

## The lower side: the Liouville cover 🎯

Take `x = B · Σ g^(−i!)`.  Past a point, the base-`g` tail of `m·x` is the digit string of
`m·B` repeated with zero gaps, so a nonzero digit is i.o. in `m·x` iff it is a digit of `m·B`.
Hence (`IsProductBlock.liouville_cover`, `sorry`, 95%, English proof in the docstring):

> a block contains, for **every** `B ≥ 1`, some `m` whose product `m·B` uses every nonzero digit.

- `B = 1`, base 5: some `m ∈ S` has digits ⊇ {1,2,3,4}, so `m ≥ 1234₅ = 194`
  (`IsProductBlock.base5_exists_ge`, proved from the cover lemma + a kernel `decide`).
- Base 3: the same bound is `12₃ = 5`; `{2, 11}` and `{1, 4, 7}` sit just above it.
- **Every search before this note capped `m` at 60, so none could have found a base-5 block.**
- Set cover over `B ≤ 300` (exact ILP, HiGHS, dual bound = optimum): minimum `|S| = 5` for
  `S ⊆ [1, 625]` (`IsProductBlock.base5_card_ge_five`, `sorry`, 93%).  Base-3 control: optimum 2.
  Raising to `B ≤ 1500` (20-min limit): best cover found has 6 (`[298, 312, 537, 574, 588, 621]`),
  proved floor still 5.
- Allowing `m ≤ 3125` (`B ≤ 600`, 20-min limit) trades size for magnitude: a 4-cover exists
  (`[1161, 2926, 3094, 3121]`), proved floor 3; at `B ≤ 2000` the best found is 5
  (`[1646, 2497, 2906, 3043, 3121]`), floor still 3.  So "≥ 5" is a statement about `[1, 625]` only.
- The filter is necessary, not sufficient: in base 3, 87 pairs `≤ 40` pass it for `B ≤ 3000`,
  and the exact checker accepts only `{2, 11}` and `{4, 22} = 2·{2, 11}` (`image_mul`).

## The upper side: exact search, still open 🔬

`mahler_product_block.py` is an exact collapse checker (carry-automaton, as for C2), rewritten
to refine only the cycle-core one channel at a time, so multipliers in the hundreds are
affordable.  A collapse is a proof; a failing assignment is only "no certificate".

- Small multipliers alone cannot work (the cover bound), and large ones alone fail the
  constant assignments (`[248, 376, 517, 558, 596]` fails all-zeros: per-digit sets need the
  small end).  A block has to mix both.
- Greedy from `{1,2,3,4,8}` (the best small 5-set): failing assignments 1400 → 4611 at
  `+16`; the multiplicative growth per channel is falling (5 → 4 → 3.3) but has not turned.
  Mixed small+large greedy (`{1,2,3,4,8}` seed, candidates `m ≤ 40` plus the 60 best
  Liouville-covering `m ≤ 1000`): `+16` 4611, `+9` 12501, `+29` 25418, `+34` 44813, `+919` 71497 failing.
  Per-step growth 3.3 → 2.7 → 2.0 → 1.8 → 1.6, still above 1.  `919 = 12134₅` is the first
  large pick, and it uses all four nonzero digits, as the cover bound says some member must.
  Steps now cost an hour in pure Python; the next lever is a compiled checker, not more time.
- **Rust port** (`experiments/mahler_block_rs`, ~115x over CPython; PyPy only 1.3x), same seed,
  candidates `m ≤ 40` plus the 200 best Liouville-covering `m ≤ 3125`, 2000-leaf sampled scoring:
  `+16` 4611, `+29` 12186, `+23` 25161, `+17` 42032, `+1838` 57622, `+2832` 50180 (first
  decline; `2832 = 42312₅` has all four nonzero digits), `+3028` 21890, `+2272` 8353.
  Growth factors 3.3, 2.6, 2.1, 1.7, 1.4, 0.87, 0.44, 0.38 at ~5 min/step, then `+2439` 1829,
  `+2188` 473, `+1251` 32, `+1254` **0**.

## 🎯 A base-5 product block (2026-10-05, ~20:45)

    S = {1, 2, 3, 4, 8, 16, 17, 23, 29, 1251, 1254, 1838, 2188, 2272, 2439, 2832, 3028}

> **For every irrational x, one of these 17 multiples of x has every base-5 digit infinitely
> often.**  (Classical comparison: ~12,500 multipliers, `[1, 15624] \ 5ℤ`, via
> `mahler_multiplier_lt` on the word `01234`.)

- Certificate: every assignment S → digits collapses on some prefix (exact carry-automaton
  collapse, the C2 method).  Found by the Rust greedy (first-level `d ↦ 4−d` symmetry).
- Re-verified: full Rust DFS **without** the symmetry reduction, 0 failing (28 min); with it, 0
  (92 s).  The Rust checker is tested against hand-derived verdicts and matches the Python
  reference counts (`test_mahler_product_block.py`); a full Python re-run was judged not worth
  its ~days of CPU.  Liouville cover holds for every `B ≤ 20000`.
- Large members in base 5: 1251 = 20001, 1254 = 20004, 1838 = 24323, 2188 = 32223,
  2272 = 33042, 2439 = 34224, 2832 = **42312** (the only one with all four nonzero digits,
  the member `base5_exists_ge` demands), 3028 = 44103.
- **Minimized to 15** (`mahler_block minimize`, each accepted deletion re-verified by a full
  DFS): `{1, 2, 8, 16, 17, 23, 29, 1251, 1254, 1838, 2188, 2272, 2439, 2832, 3028}`, dropping 4
  then 3.  No single member of the 15 is removable (inclusion-minimal, not minimum).  Gap to the
  proved floors: 3 overall, 5 if every member is `≤ 625` (`base5_card_ge_five`).
- **2-for-1 swap → 14** (`mahler_block swap21`, 22,785 moves, first hit after 910 s): drop `1`
  and `8`, add `2428 = 34203₅`:
  `{2, 16, 17, 23, 29, 1251, 1254, 1838, 2188, 2272, 2428, 2439, 2832, 3028}`.  It no longer
  contains `x` itself.  No single deletion from the 14.
- **Swap again → 13** (2374 s): drop `29` and `1251`, add `2753 = 42003₅`:
  `{2, 16, 17, 23, 1254, 1838, 2188, 2272, 2428, 2439, 2753, 2832, 3028}`.  No single deletion.
- **Swap again → 12** (25,981 s ≈ 7.2 h; each round is slower as near-blocks get rarer): drop
  `2` and `16`, add `1562 = 22222₅`:
  `{17, 23, 1254, 1562, 1838, 2188, 2272, 2428, 2439, 2753, 2832, 3028}`.  Only two members are
  below 1000.
- Lean: `checkCertA` enumerates the ambient carry product (here ∏ m ≈ 10⁴⁰), so a Lean
  certificate needs a sparse, live-states-only checker.

## Status

- Proved: `{2,11}` instance, scaling, `194 ≤ max S` (modulo the 95% cover lemma).
- Open: an explicit base-5 block, and its Lean certificate.  The existing `checkCertA` engine
  enumerates the ambient product of carry ranges (720 for M(5,1), 3240 for base 7); a block
  with multipliers in the hundreds has an astronomically larger ambient space, so a Lean
  certificate needs a sparse (live-states-only) checker.  That is a treadmill-sized job.
