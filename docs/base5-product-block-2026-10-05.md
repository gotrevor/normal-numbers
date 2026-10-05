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

## Status

- Proved: `{2,11}` instance, scaling, `194 ≤ max S` (modulo the 95% cover lemma).
- Open: an explicit base-5 block, and its Lean certificate.  The existing `checkCertA` engine
  enumerates the ambient product of carry ranges (720 for M(5,1), 3240 for base 7); a block
  with multipliers in the hundreds has an astronomically larger ambient space, so a Lean
  certificate needs a sparse (live-states-only) checker.  That is a treadmill-sized job.
