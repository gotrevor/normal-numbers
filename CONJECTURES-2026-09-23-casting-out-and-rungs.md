# Three conjectures toward more specific disjunctive/normal constants (2026-09-23)

Trevor asked for three new conjectures that would help prove more and more specific numbers
disjunctive or normal.  Before proposing, I checked them against the Maze (≈120 rows) and DIRECTION.
Two candidates died or were demoted by probe the same evening (see the end).  None of this
authorizes a campaign: these are nodes for the conjecture graph, not laps.

## C1 🎯 Casting-out equidistribution for G4 (an abelian statistic, carries only at the ends)

**Conjecture.** For every `b ≥ 3` and `L ≥ 1`, the digit sums of the length-`L` windows of
`G4_b = Σ_p 1/(bᵖ−1)` in base `b` are equidistributed mod `b−1`.

**The exact reduction (elementary, verified).**  For any real `x`, window digits satisfy
`Σ d_i ≡ ⌊b^{n+L}x⌋ − ⌊bⁿx⌋ (mod b−1)`.  For `x = Σ ω(m) b^(−m)`:

    window digit sum ≡ Σ_{m∈(n,n+L]} ω(m) + c_{n+L} − c_n   (mod b−1),   c_N = ⌊Σ_{m>N} ω(m) b^{N−m}⌋.

`probes/g4_casting_out.py` checks this against the true digits: 0 mismatches over L = 1..8 and 10⁵
positions, in bases 3 and 5 (and in bases 3, 5, 9 for the divisor weight, below).

**Why it is not the refuted "G4 sectors as digit characters" row.**  That row read digit PARITY,
where carries hit every digit and its correlation with ω-parity decays to 0.  Casting out `b−1`
is exact: the carry is a BOUNDARY term at the two window ends, never a bulk one.

**What it reduces to.**  Joint residues of `(ω(n+1), …, ω(n+K))` modulo `b^K(b−1)`, i.e.
correlations `Σ_n Π z_i^{ω(n+i)}` of the non-pretentious multiplicative functions `z^ω`
(roots of unity `z ≠ 1`).  Natural density is an Elliott-conjecture instance, which is open.  The
logarithmic-density version may already follow from Tao (2016, two-point log-Elliott) and
Tao–Teräväinen (2019).  **Check the literature before claiming it.**

**Why it matters.**  It would be the first FREQUENCY statement about the prime-Lambert family,
beyond disjunctivity.  Digit sum mod `b−1` is a function of the Parikh vector, so it is the
cheapest projection of abelian normality (`AbelianNormal.lean`).  It is also the one projection
that carries cannot scramble.  Confidence: true ~90%; the log-density version provable from
existing literature ~40%.

**Numerics caveat.**  At N = 10⁵ the L = 1 residues are far from uniform: base 5 gives
.18/.09/.33/.39.  `ω` mod q converges on a `log log` scale, so numerics cannot confirm C1.
Only the identity is measured.

## C2 Erdős–Borwein is disjunctive (does the G4 method need additivity?)

**Conjecture.** `E_b = Σ_{n≥1} 1/(bⁿ−1) = Σ_m d(m) b^(−m)` is disjunctive in base `b` for every `b ≥ 3`.

A famous named constant: Erdős (1948) proved it irrational, and its normality is open.  The G5
interface covers ADDITIVE weights (ω, Ω).  The divisor function `d` is multiplicative, so C2 is
the test of which hypothesis the local contraction (C2 in `G4LocalContraction`) actually uses.
If it transfers, it is a method.  If it fails, it names additivity as load-bearing.

The same casting-out identity holds for `d` (0 mismatches).  Note that `2^{ω(m)} | d(m)` for
squarefree `m`, so when `b−1` is a power of two, the window sum mod `b−1` is carried almost
entirely by the boundary carries.  No persistent bias shows at N = 10⁵: base 9, L = 8 lies in
.120–.131 against .125.  Base 2 stays retired for the same `rowL1` reason as G4.  Confidence:
true ~95%; the G4 machinery transfers ~30%.

## C3 The frequency-disjunctive rung for G4

**Conjecture.** For `b ≥ 3`, every base-`b` word occurs in `G4_b` with POSITIVE LOWER DENSITY.

This sits strictly between `isDisjunctive_base` (proved) and normality (conditional).  First move,
before any Lean: measure the density of the good sample set that the disjunctivity proof actually
uses.  If it is density zero by design, that sparsity IS the disjunctive/normal gap for this
family, and naming it is the finding.  Confidence: true ~95%; reachable with current tools ~25%.

## Killed or demoted tonight (candidate Maze rows, not yet added: a treadmill is mid-run in this checkout)

- **"α₂,₃ is abelian-normal in base 6"** (a natural abelian-but-not-normal number): **refuted**,
  and trivially.  In base 6, term m is `3^{3^m−m}/6^{3^m}` and occupies digits
  `[0.387·3^m, 3^m]`, so the gap `(3^m, 1.161·3^m)` is forced zeros.  Hand count at N = 2·10⁵:
  about 19% forced zeros, so freq(0) ≈ .19 + .81/6 = .325.  Measured .3217, so not even simply
  normal.  `probes/abelian_stoneham_and_times3.py` part A.  This is Bailey–Borwein's mechanism,
  not new.
- **"x and 3x abelian-normal in base 2 ⇒ x normal"**: the hexSwap example does NOT refute it.
  3ξ is far from Binomial (z ≈ 84 already at L = 1; control 3·iid ≤ 6.2 with overlap-inflated
  variance).  But the dimension count is ~2(L+1) linear constraints against ~2^L freedom, so a
  single q is probably false (~20%).  The all-odd-q version is plausibly true (~70%) and may be
  classical, via Fourier inversion over odd multipliers.  Parked pending a literature check.
