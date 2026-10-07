# Referee: the exponent sets the normal profile

Subject: `CantorExactExponentProfile.exists_computable_normalProfile_of_baker`.  For rational `μ₀ > 2`,
it gives a computable `x ∈ K` with exact exponent `μ₀` that is normal to `b = 3ˢt` iff
`t > 3^{s(μ₀−1)}`, given `Literature.BakerLogDiscrepancyEff`.  One independent pass, started
fresh: an English check from the source, no build.  The inherited `CantorLiouvilleAll` and stretch
machinery was refereed earlier (`CANTOREXP-STRETCH-REFEREE-2026-10-06.md`).

## Verdict

**Accept.**  No wrong statement and no vacuous hypothesis.  The cited Prop is implied by the
literature.  Its docstring derivation was wrong (fixed); see below.

## The literature input

- Baker–Wüstholz (1993), two logarithms: `log|q log t − p log 3| ≥ −C log t · log 3 · log B`,
  `C` absolute.  Hence `‖q log₃ t‖ ≫ (q(α+1))^{−γ}`, with `γ = C' log t`.
- Erdős–Turán (Kuipers–Niederreiter Thm 2.5) with `H = N^{1/(γ+1)}` gives
  `N D_N ≪ (α+1)^γ N^{1−1/(γ+1)}`.  This is uniform in the shift `β` (exact invariance) and over
  intervals (a sup).
- The Prop asks for one `K` with `t^K N^{1−1/(Kt)}`.  The constant `exp(O(log t log log t))` is
  not `t^{O(1)}`, but it is absorbed.  The trivial bound covers `N ≤ t^{K²t}`, and beyond that
  the extra saving dominates once `K ≳ C'²`.  **Implied; the "faithful or weaker" label holds.**
- The old docstring claimed `|q log t − p log 3| ≥ q^{−C log t}` with no constant (false at
  `t = 4, q = p = 1`).  It dropped `log B` and cited "Baker 1966", whose bounds have the shape
  `exp(−(log B)^κ)`.  Rewritten.

## Lemma checks (all correct)

- `ProfileOK`, `profileOK_iff`, `ne_rpow_of_not_dvd`: the encoding is right and the threshold is
  never attained.  Examples: 12 (2.26), 15 (2.46), 21 (2.77); 6, 18 and 36 are never normal for
  `μ₀ > 2`.
- `not_isNormal_of_not_profileOK`: the run `[A, T)` gives `≥ c(n+1) − ℓ − 3` orbit points in
  `[0, b^{−ℓ})`, `c = 1 − log₃b/(sμ₀)`, which contradicts equidistribution.
- `pair_classify_expl` is the new idea, and it is sound.  A forced place in the low window puts the
  top window in the gap after the run (`a_{k+1} = (k+2)E_k`), where it is visible either directly
  or through the pair difference (`bf_le_topProd_of_dvd`).  The case split is exhaustive.
- `secondMoment_le_profile` / `sum_topProd_le_of`: a grid sampling of `z = 3^y`.  The total is
  `3N(2/3)^W + 4N(1/3)^W + 9|C| 9^W N^{1−κ}`, a power saving with `W = 3⌊log₃N/q⌋ + 1`.
- Derandomizer wiring: the effective input makes every constant primitive recursive in `b`.  The
  small-`m` constant (`exp(H log H)`) is absorbed by the polylog weight `profW`.  `K` and `J₀`
  come from existentials, so this is classical existence of a computable sequence (standard).

## Documentation (fixed in the same commit)

These were stale: confidence levels on proved results, the module header still calling the orbit
port viable, the English proofs drifting from the code (window width, two top shifts), and
constants in `secondMoment_profile_uniform`.  The `GelfondTwoLog` docstring's "1935" date is now
softened: Gelfond's quantitative two-log bounds, `exp(−(log B)^κ)`, are stronger than the Prop.
