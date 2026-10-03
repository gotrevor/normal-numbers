# Referee: `BakerBanajiAnalytic` + `IsSelfSimilarOnWindow` vs Baker–Banaji Cor. 2.10 (2026-10-02)

**Verdict: implied as published, 92%.  Not vacuous, not false.  No change to the Lean statement is needed**; two docstring additions are recommended (below).  Source: arXiv 2401.01241**v2** TeX, `c:analyticnormal` = **Corollary 2.10** in v2 (numbering per `docs/BAKER-BANAJI-ANALYTIC-REFEREE-2026-10-02.md`, which this reuses for the `q_n = bⁿ` → `IsAbsNormal` step and the `deriv (deriv F)` reading).

## BB Cor 2.10, exact hypotheses

Φ a **non-trivial** (no common fixed point) CIFS of similarities `φ_a(x) = r_a x + t_a`, `|r_a| ∈ (0,1)`, each mapping `[0,1] → [0,1]`, uniformly contracting; `p` a probability vector with **all `p_a > 0`** (standing assumption, TeX l.122); `Σ p_a|r_a|^{-τ} < ∞` for some `τ > 0`; μ the stationary measure; `F : [0,1] → ℝ` analytic and **not affine**.  Conclusion: `F_*μ` has Properties (A), (B), (C).  No open set condition, no separation, no homogeneity.  Proof uses only: `F'' ≢ 0` ⇒ finitely many zeros on `[0,1]`; μ non-atomic ⇒ `F'' ≠ 0` μ-a.e.; then Thm 2.8.

## Quantifier-by-quantifier

| Item | BB | Lean | Status |
|---|---|---|---|
| (a) maps | similarities, `0 < |r| < 1`, `[0,1] → [0,1]` | `r a ≠ 0 ∧ |r a| < 1`, window → window; negative ratios allowed in both | ✅ |
| (a) weights | positive, sum 1 | `0 < w a`, `Σ w = 1` (ENNReal; sum 1 forces each finite) | ✅ |
| (a) `Σ p|r|^{-τ}` | needed for countable Φ | finite `Fin n`, `r a ≠ 0` ⇒ automatic | ✅ |
| (a) OSC / non-atomic | neither assumed; non-atomicity is *derived* from non-triviality | not assumed | ✅ |
| (a) non-trivial | no common fixed point | `∃ a b, c a/(1−r a) ≠ c b/(1−r b)`; fixed point of `t ↦ rt+c` is `c/(1−r)` (`r ≠ 1`), so this is exactly "not all fixed points equal"; it also forces `n ≥ 2` | ✅ |
| (b) non-degeneracy | analytic, not affine on `[0,1]` | `AnalyticOnNhd F U`, U open ⊇ `[1/2,1]`; `∃ t ∈ [1/2,1], F''(t) ≠ 0` | ✅ see below |
| (c) measure | the unique stationary probability | `IsProbabilityMeasure ν` ∧ `ν = Σ w a • ν.map φ_a` | ✅ see below |
| (d) window | `[0,1]` | `[1/2,1]` via `A(s) = 1/2 + s/2` | ✅ see below |
| conclusion | (A) for all `q_n` with `inf(q_{n+1}−q_n) > 0` | `q_n = bⁿ`, countable `∩_b` ⇒ `IsAbsNormal` (`∀ b ≥ 2, IsNormal b`) | ✅ (prior referee) |

**(b) Non-degeneracy.**  Lean's hypothesis implies BB's: if `F''(t) ≠ 0` at some `t ∈ [1/2,1]` (endpoints included: `F''` is continuous on open U, so it is non-zero at interior points too), then `F∘A` is not affine on `[0,1]`.  The converse also holds (an analytic map on a neighbourhood of the connected `[1/2,1]` with `F'' ≡ 0` there is affine there), so no generality is lost.  The support being a proper (Cantor) subset of the window is harmless: `F''` has finitely many zeros on the window (identity theorem along the connected interval; U's other components are irrelevant), μ is non-atomic, so `F'' ≠ 0` μ-a.e., which is all BB's proof uses.  An "affine on the support, curved elsewhere" analytic F cannot exist: the support is uncountable and `F''` has finitely many window zeros.  Analyticity on a neighbourhood of the whole window matches BB's "analytic on `[0,1]`" (power series at every point); maps analytic only near the support are excluded by both, which is fine.

**(c) `IsSelfSimilarOnWindow` forces ν = BB's μ.**  The stationarity equation is linear, so `0`, `2μ` etc. solve it; `IsProbabilityMeasure` (in `BakerBanajiAnalytic`) excludes them.  Uniqueness among **all** Borel probabilities on ℝ (BB's footnote only covers measures on `[0,1]`): if `ν = Σ w_a φ_a ν`, iterate n times: `ν` = law of `φ_{a_1}∘…∘φ_{a_n}(X)`, `a_i` iid `w`, `X ~ ν` independent; since `|φ_{a_1…a_n}(X) − φ_{a_1…a_n}(x₀)| ≤ ρⁿ|X − x₀| → 0` pointwise (`ρ = max|r_a| < 1`, no moment condition needed), ν equals the law of the coding map `π(a)`, i.e. μ, which is supported in the window.  Non-vacuous: `ν_2` (below) and the `cantorReal` law are witnesses; Hutchinson gives existence for every admissible `(r, c, w)`.  Dirac masses are excluded: a Dirac `δ_x` is stationary only if every `φ_a` fixes `x`, which the `∃ a b` clause forbids.

**(d) Window.**  `A⁻¹∘φ_a∘A(s) = r_a s + (r_a + 2c_a − 1)`: same ratio, maps `[0,1] → [0,1]`, fixed points `A⁻¹(c_a/(1−r_a))` still distinct, same weights; `(A⁻¹)_*ν` is its stationary measure; `F∘A` analytic on `A⁻¹U ⊇ [0,1]`, `(F∘A)'' = F''∘A / 4`.  `ν`-a.e. `t` ⇔ `(A⁻¹)_*ν`-a.e. `s` with `t = A s`.  ✅

**(e) Vacuity / falsity.**  No counterexample class found.  Affine-in-disguise is ruled out by (b); Dirac by (c); `F` junk off U is never read (ν lives on the window).  `BakerBanajiAnalytic` is exactly BB Cor 2.10 restricted to finite IFSs on the window and `q_n = bⁿ`, so falsity would mean BB is wrong.

## Recommended docstring additions (no Lean change)

1. Cite "Corollary 2.10 (arXiv v2; label `c:analyticnormal`)".
2. Add to `IsSelfSimilarOnWindow`: "the stationary probability is unique among all Borel probabilities on ℝ (random-iteration contraction), so ν is BB's μ and lives on the window; the `∃ a b` clause is BB's non-triviality and excludes Dirac masses."

## Numeric tripwire: `probes/bakerbanaji_nuL_probe.py`

`ν_2`: `y = 2/4 + Σ_{i≥2} D_i 4^{-i}`, `D_i` iid uniform `{0,1,2}`; IFS `t ↦ t/4 + 3/8 + d/16`, fixed points `1/2, 7/12, 2/3`, weights `1/3`.  Exact average over all `3^N` digit prefixes, tail handled exactly through its characteristic function after linearising F (phase error ≈ 3e-8 at `ξ = 4^10`, `N = 11`; checked against `N = 13`).  Affine control `F = 4t`: hand value `|FT(4^k)| = Π_{j≥1}(1 − (4/3)sin²(π4^{-j})) = 0.31533` for every `k ≥ 1`.

| k | ξ = 4^k | `|F_*ν_2^(ξ)|`, F = √t | control F = 4t |
|---|---|---|---|
| 4 | 256 | 2.275e-02 | 0.31533 |
| 5 | 1024 | 1.742e-02 | 0.31533 |
| 6 | 4096 | 7.791e-04 | 0.31533 |
| 7 | 16384 | 1.799e-03 | 0.31533 |
| 8 | 65536 | 1.879e-03 | 0.31533 |
| 9 | 262144 | 1.369e-03 | 0.31533 |
| 10 | 1048576 | 6.158e-04 | 0.31533 |

Control matches the hand value to 5 digits at every ξ (no decay); √t sits two to three orders of magnitude below it and trends down, consistent with polynomial decay.  N = 11 and N = 13 agree to < 1e-6 at every ξ, far below the signal.  Assertions: convergence, control = hand value ± 2e-4, and `max_{k≥8} |FT_sqrt| < 0.2 × control` (fails on the control itself, so it has teeth).
