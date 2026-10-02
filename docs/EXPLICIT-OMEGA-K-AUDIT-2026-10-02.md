# Manai's `Ω_k`: explicit points and dimension, audit 2026-10-02

Lean record: `src/NormalNumbers/ExplicitOmegaK.lean`, namespace `NormalNumbers.ExplicitOmegaK`.  This doc gives direction only; every claim below cites a declaration.

## Target, transcribed (Manai 2508.09319v4, Def. `def:deg` + Problem)

`deg_an x = inf {k ∈ ℕ : ∃ p ∈ ℤ[X], deg p = k, p(x) not normal}` (`∞` if empty), `Ω_k = {deg_an = k}` (`degAnSet`, `degAn`, `Omega`).  Three readings are forced by the paper.  First, "normal" means **absolutely** normal (§2), so it is `IsAbsNormal`.  Second, `ℕ = {1,2,…}`; otherwise every `x` has `deg_an = 0`.  Third, `x ∈ Ω_k` iff every `p` with `1 ≤ deg p < k` sends `x` to a normal number and some `p` of degree `k` does not (`mem_Omega_coe_iff`, `mem_Omega_of`, both proved).  Manai: *"It is not even known whether `Ω_k ≠ ∅` for `2 ≤ k`."*

## Verdict

- **Today's `x = √y` is not yet in `Ω₂`.**  `exists_computable_normal_sq_not_normal` gives base-2 normality only.  The cheap corollary is `exists_computable_mem_Omega_two`, with its wiring proved.  It is conditional on the refereed `ExplicitSquare.BakerBanajiQuarterCantor` plus one step, `exists_computable_isAbsNormal_sqrt_of_polyDecay`: an all-bases derandomization, 80%.  The degree-1 images are Wall in every base (`isAbsNormal_aeval_of_natDegree_eq_one`, proved).  Explicit `Ω₂`: **80%**.
- **`Ω_k ≠ ∅` for all `k ≥ 2`: 95%, essentially literature.**  Baker–Banaji Cor. `c:analyticnormal` (Math. Ann. 2025) gives a.e. absolute normality of `F(y)` for analytic non-affine `F` on a self-similar measure.  `G_p(t) = p(t^{1/k})` is non-affine whenever `1 ≤ deg p < k` (`exists_deriv2_Gk_ne_zero`, 96%).  Intersecting countably many `p` costs nothing, so `ae_mem_Omega` and `Omega_nonempty` are wired and proved from that cited input plus two routine sorries.  Manai cites BB25 but did not draw this conclusion.
- **`dim_H Ω_k = 1`: 80%** (`dimH_Omega_eq_one`, from the general self-similar `BakerBanajiAnalytic`).  The argument runs on measures `ν_L` (base-`2^L` digits avoiding the top digit, `dim → 1`) and uses the mass distribution principle.
- **Explicit `x_k = y^{1/k} ∈ Ω_k` for every `k ≥ 2`: 65%** (`exists_computable_mem_Omega`, wiring proved).

## Difficulty check

1. **What is proved.**  The definitions and their criterion.  Wall in degree 1.  The `Ω₂`, `Ω_k`, a.e. and nonempty wiring.  The witness `X^k` (`top_witness`, `rootK_pow`).  The sibling `Gk_X_pow`: `G_{X^k}` is the identity on the non-normal Cantor set.
2. **What is unproved.**  For `k = 2`, `G_p'' ≠ 0` everywhere, and the existing single-map mechanism suffices.  **For `k ≥ 3` that mechanism is closed.**  The inflection points `t = (m/n)³` of `nX² − mX` are dense (`deriv2_Gk_three_eq_zero`), so no single cylinder avoids them all.  The explicit route therefore needs **global decay across inflection points**, `polyDecay_Gk` (85%).  That step cuts `μ` at depth `m ≍ ε log|ξ|` and discards cylinders within `r = |ξ|^{-ε}` of the finitely many zeros of finite order.  It then applies BB Cor 1.5's **explicit** `min|F''|^{-κ}` constant on the rest, which is why `BakerBanajiUniformQuarterCantor` is needed rather than the per-map form.
3. **The mechanism.**  BLD/Becher–Figueira derandomization (`Derandomize.exists_primrec_avoid`), run over `(p, b, level)` with computable admission thresholds.
4. **The sibling test.**  The affine sibling (`p = aX^k + b`, `deg p = k`) fails as it must, through `not_polyDecay_rat_affine`.

## Hardest step

`exists_computable_isAbsNormal_Gk` (70%) is computability engineering.  It needs:
- per-`p` decay constants that are computable from the coefficient list, which requires root isolation for `min|G_p''|` off the inflection points;
- a sandwich test for bases that are not powers of 2, because `⌊G_p(y)bᵐ⌋` is not a finite-prefix function;
- admission thresholds that keep the total mass `≤ 1/4`.

## Cited Props (all faithful-or-weaker, against 2401.01241v2 read today)

- `BakerBanajiAnalyticQuarterCantor` is Cor. `c:analyticnormal`, Property (A) with `q_n = bⁿ`, for the law of `cantorReal` (92%).
- `BakerBanajiUniformQuarterCantor` is Cor 1.5's main clause with the explicit constant.  It quantifies over bounds `A₁, a₁, A₂, a₂`, and the window rescaling is absorbed into `C` (90%).  It implies today's Prop (`bakerBanajiQuarterCantor_of_uniform`, 97%).
- `BakerBanajiAnalytic` is the general self-similar `c:analyticnormal` (`IsSelfSimilarOnWindow`), and it implies the quarter-Cantor form (`bakerBanajiAnalyticQuarterCantor_of_general`, 95%).

**Freshness.**  Newest versions read: 2508.09319v4 (2026-09-22) and 2609.24665v1.  `papers followups 2508.09319` lists only Manai's own 2609.24665, 2606.08325 and 2506.15422.  `papers followups 2609.24665` lists only 2508.09319.  None of them mentions `Ω_k`, the normality degree or Hausdorff dimension; 2606.08325 was grepped and is clean.  2609.24665 `thm:2` uses only BB's `F'' ≠ 0` clause, restricted to an interval.

## Treadmill objective

> In `ExplicitOmegaK.lean`, first close the routine steps: `analyticOnNhd_Gk`, `exists_deriv2_Gk_ne_zero`, `deriv2_Gk_three_eq_zero` and `bakerBanajiQuarterCantor_of_uniform`.  `Omega_nonempty` then depends only on `BakerBanajiAnalyticQuarterCantor`.  Next, `exists_computable_isAbsNormal_sqrt_of_polyDecay`, generalizing `ComputableNormal` to base `b` with a sandwich test; that makes `exists_computable_mem_Omega_two` depend only on `BakerBanajiQuarterCantor`.  A refutation of any step is an advance.

`--require-decls NormalNumbers.ExplicitOmegaK.Omega_nonempty,NormalNumbers.ExplicitOmegaK.ae_mem_Omega,NormalNumbers.ExplicitOmegaK.exists_computable_mem_Omega_two,NormalNumbers.ExplicitOmegaK.exists_computable_mem_Omega,NormalNumbers.ExplicitOmegaK.mem_Omega_coe_iff,NormalNumbers.ExplicitOmegaK.BakerBanajiAnalyticQuarterCantor,NormalNumbers.ExplicitOmegaK.BakerBanajiUniformQuarterCantor,NormalNumbers.ExplicitOmegaK.exists_deriv2_Gk_ne_zero,NormalNumbers.ExplicitOmegaK.exists_computable_isAbsNormal_sqrt_of_polyDecay`

`polyDecay_Gk`, `exists_computable_isAbsNormal_Gk` and `dimH_Omega_eq_one` are second-phase work.
