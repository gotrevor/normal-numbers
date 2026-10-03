# Referee: `BakerBanajiAnalyticQuarterCantor` + `BakerBanajiUniformQuarterCantor` vs Baker–Banaji (2026-10-02)

**Verdicts.**  (1) `BakerBanajiAnalyticQuarterCantor`: **implied as published**, 92%.  (2) `BakerBanajiUniformQuarterCantor`: **implied as published**, 93%.  Neither is vacuous.  Sources read in TeX: arXiv 2401.01241**v2** (`BakerBanajiArxiv2.tex`, 17 Jan 2025); Manai 2508.09319**v4** (2026-09-22) §1; Manai 2609.24665v1 (2026-09-21) Thm 2 + proof + `thm:BB`.

**Numbering.**  In arXiv v2, `c:analyticnormal` is **Corollary 2.10**, `t:normalpushforward` is Thm 2.8, `p:equi` is Prop 2.5, `t:self-similar` is Cor 1.5, `thm:Analytic pushforward thm` is Thm 1.1.  The Math. Ann. numbering was not checked, so cite the label alongside the number.

## (1) Corollary 2.10, exact

Φ is a **non-trivial** CIFS of **similarities** on `[0,1]` (no common fixed point; weights `p_a > 0`; `Σ p_a|r_a|^{-τ} < ∞`).  μ is its stationary measure, and `F : [0,1] → ℝ` is analytic (footnote: a power series at each point of `[0,1]`) and **not affine**.  Then `F_*μ` has Properties (A), (B), (C).  **Property (A)** (§2.3): for every positive real `(q_n)` with `inf (q_{n+1} − q_n) > 0`, `(q_n x)` is u.d. mod 1 for `F_*μ`-a.e. `x`.  The proof: `F'' ≢ 0` gives finitely many zeros on `[0,1]`; μ is non-atomic, so `F'' ≠ 0` μ-a.e.; then Thm 2.8 decomposes μ into cylinders where `F'' ≠ 0`, applies Thm 1.4 to each piece, and uses Prop 2.5 (DEL criterion).  There is no homogeneity or separation hypothesis.

| Item | BB Cor 2.10 | Lean (1) | Status |
|---|---|---|---|
| Measure | stationary, non-trivial similarity IFS on `[0,1]` | law of `cantorReal` = after `s = 2t−1`, `ψ_b(s) = s/4 + b/4`, weights 1/2, fixed points 0 ≠ 1/3 | ✅ (IFS check of the earlier referee re-done by hand) |
| Same ratio needed? | no (inhomogeneous allowed) | both ratios 1/4 | ✅ |
| Map class | analytic on `[0,1]`, non-affine **on `[0,1]`** | `AnalyticOnNhd F U`, U open ⊇ `[1/2,1]`; `∃ t ∈ [1/2,1], F''(t) ≠ 0` | ✅ `F∘A`, `A(s) = 1/2+s/2`, is analytic on `A⁻¹U ⊇ [0,1]`, and `(F∘A)''(s) = F''(A s)/4 ≠ 0` somewhere, so it is non-affine.  No identity theorem is needed on our side (BB uses it on the connected `[0,1]`), and a disconnected U is irrelevant |
| `deriv (deriv F)` | true `F''` | on open U, `deriv F` = `F'` near t, so `deriv (deriv F) t` = `F''(t)` | ✅ |
| Conclusion | Property (A), all admissible `(q_n)` | `q_n = bⁿ`: gap `bⁿ(b−1) ≥ 1` ✅ ⇒ `(bⁿF(y))` u.d. = `IsNormal b` (`isNormal_iff_equidistributed_orbit`, index shift harmless); countable `∩_{b≥2}` ⇒ `IsAbsNormal` | ✅ |
| a.e. transfer | `F_*μ`-a.e. x = μ-a.e. y | `∀ᵐ ω ∂coinMeasure` via `ae_of_ae_map` (no measurability of the predicate needed; F may be junk off U, and it is only read on `supp μ ⊂ [1/2,2/3]`) | ✅ |

**Downstream inhabitation.**  For `1 ≤ d = deg p < k`, `G_p(t) = Σ_{j≤d} a_j t^{j/k}` is analytic on `(0,∞)`.  The exponents `0, 1/k, …, d/k, 1` are distinct because `j ≠ k`, so `G_p` affine on `[1/2,1]` would force `a_j = 0` for all `j ≥ 1`: **no `p` with `1 ≤ deg p < k` gives an affine `G_p`**.  `exists_deriv2_Gk_ne_zero` is true as stated (97%).  The degree-`k` witness `X^k ↦ y` is non-normal for **every** `y` in the support: the binary digits of `y` never contain `11` after the leading `10`.  So `ae_mem_Omega` is sound given (1).

## (2) Cor 1.5 main clause, quantifiers

BB: `∃ η, κ, C > 0` (depending on μ only), `∀` `C²` `F` on `[0,1]` with `F'' ≠ 0` on `[0,1]`, `∀ ξ ≠ 0`: `|\hat{F_*μ}(ξ)| ≤ C(1 + M₁ + M₁^{-κ} + M₂)(1 + m₂^{-κ})|ξ|^{-η}`, where `M₁ = max|F'|`, `M₂ = max|F''|`, `m₂ = min|F''|`.  Lean has the same `∃∀` order.  `A₁ ≥ M₁`, `A₂ ≥ M₂` and `a₂ ≤ m₂` each enlarge the right side, and `a₁ ≤ |F'(t₀)| ≤ M₁` gives `a₁^{-κ} ≥ M₁^{-κ}`.  `a₂ > 0` forces `F'' ≠ 0` on the window.  Window: `M₁ → M₁/2`, `M₂ → M₂/4`, `m₂ → m₂/4`, so BB's bound is `≤ 2^κ·4^κ` times ours with the original norms; take `C_Lean = 8^κ C_BB`.  ✅ Faithful-or-weaker.

## Most dangerous mismatch

None is in the Props.  The live one is a **docstring claim** downstream of (2): "the derandomization only hard-codes rationals `C' ≥ C`, `η' ≤ η`, `κ' ≥ κ`".  The bound is **not monotone** in `κ` or `η`: `a^{-κ'} < a^{-κ}` when `a > 1`, and `|ξ|^{-η'} < |ξ|^{-η}` when `|ξ| < 1`.  **Repair:** use `x^{-κ} ≤ 1 + x^{-κ'}` (factor 2 per term, so `C' ≥ 4C`), and handle `|ξ| < 1` with `‖pushFourier‖ ≤ 1 ≤ C'` (so require `C' ≥ 1`).  Second, cosmetic: write "Corollary 2.10 (arXiv v2; label `c:analyticnormal`)".  Third, a shortcut: **BB Thm 1.1** (self-similar μ, `F` analytic non-affine ⇒ polynomial decay of `F_*μ`) proves `polyDecay_Gk` outright with non-effective constants.  Keep the 85% English proof only for the computable-constant need of `exists_computable_isAbsNormal_Gk`.

## Why Manai did not draw `Ω_k ≠ ∅`

It is an oversight, not a hidden obstruction (80%).  (a) His sentence reads the literature in the **forward** direction: "a non-normal `x` for which `φ(x)` is normal, `φ` a non-affine polynomial".  `Ω_k` needs the **reverse**: put the fractal on `y = x^k` and push forward by the countable family `p∘(·)^{1/k}`, which are analytic, not polynomial.  (b) His own 2609.24665 Thm 2 (posted 2026-09-21) does exactly the reverse trick for one map ("apply Theorem BB to a local inverse of `f`").  With `f = X²` plus Wall for degree 1, that already gives **`Ω₂ ≠ ∅`**.  Yet 2508.09319v4 (posted the next day, 2026-09-22) keeps "not even known", so the sentence is **stale at least for k = 2 by his own result**.  (c) For `k ≥ 3` his transcription `thm:BB` (`C²`, `F'' ≠ 0` throughout `[0,1]`) cannot treat all `p` at once, because the inflection points of the `G_p` are dense (`deriv2_Gk_three_eq_zero`).  The missing input is the analytic Cor 2.10 / Thm 1.1, which handles vanishing `F''`, and he does not quote it.  **Residual risk:** someone else may already have drawn this.  Run `papers followups 2508.09319` before claiming priority anywhere outward.
