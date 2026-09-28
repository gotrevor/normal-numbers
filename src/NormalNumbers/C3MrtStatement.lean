/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtDyadicInput
import NormalNumbers.SwingC3Statement

/-!
# The audit surface for the C3/MRT reduction

`conjC3_of_dyadic_input` is restated here with **every** abbreviation of the chain unwound: no
`ConjC3`, no `IsRich`, no `WeylLambertTwist`, no `DepthDyadicBound`, no `depthRoot`, no `ee`,
no `omegaNat`, no `cKgeom`, no `CstKdeg`, no `Filter.Eventually`.  An auditor reads only
`Nat.primeFactors`, `Complex.exp`, `Real.log`, `Real.exp`, an rpow, a `tsum`, `⌊·⌋`,
`Int.fract` and a `Finset.card` density.

In words:

> Fix `c₀ > 0`, `0 < θ < 1`, `m : ℕ`.  Suppose that for every base `b ≥ 3` and every integer
> `h'` not divisible by `b`, there is a `K₀` such that for all `K ≥ K₀`, all saving exponents
> `κ ∈ (0,1]`, all `N ≥ 2` with `max 2 (K+1) ≤ (2 log N)^{κ c₀ b^{-θK}}`, and all moduli
> `0 < M ≤ (2 log N)^{κ c₀ b^{-θK}}` and residues `r`,
>
>     ‖ ∑_{N < n ≤ 2N, n ≡ r (M)} ∏_{i<K} e(h'/b^{i+1})^{ω(n+i+1)} ‖
>         ≤ exp((K+1)^m) · (2 log N)^{-κ c₀ b^{-θK}} · N / M ,
>
> where `ω(n) = #{p prime : p ∣ n}` and `e(x) = exp(2πix)`.  Then for every `b ≥ 3` the prime
> Lambert number `G_b = ∑_n ω(n) b^{-n}` is RICH in base `b`: every finite word over
> `{0,…,b−1}` occurs in its base-`b` expansion at a set of positions of positive lower density.

**What this audit form assumes that the sharp theorem does not.**  `conjC3_of_dyadic_input`
needs the bound at the single exponent `κ = ttExponent (depthRoot b h' 0)` — the archimedean
saving of the LEADING depth root.  Quantifying `∀ κ ∈ (0,1]` here assumes strictly more, and is
done only to keep `ttEps` / `resEps` out of the audit surface.  `conjC3_of_dyadic_input` itself
is the sharp statement; `audit_conjC3_of_dyadic_input` is the reader-facing upper bound on what
is assumed.

**Ledger.**  The hypothesis is 🔴 OPEN and strictly stronger than the literature.  It is the
`K`-point Elliott-type bound of Tao–Teräväinen (arXiv 2512.01739, Thm 3.1(ii)) with the
exceptional set of scales deleted, specialised to the one family `n ↦ e(h'/b^{i+1})^{ω(n)}`,
and needed only in the large-`K` regime — which print does not reach at all (TT state triple
correlations are "not within current technology").  It is NOT a published result at any `K`,
`K = 2` included.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- **The audit hypothesis is not vacuous.**  For every `K` and every positive saving exponent
`s` the threshold `max 2 (K+1) ≤ (2 log N)^s` holds for all large `N`, so the displayed bound is
being asserted about genuinely many sums — it is not satisfied by an empty range of `N`. -/
theorem dyadic_threshold_satisfiable (K : ℕ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ N : ℕ in atTop, max 2 ((K : ℝ) + 1) ≤ (2 * Real.log N) ^ s := by
  have hlog : Tendsto (fun N : ℕ => 2 * Real.log N) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num)
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact ((_root_.tendsto_rpow_atTop hs).comp hlog).eventually_ge_atTop _

open Classical in
/-- **Audit form of the C3/MRT reduction.**  Every definition of the chain unfolded. -/
theorem audit_conjC3_of_dyadic_input {c₀ θ : ℝ} (hc₀ : 0 < c₀) (hθ0 : 0 < θ) (hθ : θ < 1)
    (m : ℕ)
    (H : ∀ b : ℕ, 3 ≤ b → ∀ h' : ℤ, ¬ ((b : ℤ) ∣ h') → ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      ∀ κ : ℝ, 0 < κ → κ ≤ 1 →
      ∀ N : ℕ, 2 ≤ N →
        max 2 ((K : ℝ) + 1) ≤ (2 * Real.log N) ^ (κ * (c₀ * (b : ℝ) ^ (-(θ * K)))) →
        ∀ M r : ℕ, 0 < M →
          (M : ℝ) ≤ (2 * Real.log N) ^ (κ * (c₀ * (b : ℝ) ^ (-(θ * K)))) →
          ‖∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
              ∏ i : Fin K,
                Complex.exp (2 * Real.pi * Complex.I *
                    ((((h' : ℝ) / (b : ℝ) ^ ((i : ℕ) + 1) : ℝ)) : ℂ))
                  ^ (n + (i : ℕ) + 1).primeFactors.card‖
            ≤ Real.exp (((K : ℝ) + 1) ^ m)
                * (2 * Real.log N) ^ (-(κ * (c₀ * (b : ℝ) ^ (-(θ * K)))))
                * (N : ℝ) / (M : ℝ)) :
    ∀ b : ℕ, 3 ≤ b → ∀ w : List ℕ, (∀ d ∈ w, d < b) → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N in atTop, c * N ≤ (((range N).filter (fun n =>
        ∀ j (hj : j < w.length),
          (⌊Int.fract (∑' k : ℕ,
              (ArithmeticFunction.cardDistinctFactors k : ℝ) / (b : ℝ) ^ k)
            * (b : ℝ) ^ (n + j + 1)⌋).toNat % b = w[j])).card : ℝ) := by
  have key : ConjC3 := by
    refine conjC3_of_dyadic_input hc₀ hθ0 hθ m fun b hb h' hh' => ?_
    obtain ⟨K₀, hK₀⟩ := H b hb h' hh'
    have hb0 : 0 < b := by omega
    have hznorm : ‖depthRoot b h' 0‖ = 1 := norm_ee_real _
    have hz1 : depthRoot b h' 0 ≠ 1 := depthRoot_ne_one_of_not_dvd hb0 hh'
    refine Filter.eventually_atTop.2 ⟨K₀, fun K hK => ?_⟩
    exact hK₀ K hK _ (ttExponent_pos hznorm hz1) (ttExponent_le_one hznorm)
  intro b hb w hw
  obtain ⟨c, hc, hN⟩ := key b hb w hw
  refine ⟨c, hc, hN.mono fun N hle => ?_⟩
  refine le_trans hle (le_of_eq ?_)
  congr 2
  exact Finset.filter_congr (fun n _ => Iff.rfl)

#print axioms NormalNumbers.CastingOut.dyadic_threshold_satisfiable
#print axioms NormalNumbers.CastingOut.audit_conjC3_of_dyadic_input

end NormalNumbers.CastingOut
