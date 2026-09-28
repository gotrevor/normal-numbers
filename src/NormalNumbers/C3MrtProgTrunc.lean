/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtProgForms

/-!
# The `K`-fold truncation over an arbitrary index set

Brick 2 of obligation A (`ProgressionLogRung`, `C3MrtNatural`).

**The whole brick is a specialisation, not a new estimate.**  `multi_truncation_telescope`
(lap 43) was already stated for an arbitrary `S : Finset ℕ` with `∀ n ∈ S, n < N` — the two-term
block-mass invariant it carries never looks at the shape of `S`.  And
`joint_multi_harmonic_mass` (lap 42) likewise takes an arbitrary `S`.  So the *only* thing that
tied `multi_truncation_bound` to `range N` was its own statement.

`multi_truncation_bound_set` removes that tie: the same bound

    ‖(∑_{n ∈ S} F n ∏_i z_i^{ω(n+i+1)}) − ∑_d (∏ sqfW) ∑_{n ∈ S, d-class} …‖
      ≤ K·truncA + (1 + log N)·K^{K²}·truncB

holds for every `S ⊆ range N`.  `multi_truncation_bound` is `S = range N`;
`multi_truncation_bound_prog` is `S = {n < N : n ≡ n₀ (mod M)}`, which is what
`ProgressionLogRung` needs.

Recorded because it was NOT obvious a priori: the progression could have cost a new mass
estimate (the class mod `M` intersects each `d`-class in a class mod `lcm(M, lcm d)`, so the
*individual* masses shrink), but the bound is monotone in `S`, so nothing is needed — the
larger-modulus gain of `C3MrtProgForms` is available but unused here.
-/

open Finset

namespace NormalNumbers

namespace CastingOut

/-- **The `K`-fold truncation bound over an arbitrary index set `S ⊆ range N`.**
`multi_truncation_bound` with `range N` replaced by any `S` below `N`. -/
theorem multi_truncation_bound_set (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) {F : ℕ → ℂ}
    (hF : ∀ n : ℕ, ‖F n‖ ≤ ((n : ℝ) + 1)⁻¹) (K N Y : ℕ) (hK : 0 < K)
    (S : Finset ℕ) (hSN : ∀ n ∈ S, n < N) :
    ‖(∑ n ∈ S, F n * ∏ i : Fin K, (z i) ^ omegaNat (n + i + 1))
        - ∑ d ∈ Fintype.piFinset (fun _ : Fin K => range (Y + 1)),
            (∏ i : Fin K, sqfW (z i) (d i)) *
              ∑ n ∈ S.filter (fun n => ∀ i : Fin K, d i ∣ n + i + 1),
                F n * ∏ i : Fin K,
                  (z i) ^ ArithmeticFunction.cardFactors ((n + i + 1) / d i)‖
      ≤ (K : ℝ) * truncA z Y K
        + ((1 + Real.log N) * (K : ℝ) ^ (K * K)) * truncB z Y K := by
  classical
  have hKR : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_natCast_nonneg N
  refine multi_truncation_telescope z hz N Y K F S (K : ℝ)
    ((1 + Real.log N) * (K : ℝ) ^ (K * K)) hKR (by positivity) hSN ?_
  intro r hr1 hrK g hg
  have hmass := joint_multi_harmonic_mass (F := F) hF
    (S := S.filter (fun n => ∀ s, s < r → g s ∣ n + (K - r) + s + 1))
    (M := N) (m := K - r) (K := r)
    (fun n hn => hSN n (Finset.mem_filter.1 hn).1) (by omega) g hg
    (fun n hn s hs => (Finset.mem_filter.1 hn).2 s hs)
  refine hmass.trans (add_le_add ?_ ?_)
  · refine div_le_div_of_nonneg_right ?_ ?_
    · have : (K - r : ℕ) + 1 ≤ K := by omega
      exact_mod_cast (by exact_mod_cast this : ((K - r : ℕ) : ℝ) + 1 ≤ (K : ℝ))
    · exact Nat.cast_nonneg _
  · refine div_le_div_of_nonneg_right ?_ ?_
    · have hpow : (r : ℝ) ^ (r * r) ≤ (K : ℝ) ^ (K * K) := by
        have h1 : (r : ℕ) ^ (r * r) ≤ K ^ (K * K) := by
          calc r ^ (r * r) ≤ K ^ (r * r) := Nat.pow_le_pow_left hrK _
            _ ≤ K ^ (K * K) := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul hrK hrK)
        exact_mod_cast h1
      have h1 : (0 : ℝ) ≤ 1 + Real.log N := by linarith
      exact mul_le_mul_of_nonneg_left hpow h1
    · exact Finset.prod_nonneg fun s _ => Nat.cast_nonneg _

open scoped Classical in
/-- **The progression case**, in the shape `ProgressionLogRung` needs: `S` is the part of
`range N` in a fixed class mod `Mo`. -/
theorem multi_truncation_bound_prog (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) {F : ℕ → ℂ}
    (hF : ∀ n : ℕ, ‖F n‖ ≤ ((n : ℝ) + 1)⁻¹) (K N Y : ℕ) (hK : 0 < K) (Mo n₀ : ℕ) :
    ‖(∑ n ∈ (range N).filter (fun n => n ≡ n₀ [MOD Mo]),
            F n * ∏ i : Fin K, (z i) ^ omegaNat (n + i + 1))
        - ∑ d ∈ Fintype.piFinset (fun _ : Fin K => range (Y + 1)),
            (∏ i : Fin K, sqfW (z i) (d i)) *
              ∑ n ∈ ((range N).filter (fun n => n ≡ n₀ [MOD Mo])).filter
                    (fun n => ∀ i : Fin K, d i ∣ n + i + 1),
                F n * ∏ i : Fin K,
                  (z i) ^ ArithmeticFunction.cardFactors ((n + i + 1) / d i)‖
      ≤ (K : ℝ) * truncA z Y K
        + ((1 + Real.log N) * (K : ℝ) ^ (K * K)) * truncB z Y K :=
  multi_truncation_bound_set z hz hF K N Y hK _
    (fun n hn => Finset.mem_range.1 (Finset.mem_filter.1 hn).1)

#print axioms multi_truncation_bound_set
#print axioms multi_truncation_bound_prog

end CastingOut

end NormalNumbers
