/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtProgTrunc
import NormalNumbers.C3MrtMultiInner

/-!
# The inner layer along an extra progression — brick 3 of obligation A

`inner_multi_bound_prog` is `inner_multi_bound` with the index set intersected with a fixed class
mod `Mo`, i.e. with `L = Finset.univ.lcm d` replaced by `L' = progLcm Mo d = lcm(Mo, lcm d)`.
Every ingredient survives:

* `inner_sum_prog_forms` (lap 56) supplies the class and the reindexing `n = L'·j + a`;
* `inner_harmonic_le_generic` / `window_gap_generic` / `progression_sum_bound_generic` (lap 46)
  were deliberately stated *generic in the modulus*, so they take `L'` verbatim;
* `multi_rung_spelling` needs only `0 < L'/d i`, which `dvd_progLcm` gives.

`multi_bound_of_rung_prog` then assembles brick 2 + `multi_full_sum_bound` + this.  **`
multi_full_sum_bound` needs no change at all**: it consumes a per-tuple bound
`‖Inner d‖ ≤ 1 + R/lcm(d)`, and what brick 3 delivers is `1 + R/L'` with `L' ≥ lcm(d)` — i.e. the
progression version is *stronger* than what the tuple sum asks for.  That is the payoff of lap
56's observation that nothing needs `L` to be least.
-/

open Finset

namespace NormalNumbers

namespace CastingOut

open scoped Classical in
/-- **The per-tuple bound along an extra progression.**  `inner_multi_bound` with `lcm(d)`
replaced by `progLcm Mo d`. -/
theorem inner_multi_bound_prog_witness {K N A : ℕ} {Mo : ℕ} (hMo : 0 < Mo) (z : ℕ → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (d : Fin K → ℕ) (hd : ∀ i, 0 < d i) {n₀ : ℕ}
    (hn₀ : ∀ i : Fin K, d i ∣ n₀ + (i : ℕ) + 1) (hA : 2 ≤ A) {R : ℝ} (hR0 : 0 ≤ R)
    (hrung : ∀ a : ℕ, a < progLcm Mo d → (∀ i : Fin K, d i ∣ a + (i : ℕ) + 1) →
      ‖∑ j ∈ Finset.Ioc 0 (A ^ Nat.log A ((N - 1 - a) / progLcm Mo d)),
          (Erdos67b.harmonicWeight j : ℂ) *
            ∏ i : Fin K, zOmInt (z i)
              (Erdos67b.integerAffine (progLcm Mo d / d i)
                (((a + (i : ℕ) + 1) / d i : ℕ) : ℤ) j)‖ ≤ R) :
    ‖∑ n ∈ (range N).filter
          (fun n => n ≡ n₀ [MOD Mo] ∧ ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1),
        harmW n * ∏ i : Fin K, (z i) ^ ArithmeticFunction.cardFactors ((n + (i : ℕ) + 1) / d i)‖
      ≤ 1 + (3 + R + Real.log A) / ((progLcm Mo d : ℕ) : ℝ) := by
  classical
  set L : ℕ := progLcm Mo d with hLdef
  have hL : 0 < L := progLcm_pos hMo d hd
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hlogA : 0 ≤ Real.log A := Real.log_natCast_nonneg A
  have hRHS : 0 ≤ (3 + R + Real.log A) / (L : ℝ) := by positivity
  obtain ⟨a, haL, _haM, hadvd, heq⟩ := inner_sum_prog_forms (N := N) hMo d hd hn₀ z harmW
  rw [heq]
  by_cases haN : a < N
  · rw [filter_linear_lt_eq_range hL haN]
    set J := (N - 1 - a) / L with hJ
    set G : ℕ → ℂ := fun j =>
      ∏ i : Fin K, (z i) ^ ArithmeticFunction.cardFactors ((L / d i) * j + (a + (i : ℕ) + 1) / d i)
      with hG
    have hGnorm : ∀ j, ‖G j‖ ≤ 1 := by
      intro j
      rw [hG]
      simp only []
      rw [norm_prod]
      refine le_of_eq ?_
      refine Finset.prod_eq_one fun i _ => ?_
      rw [norm_pow, hz i, one_pow]
    have hrw : ∑ j ∈ Finset.range (J + 1), harmW (L * j + a) * G j
        = ∑ j ∈ Finset.range (J + 1), ((((L * j + a : ℕ) : ℝ) + 1)⁻¹ : ℝ) • G j :=
      Finset.sum_congr rfl fun j _ => harmW_smul _ _
    show ‖∑ j ∈ Finset.range (J + 1), harmW (L * j + a) * G j‖ ≤ _
    rw [hrw]
    rcases Nat.eq_zero_or_pos J with hJ0 | hJ1
    · rw [hJ0]
      have hone : Finset.range (0 + 1) = ({0} : Finset ℕ) := by
        ext j; simp only [Finset.mem_range, Finset.mem_singleton]; omega
      rw [hone, Finset.sum_singleton]
      have hnorm : ‖((((L * 0 + a : ℕ) : ℝ) + 1)⁻¹ : ℝ) • G 0‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h1 : (((L * 0 + a : ℕ) : ℝ) + 1)⁻¹ ≤ 1 := by
          rw [inv_le_one_iff₀]
          right
          have : (0 : ℝ) ≤ ((L * 0 + a : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
        calc (((L * 0 + a : ℕ) : ℝ) + 1)⁻¹ * ‖G 0‖
            ≤ 1 * 1 := mul_le_mul h1 (hGnorm 0) (norm_nonneg _) zero_le_one
          _ = 1 := by ring
      linarith
    · have hspell := multi_rung_spelling z (fun i => L / d i)
        (fun i => (a + (i : ℕ) + 1) / d i)
        (fun i => Nat.div_pos (Nat.le_of_dvd hL (dvd_progLcm Mo d i)) (hd i))
        (A ^ Nat.log A J)
      have hrung' : ‖∑ j ∈ Finset.Ioc 0 (A ^ Nat.log A J), (((j : ℝ))⁻¹ : ℝ) • G j‖ ≤ R := by
        rw [hG]
        simp only []
        rw [hspell]
        exact hrung a haL hadvd
      have hbound := progression_sum_bound_generic (L := L) (a := a) (A := A) (J := J)
        hL (by omega) hA hJ1 G hGnorm hrung'
      refine le_trans hbound ?_
      have h1 : ((a : ℝ) + 1)⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]
        right
        have : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
        linarith
      have heq2 : 2 / (L : ℝ) + (L : ℝ)⁻¹ * (R + (1 + Real.log A))
          = (3 + R + Real.log A) / (L : ℝ) := by
        field_simp
        ring
      linarith
  · have hempty : (Finset.range N).filter (fun j => L * j + a < N) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun j hj => ?_
      have := (Finset.mem_filter.1 hj).2
      omega
    rw [hempty, Finset.sum_empty, norm_zero]
    linarith


open scoped Classical in
/-- **The per-tuple bound along the class of an arbitrary `r`.**  If the progression class of `r`
mod `Mo` and the joint `d`-class have a common solution, `inner_multi_bound_prog_witness` applies at
that solution; otherwise the index set is empty and the bound is trivial. -/
theorem inner_multi_bound_prog {K N A : ℕ} {Mo : ℕ} (hMo : 0 < Mo) (z : ℕ → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (d : Fin K → ℕ) (hd : ∀ i, 0 < d i) (r : ℕ)
    (hA : 2 ≤ A) {R : ℝ} (hR0 : 0 ≤ R)
    (hrung : ∀ a : ℕ, a < progLcm Mo d → (∀ i : Fin K, d i ∣ a + (i : ℕ) + 1) →
      ‖∑ j ∈ Finset.Ioc 0 (A ^ Nat.log A ((N - 1 - a) / progLcm Mo d)),
          (Erdos67b.harmonicWeight j : ℂ) *
            ∏ i : Fin K, zOmInt (z i)
              (Erdos67b.integerAffine (progLcm Mo d / d i)
                (((a + (i : ℕ) + 1) / d i : ℕ) : ℤ) j)‖ ≤ R) :
    ‖∑ n ∈ (range N).filter
          (fun n => n ≡ r [MOD Mo] ∧ ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1),
        harmW n * ∏ i : Fin K, (z i) ^ ArithmeticFunction.cardFactors ((n + (i : ℕ) + 1) / d i)‖
      ≤ 1 + (3 + R + Real.log A) / ((progLcm Mo d : ℕ) : ℝ) := by
  classical
  have hlogA : 0 ≤ Real.log A := Real.log_natCast_nonneg A
  have hL : 0 < progLcm Mo d := progLcm_pos hMo d hd
  have hLR : (0 : ℝ) < ((progLcm Mo d : ℕ) : ℝ) := by exact_mod_cast hL
  by_cases hex : ∃ n₀ : ℕ, n₀ ≡ r [MOD Mo] ∧ ∀ i : Fin K, d i ∣ n₀ + (i : ℕ) + 1
  · obtain ⟨n₀, hn₀r, hn₀d⟩ := hex
    have hpred : (range N).filter
          (fun n => n ≡ r [MOD Mo] ∧ ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1)
        = (range N).filter
          (fun n => n ≡ n₀ [MOD Mo] ∧ ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1) := by
      refine Finset.filter_congr fun n _ => ?_
      exact ⟨fun h => ⟨h.1.trans hn₀r.symm, h.2⟩, fun h => ⟨h.1.trans hn₀r, h.2⟩⟩
    rw [hpred]
    exact inner_multi_bound_prog_witness hMo z hz d hd hn₀d hA hR0 hrung
  · have hempty : (range N).filter
        (fun n => n ≡ r [MOD Mo] ∧ ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun n hn => ?_
      exact absurd ⟨n, (Finset.mem_filter.1 hn).2⟩ hex
    rw [hempty, Finset.sum_empty, norm_zero]
    positivity

open scoped Classical in
/-- **The `K`-fold correlation along a progression, bounded by the rung.**
`multi_bound_of_rung` with `range N` replaced by the class of `n₀` mod `Mo`.  Note
`multi_full_sum_bound` is used UNCHANGED: brick 3's per-tuple bound has `progLcm Mo d ≥ lcm d`
in the denominator, which is stronger than what it asks for. -/
theorem multi_bound_of_rung_prog {K : ℕ} (hK : 0 < K) {Mo : ℕ} (hMo : 0 < Mo) (n₀ : ℕ)
    (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (Y N A : ℕ) (hA : 2 ≤ A) {R : ℝ} (hR0 : 0 ≤ R)
    (hrung : ∀ d : Fin K → ℕ, (∀ i, d i ≤ Y) → (∀ i, 0 < d i) →
      (∃ n : ℕ, ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1) →
      ∀ a : ℕ, a < progLcm Mo d → (∀ i : Fin K, d i ∣ a + (i : ℕ) + 1) →
        ‖∑ j ∈ Finset.Ioc 0 (A ^ Nat.log A ((N - 1 - a) / progLcm Mo d)),
            (Erdos67b.harmonicWeight j : ℂ) *
              ∏ i : Fin K, zOmInt (z i)
                (Erdos67b.integerAffine (progLcm Mo d / d i)
                  (((a + (i : ℕ) + 1) / d i : ℕ) : ℤ) j)‖ ≤ R) :
    ‖∑ n ∈ (range N).filter (fun n => n ≡ n₀ [MOD Mo]),
        harmW n * ∏ i : Fin K, (z i) ^ omegaNat (n + (i : ℕ) + 1)‖
      ≤ ((K : ℝ) * truncA z Y K + ((1 + Real.log N) * (K : ℝ) ^ (K * K)) * truncB z Y K)
        + ((∏ i : Fin K, sqfWPartial (z i) Y)
          + (3 + R + Real.log A) * ((K : ℝ) ^ (K * K) * ∏ i : Fin K, sqfWMass (z i))) := by
  classical
  have hF : ∀ n : ℕ, ‖harmW n‖ ≤ ((n : ℝ) + 1)⁻¹ := fun n => le_of_eq (norm_harmW n)
  set S : Finset ℕ := (range N).filter (fun n => n ≡ n₀ [MOD Mo]) with hS
  set Inner : (Fin K → ℕ) → ℂ := fun d =>
    ∑ n ∈ S.filter (fun n => ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1),
      harmW n * ∏ i : Fin K, (z i) ^ ArithmeticFunction.cardFactors ((n + (i : ℕ) + 1) / d i)
    with hInner
  set sol : (Fin K → ℕ) → Prop := fun d =>
    (∀ i, 0 < d i) ∧ ∃ n : ℕ, ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1 with hsolDef
  have htrunc := multi_truncation_bound_set z hz hF K N Y hK S
    (fun n hn => Finset.mem_range.1 (Finset.mem_filter.1 hn).1)
  have hlogA : 0 ≤ Real.log A := Real.log_natCast_nonneg A
  -- the filter rewrite: `S.filter dclass = (range N).filter (prog ∧ dclass)`
  have hrefil : ∀ d : Fin K → ℕ,
      S.filter (fun n => ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1)
        = (range N).filter
            (fun n => n ≡ n₀ [MOD Mo] ∧ ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1) := by
    intro d
    rw [hS, Finset.filter_filter]
  have hfull := multi_full_sum_bound (K := K) z hz Y Inner
    (R := 3 + R + Real.log A) (by linarith) sol
    (fun d h => ⟨h.1, h.2⟩)
    (fun d _ hns => by
      rw [hInner]
      simp only []
      by_cases hpos : ∀ i, 0 < d i
      · refine Finset.sum_eq_zero fun n hn => ?_
        exact absurd ⟨hpos, ⟨n, (Finset.mem_filter.1 hn).2⟩⟩ hns
      · push_neg at hpos
        obtain ⟨i, hi⟩ := hpos
        have hi0 : d i = 0 := by omega
        refine Finset.sum_eq_zero fun n hn => ?_
        have := (Finset.mem_filter.1 hn).2 i
        rw [hi0] at this
        simp only [Nat.zero_dvd] at this
        omega)
    (fun d hd h => by
      obtain ⟨hpos, n, hn⟩ := h
      have hdY : ∀ i, d i ≤ Y := by
        intro i
        have := Fintype.mem_piFinset.1 hd i
        have := Finset.mem_range.1 this
        omega
      have hbd := inner_multi_bound_prog (N := N) (A := A) hMo z hz d hpos n₀ hA hR0
        (hrung d hdY hpos ⟨n, hn⟩)
      have hkey : ‖Inner d‖ ≤ 1 + (3 + R + Real.log A) / ((progLcm Mo d : ℕ) : ℝ) := by
        rw [hInner]
        simp only []
        rw [hrefil d]
        exact hbd
      refine hkey.trans ?_
      have hlcmdvd : (Finset.univ : Finset (Fin K)).lcm d ∣ progLcm Mo d :=
        Nat.dvd_lcm_right _ _
      have hlcmpos : (0 : ℝ) < (((Finset.univ : Finset (Fin K)).lcm d : ℕ) : ℝ) := by
        exact_mod_cast univLcm_pos d hpos
      have hle : (((Finset.univ : Finset (Fin K)).lcm d : ℕ) : ℝ) ≤ ((progLcm Mo d : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_of_dvd (progLcm_pos hMo d hpos) hlcmdvd
      have hstep : (3 + R + Real.log A) / ((progLcm Mo d : ℕ) : ℝ)
          ≤ (3 + R + Real.log A) / (((Finset.univ : Finset (Fin K)).lcm d : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (by linarith) hlcmpos hle
      linarith)
  have htri : ‖∑ n ∈ S, harmW n * ∏ i : Fin K, (z i) ^ omegaNat (n + (i : ℕ) + 1)‖
      ≤ ‖(∑ n ∈ S, harmW n * ∏ i : Fin K, (z i) ^ omegaNat (n + (i : ℕ) + 1))
          - ∑ d ∈ Fintype.piFinset (fun _ : Fin K => range (Y + 1)),
              (∏ i : Fin K, sqfW (z i) (d i)) * Inner d‖
        + ‖∑ d ∈ Fintype.piFinset (fun _ : Fin K => range (Y + 1)),
              (∏ i : Fin K, sqfW (z i) (d i)) * Inner d‖ := by
    have := norm_add_le
      ((∑ n ∈ S, harmW n * ∏ i : Fin K, (z i) ^ omegaNat (n + (i : ℕ) + 1))
        - ∑ d ∈ Fintype.piFinset (fun _ : Fin K => range (Y + 1)),
            (∏ i : Fin K, sqfW (z i) (d i)) * Inner d)
      (∑ d ∈ Fintype.piFinset (fun _ : Fin K => range (Y + 1)),
        (∏ i : Fin K, sqfW (z i) (d i)) * Inner d)
    simpa using this
  simp only [hInner] at hfull htri
  linarith

#print axioms inner_multi_bound_prog_witness
#print axioms inner_multi_bound_prog
#print axioms multi_bound_of_rung_prog

end CastingOut

end NormalNumbers
