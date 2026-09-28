import NormalNumbers.C3MrtUnifK

/-!
Audit of the quantifiers in `TTNonPretentious`.  The witness `A` is allowed to
depend on `X` and `L`; consequently the constant function satisfies the named
"nonpretentious" hypothesis at every positive `L`.
-/

open Finset MeasureTheory

namespace NormalNumbers.CastingOut

private theorem phase_re_le_one (t : ℝ) (p : ℕ) :
    (Complex.exp (-(t : ℂ) * Complex.I * (Real.log p : ℂ))).re ≤ 1 := by
  have hnorm : ‖Complex.exp (-(t : ℂ) * Complex.I * (Real.log p : ℂ))‖ = 1 := by
    calc
      ‖Complex.exp (-(t : ℂ) * Complex.I * (Real.log p : ℂ))‖
          = ‖Complex.exp (((-(t * Real.log p) : ℝ) : ℂ) * Complex.I)‖ := by
              congr 1
              push_cast
              ring_nf
      _ = 1 := Complex.norm_exp_ofReal_mul_I _
  exact (Complex.re_le_norm _).trans_eq hnorm

theorem ttPretentiousSum_const_one_nonneg (X t : ℝ) :
    0 ≤ ttPretentiousSum (fun _ => (1 : ℂ)) X t := by
  unfold ttPretentiousSum
  apply Finset.sum_nonneg
  intro p hp
  have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hterm : 0 ≤ 1 - (Complex.exp
      (-(t : ℂ) * Complex.I * (Real.log p : ℂ))).re := by
    linarith [phase_re_le_one t p]
  simpa using div_nonneg hterm hp0.le

theorem ttNonPretentious_const_one (X L : ℝ) (hL : 0 < L) :
    TTNonPretentious (fun _ => (1 : ℂ)) X L := by
  refine ⟨L⁻¹, inv_pos.mpr hL, ?_⟩
  intro t _
  have hsum := ttPretentiousSum_const_one_nonneg X t
  have hexp : 1 ≤ Real.exp (ttPretentiousSum (fun _ => (1 : ℂ)) X t) := by
    calc
      1 = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ _ := Real.exp_le_exp.mpr hsum
  simpa [inv_mul_cancel₀ (ne_of_gt hL)] using hexp

end NormalNumbers.CastingOut

/-!
The exceptional set in `TwoPointNaturalCorrelation` may contain every
natural-number scale in the real interval: that set is countable and has
zero Lebesgue integral.  Thus the conclusion at natural `N` is vacuous.
-/

namespace NormalNumbers.CastingOut

theorem twoPointNaturalCorrelation_vacuous : TwoPointNaturalCorrelation := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro g₁ g₂ _ _ _ _ X L hX hL _ _
  let E : Set ℝ := Set.Icc (Real.sqrt X) X ∩ Set.range (fun n : ℕ => (n : ℝ))
  have hEc : E.Countable :=
    (Set.countable_range (fun n : ℕ => (n : ℝ))).mono Set.inter_subset_right
  have hEm : MeasurableSet E := hEc.measurableSet
  have hE0 : (volume E) = 0 := hEc.measure_zero volume
  refine ⟨E, hEm, Set.inter_subset_left, ?_, ?_⟩
  · rw [MeasureTheory.setIntegral_measure_zero _ hE0]
    have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
    positivity
  · intro N hNlo hNhi hNnot
    exfalso
    apply hNnot
    exact ⟨⟨hNlo, hNhi⟩, ⟨N, rfl⟩⟩

end NormalNumbers.CastingOut

namespace NormalNumbers.CastingOut

/-- A finite sanity counterexample to the no-exception input with fixed
constants `cK(2) = CstK(2) = 1`.  Take both functions constantly one,
`X = N = 16`, `L = 2`, modulus one, and shifts one and two.  The normalized
correlation is one, while the asserted bound is one half.  This theorem does
not quantify over arbitrary positive choices of the two constants. -/
theorem kPointNoExcWith_one_one_two_false :
    ¬ KPointNoExcWith (fun _ => 1) (fun _ => 1) 2 := by
  intro h
  have hlog16 : (2 : ℝ) ≤ Real.log 16 := by
    have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num at *
    linarith
  let hs : Fin 2 → ℕ := fun i => i.val + 1
  have hs_le : ∀ i, (hs i : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) := by
    intro i
    fin_cases i <;> norm_num [hs]
  have hs_inj : Function.Injective hs := by
    intro i j hij
    apply Fin.ext
    exact Nat.add_right_cancel hij
  have hm : ∀ i : Fin 2, IsCoprimeMultiplicativeNat (fun _ => (1 : ℂ)) := by
    intro i
    exact ⟨by simp, by intros; simp⟩
  have hb : ∀ (i : Fin 2) (n : ℕ), ‖(1 : ℂ)‖ ≤ 1 := by simp
  have hspec := h (fun _ _ => (1 : ℂ)) hm hb (16 : ℝ) (2 : ℝ)
    (by norm_num) (by norm_num) hlog16
    ⟨0, ttNonPretentious_const_one 16 2 (by norm_num)⟩
    (16 : ℕ) (by norm_num) (by norm_num)
    (1 : ℕ) (0 : ℕ) hs (by norm_num) (by norm_num) hs_le hs_inj
  norm_num [hs, Fin.prod_univ_two, Finset.Ioc] at hspec
  have hcard :
      #({x ∈ LocallyFiniteOrder.finsetIoc (16 : ℕ) 32 | x % 1 = 0}) = 16 := by decide
  rw [hcard] at hspec
  norm_num at hspec

end NormalNumbers.CastingOut

#print axioms NormalNumbers.CastingOut.ttNonPretentious_const_one
#print axioms NormalNumbers.CastingOut.twoPointNaturalCorrelation_vacuous
#print axioms NormalNumbers.CastingOut.kPointNoExcWith_one_one_two_false
