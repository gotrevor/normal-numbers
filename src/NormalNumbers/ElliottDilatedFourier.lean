import NormalNumbers.ElliottDilatedSelect

/-!
# The dilated Fourier first moment from MRT

The last structural ingredient of leaf 1: the criterion
`NormalNumbers.ElliottDilatedSelect.exists_affineLogCorrelation_small_of_fourier_first_moments`
wants the log-average of `‖blockFourier T (affineBlock f a n H) t‖`, while
`Erdos67b.logProb_fourier_firstMoment_of_MRT` delivers the log-average of
`‖blockFourier T (finiteSequenceBlock f H n) t‖`.  Two observations close the gap, and both are
exact.

* **The dilated block is an ordinary block at a dilated base point.**
  `affineBlock f a n H = finiteSequenceBlock f H (a(n+1) - 1)` (both read
  `f (a(n+1) + i)`), so the dilated Fourier coefficient is `modulatedShortSum f (a(n+1)-1) H (t/T)`.
* **The dilated base points are a sub-progression of a window `a` times longer.**
  `n ↦ a(n+1) - 1` is strictly monotone, and for `n ≥ 1` one has `a(n+1)-1 ≤ 2 a n`, so
  `n⁻¹ ≤ 2a · (a(n+1)-1)⁻¹`: the harmonic weight of the dilated base point dominates, up to the
  factor `2a`, the weight of `n`.  Hence the whole dilated first moment is at most `2a` times an
  ordinary MRT first moment over the stretched window — and `a` is a constant fixed before every
  tolerance.

Also here: `MRTNonpretentious_of_le`, the (free) passage of non-pretentiousness from `(A, X)` to
`(A', X')` whenever `A' ≤ A`, `X ≤ X'` and `A' X' ≤ A X`.  `pretentiousDistSqToTwist` is monotone in
the cutoff, so enlarging the scale only helps; the constraint is the frequency range, which is why
`A'` must shrink by the same factor `a` the scale grows by.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate
open Finset Filter

namespace NormalNumbers.ElliottDilatedFourier

open Erdos67b
open NormalNumbers.ElliottDilatedPairing

noncomputable section

/-! ## The dilated block is an ordinary block at a dilated base point -/

theorem affineBlock_eq_finiteSequenceBlock {f : ℕ → ℂ} {a : ℕ} (ha : 0 < a) (n H : ℕ) :
    affineBlock f a n H = finiteSequenceBlock f H (a * (n + 1) - 1) := by
  funext i
  have hpos : 0 < a * (n + 1) := by positivity
  have hidx : a * (n + 1) - 1 + i.1 + 1 = a * (n + 1) + i.1 := by omega
  have hcast : ((a * (n + 1) : ℕ) : ℤ) + (i.1 : ℤ) = ((a * (n + 1) - 1 + i.1 + 1 : ℕ) : ℤ) := by
    rw [hidx]; push_cast; ring
  simp only [affineBlock, finiteSequenceBlock, hcast]
  exact positiveIntExtension_natCast (by omega)

theorem norm_blockFourier_affineBlock {f : ℕ → ℂ} {a : ℕ} (ha : 0 < a) (n H T : ℕ) (t : ℤ) :
    ‖blockFourier T (affineBlock f a n H) t‖ =
      ‖modulatedShortSum f (a * (n + 1) - 1) H ((t : ℝ) / T)‖ := by
  rw [affineBlock_eq_finiteSequenceBlock ha, norm_blockFourier_finiteSequenceBlock]

/-! ## Non-pretentiousness transfers to a larger scale, at a smaller threshold -/

theorem MRTNonpretentious_of_le {f : ℕ → ℂ} (hf : ∀ n : ℕ, 0 < n → ‖f n‖ = 1)
    {A X A' X' : ℕ} (h : MRTNonpretentious f A X)
    (hA : A' ≤ A) (hX : X ≤ X') (hprod : (A' : ℝ) * X' ≤ (A : ℝ) * X) :
    MRTNonpretentious f A' X' := by
  intro q hq hqA' χ t ht
  have hfp : ∀ p : ℕ, p.Prime → ‖f p‖ ≤ 1 := fun p hp ↦ (hf p hp.pos).le
  have hA' : (A' : ℝ) ≤ A := by exact_mod_cast hA
  have hmain := h q hq (hqA'.trans hA) χ t (ht.trans hprod)
  exact hA'.trans (hmain.trans (pretentiousDistSqToTwist_mono χ t hX hfp))

/-! ## The dilated first moment -/

/-- **The dilated Fourier first moment.**  The log-average of the dilated block transform over the
trimmed window is at most `4 a δ H`, given an MRT bound `δ log W` on the *ordinary* first moment
over any window `(X', W')` containing every dilated base point `a(n+1)-1`.

The factor `2a` is the harmonic-weight comparison and the other `2` is the trimmed-mass bound
`log W / 2 ≤ M`; both are the dependency's own losses with `a` inserted. -/
theorem logProb_fourier_firstMoment_affineBlock_of_MRT
    {X W L₀ H T a X' W' : ℕ} (ha : 0 < a) (hW : 2 ≤ W) (hH : 0 < H)
    (hincl : ∀ n ∈ Icc (elliottTrimmedLower X W L₀) X,
      a * (n + 1) - 1 ∈ elliottLogWindow X' W')
    (hM : 0 < (logProbMassNN (elliottTrimmedLower X W L₀) X : ℝ))
    (hMlo : Real.log W / 2 ≤ (logProbMassNN (elliottTrimmedLower X W L₀) X : ℝ))
    {δ : ℝ} (hδ : 0 ≤ δ) (f : ℕ → ℂ) (t : ℤ)
    (hfirst : logAverageModulatedShortSum f X' W' H ((t : ℝ) / T) ≤ δ * Real.log W) :
    logProbExpectation (elliottTrimmedLower X W L₀) X
        (fun n ↦ ‖blockFourier T (affineBlock f a n H) t‖) ≤ 4 * a * δ * H := by
  classical
  set L := elliottTrimmedLower X W L₀ with hLdef
  set α : ℝ := (t : ℝ) / T with hαdef
  have hLpos : 0 < L := by
    rw [hLdef]
    exact lt_of_lt_of_le (Nat.succ_pos (X / W)) (le_max_right _ _)
  have hlogW : 0 < Real.log W := Real.log_pos (by exact_mod_cast hW)
  have har : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  set φ : ℕ → ℕ := fun n ↦ a * (n + 1) - 1 with hφdef
  -- the pointwise harmonic comparison
  have hapos : ∀ k : ℕ, 1 ≤ a * (k + 1) :=
    fun k ↦ Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hpoint : ∀ n ∈ Icc L X, (n : ℝ)⁻¹ * ‖modulatedShortSum f (φ n) H α‖ ≤
      2 * a * ((φ n : ℝ)⁻¹ * ‖modulatedShortSum f (φ n) H α‖) := by
    intro n hn
    have hn1 : 1 ≤ n := le_trans hLpos (mem_Icc.mp hn).1
    have hatwo : 2 ≤ a * (n + 1) := by
      have := Nat.mul_le_mul ha (show 2 ≤ n + 1 by omega)
      omega
    have hφpos : 0 < φ n := by
      simp only [hφdef]
      omega
    have hmul : a ≤ a * n := Nat.le_mul_of_pos_right a hn1
    have he : a * (n + 1) = a * n + a := by ring
    have hφnat : φ n ≤ 2 * (a * n) := by
      simp only [hφdef, he]
      calc a * n + a - 1 ≤ a * n + a := Nat.sub_le _ _
        _ ≤ a * n + a * n := Nat.add_le_add_left hmul _
        _ = 2 * (a * n) := by ring
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
    have hφr : (0 : ℝ) < φ n := by exact_mod_cast hφpos
    have hφle : (φ n : ℝ) ≤ 2 * (a : ℝ) * n := by
      have := (Nat.cast_le (α := ℝ)).mpr hφnat
      push_cast at this
      linarith
    have hinv : (n : ℝ)⁻¹ ≤ 2 * a * (φ n : ℝ)⁻¹ := by
      calc (n : ℝ)⁻¹ = 1 / n := (one_div _).symm
        _ ≤ (2 * (a : ℝ)) / (φ n : ℝ) := by
            rw [div_le_div_iff₀ hnr hφr]
            nlinarith
        _ = 2 * a * (φ n : ℝ)⁻¹ := by rw [div_eq_mul_inv]
    calc (n : ℝ)⁻¹ * ‖modulatedShortSum f (φ n) H α‖
        ≤ (2 * a * (φ n : ℝ)⁻¹) * ‖modulatedShortSum f (φ n) H α‖ :=
          mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
      _ = 2 * a * ((φ n : ℝ)⁻¹ * ‖modulatedShortSum f (φ n) H α‖) := by ring
  -- reindex onto the dilated base points and enlarge to the MRT window
  have hinj : ∀ x ∈ Icc L X, ∀ y ∈ Icc L X, φ x = φ y → x = y := by
    intro x _ y _ hxy
    simp only [hφdef] at hxy
    have hx := hapos x
    have hy := hapos y
    have heq : a * (x + 1) = a * (y + 1) := by omega
    have hsucc := Nat.eq_of_mul_eq_mul_left ha heq
    omega
  have hreindex : (∑ n ∈ Icc L X, (φ n : ℝ)⁻¹ * ‖modulatedShortSum f (φ n) H α‖) =
      ∑ m ∈ (Icc L X).image φ, (m : ℝ)⁻¹ * ‖modulatedShortSum f m H α‖ :=
    (Finset.sum_image (f := fun m : ℕ ↦ (m : ℝ)⁻¹ * ‖modulatedShortSum f m H α‖) hinj).symm
  have henlarge : (∑ m ∈ (Icc L X).image φ, (m : ℝ)⁻¹ * ‖modulatedShortSum f m H α‖) ≤
      ∑ m ∈ elliottLogWindow X' W', (m : ℝ)⁻¹ * ‖modulatedShortSum f m H α‖ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
      exact hincl n hn
    · intro m _ _; positivity
  have hMRT : (∑ m ∈ elliottLogWindow X' W', (m : ℝ)⁻¹ * ‖modulatedShortSum f m H α‖) ≤
      (H : ℝ) * (δ * Real.log W) := by
    rw [sum_weighted_modulated_norm_eq hH]
    exact mul_le_mul_of_nonneg_left hfirst (Nat.cast_nonneg H)
  -- assemble
  have hsum : (∑ n ∈ Icc L X, (n : ℝ)⁻¹ * ‖blockFourier T (affineBlock f a n H) t‖) ≤
      2 * a * ((H : ℝ) * (δ * Real.log W)) := by
    have hcongr : ∀ n ∈ Icc L X, (n : ℝ)⁻¹ * ‖blockFourier T (affineBlock f a n H) t‖ =
        (n : ℝ)⁻¹ * ‖modulatedShortSum f (φ n) H α‖ := by
      intro n _
      rw [norm_blockFourier_affineBlock ha]
    rw [Finset.sum_congr rfl hcongr]
    calc ∑ n ∈ Icc L X, (n : ℝ)⁻¹ * ‖modulatedShortSum f (φ n) H α‖
        ≤ ∑ n ∈ Icc L X, 2 * a * ((φ n : ℝ)⁻¹ * ‖modulatedShortSum f (φ n) H α‖) :=
          Finset.sum_le_sum hpoint
      _ = 2 * a * ∑ n ∈ Icc L X, (φ n : ℝ)⁻¹ * ‖modulatedShortSum f (φ n) H α‖ := by
          rw [Finset.mul_sum]
      _ ≤ 2 * a * ((H : ℝ) * (δ * Real.log W)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hreindex]
          exact henlarge.trans hMRT
  rw [logProbExpectation_eq_mass_inv_smul_sum]
  simp only [smul_eq_mul]
  rw [inv_mul_eq_div, div_le_iff₀ hM]
  refine hsum.trans ?_
  nlinarith [mul_le_mul_of_nonneg_left hMlo (show (0:ℝ) ≤ 4 * (a : ℝ) * δ * H by positivity)]

end

end NormalNumbers.ElliottDilatedFourier

#print axioms NormalNumbers.ElliottDilatedFourier.norm_blockFourier_affineBlock
#print axioms NormalNumbers.ElliottDilatedFourier.MRTNonpretentious_of_le
#print axioms NormalNumbers.ElliottDilatedFourier.logProb_fourier_firstMoment_affineBlock_of_MRT
