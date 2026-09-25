import NormalNumbers.ElliottTwistedGraphMirror

/-!
# The two-shift rung: arbitrary integer shifts on both affine forms

`NormalNumbers.ElliottTwistedGraph.shiftCMLogElliott` bounds `∑ (1/n) f₁(n) f₂(n+h)` for a
*natural* shift `h > 0` on the second form only.  The crux's slice rung needs both forms shifted by
arbitrary *integers*: `∑ (1/m) f₁(m+c₁) f₂(m+c₂)` with `c₁ ≠ c₂`.  This file closes that gap, i.e.
the `a = 1` case of `NormalNumbers.ElliottDilatedSlice.DilatedSliceCMLogElliott`.

## The estimate

Translating the window by `c₁` costs two constants, both depending on `c₁` alone:

* the **weight discrepancy** `∑_m |1/m − 1/(m+r)| = ∑_m (1/m − 1/(m+r)) ≤ r`, by the telescoping
  bound `sum_harmonicWeight_shift_diff_le` (the two harmonic sums over `Icc 1 X` and
  `Icc (1+r) (X+r)` differ by at most `∑_{Icc 1 r} 1/k ≤ r`);
* the **boundary**, at most `2r` terms of harmonic weight `≤ 1`, by `norm_sum_window_sub_le`.

Both are absorbed by enlarging `A₀`, since `ε log W → ∞`; the device is the dependency's own
`Erdos67b.elliottExists_finalThreshold`, used exactly as it is used for `L₀` in
`Erdos67b.unitCircleLogElliott`.

The sign of `c₁` is the only case split, and the sign of `c₂ − c₁` is handled by
`twoShiftLogCorrelation_swap` together with the mirrored rung
`NormalNumbers.ElliottTwistedGraph.shiftCMLogElliottMirror`, which carries non-pretentiousness on
the *second* function.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace NormalNumbers.ElliottTwoShift

open Erdos67b
open NormalNumbers.ElliottTwistedGraph

noncomputable section

/-! ## The two-shift correlation -/

/-- `∑_{m ∈ (X/W, X]} (1/m) f₁(m+c₁) f₂(m+c₂)`, with both shifts arbitrary integers. -/
def twoShiftLogCorrelation (f₁ f₂ : ℕ → ℂ) (c₁ c₂ : ℤ) (X W : ℕ) : ℂ :=
  ∑ m ∈ elliottLogWindow X W,
    (harmonicWeight m : ℂ) * positiveIntExtension f₁ ((m : ℤ) + c₁) *
      positiveIntExtension f₂ ((m : ℤ) + c₂)

/-- The two-shift correlation is symmetric in the two (function, shift) pairs. -/
theorem twoShiftLogCorrelation_swap (f₁ f₂ : ℕ → ℂ) (c₁ c₂ : ℤ) (X W : ℕ) :
    twoShiftLogCorrelation f₁ f₂ c₁ c₂ X W = twoShiftLogCorrelation f₂ f₁ c₂ c₁ X W :=
  Finset.sum_congr rfl fun m _ ↦ by ring

/-! ## Generic finite-sum helpers -/

/-- Two finite sums of the same summand differ by at most the symmetric-difference mass. -/
theorem norm_sum_sub_sum_le_sdiff (A B : Finset ℕ) (F : ℕ → ℂ) :
    ‖(∑ k ∈ A, F k) - ∑ k ∈ B, F k‖ ≤ (∑ k ∈ A \ B, ‖F k‖) + ∑ k ∈ B \ A, ‖F k‖ := by
  have hAB : A \ (A ∩ B) = A \ B := by ext x; simp
  have hBA : B \ (A ∩ B) = B \ A := by ext x; simp
  have hA : (∑ k ∈ A \ B, F k) + ∑ k ∈ A ∩ B, F k = ∑ k ∈ A, F k := by
    have h := Finset.sum_sdiff (f := F) (Finset.inter_subset_left (s₁ := A) (s₂ := B))
    rwa [hAB] at h
  have hB : (∑ k ∈ B \ A, F k) + ∑ k ∈ A ∩ B, F k = ∑ k ∈ B, F k := by
    have h := Finset.sum_sdiff (f := F) (Finset.inter_subset_right (s₁ := A) (s₂ := B))
    rwa [hBA] at h
  have hdiff : (∑ k ∈ A, F k) - ∑ k ∈ B, F k = (∑ k ∈ A \ B, F k) - ∑ k ∈ B \ A, F k := by
    rw [← hA, ← hB]; ring
  rw [hdiff]
  exact (norm_sub_le _ _).trans (add_le_add (norm_sum_le _ _) (norm_sum_le _ _))

theorem harmonicWeight_le_one {k : ℕ} (hk : 0 < k) : harmonicWeight k ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hpos : (0 : ℝ) < (k : ℝ) := by linarith
  rw [harmonicWeight, inv_eq_one_div, div_le_one hpos]
  exact h1

theorem sum_norm_le_of_card_le {s : Finset ℕ} {F : ℕ → ℂ} {r : ℕ}
    (hF : ∀ k ∈ s, ‖F k‖ ≤ 1) (hcard : s.card ≤ r) :
    ∑ k ∈ s, ‖F k‖ ≤ (r : ℝ) := by
  calc ∑ k ∈ s, ‖F k‖ ≤ ∑ _k ∈ s, (1 : ℝ) := Finset.sum_le_sum hF
    _ = (s.card : ℝ) := by simp
    _ ≤ (r : ℝ) := by exact_mod_cast hcard

/-- **The telescoping weight bound.**  Over any subset of `[1, X]` the total harmonic discrepancy
under a shift by `r` is at most `r`. -/
theorem sum_harmonicWeight_shift_diff_le {s : Finset ℕ} {X r : ℕ}
    (hs : s ⊆ Finset.Icc 1 X) :
    ∑ k ∈ s, (harmonicWeight k - harmonicWeight (k + r)) ≤ (r : ℝ) := by
  have hnonneg : ∀ k ∈ Finset.Icc 1 X, 0 ≤ harmonicWeight k - harmonicWeight (k + r) := by
    intro k hk
    exact sub_nonneg.mpr (harmonicWeight_shift_le (Finset.mem_Icc.mp hk).1)
  have hstep : ∑ k ∈ s, (harmonicWeight k - harmonicWeight (k + r)) ≤
      ∑ k ∈ Finset.Icc 1 X, (harmonicWeight k - harmonicWeight (k + r)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun k hk _ ↦ hnonneg k hk)
  refine hstep.trans ?_
  rw [Finset.sum_sub_distrib]
  have hre : ∑ k ∈ Finset.Icc 1 X, harmonicWeight (k + r)
      = ∑ k ∈ Finset.Icc (1 + r) (X + r), harmonicWeight k := by
    rw [← Finset.map_add_right_Icc, Finset.sum_map]
    rfl
  have hdisj : Disjoint (Finset.Icc 1 r) (Finset.Icc (1 + r) (X + r)) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    rw [Finset.mem_Icc] at hk hk'
    omega
  have hsub : Finset.Icc 1 X ⊆ Finset.Icc 1 r ∪ Finset.Icc (1 + r) (X + r) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    by_cases hle : k ≤ r
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hk.1, hle⟩)
    · exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hsplit : ∑ k ∈ Finset.Icc 1 X, harmonicWeight k ≤
      (∑ k ∈ Finset.Icc 1 r, harmonicWeight k) +
        ∑ k ∈ Finset.Icc (1 + r) (X + r), harmonicWeight k := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ ↦ harmonicWeight_nonneg k)
    rwa [Finset.sum_union hdisj] at h
  have hsmall : ∑ k ∈ Finset.Icc 1 r, harmonicWeight k ≤ (r : ℝ) := by
    calc ∑ k ∈ Finset.Icc 1 r, harmonicWeight k ≤ ∑ _k ∈ Finset.Icc 1 r, (1 : ℝ) :=
          Finset.sum_le_sum fun k hk ↦ harmonicWeight_le_one (Finset.mem_Icc.mp hk).1
      _ = ((Finset.Icc 1 r).card : ℝ) := by simp
      _ = (r : ℝ) := by rw [Nat.card_Icc]; simp
  rw [hre]
  linarith

/-- Comparing a harmonic sum over an arbitrary index set with the same sum over the window: the
error is the symmetric-difference count. -/
theorem norm_sum_window_sub_le {J : Finset ℕ} {G : ℕ → ℂ} {X W r : ℕ}
    (hG : ∀ k, 0 < k → ‖G k‖ ≤ 1)
    (hJpos : ∀ k ∈ J, 0 < k)
    (h1 : (J \ elliottLogWindow X W).card ≤ r)
    (h2 : (elliottLogWindow X W \ J).card ≤ r) :
    ‖(∑ k ∈ J, (harmonicWeight k : ℂ) * G k) -
        ∑ k ∈ elliottLogWindow X W, (harmonicWeight k : ℂ) * G k‖ ≤ 2 * (r : ℝ) := by
  have hnorm : ∀ k : ℕ, 0 < k → ‖(harmonicWeight k : ℂ) * G k‖ ≤ 1 := by
    intro k hk
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (harmonicWeight_nonneg k)]
    calc harmonicWeight k * ‖G k‖ ≤ 1 * 1 :=
          mul_le_mul (harmonicWeight_le_one hk) (hG k hk) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hb1 : ∑ k ∈ J \ elliottLogWindow X W, ‖(harmonicWeight k : ℂ) * G k‖ ≤ (r : ℝ) :=
    sum_norm_le_of_card_le (fun k hk ↦ hnorm k (hJpos k (Finset.mem_sdiff.mp hk).1)) h1
  have hb2 : ∑ k ∈ elliottLogWindow X W \ J, ‖(harmonicWeight k : ℂ) * G k‖ ≤ (r : ℝ) :=
    sum_norm_le_of_card_le (fun k hk ↦ hnorm k
      (mem_elliottLogWindow.mp (Finset.mem_sdiff.mp hk).1).1) h2
  have := norm_sum_sub_sum_le_sdiff J (elliottLogWindow X W)
    (fun k ↦ (harmonicWeight k : ℂ) * G k)
  linarith

/-- `‖t‖ ≤ ‖t - A‖ + ‖A - B‖ + ‖B‖`, in the additive shape the translation estimate needs. -/
theorem norm_le_of_three_split {E : Type*} [NormedAddCommGroup E] (t A B : E)
    {x y z : ℝ} (h1 : ‖t - A‖ ≤ x) (h2 : ‖A - B‖ ≤ y) (h3 : ‖B‖ ≤ z) :
    ‖t‖ ≤ x + (y + z) := by
  have hsplit : t = (t - A) + ((A - B) + B) := by abel
  have hb1 : ‖(t - A) + ((A - B) + B)‖ ≤ ‖t - A‖ + ‖(A - B) + B‖ := norm_add_le _ _
  have hb2 : ‖(A - B) + B‖ ≤ ‖A - B‖ + ‖B‖ := norm_add_le _ _
  calc ‖t‖ = ‖(t - A) + ((A - B) + B)‖ := by rw [← hsplit]
    _ ≤ ‖t - A‖ + ‖(A - B) + B‖ := hb1
    _ ≤ x + (y + z) := by linarith

/-! ## The translation estimate -/

/-- **The two-shift correlation is the pure-shift correlation, up to `3|c₁|`.**

Translating the window by `c₁` costs the boundary (`2|c₁|` terms of harmonic weight `≤ 1`) and the
weight discrepancy (`≤ |c₁|` by telescoping).  Both constants depend on `c₁` only. -/
theorem norm_twoShift_le_shiftedPair_add {f₁ f₂ : ℕ → ℂ}
    (hu₁ : ∀ n : ℕ, 0 < n → ‖f₁ n‖ = 1) (hu₂ : ∀ n : ℕ, 0 < n → ‖f₂ n‖ = 1)
    {c₁ c₂ : ℤ} (hlt : c₁ < c₂) {X W : ℕ} (hW : 0 < W) :
    ‖twoShiftLogCorrelation f₁ f₂ c₁ c₂ X W‖ ≤
      ‖shiftedPairLogCorrelation f₁ f₂ (c₂ - c₁).toNat X W‖ + 3 * (c₁.natAbs : ℝ) := by
  set h : ℕ := (c₂ - c₁).toNat with hhdef
  set r : ℕ := c₁.natAbs with hrdef
  have hc2 : c₂ = c₁ + (h : ℤ) := by omega
  set G : ℕ → ℂ := fun k ↦ f₁ k * f₂ (k + h) with hGdef
  have hGnorm : ∀ k : ℕ, 0 < k → ‖G k‖ ≤ 1 := by
    intro k hk
    simp only [hGdef, norm_mul, hu₁ k hk, hu₂ (k + h) (by omega)]
    norm_num
  obtain ⟨L, hL⟩ : ∃ L : ℕ, elliottLogWindow X W = Finset.Ioc L X :=
    ⟨X / W, elliottLogWindow_eq_Ioc hW⟩
  have hmem : ∀ k : ℕ, k ∈ elliottLogWindow X W ↔ (L < k ∧ k ≤ X) := by
    intro k
    rw [hL, Finset.mem_Ioc]
  have hB : shiftedPairLogCorrelation f₁ f₂ h X W
      = ∑ k ∈ elliottLogWindow X W, (harmonicWeight k : ℂ) * G k :=
    Finset.sum_congr rfl fun k _ ↦ mul_assoc _ _ _
  -- the telescoping weight bound, in the shape used twice below
  have hweightsum : ∀ s : Finset ℕ, s ⊆ Finset.Icc 1 X →
      ∑ n ∈ s, (r : ℝ) / ((n : ℝ) * (n + r : ℝ)) ≤ (r : ℝ) := by
    intro s hs
    have heq : ∀ n ∈ s, (r : ℝ) / ((n : ℝ) * (n + r : ℝ))
        = harmonicWeight n - harmonicWeight (n + r) := by
      intro n hn
      exact (harmonicWeight_sub_shift (Finset.mem_Icc.mp (hs hn)).1).symm
    rw [Finset.sum_congr rfl heq]
    exact sum_harmonicWeight_shift_diff_le hs
  by_cases hc : 0 ≤ c₁
  · -- the shift is forwards
    have hc1 : (r : ℤ) = c₁ := by omega
    have hT : twoShiftLogCorrelation f₁ f₂ c₁ c₂ X W
        = ∑ m ∈ elliottLogWindow X W, (harmonicWeight m : ℂ) * G (m + r) := by
      refine Finset.sum_congr rfl fun m hm ↦ ?_
      have hm0 : 0 < m := (mem_elliottLogWindow.mp hm).1
      have e1 : (m : ℤ) + c₁ = ((m + r : ℕ) : ℤ) := by push_cast; omega
      have e2 : (m : ℤ) + c₂ = ((m + r + h : ℕ) : ℤ) := by push_cast; omega
      rw [e1, e2, positiveIntExtension_natCast (by omega),
        positiveIntExtension_natCast (by omega), hGdef, mul_assoc]
    set J : Finset ℕ := (elliottLogWindow X W).image (fun m ↦ m + r) with hJdef
    have hre : ∑ k ∈ J, (harmonicWeight k : ℂ) * G k
        = ∑ m ∈ elliottLogWindow X W, (harmonicWeight (m + r) : ℂ) * G (m + r) := by
      rw [hJdef, Finset.sum_image (fun x _ y _ hxy ↦ by omega)]
    have h1 : ‖twoShiftLogCorrelation f₁ f₂ c₁ c₂ X W -
        ∑ k ∈ J, (harmonicWeight k : ℂ) * G k‖ ≤ (r : ℝ) := by
      rw [hT, hre]
      refine (norm_sum_harmonic_shift_sub_le (elliottLogWindow X W) G r
        (fun n hn ↦ (mem_elliottLogWindow.mp hn).1)
        (fun n hn ↦ hGnorm (n + r) (by
          have := (mem_elliottLogWindow.mp hn).1; omega))).trans ?_
      exact hweightsum _ (elliottLogWindow_subset_range X W)
    have hJpos : ∀ k ∈ J, 0 < k := by
      intro k hk
      rw [hJdef, Finset.mem_image] at hk
      obtain ⟨m, hm, rfl⟩ := hk
      have := (mem_elliottLogWindow.mp hm).1
      omega
    have hcard1 : (J \ elliottLogWindow X W).card ≤ r := by
      have hsub : J \ elliottLogWindow X W ⊆ Finset.Ioc X (X + r) := by
        intro k hk
        rw [Finset.mem_sdiff, hJdef, Finset.mem_image] at hk
        obtain ⟨⟨m, hm, rfl⟩, hnot⟩ := hk
        have hmw := (hmem m).mp hm
        rw [Finset.mem_Ioc]
        refine ⟨?_, by omega⟩
        by_contra hle
        exact hnot ((hmem (m + r)).mpr ⟨by omega, by omega⟩)
      refine (Finset.card_le_card hsub).trans ?_
      rw [Nat.card_Ioc]
      omega
    have hcard2 : (elliottLogWindow X W \ J).card ≤ r := by
      have hsub : elliottLogWindow X W \ J ⊆ Finset.Ioc L (L + r) := by
        intro k hk
        rw [Finset.mem_sdiff] at hk
        obtain ⟨hkw, hnot⟩ := hk
        have hkm := (hmem k).mp hkw
        rw [Finset.mem_Ioc]
        refine ⟨hkm.1, ?_⟩
        by_contra hgt
        apply hnot
        rw [hJdef, Finset.mem_image]
        exact ⟨k - r, (hmem (k - r)).mpr ⟨by omega, by omega⟩, by omega⟩
      refine (Finset.card_le_card hsub).trans ?_
      rw [Nat.card_Ioc]
      omega
    have h2 := norm_sum_window_sub_le (J := J) (G := G) (X := X) (W := W) (r := r)
      hGnorm hJpos hcard1 hcard2
    rw [hB]
    have hthree := norm_le_of_three_split _ _ _ h1 h2
      (le_refl ‖∑ k ∈ elliottLogWindow X W, (harmonicWeight k : ℂ) * G k‖)
    linarith
  · -- the shift is backwards
    rw [not_le] at hc
    have hc1 : (r : ℤ) = -c₁ := by omega
    set S : Finset ℕ := (elliottLogWindow X W).filter (fun m ↦ r < m) with hSdef
    have hT : twoShiftLogCorrelation f₁ f₂ c₁ c₂ X W
        = ∑ m ∈ S, (harmonicWeight m : ℂ) * G (m - r) := by
      rw [twoShiftLogCorrelation,
        ← Finset.sum_filter_add_sum_filter_not (elliottLogWindow X W) (fun m ↦ r < m)]
      have hzero : ∑ m ∈ (elliottLogWindow X W).filter (fun m ↦ ¬ r < m),
          (harmonicWeight m : ℂ) * positiveIntExtension f₁ ((m : ℤ) + c₁) *
            positiveIntExtension f₂ ((m : ℤ) + c₂) = 0 := by
        refine Finset.sum_eq_zero fun m hm ↦ ?_
        rw [Finset.mem_filter] at hm
        have hnp : (m : ℤ) + c₁ ≤ 0 := by
          have : m ≤ r := by omega
          omega
        rw [positiveIntExtension_nonpos hnp]
        ring
      rw [hzero, add_zero, ← hSdef]
      refine Finset.sum_congr rfl fun m hm ↦ ?_
      rw [hSdef, Finset.mem_filter] at hm
      have hrm : r < m := hm.2
      have e1 : (m : ℤ) + c₁ = ((m - r : ℕ) : ℤ) := by
        rw [Nat.cast_sub (le_of_lt hrm)]; omega
      have e2 : (m : ℤ) + c₂ = ((m - r + h : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_sub (le_of_lt hrm)]; omega
      rw [e1, e2, positiveIntExtension_natCast (by omega),
        positiveIntExtension_natCast (by omega), hGdef, mul_assoc]
    set K : Finset ℕ := S.image (fun m ↦ m - r) with hKdef
    have hSmem : ∀ m ∈ S, L < m ∧ m ≤ X ∧ r < m := by
      intro m hm
      rw [hSdef, Finset.mem_filter] at hm
      exact ⟨((hmem m).mp hm.1).1, ((hmem m).mp hm.1).2, hm.2⟩
    have hKpos : ∀ k ∈ K, 0 < k := by
      intro k hk
      rw [hKdef, Finset.mem_image] at hk
      obtain ⟨m, hm, rfl⟩ := hk
      have := hSmem m hm
      omega
    have hKsub : K ⊆ Finset.Icc 1 X := by
      intro k hk
      rw [hKdef, Finset.mem_image] at hk
      obtain ⟨m, hm, rfl⟩ := hk
      have := hSmem m hm
      rw [Finset.mem_Icc]
      omega
    have hre : ∑ k ∈ K, (harmonicWeight (k + r) : ℂ) * G k
        = ∑ m ∈ S, (harmonicWeight m : ℂ) * G (m - r) := by
      rw [hKdef, Finset.sum_image (fun x hx y hy hxy ↦ by
        have := hSmem x hx; have := hSmem y hy; omega)]
      refine Finset.sum_congr rfl fun m hm ↦ ?_
      have := hSmem m hm
      rw [show m - r + r = m by omega]
    have h1 : ‖twoShiftLogCorrelation f₁ f₂ c₁ c₂ X W -
        ∑ k ∈ K, (harmonicWeight k : ℂ) * G k‖ ≤ (r : ℝ) := by
      have hwt := norm_sum_harmonic_shift_sub_le K (fun j ↦ G (j - r)) r hKpos
        (fun k hk ↦ by
          simpa only [Nat.add_sub_cancel] using hGnorm k (hKpos k hk))
      simp only [Nat.add_sub_cancel] at hwt
      rw [hT, ← hre, norm_sub_rev]
      exact hwt.trans (hweightsum _ hKsub)
    have hcard1 : (K \ elliottLogWindow X W).card ≤ r := by
      have hsub : K \ elliottLogWindow X W ⊆ Finset.Ioc (L - r) L := by
        intro k hk
        rw [Finset.mem_sdiff, hKdef, Finset.mem_image] at hk
        obtain ⟨⟨m, hm, rfl⟩, hnot⟩ := hk
        have hms := hSmem m hm
        rw [Finset.mem_Ioc]
        refine ⟨by omega, ?_⟩
        by_contra hgt
        exact hnot ((hmem (m - r)).mpr ⟨by omega, by omega⟩)
      refine (Finset.card_le_card hsub).trans ?_
      rw [Nat.card_Ioc]
      omega
    have hcard2 : (elliottLogWindow X W \ K).card ≤ r := by
      have hsub : elliottLogWindow X W \ K ⊆ Finset.Ioc (X - r) X := by
        intro k hk
        rw [Finset.mem_sdiff] at hk
        obtain ⟨hkw, hnot⟩ := hk
        have hkm := (hmem k).mp hkw
        rw [Finset.mem_Ioc]
        refine ⟨?_, hkm.2⟩
        by_contra hle
        apply hnot
        rw [hKdef, Finset.mem_image]
        refine ⟨k + r, ?_, by omega⟩
        rw [hSdef, Finset.mem_filter]
        exact ⟨(hmem (k + r)).mpr ⟨by omega, by omega⟩, by omega⟩
      refine (Finset.card_le_card hsub).trans ?_
      rw [Nat.card_Ioc]
      omega
    have h2 := norm_sum_window_sub_le (J := K) (G := G) (X := X) (W := W) (r := r)
      hGnorm hKpos hcard1 hcard2
    rw [hB]
    have hthree := norm_le_of_three_split _ _ _ h1 h2
      (le_refl ‖∑ k ∈ elliottLogWindow X W, (harmonicWeight k : ℂ) * G k‖)
    linarith

/-! ## The two-shift rung, proved -/

/-- **The `a = 1` case of `NormalNumbers.ElliottDilatedSlice.DilatedSliceCMLogElliott`.**  Two
independent completely multiplicative unimodular functions against the forms `n + c₁`, `n + c₂`
with `c₁ ≠ c₂`, non-pretentiousness on `f₁` only. -/
def TwoShiftCMLogElliott : Prop :=
  ∀ (c₁ c₂ : ℤ), c₁ ≠ c₂ →
    ∀ ε : ℝ, 0 < ε →
      ∃ A₀ : ℕ, 2 ≤ A₀ ∧
        ∀ A X W : ℕ, A₀ ≤ A → A ≤ W → W ≤ X →
          ∀ f₁ f₂ : ℕ → ℂ,
            IsCompletelyMultiplicativeOnPositive f₁ →
            IsCompletelyMultiplicativeOnPositive f₂ →
            (∀ n : ℕ, 0 < n → ‖f₁ n‖ = 1) →
            (∀ n : ℕ, 0 < n → ‖f₂ n‖ = 1) →
            MRTNonpretentious f₁ A X →
            ‖twoShiftLogCorrelation f₁ f₂ c₁ c₂ X W‖ ≤ ε * Real.log W

/-- **Proved.**  Both integer shifts are free over the pure-shift rung: the translation costs
`3|c₁|` (or `3|c₂|` in the mirrored orientation), which `Erdos67b.elliottExists_finalThreshold`
absorbs into `(ε/2) log W`.

The sign of `c₂ - c₁` decides which orientation of the pure-shift rung applies.  When `c₂ < c₁` the
hypothesised function `f₁` sits at the *larger* shift, and that is exactly the case
`NormalNumbers.ElliottTwistedGraph.shiftCMLogElliottMirror` was proved for. -/
theorem twoShiftCMLogElliott : TwoShiftCMLogElliott := by
  intro c₁ c₂ hne ε hε
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `c₁ < c₂`: the hypothesised function carries the smaller shift
    obtain ⟨A₁, hA₁, hmain⟩ :=
      shiftCMLogElliott (ε / 2) (by positivity) (c₂ - c₁).toNat (by omega)
    obtain ⟨A₂, hA₂4, -, -, hthr⟩ := elliottExists_finalThreshold (3 * c₁.natAbs) 0 0 hε
    refine ⟨max A₁ A₂, hA₁.trans (le_max_left _ _), ?_⟩
    intro A X W hA hAW hWX f₁ f₂ hm₁ hm₂ hu₁ hu₂ hpret
    have hA₂W : A₂ ≤ W := (le_max_right A₁ A₂).trans (hA.trans hAW)
    have hW : 0 < W := by omega
    have hres := hmain A X W ((le_max_left A₁ A₂).trans hA) hAW hWX f₁ f₂ hm₁ hm₂ hu₁ hu₂ hpret
    have hest := norm_twoShift_le_shiftedPair_add hu₁ hu₂ hlt (X := X) (W := W) hW
    obtain ⟨-, -, herr⟩ := hthr W hA₂W
    have herr' : 3 * (c₁.natAbs : ℝ) ≤ ε / 2 * Real.log W := by push_cast at herr; linarith
    linarith
  · -- `c₂ < c₁`: the hypothesised function carries the larger shift — the mirrored rung
    obtain ⟨A₁, hA₁, hmain⟩ :=
      shiftCMLogElliottMirror (ε / 2) (by positivity) (c₁ - c₂).toNat (by omega)
    obtain ⟨A₂, hA₂4, -, -, hthr⟩ := elliottExists_finalThreshold (3 * c₂.natAbs) 0 0 hε
    refine ⟨max A₁ A₂, hA₁.trans (le_max_left _ _), ?_⟩
    intro A X W hA hAW hWX f₁ f₂ hm₁ hm₂ hu₁ hu₂ hpret
    have hA₂W : A₂ ≤ W := (le_max_right A₁ A₂).trans (hA.trans hAW)
    have hW : 0 < W := by omega
    have hres := hmain A X W ((le_max_left A₁ A₂).trans hA) hAW hWX f₂ f₁ hm₂ hm₁ hu₂ hu₁ hpret
    have hest := norm_twoShift_le_shiftedPair_add hu₂ hu₁ hgt (X := X) (W := W) hW
    obtain ⟨-, -, herr⟩ := hthr W hA₂W
    have herr' : 3 * (c₂.natAbs : ℝ) ≤ ε / 2 * Real.log W := by push_cast at herr; linarith
    rw [twoShiftLogCorrelation_swap]
    linarith

end

end NormalNumbers.ElliottTwoShift
