import NormalNumbers.ElliottCaseAThin
import NormalNumbers.ElliottSquarefullConv

/-!
# The divisor tail over a window

Leaf 2, Case B: the machinery that makes the truncation of the squarefull expansion at a
*fixed* `D` cost only `ε log W`.

After expanding `U₁(a₁n+b₁) = ∑_{d ∣ a₁n+b₁} u₁(d) Ũ₁((a₁n+b₁)/d)` the terms with `d > D` are
bounded, in absolute value, by the weighted divisor sum `T(m) = ∑_{d ∣ m, d > D} ‖u₁ d‖`.  The
point of this file is that

`∑_{n ∈ (X/W, X]} T(a₁n+b₁)/n ≤ (a₁+|b₁|) (1 + log(Y/L)) · ∑_{d > D} ‖u₁ d‖/d`,

i.e. the *same* thin-window transfer that Case A uses, followed by the elementary
`∑_{m ≤ Y, d ∣ m} 1/m ≤ (1 + log(Y/L))/d`.  Since `Y/L ≤ 4W` in the thin regime, the tail costs
`ε (log W + O(1))`, which is what the Rankin bound `ElliottRankin.exists_squarefull_tail_bound`
was proved for.

Crucially the `1/d` is kept throughout: a per-`d` additive constant (which is what a
progression-by-progression treatment would produce) would be fatal, since `∑_{d ≤ Y} ‖u₁ d‖`
is unbounded.

## Main results

* `sum_Icc_inv_le` — `∑_{a ≤ k ≤ b} 1/k ≤ 1 + log b − log a` (as in `G4MediumPrimes`).
* `sum_Icc_multiples_inv_le` — `∑_{L ≤ m ≤ Y, d ∣ m} 1/m ≤ (1 + log Y − log L)/d`.
* `sum_window_le_transfer_nonneg` — the thin-window transfer for an arbitrary nonnegative `h`,
  with no `1`-boundedness hypothesis (the terms at nonpositive affine values are simply absent).
-/

open scoped BigOperators
open Finset

namespace NormalNumbers.ElliottDivisorTail

open Erdos67b NormalNumbers.ElliottCaseA

noncomputable section

/-- `∑_{a ≤ k ≤ b} 1/k ≤ 1 + log b − log a` for `1 ≤ a ≤ b`. -/
theorem sum_Icc_inv_le {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ k ∈ Finset.Icc a b, (k : ℝ)⁻¹ ≤ 1 + Real.log b - Real.log a := by
  induction b, hab using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.sum_singleton]
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have := inv_le_one_of_one_le₀ this
    linarith
  | succ b hab ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hb : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    have hstep : ((b + 1 : ℕ) : ℝ)⁻¹ ≤ Real.log (b + 1 : ℕ) - Real.log b := by
      push_cast
      rw [← Real.log_div (by positivity) hb.ne']
      have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < (b + 1) / b by positivity)
      rw [inv_div, show (1 : ℝ) - b / (b + 1) = ((b : ℝ) + 1)⁻¹ by field_simp; ring] at this
      exact this
    linarith

/-- **The harmonic mass of the multiples of `d`.**  The `1/d` saving is uniform in the range. -/
theorem sum_Icc_multiples_inv_le {d L Y : ℕ} (hd : 1 ≤ d) (hL : 1 ≤ L) (hLY : L ≤ Y) :
    ∑ m ∈ (Finset.Icc L Y).filter (fun m => d ∣ m), (m : ℝ)⁻¹
      ≤ (1 + Real.log (Y : ℝ) - Real.log (L : ℝ)) / d := by
  classical
  have hd0 : 0 < d := by omega
  set j₀ : ℕ := (L + d - 1) / d with hj₀
  set j₁ : ℕ := Y / d with hj₁
  have hLj₀ : L ≤ d * j₀ := by
    have hdm := Nat.div_add_mod (L + d - 1) d
    have hmod : (L + d - 1) % d < d := Nat.mod_lt _ hd0
    rw [hj₀]
    omega
  have himage : (Finset.Icc L Y).filter (fun m => d ∣ m)
      = (Finset.Icc j₀ j₁).image fun j => d * j := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hmL, hmY⟩, c, rfl⟩
      refine ⟨c, ⟨?_, ?_⟩, rfl⟩
      · refine (Nat.div_le_iff_le_mul_add_pred hd0).mpr ?_
        calc L + d - 1 = L + (d - 1) := by omega
          _ ≤ d * c + (d - 1) := Nat.add_le_add_right hmL _
      · refine (Nat.le_div_iff_mul_le hd0).mpr ?_
        rw [Nat.mul_comm]
        exact hmY
    · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ⟨j, rfl⟩⟩
      · exact le_trans hLj₀ (Nat.mul_le_mul_left d hj1)
      · have := (Nat.le_div_iff_mul_le hd0).mp hj2
        rw [Nat.mul_comm]
        exact this
  rw [himage, Finset.sum_image (by
    intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_left hd0 hxy)]
  have hdr : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hrw : ∀ j : ℕ, (((d * j : ℕ)) : ℝ)⁻¹ = (d : ℝ)⁻¹ * (j : ℝ)⁻¹ := by
    intro j
    push_cast
    rw [mul_inv]
  rw [Finset.sum_congr rfl fun j _ => hrw j, ← Finset.mul_sum]
  have hlogLY : Real.log (L : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log (by exact_mod_cast hL) (by exact_mod_cast hLY)
  rcases le_or_gt j₀ j₁ with hle | hgt
  · have hj₀1 : 1 ≤ j₀ := by
      rw [hj₀]
      exact (Nat.one_le_div_iff hd0).mpr (by omega)
    have hharm := sum_Icc_inv_le hj₀1 hle
    have hj₀pos : (0 : ℝ) < (j₀ : ℝ) := by exact_mod_cast hj₀1
    have hj₁pos : (0 : ℝ) < (j₁ : ℝ) := by
      have : 1 ≤ j₁ := le_trans hj₀1 hle
      exact_mod_cast this
    have hYd : (j₁ : ℝ) * d ≤ (Y : ℝ) := by
      have : j₁ * d ≤ Y := Nat.div_mul_le_self Y d
      exact_mod_cast this
    have hLd : (L : ℝ) ≤ (d : ℝ) * (j₀ : ℝ) := by exact_mod_cast hLj₀
    have h1 : Real.log (j₁ : ℝ) + Real.log (d : ℝ) ≤ Real.log (Y : ℝ) := by
      rw [← Real.log_mul (ne_of_gt hj₁pos) (ne_of_gt hdr)]
      exact Real.log_le_log (by positivity) hYd
    have h2 : Real.log (L : ℝ) ≤ Real.log (d : ℝ) + Real.log (j₀ : ℝ) := by
      rw [← Real.log_mul (ne_of_gt hdr) (ne_of_gt hj₀pos)]
      exact Real.log_le_log (by exact_mod_cast hL) hLd
    rw [div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  · have hempty : Finset.Icc j₀ j₁ = ∅ := by
      rw [Finset.Icc_eq_empty]
      omega
    rw [hempty]
    simp only [Finset.sum_empty, mul_zero]
    refine div_nonneg (by linarith) (by positivity)

/-! ## The thin-window transfer for an arbitrary nonnegative weight -/

/-- **The transfer, for a general nonnegative `h`.**  Identical to
`ElliottCaseAThin.sum_window_le_transfer_ge`, but the summand is restricted to the `n` at which the
affine form is positive, so no `1`-boundedness is needed and there is no additive remainder.  This
is the form the divisor tail `h m = ∑_{d ∣ m, d > D} ‖u d‖` needs — that `h` is unbounded. -/
theorem sum_window_le_transfer_nonneg {h : ℕ → ℝ} (hnn : ∀ m, 0 ≤ h m)
    {a₁ : ℕ} (ha₁ : 0 < a₁) (b₁ : ℤ) (X W : ℕ) {L : ℕ} (hL : 1 ≤ L)
    (hLbd : ∀ n ∈ elliottLogWindow X W, 0 < integerAffine a₁ b₁ n →
      (L : ℤ) ≤ integerAffine a₁ b₁ n) :
    ∑ n ∈ (elliottLogWindow X W).filter (fun n => 0 < integerAffine a₁ b₁ n),
        (n : ℝ)⁻¹ * h ((integerAffine a₁ b₁ n).toNat)
      ≤ ((a₁ + b₁.natAbs : ℕ) : ℝ) *
          ∑ m ∈ Finset.Icc L (a₁ * X + b₁.natAbs), h m / (m : ℝ) := by
  classical
  have hIA : ∀ n : ℕ, integerAffine a₁ b₁ n = (a₁ : ℤ) * n + b₁ := fun n ↦ rfl
  set S := elliottLogWindow X W with hS
  set C : ℝ := ((a₁ + b₁.natAbs : ℕ) : ℝ) with hC
  set Y : ℕ := a₁ * X + b₁.natAbs with hY
  set P : ℕ → Prop := fun n ↦ 0 < integerAffine a₁ b₁ n with hP
  set φ : ℕ → ℕ := fun n ↦ (integerAffine a₁ b₁ n).toNat with hφ
  have hmem : ∀ n ∈ S.filter P, φ n ∈ Finset.Icc L Y := by
    intro n hn
    obtain ⟨hnS, hnP⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnpos, hnX, -⟩ := mem_elliottLogWindow.mp hnS
    have hnP' : (0 : ℤ) < integerAffine a₁ b₁ n := hnP
    have hcast : ((φ n : ℕ) : ℤ) = (a₁ : ℤ) * n + b₁ := by
      rw [hφ]; simpa [hIA] using Int.toNat_of_nonneg hnP'.le
    have hlow : (L : ℤ) ≤ ((φ n : ℕ) : ℤ) := by
      rw [hcast, ← hIA n]; exact hLbd n hnS hnP'
    have hub : (a₁ : ℤ) * n + b₁ ≤ (Y : ℤ) := by
      rw [hY]
      have h1 : (a₁ : ℤ) * n ≤ (a₁ : ℤ) * X := by
        have : (n : ℤ) ≤ (X : ℤ) := by exact_mod_cast hnX
        have ha : (0 : ℤ) ≤ (a₁ : ℤ) := by positivity
        nlinarith
      push_cast
      have hb : b₁ ≤ |b₁| := le_abs_self b₁
      have hbn : (b₁.natAbs : ℤ) = |b₁| := (Int.abs_eq_natAbs b₁).symm
      linarith
    refine Finset.mem_Icc.mpr ⟨by exact_mod_cast hlow, ?_⟩
    omega
  have hinj : ∀ x ∈ S.filter P, ∀ y ∈ S.filter P, φ x = φ y → x = y := by
    intro x hx y hy hxy
    have hxP : (0 : ℤ) < integerAffine a₁ b₁ x := (Finset.mem_filter.mp hx).2
    have hyP : (0 : ℤ) < integerAffine a₁ b₁ y := (Finset.mem_filter.mp hy).2
    have hcx : ((φ x : ℕ) : ℤ) = (a₁ : ℤ) * x + b₁ := by
      rw [hφ]; simpa [hIA] using Int.toNat_of_nonneg hxP.le
    have hcy : ((φ y : ℕ) : ℤ) = (a₁ : ℤ) * y + b₁ := by
      rw [hφ]; simpa [hIA] using Int.toNat_of_nonneg hyP.le
    rw [hxy] at hcx
    have ha : (0 : ℤ) < (a₁ : ℤ) := by exact_mod_cast ha₁
    have : (a₁ : ℤ) * x = (a₁ : ℤ) * y := by omega
    have := mul_left_cancel₀ (ne_of_gt ha) this
    exact_mod_cast this
  have hterm : ∀ n ∈ S.filter P,
      (n : ℝ)⁻¹ * h (φ n) ≤ C * (h (φ n) / (φ n : ℝ)) := by
    intro n hn
    obtain ⟨hnS, hnP⟩ := Finset.mem_filter.mp hn
    have hnpos : 0 < n := (mem_elliottLogWindow.mp hnS).1
    have hnP' : (0 : ℤ) < integerAffine a₁ b₁ n := hnP
    have hcast : ((φ n : ℕ) : ℤ) = (a₁ : ℤ) * n + b₁ := by
      rw [hφ]; simpa [hIA] using Int.toNat_of_nonneg hnP'.le
    have hφpos : 0 < φ n := by
      have : (0 : ℤ) < ((φ n : ℕ) : ℤ) := by rw [hcast]; simpa [hIA] using hnP'
      exact_mod_cast this
    have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hφr : (0 : ℝ) < ((φ n : ℕ) : ℝ) := by exact_mod_cast hφpos
    have hbound : ((φ n : ℕ) : ℝ) ≤ C * n := by
      have hint : ((φ n : ℕ) : ℤ) ≤ ((a₁ + b₁.natAbs : ℕ) : ℤ) * n := by
        rw [hcast]
        have hn1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hnpos
        push_cast
        have hb : b₁ ≤ |b₁| := le_abs_self b₁
        have hbn : (0 : ℤ) ≤ |b₁| := abs_nonneg b₁
        have hbe : (b₁.natAbs : ℤ) = |b₁| := (Int.abs_eq_natAbs b₁).symm
        nlinarith [mul_le_mul_of_nonneg_left hn1 hbn]
      rw [hC]
      exact_mod_cast hint
    have key : (n : ℝ)⁻¹ ≤ C / ((φ n : ℕ) : ℝ) := by
      rw [inv_eq_one_div, div_le_div_iff₀ hnr hφr]
      linarith
    calc (n : ℝ)⁻¹ * h (φ n) ≤ (C / ((φ n : ℕ) : ℝ)) * h (φ n) :=
          mul_le_mul_of_nonneg_right key (hnn _)
      _ = C * (h (φ n) / ((φ n : ℕ) : ℝ)) := by ring
  have hCnn : (0 : ℝ) ≤ C := by rw [hC]; positivity
  calc ∑ n ∈ S.filter P, (n : ℝ)⁻¹ * h (φ n)
      ≤ ∑ n ∈ S.filter P, C * (h (φ n) / (φ n : ℝ)) := Finset.sum_le_sum hterm
    _ = C * ∑ n ∈ S.filter P, h (φ n) / (φ n : ℝ) := by rw [Finset.mul_sum]
    _ = C * ∑ m ∈ (S.filter P).image φ, h m / (m : ℝ) := by rw [Finset.sum_image hinj]
    _ ≤ C * ∑ m ∈ Finset.Icc L Y, h m / (m : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ hCnn
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun i _ _ ↦ div_nonneg (hnn i) (by positivity))
        intro m hm
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
        exact hmem n hn

/-! ## Swapping the divisor sum -/

/-- `∑_{m ∈ A} (∑_{d ∈ B, d ∣ m} f d)/m = ∑_{d ∈ B} f d ∑_{m ∈ A, d ∣ m} 1/m`. -/
theorem sum_div_divisor_swap (A B : Finset ℕ) (f : ℕ → ℝ) :
    ∑ m ∈ A, (∑ d ∈ B.filter (fun d => d ∣ m), f d) / (m : ℝ)
      = ∑ d ∈ B, f d * ∑ m ∈ A.filter (fun m => d ∣ m), (m : ℝ)⁻¹ := by
  classical
  have h1 : ∀ m : ℕ, (∑ d ∈ B.filter (fun d => d ∣ m), f d) / (m : ℝ)
      = ∑ d ∈ B, (if d ∣ m then f d * (m : ℝ)⁻¹ else 0) := by
    intro m
    rw [Finset.sum_filter, Finset.sum_div]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hd : d ∣ m <;> simp [hd, div_eq_mul_inv]
  rw [Finset.sum_congr rfl fun m _ => h1 m, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum, Finset.sum_filter]

/-! ## The tail of the squarefull expansion over the window -/

/-- **The truncation cost.**  With the truncation point `D` chosen before `U` (as
`ElliottRankin.exists_squarefull_tail_bound` allows), the divisors `d > D` contribute at most
`(a₁+|b₁|)(1 + log Y − log L) ε` to the window sum — in particular `O(ε log W)` once
`Y/L ≤ 4W`. -/
theorem sum_window_divisor_tail_le {U : ℕ → ℂ} {a₁ : ℕ} (ha₁ : 0 < a₁) (b₁ : ℤ) (X W : ℕ)
    {L D : ℕ} (hL : 1 ≤ L) (hD : 1 ≤ D) {ε : ℝ} (hε : 0 ≤ ε)
    (hLY : L ≤ a₁ * X + b₁.natAbs)
    (hLbd : ∀ n ∈ elliottLogWindow X W, 0 < integerAffine a₁ b₁ n →
      (L : ℤ) ≤ integerAffine a₁ b₁ n)
    (htail : ∑ d ∈ Finset.Icc (D + 1) (a₁ * X + b₁.natAbs),
      ‖NormalNumbers.ElliottSquarefullConv.squarefullPart U d‖ / (d : ℝ) ≤ ε) :
    ∑ n ∈ (elliottLogWindow X W).filter (fun n => 0 < integerAffine a₁ b₁ n),
        (n : ℝ)⁻¹ * ∑ d ∈ (Finset.Icc (D + 1) (a₁ * X + b₁.natAbs)).filter
            (fun d => d ∣ (integerAffine a₁ b₁ n).toNat),
          ‖NormalNumbers.ElliottSquarefullConv.squarefullPart U d‖
      ≤ ((a₁ + b₁.natAbs : ℕ) : ℝ) *
          ((1 + Real.log ((a₁ * X + b₁.natAbs : ℕ) : ℝ) - Real.log (L : ℝ)) * ε) := by
  classical
  set Y : ℕ := a₁ * X + b₁.natAbs with hY
  set f : ℕ → ℝ := fun d => ‖NormalNumbers.ElliottSquarefullConv.squarefullPart U d‖ with hf
  set h : ℕ → ℝ := fun m => ∑ d ∈ (Finset.Icc (D + 1) Y).filter (fun d => d ∣ m), f d with hh
  have hnn : ∀ m, 0 ≤ h m := by
    intro m
    rw [hh]
    exact Finset.sum_nonneg fun d _ => norm_nonneg _
  have hstep := sum_window_le_transfer_nonneg hnn ha₁ b₁ X W hL hLbd
  refine le_trans hstep ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hswap : ∑ m ∈ Finset.Icc L Y, h m / (m : ℝ)
      = ∑ d ∈ Finset.Icc (D + 1) Y, f d *
          ∑ m ∈ (Finset.Icc L Y).filter (fun m => d ∣ m), (m : ℝ)⁻¹ :=
    sum_div_divisor_swap _ _ f
  rw [hswap]
  set Λ : ℝ := 1 + Real.log (Y : ℝ) - Real.log (L : ℝ) with hΛ
  have hΛnn : 0 ≤ Λ := by
    rw [hΛ]
    have : Real.log (L : ℝ) ≤ Real.log (Y : ℝ) :=
      Real.log_le_log (by exact_mod_cast hL) (by exact_mod_cast hLY)
    linarith
  have hbd : ∀ d ∈ Finset.Icc (D + 1) Y,
      f d * ∑ m ∈ (Finset.Icc L Y).filter (fun m => d ∣ m), (m : ℝ)⁻¹ ≤ Λ * (f d / (d : ℝ)) := by
    intro d hd
    have hd1 : 1 ≤ d := by
      have := (Finset.mem_Icc.mp hd).1
      omega
    have := sum_Icc_multiples_inv_le (d := d) (L := L) (Y := Y) hd1 hL hLY
    have hfnn : 0 ≤ f d := norm_nonneg _
    calc f d * ∑ m ∈ (Finset.Icc L Y).filter (fun m => d ∣ m), (m : ℝ)⁻¹
        ≤ f d * (Λ / (d : ℝ)) := mul_le_mul_of_nonneg_left this hfnn
      _ = Λ * (f d / (d : ℝ)) := by ring
  refine le_trans (Finset.sum_le_sum hbd) ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left htail hΛnn

end

end NormalNumbers.ElliottDivisorTail
