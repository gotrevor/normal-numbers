/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ArithmeticDisjunctivityDefs
import NormalNumbers.JointLambertDisjunctivity
import NormalNumbers.JointLambertTailBounds

/-!
# A mean bound from small coefficient prefixes

If the coefficient mass up to every cutoff is at most one eighth of the
cutoff, the associated Lambert value has orbit averages at most one eighth
asymptotically.  This gives a direct obstruction to normality.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

open Finset NormalNumbers.JointLambert

theorem coefficient_le_index_of_prefix_bound
    (f : ℕ → ℕ) (h0 : f 0 = 0)
    (hprefix : ∀ N : ℕ, (∑ n ∈ range N, (f n : ℝ)) ≤ (N : ℝ) / 8) :
    ∀ n : ℕ, f n ≤ n := by
  intro n
  cases n with
  | zero => simp [h0]
  | succ n =>
      have hmem : n + 1 ∈ range (n + 2) := by simp
      have hsingle : f (n + 1) ≤ ∑ i ∈ range (n + 2), f i :=
        Finset.single_le_sum (fun i hi => Nat.zero_le (f i)) hmem
      have hreal : (f (n + 1) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) / 8 := by
        exact le_trans (by exact_mod_cast hsingle) (hprefix (n + 2))
      have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hbound : ((n + 2 : ℕ) : ℝ) / 8 ≤ (n + 1 : ℝ) := by
        push_cast
        nlinarith
      exact_mod_cast hreal.trans hbound

theorem summable_sum_tsum_range
    (N : ℕ) (g : ℕ → ℕ → ℝ) (hg : ∀ n, Summable (g n)) :
    (∑ n ∈ range N, ∑' j : ℕ, g n j) =
      ∑' j : ℕ, ∑ n ∈ range N, g n j := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hs : Summable (fun j : ℕ => ∑ n ∈ range N, g n j) :=
        summable_sum fun n hn => hg n
      calc
        (∑ n ∈ range (N + 1), ∑' j : ℕ, g n j)
            = (∑ n ∈ range N, ∑' j : ℕ, g n j) + ∑' j : ℕ, g N j := by
                rw [Finset.sum_range_succ]
        _ = (∑' j : ℕ, ∑ n ∈ range N, g n j) + ∑' j : ℕ, g N j := by rw [ih]
        _ = ∑' j : ℕ, ((∑ n ∈ range N, g n j) + g N j) :=
              (hs.tsum_add (hg N)).symm
        _ = ∑' j : ℕ, ∑ n ∈ range (N + 1), g n j := by
              congr 1
              funext j
              rw [Finset.sum_range_succ]

theorem shifted_prefix_sum_bound
    (f : ℕ → ℕ) (hprefix : ∀ N : ℕ,
      (∑ n ∈ range N, (f n : ℝ)) ≤ (N : ℝ) / 8)
    (N j : ℕ) :
    (∑ n ∈ range N, (f (n + 1 + j) : ℝ)) ≤ ((N + j + 1 : ℕ) : ℝ) / 8 := by
  let s : Finset ℕ := (range N).image (fun n => n + 1 + j)
  have hinj : Set.InjOn (fun n : ℕ => n + 1 + j) (range N : Set ℕ) := by
    intro x hx y hy hxy
    exact Nat.add_right_cancel (Nat.add_right_cancel hxy)
  have hsum : (∑ n ∈ range N, (f (n + 1 + j) : ℝ)) = ∑ x ∈ s, (f x : ℝ) := by
    dsimp [s]
    rw [Finset.sum_image hinj]
  have hsub : s ⊆ range (N + j + 1) := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_range] at hn ⊢
    omega
  have hall : (∑ x ∈ s, (f x : ℝ)) ≤
      ∑ x ∈ range (N + j + 1), (f x : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun x hx hxnot => by positivity)
  rw [hsum]
  exact hall.trans (hprefix (N + j + 1))

theorem affine_half_geometric_sum (N : ℕ) :
    ∑' j : ℕ, ((N + 1 + j : ℕ) : ℝ) / (2 : ℝ) ^ (j + 1) = (N : ℝ) + 2 := by
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos] <;> norm_num
  have h1 : Summable (fun j : ℕ => ((N + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ j) :=
    (summable_geometric_of_norm_lt_one hr).mul_left _
  have h2 : Summable (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
  have hsum := h1.add h2
  have hcong : (fun j : ℕ => ((N + 1 + j : ℕ) : ℝ) / (2 : ℝ) ^ (j + 1)) =
      fun j : ℕ => (1 / 2 : ℝ) *
        (((N + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ j + (j : ℝ) * (1 / 2 : ℝ) ^ j) := by
    funext j
    rw [one_div_pow]
    push_cast
    ring
  have hgeomval := tsum_geometric_of_norm_lt_one hr
  have hweighted := tsum_coe_mul_geometric_of_norm_lt_one hr
  rw [hcong]
  rw [tsum_mul_left, h1.tsum_add h2, tsum_mul_left]
  rw [hgeomval, hweighted]
  norm_num
  ring

/-- Small coefficient prefixes force a small mean for the Lambert orbit. -/
@[blueprint (title := "Small coefficient prefixes obstruct normal orbit means")]
theorem orbit_sum_le_of_small_coefficients
    (b : ℕ) (hb : 2 ≤ b) (f : ℕ → ℕ) (h0 : f 0 = 0)
    (hprefix : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, (f n : ℝ)) ≤ (N : ℝ) / 8) :
    ∀ N : ℕ,
      (∑ n ∈ Finset.range N, orbit b (coefficientValue f b) n) ≤ ((N : ℝ) + 2) / 8 := by
  intro N
  have hf : ∀ n : ℕ, f n ≤ n := coefficient_le_index_of_prefix_bound f h0 hprefix
  have hs : ∀ n : ℕ,
      Summable (fun j : ℕ => (f (n + 1 + j) : ℝ) / (b : ℝ) ^ (j + 1)) :=
    fun n => summable_shift_tail b hb f hf n
  let g : ℕ → ℕ → ℝ := fun n j => (f (n + 1 + j) : ℝ) / (b : ℝ) ^ (j + 1)
  have hmaster (n : ℕ) :
      coefficientValue f b * (b : ℝ) ^ n =
        ((∑ m ∈ range (n + 1), f m * b ^ (n - m) : ℕ) : ℝ) + ∑' j : ℕ, g n j := by
    simpa [g, coefficientValue, CastingOut.lambertVal, mul_comm] using
      lambertVal_mul_pow_eq b hb f hf n
  have horbit (n : ℕ) :
      orbit b (coefficientValue f b) n ≤ ∑' j : ℕ, g n j := by
    have htail0 : 0 ≤ ∑' j : ℕ, g n j := tsum_nonneg fun j => by positivity
    have hfractle : Int.fract (∑' j : ℕ, g n j) ≤ ∑' j : ℕ, g n j := by
      unfold Int.fract
      have hfloor0 : (0 : ℝ) ≤ (⌊∑' j : ℕ, g n j⌋ : ℤ) := by
        exact_mod_cast (Int.floor_nonneg.mpr htail0)
      linarith [Int.floor_le (∑' j : ℕ, g n j)]
    calc
      orbit b (coefficientValue f b) n =
          Int.fract (∑' j : ℕ, g n j) := by
            unfold orbit
            rw [hmaster n, add_comm, Int.fract_add_natCast]
      _ ≤ ∑' j : ℕ, g n j := hfractle
  have hsum_swap :
      (∑ n ∈ range N, ∑' j : ℕ, g n j) =
        ∑' j : ℕ, ∑ n ∈ range N, g n j := summable_sum_tsum_range N g (fun n => hs n)
  have hsOuter : Summable (fun j : ℕ => ∑ n ∈ range N, g n j) :=
    summable_sum fun n hn => hs n
  have hgeom : Summable (fun j : ℕ => ((N + 1 + j : ℕ) : ℝ) / (2 : ℝ) ^ (j + 1)) := by
    have h := (JointLambert.summable_affine_geometric ((N + 1 : ℕ) : ℝ)).mul_right (1 / 2 : ℝ)
    refine h.congr ?_
    intro j
    rw [pow_succ]
    field_simp
    push_cast
    ring
  have hterm : ∀ j : ℕ, (∑ n ∈ range N, g n j) ≤
      ((N + 1 + j : ℕ) : ℝ) / (8 * (2 : ℝ) ^ (j + 1)) := by
    intro j
    have hprefixJ := shifted_prefix_sum_bound f hprefix N j
    have hnum : (∑ n ∈ range N, (f (n + 1 + j) : ℝ)) ≤
        ((N + 1 + j : ℕ) : ℝ) / 8 := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hprefixJ
    have hden : (2 : ℝ) ^ (j + 1) ≤ (b : ℝ) ^ (j + 1) := by
      exact_mod_cast Nat.pow_le_pow_left (by omega : 2 ≤ b) (j + 1)
    change (∑ n ∈ range N, (f (n + 1 + j) : ℝ) / (b : ℝ) ^ (j + 1)) ≤ _
    calc
      ∑ n ∈ range N, (f (n + 1 + j) : ℝ) / (b : ℝ) ^ (j + 1)
          = (∑ n ∈ range N, (f (n + 1 + j) : ℝ)) / (b : ℝ) ^ (j + 1) := by
              rw [Finset.sum_div]
      _ ≤ (((N + 1 + j : ℕ) : ℝ) / 8) / (2 : ℝ) ^ (j + 1) := by
            have hdenb : (0 : ℝ) < (b : ℝ) ^ (j + 1) := by positivity
            have hden2 : (0 : ℝ) < (2 : ℝ) ^ (j + 1) := by positivity
            calc
              _ ≤ (((N + 1 + j : ℕ) : ℝ) / 8) / (b : ℝ) ^ (j + 1) :=
                div_le_div_of_nonneg_right hnum (le_of_lt hdenb)
              _ ≤ (((N + 1 + j : ℕ) : ℝ) / 8) / (2 : ℝ) ^ (j + 1) :=
                div_le_div_of_nonneg_left (by positivity) hden2 hden
      _ = ((N + 1 + j : ℕ) : ℝ) / (8 * (2 : ℝ) ^ (j + 1)) := by ring
  have hgeom8 : Summable (fun j : ℕ => ((N + 1 + j : ℕ) : ℝ) /
      (8 * (2 : ℝ) ^ (j + 1))) := by
    refine (hgeom.mul_left (1 / 8 : ℝ)).congr ?_
    intro j
    ring
  have hbound := Summable.tsum_le_tsum hterm hsOuter hgeom8
  have hsumid :
      (∑ n ∈ range N, orbit b (coefficientValue f b) n) ≤
        ∑' j : ℕ, ∑ n ∈ range N, g n j := by
    calc
      (∑ n ∈ range N, orbit b (coefficientValue f b) n) ≤
          ∑ n ∈ range N, ∑' j : ℕ, g n j :=
            Finset.sum_le_sum fun n hn => horbit n
      _ = ∑' j : ℕ, ∑ n ∈ range N, g n j := hsum_swap
  calc
    (∑ n ∈ range N, orbit b (coefficientValue f b) n)
        ≤ ∑' j : ℕ, ∑ n ∈ range N, g n j := hsumid
    _ ≤ ∑' j : ℕ, ((N + 1 + j : ℕ) : ℝ) / (8 * (2 : ℝ) ^ (j + 1)) := hbound
    _ = ((N : ℝ) + 2) / 8 := by
      have := affine_half_geometric_sum N
      have hcong : (fun j : ℕ => ((N + 1 + j : ℕ) : ℝ) / (8 * (2 : ℝ) ^ (j + 1))) =
          fun j => (1 / 8 : ℝ) * (((N + 1 + j : ℕ) : ℝ) / (2 : ℝ) ^ (j + 1)) := by
        funext j
        ring
      rw [hcong, tsum_mul_left, this]
      ring

end NormalNumbers.ArithmeticDisjunctivity
