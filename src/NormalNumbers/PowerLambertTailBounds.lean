/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Elementary finite bounds for power-Lambert tails
-/

namespace NormalNumbers.ArithmeticDisjunctivity

open Finset

/-- Positive multiples of `q` below `N` are no more numerous than `N / q`. -/
theorem card_positive_multiples_lt_le (N q : ℕ) (hq : 0 < q) :
    ((Finset.range N).filter fun n => n ≠ 0 ∧ q ∣ n).card ≤ N / q := by
  classical
  let s : Finset ℕ := (range N).filter fun n => n ≠ 0 ∧ q ∣ n
  let f : ℕ → ℕ := fun n => n / q - 1
  have hinj : Set.InjOn f (s : Set ℕ) := by
    intro x hx y hy hxy
    have hxdiv : q ∣ x := (Finset.mem_filter.mp hx).2.2
    have hydiv : q ∣ y := (Finset.mem_filter.mp hy).2.2
    have hxrec : x / q * q = x := Nat.div_mul_cancel hxdiv
    have hyrec : y / q * q = y := Nat.div_mul_cancel hydiv
    have hxne : x ≠ 0 := (Finset.mem_filter.mp hx).2.1
    have hyne : y ≠ 0 := (Finset.mem_filter.mp hy).2.1
    have hxpos : 0 < x / q := Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hxne) hxdiv) hq
    have hypos : 0 < y / q := Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hyne) hydiv) hq
    have hquot : x / q = y / q := by
      dsimp [f] at hxy
      have hh := congrArg (fun z : ℕ => z + 1) hxy
      rw [Nat.sub_add_cancel (by omega : 1 ≤ x / q),
        Nat.sub_add_cancel (by omega : 1 ≤ y / q)] at hh
      exact hh
    calc
      x = x / q * q := hxrec.symm
      _ = y / q * q := by rw [hquot]
      _ = y := hyrec
  have himage : s.image f ⊆ range (N / q) := by
    intro z hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
    have hn' := Finset.mem_filter.mp hn
    have hnrange := Finset.mem_range.mp hn'.1
    have hdiv : q ∣ n := hn'.2.2
    have hrec : n / q * q = n := Nat.div_mul_cancel hdiv
    have hnne : n ≠ 0 := hn'.2.1
    have hqquot : 0 < n / q := Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hnne) hdiv) hq
    have hmon : n / q ≤ N / q := Nat.div_le_div_right (Nat.le_of_lt hnrange)
    simp only [Finset.mem_range]
    dsimp [f]
    have hsub : n / q - 1 < n / q := Nat.sub_lt hqquot (by decide)
    exact lt_of_lt_of_le hsub hmon
  calc
    s.card = (s.image f).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (range (N / q)).card := Finset.card_le_card himage
    _ = N / q := Finset.card_range _

noncomputable def reciprocalDifference (d : ℕ) : ℝ :=
  1 / ((d : ℝ) - 1) - 1 / (d : ℝ)

theorem reciprocalDifference_sum_Ico (N : ℕ) (hN : 9 ≤ N) :
    (∑ d ∈ Finset.Ico 9 N, reciprocalDifference d) =
      (1 / 8 : ℝ) - 1 / ((N - 1 : ℕ) : ℝ) := by
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases hbase : N = 8
      · subst N
        norm_num [reciprocalDifference, Finset.Ico_eq_empty_of_le]
      · have hprev : 9 ≤ N := by omega
        rw [Finset.sum_Ico_succ_top hprev, ih hprev]
        have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
        have hNsub : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ N)]
          norm_num
        dsimp [reciprocalDifference]
        rw [hNsub]
        field_simp
        ring

/-- The reciprocal divisor kernel past eight has total mass at most one eighth. -/
theorem reciprocalDivisorTail_le_eighth (N : ℕ) :
    (∑ d ∈ Finset.range N,
      if 8 < d then (1 : ℝ) / ((d : ℝ) * ((d : ℝ) - 1)) else 0) ≤ 1 / 8 := by
  classical
  by_cases hN : N < 9
  · have hzero : ∀ d ∈ range N, ¬ 8 < d := by
      intro d hd
      have := Finset.mem_range.mp hd
      omega
    calc
      (∑ d ∈ range N,
        if 8 < d then (1 : ℝ) / ((d : ℝ) * ((d : ℝ) - 1)) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro d hd
          simp [hzero d hd]
      _ ≤ 1 / 8 := by norm_num
  have hfilter : (range N).filter (fun d => 8 < d) = Finset.Ico 9 N := by
    ext d
    simp only [mem_filter, mem_range, Finset.mem_Ico]
    omega
  have hsum :
      (∑ d ∈ range N,
        if 8 < d then (1 : ℝ) / ((d : ℝ) * ((d : ℝ) - 1)) else 0) =
        ∑ d ∈ Finset.Ico 9 N, reciprocalDifference d := by
    rw [← Finset.sum_filter, hfilter]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd9 : 9 ≤ d := (Finset.mem_Ico.mp hd).1
    have hden : (d : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
      linarith
    dsimp [reciprocalDifference]
    field_simp
    ring
  rw [hsum]
  by_cases heq : N = 9
  · subst N
    norm_num [Finset.Ico_eq_empty_of_le]
  have h9N : 9 ≤ N := by omega
  rw [reciprocalDifference_sum_Ico N h9N]
  have hpos : 0 < ((N - 1 : ℕ) : ℝ) := by
    have : 0 < N - 1 := by omega
    exact_mod_cast this
  have hrecip : 0 ≤ 1 / ((N - 1 : ℕ) : ℝ) := by positivity
  linarith

end NormalNumbers.ArithmeticDisjunctivity
