/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.PrimeCounting

/-!
# G4 disjunctivity: elementary Mertens-type bounds on `∑ 1/p`

Neither bound is in mathlib.  Both are needed by the §5 schedule: the lower bound gives the
good-prime harmonic mass `L − o(L)` in §4C, the excluded-prime bound shows the primes dividing
the progression modulus cost only `O(log ω(P₀))`.

* `log_log_le_sum_inv_primesBelow` — **lower Mertens**: `log log N ≤ ∑_{p < N} 1/p + 1` for
  `N ≥ 2`.  Route: the finite Euler product `∏_{p<N}(1−1/p)^{−1} = ∑_{m N-smooth} 1/m`
  (mathlib, `EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric`)
  dominates `∑_{m<N} 1/m ≥ log N`; then `−log(1−1/p) ≤ 1/(p−1) = 1/p + 1/(p(p−1))` and the
  telescoping `∑_{n≥2} 1/(n(n−1)) ≤ 1`.
* `sum_inv_le_log_card_add_one` — **excluded primes**: for any finset `T` of integers `≥ 2`,
  `∑_{t∈T} 1/t ≤ ∑_{k ≤ |T|} 1/(k+1) ≤ log |T| + 1`.
-/

open Finset Real
open scoped BigOperators

namespace NormalNumbers.G4

/-! ### The finite Euler product dominates the harmonic sum -/

/-- `n ↦ n⁻¹` as a monoid homomorphism `ℕ →* ℝ`. -/
noncomputable def invHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by push_cast; rw [mul_inv]

lemma invHom_apply (n : ℕ) : invHom n = (n : ℝ)⁻¹ := rfl

/-- `∑_{m<N} 1/m ≤ ∏_{p<N} (1 − 1/p)⁻¹`. -/
theorem sum_range_inv_le_prod_primesBelow (N : ℕ) :
    ∑ m ∈ range N, (m : ℝ)⁻¹ ≤ ∏ p ∈ N.primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hlt : ∀ {p : ℕ}, p.Prime → ‖invHom p‖ < 1 := by
    intro p hp
    rw [invHom_apply, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have h := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hlt N).2
  simp only [invHom_apply] at h
  have h' : HasSum ((N.smoothNumbers : Set ℕ).indicator fun m : ℕ => (m : ℝ)⁻¹)
      (∏ p ∈ N.primesBelow, (1 - (p : ℝ)⁻¹)⁻¹) := by
    rw [← hasSum_subtype_iff_indicator]
    exact h
  refine le_trans ?_ (sum_le_hasSum (range N) (fun i _ => ?_) h')
  · refine Finset.sum_le_sum fun m hm => ?_
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      simp only [CharP.cast_eq_zero, inv_zero]
      exact Set.indicator_nonneg (fun m _ => by positivity) _
    · rw [Set.indicator_of_mem]
      exact Nat.mem_smoothNumbers_of_lt h0 (Finset.mem_range.1 hm)
  · exact Set.indicator_nonneg (fun m _ => by positivity) i

/-- `log N ≤ ∑_{m<N} 1/m` for `N ≥ 1`. -/
lemma log_le_sum_range_inv (N : ℕ) (hN : 1 ≤ N) : Real.log N ≤ ∑ m ∈ range N, (m : ℝ)⁻¹ := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have h := log_add_one_le_harmonic n
  have : (harmonic n : ℝ) = ∑ m ∈ range (n + 1), (m : ℝ)⁻¹ := by
    rw [Finset.sum_range_succ', harmonic]
    push_cast
    simp
  rw [this] at h
  exact_mod_cast h

/-! ### `−log(1 − 1/p) ≤ 1/(p−1)` and the telescoping tail -/

lemma neg_log_one_sub_inv_le {p : ℕ} (hp : 2 ≤ p) :
    Real.log (1 - (p : ℝ)⁻¹)⁻¹ ≤ (p : ℝ)⁻¹ + ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hpos : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by
    rw [sub_pos]; exact inv_lt_one_of_one_lt₀ hp1
  rw [Real.log_inv]
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  have key : (1 - (p : ℝ)⁻¹)⁻¹ = (p : ℝ) / ((p : ℝ) - 1) := by
    field_simp
  have key2 : (p : ℝ)⁻¹ + ((p : ℝ) * ((p : ℝ) - 1))⁻¹ = ((p : ℝ) - 1)⁻¹ := by
    field_simp
    ring
  rw [key2]
  have : 1 - (p : ℝ) / ((p : ℝ) - 1) = -((p : ℝ) - 1)⁻¹ := by
    field_simp
    ring
  rw [key, this] at h
  linarith

/-- `∑_{n ∈ Ico 2 N} 1/(n(n−1)) ≤ 1` (telescoping). -/
lemma sum_Ico_inv_mul_sub_one_le (N : ℕ) :
    ∑ n ∈ Ico 2 N, ((n : ℝ) * ((n : ℝ) - 1))⁻¹ ≤ 1 := by
  have h : ∀ N : ℕ, 2 ≤ N → ∑ n ∈ Ico 2 N, ((n : ℝ) * ((n : ℝ) - 1))⁻¹ = 1 - ((N : ℝ) - 1)⁻¹ := by
    intro N hN
    induction N with
    | zero => omega
    | succ N ih =>
      rcases Nat.lt_or_ge N 2 with h2 | h2
      · have : N = 1 := by omega
        subst this; norm_num
      · rw [Finset.sum_Ico_succ_top (by omega : 2 ≤ N), ih h2]
        have h1 : (N : ℝ) - 1 ≠ 0 := by
          have : (2 : ℝ) ≤ N := by exact_mod_cast h2
          linarith
        have h0 : (N : ℝ) ≠ 0 := by positivity
        push_cast
        rw [show ((N : ℝ) + 1 - 1) = N by ring, mul_inv, sub_add_eq_add_sub]
        field_simp
        ring
  rcases Nat.lt_or_ge N 2 with h2 | h2
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]; norm_num
  · rw [h N h2]
    have : (0 : ℝ) ≤ ((N : ℝ) - 1)⁻¹ := by
      have : (2 : ℝ) ≤ N := by exact_mod_cast h2
      have : (0 : ℝ) < (N : ℝ) - 1 := by linarith
      positivity
    linarith

/-- `∑_{p<N} 1/(p(p−1)) ≤ 1`. -/
lemma sum_primesBelow_inv_mul_sub_one_le (N : ℕ) :
    ∑ p ∈ N.primesBelow, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ ≤ 1 := by
  refine le_trans ?_ (sum_Ico_inv_mul_sub_one_le N)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n hn _ => ?_
  · intro p hp
    rw [Nat.mem_primesBelow] at hp
    rw [Finset.mem_Ico]
    exact ⟨hp.2.two_le, hp.1⟩
  · rw [Finset.mem_Ico] at hn
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn.1
    have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    positivity

/-- **Lower Mertens bound**: `log log N ≤ ∑_{p<N} 1/p + 1` for `N ≥ 2`. -/
theorem log_log_le_sum_inv_primesBelow (N : ℕ) (hN : 2 ≤ N) :
    Real.log (Real.log N) ≤ ∑ p ∈ N.primesBelow, (p : ℝ)⁻¹ + 1 := by
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have h1 := log_le_sum_range_inv N (by omega)
  have h2 := sum_range_inv_le_prod_primesBelow N
  have hpos : ∀ p ∈ N.primesBelow, 0 < (1 - (p : ℝ)⁻¹)⁻¹ := by
    intro p hp
    have := (Nat.mem_primesBelow.1 hp).2.one_lt
    have : (1 : ℝ) < p := by exact_mod_cast this
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ this
    exact inv_pos.2 (by linarith)
  calc Real.log (Real.log N) ≤ Real.log (∏ p ∈ N.primesBelow, (1 - (p : ℝ)⁻¹)⁻¹) :=
        Real.log_le_log hlogN (h1.trans h2)
    _ = ∑ p ∈ N.primesBelow, Real.log (1 - (p : ℝ)⁻¹)⁻¹ :=
        Real.log_prod (fun p hp => (hpos p hp).ne')
    _ ≤ ∑ p ∈ N.primesBelow, ((p : ℝ)⁻¹ + ((p : ℝ) * ((p : ℝ) - 1))⁻¹) :=
        Finset.sum_le_sum fun p hp => neg_log_one_sub_inv_le (Nat.mem_primesBelow.1 hp).2.two_le
    _ = ∑ p ∈ N.primesBelow, (p : ℝ)⁻¹ + ∑ p ∈ N.primesBelow, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ :=
        Finset.sum_add_distrib
    _ ≤ ∑ p ∈ N.primesBelow, (p : ℝ)⁻¹ + 1 := by
        linarith [sum_primesBelow_inv_mul_sub_one_le N]

/-! ### Excluded primes: a finset of integers `≥ 2` has harmonic mass `≤ H(|T|)` -/

/-- For a finset `T` of integers `≥ 2`, `∑_{t∈T} 1/t ≤ ∑_{k<|T|} 1/(k+2)`. -/
theorem sum_inv_le_sum_range_card (T : Finset ℕ) (hT : ∀ t ∈ T, 2 ≤ t) :
    ∑ t ∈ T, (t : ℝ)⁻¹ ≤ ∑ k ∈ range T.card, ((k : ℝ) + 2)⁻¹ := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a T ha ih =>
    have haT : a ∉ T := fun h => lt_irrefl a (ha a h)
    have hT' : ∀ t ∈ T, 2 ≤ t := fun t ht => hT t (Finset.mem_insert_of_mem ht)
    rw [Finset.sum_insert haT, Finset.card_insert_of_notMem haT, Finset.sum_range_succ]
    -- `a` exceeds `|T|` distinct elements each `≥ 2`, so `a ≥ |T| + 2`
    have hcard : T.card + 2 ≤ a := by
      have : T ⊆ Finset.Ico 2 a := fun t ht => Finset.mem_Ico.2 ⟨hT' t ht, ha t ht⟩
      have := Finset.card_le_card this
      rw [Nat.card_Ico] at this
      have := hT a (Finset.mem_insert_self _ _)
      omega
    have h1 : (a : ℝ)⁻¹ ≤ ((T.card : ℝ) + 2)⁻¹ := by
      have ha2 : (2 : ℝ) ≤ a := by exact_mod_cast hT a (Finset.mem_insert_self _ _)
      rw [inv_le_inv₀ (by linarith) (by positivity)]
      exact_mod_cast hcard
    linarith [ih hT']

/-- `∑_{k<n} 1/(k+2) ≤ log n + 1`. -/
lemma sum_range_inv_add_two_le (n : ℕ) :
    ∑ k ∈ range n, ((k : ℝ) + 2)⁻¹ ≤ Real.log n + 1 := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp
  have h := harmonic_le_one_add_log n
  have hh : (harmonic n : ℝ) = ∑ k ∈ range n, ((k : ℝ) + 1)⁻¹ := by
    rw [harmonic]; push_cast; rfl
  rw [hh] at h
  have : ∑ k ∈ range n, ((k : ℝ) + 2)⁻¹ ≤ ∑ k ∈ range n, ((k : ℝ) + 1)⁻¹ :=
    Finset.sum_le_sum fun k _ => by
      rw [inv_le_inv₀ (by positivity) (by positivity)]; linarith
  linarith

/-- **Excluded primes**: any finset of integers `≥ 2` has harmonic mass at most `log |T| + 1`. -/
theorem sum_inv_le_log_card_add_one (T : Finset ℕ) (hT : ∀ t ∈ T, 2 ≤ t) :
    ∑ t ∈ T, (t : ℝ)⁻¹ ≤ Real.log T.card + 1 :=
  (sum_inv_le_sum_range_card T hT).trans (sum_range_inv_add_two_le _)

end NormalNumbers.G4
