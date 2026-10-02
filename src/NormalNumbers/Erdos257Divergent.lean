/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Base2DecAssembly
import NormalNumbers.Erdos257Base2

/-!
# Base-2 disjunctivity for every divergent prime set

`isDisjunctive_subsetLambert_two_of_divergent`: if `S` is a set of primes with
`Σ_{p∈S} 1/p = ∞`, then `Σ_{p∈S} 1/(2ᵖ − 1)` is disjunctive in base 2, conditional on
Tao–Teräväinen Thm 3.1(i) (`CastingOut.TTEquidistributedDyadic`).  No Mertens rate is needed:
the decoupled frame (`G4Base2DecAssembly`) takes the first cutoff at which `F_S` crosses the
demand.
-/

open Filter

namespace NormalNumbers.Erdos257

open G4

/-- Divergence of `Σ_{p∈S} 1/p` makes the tower sums `F_S(2^{2^e}+1)` unbounded. -/
theorem towerF_unbounded {S : Set ℕ} [DecidablePred (· ∈ S)] (hS : ∀ p ∈ S, p.Prime)
    (hdiv : ¬ Summable (fun p : S => (1 : ℝ) / p.1)) :
    ∀ B : ℝ, ∃ e, B ≤ towerF (· ∈ S) e := by
  classical
  intro B
  by_contra hcon
  push_neg at hcon
  apply hdiv
  refine summable_of_sum_le (c := B) (fun p => by positivity) fun u => ?_
  set v : Finset ℕ := u.map (Function.Embedding.subtype _) with hv
  set e : ℕ := v.sup id with he
  have hsum : ∑ x ∈ u, (1 : ℝ) / x.1 = ∑ n ∈ v, (n : ℝ)⁻¹ := by
    rw [hv, Finset.sum_map]; simp [one_div]
  rw [hsum]
  refine le_trans ?_ (hcon e).le
  unfold towerF MertensAP.sumInvPrimesIn
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
  intro n hn
  have hnS : n ∈ S := by
    rw [hv, Finset.mem_map] at hn
    obtain ⟨x, -, rfl⟩ := hn
    exact x.2
  have hne : n ≤ e := Finset.le_sup (f := id) hn
  have h1 : n < 2 ^ n := Nat.lt_two_pow_self
  have h2 : 2 ^ n ≤ 2 ^ 2 ^ e :=
    Nat.pow_le_pow_right (by norm_num) (hne.trans (Nat.lt_two_pow_self).le)
  simp only [Finset.mem_filter, Nat.mem_primesBelow]
  exact ⟨⟨by omega, hS n hnS⟩, hnS⟩

/-- **Base-2 disjunctivity for every divergent prime set** (conditional on TT 3.1(i)). -/
theorem isDisjunctive_subsetLambert_two_of_divergent (htt : CastingOut.TTEquidistributedDyadic)
    {S : Set ℕ} [DecidablePred (· ∈ S)] (hS : ∀ p ∈ S, p.Prime)
    (hdiv : ¬ Summable (fun p : S => (1 : ℝ) / p.1)) :
    IsDisjunctive 2 (PrimeLambert.subsetLambert (· ∈ S) 2) := by
  refine G4.isDisjunctive_subsetLambert_of_witnessCS (· ∈ S) 2 le_rfl fun ℓ w hw homit => ?_
  rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
  · exfalso
    subst hℓ
    have hw0 : w = 0 := by simpa using hw
    subst hw0
    have := homit 0
    simp only [Nat.cast_zero, pow_zero, zero_add, div_one] at this
    exact this (orbit_mem_Ico 2 (PrimeLambert.subsetLambert (· ∈ S) 2) 0)
  · exact G4.SchedB.Dec.exists_scheduleWitnessSCS_two_of_divergent (· ∈ S)
      (veryLargeCovSupplyEff_of_TT htt) (towerF_unbounded hS hdiv) ℓ w hℓ

end NormalNumbers.Erdos257
