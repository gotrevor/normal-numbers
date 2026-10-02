/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4FarTail
import NormalNumbers.G4SubsetWeight
import NormalNumbers.G4SubsetSchedule

/-!
# The far tail restricted to `S`-primes

`G4FarTail.sum_omegaR_add_le` bounds the progression mean of `ω` by `log(X/|P|) + log log X`, an
all-primes harmonic sum; in the base-2 frame that term is `≈ e` and forces `e ≤ 2^{O(K²)}`
(`G4.SchedB.hypE_frame_excludes_logRate`).  For `ω_S` the same Jensen argument, with the
`S`-smooth squarefree divisor count `2^{ω_S(m)} = #{A ⊆ S-primes : ∏A ∣ m}` in place of `d(m)`,
gives `log(X/|P|) + F_S(X)` (`sum_omegaS_add_le`): the far tail sees only the `S`-mass.
This is the first half of the decoupling the reopen node `SRestrictedFrame` asks for.
-/

open Finset Real

namespace NormalNumbers.G4

open PrimeLambert

variable (S : ℕ → Prop) [DecidablePred S]

/-- The `S`-primes `≤ N`. -/
def sPrimesLe (N : ℕ) : Finset ℕ := (N + 1).primesBelow.filter S

lemma two_pow_omegaSN_eq {N m : ℕ} (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    (2 : ℝ) ^ omegaSN S m
      = ∑ A ∈ (sPrimesLe S N).powerset, if (∏ p ∈ A, p) ∣ m then (1 : ℝ) else 0 := by
  classical
  rw [Finset.sum_boole]
  have hfil : (sPrimesLe S N).powerset.filter (fun A => (∏ p ∈ A, p) ∣ m)
      = (m.primeFactors.filter S).powerset := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powerset, sPrimesLe]
    constructor
    · rintro ⟨hA, hd⟩ p hp
      have hp' := hA hp
      rw [Finset.mem_filter, Nat.mem_primesBelow] at hp'
      rw [Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨hp'.1.2, (Finset.dvd_prod_of_mem _ hp).trans hd, by omega⟩, hp'.2⟩
    · intro hA
      refine ⟨fun p hp => ?_, ?_⟩
      · have := hA hp
        rw [Finset.mem_filter, Nat.mem_primeFactors] at this
        rw [Finset.mem_filter, Nat.mem_primesBelow]
        exact ⟨⟨by have := Nat.le_of_dvd (by omega) this.1.2.1; omega, this.1.1⟩, this.2⟩
      · refine Finset.prod_primes_dvd m (fun p hp => ?_) (fun p hp => ?_)
        · have := hA hp
          rw [Finset.mem_filter, Nat.mem_primeFactors] at this
          exact this.1.1.prime
        · have := hA hp
          rw [Finset.mem_filter, Nat.mem_primeFactors] at this
          exact this.1.2.1
  rw [hfil, Finset.card_powerset]
  unfold omegaSN
  push_cast
  ring

/-- `∑_{1 ≤ m ≤ N} 2^{ω_S(m)} ≤ (N+1)·exp(F_S(N+1))`. -/
lemma sum_two_pow_omegaSN_le (N : ℕ) :
    ∑ m ∈ Finset.Ico 1 (N + 1), (2 : ℝ) ^ omegaSN S m
      ≤ (N + 1 : ℕ) * Real.exp (MertensAP.sumInvPrimesIn S (N + 1)) := by
  classical
  have hpos : ∀ A ∈ (sPrimesLe S N).powerset, 0 < ∏ p ∈ A, p := by
    intro A hA
    rw [Finset.mem_powerset] at hA
    refine Finset.prod_pos fun p hp => ?_
    have := hA hp
    rw [sPrimesLe, Finset.mem_filter, Nat.mem_primesBelow] at this
    exact this.1.2.pos
  calc ∑ m ∈ Finset.Ico 1 (N + 1), (2 : ℝ) ^ omegaSN S m
      = ∑ m ∈ Finset.Ico 1 (N + 1), ∑ A ∈ (sPrimesLe S N).powerset,
          if (∏ p ∈ A, p) ∣ m then (1 : ℝ) else 0 := by
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [Finset.mem_Ico] at hm
        exact two_pow_omegaSN_eq S (by omega) (by omega)
    _ = ∑ A ∈ (sPrimesLe S N).powerset, ∑ m ∈ Finset.Ico 1 (N + 1),
          if (∏ p ∈ A, p) ∣ m then (1 : ℝ) else 0 := Finset.sum_comm
    _ ≤ ∑ A ∈ (sPrimesLe S N).powerset, ((N + 1 : ℕ) : ℝ) * ∏ p ∈ A, (p : ℝ)⁻¹ := by
        refine Finset.sum_le_sum fun A hA => ?_
        rw [Finset.sum_boole]
        have := card_multiples_Ico_le (N + 1) (∏ p ∈ A, p) (hpos A hA)
        refine this.trans (le_of_eq ?_)
        rw [div_eq_mul_inv, Nat.cast_prod, Finset.prod_inv_distrib]
    _ = ((N + 1 : ℕ) : ℝ) * ∏ p ∈ sPrimesLe S N, (1 + (p : ℝ)⁻¹) := by
        rw [← Finset.mul_sum, Finset.prod_one_add]
    _ ≤ ((N + 1 : ℕ) : ℝ) * Real.exp (MertensAP.sumInvPrimesIn S (N + 1)) := by
        gcongr
        unfold MertensAP.sumInvPrimesIn
        rw [Real.exp_sum]
        have hs : sPrimesLe S N = (N + 1).primesBelow.filter S := rfl
        rw [hs]
        refine Finset.prod_le_prod (fun p _ => by positivity) fun p _ => ?_
        have := Real.add_one_le_exp ((p : ℝ)⁻¹)
        linarith

/-- **The `S`-restricted far tail.**  For `P ⊆ [0, X)` nonempty and `ρ ≥ 1`,
`∑_{n∈P} ω_S(n+ρ) · log 2 ≤ |P|·(log((X+ρ)/|P|) + F_S(X+ρ))`. -/
theorem sum_omegaS_add_le {X : ℕ} (P : Finset ℕ) (hP : P ⊆ Finset.range X) (hne : P.Nonempty)
    {ρ : ℕ} (hρ : 1 ≤ ρ) :
    (∑ n ∈ P, omegaS S (n + ρ)) * Real.log 2
      ≤ P.card * (Real.log (((X + ρ : ℕ) : ℝ) / P.card)
          + MertensAP.sumInvPrimesIn S (X + ρ)) := by
  classical
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hne.card_pos
  have hX : 1 ≤ X := by
    obtain ⟨n, hn⟩ := hne
    have := Finset.mem_range.1 (hP hn); omega
  set N := X + ρ - 1 with hN
  have hN1 : N + 1 = X + ρ := by omega
  have hx : ∀ n ∈ P, 0 < (2 : ℝ) ^ omegaSN S (n + ρ) := fun _ _ => by positivity
  have hstep : (∑ n ∈ P, omegaS S (n + ρ)) * Real.log 2
      = ∑ n ∈ P, Real.log ((2 : ℝ) ^ omegaSN S (n + ρ)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Real.log_pow]; rfl
  have hshift : ∑ n ∈ P, (2 : ℝ) ^ omegaSN S (n + ρ)
      ≤ ∑ m ∈ Finset.Ico 1 (N + 1), (2 : ℝ) ^ omegaSN S m := by
    rw [← Finset.sum_image (f := fun m => (2 : ℝ) ^ omegaSN S m) (s := P) (g := fun n => n + ρ)
      (fun a _ b _ h => by simpa using h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨n, hn, rfl⟩ := hm
    have := Finset.mem_range.1 (hP hn)
    rw [Finset.mem_Ico]; omega
  have hbound := (hshift.trans (sum_two_pow_omegaSN_le S N))
  rw [hN1] at hbound
  have hsum0 : 0 < ∑ n ∈ P, (2 : ℝ) ^ omegaSN S (n + ρ) := Finset.sum_pos hx hne
  rw [hstep]
  refine (sum_log_le_card_mul_log_avg P hne _ hx).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hc.le
  have hXρ : (0 : ℝ) < ((X + ρ : ℕ) : ℝ) := by exact_mod_cast (show 0 < X + ρ by omega)
  calc Real.log ((∑ n ∈ P, (2 : ℝ) ^ omegaSN S (n + ρ)) / P.card)
      ≤ Real.log (((X + ρ : ℕ) : ℝ) * Real.exp (MertensAP.sumInvPrimesIn S (X + ρ)) / P.card) :=
        Real.log_le_log (div_pos hsum0 hc) (div_le_div_of_nonneg_right hbound hc.le)
    _ = Real.log (((X + ρ : ℕ) : ℝ) / P.card) + MertensAP.sumInvPrimesIn S (X + ρ) := by
        rw [mul_div_right_comm, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]

end NormalNumbers.G4
