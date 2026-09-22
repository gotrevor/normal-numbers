import NormalNumbers.PrimeModelPhaseFactorGraded

/-!
# The phase factorisation with an arbitrary split point

Lap 6f of `KICKOFF-2026-09-22-multicutoff-lean.md`.  `phase_factorisationG` splits the primes at
`k`: the primes `≤ k` go into the residue modulus `k#` and the primes `> k` carry the radical
state.  Fable §2 (E5) and Astra §4 need the split at **`2k`** instead — `Q = primorial (2k)` —
because the graded sieve assigns `d_p = k` classes to each sieve prime and therefore needs
`2 d_p ≤ p`, i.e. `p > 2k`.  Nothing in the argument depends on the split point being `k`, so
this file re-proves the factorisation with an arbitrary `m ≥ k`:

    ∏_j z_j^{ω_{≤ y_j}(n+j+1)} = g₁^{(m)}(n mod m#) · ∏_{p ∈ midPrimes S m Y} localPhase (z^{(p)}) s_p.

The site index still runs over `Fin k`; only the prime bookkeeping moves.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.PhaseFactor

open NormalNumbers.PrimeModel.Radical NormalNumbers.PrimeModel.RadicalState
open NormalNumbers.PrimeModel.PhaseAlgebra

variable (S : ℕ → Prop) [DecidablePred S]

/-- The residue factor with the split at `m`: the `S`-primes `≤ m`, a function of `n mod m#`. -/
noncomputable def residuePhaseM (k m : ℕ) (h : ℤ) (r : ℕ) : ℂ :=
  ∏ p ∈ smallPrimes S m, ∏ j : Fin k, if p ∣ r + j.val + 1 then zPhase h k j else 1

theorem norm_residuePhaseM_le (k m : ℕ) (h : ℤ) (r : ℕ) : ‖residuePhaseM S k m h r‖ ≤ 1 := by
  rw [residuePhaseM, norm_prod]
  refine Finset.prod_le_one (fun i _ => norm_nonneg _) fun p _ => ?_
  rw [norm_prod]
  refine Finset.prod_le_one (fun i _ => norm_nonneg _) fun j _ => ?_
  split
  · exact le_of_eq (norm_zPhase h k j)
  · norm_num

/-- The graded state phase with the split at `m`. -/
noncomputable def statePhaseGM (k m : ℕ) (y : Fin k → ℕ) (Y : ℕ) (h : ℤ)
    (s : {q // q ∈ midPrimes S m Y} → Option (Fin k)) : ℂ :=
  ∏ i : {q // q ∈ midPrimes S m Y}, localPhase k (zSee k y h i.val) (s i)

theorem norm_statePhaseGM_le (k m : ℕ) (y : Fin k → ℕ) (Y : ℕ) (h : ℤ)
    (s : {q // q ∈ midPrimes S m Y} → Option (Fin k)) : ‖statePhaseGM S k m y Y h s‖ ≤ 1 := by
  rw [statePhaseGM, norm_prod]
  refine Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => ?_
  cases hsi : s i with
  | none => simp
  | some t => rw [localPhase_some, norm_zSee]

private lemma prod_ite_eq_pow_card'' (A : Finset ℕ) (z : ℂ) (Pr : ℕ → Prop) [DecidablePred Pr] :
    ∏ p ∈ A, (if Pr p then z else 1) = z ^ (A.filter Pr).card := by
  classical
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

private lemma dvd_mod_of_dvd'' {p Q n a : ℕ} (hpQ : p ∣ Q) :
    p ∣ n % Q + a + 1 ↔ p ∣ n + a + 1 := by
  have h1 : n % Q + a + 1 ≡ n + a + 1 [MOD p] :=
    (((Nat.mod_modEq n Q).of_dvd hpQ).add_right a).add_right 1
  rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
  exact ⟨fun hd => h1.symm.trans hd, fun hd => h1.trans hd⟩

private lemma prod_ite_eq_localPhase'' {k p n : ℕ} (hp : k < p) (z : Fin k → ℂ) :
    ∏ j : Fin k, (if p ∣ n + j.val + 1 then z j else 1) = localPhase k z (hitShift k p n) := by
  classical
  cases hs : hitShift k p n with
  | none =>
      have hnone := hitShift_eq_none_iff.mp hs
      simp only [localPhase]
      exact Finset.prod_eq_one fun j _ => if_neg (hnone j)
  | some t =>
      have ht := (hitShift_eq_some_iff hp t).mp hs
      have hsingle : ∏ j : Fin k, (if p ∣ n + j.val + 1 then z j else 1)
          = if p ∣ n + t.val + 1 then z t else 1 :=
        Finset.prod_eq_single t
          (fun j _ hjt => if_neg (fun hd => hjt (hit_unique hp hd ht)))
          (fun hmem => absurd (Finset.mem_univ t) hmem)
      simp only [localPhase]
      rw [hsingle, if_pos ht]

/-- **The graded phase factorisation with the split at `m ≥ k`.** -/
theorem phase_factorisationGM (k m : ℕ) (y : Fin k → ℕ) (Y : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m)
    (hmy : ∀ j, m ≤ y j) (hyY : ∀ j, y j ≤ Y) (h : ℤ) (n : ℕ) :
    ∏ j : Fin k, zPhase h k j ^ omegaLe S (y j) (n + j.val + 1)
      = residuePhaseM S k m h (n % primorial m)
          * statePhaseGM S k m y Y h (actualState k (midPrimes S m Y) n) := by
  classical
  have hsplit : ∀ j : Fin k,
      omegaLe S (y j) (n + j.val + 1)
        = ((smallPrimes S m).filter (fun p => p ∣ n + j.val + 1)).card
          + ((midPrimes S m Y).filter (fun p => p ≤ y j ∧ p ∣ n + j.val + 1)).card := by
    intro j
    rw [omegaLe]
    have hunion : ((n + j.val + 1).primeFactors.filter S).filter (fun p => p ≤ y j)
        = ((smallPrimes S m).filter (fun p => p ∣ n + j.val + 1))
          ∪ ((midPrimes S m Y).filter (fun p => p ≤ y j ∧ p ∣ n + j.val + 1)) := by
      ext p
      simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_union, smallPrimes,
        midPrimes, Finset.mem_Iic]
      constructor
      · rintro ⟨⟨⟨hp, hdvd, -⟩, hSp⟩, hpy⟩
        by_cases hpm : p ≤ m
        · exact Or.inl ⟨⟨hpm, hp, hSp⟩, hdvd⟩
        · exact Or.inr ⟨⟨le_trans hpy (hyY j), hp, hSp, by omega⟩, hpy, hdvd⟩
      · rintro (⟨⟨hpm, hp, hSp⟩, hdvd⟩ | ⟨⟨-, hp, hSp, hmp⟩, hpy, hdvd⟩)
        · exact ⟨⟨⟨hp, hdvd, by omega⟩, hSp⟩, le_trans hpm (hmy j)⟩
        · exact ⟨⟨⟨hp, hdvd, by omega⟩, hSp⟩, hpy⟩
    rw [hunion, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro p hp hp'
    rw [Finset.mem_filter, smallPrimes, Finset.mem_filter, Finset.mem_Iic] at hp
    rw [Finset.mem_filter, midPrimes, Finset.mem_filter, Finset.mem_Iic] at hp'
    omega
  have hprod : ∏ j : Fin k, zPhase h k j ^ omegaLe S (y j) (n + j.val + 1)
      = (∏ j : Fin k, zPhase h k j ^ ((smallPrimes S m).filter (fun p => p ∣ n + j.val + 1)).card)
        * ∏ j : Fin k,
            zPhase h k j ^ ((midPrimes S m Y).filter
              (fun p => p ≤ y j ∧ p ∣ n + j.val + 1)).card := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hsplit j, pow_add]
  rw [hprod]
  congr 1
  · rw [residuePhaseM, Finset.prod_comm]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [prod_ite_eq_pow_card'']
    congr 2
    apply Finset.filter_congr
    intro p hp
    have hpQ : p ∣ primorial m := by
      rw [smallPrimes, Finset.mem_filter, Finset.mem_Iic] at hp
      exact (Nat.Prime.dvd_primorial_iff hp.2.1).mpr hp.1
    simpa using (dvd_mod_of_dvd'' (n := n) (a := j.val) hpQ).symm
  · rw [statePhaseGM]
    have hRHS : (∏ i : {q // q ∈ midPrimes S m Y},
        localPhase k (zSee k y h i.val) (actualState k (midPrimes S m Y) n i))
        = ∏ p ∈ midPrimes S m Y, localPhase k (zSee k y h p) (hitShift k p n) :=
      Finset.prod_coe_sort (midPrimes S m Y)
        (fun p => localPhase k (zSee k y h p) (hitShift k p n))
    rw [hRHS]
    have hL : ∀ j : Fin k,
        zPhase h k j ^ ((midPrimes S m Y).filter (fun p => p ≤ y j ∧ p ∣ n + j.val + 1)).card
          = ∏ p ∈ midPrimes S m Y,
              (if p ≤ y j ∧ p ∣ n + j.val + 1 then zPhase h k j else 1) :=
      fun j => (prod_ite_eq_pow_card'' _ _ _).symm
    rw [Finset.prod_congr rfl (fun j (_ : j ∈ Finset.univ) => hL j), Finset.prod_comm]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hmp : m < p := ((mem_midPrimes S).mp hp).2.2.1
    have hkp : k < p := lt_of_le_of_lt hkm hmp
    rw [← prod_ite_eq_localPhase'' hkp (zSee k y h p)]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [zSee]
    by_cases hpy : p ≤ y j
    · simp [hpy]
    · simp [hpy]

end NormalNumbers.PrimeModel.PhaseFactor
