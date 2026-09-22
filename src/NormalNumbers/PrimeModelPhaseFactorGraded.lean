import NormalNumbers.PrimeModelPhaseFactor
import NormalNumbers.PrimeModelPhaseAlgebraGraded

/-!
# Theorem A: the graded phase factorisation

Lap 6c of `KICKOFF-2026-09-22-multicutoff-lean.md`; spec `papers/ROUND2-multicutoff-fable.md` §2
("Phase factorisation").  With per-site cutoffs `y_j` the truncated window term still splits as

    ∏_j z_j^{ω_{≤ y_j}(n+j+1)} = g₁(n mod k#) · ∏_{p ∈ midPrimes} localPhase (z^{(p)}) (s_p(n)),

but the site vector is now **per prime**: site `j` sees `p` only when `p ≤ y_j`, so

    z^{(p)}_j = if p ≤ y_j then z_j else 1        (`zSee`).

The residue factor is unchanged (`p ≤ k ≤ y_j` for every site).  Since
`Radical.radical_phase_product_prime` is already stated for a per-prime site vector, the model
expectation of the graded state phase is `∏_p (1 + (∑_j (z^{(p)}_j − 1))/p)`, and
`sum_zSee_sub_one_eq_prefixA` identifies `∑_j (z^{(p)}_j − 1)` with the prefix defect
`PhaseAlgebra.prefixA z (dsee p)` for a **monotone (decreasing) schedule** — which is exactly the
input of the graded E5 bound `model_phase_norm_le_graded`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.PhaseFactor

open NormalNumbers.PrimeModel.Radical NormalNumbers.PrimeModel.RadicalState
open NormalNumbers.PrimeModel.PhaseAlgebra

variable (S : ℕ → Prop) [DecidablePred S]

/-- The site vector a prime `p` actually sees: site `j` contributes only if `p ≤ y j`. -/
noncomputable def zSee (k : ℕ) (y : Fin k → ℕ) (h : ℤ) (p : ℕ) : Fin k → ℂ :=
  fun j => if p ≤ y j then zPhase h k j else 1

theorem norm_zSee (k : ℕ) (y : Fin k → ℕ) (h : ℤ) (p : ℕ) (j : Fin k) :
    ‖zSee k y h p j‖ = 1 := by
  rw [zSee]
  split
  · exact norm_zPhase h k j
  · norm_num

/-- The graded state phase. -/
noncomputable def statePhaseG (k : ℕ) (y : Fin k → ℕ) (Y : ℕ) (h : ℤ)
    (s : {q // q ∈ midPrimes S k Y} → Option (Fin k)) : ℂ :=
  ∏ i : {q // q ∈ midPrimes S k Y}, localPhase k (zSee k y h i.val) (s i)

theorem norm_statePhaseG_le (k : ℕ) (y : Fin k → ℕ) (Y : ℕ) (h : ℤ)
    (s : {q // q ∈ midPrimes S k Y} → Option (Fin k)) : ‖statePhaseG S k y Y h s‖ ≤ 1 := by
  rw [statePhaseG, norm_prod]
  refine Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => ?_
  cases hsi : s i with
  | none => simp
  | some t => rw [localPhase_some, norm_zSee]

private lemma prod_ite_eq_pow_card' (A : Finset ℕ) (z : ℂ) (P : ℕ → Prop) [DecidablePred P] :
    ∏ p ∈ A, (if P p then z else 1) = z ^ (A.filter P).card := by
  classical
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

private lemma dvd_mod_of_dvd' {p Q n a : ℕ} (hpQ : p ∣ Q) :
    p ∣ n % Q + a + 1 ↔ p ∣ n + a + 1 := by
  have h1 : n % Q + a + 1 ≡ n + a + 1 [MOD p] :=
    (((Nat.mod_modEq n Q).of_dvd hpQ).add_right a).add_right 1
  rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
  exact ⟨fun hd => h1.symm.trans hd, fun hd => h1.trans hd⟩

private lemma prod_ite_eq_localPhase' {k p n : ℕ} (hp : k < p) (z : Fin k → ℂ) :
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

/-- **The graded phase factorisation.** -/
theorem phase_factorisationG (k : ℕ) (y : Fin k → ℕ) (Y : ℕ) (hk : 1 ≤ k)
    (hky : ∀ j, k ≤ y j) (hyY : ∀ j, y j ≤ Y) (h : ℤ) (n : ℕ) :
    ∏ j : Fin k, zPhase h k j ^ omegaLe S (y j) (n + j.val + 1)
      = residuePhase S k h (n % primorial k)
          * statePhaseG S k y Y h (actualState k (midPrimes S k Y) n) := by
  classical
  -- split `omegaLe` at `k`
  have hsplit : ∀ j : Fin k,
      omegaLe S (y j) (n + j.val + 1)
        = ((smallPrimes S k).filter (fun p => p ∣ n + j.val + 1)).card
          + ((midPrimes S k Y).filter (fun p => p ≤ y j ∧ p ∣ n + j.val + 1)).card := by
    intro j
    rw [omegaLe]
    have hunion : ((n + j.val + 1).primeFactors.filter S).filter (fun p => p ≤ y j)
        = ((smallPrimes S k).filter (fun p => p ∣ n + j.val + 1))
          ∪ ((midPrimes S k Y).filter (fun p => p ≤ y j ∧ p ∣ n + j.val + 1)) := by
      ext p
      simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_union, smallPrimes,
        midPrimes, Finset.mem_Iic]
      constructor
      · rintro ⟨⟨⟨hp, hdvd, -⟩, hSp⟩, hpy⟩
        by_cases hpk : p ≤ k
        · exact Or.inl ⟨⟨hpk, hp, hSp⟩, hdvd⟩
        · exact Or.inr ⟨⟨le_trans hpy (hyY j), hp, hSp, by omega⟩, hpy, hdvd⟩
      · rintro (⟨⟨hpk, hp, hSp⟩, hdvd⟩ | ⟨⟨-, hp, hSp, hkp⟩, hpy, hdvd⟩)
        · exact ⟨⟨⟨hp, hdvd, by omega⟩, hSp⟩, le_trans hpk (hky j)⟩
        · exact ⟨⟨⟨hp, hdvd, by omega⟩, hSp⟩, hpy⟩
    rw [hunion, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro p hp hp'
    rw [Finset.mem_filter, smallPrimes, Finset.mem_filter, Finset.mem_Iic] at hp
    rw [Finset.mem_filter, midPrimes, Finset.mem_filter, Finset.mem_Iic] at hp'
    omega
  have hprod : ∏ j : Fin k, zPhase h k j ^ omegaLe S (y j) (n + j.val + 1)
      = (∏ j : Fin k, zPhase h k j ^ ((smallPrimes S k).filter (fun p => p ∣ n + j.val + 1)).card)
        * ∏ j : Fin k,
            zPhase h k j ^ ((midPrimes S k Y).filter
              (fun p => p ≤ y j ∧ p ∣ n + j.val + 1)).card := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hsplit j, pow_add]
  rw [hprod]
  congr 1
  · -- the small primes: residue factor, unchanged
    rw [residuePhase, Finset.prod_comm]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [prod_ite_eq_pow_card']
    congr 2
    apply Finset.filter_congr
    intro p hp
    have hpQ : p ∣ primorial k := by
      rw [smallPrimes, Finset.mem_filter, Finset.mem_Iic] at hp
      exact (Nat.Prime.dvd_primorial_iff hp.2.1).mpr hp.1
    simpa using (dvd_mod_of_dvd' (n := n) (a := j.val) hpQ).symm
  · -- the mid primes: graded state factor
    rw [statePhaseG]
    have hRHS : (∏ i : {q // q ∈ midPrimes S k Y},
        localPhase k (zSee k y h (i : ℕ)) (actualState k (midPrimes S k Y) n i))
        = ∏ p ∈ midPrimes S k Y, localPhase k (zSee k y h p) (hitShift k p n) :=
      Finset.prod_coe_sort (midPrimes S k Y)
        (fun p => localPhase k (zSee k y h p) (hitShift k p n))
    rw [hRHS]
    have hL : ∀ j : Fin k,
        zPhase h k j ^ ((midPrimes S k Y).filter (fun p => p ≤ y j ∧ p ∣ n + j.val + 1)).card
          = ∏ p ∈ midPrimes S k Y,
              (if p ≤ y j ∧ p ∣ n + j.val + 1 then zPhase h k j else 1) :=
      fun j => (prod_ite_eq_pow_card' _ _ _).symm
    rw [Finset.prod_congr rfl (fun j (_ : j ∈ Finset.univ) => hL j), Finset.prod_comm]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hkp : k < p := ((mem_midPrimes S).mp hp).2.2.1
    rw [← prod_ite_eq_localPhase' hkp (zSee k y h p)]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [zSee]
    by_cases hpy : p ≤ y j
    · simp [hpy]
    · simp [hpy]

/-! ### The prefix identification for a monotone schedule -/

/-- For a **decreasing** schedule `y` the sites that see `p` are a prefix `{j : j < d}`, so the
per-prime defect `∑_j (z^{(p)}_j − 1)` is the prefix defect `A_d` of the graded E5 bound. -/
theorem sum_zSee_sub_one_eq_prefixA (k : ℕ) (y : Fin k → ℕ) (h : ℤ) (p : ℕ) (d : ℕ)
    (hd : ∀ j : Fin k, p ≤ y j ↔ j.val < d) :
    ∑ j : Fin k, (zSee k y h p j - 1) = prefixA (zPhase h k) d := by
  classical
  have hzero : ∑ j ∈ Finset.univ.filter (fun j : Fin k => ¬ j.val < d),
      (zSee k y h p j - 1) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hnot : ¬ j.val < d := (Finset.mem_filter.1 hj).2
    have hp : ¬ p ≤ y j := fun hc => hnot ((hd j).1 hc)
    rw [zSee]
    simp [hp]
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : Fin k => j.val < d) (fun j => zSee k y h p j - 1)
  rw [hzero, add_zero] at hsplit
  rw [← hsplit, prefixA]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hlt : j.val < d := (Finset.mem_filter.1 hj).2
  rw [zSee, if_pos ((hd j).2 hlt)]

/-- The number of sites that see `p`, for a decreasing schedule: the seeing set is a down-set
in `Fin k`, hence the initial segment of its own cardinality. -/
theorem exists_prefix_count (k : ℕ) (y : Fin k → ℕ)
    (hmono : ∀ i j : Fin k, i ≤ j → y j ≤ y i) (p : ℕ) :
    ∃ d : ℕ, ∀ j : Fin k, p ≤ y j ↔ j.val < d := by
  classical
  set F : Finset (Fin k) := Finset.univ.filter (fun j : Fin k => p ≤ y j) with hF
  have hmemF : ∀ j : Fin k, j ∈ F ↔ p ≤ y j := by
    intro j; rw [hF, Finset.mem_filter]; simp
  have hdown : ∀ i j : Fin k, i ≤ j → p ≤ y j → p ≤ y i := fun i j hij hp =>
    le_trans hp (hmono i j hij)
  refine ⟨F.card, fun j => ?_⟩
  rw [← hmemF j]
  constructor
  · intro hjF
    have hsub : (Finset.univ.filter (fun i : Fin k => i ≤ j)) ⊆ F := by
      intro i hi
      rw [hmemF]
      exact hdown i j (Finset.mem_filter.1 hi).2 ((hmemF j).1 hjF)
    have hc := Finset.card_le_card hsub
    have hIic : (Finset.univ.filter (fun i : Fin k => i ≤ j)) = Finset.Iic j := by
      ext i; rw [Finset.mem_filter, Finset.mem_Iic]; simp
    rw [hIic, Fin.card_Iic] at hc
    omega
  · intro hjlt
    by_contra hjF
    have hsub : F ⊆ Finset.univ.filter (fun i : Fin k => i.val < j.val) := by
      intro i hi
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hc
      push_neg at hc
      exact hjF ((hmemF j).2 (hdown j i (by exact hc) ((hmemF i).1 hi)))
    have hc := Finset.card_le_card hsub
    have hIio : (Finset.univ.filter (fun i : Fin k => i.val < j.val)) = Finset.Iio j := by
      ext i; rw [Finset.mem_filter, Finset.mem_Iio, Fin.lt_def]; simp
    rw [hIio, Fin.card_Iio] at hc
    omega

end NormalNumbers.PrimeModel.PhaseFactor
