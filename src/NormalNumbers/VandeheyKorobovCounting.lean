/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyKorobovDivisors

/-!
# Inclusion--exclusion count for Vandehey's Korobov estimate

This file proves Vandehey's Lemma 4.3. Exact inclusion--exclusion over the prime factors
gives the Euler-totient main term, while the one-unit error for each squarefree divisor
adds to `2^s` when the modulus has at most `s` distinct prime factors.
-/

open Finset Nat
open scoped BigOperators

namespace NormalNumbers.VandeheyKorobov

private def noPrimeDiv (P : Finset ℕ) (u : ℕ) : Prop := ∀ p ∈ P, ¬ p ∣ u + 1
private instance (P : Finset ℕ) : DecidablePred (noPrimeDiv P) := fun _ => by unfold noPrimeDiv; infer_instance
private def allPrimeDiv (E : Finset ℕ) (u : ℕ) : Prop := ∀ p ∈ E, p ∣ u + 1
private instance (E : Finset ℕ) : DecidablePred (allPrimeDiv E) := fun _ => by unfold allPrimeDiv; infer_instance
private def hitSet (P : Finset ℕ) (u : ℕ) : Finset ℕ := P.filter fun p => p ∣ u + 1

private lemma legendre_identity (P : Finset ℕ) (X : ℕ) :
    ∑ E ∈ P.powerset, (-1 : ℝ) ^ E.card * (((range X).filter (allPrimeDiv E)).card : ℝ) =
      (((range X).filter (noPrimeDiv P)).card : ℝ) := by
  classical
  have hind : ∀ (Φ : ℕ → Prop) (_ : DecidablePred Φ),
      (((range X).filter Φ).card : ℝ) = ∑ u ∈ range X, if Φ u then (1 : ℝ) else 0 := by
    intro Φ _; rw [Finset.sum_boole]
  rw [hind (noPrimeDiv P) inferInstance]
  have hL : ∑ E ∈ P.powerset, (-1 : ℝ) ^ E.card * (((range X).filter (allPrimeDiv E)).card : ℝ) =
      ∑ u ∈ range X, ∑ E ∈ P.powerset,
        (-1 : ℝ) ^ E.card * (if allPrimeDiv E u then (1 : ℝ) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun E _ => ?_
    rw [hind (allPrimeDiv E) inferInstance, Finset.mul_sum]
  rw [hL]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hsub : ∀ E ∈ P.powerset, allPrimeDiv E u ↔ E ⊆ hitSet P u := by
    intro E hE
    simp only [allPrimeDiv, hitSet, Finset.subset_iff, Finset.mem_filter]
    exact forall_congr' fun p => imp_congr_right fun hp =>
      ⟨fun hd => ⟨(Finset.mem_powerset.mp hE) hp, hd⟩, fun h => h.2⟩
  have hsum : ∑ E ∈ P.powerset,
        (-1 : ℝ) ^ E.card * (if allPrimeDiv E u then (1 : ℝ) else 0) =
      ∑ E ∈ (hitSet P u).powerset, (-1 : ℝ) ^ E.card := by
    calc
      _ = ∑ E ∈ P.powerset.filter (fun E => allPrimeDiv E u), (-1 : ℝ) ^ E.card := by
        have hif : ∀ E ∈ P.powerset,
            (-1 : ℝ) ^ E.card * (if allPrimeDiv E u then (1 : ℝ) else 0) =
              if allPrimeDiv E u then (-1 : ℝ) ^ E.card else 0 := by
          intro E _
          by_cases h : allPrimeDiv E u <;> simp [h]
        rw [Finset.sum_congr rfl hif, Finset.sum_filter]
      _ = _ := by
        apply Finset.sum_congr
        ext E
        simp only [Finset.mem_filter, Finset.mem_powerset]
        constructor
        · rintro ⟨hEP, h⟩
          exact (hsub E (Finset.mem_powerset.mpr hEP)).mp h
        · intro hE
          have hEP := hE.trans (Finset.filter_subset _ _)
          exact ⟨hEP, (hsub E (Finset.mem_powerset.mpr hEP)).mpr hE⟩
        intro E _
        rfl
  rw [hsum]
  have hpow : ∑ E ∈ (hitSet P u).powerset, (-1 : ℝ) ^ E.card =
      ((if hitSet P u = ∅ then (1 : ℤ) else 0 : ℤ) : ℝ) := by
    rw [← Finset.sum_powerset_neg_one_pow_card]
    push_cast
    rfl
  rw [hpow]
  have hempty : hitSet P u = ∅ ↔ noPrimeDiv P u := by
    unfold noPrimeDiv hitSet
    simp [Finset.filter_eq_empty_iff]
  by_cases h : hitSet P u = ∅
  · simp [h, hempty.mp h]
  · have hn : ¬ noPrimeDiv P u := fun hn => h (hempty.mpr hn)
    simp [h, hn]

private lemma allPrimeDiv_iff_prod_dvd {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) (u : ℕ) :
    allPrimeDiv E u ↔ (∏ p ∈ E, p) ∣ u + 1 := by
  constructor
  · intro h
    have hsub : E ⊆ (u + 1).primeFactors := by
      intro p hp
      exact (Nat.mem_primeFactors_of_ne_zero (by omega)).2 ⟨hE p hp, h p hp⟩
    exact dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ hsub) (Nat.prod_primeFactors_dvd (u + 1))
  · intro h p hp
    exact dvd_trans (Finset.dvd_prod_of_mem (fun x => x) hp) h

private lemma abs_card_allPrimeDiv_sub_le_one (P E : Finset ℕ) (hE : E ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (X : ℕ) :
    |(((range X).filter (allPrimeDiv E)).card : ℝ) - (X : ℝ) / (∏ p ∈ E, p : ℕ)| ≤ 1 := by
  have hcard : ((range X).filter (allPrimeDiv E)).card = X / (∏ p ∈ E, p) := by
    rw [show (range X).filter (allPrimeDiv E) =
        (range X).filter (fun u => (∏ p ∈ E, p) ∣ u + 1) by
      ext u
      simp only [mem_filter, mem_range, and_congr_right_iff]
      intro _
      exact allPrimeDiv_iff_prod_dvd (fun p hp => hP p (hE hp)) u]
    exact Nat.card_multiples X (∏ p ∈ E, p)
  rw [hcard]
  have hd : 0 < ∏ p ∈ E, p := Finset.prod_pos fun p hp => (hP p (hE hp)).pos
  have hfloor : (X : ℝ) / (∏ p ∈ E, p : ℕ) - 1 < (X / ∏ p ∈ E, p : ℕ) := by
    have hdR : (0 : ℝ) < (∏ p ∈ E, p : ℕ) := by exact_mod_cast hd
    rw [div_sub_one hdR.ne', div_lt_iff₀ hdR]
    have heq := Nat.div_add_mod X (∏ p ∈ E, p)
    have hmod := Nat.mod_lt X hd
    have heqR : ((∏ p ∈ E, p : ℕ) : ℝ) * (X / ∏ p ∈ E, p : ℕ) +
        (X % ∏ p ∈ E, p : ℕ) = X := by exact_mod_cast heq
    have hmodR : ((X % ∏ p ∈ E, p : ℕ) : ℝ) < (∏ p ∈ E, p : ℕ) := by
      exact_mod_cast hmod
    nlinarith
  have hle : ((X / ∏ p ∈ E, p : ℕ) : ℝ) ≤ (X : ℝ) / (∏ p ∈ E, p : ℕ) := by
    rw [le_div_iff₀ (by exact_mod_cast hd)]
    exact_mod_cast Nat.div_mul_le_self X (∏ p ∈ E, p)
  rw [abs_le]
  constructor <;> linarith

private lemma legendre_main_term (P : Finset ℕ) (X : ℕ) :
    ∑ E ∈ P.powerset, (-1 : ℝ) ^ E.card * ((X : ℝ) / (∏ p ∈ E, p : ℕ)) =
      (X : ℝ) * ∏ p ∈ P, (1 - (1 : ℝ) / p) := by
  have hPe : ∏ p ∈ P, (1 - (1 : ℝ) / p) =
      ∑ E ∈ P.powerset, ∏ p ∈ E, (-(1 : ℝ) / p) := by
    rw [← Finset.prod_one_add]
    exact Finset.prod_congr rfl fun p _ => by ring
  rw [hPe, Finset.mul_sum]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [Finset.prod_div_distrib, Finset.prod_const]
  push_cast
  rw [neg_pow]
  ring

private lemma noPrimeDiv_primeFactors_iff (q u : ℕ) (hq : q ≠ 0) :
    noPrimeDiv q.primeFactors u ↔ Nat.Coprime (u + 1) q := by
  constructor
  · intro h
    by_contra hcop
    obtain ⟨p, hp, hpu, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    exact h p ((Nat.mem_primeFactors_of_ne_zero hq).2 ⟨hp, hpq⟩) hpu
  · intro h p hpq hpu
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpq
    have hpq' : p ∣ q := Nat.dvd_of_mem_primeFactors hpq
    exact (hp.coprime_iff_not_dvd.mp (h.symm.coprime_dvd_left hpq')) hpu

private lemma prod_one_sub_inv_eq_totient_div (q : ℕ) (hq : q ≠ 0) :
    (∏ p ∈ q.primeFactors, (1 - (1 : ℝ) / (p : ℝ))) = (q.totient : ℝ) / q := by
  have hrat := Nat.totient_eq_mul_prod_factors q
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have hprodQ : (∏ p ∈ q.primeFactors, (1 - (p : ℚ)⁻¹)) = (q.totient : ℚ) / q := by
    rw [hrat, mul_div_cancel_left₀ _ hqQ]
  have hcast := congrArg ((↑) : ℚ → ℝ) hprodQ
  push_cast at hcast
  simpa [div_eq_mul_inv] using hcast

private lemma coprime_count_abs (q X : ℕ) (hq : q ≠ 0) :
    |(((Ico 1 (X + 1)).filter (fun i => Nat.Coprime i q)).card : ℝ) -
        (X : ℝ) * ((q.totient : ℝ) / q)| ≤ (2 : ℝ) ^ q.primeFactors.card := by
  have hcard : ((range X).filter (noPrimeDiv q.primeFactors)).card =
      ((Ico 1 (X + 1)).filter (fun i => Nat.Coprime i q)).card := by
    apply Finset.card_bij (fun a _ => a + 1)
    · intro a ha
      simp only [mem_filter, mem_range] at ha
      simp only [mem_filter, mem_Ico]
      exact ⟨⟨by omega, by omega⟩, (noPrimeDiv_primeFactors_iff q a hq).mp ha.2⟩
    · intro a _ b _ hab
      omega
    · intro b hb
      simp only [mem_filter, mem_Ico] at hb
      refine ⟨b - 1, ?_, by omega⟩
      simp only [mem_filter, mem_range]
      refine ⟨by omega, (noPrimeDiv_primeFactors_iff q (b - 1) hq).mpr ?_⟩
      simpa [Nat.sub_add_cancel hb.1.1] using hb.2
  rw [← hcard, ← prod_one_sub_inv_eq_totient_div q hq,
    ← legendre_identity q.primeFactors X, ← legendre_main_term q.primeFactors X,
    ← Finset.sum_sub_distrib]
  calc
    |∑ E ∈ q.primeFactors.powerset,
        ((-1 : ℝ) ^ E.card * (((range X).filter (allPrimeDiv E)).card : ℝ) -
          (-1 : ℝ) ^ E.card * ((X : ℝ) / (∏ p ∈ E, p : ℕ)))| ≤
        ∑ E ∈ q.primeFactors.powerset,
          |(-1 : ℝ) ^ E.card * (((range X).filter (allPrimeDiv E)).card : ℝ) -
            (-1 : ℝ) ^ E.card * ((X : ℝ) / (∏ p ∈ E, p : ℕ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _E ∈ q.primeFactors.powerset, (1 : ℝ) := by
      refine Finset.sum_le_sum fun E hE => ?_
      rw [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact abs_card_allPrimeDiv_sub_le_one q.primeFactors E
        (Finset.mem_powerset.mp hE) (fun p hp => Nat.prime_of_mem_primeFactors hp) X
    _ = (2 : ℝ) ^ q.primeFactors.card := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_powerset]
      push_cast
      rfl

theorem coprime_Ico_count_le (q X : ℕ) (hq : q ≠ 0) :
    (((Ico 1 X).filter (fun i => Nat.Coprime i q)).card : ℝ) ≤
      (X : ℝ) / q * q.totient + (2 : ℝ) ^ q.primeFactors.card := by
  have h := coprime_count_abs q (X - 1) hq
  have hI : Ico 1 (X - 1 + 1) = Ico 1 X := by
    by_cases hX : X = 0
    · simp [hX]
    · rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hX)]
  rw [hI] at h
  have hu : (((Ico 1 X).filter (fun i => Nat.Coprime i q)).card : ℝ) ≤
      ((X - 1 : ℕ) : ℝ) * ((q.totient : ℝ) / q) +
        (2 : ℝ) ^ q.primeFactors.card := by
    have hle := (le_abs_self
      ((((Ico 1 X).filter (fun i => Nat.Coprime i q)).card : ℝ) -
        ((X - 1 : ℕ) : ℝ) * ((q.totient : ℝ) / q))).trans h
    linarith
  have hX : (((X - 1 : ℕ) : ℝ)) ≤ X := by exact_mod_cast Nat.sub_le X 1
  have hnonneg : 0 ≤ (q.totient : ℝ) / q := by positivity
  calc
    _ ≤ ((X - 1 : ℕ) : ℝ) * ((q.totient : ℝ) / q) +
        (2 : ℝ) ^ q.primeFactors.card := hu
    _ ≤ (X : ℝ) / q * q.totient + (2 : ℝ) ^ q.primeFactors.card := by
      have hm := mul_le_mul_of_nonneg_right hX hnonneg
      calc
        ((X - 1 : ℕ) : ℝ) * ((q.totient : ℝ) / q) +
            (2 : ℝ) ^ q.primeFactors.card ≤
          (X : ℝ) * ((q.totient : ℝ) / q) +
            (2 : ℝ) ^ q.primeFactors.card := by gcongr
        _ = (X : ℝ) / q * q.totient + (2 : ℝ) ^ q.primeFactors.card := by ring

/-- Vandehey's Lemma 4.3, with an integral right endpoint. -/
theorem gcd_Ico_count_le (n d X : ℕ) (hn : n ≠ 0) (hdvd : d ∣ n) :
    (((Ico 1 X).filter (fun i => i.gcd n = d)).card : ℝ) ≤
      (X : ℝ) / n * (n / d).totient + (2 : ℝ) ^ (n / d).primeFactors.card := by
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn)
  let q := n / d
  let Y := (X - 1) / d
  have hq : q ≠ 0 := by
    dsimp [q]
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) hd).ne'
  have hcard : ((Ico 1 X).filter (fun i => i.gcd n = d)).card ≤
      ((Ico 1 (Y + 1)).filter (fun j => Nat.Coprime j q)).card := by
    apply Finset.card_le_card_of_injOn (fun i => i / d)
    · intro i hi
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ico] at hi ⊢
      have hdvi : d ∣ i := by rw [← hi.2]; exact Nat.gcd_dvd_left i n
      have hi0 : 0 < i := by omega
      have hlo : 1 ≤ i / d := Nat.div_pos (Nat.le_of_dvd hi0 hdvi) hd
      have hhi : i ≤ X - 1 := by omega
      have hupp : i / d ≤ Y := Nat.div_le_div_right hhi
      have hcop0 := Nat.coprime_div_gcd_div_gcd (m := i) (n := n) (by
        rw [hi.2]
        exact hd)
      have hcop : Nat.Coprime (i / d) q := by simpa [q, hi.2] using hcop0
      exact ⟨⟨hlo, by omega⟩, hcop⟩
    · intro i hi j hj hij
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ico] at hi hj
      have hdi : d ∣ i := by rw [← hi.2]; exact Nat.gcd_dvd_left i n
      have hdj : d ∣ j := by rw [← hj.2]; exact Nat.gcd_dvd_left j n
      dsimp at hij
      calc
        i = d * (i / d) := (Nat.mul_div_cancel' hdi).symm
        _ = d * (j / d) := by rw [hij]
        _ = j := Nat.mul_div_cancel' hdj
  have habs := coprime_count_abs q Y hq
  have hupper : (((Ico 1 (Y + 1)).filter (fun j => Nat.Coprime j q)).card : ℝ) ≤
      (Y : ℝ) * ((q.totient : ℝ) / q) + (2 : ℝ) ^ q.primeFactors.card := by
    have hh := (le_abs_self
      ((((Ico 1 (Y + 1)).filter (fun j => Nat.Coprime j q)).card : ℝ) -
        (Y : ℝ) * ((q.totient : ℝ) / q))).trans habs
    linarith
  have hnfac : d * q = n := by
    dsimp [q]
    exact Nat.mul_div_cancel' hdvd
  have hYmul : Y * d ≤ X := by
    dsimp [Y]
    exact (Nat.div_mul_le_self (X - 1) d).trans (Nat.sub_le X 1)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hnfacR : (d : ℝ) * q = n := by exact_mod_cast hnfac
  have hYmulR : (Y : ℝ) * d ≤ X := by exact_mod_cast hYmul
  have hmain : (Y : ℝ) * ((q.totient : ℝ) / q) ≤
      (X : ℝ) / n * (q.totient : ℝ) := by
    have hratio : (Y : ℝ) / q ≤ (X : ℝ) / n := by
      rw [← hnfacR]
      rw [div_le_div_iff₀ hqR (mul_pos hdR hqR)]
      nlinarith
    have htot : (0 : ℝ) ≤ q.totient := by positivity
    calc
      (Y : ℝ) * ((q.totient : ℝ) / q) = (Y : ℝ) / q * q.totient := by ring
      _ ≤ (X : ℝ) / n * q.totient := mul_le_mul_of_nonneg_right hratio htot
  calc
    (((Ico 1 X).filter (fun i => i.gcd n = d)).card : ℝ) ≤
        (((Ico 1 (Y + 1)).filter (fun j => Nat.Coprime j q)).card : ℝ) := by exact_mod_cast hcard
    _ ≤ (Y : ℝ) * ((q.totient : ℝ) / q) + (2 : ℝ) ^ q.primeFactors.card := hupper
    _ ≤ (X : ℝ) / n * q.totient + (2 : ℝ) ^ q.primeFactors.card := by gcongr

/-- Vandehey's Lemma 4.3 in the paper's stated `2^s` form. -/
theorem gcd_Ico_count_le_two_pow (n d X s : ℕ) (hn : n ≠ 0) (hdvd : d ∣ n)
    (hs : n.primeFactors.card ≤ s) :
    (((Ico 1 X).filter (fun i => i.gcd n = d)).card : ℝ) ≤
      (X : ℝ) / n * (n / d).totient + (2 : ℝ) ^ s := by
  refine (gcd_Ico_count_le n d X hn hdvd).trans ?_
  have hsub : (n / d).primeFactors ⊆ n.primeFactors := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ n / d := Nat.dvd_of_mem_primeFactors hp
    exact (Nat.mem_primeFactors_of_ne_zero hn).2
      ⟨hpprime, hpd.trans (Nat.div_dvd_of_dvd hdvd)⟩
  have hcard : (n / d).primeFactors.card ≤ s := (Finset.card_le_card hsub).trans hs
  gcongr
  norm_num

end NormalNumbers.VandeheyKorobov
