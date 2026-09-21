/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PrimeModelPrimeDimension
import NormalNumbers.PrimeModelRadicalCRT

/-!
# The quantitative lower arithmetic sieve count

Combining the Brun lower weights of `PrimeModelPrimeDimension` (whose three defining
properties are now unconditional) with the exact CRT counts of `PrimeModelRadicalCRT`
gives an honest **lower bound for the sifted count**

    #{n < X : SiftedCond h A U Q r j n}
      ≥ (1 - 2 exp (-s/2)) · X / (Q ∏_{p ∈ A} p) · ∏_{p ∈ U} (1 - h/p) - (y^s)^2 .

Two named results:

* `brun_remainder_le_square` — the remainder simplification.  For any weights `λ` bounded by
  `1` and supported on subsets of product at most `R ≥ 1`, and `U` a set of primes `p > h`,
  `∑_{E ⊆ U} |λ E| h^{#E} ≤ R^2`.  This is coarser than the sharp divisor-sum estimate
  `R (1 + log R)^{h-1}` but avoids all divisor machinery and is amply sufficient here: in the
  target regime `R = x^{1/4}` and the normalizing main term is `≫ x^{5/8}`.
* `brun_sifted_count_lower` — the arithmetic count itself.

## Route

1. *Pointwise minorant.*  For `n` satisfying the base conditions, the primes of `U` that hit
   one of the `h` shifts form `B n ⊆ U`, and `n` is sifted exactly when `B n = ∅`.  The Brun
   property `∑_{E ⊆ B} λ E ≤ [B = ∅]` therefore minorizes the sifted indicator.
2. *Interchange.*  Summing over `n < X` turns `∑_n ∑_{E ⊆ B n} λ E` into
   `∑_{E ⊆ U} λ E · #{n < X : SieveCond h A E Q r j n}`.
3. *CRT.*  `Radical.radical_sieve_count` replaces each count by `X h^{#E}/(Q D ∏ E)` with
   error `≤ h^{#E}`; the main terms factor as `X/(Q D) · ∑_E λ E ∏_{p ∈ E} (h/p)`, bounded
   below by `PrimeDensity.prime_density_brun_lower`, and the errors by
   `brun_remainder_le_square` with `R = y^s`.

No analytic hypothesis beyond those already discharged is introduced.
-/

set_option linter.unusedSectionVars false

open scoped BigOperators
open Finset

namespace NormalNumbers.PrimeModel.BrunCount

open NormalNumbers.PrimeModel

/-! ### The remainder simplification -/

/-- On subsets of a finite set of primes, `E ↦ ∏_{p ∈ E} p` is injective. -/
lemma prod_injOn_powerset {U : Finset ℕ} (hU : ∀ p ∈ U, Nat.Prime p) :
    Set.InjOn (fun E : Finset ℕ => ∏ p ∈ E, p) (U.powerset : Set (Finset ℕ)) := by
  intro E hE F hF hEF
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
    Finset.coe_subset] at hE hF
  have hEF' : ∏ p ∈ E, p = ∏ p ∈ F, p := hEF
  have key : ∀ (G : Finset ℕ), G ⊆ U → ∀ p ∈ U, (p ∣ ∏ q ∈ G, q ↔ p ∈ G) := by
    intro G hG p hp
    constructor
    · intro hdvd
      obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime (hU p hp)).exists_mem_finset_dvd hdvd
      have : p = q := ((Nat.prime_dvd_prime_iff_eq (hU p hp) (hU q (hG hq))).1 hpq)
      exact this ▸ hq
    · intro hmem; exact Finset.dvd_prod_of_mem _ hmem
  ext p
  constructor
  · intro hp
    have hpU := hE hp
    exact (key F hF p hpU).1 (hEF' ▸ Finset.dvd_prod_of_mem _ hp)
  · intro hp
    have hpU := hF hp
    exact (key E hE p hpU).1 (hEF'.symm ▸ Finset.dvd_prod_of_mem _ hp)

/-- **Remainder simplification.**  If every `p ∈ U` is a prime exceeding `h`, the weights `λ`
are bounded by `1` in absolute value and supported on subsets of product at most `R ≥ 1`, then

    `∑_{E ⊆ U} |λ E| · h^{#E} ≤ R^2`.

Each `h^{#E} ≤ ∏_{p ∈ E} p ≤ R`, and `E ↦ ∏_{p ∈ E} p` is injective into the positive
integers `≤ ⌊R⌋`, so at most `⌊R⌋ ≤ R` summands are nonzero. -/
theorem brun_remainder_le_square {h : ℕ} {U : Finset ℕ}
    (hU : ∀ p ∈ U, Nat.Prime p ∧ h < p) (lam : Finset ℕ → ℝ) {R : ℝ} (hR : 1 ≤ R)
    (hlam : ∀ E ⊆ U, |lam E| ≤ 1 ∧ (lam E ≠ 0 → ((∏ p ∈ E, p : ℕ) : ℝ) ≤ R)) :
    ∑ E ∈ U.powerset, |lam E| * (h : ℝ) ^ E.card ≤ R ^ 2 := by
  classical
  set S : Finset (Finset ℕ) := U.powerset.filter (fun E => lam E ≠ 0) with hS
  -- the sum is carried by `S`
  have hsum : ∑ E ∈ U.powerset, |lam E| * (h : ℝ) ^ E.card
      = ∑ E ∈ S, |lam E| * (h : ℝ) ^ E.card := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun E _ => ?_
    by_cases hE : lam E = 0
    · simp [hE]
    · rw [if_pos hE]
  -- each retained summand is at most `R`
  have hterm : ∀ E ∈ S, |lam E| * (h : ℝ) ^ E.card ≤ R := by
    intro E hES
    rw [hS, Finset.mem_filter, Finset.mem_powerset] at hES
    obtain ⟨hEU, hEne⟩ := hES
    obtain ⟨hb, hsupp⟩ := hlam E hEU
    have hpow : (h : ℝ) ^ E.card ≤ ((∏ p ∈ E, p : ℕ) : ℝ) := by
      have : (h : ℝ) ^ E.card = ∏ _p ∈ E, (h : ℝ) := by rw [Finset.prod_const]
      rw [this]
      push_cast
      refine Finset.prod_le_prod (fun p _ => by positivity) ?_
      intro p hp
      exact_mod_cast le_of_lt (hU p (hEU hp)).2
    have hpow0 : (0 : ℝ) ≤ (h : ℝ) ^ E.card := by positivity
    calc |lam E| * (h : ℝ) ^ E.card ≤ 1 * ((∏ p ∈ E, p : ℕ) : ℝ) :=
          mul_le_mul hb (le_trans hpow (le_refl _)) hpow0 zero_le_one
      _ = ((∏ p ∈ E, p : ℕ) : ℝ) := one_mul _
      _ ≤ R := hsupp hEne
  -- there are at most `⌊R⌋` retained subsets
  have hcard : (S.card : ℝ) ≤ R := by
    have hmaps : Set.MapsTo (fun E : Finset ℕ => ∏ p ∈ E, p) (S : Set (Finset ℕ))
        (Finset.Icc 1 ⌊R⌋₊ : Set ℕ) := by
      intro E hE
      have hE' : E ∈ S := hE
      rw [hS, Finset.mem_filter, Finset.mem_powerset] at hE'
      obtain ⟨hEU, hEne⟩ := hE'
      obtain ⟨-, hsupp⟩ := hlam E hEU
      have hpos : 0 < ∏ p ∈ E, p :=
        Finset.prod_pos fun p hp => (hU p (hEU hp)).1.pos
      simp only [Finset.coe_Icc, Set.mem_Icc]
      refine ⟨hpos, ?_⟩
      exact Nat.le_floor (hsupp hEne)
    have hinj : Set.InjOn (fun E : Finset ℕ => ∏ p ∈ E, p) (S : Set (Finset ℕ)) := by
      refine Set.InjOn.mono ?_ (prod_injOn_powerset (fun p hp => (hU p hp).1))
      intro E hE
      have hE' : E ∈ S := hE
      rw [hS, Finset.mem_filter] at hE'
      exact hE'.1
    have := Finset.card_le_card_of_injOn (fun E : Finset ℕ => ∏ p ∈ E, p) hmaps hinj
    have hIcc : (Finset.Icc 1 ⌊R⌋₊).card = ⌊R⌋₊ := by
      rw [Nat.card_Icc]; omega
    rw [hIcc] at this
    calc (S.card : ℝ) ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast this
      _ ≤ R := Nat.floor_le (by linarith)
  calc ∑ E ∈ U.powerset, |lam E| * (h : ℝ) ^ E.card
      = ∑ E ∈ S, |lam E| * (h : ℝ) ^ E.card := hsum
    _ ≤ ∑ _E ∈ S, R := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * R := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ R * R := by
        refine mul_le_mul_of_nonneg_right hcard (by linarith)
    _ = R ^ 2 := by ring

end NormalNumbers.PrimeModel.BrunCount
