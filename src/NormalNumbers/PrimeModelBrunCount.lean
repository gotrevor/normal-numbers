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

/-! ### The pointwise minorant and the counting transfer -/

open NormalNumbers.PrimeModel.Radical

/-- The primes of `U` that divide one of the `h` shifted values at `n`. -/
def hitU (h : ℕ) (U : Finset ℕ) (n : ℕ) : Finset ℕ :=
  U.filter fun p => ∃ t : Fin h, p ∣ n + t.val + 1

lemma hitU_subset (h : ℕ) (U : Finset ℕ) (n : ℕ) : hitU h U n ⊆ U := Finset.filter_subset _ _

lemma sieveCond_iff_sub {h : ℕ} (A E U : Finset ℕ) (Q r : ℕ) (j : ℕ → Fin h) (n : ℕ)
    (hE : E ⊆ U) :
    SieveCond h A E Q r j n ↔
      ((n % Q = r ∧ ∀ p ∈ A, p ∣ n + (j p).val + 1) ∧ E ⊆ hitU h U n) := by
  unfold SieveCond hitU
  simp only [Finset.subset_iff, Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, fun p hp => ⟨hE hp, h3 p hp⟩⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, fun p hp => (h3 hp).2⟩

lemma siftedCond_iff_hit_empty {h : ℕ} (A U : Finset ℕ) (Q r : ℕ) (j : ℕ → Fin h) (n : ℕ) :
    SiftedCond h A U Q r j n ↔
      ((n % Q = r ∧ ∀ p ∈ A, p ∣ n + (j p).val + 1) ∧ hitU h U n = ∅) := by
  unfold SiftedCond hitU
  rw [Finset.filter_eq_empty_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, fun p hp ⟨t, ht⟩ => h3 p hp t ht⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, fun p hp t ht => h3 hp ⟨t, ht⟩⟩

/-- **The Brun minorant, summed.**  If the weights satisfy the Bonferroni-type lower
property `∑_{E ⊆ B} λ E ≤ [B = ∅]` for every `B ⊆ U`, then the weighted combination of the
one-sided counts is a lower bound for the sifted count. -/
theorem weighted_counts_le_sifted {h : ℕ} (lam : Finset ℕ → ℝ) (A U : Finset ℕ) (Q r : ℕ)
    (j : ℕ → Fin h) (X : ℕ)
    (hminor : ∀ B ⊆ U, ∑ E ∈ B.powerset, lam E ≤ if B = ∅ then 1 else 0) :
    ∑ E ∈ U.powerset, lam E * (((range X).filter (SieveCond h A E Q r j)).card : ℝ)
      ≤ (((range X).filter (SiftedCond h A U Q r j)).card : ℝ) := by
  classical
  have hind : ∀ (Φ : ℕ → Prop) (_ : DecidablePred Φ),
      (((range X).filter Φ).card : ℝ) = ∑ n ∈ range X, if Φ n then (1 : ℝ) else 0 := by
    intro Φ _
    rw [Finset.sum_boole]
  rw [hind (SiftedCond h A U Q r j) inferInstance]
  have hL : ∑ E ∈ U.powerset, lam E * (((range X).filter (SieveCond h A E Q r j)).card : ℝ)
      = ∑ n ∈ range X, ∑ E ∈ U.powerset,
          lam E * (if SieveCond h A E Q r j n then (1 : ℝ) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun E _ => ?_
    rw [hind (SieveCond h A E Q r j) inferInstance, Finset.mul_sum]
  rw [hL]
  refine Finset.sum_le_sum fun n _ => ?_
  by_cases hbase : n % Q = r ∧ ∀ p ∈ A, p ∣ n + (j p).val + 1
  · have h1 : ∀ E ∈ U.powerset,
        lam E * (if SieveCond h A E Q r j n then (1 : ℝ) else 0)
        = if E ⊆ hitU h U n then lam E else 0 := by
      intro E hEp
      have hE : E ⊆ U := Finset.mem_powerset.1 hEp
      by_cases hsub : E ⊆ hitU h U n
      · rw [if_pos hsub, if_pos ((sieveCond_iff_sub A E U Q r j n hE).2 ⟨hbase, hsub⟩), mul_one]
      · rw [if_neg hsub, if_neg (fun hc =>
          hsub ((sieveCond_iff_sub A E U Q r j n hE).1 hc).2), mul_zero]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
    have h2 : U.powerset.filter (fun E => E ⊆ hitU h U n) = (hitU h U n).powerset := by
      ext E
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨fun hx => hx.2, fun hx => ⟨hx.trans (hitU_subset h U n), hx⟩⟩
    rw [h2]
    refine le_trans (hminor _ (hitU_subset h U n)) ?_
    by_cases hemp : hitU h U n = ∅
    · rw [if_pos hemp, if_pos ((siftedCond_iff_hit_empty A U Q r j n).2 ⟨hbase, hemp⟩)]
    · rw [if_neg hemp]
      split <;> norm_num
  · have hz : ∀ E ∈ U.powerset,
        lam E * (if SieveCond h A E Q r j n then (1 : ℝ) else 0) = 0 := by
      intro E _
      rw [if_neg (fun hc => hbase ⟨hc.1, hc.2.1⟩), mul_zero]
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero,
      if_neg (fun hc => hbase ⟨hc.1, hc.2.1⟩)]

/-- The per-subset main term factors as `X/(Q D) · ∏_{p ∈ E} (h/p)`. -/
lemma main_term_factor (h : ℕ) (A E : Finset ℕ) (Q X : ℕ) :
    (X : ℝ) * ((h ^ E.card : ℕ) : ℝ)
        / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ) * ((∏ p ∈ E, p : ℕ) : ℝ))
      = (X : ℝ) / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ)) * ∏ p ∈ E, (h : ℝ) / (p : ℝ) := by
  have hprod : ∏ p ∈ E, (h : ℝ) / (p : ℝ)
      = ((h ^ E.card : ℕ) : ℝ) / ((∏ p ∈ E, p : ℕ) : ℝ) := by
    rw [Finset.prod_div_distrib, Finset.prod_const]
    push_cast
    ring
  rw [hprod, div_mul_div_comm, mul_div_assoc]

/-! ### The arithmetic count -/

/-- **The quantitative lower arithmetic sieve count.**

For `h ≥ 1`, disjoint finite sets `A` (assigned primes) and `U` (sieve primes) of primes
exceeding `h`, with `U` bounded by `y ≥ exp 2`, `Q > 0` coprime to every prime of `A ∪ U`,
`r < Q`, any shift assignment `j`, any `X`, and `s` large enough
(`s ≥ 1920 h` and `s ≥ 40 log (4^h exp (16h)) + 4`):

    #{n < X : SiftedCond h A U Q r j n}
      ≥ (1 - 2 exp (-s/2)) · X / (Q ∏_{p ∈ A} p) · ∏_{p ∈ U} (1 - h/p) - (y^s)^2 .

No sieve-weight, dimension, counting-error or root-cardinality hypothesis remains: the Brun
weights come from `PrimeDensity.prime_density_brun_lower`, the counts from
`Radical.radical_sieve_count`, and the remainder from `brun_remainder_le_square`. -/
theorem brun_sifted_count_lower {h y : ℕ} (hh : 1 ≤ h) {s : ℝ}
    (hy : Real.exp 2 ≤ (y : ℝ)) (hs80 : 1920 * (h : ℝ) ≤ s)
    (hsA : 40 * Real.log ((4 : ℝ) ^ h * Real.exp (16 * h)) + 4 ≤ s)
    (A U : Finset ℕ) (Q r : ℕ) (j : ℕ → Fin h) (X : ℕ)
    (hA : ∀ p ∈ A, Nat.Prime p ∧ h < p) (hU : ∀ p ∈ U, Nat.Prime p ∧ h < p ∧ p ≤ y)
    (hAU : Disjoint A U) (hQ : 0 < Q) (hr : r < Q)
    (hQcop : ∀ p ∈ A ∪ U, Nat.Coprime Q p) :
    (1 - 2 * Real.exp (-s / 2)) * ((X : ℝ) / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ)))
          * ∏ p ∈ U, (1 - (h : ℝ) / (p : ℝ)) - ((y : ℝ) ^ s) ^ 2
      ≤ (((range X).filter (SiftedCond h A U Q r j)).card : ℝ) := by
  classical
  set lam : Finset ℕ → ℝ := Brun.lam (Brun.brunCut (24 * h) s y) with hlamdef
  have hs80' : 80 * ((24 * h : ℕ) : ℝ) ≤ s := by push_cast; linarith
  obtain ⟨hsupp, hminor, hmain⟩ :=
    PrimeDensity.prime_density_brun_lower hh hy hs80' hsA hU
  -- `R = y ^ s ≥ 1`
  have hy1 : (1 : ℝ) ≤ (y : ℝ) := le_trans (by nlinarith [Real.add_one_le_exp (2 : ℝ)]) hy
  have hs0 : (0 : ℝ) ≤ s := le_trans (by positivity) hs80
  have hR : (1 : ℝ) ≤ (y : ℝ) ^ s := Real.one_le_rpow hy1 hs0
  -- Step 1: the minorant
  have hstep1 : ∑ E ∈ U.powerset, lam E * (((range X).filter (SieveCond h A E Q r j)).card : ℝ)
      ≤ (((range X).filter (SiftedCond h A U Q r j)).card : ℝ) :=
    weighted_counts_le_sifted lam A U Q r j X hminor
  -- Step 2: replace the counts by their main terms
  have hDpos : (0 : ℝ) ≤ (X : ℝ) / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ)) := by positivity
  have hstep2 : ∀ E ∈ U.powerset,
      lam E * ((X : ℝ) / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ)) * ∏ p ∈ E, (h : ℝ) / (p : ℝ))
        - |lam E| * (h : ℝ) ^ E.card
      ≤ lam E * (((range X).filter (SieveCond h A E Q r j)).card : ℝ) := by
    intro E hEp
    have hE : E ⊆ U := Finset.mem_powerset.1 hEp
    have hbound := radical_sieve_count hh A E Q r j
      (fun p hp => (hA p hp).1) (fun p hp => (hA p hp).2)
      (fun p hp => (hU p (hE hp)).1) (fun p hp => (hU p (hE hp)).2.1)
      (hAU.mono_right hE) hQ hr
      (fun p hp => hQcop p (by
        rcases Finset.mem_union.1 hp with hx | hx
        · exact Finset.mem_union_left _ hx
        · exact Finset.mem_union_right _ (hE hx))) X
    set c : ℝ := (((range X).filter (SieveCond h A E Q r j)).card : ℝ) with hc
    set m : ℝ := (X : ℝ) * ((h ^ E.card : ℕ) : ℝ)
        / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ) * ((∏ p ∈ E, p : ℕ) : ℝ)) with hm
    have habs : |c - m| ≤ ((h ^ E.card : ℕ) : ℝ) := hbound
    have hmf := main_term_factor h A E Q X
    rw [← hmf, ← hm]
    have h1 : |lam E * (m - c)| ≤ |lam E| * (h : ℝ) ^ E.card := by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [abs_sub_comm] at habs
      calc |m - c| ≤ ((h ^ E.card : ℕ) : ℝ) := habs
        _ = (h : ℝ) ^ E.card := by push_cast; ring
    have h2 : lam E * m - lam E * c ≤ |lam E| * (h : ℝ) ^ E.card := by
      calc lam E * m - lam E * c = lam E * (m - c) := by ring
        _ ≤ |lam E * (m - c)| := le_abs_self _
        _ ≤ |lam E| * (h : ℝ) ^ E.card := h1
    linarith
  have hstep2' :
      (∑ E ∈ U.powerset, lam E * ((X : ℝ) / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ))
          * ∏ p ∈ E, (h : ℝ) / (p : ℝ)))
        - ∑ E ∈ U.powerset, |lam E| * (h : ℝ) ^ E.card
      ≤ ∑ E ∈ U.powerset, lam E * (((range X).filter (SieveCond h A E Q r j)).card : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum hstep2
  -- Step 3: the main term from the Brun lower weight property
  have hmainsum : (1 - 2 * Real.exp (-s / 2))
        * ((X : ℝ) / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ)))
        * ∏ p ∈ U, (1 - (h : ℝ) / (p : ℝ))
      ≤ ∑ E ∈ U.powerset, lam E * ((X : ℝ) / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ))
          * ∏ p ∈ E, (h : ℝ) / (p : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hmain hDpos
    calc (1 - 2 * Real.exp (-s / 2))
          * ((X : ℝ) / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ)))
          * ∏ p ∈ U, (1 - (h : ℝ) / (p : ℝ))
        = (X : ℝ) / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ))
            * ((1 - 2 * Real.exp (-s / 2)) * ∏ p ∈ U, (1 - (h : ℝ) / (p : ℝ))) := by ring
      _ ≤ (X : ℝ) / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ))
            * ∑ E ∈ U.powerset, lam E * ∏ p ∈ E, (h : ℝ) / (p : ℝ) := this
      _ = ∑ E ∈ U.powerset, lam E * ((X : ℝ) / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ))
            * ∏ p ∈ E, (h : ℝ) / (p : ℝ)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun E _ => by ring
  -- Step 4: the remainder
  have hrem : ∑ E ∈ U.powerset, |lam E| * (h : ℝ) ^ E.card ≤ ((y : ℝ) ^ s) ^ 2 :=
    brun_remainder_le_square (fun p hp => ⟨(hU p hp).1, (hU p hp).2.1⟩) lam hR
      (fun E hE => hsupp E hE)
  linarith

end NormalNumbers.PrimeModel.BrunCount

#print axioms NormalNumbers.PrimeModel.BrunCount.brun_remainder_le_square
#print axioms NormalNumbers.PrimeModel.BrunCount.brun_sifted_count_lower
