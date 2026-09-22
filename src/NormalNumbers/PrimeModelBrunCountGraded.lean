import NormalNumbers.PrimeModelBrunCount
import NormalNumbers.PrimeModelRadicalCRTGraded

/-!
# The graded lower arithmetic sieve count

Lap 4b of `KICKOFF-2026-09-22-multicutoff-lean.md`.  This is the graded analogue of
`PrimeModelBrunCount.brun_sifted_count_lower`: the number of admissible shifts is `d p` at the
prime `p` rather than a uniform `h`, and the sieve weights `λ` are left **abstract** — the
arithmetic does not need to know that they come from a Bonferroni construction, only that they
minorize (`∑_{E ⊆ B} λ E ≤ [B = ∅]`), are bounded by `1`, and are supported on subsets of
product at most `R`.  `PrimeModelBlockSieve` supplies exactly those three properties.

## Main results

* `weighted_counts_le_sifted_graded` — the pointwise minorant, summed.
* `brun_remainder_le_square_graded` — `∑_{E ⊆ U} |λ E| ∏_{p ∈ E} d p ≤ R²`.
* `graded_sifted_count_lower` —
  `#{n < X : SiftedCondD} ≥ X/(Q ∏_A p) · ∑_{E ⊆ U} λ E ∏_{p∈E} (d p/p) − R²`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.BrunGraded

open NormalNumbers.PrimeModel.Radical NormalNumbers.PrimeModel.RadicalGraded
open NormalNumbers.PrimeModel.BrunCount

/-- The sifted condition: residue `r` mod `Q`, the prescribed shift at each assigned prime of
`A`, and **no** prime `p ∈ U` dividing any of the `d p` shifted values. -/
def SiftedCondD (A U : Finset ℕ) (d j : ℕ → ℕ) (Q r : ℕ) (n : ℕ) : Prop :=
  n % Q = r ∧ (∀ p ∈ A, p ∣ n + j p + 1) ∧ (∀ p ∈ U, ∀ t, t < d p → ¬ p ∣ n + t + 1)

instance (A U : Finset ℕ) (d j : ℕ → ℕ) (Q r : ℕ) :
    DecidablePred (SiftedCondD A U d j Q r) := fun n => by
  unfold SiftedCondD; infer_instance

/-- The primes of `U` that divide one of their `d p` shifted values at `n`. -/
def hitUD (U : Finset ℕ) (d : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  U.filter fun p => ∃ t, t < d p ∧ p ∣ n + t + 1

lemma hitUD_subset (U : Finset ℕ) (d : ℕ → ℕ) (n : ℕ) : hitUD U d n ⊆ U :=
  Finset.filter_subset _ _

lemma sieveCondD_iff_sub (A E U : Finset ℕ) (d j : ℕ → ℕ) (Q r : ℕ) (n : ℕ) (hE : E ⊆ U) :
    SieveCondD A E d j Q r n ↔
      ((n % Q = r ∧ ∀ p ∈ A, p ∣ n + j p + 1) ∧ E ⊆ hitUD U d n) := by
  unfold SieveCondD hitUD
  simp only [Finset.subset_iff, Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, fun p hp => ⟨hE hp, h3 p hp⟩⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, fun p hp => (h3 hp).2⟩

lemma siftedCondD_iff_hit_empty (A U : Finset ℕ) (d j : ℕ → ℕ) (Q r : ℕ) (n : ℕ) :
    SiftedCondD A U d j Q r n ↔
      ((n % Q = r ∧ ∀ p ∈ A, p ∣ n + j p + 1) ∧ hitUD U d n = ∅) := by
  unfold SiftedCondD hitUD
  rw [Finset.filter_eq_empty_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, fun p hp ⟨t, htd, ht⟩ => h3 p hp t htd ht⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, fun p hp t htd ht => h3 hp ⟨t, htd, ht⟩⟩

/-- **The graded minorant, summed.** -/
theorem weighted_counts_le_sifted_graded (lam : Finset ℕ → ℝ) (A U : Finset ℕ) (d j : ℕ → ℕ)
    (Q r X : ℕ) (hminor : ∀ B ⊆ U, ∑ E ∈ B.powerset, lam E ≤ if B = ∅ then 1 else 0) :
    ∑ E ∈ U.powerset, lam E * (((range X).filter (SieveCondD A E d j Q r)).card : ℝ)
      ≤ (((range X).filter (SiftedCondD A U d j Q r)).card : ℝ) := by
  classical
  have hind : ∀ (Φ : ℕ → Prop) (_ : DecidablePred Φ),
      (((range X).filter Φ).card : ℝ) = ∑ n ∈ range X, if Φ n then (1 : ℝ) else 0 := by
    intro Φ _
    rw [Finset.sum_boole]
  rw [hind (SiftedCondD A U d j Q r) inferInstance]
  have hL : ∑ E ∈ U.powerset, lam E * (((range X).filter (SieveCondD A E d j Q r)).card : ℝ)
      = ∑ n ∈ range X, ∑ E ∈ U.powerset,
          lam E * (if SieveCondD A E d j Q r n then (1 : ℝ) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun E _ => ?_
    rw [hind (SieveCondD A E d j Q r) inferInstance, Finset.mul_sum]
  rw [hL]
  refine Finset.sum_le_sum fun n _ => ?_
  by_cases hbase : n % Q = r ∧ ∀ p ∈ A, p ∣ n + j p + 1
  · have h1 : ∀ E ∈ U.powerset,
        lam E * (if SieveCondD A E d j Q r n then (1 : ℝ) else 0)
        = if E ⊆ hitUD U d n then lam E else 0 := by
      intro E hEp
      have hE : E ⊆ U := Finset.mem_powerset.1 hEp
      by_cases hsub : E ⊆ hitUD U d n
      · rw [if_pos hsub, if_pos ((sieveCondD_iff_sub A E U d j Q r n hE).2 ⟨hbase, hsub⟩),
          mul_one]
      · rw [if_neg hsub, if_neg (fun hc =>
          hsub ((sieveCondD_iff_sub A E U d j Q r n hE).1 hc).2), mul_zero]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
    have h2 : U.powerset.filter (fun E => E ⊆ hitUD U d n) = (hitUD U d n).powerset := by
      ext E
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨fun hx => hx.2, fun hx => ⟨hx.trans (hitUD_subset U d n), hx⟩⟩
    rw [h2]
    refine le_trans (hminor _ (hitUD_subset U d n)) ?_
    by_cases hemp : hitUD U d n = ∅
    · rw [if_pos hemp, if_pos ((siftedCondD_iff_hit_empty A U d j Q r n).2 ⟨hbase, hemp⟩)]
    · rw [if_neg hemp]
      split <;> norm_num
  · have hz : ∀ E ∈ U.powerset,
        lam E * (if SieveCondD A E d j Q r n then (1 : ℝ) else 0) = 0 := by
      intro E _
      rw [if_neg (fun hc => hbase ⟨hc.1, hc.2.1⟩), mul_zero]
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero,
      if_neg (fun hc => hbase ⟨hc.1, hc.2.1⟩)]

/-- **Graded remainder simplification**: `∑_{E ⊆ U} |λ E| ∏_{p ∈ E} d p ≤ R²`.
Each `∏_{p ∈ E} d p ≤ ∏_{p ∈ E} p ≤ R` (using `d p ≤ p`), and `E ↦ ∏_{p ∈ E} p` is injective
into `[1, ⌊R⌋]`, so at most `R` summands are nonzero. -/
theorem brun_remainder_le_square_graded {U : Finset ℕ} {d : ℕ → ℕ}
    (hU : ∀ p ∈ U, Nat.Prime p ∧ d p ≤ p) (lam : Finset ℕ → ℝ) {R : ℝ} (hR : 1 ≤ R)
    (hlam : ∀ E ⊆ U, |lam E| ≤ 1 ∧ (lam E ≠ 0 → ((∏ p ∈ E, p : ℕ) : ℝ) ≤ R)) :
    ∑ E ∈ U.powerset, |lam E| * ((∏ p ∈ E, d p : ℕ) : ℝ) ≤ R ^ 2 := by
  classical
  set S : Finset (Finset ℕ) := U.powerset.filter (fun E => lam E ≠ 0) with hS
  have hsum : ∑ E ∈ U.powerset, |lam E| * ((∏ p ∈ E, d p : ℕ) : ℝ)
      = ∑ E ∈ S, |lam E| * ((∏ p ∈ E, d p : ℕ) : ℝ) := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun E _ => ?_
    by_cases hE : lam E = 0
    · simp [hE]
    · rw [if_pos hE]
  have hterm : ∀ E ∈ S, |lam E| * ((∏ p ∈ E, d p : ℕ) : ℝ) ≤ R := by
    intro E hES
    rw [hS, Finset.mem_filter, Finset.mem_powerset] at hES
    obtain ⟨hEU, hEne⟩ := hES
    obtain ⟨hb, hsupp⟩ := hlam E hEU
    have hdle : ((∏ p ∈ E, d p : ℕ) : ℝ) ≤ ((∏ p ∈ E, p : ℕ) : ℝ) := by
      have : (∏ p ∈ E, d p) ≤ ∏ p ∈ E, p :=
        Finset.prod_le_prod' fun p hp => (hU p (hEU hp)).2
      exact_mod_cast this
    have hnn : (0:ℝ) ≤ ((∏ p ∈ E, d p : ℕ) : ℝ) := by positivity
    calc |lam E| * ((∏ p ∈ E, d p : ℕ) : ℝ) ≤ 1 * ((∏ p ∈ E, p : ℕ) : ℝ) :=
          mul_le_mul hb hdle hnn zero_le_one
      _ = ((∏ p ∈ E, p : ℕ) : ℝ) := one_mul _
      _ ≤ R := hsupp hEne
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
      exact ⟨hpos, Nat.le_floor (hsupp hEne)⟩
    have hinj : Set.InjOn (fun E : Finset ℕ => ∏ p ∈ E, p) (S : Set (Finset ℕ)) := by
      refine Set.InjOn.mono ?_ (prod_injOn_powerset (fun p hp => (hU p hp).1))
      intro E hE
      have hE' : E ∈ S := hE
      rw [hS, Finset.mem_filter] at hE'
      exact hE'.1
    have hle := Finset.card_le_card_of_injOn (fun E : Finset ℕ => ∏ p ∈ E, p) hmaps hinj
    have hIcc : (Finset.Icc 1 ⌊R⌋₊).card = ⌊R⌋₊ := by rw [Nat.card_Icc]; omega
    rw [hIcc] at hle
    calc (S.card : ℝ) ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast hle
      _ ≤ R := Nat.floor_le (by linarith)
  calc ∑ E ∈ U.powerset, |lam E| * ((∏ p ∈ E, d p : ℕ) : ℝ)
      = ∑ E ∈ S, |lam E| * ((∏ p ∈ E, d p : ℕ) : ℝ) := hsum
    _ ≤ ∑ _E ∈ S, R := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * R := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ R * R := mul_le_mul_of_nonneg_right hcard (by linarith)
    _ = R ^ 2 := by ring

/-- The per-subset main term factors as `X/(Q D) · ∏_{p ∈ E} (d p / p)`. -/
lemma main_term_factor_graded (A E : Finset ℕ) (d : ℕ → ℕ) (Q X : ℕ) :
    (X : ℝ) * ((∏ p ∈ E, d p : ℕ) : ℝ)
        / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ) * ((∏ p ∈ E, p : ℕ) : ℝ))
      = (X : ℝ) / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ)) * ∏ p ∈ E, (d p : ℝ) / (p : ℝ) := by
  have hprod : ∏ p ∈ E, (d p : ℝ) / (p : ℝ)
      = ((∏ p ∈ E, d p : ℕ) : ℝ) / ((∏ p ∈ E, p : ℕ) : ℝ) := by
    rw [Finset.prod_div_distrib]
    push_cast
    ring
  rw [hprod, div_mul_div_comm, mul_div_assoc]

/-- **The graded lower arithmetic sieve count.**  With abstract weights `λ` that minorize, are
bounded by `1` and are supported on subsets of product at most `R ≥ 1`:

    #{n < X : SiftedCondD A U d j Q r}
      ≥ X/(Q ∏_{p∈A} p) · ∑_{E ⊆ U} λ E ∏_{p∈E} (d p / p) − R² . -/
theorem graded_sifted_count_lower (lam : Finset ℕ → ℝ) (A U : Finset ℕ) (d j : ℕ → ℕ)
    (Q r X : ℕ) {R : ℝ} (hR : 1 ≤ R)
    (hA : ∀ p ∈ A, Nat.Prime p) (hAj : ∀ p ∈ A, j p < p)
    (hU : ∀ p ∈ U, Nat.Prime p ∧ d p ≤ p)
    (hAU : Disjoint A U) (hQ : 0 < Q) (hr : r < Q)
    (hQcop : ∀ p ∈ A ∪ U, Nat.Coprime Q p)
    (hminor : ∀ B ⊆ U, ∑ E ∈ B.powerset, lam E ≤ if B = ∅ then 1 else 0)
    (hlam : ∀ E ⊆ U, |lam E| ≤ 1 ∧ (lam E ≠ 0 → ((∏ p ∈ E, p : ℕ) : ℝ) ≤ R)) :
    (X : ℝ) / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ))
        * (∑ E ∈ U.powerset, lam E * ∏ p ∈ E, (d p : ℝ) / (p : ℝ)) - R ^ 2
      ≤ (((range X).filter (SiftedCondD A U d j Q r)).card : ℝ) := by
  classical
  refine le_trans ?_ (weighted_counts_le_sifted_graded lam A U d j Q r X hminor)
  -- replace each count by its main term, paying the CRT error
  have hEvery : ∀ E ∈ U.powerset,
      lam E * ((X : ℝ) / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ)) * ∏ p ∈ E, (d p : ℝ) / (p : ℝ))
        - |lam E| * ((∏ p ∈ E, d p : ℕ) : ℝ)
      ≤ lam E * (((range X).filter (SieveCondD A E d j Q r)).card : ℝ) := by
    intro E hEp
    have hEU : E ⊆ U := Finset.mem_powerset.1 hEp
    have hcount := radical_sieve_count_graded A E d j Q r
      hA hAj (fun p hp => (hU p (hEU hp)).1) (fun p hp => (hU p (hEU hp)).2)
      (Finset.disjoint_of_subset_right hEU hAU) hQ hr
      (fun p hp => hQcop p (by
        rcases Finset.mem_union.1 hp with h | h
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ (hEU h))) X
    rw [main_term_factor_graded A E d Q X] at hcount
    set T : ℝ := (X : ℝ) / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ)) * ∏ p ∈ E, (d p : ℝ) / (p : ℝ)
      with hT
    set C : ℝ := (((range X).filter (SieveCondD A E d j Q r)).card : ℝ) with hC
    set D : ℝ := ((∏ p ∈ E, d p : ℕ) : ℝ) with hD
    have habs : |C - T| ≤ D := by rw [abs_sub_comm] at hcount ⊢; exact hcount
    have h1 : T - C ≤ D := by
      have := abs_le.1 habs
      linarith [this.1, this.2]
    have h2 : lam E * T - lam E * C ≤ |lam E| * D := by
      rcases le_or_gt 0 (lam E) with hpos | hneg
      · rw [abs_of_nonneg hpos, ← mul_sub]
        exact mul_le_mul_of_nonneg_left h1 hpos
      · rw [abs_of_neg hneg, ← mul_sub]
        have h3 : C - T ≤ D := by
          have := abs_le.1 habs
          linarith [this.1, this.2]
        have := mul_le_mul_of_nonneg_left h3 (le_of_lt (neg_pos.2 hneg))
        nlinarith [this]
    linarith
  have hsum := Finset.sum_le_sum hEvery
  rw [Finset.sum_sub_distrib] at hsum
  have hrem := brun_remainder_le_square_graded hU lam hR hlam
  have hmain : ∑ E ∈ U.powerset,
      lam E * ((X : ℝ) / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ)) * ∏ p ∈ E, (d p : ℝ) / (p : ℝ))
      = (X : ℝ) / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ))
        * (∑ E ∈ U.powerset, lam E * ∏ p ∈ E, (d p : ℝ) / (p : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun E _ => by ring
  rw [hmain] at hsum
  linarith

end NormalNumbers.PrimeModel.BrunGraded
