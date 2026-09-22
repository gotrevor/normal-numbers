import NormalNumbers.PrimeModelRadicalCRT

/-!
# Graded CRT counting: per-prime class counts

Lap 4 of `KICKOFF-2026-09-22-multicutoff-lean.md`; spec `papers/ROUND2-multicutoff-astra.md` §4
and `papers/ROUND2-multicutoff-fable.md` §3.

`PrimeModelRadicalCRT` counts with a *uniform* number `k` of admissible shifts at every sieve
prime.  The multicutoff sieve needs a **graded** count: the prime `p` lying in the band
`(y_{j+1}, y_j]` admits `d p = d_j` classes, and the admissible class count over a set `E` of
sieve primes is `∏_{p ∈ E} d p`, not `k^{#E}`.

The CRT infrastructure of `PrimeModelRadicalCRT` (`card_filter_shift`, `card_filter_range_prod`,
`abs_card_filter_periodic_sub_le`) is uniform in the local counts and is reused verbatim; only
the local condition and the product of local counts change.  Assigned primes now carry a plain
shift `j p < p` rather than an element of `Fin k`, which is both simpler and more general.

## Main results

* `radical_sieve_admissible_card_graded` — the admissible classes mod `Q D e` number exactly
  `∏_{p ∈ E} d p`.
* `radical_sieve_count_graded` — `|count − X ∏ d / (Q D e)| ≤ ∏_{p ∈ E} d p`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.RadicalGraded

open NormalNumbers.PrimeModel.Radical

/-- Residue condition mod `Q`, prescribed shift `j p` at each assigned prime `p ∈ A`, and
*some* shift `< d p` at each sieve prime `p ∈ E`. -/
def SieveCondD (A E : Finset ℕ) (d j : ℕ → ℕ) (Q r : ℕ) (n : ℕ) : Prop :=
  n % Q = r ∧ (∀ p ∈ A, p ∣ n + j p + 1) ∧ (∀ p ∈ E, ∃ t, t < d p ∧ p ∣ n + t + 1)

instance (A E : Finset ℕ) (d j : ℕ → ℕ) (Q r : ℕ) :
    DecidablePred (SieveCondD A E d j Q r) := fun n => by
  unfold SieveCondD; infer_instance

/-- The local modulus family: `Q` at the index `0`, and `p` itself at each prime `p ∈ A ∪ E`. -/
private def locMod (Q : ℕ) : ℕ → ℕ := fun i => if i = 0 then Q else i

/-- The local condition at each index. -/
private def locCondD (A : Finset ℕ) (d j : ℕ → ℕ) (r : ℕ) : ℕ → ℕ → Prop :=
  fun i c => if i = 0 then c = r else if i ∈ A then i ∣ c + j i + 1
    else ∃ t, t < d i ∧ i ∣ c + t + 1

private instance (A : Finset ℕ) (d j : ℕ → ℕ) (r : ℕ) (i : ℕ) :
    DecidablePred (locCondD A d j r i) := fun c => by
  unfold locCondD; infer_instance

private lemma zero_notMem (A E : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (hE : ∀ p ∈ E, p.Prime) :
    0 ∉ A ∪ E := by
  simp only [Finset.mem_union, not_or]
  exact ⟨fun h => Nat.not_prime_zero (hA 0 h), fun h => Nat.not_prime_zero (hE 0 h)⟩

private lemma prime_of_mem_union {A E : Finset ℕ} (hA : ∀ p ∈ A, p.Prime)
    (hE : ∀ p ∈ E, p.Prime) {p : ℕ} (hp : p ∈ A ∪ E) : p.Prime := by
  rcases Finset.mem_union.1 hp with h | h
  · exact hA p h
  · exact hE p h

private lemma sieveCondD_iff (A E : Finset ℕ) (d j : ℕ → ℕ) (Q r : ℕ)
    (hA : ∀ p ∈ A, p.Prime) (hE : ∀ p ∈ E, p.Prime) (hAE : Disjoint A E) (n : ℕ) :
    SieveCondD A E d j Q r n ↔
      ∀ i ∈ insert 0 (A ∪ E), locCondD A d j r i (n % locMod Q i) := by
  constructor
  · rintro ⟨h1, h2, h3⟩ i hi
    rcases Finset.mem_insert.1 hi with rfl | hi'
    · simpa [locCondD, locMod] using h1
    · have hi0 : i ≠ 0 := fun h => zero_notMem A E hA hE (h ▸ hi')
      rcases Finset.mem_union.1 hi' with hiA | hiE
      · simp only [locCondD, locMod, if_neg hi0, if_pos hiA]
        exact (dvd_mod_add_succ_iff i n _).2 (h2 i hiA)
      · have hiA : i ∉ A := fun h => (Finset.disjoint_left.1 hAE h) hiE
        simp only [locCondD, locMod, if_neg hi0, if_neg hiA]
        obtain ⟨t, htd, ht⟩ := h3 i hiE
        exact ⟨t, htd, (dvd_mod_add_succ_iff i n _).2 ht⟩
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa [locCondD, locMod] using h 0 (Finset.mem_insert_self _ _)
    · intro p hp
      have hp0 : p ≠ 0 := fun hz => Nat.not_prime_zero (hz ▸ hA p hp)
      have hthis := h p (Finset.mem_insert_of_mem (Finset.mem_union_left _ hp))
      simp only [locCondD, locMod, if_neg hp0, if_pos hp] at hthis
      exact (dvd_mod_add_succ_iff p n _).1 hthis
    · intro p hp
      have hp0 : p ≠ 0 := fun hz => Nat.not_prime_zero (hz ▸ hE p hp)
      have hpA : p ∉ A := fun hh => (Finset.disjoint_left.1 hAE hh) hp
      have hthis := h p (Finset.mem_insert_of_mem (Finset.mem_union_right _ hp))
      simp only [locCondD, locMod, if_neg hp0, if_neg hpA] at hthis
      obtain ⟨t, htd, ht⟩ := hthis
      exact ⟨t, htd, (dvd_mod_add_succ_iff p n _).1 ht⟩

private lemma prod_locMod (A E : Finset ℕ) (Q : ℕ) (hA : ∀ p ∈ A, p.Prime)
    (hE : ∀ p ∈ E, p.Prime) (hAE : Disjoint A E) :
    ∏ i ∈ insert 0 (A ∪ E), locMod Q i = Q * ((∏ p ∈ A, p) * ∏ p ∈ E, p) := by
  have h1 : ∀ i ∈ A ∪ E, locMod Q i = i := by
    intro i hi
    have : i ≠ 0 := fun h => zero_notMem A E hA hE (h ▸ hi)
    simp [locMod, this]
  rw [Finset.prod_insert (zero_notMem A E hA hE), Finset.prod_congr rfl h1,
    Finset.prod_union hAE]
  simp [locMod]

private lemma locMod_pos {A E : Finset ℕ} {Q : ℕ} (hA : ∀ p ∈ A, p.Prime)
    (hE : ∀ p ∈ E, p.Prime) (hQ : 0 < Q) :
    ∀ i ∈ insert 0 (A ∪ E), 0 < locMod Q i := by
  intro i hi
  rcases Finset.mem_insert.1 hi with rfl | hi'
  · simpa [locMod] using hQ
  · have hi0 : i ≠ 0 := fun h => zero_notMem A E hA hE (h ▸ hi')
    simp only [locMod, if_neg hi0]
    omega

private lemma pairwise_coprime_locMod {A E : Finset ℕ} {Q : ℕ} (hA : ∀ p ∈ A, p.Prime)
    (hE : ∀ p ∈ E, p.Prime) (hQcop : ∀ p ∈ A ∪ E, Nat.Coprime Q p) :
    ((insert 0 (A ∪ E) : Finset ℕ) : Set ℕ).Pairwise
      fun i i' => (locMod Q i).Coprime (locMod Q i') := by
  intro x hx y hy hxy
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · exact absurd rfl hxy
    · have hy0 : y ≠ 0 := fun h => zero_notMem A E hA hE (h ▸ hy)
      simp only [locMod, if_neg hy0]
      exact hQcop y hy
  · have hx0 : x ≠ 0 := fun h => zero_notMem A E hA hE (h ▸ hx)
    rcases hy with rfl | hy
    · simp only [locMod, if_neg hx0]
      exact (hQcop x hx).symm
    · have hy0 : y ≠ 0 := fun h => zero_notMem A E hA hE (h ▸ hy)
      simp only [locMod, if_neg hx0, if_neg hy0]
      exact (Nat.coprime_primes (prime_of_mem_union hA hE hx)
        (prime_of_mem_union hA hE hy)).2 hxy

/-- A sieve prime `p` with `d p ≤ p` admits exactly `d p` residue classes. -/
lemma card_sieve_graded {p m : ℕ} (hmp : m ≤ p) :
    ((range p).filter fun c => ∃ t, t < m ∧ p ∣ c + t + 1).card = m := by
  have heq : ((range p).filter fun c => ∃ t, t < m ∧ p ∣ c + t + 1)
      = (range p).filter fun c => ∃ t ∈ range m, p ∣ c + t + 1 := by
    refine Finset.filter_congr fun c _ => ?_
    constructor
    · rintro ⟨t, htm, ht⟩; exact ⟨t, Finset.mem_range.2 htm, ht⟩
    · rintro ⟨t, ht, hd⟩; exact ⟨t, Finset.mem_range.1 ht, hd⟩
  rw [heq, card_filter_shift p (range m)
    (fun t ht => lt_of_lt_of_le (Finset.mem_range.1 ht) hmp), Finset.card_range]

private lemma prod_card_locCondD (A E : Finset ℕ) (d j : ℕ → ℕ) (Q r : ℕ)
    (hA : ∀ p ∈ A, p.Prime) (hAj : ∀ p ∈ A, j p < p) (hE : ∀ p ∈ E, p.Prime)
    (hEd : ∀ p ∈ E, d p ≤ p) (hAE : Disjoint A E) (hr : r < Q) :
    ∏ i ∈ insert 0 (A ∪ E), ((range (locMod Q i)).filter (locCondD A d j r i)).card
      = ∏ p ∈ E, d p := by
  rw [Finset.prod_insert (zero_notMem A E hA hE)]
  have h0 : ((range (locMod Q 0)).filter (locCondD A d j r 0)).card = 1 := by
    have hlm : locMod Q 0 = Q := by simp [locMod]
    rw [hlm, Finset.filter_congr (q := fun c => c = r) (fun c _ => by simp [locCondD]),
      Finset.filter_eq' (range Q) r, if_pos (Finset.mem_range.2 hr), Finset.card_singleton]
  have hAc : ∀ p ∈ A, ((range (locMod Q p)).filter (locCondD A d j r p)).card = 1 := by
    intro p hp
    have hp0 : p ≠ 0 := fun hz => Nat.not_prime_zero (hz ▸ hA p hp)
    have hlm : locMod Q p = p := by simp [locMod, hp0]
    rw [hlm, Finset.filter_congr (q := fun c => p ∣ c + j p + 1)
      (fun c _ => by simp [locCondD, hp0, hp])]
    exact card_assigned p _ (hAj p hp)
  have hEc : ∀ p ∈ E, ((range (locMod Q p)).filter (locCondD A d j r p)).card = d p := by
    intro p hp
    have hp0 : p ≠ 0 := fun hz => Nat.not_prime_zero (hz ▸ hE p hp)
    have hpA : p ∉ A := fun hh => (Finset.disjoint_left.1 hAE hh) hp
    have hlm : locMod Q p = p := by simp [locMod, hp0]
    rw [hlm, Finset.filter_congr (q := fun c => ∃ t, t < d p ∧ p ∣ c + t + 1)
      (fun c _ => by simp [locCondD, hp0, hpA])]
    exact card_sieve_graded (hEd p hp)
  rw [h0, Finset.prod_union hAE, Finset.prod_congr rfl hAc, Finset.prod_congr rfl hEc]
  simp

/-- **The graded admissible class count**: exactly `∏_{p ∈ E} d p` classes mod `Q D e`. -/
theorem radical_sieve_admissible_card_graded (A E : Finset ℕ) (d j : ℕ → ℕ) (Q r : ℕ)
    (hA : ∀ p ∈ A, p.Prime) (hAj : ∀ p ∈ A, j p < p) (hE : ∀ p ∈ E, p.Prime)
    (hEd : ∀ p ∈ E, d p ≤ p) (hAE : Disjoint A E) (hQ : 0 < Q) (hr : r < Q)
    (hQcop : ∀ p ∈ A ∪ E, Nat.Coprime Q p) :
    ((range (Q * ((∏ p ∈ A, p) * ∏ p ∈ E, p))).filter (SieveCondD A E d j Q r)).card
      = ∏ p ∈ E, d p := by
  rw [← prod_locMod A E Q hA hE hAE,
    Finset.filter_congr (fun n _ => sieveCondD_iff A E d j Q r hA hE hAE n),
    card_filter_range_prod (insert 0 (A ∪ E)) (locMod Q) (locCondD A d j r)
      (locMod_pos hA hE hQ) (pairwise_coprime_locMod hA hE hQcop)]
  exact prod_card_locCondD A E d j Q r hA hAj hE hEd hAE hr

/-- **Graded CRT counting for the radical sieve.**  The count of `n < X` satisfying
`SieveCondD` is `X ∏_{p ∈ E} d p / (Q D e)` up to an error of at most `∏_{p ∈ E} d p`. -/
theorem radical_sieve_count_graded (A E : Finset ℕ) (d j : ℕ → ℕ) (Q r : ℕ)
    (hA : ∀ p ∈ A, p.Prime) (hAj : ∀ p ∈ A, j p < p) (hE : ∀ p ∈ E, p.Prime)
    (hEd : ∀ p ∈ E, d p ≤ p) (hAE : Disjoint A E) (hQ : 0 < Q) (hr : r < Q)
    (hQcop : ∀ p ∈ A ∪ E, Nat.Coprime Q p) (X : ℕ) :
    |(((range X).filter (SieveCondD A E d j Q r)).card : ℝ)
        - (X : ℝ) * ((∏ p ∈ E, d p : ℕ) : ℝ)
          / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ) * ((∏ p ∈ E, p : ℕ) : ℝ))|
      ≤ ((∏ p ∈ E, d p : ℕ) : ℝ) := by
  classical
  set M : ℕ := Q * ((∏ p ∈ A, p) * ∏ p ∈ E, p) with hMdef
  have hDpos : 0 < (∏ p ∈ A, p) * ∏ p ∈ E, p :=
    Nat.mul_pos (Finset.prod_pos fun p hp => (hA p hp).pos)
      (Finset.prod_pos fun p hp => (hE p hp).pos)
  have hM : 0 < M := Nat.mul_pos hQ hDpos
  have hMprod : M = ∏ i ∈ insert 0 (A ∪ E), locMod Q i :=
    (prod_locMod A E Q hA hE hAE).symm
  have hperiod : ∀ n, SieveCondD A E d j Q r n ↔ SieveCondD A E d j Q r (n % M) := by
    intro n
    rw [sieveCondD_iff A E d j Q r hA hE hAE, sieveCondD_iff A E d j Q r hA hE hAE]
    refine forall_congr' fun i => imp_congr_right fun hi => ?_
    have hdvd : locMod Q i ∣ M := by
      rw [hMprod]; exact Finset.dvd_prod_of_mem _ hi
    rw [Nat.mod_mod_of_dvd n hdvd]
  have hbase := abs_card_filter_periodic_sub_le hM X (SieveCondD A E d j Q r) hperiod
  rw [radical_sieve_admissible_card_graded A E d j Q r hA hAj hE hEd hAE hQ hr hQcop] at hbase
  have hMcast : (M : ℝ) = (Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ) * ((∏ p ∈ E, p : ℕ) : ℝ) := by
    rw [hMdef]; push_cast; ring
  calc |(((range X).filter (SieveCondD A E d j Q r)).card : ℝ)
        - (X : ℝ) * ((∏ p ∈ E, d p : ℕ) : ℝ)
          / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ) * ((∏ p ∈ E, p : ℕ) : ℝ))|
      = |(((range X).filter (SieveCondD A E d j Q r)).card : ℝ)
          - ((∏ p ∈ E, d p : ℕ) : ℝ) * (X : ℝ) / (M : ℝ)| := by
        rw [← hMcast]; ring_nf
    _ ≤ ((∏ p ∈ E, d p : ℕ) : ℝ) := hbase

end NormalNumbers.PrimeModel.RadicalGraded
