/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4CRTInput

/-!
# Exact CRT counting for the radical sieve

The prime-model radical sieve needs to count `n < X` subject to a *residue* condition modulo
`Q` together with local divisibility conditions at two disjoint families of "large" primes:

* **assigned** primes `p ∈ A`: a prescribed shift `j p : Fin k` with `p ∣ n + (j p) + 1`;
* **sieve** primes `p ∈ E`: *some* shift `t < k` with `p ∣ n + t + 1`.

The main theorem `radical_sieve_count` gives the count with error at most `ρ = k ^ #E`, the
number of admissible classes modulo `Q · D · e`.  The class count is **proved**, not assumed.

## Main results

* `card_filter_shift` — for `m > 0` and `S ⊆ range m`, exactly `#S` residues `c < m` satisfy
  `∃ t ∈ S, m ∣ c + t + 1` (the negative shifts `-(t+1)` are distinct mod `m`).
* `sum_range_prod_eq_prod_sum` — the multi-modulus CRT factorisation of a sum of products of
  periodic functions (induction on the index set, on top of `G4.sum_range_mul_eq_mul_sum`).
* `card_filter_range_prod` — **CRT class count**: the number of residues mod `∏ m i` satisfying
  a local condition at each pairwise-coprime modulus is the product of the local counts.
* `abs_card_filter_periodic_sub_le` — for an `M`-periodic predicate, the count over `range X` is
  within `#classes` of `#classes · X / M`.
* `radical_sieve_admissible_card` — the admissible classes mod `Q · D · e` number exactly `ρ`.
* **`radical_sieve_count`** — the headline bound `|count − X ρ / (Q D e)| ≤ ρ`.

This counts *divisibility at the sieve primes*, not exact radical tuples, and it is **not** the
two-sided fundamental lemma of the sieve; see the note at the end of the file.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.Radical

/-! ### The `k` negative shifts are distinct residues -/

/-- For `m > 0` and `S` a set of residues `< m`, exactly `#S` residues `c < m` satisfy
`∃ t ∈ S, m ∣ c + t + 1`: the solution for a given `t` is the single class `c = m - 1 - t`. -/
lemma card_filter_shift (m : ℕ) (S : Finset ℕ) (hS : ∀ t ∈ S, t < m) :
    ((range m).filter fun c => ∃ t ∈ S, m ∣ c + t + 1).card = S.card := by
  classical
  refine Finset.card_bij' (fun c _ => m - 1 - c) (fun t _ => m - 1 - t) ?_ ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_range] at hc
    obtain ⟨hcm, t, htS, u, hu⟩ := hc
    have htm : t < m := hS t htS
    have hu1 : u = 1 := by
      match u with
      | 0 => omega
      | 1 => rfl
      | (v + 2) =>
        exfalso
        have : m * 2 ≤ m * (v + 2) := Nat.mul_le_mul_left _ (by omega)
        omega
    subst hu1
    have : m - 1 - c = t := by omega
    rw [this]; exact htS
  · intro t ht
    have htm : t < m := hS t ht
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, t, ht, ?_⟩
    have : m - 1 - t + t + 1 = m := by omega
    rw [this]
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_range] at hc
    omega
  · intro t ht
    have := hS t ht
    omega

/-! ### Multi-modulus CRT factorisation of a sum -/

/-- **Multi-modulus CRT.** For pairwise-coprime positive moduli `p i` and `h i` periodic mod
`p i`, `∑_{b < ∏ p i} ∏ h i b = ∏ (∑_{b < p i} h i b)`. -/
lemma sum_range_prod_eq_prod_sum {ι : Type*} [DecidableEq ι] (T : Finset ι) (h : ι → ℕ → ℂ)
    (p : ι → ℕ) (hp : ∀ i ∈ T, 0 < p i)
    (hcop : (T : Set ι).Pairwise fun i j => (p i).Coprime (p j))
    (hper : ∀ i ∈ T, G4.PeriodicMod (h i) (p i)) :
    ∑ b ∈ range (∏ i ∈ T, p i), ∏ i ∈ T, h i b = ∏ i ∈ T, ∑ b ∈ range (p i), h i b := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T haT ih =>
    have hpa : 0 < p a := hp a (Finset.mem_insert_self a T)
    have hpT : ∀ i ∈ T, 0 < p i := fun i hi => hp i (Finset.mem_insert_of_mem hi)
    have hperT : ∀ i ∈ T, G4.PeriodicMod (h i) (p i) := fun i hi =>
      hper i (Finset.mem_insert_of_mem hi)
    have hcopT : (T : Set ι).Pairwise fun i j => (p i).Coprime (p j) :=
      hcop.mono (by intro x hx; simp only [Finset.coe_insert, Set.mem_insert_iff]; exact Or.inr hx)
    have hcopa : (p a).Coprime (∏ i ∈ T, p i) := by
      rw [Nat.coprime_prod_right_iff]
      intro i hi
      exact hcop (Finset.mem_insert_self a T) (Finset.mem_insert_of_mem hi)
        (fun hh => haT (hh ▸ hi))
    have hQT : 0 < ∏ i ∈ T, p i := Finset.prod_pos hpT
    have hkey := G4.sum_range_mul_eq_mul_sum hcopa hpa hQT (h a) (fun n => ∏ i ∈ T, h i n)
      (hper a (Finset.mem_insert_self a T)) (G4.periodicMod_prod T h p hperT)
    simp only [Finset.prod_insert haT]
    rw [hkey, ih hpT hcopT hperT]

/-! ### The CRT class count -/

/-- **CRT class count.** The number of residues `n < ∏ m i` satisfying a local condition
`B i` on `n % m i` for each `i` in a family of pairwise-coprime positive moduli is the product
of the local counts. -/
lemma card_filter_range_prod {ι : Type*} [DecidableEq ι] (T : Finset ι) (m : ι → ℕ)
    (B : ι → ℕ → Prop) [∀ i, DecidablePred (B i)] (hm : ∀ i ∈ T, 0 < m i)
    (hcop : (T : Set ι).Pairwise fun i j => (m i).Coprime (m j)) :
    ((range (∏ i ∈ T, m i)).filter fun n => ∀ i ∈ T, B i (n % m i)).card
      = ∏ i ∈ T, ((range (m i)).filter (B i)).card := by
  classical
  set h : ι → ℕ → ℂ := fun i n => if B i (n % m i) then 1 else 0 with hh
  have hper : ∀ i ∈ T, G4.PeriodicMod (h i) (m i) := by
    intro i _ n
    simp only [hh, Nat.mod_mod_of_dvd n (dvd_refl (m i))]
  have hkey := sum_range_prod_eq_prod_sum T h m hm hcop hper
  -- left side is the class count
  have hL : ∑ b ∈ range (∏ i ∈ T, m i), ∏ i ∈ T, h i b
      = (((range (∏ i ∈ T, m i)).filter fun n => ∀ i ∈ T, B i (n % m i)).card : ℂ) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun b _ => ?_
    simpa only [hh] using Finset.prod_boole (s := T) (p := fun i => B i (b % m i)) (M₀ := ℂ)
  -- each factor on the right is a local count
  have hR : ∀ i ∈ T, ∑ b ∈ range (m i), h i b = ((((range (m i)).filter (B i)).card : ℕ) : ℂ) := by
    intro i _
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [hh]
    simp only [Nat.mod_eq_of_lt (Finset.mem_range.1 hb)]
  rw [hL, Finset.prod_congr rfl hR] at hkey
  have : ((((range (∏ i ∈ T, m i)).filter fun n => ∀ i ∈ T, B i (n % m i)).card : ℕ) : ℂ)
      = ((∏ i ∈ T, ((range (m i)).filter (B i)).card : ℕ) : ℂ) := by
    rw [hkey]; push_cast; ring
  exact_mod_cast this

/-! ### From a periodic predicate to a count over `range X` -/

/-- For an `M`-periodic predicate `P`, the number of `n < X` with `P n` is within
`#{c < M : P c}` of `#{c < M : P c} · X / M`. -/
lemma abs_card_filter_periodic_sub_le {M : ℕ} (hM : 0 < M) (X : ℕ) (P : ℕ → Prop)
    [DecidablePred P] (hP : ∀ n, P n ↔ P (n % M)) :
    |(((range X).filter P).card : ℝ) - (((range M).filter P).card : ℝ) * (X : ℝ) / M|
      ≤ (((range M).filter P).card : ℝ) := by
  classical
  set S := (range M).filter P with hS
  have hunion : (range X).filter P
      = S.biUnion fun c => (range X).filter fun n => n % M = c := by
    ext n
    simp only [hS, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hn, hPn⟩
      exact ⟨n % M, ⟨Nat.mod_lt _ hM, (hP n).1 hPn⟩, hn, rfl⟩
    · rintro ⟨c, ⟨_, hPc⟩, hn, hnc⟩
      exact ⟨hn, (hP n).2 (hnc ▸ hPc)⟩
  have hdisj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      Disjoint ((range X).filter fun n => n % M = x) ((range X).filter fun n => n % M = y) := by
    intro x _ y _ hxy
    simp only [Finset.disjoint_left, Finset.mem_filter]
    rintro n ⟨_, hnx⟩ ⟨_, hny⟩
    exact hxy (hnx ▸ hny ▸ rfl)
  have hcard : ∀ c ∈ S, |(((range X).filter fun n => n % M = c).card : ℝ) - (X : ℝ) / M| ≤ 1 := by
    intro c hc
    have hcM : c < M := Finset.mem_range.1 (Finset.mem_filter.1 hc).1
    have heq : ((range X).filter fun n => n % M = c)
        = (range X).filter fun n => n ≡ c [MOD M] := by
      refine Finset.filter_congr fun n _ => ?_
      simp only [Nat.ModEq, Nat.mod_eq_of_lt hcM]
    rw [heq]
    exact G4.abs_card_filter_modEq_sub_le X M c hM
  rw [hunion, Finset.card_biUnion hdisj]
  have hrw : ((∑ c ∈ S, ((range X).filter fun n => n % M = c).card : ℕ) : ℝ)
      - (S.card : ℝ) * (X : ℝ) / M
      = ∑ c ∈ S, ((((range X).filter fun n => n % M = c).card : ℝ) - (X : ℝ) / M) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    push_cast
    ring
  rw [hrw]
  calc |∑ c ∈ S, ((((range X).filter fun n => n % M = c).card : ℝ) - (X : ℝ) / M)|
      ≤ ∑ c ∈ S, |(((range X).filter fun n => n % M = c).card : ℝ) - (X : ℝ) / M| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ S, (1 : ℝ) := Finset.sum_le_sum hcard
    _ = (S.card : ℝ) := by simp

/-! ### The radical sieve condition -/

/-- Residue condition mod `Q`, prescribed shift at each assigned prime `p ∈ A`, and *some*
shift `< k` at each sieve prime `p ∈ E`. -/
def SieveCond (k : ℕ) (A E : Finset ℕ) (Q r : ℕ) (j : ℕ → Fin k) (n : ℕ) : Prop :=
  n % Q = r ∧ (∀ p ∈ A, p ∣ n + (j p).val + 1) ∧ (∀ p ∈ E, ∃ t : Fin k, p ∣ n + t.val + 1)

instance (k : ℕ) (A E : Finset ℕ) (Q r : ℕ) (j : ℕ → Fin k) :
    DecidablePred (SieveCond k A E Q r j) := fun n => by
  unfold SieveCond; infer_instance

/-- Reducing the argument mod `p` does not change divisibility of the shifted value. -/
lemma dvd_mod_add_succ_iff (p n a : ℕ) : p ∣ n % p + a + 1 ↔ p ∣ n + a + 1 := by
  have h : n % p + a + 1 ≡ n + a + 1 [MOD p] :=
    ((Nat.mod_modEq n p).add_right a).add_right 1
  rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
  exact ⟨fun hd => h.symm.trans hd, fun hd => h.trans hd⟩

/-- The local modulus family: `Q` at the index `0`, and `p` itself at each prime `p ∈ A ∪ E`. -/
private def locMod (Q : ℕ) : ℕ → ℕ := fun i => if i = 0 then Q else i

/-- The local condition at each index. -/
private def locCond (k : ℕ) (A : Finset ℕ) (r : ℕ) (j : ℕ → Fin k) : ℕ → ℕ → Prop :=
  fun i c => if i = 0 then c = r else if i ∈ A then i ∣ c + (j i).val + 1
    else ∃ t : Fin k, i ∣ c + t.val + 1

private instance (k : ℕ) (A : Finset ℕ) (r : ℕ) (j : ℕ → Fin k) (i : ℕ) :
    DecidablePred (locCond k A r j i) := fun c => by
  unfold locCond; infer_instance

/-- `0` is not a prime, so it is not one of the sieve indices. -/
private lemma zero_notMem (A E : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (hE : ∀ p ∈ E, p.Prime) :
    0 ∉ A ∪ E := by
  simp only [Finset.mem_union, not_or]
  exact ⟨fun h => Nat.not_prime_zero (hA 0 h), fun h => Nat.not_prime_zero (hE 0 h)⟩

private lemma prime_of_mem_union {A E : Finset ℕ} (hA : ∀ p ∈ A, p.Prime)
    (hE : ∀ p ∈ E, p.Prime) {p : ℕ} (hp : p ∈ A ∪ E) : p.Prime := by
  rcases Finset.mem_union.1 hp with h | h
  · exact hA p h
  · exact hE p h

/-- `SieveCond` is exactly the conjunction of the local conditions at the pairwise-coprime
moduli `Q` (index `0`) and `p` (index `p ∈ A ∪ E`). -/
private lemma sieveCond_iff {k : ℕ} (A E : Finset ℕ) (Q r : ℕ) (j : ℕ → Fin k)
    (hA : ∀ p ∈ A, p.Prime) (hE : ∀ p ∈ E, p.Prime) (hAE : Disjoint A E) (n : ℕ) :
    SieveCond k A E Q r j n ↔
      ∀ i ∈ insert 0 (A ∪ E), locCond k A r j i (n % locMod Q i) := by
  constructor
  · rintro ⟨h1, h2, h3⟩ i hi
    rcases Finset.mem_insert.1 hi with rfl | hi'
    · simpa [locCond, locMod] using h1
    · have hi0 : i ≠ 0 := fun h => zero_notMem A E hA hE (h ▸ hi')
      rcases Finset.mem_union.1 hi' with hiA | hiE
      · simp only [locCond, locMod, if_neg hi0, if_pos hiA]
        exact (dvd_mod_add_succ_iff i n _).2 (h2 i hiA)
      · have hiA : i ∉ A := fun h => (Finset.disjoint_left.1 hAE h) hiE
        simp only [locCond, locMod, if_neg hi0, if_neg hiA]
        obtain ⟨t, ht⟩ := h3 i hiE
        exact ⟨t, (dvd_mod_add_succ_iff i n _).2 ht⟩
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa [locCond, locMod] using h 0 (Finset.mem_insert_self _ _)
    · intro p hp
      have hp0 : p ≠ 0 := fun hz => Nat.not_prime_zero (hz ▸ hA p hp)
      have hthis := h p (Finset.mem_insert_of_mem (Finset.mem_union_left _ hp))
      simp only [locCond, locMod, if_neg hp0, if_pos hp] at hthis
      exact (dvd_mod_add_succ_iff p n _).1 hthis
    · intro p hp
      have hp0 : p ≠ 0 := fun hz => Nat.not_prime_zero (hz ▸ hE p hp)
      have hpA : p ∉ A := fun hh => (Finset.disjoint_left.1 hAE hh) hp
      have hthis := h p (Finset.mem_insert_of_mem (Finset.mem_union_right _ hp))
      simp only [locCond, locMod, if_neg hp0, if_neg hpA] at hthis
      obtain ⟨t, ht⟩ := hthis
      exact ⟨t, (dvd_mod_add_succ_iff p n _).1 ht⟩

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

/-! ### The local counts -/

/-- An assigned prime pins down a single residue class. -/
lemma card_assigned (p a : ℕ) (hap : a < p) :
    ((range p).filter fun c => p ∣ c + a + 1).card = 1 := by
  have h := card_filter_shift p {a} (by simpa using hap)
  simpa using h

/-- A sieve prime `p > k` admits exactly `k` residue classes. -/
lemma card_sieve {k : ℕ} (p : ℕ) (hkp : k < p) :
    ((range p).filter fun c => ∃ t : Fin k, p ∣ c + t.val + 1).card = k := by
  have heq : ((range p).filter fun c => ∃ t : Fin k, p ∣ c + t.val + 1)
      = (range p).filter fun c => ∃ t ∈ range k, p ∣ c + t + 1 := by
    refine Finset.filter_congr fun c _ => ?_
    constructor
    · rintro ⟨t, ht⟩; exact ⟨t.val, Finset.mem_range.2 t.isLt, ht⟩
    · rintro ⟨t, ht, hd⟩; exact ⟨⟨t, Finset.mem_range.1 ht⟩, hd⟩
  rw [heq, card_filter_shift p (range k)
    (fun t ht => lt_trans (Finset.mem_range.1 ht) hkp), Finset.card_range]

private lemma prod_card_locCond {k : ℕ} (A E : Finset ℕ) (Q r : ℕ) (j : ℕ → Fin k)
    (hA : ∀ p ∈ A, p.Prime) (hAk : ∀ p ∈ A, k < p) (hE : ∀ p ∈ E, p.Prime)
    (hEk : ∀ p ∈ E, k < p) (hAE : Disjoint A E) (hr : r < Q) :
    ∏ i ∈ insert 0 (A ∪ E), ((range (locMod Q i)).filter (locCond k A r j i)).card
      = k ^ E.card := by
  rw [Finset.prod_insert (zero_notMem A E hA hE)]
  have h0 : ((range (locMod Q 0)).filter (locCond k A r j 0)).card = 1 := by
    have hlm : locMod Q 0 = Q := by simp [locMod]
    rw [hlm, Finset.filter_congr (q := fun c => c = r) (fun c _ => by simp [locCond]),
      Finset.filter_eq' (range Q) r, if_pos (Finset.mem_range.2 hr), Finset.card_singleton]
  have hAc : ∀ p ∈ A, ((range (locMod Q p)).filter (locCond k A r j p)).card = 1 := by
    intro p hp
    have hp0 : p ≠ 0 := fun hz => Nat.not_prime_zero (hz ▸ hA p hp)
    have hlm : locMod Q p = p := by simp [locMod, hp0]
    rw [hlm, Finset.filter_congr (q := fun c => p ∣ c + (j p).val + 1)
      (fun c _ => by simp [locCond, hp0, hp])]
    exact card_assigned p _ (lt_trans (j p).isLt (hAk p hp))
  have hEc : ∀ p ∈ E, ((range (locMod Q p)).filter (locCond k A r j p)).card = k := by
    intro p hp
    have hp0 : p ≠ 0 := fun hz => Nat.not_prime_zero (hz ▸ hE p hp)
    have hpA : p ∉ A := fun hh => (Finset.disjoint_left.1 hAE hh) hp
    have hlm : locMod Q p = p := by simp [locMod, hp0]
    rw [hlm, Finset.filter_congr (q := fun c => ∃ t : Fin k, p ∣ c + t.val + 1)
      (fun c _ => by simp [locCond, hp0, hpA])]
    exact card_sieve p (hEk p hp)
  rw [h0, Finset.prod_union hAE, Finset.prod_congr rfl hAc, Finset.prod_congr rfl hEc]
  simp

/-! ### The admissible class count and the headline bound -/

/-- **The admissible classes modulo `Q · D · e` number exactly `ρ = k ^ #E`.** -/
theorem radical_sieve_admissible_card {k : ℕ} (A E : Finset ℕ) (Q r : ℕ) (j : ℕ → Fin k)
    (hA : ∀ p ∈ A, p.Prime) (hAk : ∀ p ∈ A, k < p) (hE : ∀ p ∈ E, p.Prime)
    (hEk : ∀ p ∈ E, k < p) (hAE : Disjoint A E) (hQ : 0 < Q) (hr : r < Q)
    (hQcop : ∀ p ∈ A ∪ E, Nat.Coprime Q p) :
    ((range (Q * ((∏ p ∈ A, p) * ∏ p ∈ E, p))).filter (SieveCond k A E Q r j)).card
      = k ^ E.card := by
  rw [← prod_locMod A E Q hA hE hAE,
    Finset.filter_congr (fun n _ => sieveCond_iff A E Q r j hA hE hAE n),
    card_filter_range_prod (insert 0 (A ∪ E)) (locMod Q) (locCond k A r j)
      (locMod_pos hA hE hQ) (pairwise_coprime_locMod hA hE hQcop)]
  exact prod_card_locCond A E Q r j hA hAk hE hEk hAE hr

/-- **Exact CRT counting for the radical sieve.**  With `k ≥ 1`, `A` (assigned primes) and `E`
(sieve primes) disjoint sets of primes all `> k`, `Q > 0` coprime to every prime of `A ∪ E`,
and `r < Q`, the number of `n < X` with

* `n ≡ r (mod Q)`,
* `p ∣ n + (j p) + 1` for every assigned prime `p ∈ A`,
* `p ∣ n + t + 1` for *some* `t < k`, for every sieve prime `p ∈ E`,

is `X ρ / (Q D e)` up to an error of at most `ρ`, where `D = ∏_{p ∈ A} p`, `e = ∏_{p ∈ E} p`
and `ρ = k ^ #E`.  The class count `ρ` is proved in `radical_sieve_admissible_card`. -/
theorem radical_sieve_count {k : ℕ} (_hk : 1 ≤ k) (A E : Finset ℕ) (Q r : ℕ) (j : ℕ → Fin k)
    (hA : ∀ p ∈ A, p.Prime) (hAk : ∀ p ∈ A, k < p) (hE : ∀ p ∈ E, p.Prime)
    (hEk : ∀ p ∈ E, k < p) (hAE : Disjoint A E) (hQ : 0 < Q) (hr : r < Q)
    (hQcop : ∀ p ∈ A ∪ E, Nat.Coprime Q p) (X : ℕ) :
    |(((range X).filter (SieveCond k A E Q r j)).card : ℝ)
        - (X : ℝ) * ((k ^ E.card : ℕ) : ℝ)
          / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ) * ((∏ p ∈ E, p : ℕ) : ℝ))|
      ≤ ((k ^ E.card : ℕ) : ℝ) := by
  classical
  set M : ℕ := Q * ((∏ p ∈ A, p) * ∏ p ∈ E, p) with hMdef
  have hDpos : 0 < (∏ p ∈ A, p) * ∏ p ∈ E, p :=
    Nat.mul_pos (Finset.prod_pos fun p hp => (hA p hp).pos)
      (Finset.prod_pos fun p hp => (hE p hp).pos)
  have hM : 0 < M := Nat.mul_pos hQ hDpos
  have hMprod : M = ∏ i ∈ insert 0 (A ∪ E), locMod Q i :=
    (prod_locMod A E Q hA hE hAE).symm
  have hperiod : ∀ n, SieveCond k A E Q r j n ↔ SieveCond k A E Q r j (n % M) := by
    intro n
    rw [sieveCond_iff A E Q r j hA hE hAE, sieveCond_iff A E Q r j hA hE hAE]
    refine forall_congr' fun i => imp_congr_right fun hi => ?_
    have hdvd : locMod Q i ∣ M := by
      rw [hMprod]; exact Finset.dvd_prod_of_mem _ hi
    rw [Nat.mod_mod_of_dvd n hdvd]
  have hbase := abs_card_filter_periodic_sub_le hM X (SieveCond k A E Q r j) hperiod
  rw [radical_sieve_admissible_card A E Q r j hA hAk hE hEk hAE hQ hr hQcop] at hbase
  have hMcast : (M : ℝ) = (Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ) * ((∏ p ∈ E, p : ℕ) : ℝ) := by
    rw [hMdef]; push_cast; ring
  have hMne : (M : ℝ) ≠ 0 := by positivity
  calc |(((range X).filter (SieveCond k A E Q r j)).card : ℝ)
        - (X : ℝ) * ((k ^ E.card : ℕ) : ℝ)
          / ((Q : ℝ) * ((∏ p ∈ A, p : ℕ) : ℝ) * ((∏ p ∈ E, p : ℕ) : ℝ))|
      = |(((range X).filter (SieveCond k A E Q r j)).card : ℝ)
          - ((k ^ E.card : ℕ) : ℝ) * (X : ℝ) / (M : ℝ)| := by
        rw [← hMcast]; ring_nf
    _ ≤ ((k ^ E.card : ℕ) : ℝ) := hbase

/-! ### Numeric anchors

`k = 2`, `Q = 2`, `r = 0`, `A = {3}` with shift `0`, `E = {5}`: the two admissible classes
mod `30` are `8` and `14`.  Independently checked by the kernel. -/

example : ((range 30).filter (SieveCond 2 {3} {5} 2 0 (fun _ => 0))).card = 2 := by decide

example : ((range 30).filter (SieveCond 2 {3} {5} 2 0 (fun _ => 0))) = {8, 14} := by decide

example : ((range 20).filter (SieveCond 2 {3} {5} 2 0 (fun _ => 0))).card = 2 := by decide

example : ((range 9).filter (SieveCond 2 {3} {5} 2 0 (fun _ => 0))).card = 1 := by decide

example : ((range 20).filter (SieveCond 2 {3} ∅ 2 0 (fun _ => 0))).card = 3 := by decide

example : ((range 20).filter (SieveCond 2 ∅ {3, 5} 2 0 (fun _ => 0))).card = 3 := by decide

/-! ### Scope of this result

For the radical tuple sieve, `E` ranges over the subsets of the *unassigned* primes in the
sieve range: an inclusion-exclusion / Selberg weight over those subsets is what converts the
one-sided divisibility count above into a count of `n` whose shifted values `n + t + 1`
(`t < k`) have no unassigned prime factor in the range.  The assigned primes `p ∈ A` need no
exclusion because the shift `j p` is prescribed, so their local condition is a single class
and contributes the factor `1/p` exactly; only the sieve primes contribute the `k` choices,
giving the main density `ρ / (Q D e)` with `ρ = k^{#E}`.

**Remaining obligation.** This is a one-sided local count.  The two-sided fundamental lemma of
the sieve (upper *and* lower bounds for the sifted count, with the error term summed over all
`E` in the sieve range) is *not* proved here.
-/

end NormalNumbers.PrimeModel.Radical
