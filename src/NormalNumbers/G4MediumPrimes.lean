/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4RowMass

/-!
# G4 disjunctivity, §4D: the medium primes `R < p ≤ Y` — the signed L² estimate

Brief §4D, medium range.  For a sample `P`, shifts `ρ_i`, real coefficients `c_i` with
`∑ c_i = 0`, and a set `S` of primes, the block

  `T(n) = ∑_{p ∈ S} ∑_i c_i · 1[p ∣ n + ρ_i]`

has sample second moment controlled by **two-congruence counting**:

  `∑_{n∈P} T(n)² = ∑_{p,p'} ∑_{i,i'} c_i c_{i'} · #{n ∈ P : p ∣ n+ρ_i, p' ∣ n+ρ_{i'}}`.

* `p ≠ p'`: the count is one residue class mod `pp'`, so it is `|P|/(pp') + O(1)`; the main
  term carries the factor `(∑_i c_i)² = 0` — **the signed cancellation** — leaving `O((∑|c_i|)²)`.
* `p = p'`: if the shifts are *separated* mod `p` (no `p ∈ S` divides `n+ρ_i` and `n+ρ_{i'}`
  with `i ≠ i'`; true when every `|ρ_i − ρ_{i'}| < p`), only `i = i'` survives, giving
  `(|P|/p + O(1)) ∑_i c_i²`.

Hence `sum_sq_block_le`:

  `∑_{n∈P} T(n)² ≤ |P| · (∑_{p∈S} 1/p) · (∑_i c_i²) + 2 |S|² (∑_i |c_i|)²`,

and by Cauchy–Schwarz (`sampleAvg_abs_le_sqrt`) the sample mean of `|T|` is at most the square
root of the sample mean of `T²`.  A single pointwise bound over all primes above `R` would
replace `∑ c_i²` by `(∑|c_i|)²`-type mass with a `log X` weight, which is what the brief forbids.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

/-! ### Residue classes of `p ∣ n + ρ` -/

/-- `p ∣ n + ρ ↔ n ≡ (p − 1) ρ (mod p)`. -/
lemma dvd_add_iff_modEq {p : ℕ} (hp : 0 < p) (n ρ : ℕ) :
    p ∣ n + ρ ↔ n ≡ (p - 1) * ρ [MOD p] := by
  have key : (p - 1) * ρ + ρ = p * ρ := by
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    rw [Nat.add_sub_cancel]; ring
  have hp0 : p * ρ ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.2 (dvd_mul_right p ρ)
  constructor
  · intro h
    refine Nat.ModEq.add_right_cancel' ρ ?_
    rw [key]
    exact (Nat.modEq_zero_iff_dvd.2 h).trans hp0.symm
  · intro h
    have h1 : n + ρ ≡ (p - 1) * ρ + ρ [MOD p] := Nat.ModEq.add_right ρ h
    rw [key] at h1
    exact Nat.modEq_zero_iff_dvd.1 (h1.trans hp0)

/-- The class `{n ∈ P : p ∣ n + ρ}` as a residue class `n % p = r`, `r < p`. -/
lemma filter_dvd_add_eq (P : Finset ℕ) {p : ℕ} (hp : 0 < p) (ρ : ℕ) :
    P.filter (fun n => p ∣ n + ρ) = P.filter (fun n => n % p = ((p - 1) * ρ) % p) :=
  Finset.filter_congr fun n _ => dvd_add_iff_modEq hp n ρ

/-- The class `{n ∈ P : p ∣ n + ρ, p' ∣ n + ρ'}` for coprime `p, p'` as a residue class modulo
`pp'`. -/
lemma filter_dvd_add_and_eq (P : Finset ℕ) {p p' : ℕ} (hp : 0 < p) (hp' : 0 < p')
    (hcop : p.Coprime p') (ρ ρ' : ℕ) :
    P.filter (fun n => p ∣ n + ρ ∧ p' ∣ n + ρ')
      = P.filter (fun n => n % (p * p')
          = (Nat.chineseRemainder hcop ((p - 1) * ρ) ((p' - 1) * ρ') : ℕ)) := by
  refine Finset.filter_congr fun n _ => ?_
  obtain ⟨hk1, hk2⟩ := (Nat.chineseRemainder hcop ((p - 1) * ρ) ((p' - 1) * ρ')).prop
  have hlt := Nat.chineseRemainder_lt_mul hcop ((p - 1) * ρ) ((p' - 1) * ρ') hp.ne' hp'.ne'
  rw [dvd_add_iff_modEq hp, dvd_add_iff_modEq hp']
  constructor
  · rintro ⟨h1, h2⟩
    have := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨h1.trans hk1.symm, h2.trans hk2.symm⟩
    unfold Nat.ModEq at this
    rw [this, Nat.mod_eq_of_lt hlt]
  · intro h
    have h' : n ≡ (Nat.chineseRemainder hcop ((p - 1) * ρ) ((p' - 1) * ρ') : ℕ) [MOD p * p'] := by
      unfold Nat.ModEq; rw [h, Nat.mod_eq_of_lt hlt]
    obtain ⟨h1, h2⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hcop).2 h'
    exact ⟨h1.trans hk1, h2.trans hk2⟩

/-! ### The indicator and the pair count -/

/-- `1[p ∣ m]`. -/
noncomputable def ind (p m : ℕ) : ℝ := if p ∣ m then 1 else 0

lemma ind_mul_ind (p m p' m' : ℕ) :
    ind p m * ind p' m' = if (p ∣ m ∧ p' ∣ m') then 1 else 0 := by
  unfold ind
  split_ifs <;> simp_all

section Abstract

variable {ι : Type*} [Fintype ι]

/-- The pair count `#{n ∈ P : p ∣ n+ρ_i, p' ∣ n+ρ_{i'}}`. -/
noncomputable def pairCount (P : Finset ℕ) (ρ : ι → ℕ) (p : ℕ) (i : ι) (p' : ℕ) (i' : ι) : ℝ :=
  ((P.filter (fun n => p ∣ n + ρ i ∧ p' ∣ n + ρ i')).card : ℝ)

/-- **Expansion of the second moment by pair counts.** -/
lemma sum_sq_block_eq (P S : Finset ℕ) (c : ι → ℝ) (ρ : ι → ℕ) :
    ∑ n ∈ P, (∑ p ∈ S, ∑ i, c i * ind p (n + ρ i)) ^ 2
      = ∑ p ∈ S, ∑ p' ∈ S, ∑ i, ∑ i', c i * c i' * pairCount P ρ p i p' i' := by
  set f : ℕ × ι → ℕ → ℝ := fun x n => c x.2 * ind x.1 (n + ρ x.2) with hf
  set g : ℕ × ι → ℕ × ι → ℝ := fun x y => c x.2 * c y.2 * pairCount P ρ x.1 x.2 y.1 y.2 with hg
  have h1 : ∀ n, (∑ p ∈ S, ∑ i, c i * ind p (n + ρ i))
      = ∑ x ∈ S ×ˢ (Finset.univ : Finset ι), f x n := by
    intro n; rw [Finset.sum_product]
  have h2 : ∀ x y : ℕ × ι, ∑ n ∈ P, f x n * f y n = g x y := by
    intro x y
    simp only [hf, hg, pairCount]
    rw [← Finset.sum_boole, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show c x.2 * ind x.1 (n + ρ x.2) * (c y.2 * ind y.1 (n + ρ y.2))
        = c x.2 * c y.2 * (ind x.1 (n + ρ x.2) * ind y.1 (n + ρ y.2)) by ring, ind_mul_ind]
  calc ∑ n ∈ P, (∑ p ∈ S, ∑ i, c i * ind p (n + ρ i)) ^ 2
      = ∑ n ∈ P, ∑ x ∈ S ×ˢ (Finset.univ : Finset ι),
          ∑ y ∈ S ×ˢ (Finset.univ : Finset ι), f x n * f y n := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [h1, sq, Finset.sum_mul_sum]
    _ = ∑ x ∈ S ×ˢ (Finset.univ : Finset ι),
          ∑ y ∈ S ×ˢ (Finset.univ : Finset ι), ∑ n ∈ P, f x n * f y n := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ x ∈ S ×ˢ (Finset.univ : Finset ι), ∑ y ∈ S ×ˢ (Finset.univ : Finset ι), g x y := by
        simp_rw [h2]
    _ = ∑ p ∈ S, ∑ i, ∑ p' ∈ S, ∑ i', g (p, i) (p', i') := by
        rw [Finset.sum_product]
        refine Finset.sum_congr rfl fun p _ => ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_product]
    _ = ∑ p ∈ S, ∑ p' ∈ S, ∑ i, ∑ i', g (p, i) (p', i') := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]
    _ = _ := rfl

/-! ### The three pair-count estimates -/

omit [Fintype ι] in
/-- Same prime, same shift: the class `p ∣ n + ρ_i` has `|P|/p + O(1)` elements. -/
lemma pairCount_diag_le (P : Finset ℕ) (ρ : ι → ℕ) {p : ℕ} (hp : 0 < p)
    (heq : ∀ r < p, |((P.filter (fun n => n % p = r)).card : ℝ) - P.card / p| ≤ 2) (i : ι) :
    pairCount P ρ p i p i ≤ P.card / p + 2 := by
  unfold pairCount
  have h : P.filter (fun n => p ∣ n + ρ i ∧ p ∣ n + ρ i)
      = P.filter (fun n => n % p = ((p - 1) * ρ i) % p) := by
    rw [← filter_dvd_add_eq P hp]
    exact Finset.filter_congr fun n _ => and_self_iff
  rw [h]
  have := heq (((p - 1) * ρ i) % p) (Nat.mod_lt _ hp)
  linarith [(abs_le.1 this).2]

omit [Fintype ι] in
/-- Same prime, different shifts, separated: **zero**. -/
lemma pairCount_diag_eq_zero (P : Finset ℕ) (ρ : ι → ℕ) (p : ℕ)
    (hsep : ∀ n, ∀ i i', p ∣ n + ρ i → p ∣ n + ρ i' → i = i') {i i' : ι} (h : i ≠ i') :
    pairCount P ρ p i p i' = 0 := by
  unfold pairCount
  rw [Finset.filter_eq_empty_iff.2 fun n _ hn => h (hsep n i i' hn.1 hn.2)]
  simp

omit [Fintype ι] in
/-- Distinct coprime primes: one class modulo `pp'`, so `|P|/(pp') + O(1)`. -/
lemma abs_pairCount_sub_le (P : Finset ℕ) (ρ : ι → ℕ) {p p' : ℕ} (hp : 0 < p) (hp' : 0 < p')
    (hcop : p.Coprime p')
    (heq : ∀ r < p * p',
      |((P.filter (fun n => n % (p * p') = r)).card : ℝ) - P.card / ((p * p' : ℕ) : ℝ)| ≤ 2)
    (i i' : ι) :
    |pairCount P ρ p i p' i' - P.card / ((p : ℝ) * p')| ≤ 2 := by
  unfold pairCount
  rw [filter_dvd_add_and_eq P hp hp' hcop]
  have := heq (Nat.chineseRemainder hcop ((p - 1) * ρ i) ((p' - 1) * ρ i') : ℕ)
    (Nat.chineseRemainder_lt_mul hcop _ _ hp.ne' hp'.ne')
  push_cast at this
  exact this

lemma sum_sq_le_sq_sum_abs (c : ι → ℝ) : ∑ i, c i ^ 2 ≤ (∑ i, |c i|) ^ 2 := by
  have := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |c i|)
    (fun i _ => abs_nonneg _)
  simpa [sq_abs] using this

/-! ### The signed L² estimate -/

/-- **The medium-prime second moment.**  For a sample `P` equidistributed (deviation `2`) in
every residue class of every `Good` modulus, a set `S` of pairwise coprime primes with `Good p`
and `Good (pp')`, shifts separated modulo each `p ∈ S`, and coefficients with `∑ c_i = 0`:

  `∑_{n∈P} (∑_{p∈S} ∑_i c_i 1[p ∣ n+ρ_i])² ≤ |P| (∑_{p∈S} 1/p)(∑ c_i²) + 2|S|²(∑|c_i|)²`.

The `p ≠ p'` main terms vanish by `∑ c_i = 0`; the `p = p'` cross terms vanish by separation. -/
theorem sum_sq_block_le [DecidableEq ι] (P S : Finset ℕ) (c : ι → ℝ) (ρ : ι → ℕ) (Good : ℕ → Prop)
    (hc0 : ∑ i, c i = 0)
    (hS : ∀ p ∈ S, 0 < p)
    (hcop : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.Coprime p')
    (hgood1 : ∀ p ∈ S, Good p) (hgood2 : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → Good (p * p'))
    (hsep : ∀ p ∈ S, ∀ n, ∀ i i', p ∣ n + ρ i → p ∣ n + ρ i' → i = i')
    (heq : ∀ q, Good q → ∀ r < q,
      |((P.filter (fun n => n % q = r)).card : ℝ) - P.card / q| ≤ 2) :
    ∑ n ∈ P, (∑ p ∈ S, ∑ i, c i * ind p (n + ρ i)) ^ 2
      ≤ P.card * (∑ p ∈ S, (p : ℝ)⁻¹) * (∑ i, c i ^ 2)
        + 2 * (S.card : ℝ) ^ 2 * (∑ i, |c i|) ^ 2 := by
  rw [sum_sq_block_eq]
  have hsq := sum_sq_le_sq_sum_abs c
  have hpair : ∀ p ∈ S, ∀ p' ∈ S, ∑ i, ∑ i', c i * c i' * pairCount P ρ p i p' i'
      ≤ (if p = p' then (P.card : ℝ) * (p : ℝ)⁻¹ * ∑ i, c i ^ 2 else 0)
        + 2 * (∑ i, |c i|) ^ 2 := by
    intro p hp p' hp'
    by_cases hpp : p = p'
    · subst hpp
      rw [if_pos rfl]
      have hdiag : ∀ i, ∑ i', c i * c i' * pairCount P ρ p i p i'
          = c i ^ 2 * pairCount P ρ p i p i := by
        intro i
        rw [Finset.sum_eq_single i]
        · ring
        · intro i' _ hne
          rw [pairCount_diag_eq_zero P ρ p (hsep p hp) (Ne.symm hne)]; ring
        · intro h; exact absurd (Finset.mem_univ i) h
      simp_rw [hdiag]
      have hle : ∀ i, c i ^ 2 * pairCount P ρ p i p i ≤ c i ^ 2 * (P.card / p + 2) := fun i =>
        mul_le_mul_of_nonneg_left (pairCount_diag_le P ρ (hS p hp) (heq p (hgood1 p hp)) i)
          (sq_nonneg _)
      calc ∑ i, c i ^ 2 * pairCount P ρ p i p i
          ≤ ∑ i, c i ^ 2 * (P.card / p + 2) := Finset.sum_le_sum fun i _ => hle i
        _ = (P.card : ℝ) * (p : ℝ)⁻¹ * ∑ i, c i ^ 2 + 2 * ∑ i, c i ^ 2 := by
            rw [← Finset.sum_mul]; ring
        _ ≤ (P.card : ℝ) * (p : ℝ)⁻¹ * ∑ i, c i ^ 2 + 2 * (∑ i, |c i|) ^ 2 := by
            gcongr
    · rw [if_neg hpp, zero_add]
      have hsplit : ∑ i, ∑ i', c i * c i' * pairCount P ρ p i p' i'
          = ∑ i, ∑ i', c i * c i' * (P.card / ((p : ℝ) * p'))
            + ∑ i, ∑ i', c i * c i' * (pairCount P ρ p i p' i' - P.card / ((p : ℝ) * p')) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i' _ => ?_
        ring
      have hebd : ∀ i i', |pairCount P ρ p i p' i' - P.card / ((p : ℝ) * p')| ≤ 2 := fun i i' =>
        abs_pairCount_sub_le P ρ (hS p hp) (hS p' hp') (hcop p hp p' hp' hpp)
          (heq _ (hgood2 p hp p' hp' hpp)) i i'
      rw [hsplit]
      have hmain : ∑ i, ∑ i', c i * c i' * (P.card / ((p : ℝ) * p')) = 0 := by
        have : ∑ i, ∑ i', c i * c i' * (P.card / ((p : ℝ) * p'))
            = (∑ i, c i) * (∑ i', c i') * (P.card / ((p : ℝ) * p')) := by
          rw [Finset.sum_mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
        rw [this, hc0]; ring
      rw [hmain, zero_add]
      calc ∑ i, ∑ i', c i * c i' * (pairCount P ρ p i p' i' - P.card / ((p : ℝ) * p'))
          ≤ |∑ i, ∑ i', c i * c i' * (pairCount P ρ p i p' i' - P.card / ((p : ℝ) * p'))| :=
            le_abs_self _
        _ ≤ ∑ i, ∑ i', |c i| * |c i'| * 2 := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i' _ => ?_)
            rw [abs_mul, abs_mul]
            exact mul_le_mul_of_nonneg_left (hebd i i') (by positivity)
        _ = 2 * (∑ i, |c i|) ^ 2 := by
            rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i' _ => ?_
            ring
  calc ∑ p ∈ S, ∑ p' ∈ S, ∑ i, ∑ i', c i * c i' * pairCount P ρ p i p' i'
      ≤ ∑ p ∈ S, ∑ p' ∈ S, ((if p = p' then (P.card : ℝ) * (p : ℝ)⁻¹ * ∑ i, c i ^ 2 else 0)
          + 2 * (∑ i, |c i|) ^ 2) :=
        Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun p' hp' => hpair p hp p' hp'
    _ = ∑ p ∈ S, ((P.card : ℝ) * (p : ℝ)⁻¹ * ∑ i, c i ^ 2 + S.card * (2 * (∑ i, |c i|) ^ 2)) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          Finset.sum_ite_eq S p (fun _ => (P.card : ℝ) * (p : ℝ)⁻¹ * ∑ i, c i ^ 2), if_pos hp]
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul,
          ← Finset.mul_sum]
        ring

/-! ### From the second moment to the first -/

/-- Cauchy–Schwarz on the sample: the mean of `|T|` is at most the root of the mean of `T²`. -/
lemma sampleAvg_abs_le_sqrt (P : Finset ℕ) (T : ℕ → ℝ) :
    (P.card : ℝ)⁻¹ * ∑ n ∈ P, |T n|
      ≤ Real.sqrt ((P.card : ℝ)⁻¹ * ∑ n ∈ P, T n ^ 2) := by
  rcases P.eq_empty_or_nonempty with hP | hP
  · subst hP; simp
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  refine Real.le_sqrt_of_sq_le ?_
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq P (fun _ => (1 : ℝ)) (fun n => |T n|)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] at hcs
  rw [mul_pow, inv_pow, sq, mul_inv]
  calc (P.card : ℝ)⁻¹ * (P.card : ℝ)⁻¹ * (∑ n ∈ P, |T n|) ^ 2
      ≤ (P.card : ℝ)⁻¹ * (P.card : ℝ)⁻¹ * ((P.card : ℝ) * ∑ n ∈ P, T n ^ 2) := by
        gcongr
    _ = (P.card : ℝ)⁻¹ * ∑ n ∈ P, T n ^ 2 := by field_simp

end Abstract

/-! ### The medium / very-large split of the large-prime count -/

/-- The medium primes: `R < p ≤ Y`, prime to `P₀`. -/
def medPrimes (R Y P₀ : ℕ) : Finset ℕ := (Y + 1).primesBelow.filter (fun p => ¬ p ∣ P₀ ∧ R < p)

lemma mem_medPrimes {R Y P₀ p : ℕ} :
    p ∈ medPrimes R Y P₀ ↔ p.Prime ∧ R < p ∧ p ≤ Y ∧ ¬ p ∣ P₀ := by
  unfold medPrimes
  rw [Finset.mem_filter, Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h2, h4, by omega, h3⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨by omega, h1⟩, h4, h2⟩

lemma medPrimes_prime {R Y P₀ p : ℕ} (hp : p ∈ medPrimes R Y P₀) : p.Prime :=
  (mem_medPrimes.1 hp).1

lemma medPrimes_not_dvd {R Y P₀ p : ℕ} (hp : p ∈ medPrimes R Y P₀) : ¬ p ∣ P₀ :=
  (mem_medPrimes.1 hp).2.2.2

lemma card_medPrimes_le (R Y P₀ : ℕ) : (medPrimes R Y P₀).card ≤ Y := by
  calc (medPrimes R Y P₀).card ≤ (Y + 1).primesBelow.card := Finset.card_filter_le _ _
    _ ≤ ((Finset.range (Y + 1)).filter (fun p => p ≠ 0)).card := by
        refine Finset.card_le_card fun p hp => ?_
        rw [Nat.mem_primesBelow] at hp
        exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hp.1, hp.2.ne_zero⟩
    _ = Y := by
        rw [Finset.range_eq_Ico, Finset.filter_ne', Finset.card_erase_of_mem (by simp)]
        simp

/-- The very-large-prime count: prime factors above `Y`, prime to `P₀`. -/
def omegaVL (Y P₀ m : ℕ) : ℕ := (m.primeFactors.filter (fun p => ¬ p ∣ P₀ ∧ Y < p)).card

lemma omegaOn_medPrimes_eq {R Y P₀ m : ℕ} (hm : m ≠ 0) :
    omegaOn (medPrimes R Y P₀) m
      = (m.primeFactors.filter (fun p => ¬ p ∣ P₀ ∧ R < p ∧ p ≤ Y)).card := by
  classical
  unfold omegaOn
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors, mem_medPrimes]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩; exact ⟨⟨h1, h5, hm⟩, h4, h2, h3⟩
  · rintro ⟨⟨h1, h2, -⟩, h3, h4, h5⟩; exact ⟨⟨h1, h4, h5, h3⟩, h2⟩

/-- **The medium / very-large split**: `ω_{>R}(m) = ω_{R<p≤Y}(m) + ω_{>Y}(m)` when `R ≤ Y`. -/
theorem omegaBig_split {R Y P₀ m : ℕ} (hRY : R ≤ Y) (hm : m ≠ 0) :
    omegaBig R P₀ m = omegaOn (medPrimes R Y P₀) m + omegaVL Y P₀ m := by
  classical
  rw [omegaOn_medPrimes_eq hm]
  unfold omegaBig omegaVL
  rw [← Finset.card_filter_add_card_filter_not
    (s := m.primeFactors.filter (fun p => ¬ p ∣ P₀ ∧ R < p)) (p := fun p => p ≤ Y)]
  congr 1
  · congr 1
    ext p
    simp only [Finset.mem_filter]
    tauto
  · congr 1
    ext p
    simp only [Finset.mem_filter, not_le]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨h1, h2, h4⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2, by omega⟩, h3⟩

/-! ### The block as an indicator sum -/

/-- The row coefficients `c_{(α,jj)} = A_{aα} / 4^{layer jj}`. -/
noncomputable def rowCoeff (G : GridParams) (a : Fin G.K → Fin G.s) (i : G.Idx) : ℝ :=
  ((kronPow G.K (diffZ G.s) a i.1 : ℤ) : ℝ) / (4 : ℝ) ^ layer G.K i.2

lemma omegaOn_eq_sum_ind (S : Finset ℕ) (m : ℕ) : (omegaOn S m : ℝ) = ∑ p ∈ S, ind p m := by
  unfold omegaOn ind
  rw [Finset.natCast_card_filter]

/-- `blockSum G ω_S n a = ∑_{p∈S} ∑_i c_i 1[p ∣ n + ρ_i]`. -/
lemma blockSum_omegaOn_eq (G : GridParams) (S : Finset ℕ) (n : ℕ) (a : Fin G.K → Fin G.s) :
    blockSum G (fun m => (omegaOn S m : ℝ)) n a
      = ∑ p ∈ S, ∑ i : G.Idx, rowCoeff G a i * ind p (n + shiftAL G.B G.Q G.D₀ i) := by
  have hL : blockSum G (fun m => (omegaOn S m : ℝ)) n a
      = ∑ i : G.Idx, rowCoeff G a i * (omegaOn S (n + shiftAL G.B G.Q G.D₀ i) : ℝ) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun jj _ => ?_
    show ((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ) *
        ((omegaOn S (n + shiftAL G.B G.Q G.D₀ (α, jj)) : ℝ) / (4 : ℝ) ^ layer G.K jj)
      = ((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ) / (4 : ℝ) ^ layer G.K jj
        * (omegaOn S (n + shiftAL G.B G.Q G.D₀ (α, jj)) : ℝ)
    ring
  rw [hL, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [omegaOn_eq_sum_ind, Finset.mul_sum]

/-! ### The row budgets -/

lemma sum_rowCoeff_eq_zero (G : GridParams) (hK : 0 < G.K) (a : Fin G.K → Fin G.s) :
    ∑ i : G.Idx, rowCoeff G a i = 0 := by
  unfold rowCoeff
  rw [Fintype.sum_prod_type]
  have h : ∑ α : G.Atom, ∑ jj : Fin G.N,
      ((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ) / (4 : ℝ) ^ layer G.K jj
      = (∑ α : G.Atom, ((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ))
          * ∑ jj : Fin G.N, (1 : ℝ) / (4 : ℝ) ^ layer G.K jj := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun jj _ => ?_
    ring
  rw [h, sum_kronPow_diffZ_eq_zero hK, zero_mul]

lemma sum_sq_rowCoeff_le (G : GridParams) (a : Fin G.K → Fin G.s) :
    ∑ i : G.Idx, rowCoeff G a i ^ 2 ≤ (1 / 8 : ℝ) ^ G.K / 15 := by
  unfold rowCoeff
  rw [Fintype.sum_prod_type]
  have h : ∀ α : G.Atom, ∀ jj : Fin G.N,
      (((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ) / (4 : ℝ) ^ layer G.K jj) ^ 2
        = ((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ) ^ 2 * ((1 : ℝ) / (4 : ℝ) ^ layer G.K jj) ^ 2 := by
    intro α jj; ring
  simp_rw [h]
  rw [← Finset.sum_mul_sum, sum_sq_kronPow_diffZ]
  calc (2 : ℝ) ^ G.K * ∑ jj : Fin G.N, ((1 : ℝ) / (4 : ℝ) ^ layer G.K jj) ^ 2
      ≤ (2 : ℝ) ^ G.K * ((1 / 16 : ℝ) ^ G.K / 15) :=
        mul_le_mul_of_nonneg_left (sum_layer_inv_sq_le G.K G.N) (by positivity)
    _ = (1 / 8 : ℝ) ^ G.K / 15 := by
        rw [← mul_div_assoc, ← mul_pow]; norm_num

lemma sum_abs_rowCoeff_le (G : GridParams) (a : Fin G.K → Fin G.s) :
    ∑ i : G.Idx, |rowCoeff G a i| ≤ (1 / 2 : ℝ) ^ G.K / 3 := by
  unfold rowCoeff
  rw [Fintype.sum_prod_type]
  have h : ∀ α : G.Atom, ∀ jj : Fin G.N,
      |((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ) / (4 : ℝ) ^ layer G.K jj|
        = |((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ)| * ((1 : ℝ) / (4 : ℝ) ^ layer G.K jj) := by
    intro α jj
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (4 : ℝ) ^ layer G.K jj)]
    ring
  simp_rw [h]
  rw [← Finset.sum_mul_sum, sum_abs_kronPow_diffZ]
  calc (2 : ℝ) ^ G.K * ∑ jj : Fin G.N, ((1 : ℝ) / (4 : ℝ) ^ layer G.K jj)
      ≤ (2 : ℝ) ^ G.K * ((1 / 4 : ℝ) ^ G.K / 3) :=
        mul_le_mul_of_nonneg_left (sum_layer_inv_le G.K G.N) (by positivity)
    _ = (1 / 2 : ℝ) ^ G.K / 3 := by
        rw [← mul_div_assoc, ← mul_pow]; norm_num

/-! ### Separation and equidistribution on the concrete progression -/

/-- A good prime separates the shifts: `p ∣ n+ρ_i` and `p ∣ n+ρ_{i'}` force `i = i'`. -/
lemma sep_of_goodPrime {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : ι → ℕ) {p : ℕ}
    (hp : 0 < p) (hg : GoodPrime ρ p) :
    ∀ n, ∀ i i', p ∣ n + ρ i → p ∣ n + ρ i' → i = i' := by
  intro n i i' h1 h2
  rw [dvd_add_iff_mod_eq_root hp] at h1 h2
  exact hg (h1.symm.trans h2)

/-- The AP sample is equidistributed (deviation `2`) modulo every `q` coprime to `P₀`. -/
lemma apSample_equidistributed (G : GridParams) (X : ℕ) :
    ∀ q : ℕ, (0 < q ∧ q.Coprime G.P₀) → ∀ r < q,
      |(((apSample X G.P₀ G.b₀).filter (fun n => n % q = r)).card : ℝ)
        - (apSample X G.P₀ G.b₀).card / q| ≤ 2 := by
  rintro q ⟨hq, hcop⟩ r hr
  exact abs_card_filter_apSample_sub_le X G.P₀ G.b₀ q G.P₀_pos hq hcop.symm G.b₀_lt_P₀ r
    (Finset.mem_range.2 hr)

/-- **The medium-prime second moment on the concrete grid.** -/
theorem sum_sq_blockSum_med_le (G : GridParams) (X R Y : ℕ) (hK : 0 < G.K)
    (a : Fin G.K → Fin G.s) :
    ∑ n ∈ apSample X G.P₀ G.b₀,
        blockSum G (fun m => (omegaOn (medPrimes R Y G.P₀) m : ℝ)) n a ^ 2
      ≤ (apSample X G.P₀ G.b₀).card * (∑ p ∈ medPrimes R Y G.P₀, (p : ℝ)⁻¹)
          * ((1 / 8 : ℝ) ^ G.K / 15)
        + 2 * ((medPrimes R Y G.P₀).card : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ G.K / 3) ^ 2 := by
  simp_rw [blockSum_omegaOn_eq]
  have hmain := sum_sq_block_le (apSample X G.P₀ G.b₀) (medPrimes R Y G.P₀) (rowCoeff G a)
    (shiftAL G.B G.Q G.D₀) (fun q => 0 < q ∧ q.Coprime G.P₀)
    (sum_rowCoeff_eq_zero G hK a)
    (fun p hp => (medPrimes_prime hp).pos)
    (fun p hp p' hp' hne => (Nat.coprime_primes (medPrimes_prime hp) (medPrimes_prime hp')).2 hne)
    (fun p hp => ⟨(medPrimes_prime hp).pos,
      (Nat.Prime.coprime_iff_not_dvd (medPrimes_prime hp)).2 (medPrimes_not_dvd hp)⟩)
    (fun p hp p' hp' _ => ⟨Nat.mul_pos (medPrimes_prime hp).pos (medPrimes_prime hp').pos,
      Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd (medPrimes_prime hp)).2 (medPrimes_not_dvd hp))
        ((Nat.Prime.coprime_iff_not_dvd (medPrimes_prime hp')).2 (medPrimes_not_dvd hp'))⟩)
    (fun p hp => sep_of_goodPrime _ (medPrimes_prime hp).pos
      (G.goodPrime_of_not_dvd_P₀ (medPrimes_prime hp) (medPrimes_not_dvd hp)))
    (apSample_equidistributed G X)
  refine hmain.trans ?_
  have h1 := sum_sq_rowCoeff_le G a
  have h2 := sum_abs_rowCoeff_le G a
  have h2' : 0 ≤ ∑ i : G.Idx, |rowCoeff G a i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hinv : 0 ≤ ∑ p ∈ medPrimes R Y G.P₀, (p : ℝ)⁻¹ := Finset.sum_nonneg fun p _ => by positivity
  gcongr


/-! ### The very-large primes: a pointwise logarithmic count -/

/-- Prime factors above `Y` are few: `#{p ∣ m : p > Y} · log Y ≤ log m`. -/
lemma card_filter_gt_mul_log_le {Y m : ℕ} (hY : 0 < Y) (hm : 0 < m) (S : Finset ℕ)
    (hS : S ⊆ m.primeFactors) (hYS : ∀ p ∈ S, Y < p) :
    (S.card : ℝ) * Real.log Y ≤ Real.log m := by
  have hdvd : ∏ p ∈ S, p ∣ m :=
    (Finset.prod_dvd_prod_of_subset S m.primeFactors (fun p => p) hS).trans
      (Nat.prod_primeFactors_dvd m)
  have hle : ∏ p ∈ S, p ≤ m := Nat.le_of_dvd hm hdvd
  have hpow : Y ^ S.card ≤ ∏ p ∈ S, p := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod' fun p hp => (hYS p hp).le
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  have h1 : ((Y ^ S.card : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hpow.trans hle
  push_cast at h1
  have h2 := Real.log_le_log (by positivity) h1
  rwa [Real.log_pow] at h2

/-- `ω_{>Y}(m) ≤ log m / log Y`. -/
lemma omegaVL_le {Y P₀ m : ℕ} (hY : 1 < Y) (hm : 0 < m) :
    (omegaVL Y P₀ m : ℝ) ≤ Real.log m / Real.log Y := by
  have hlog : 0 < Real.log Y := Real.log_pos (by exact_mod_cast hY)
  rw [le_div_iff₀ hlog]
  exact card_filter_gt_mul_log_le (by omega) hm _ (Finset.filter_subset _ _)
    (fun p hp => (Finset.mem_filter.1 hp).2.2)

/-- **The very-large-prime block, pointwise.**  If every retained argument is at most `Mx`, the
`p > Y` block of any row is at most `(log Mx / log Y) · 2^{−K}/3`. -/
theorem abs_blockSum_omegaVL_le (G : GridParams) {Y : ℕ} (hY : 1 < Y) {Mx : ℝ} (hMx1 : 1 ≤ Mx)
    {n : ℕ} (hMx : ∀ i : G.Idx, ((n + shiftAL G.B G.Q G.D₀ i : ℕ) : ℝ) ≤ Mx)
    (a : Fin G.K → Fin G.s) :
    |blockSum G (fun m => (omegaVL Y G.P₀ m : ℝ)) n a|
      ≤ (Real.log Mx / Real.log Y) * (1 / 2 : ℝ) ^ G.K / 3 := by
  have hlog : 0 < Real.log Y := Real.log_pos (by exact_mod_cast hY)
  have hC : 0 ≤ Real.log Mx / Real.log Y := div_nonneg (Real.log_nonneg hMx1) hlog.le
  refine abs_blockSum_le G hC n a fun α jj => ?_
  rw [abs_of_nonneg (by positivity)]
  have hpos : 0 < n + shiftAL G.B G.Q G.D₀ (α, jj) := by have := shiftAL_pos G (α, jj); omega
  refine (omegaVL_le hY hpos).trans ?_
  refine div_le_div_of_nonneg_right ?_ hlog.le
  exact Real.log_le_log (by exact_mod_cast hpos) (hMx (α, jj))

/-! ### `bigAvg`, split at `Y` -/

lemma avg_le_of_forall_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i ∈ s, f i ≤ b) : (s.card : ℝ)⁻¹ * ∑ i ∈ s, f i ≤ b := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs; simp [hb]
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  calc (s.card : ℝ)⁻¹ * ∑ i ∈ s, f i
      ≤ (s.card : ℝ)⁻¹ * ∑ i ∈ s, b :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum h) (by positivity)
    _ = b := by rw [Finset.sum_const, nsmul_eq_mul]; field_simp

/-- The medium-prime budget of one row, before the square root:
`(∑_{R<p≤Y, p∤P₀} 1/p) · 8^{−K}/15 + 2 |med|² (2^{−K}/3)² / |P|`. -/
noncomputable def medBudget (G : GridParams) (X R Y : ℕ) : ℝ :=
  (∑ p ∈ medPrimes R Y G.P₀, (p : ℝ)⁻¹) * ((1 / 8 : ℝ) ^ G.K / 15)
    + 2 * ((medPrimes R Y G.P₀).card : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ G.K / 3) ^ 2
        / (apSample X G.P₀ G.b₀).card

lemma medBudget_nonneg (G : GridParams) (X R Y : ℕ) : 0 ≤ medBudget G X R Y := by
  unfold medBudget
  have : 0 ≤ ∑ p ∈ medPrimes R Y G.P₀, (p : ℝ)⁻¹ := Finset.sum_nonneg fun p _ => by positivity
  positivity

/-- **The medium-prime first moment**: the sample mean of `|block_{R<p≤Y}|` is at most
`√(medBudget)`. -/
theorem sampleAvg_abs_blockSum_med_le (G : GridParams) (X R Y : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (hK : 0 < G.K) (a : Fin G.K → Fin G.s) :
    ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
        |blockSum G (fun m => (omegaOn (medPrimes R Y G.P₀) m : ℝ)) n a|
      ≤ Real.sqrt (medBudget G X R Y) := by
  refine (sampleAvg_abs_le_sqrt _ _).trans (Real.sqrt_le_sqrt ?_)
  have hc : (0 : ℝ) < (apSample X G.P₀ G.b₀).card := by exact_mod_cast hne.card_pos
  have h := sum_sq_blockSum_med_le G X R Y hK a
  unfold medBudget
  calc ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
        blockSum G (fun m => (omegaOn (medPrimes R Y G.P₀) m : ℝ)) n a ^ 2
      ≤ ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ *
          ((apSample X G.P₀ G.b₀).card * (∑ p ∈ medPrimes R Y G.P₀, (p : ℝ)⁻¹)
              * ((1 / 8 : ℝ) ^ G.K / 15)
            + 2 * ((medPrimes R Y G.P₀).card : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ G.K / 3) ^ 2) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp

/-- **`bigAvg`, split at `Y` (brief §4D).**  The large-prime block average is at most the
medium-range L² bound `√(medBudget)` plus the very-large-range pointwise bound
`(log Mx / log Y) · 2^{−K}/3`, where `Mx` bounds every retained argument `n + ρ_i` on the
sample.  No pointwise bound is applied to the medium range. -/
theorem bigAvg_le (G : GridParams) (X R Y : ℕ) (hne : (apSample X G.P₀ G.b₀).Nonempty)
    (hK : 0 < G.K) (hRY : R ≤ Y) (hY : 1 < Y) {Mx : ℝ} (hMx1 : 1 ≤ Mx)
    (hMx : ∀ n ∈ apSample X G.P₀ G.b₀, ∀ i : G.Idx,
      ((n + shiftAL G.B G.Q G.D₀ i : ℕ) : ℝ) ≤ Mx) :
    bigAvg G X R
      ≤ Real.sqrt (medBudget G X R Y) + (Real.log Mx / Real.log Y) * (1 / 2 : ℝ) ^ G.K / 3 := by
  set P := apSample X G.P₀ G.b₀ with hP
  set wmed : ℕ → ℝ := fun m => (omegaOn (medPrimes R Y G.P₀) m : ℝ) with hwmed
  set wvl : ℕ → ℝ := fun m => (omegaVL Y G.P₀ m : ℝ) with hwvl
  have hlog : 0 < Real.log Y := Real.log_pos (by exact_mod_cast hY)
  have hC : 0 ≤ (Real.log Mx / Real.log Y) * (1 / 2 : ℝ) ^ G.K / 3 := by
    have := Real.log_nonneg hMx1; positivity
  have hsplit : ∀ n ∈ P, ∀ ν : Fin G.rDim,
      |blockSum G (fun m => (omegaBig R G.P₀ m : ℝ)) n (G.rowEquiv.symm ν)|
        ≤ |blockSum G wmed n (G.rowEquiv.symm ν)| + |blockSum G wvl n (G.rowEquiv.symm ν)| := by
    intro n _ ν
    have h : blockSum G (fun m => (omegaBig R G.P₀ m : ℝ)) n (G.rowEquiv.symm ν)
        = blockSum G wmed n (G.rowEquiv.symm ν) + blockSum G wvl n (G.rowEquiv.symm ν) := by
      rw [← blockSum_add]
      refine blockSum_congr G _ fun α jj => ?_
      have hpos := shiftAL_pos G (α, jj)
      simp only [hwmed, hwvl]
      rw [omegaBig_split hRY (by omega)]
      push_cast; ring
    rw [h]; exact abs_add_le _ _
  unfold bigAvg
  rw [← hP]
  calc (P.card : ℝ)⁻¹ * ∑ n ∈ P, (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
        |blockSum G (fun m => (omegaBig R G.P₀ m : ℝ)) n (G.rowEquiv.symm ν)|
      ≤ (P.card : ℝ)⁻¹ * ∑ n ∈ P, (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
          (|blockSum G wmed n (G.rowEquiv.symm ν)| + |blockSum G wvl n (G.rowEquiv.symm ν)|) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn =>
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ν _ => hsplit n hn ν) (by positivity))
          (by positivity)
    _ = (P.card : ℝ)⁻¹ * ∑ n ∈ P, (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
            |blockSum G wmed n (G.rowEquiv.symm ν)|
        + (P.card : ℝ)⁻¹ * ∑ n ∈ P, (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
            |blockSum G wvl n (G.rowEquiv.symm ν)| := by
        simp_rw [Finset.sum_add_distrib, mul_add]
        rw [Finset.sum_add_distrib, mul_add]
    _ ≤ Real.sqrt (medBudget G X R Y)
        + (Real.log Mx / Real.log Y) * (1 / 2 : ℝ) ^ G.K / 3 := by
        refine add_le_add ?_ ?_
        · have hswap : (P.card : ℝ)⁻¹ * ∑ n ∈ P, (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
                |blockSum G wmed n (G.rowEquiv.symm ν)|
              = (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim, (P.card : ℝ)⁻¹ * ∑ n ∈ P,
                |blockSum G wmed n (G.rowEquiv.symm ν)| := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun n _ => ?_
            ring
          rw [hswap]
          have hr : ((Finset.univ : Finset (Fin G.rDim)).card : ℝ) = G.rDim := by simp
          rw [← hr]
          refine avg_le_of_forall_le _ _ (Real.sqrt_nonneg _) fun ν _ => ?_
          exact sampleAvg_abs_blockSum_med_le G X R Y hne hK _
        · refine avg_le_of_forall_le _ _ hC fun n hn => ?_
          have hr : ((Finset.univ : Finset (Fin G.rDim)).card : ℝ) = G.rDim := by simp
          rw [← hr]
          refine avg_le_of_forall_le _ _ hC fun ν _ => ?_
          exact abs_blockSum_omegaVL_le G hY hMx1 (hMx n hn) _

end NormalNumbers.G4
