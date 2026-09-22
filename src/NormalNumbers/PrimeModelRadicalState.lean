/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PrimeModelRadicalTail
import NormalNumbers.PrimeModelRadicalCRT

/-!
# Radical states: identification with the arithmetic sifted condition, and retained counting

This file bridges the *abstract* finite radical model of `PrimeModelRadical` (a product law on
state tuples `ι → Option (Fin k)`) with the *arithmetic* sifted condition of
`PrimeModelRadicalCRT` (`Radical.SiftedCond`), and proves the cardinality bound on the retained
box that the tail estimate needs on the counting side.

## Main results

* `retainedBox_card_le` — `#(retainedBox k p T) ≤ ⌊T⌋₊ ^ k` for injective prime-valued `p`.
  The proof sends a state to its tuple of natural radical sizes `(d_j(s))_{j < k}`, shows that
  map is injective by unique factorisation (`p i ∣ d_j(s) ↔ s i = some j`), and lands the image
  in `(Icc 1 ⌊T⌋₊)^k`.  The bound is independent of `#ι` — the trivial bound `(k+1)^{#ι}` is
  useless for the tail.
* `actual_state_sifted_iff` — the state read off arithmetically at `n` (the unique shift `t < k`
  with `p ∣ n + t + 1`, if any) equals a prescribed state `s`, together with `n % Q = r`, exactly
  when `SiftedCond k A U Q r j n` holds for the assigned set `A = stateA s`, the unassigned set
  `U = stateU s = P \ A` and the shift function `j = stateShift s`.
* `state_model_density` — the model weight of `s` is `(1 / ∏_{q ∈ A} q) * ∏_{q ∈ U} (1 - k/q)`,
  i.e. exactly the main-term density attached to `SiftedCond k A U Q r j`.

All shifts are `n + t + 1` throughout, matching `Radical.SiftedCond`; the permanent `decide`
examples at the end of the file pin that convention down.

No analytic hypothesis is used.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.RadicalState

open NormalNumbers.PrimeModel.Radical

/-! ## Part 1: the retained box is small -/

section Retained

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- The natural-number radical size: the product of the primes assigned to shift `j`. -/
def natRadSize (p : ι → ℕ) (j : Fin k) (s : ι → Option (Fin k)) : ℕ :=
  ∏ i, (if s i = some j then p i else 1)

lemma natRadSize_cast (p : ι → ℕ) (j : Fin k) (s : ι → Option (Fin k)) :
    (natRadSize p j s : ℝ) = radSize p j s := by
  rw [natRadSize, radSize, Nat.cast_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : s i = some j <;> simp [h]

lemma one_le_natRadSize {p : ι → ℕ} (hp : ∀ i, 1 ≤ p i) (j : Fin k) (s : ι → Option (Fin k)) :
    1 ≤ natRadSize p j s := by
  refine Finset.one_le_prod' fun i _ => ?_
  by_cases h : s i = some j <;> simp [h, hp i]

/-- **Unique factorisation, one site at a time.**  A prime `p i` divides the radical size at
shift `j` exactly when the state assigns site `i` to that shift. -/
lemma prime_dvd_natRadSize {p : ι → ℕ} (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (j : Fin k) (s : ι → Option (Fin k)) (i : ι) :
    p i ∣ natRadSize p j s ↔ s i = some j := by
  constructor
  · intro h
    rw [natRadSize, (hp i).prime.dvd_finsetProd_iff] at h
    obtain ⟨a, -, ha⟩ := h
    by_cases hsa : s a = some j
    · rw [if_pos hsa] at ha
      have : p i = p a := (Nat.prime_dvd_prime_iff_eq (hp i) (hp a)).mp ha
      rw [hinj this]; exact hsa
    · rw [if_neg hsa] at ha
      exact absurd (Nat.eq_one_of_dvd_one ha) (hp i).ne_one
  · intro h
    have := Finset.dvd_prod_of_mem (fun i => if s i = some j then p i else 1)
      (Finset.mem_univ i)
    rwa [if_pos h] at this

/-- The map sending a state to its tuple of radical sizes is injective. -/
lemma natRadTuple_injective {p : ι → ℕ} (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    Function.Injective (fun (s : ι → Option (Fin k)) => fun j : Fin k => natRadSize p j s) := by
  intro s s' h
  funext i
  have key : ∀ j : Fin k, s i = some j ↔ s' i = some j := by
    intro j
    rw [← prime_dvd_natRadSize hp hinj j s i, ← prime_dvd_natRadSize hp hinj j s' i,
      show natRadSize p j s = natRadSize p j s' from congrFun h j]
  cases hsi : s i with
  | none =>
      cases hsi' : s' i with
      | none => rfl
      | some j => exact absurd ((key j).mpr hsi') (by simp [hsi])
  | some j =>
      have := (key j).mp hsi
      rw [this]

/-- **Retained-box cardinality.**  At most `⌊T⌋₊ ^ k` states have all `k` radical sizes at
most `T`: the sizes form a `k`-tuple of naturals in `[1, ⌊T⌋₊]`, and the state is determined by
that tuple.  Crucially the bound does not involve the number of primes. -/
theorem retainedBox_card_le {p : ι → ℕ} (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (k : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    ((retainedBox k p T).card : ℝ) ≤ (Nat.floor T : ℝ) ^ k := by
  classical
  have hp1 : ∀ i, 1 ≤ p i := fun i => (hp i).one_lt.le.trans' (by norm_num)
  have himg : (retainedBox k p T).image (fun s => fun j : Fin k => natRadSize p j s)
      ⊆ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 (Nat.floor T)) := by
    intro f hf
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hf
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_Icc]
    refine ⟨one_le_natRadSize hp1 j s, ?_⟩
    refine Nat.le_floor ?_
    rw [natRadSize_cast]
    exact (mem_retainedBox.mp hs) j
  have hcard : (retainedBox k p T).card ≤ (Nat.floor T) ^ k := by
    have h2 := Finset.card_le_card himg
    rw [Finset.card_image_of_injective _ (natRadTuple_injective hp hinj)] at h2
    refine h2.trans (le_of_eq ?_)
    rw [Fintype.card_piFinset]
    simp
  exact_mod_cast hcard

end Retained

/-! ## Part 2: the arithmetic state and the sifted condition -/

section Arithmetic

variable {k : ℕ}

/-- The shift hit by `q` at `n`, if any: the unique `t < k` with `q ∣ n + t + 1`. -/
def hitShift (k q n : ℕ) : Option (Fin k) :=
  if h : ∃ t : Fin k, q ∣ n + t.val + 1 then some (Fin.find _ h) else none

/-- **Uniqueness of the hit shift.**  A prime (indeed any modulus) exceeding `k` divides at most
one of the `k` shifted values `n + t + 1`, `t < k`. -/
lemma hit_unique {q n : ℕ} (hq : k < q) {t t' : Fin k}
    (ht : q ∣ n + t.val + 1) (ht' : q ∣ n + t'.val + 1) : t = t' := by
  have h1 : q ∣ t'.val - t.val := by
    have hd := Nat.dvd_sub ht' ht
    rwa [show n + t'.val + 1 - (n + t.val + 1) = t'.val - t.val from by omega] at hd
  have h2 : q ∣ t.val - t'.val := by
    have hd := Nat.dvd_sub ht ht'
    rwa [show n + t.val + 1 - (n + t'.val + 1) = t.val - t'.val from by omega] at hd
  have l1 : t'.val - t.val < q := lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_lt_of_le t'.isLt hq.le)
  have l2 : t.val - t'.val < q := lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_lt_of_le t.isLt hq.le)
  have e1 := Nat.eq_zero_of_dvd_of_lt h1
  have e2 := Nat.eq_zero_of_dvd_of_lt h2
  exact Fin.ext (by omega)

lemma hitShift_eq_some_iff {q n : ℕ} (hq : k < q) (t : Fin k) :
    hitShift k q n = some t ↔ q ∣ n + t.val + 1 := by
  unfold hitShift
  constructor
  · intro h
    split at h
    · rename_i hex
      have hspec := Fin.find_spec (p := fun t : Fin k => q ∣ n + t.val + 1) hex
      have : Fin.find _ hex = t := by simpa using h
      rwa [this] at hspec
    · exact absurd h (by simp)
  · intro h
    have hex : ∃ t : Fin k, q ∣ n + t.val + 1 := ⟨t, h⟩
    rw [dif_pos hex]
    exact congrArg some
      (hit_unique hq (Fin.find_spec (p := fun t : Fin k => q ∣ n + t.val + 1) hex) h)

lemma hitShift_eq_none_iff {q n : ℕ} :
    hitShift k q n = none ↔ ∀ t : Fin k, ¬ q ∣ n + t.val + 1 := by
  unfold hitShift
  constructor
  · intro h t ht
    rw [dif_pos ⟨t, ht⟩] at h
    exact absurd h (by simp)
  · intro h
    rw [dif_neg (by rintro ⟨t, ht⟩; exact h t ht)]

variable (k) in
/-- The state actually realised by `n` at the primes of `P`. -/
def actualState (P : Finset ℕ) (n : ℕ) : {q // q ∈ P} → Option (Fin k) :=
  fun i => hitShift k (i : ℕ) n

/-! ### Assigned and unassigned primes of a state -/

variable (P : Finset ℕ) (s : {q // q ∈ P} → Option (Fin k))

/-- The primes of `P` that the state `s` assigns to some shift. -/
def stateA : Finset ℕ := (P.attach.filter fun i => (s i).isSome).image Subtype.val

/-- The primes of `P` that the state `s` leaves unassigned. -/
def stateU : Finset ℕ := (P.attach.filter fun i => ¬ (s i).isSome).image Subtype.val

variable {P s}

lemma mem_stateA {q : ℕ} : q ∈ stateA P s ↔ ∃ h : q ∈ P, (s ⟨q, h⟩).isSome := by
  simp [stateA, Finset.mem_image, Finset.mem_filter]

lemma mem_stateU {q : ℕ} : q ∈ stateU P s ↔ ∃ h : q ∈ P, ¬ (s ⟨q, h⟩).isSome := by
  simp [stateU, Finset.mem_image, Finset.mem_filter]

lemma stateA_subset : stateA P s ⊆ P := by
  intro q hq; obtain ⟨h, -⟩ := mem_stateA.mp hq; exact h

lemma stateU_subset : stateU P s ⊆ P := by
  intro q hq; obtain ⟨h, -⟩ := mem_stateU.mp hq; exact h

lemma stateA_disjoint_stateU : Disjoint (stateA P s) (stateU P s) := by
  rw [Finset.disjoint_left]
  intro q hA hU
  obtain ⟨h, h1⟩ := mem_stateA.mp hA
  obtain ⟨h', h2⟩ := mem_stateU.mp hU
  exact h2 h1

lemma stateU_eq_sdiff : stateU P s = P \ stateA P s := by
  ext q
  simp only [Finset.mem_sdiff, mem_stateU, mem_stateA]
  constructor
  · rintro ⟨h, hns⟩
    exact ⟨h, fun hc => (hc.elim fun h' hs => hns hs)⟩
  · rintro ⟨h, hns⟩
    exact ⟨h, fun hs => hns ⟨h, hs⟩⟩

lemma stateA_union_stateU : stateA P s ∪ stateU P s = P := by
  rw [stateU_eq_sdiff, Finset.union_sdiff_self_eq_union]
  exact Finset.union_eq_right.mpr stateA_subset |>.trans rfl

variable (P s) in
/-- The shift function prescribed by the state: the assigned shift at assigned primes, and the
(irrelevant) default `0` elsewhere. -/
def stateShift (hk : 0 < k) : ℕ → Fin k := fun q =>
  if h : q ∈ P then (s ⟨q, h⟩).getD ⟨0, hk⟩ else ⟨0, hk⟩

lemma stateShift_of_some {hk : 0 < k} {q : ℕ} (h : q ∈ P) {t : Fin k} (hs : s ⟨q, h⟩ = some t) :
    stateShift P s hk q = t := by
  simp [stateShift, h, hs]

/-- **State identification.**  Being in residue class `r` mod `Q` *and* realising exactly the
state `s` at the primes of `P` is the same as the arithmetic sifted condition with assigned set
`stateA s`, sieve set `stateU s = P \ stateA s` and shift function `stateShift s`. -/
theorem actual_state_sifted_iff (hk : 0 < k) (hP : ∀ q ∈ P, k < q) (Q r n : ℕ) :
    (n % Q = r ∧ actualState k P n = s)
      ↔ Radical.SiftedCond k (stateA P s) (stateU P s) Q r (stateShift P s hk) n := by
  constructor
  · rintro ⟨hr, hst⟩
    refine ⟨hr, ?_, ?_⟩
    · intro q hq
      obtain ⟨h, hsome⟩ := mem_stateA.mp hq
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hsome
      have hhit : hitShift k q n = some t := by
        rw [← ht, ← hst]; rfl
      rw [stateShift_of_some h ht]
      exact (hitShift_eq_some_iff (hP q h) t).mp hhit
    · intro q hq t
      obtain ⟨h, hnone⟩ := mem_stateU.mp hq
      have hsn : s ⟨q, h⟩ = none := by
        cases hh : s ⟨q, h⟩ with
        | none => rfl
        | some t => exact absurd (by simp [hh]) hnone
      have hhit : hitShift k q n = none := by
        rw [← hsn, ← hst]; rfl
      exact hitShift_eq_none_iff.mp hhit t
  · rintro ⟨hr, hA, hU⟩
    refine ⟨hr, ?_⟩
    funext i
    obtain ⟨q, hq⟩ := i
    show hitShift k q n = s ⟨q, hq⟩
    cases hs : s ⟨q, hq⟩ with
    | none =>
        rw [hitShift_eq_none_iff]
        have hmem : q ∈ stateU P s := mem_stateU.mpr ⟨hq, by simp [hs]⟩
        exact hU q hmem
    | some t =>
        have hmem : q ∈ stateA P s := mem_stateA.mpr ⟨hq, by simp [hs]⟩
        have := hA q hmem
        rw [stateShift_of_some hq hs] at this
        exact (hitShift_eq_some_iff (hP q hq) t).mpr this

/-! ### The model density of a state -/

/-- **State density.**  The radical-model weight of `s` is the density attached to the sifted
condition of `actual_state_sifted_iff`: one factor `1/q` per assigned prime and one factor
`1 - k/q` per unassigned prime. -/
theorem state_model_density :
    Radical.weight k (Radical.primeRecip (fun i : {q // q ∈ P} => (i : ℕ))) s
      = (1 / ∏ q ∈ stateA P s, (q : ℝ)) * ∏ q ∈ stateU P s, (1 - (k : ℝ) / q) := by
  classical
  have hval : Function.Injective (Subtype.val : {q // q ∈ P} → ℕ) := Subtype.val_injective
  have hsplit :
      (∏ i ∈ P.attach.filter (fun i => (s i).isSome),
          Radical.localWeight k (Radical.primeRecip (fun i : {q // q ∈ P} => (i : ℕ)) i) (s i)) *
      (∏ i ∈ P.attach.filter (fun i => ¬ (s i).isSome),
          Radical.localWeight k (Radical.primeRecip (fun i : {q // q ∈ P} => (i : ℕ)) i) (s i))
        = Radical.weight k (Radical.primeRecip (fun i : {q // q ∈ P} => (i : ℕ))) s := by
    rw [Radical.weight, Finset.prod_filter_mul_prod_filter_not]
    exact Finset.prod_congr (by simp [Finset.attach]) fun i _ => rfl
  rw [← hsplit]
  congr 1
  · rw [stateA, Finset.prod_image (fun a _ b _ h => hval h)]
    rw [one_div, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp hi).2
    simp [ht, Radical.primeRecip]
  · rw [stateU, Finset.prod_image (fun a _ b _ h => hval h)]
    refine Finset.prod_congr rfl fun i hi => ?_
    have : s i = none := by
      cases hh : s i with
      | none => rfl
      | some t => exact absurd (by simp [hh]) (Finset.mem_filter.mp hi).2
    simp [this, Radical.primeRecip, div_eq_mul_inv]

end Arithmetic

/-! ## Permanent convention anchors

`P = {3, 5}`, `k = 2`, shifts `n + t + 1` for `t ∈ {0, 1}`.  These catch an `n + t` versus
`n + t + 1` mismatch. -/

example : hitShift 2 3 0 = none := by decide
example : hitShift 2 5 0 = none := by decide
example : hitShift 2 3 1 = some 1 := by decide
example : hitShift 2 3 2 = some 0 := by decide
example : hitShift 2 5 3 = some 1 := by decide

/-! ## Axiom audit -/

#print axioms retainedBox_card_le
#print axioms actual_state_sifted_iff
#print axioms state_model_density

end NormalNumbers.PrimeModel.RadicalState
