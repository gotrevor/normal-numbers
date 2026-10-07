/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.NumberTheory.Padics.RingHoms
import NormalNumbers.LiteratureDigitsOfPowers

/-!
# Erdős #406 from gap-two triples of 3-adic Cantor translates

`/create` session 2026-10-06 on the digit family (`LiteratureDigitsOfPowers`).  Lagarias
(arXiv:math/0512006) and Abram–Bolshakov–Lagarias (arXiv:1308.3133, 1508.05967) study
`C(M₁, …, Mₖ) = ⋂ Mᵢ⁻¹ Σ`, `Σ` the 3-adic integers with digits in `{0, 1}`, and bound the
3-adic exceptional set `E(ℤ₃) = {λ : λ 2ⁿ ∈ Σ for infinitely many n}` by the supremum of
`dim C(1, 2^m₁, …)` over **all** exponent tuples.  That supremum stays at `log₃ φ ≈ 0.438`, and
the large values come from the multiplier `4 = 1 + 3` (`C(1, 4)` is the golden-mean shift).

**The move here (ask what the bad tuples have that the orbit can avoid).**  An infinite
exponent set always contains three members with both gaps as large as we like, so the small-gap
tuples, which carry the positive dimension, never have to be faced.  Gaps measured in powers of
`4` (the exponents of a nonzero orbit point all share a parity):

* `GapTwoTriples`: `C(1, 4ᵃ, 4ᵃ⁺ᵇ) = {0}` whenever `a, b ≥ 2`.
* `erdos406_of_gapTriplesEventually`: any eventual form of it gives Erdős #406, and
  `exceptionalSet_eq_zero_of_gapTriplesEventually` gives `E(ℤ₃) = {0}`, far stronger than
  Lagarias's Exceptional Set Conjecture (`dim E(ℤ₃) = 0`).
* Each instance is a finite automaton question (carries as states), decided exactly.  All 12 403
  triples with `a, b ≥ 2`, `a + b ≤ 160` are `{0}`; the largest reachable automaton has 388
  states (`experiments/erdos-triples/triple.py`).  Every nonzero triple found has `a = 1` or
  `b = 1`, and those are genuinely nonzero (`not_tripleTrivial_one_three`,
  `not_tripleTrivial_eight_one`), so the gap bound 2 is sharp on both sides.
* Calibration: `dim C(1, 4ᵃ)` for `a = 2..11` runs 0.438, 0.256, 0.278, 0.307, 0.215, 0.244,
  0.267, 0.2619, 0.2597, 0.2623, 0.2627, settling on `log₃(4/3) ≈ 0.2619`, the dimension of two
  independent copies of `Σ`.  Three independent copies have dimension `3 log₃ 2 − 2 < 0`, which is
  why gap-two triples are expected to die.

Difficulty check.  *Proved*: the wiring theorems below (elementary).  *Unproved premise*:
`GapTwoTriples` (or any eventual form).  *Mechanism*: none yet.  Each instance is decided by the
residues of `4ᵃ, 4ᵃ⁺ᵇ` modulo `3^D`, `D` the automaton's extinction depth, but `a` can sit
3-adically close to `1` (`a = 1 + 3ᴰ t`), where the automaton imitates the golden-mean one for
`D` levels.  A proof must control those imitators uniformly; the look-alike families
`a = 1 + 3ʲ` (`j ≤ 5`) and `b = 1 + 3ʲ` all die within 44 reachable states.
-/

namespace NormalNumbers.ErdosTriples

open NormalNumbers.Literature.DigitsOfPowers

/-! ## Finite prefixes -/

/-- The ternary digits of `n` in positions `0, …, d` are all `0` or `1`. -/
def LowZeroOne (d n : ℕ) : Prop := ∀ i ≤ d, n / 3 ^ i % 3 ≤ 1

instance (d n : ℕ) : Decidable (LowZeroOne d n) := by
  unfold LowZeroOne; infer_instance

/-- `C(1, M₁, …, Mₖ)` has a unit point to depth `d`: some `x < 3^(d+1)` with `x ≡ 1 (mod 3)`
such that `x` and every `Mᵢ x` have `0/1` digits in positions `0..d`.  A nonzero point of the
3-adic set can be shifted to a unit, so `C(1, M₁, …) ≠ {0}` iff this holds for every `d`
(König). -/
def Survives (Ms : List ℕ) (d : ℕ) : Prop :=
  ∃ x ∈ Finset.range (3 ^ (d + 1)), x % 3 = 1 ∧ LowZeroOne d x ∧ ∀ M ∈ Ms, LowZeroOne d (M * x)

instance (Ms : List ℕ) (d : ℕ) : Decidable (Survives Ms d) := by
  unfold Survives; infer_instance

/-- `C(1, 4ᵃ, 4ᵃ⁺ᵇ) = {0}`, witnessed by an extinction depth. -/
def TripleTrivial (a b : ℕ) : Prop := ∃ d, ¬ Survives [4 ^ a, 4 ^ (a + b)] d

/-- **Open node: gap-two triples are trivial.**  `C(1, 4ᵃ, 4ᵃ⁺ᵇ) = {0}` for all `a, b ≥ 2`.

Believed, confidence 75%.  Evidence: exact automaton decisions for all `a, b ≥ 2`, `a + b ≤ 160`
(`tripleTrivial_of_sum_le_160`), plus the 3-adic look-alikes of the exceptions.  Heuristic:
three independent copies of `Σ` have dimension `3 log₃ 2 − 2 < 0`, and for `a, b ≥ 2` the pair
dimensions are at most `0.307 < 1 − log₃ 2`, so the third constraint is subcritical.  The 25%
is the imitators `a ≡ 1 (mod 3ᴰ)`: infinitely many chances for a rare survivor. -/
def GapTwoTriples : Prop := ∀ a b, 2 ≤ a → 2 ≤ b → TripleTrivial a b

/-- The weakest form the wiring needs: gap-`A` triples are trivial for some `A`. -/
def GapTriplesEventually : Prop := ∃ A, ∀ a b, A ≤ a → A ≤ b → TripleTrivial a b

theorem gapTriplesEventually_of_gapTwoTriples (h : GapTwoTriples) : GapTriplesEventually :=
  ⟨2, fun a b ha hb => h a b ha hb⟩

/-! ## Instances and sharpness -/

/-- `C(1, 16, 256) = {0}`: no unit prefix survives two digits. -/
theorem tripleTrivial_two_two : TripleTrivial 2 2 := ⟨1, by decide⟩

/-- `C(1, 16, 512²) = {0}`. -/
theorem tripleTrivial_two_three : TripleTrivial 2 3 := ⟨2, by decide⟩

/-- `C(1, 64, 1024) = {0}`. -/
theorem tripleTrivial_three_two : TripleTrivial 3 2 := ⟨2, by decide⟩

/-- **Verified range.**  Every gap-two triple with `a + b ≤ 160` (12 403 triples) is trivial.

Believed, confidence 97%: exact decision by `experiments/erdos-triples/triple.py` (depth-first
search of the carry automaton from the state after digit `1`; a reachable cycle is a nonzero
point, an acyclic reachable graph is extinction).  The automaton search is cross-checked against
brute-force prefix enumeration in `experiments/erdos-triples/test_triple.py`.  Discharge: a Lean
version of the carry automaton with a soundness lemma, then `decide` per instance. -/
theorem tripleTrivial_of_sum_le_160 :
    ∀ a b, 2 ≤ a → 2 ≤ b → a + b ≤ 160 → TripleTrivial a b := by
  sorry

/-- Digits `0..d` only see the residue mod `3^(d+1)`. -/
theorem div_pow_mod_three_of_le {n i d : ℕ} (hi : i ≤ d) :
    n % 3 ^ (d + 1) / 3 ^ i % 3 = n / 3 ^ i % 3 := by
  have h : 3 ^ (d + 1) = 3 ^ i * 3 ^ (d + 1 - i) := by
    rw [← pow_add]; congr 1; omega
  rw [h, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact dvd_pow_self 3 (by omega)

theorem lowZeroOne_mod_iff {d n : ℕ} : LowZeroOne d (n % 3 ^ (d + 1)) ↔ LowZeroOne d n := by
  unfold LowZeroOne
  exact forall₂_congr fun i hi => by rw [div_pow_mod_three_of_le hi]

theorem lowZeroOne_mul_mod_iff {d M x : ℕ} :
    LowZeroOne d (M * (x % 3 ^ (d + 1))) ↔ LowZeroOne d (M * x) := by
  rw [← lowZeroOne_mod_iff, ← @lowZeroOne_mod_iff d (M * x), Nat.mul_mod, Nat.mod_mod,
    ← Nat.mul_mod]

/-- A number whose ternary digits are all `0/1` passes at every depth. -/
theorem lowZeroOne_of_two_not_mem {n : ℕ} (h : 2 ∉ Nat.digits 3 n) (d : ℕ) :
    LowZeroOne d n := by
  intro i _
  rw [← Nat.getD_digits n i (by norm_num)]
  rcases Nat.lt_or_ge i (Nat.digits 3 n).length with hl | hl
  · rw [List.getD_eq_getElem _ _ hl]
    have hm := List.getElem_mem hl
    have := Nat.digits_lt_base (by norm_num) hm
    have hne : (Nat.digits 3 n)[i] ≠ 2 := fun he => h (he ▸ hm)
    omega
  · rw [List.getD_eq_default _ _ hl]; omega

theorem lowZeroOne_one (d : ℕ) : LowZeroOne d 1 := by
  intro i _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · decide
  · rw [Nat.div_eq_of_lt (Nat.one_lt_pow hi.ne' (by norm_num))]; decide

/-- A number with all ternary digits `0/1` passes at every depth (helper for the witnesses). -/
theorem lowZeroOne_of_lt_pow {n k : ℕ} (hn : n < 3 ^ k) (h : ∀ i < k, n / 3 ^ i % 3 ≤ 1)
    (d : ℕ) : LowZeroOne d n := by
  intro i _
  by_cases hik : i < k
  · exact h i hik
  · rw [Nat.div_eq_of_lt (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    decide

/-- **`a = 1` is a real exception**: `1, 4, 256` all have digits `0/1`, so `C(1, 4, 4⁴) ∋ 1`.
This is Erdős's own `2⁰, 2², 2⁸`. -/
theorem not_tripleTrivial_one_three : ¬ TripleTrivial 1 3 := by
  rintro ⟨d, hd⟩
  refine hd ⟨1, Finset.mem_range.2 (Nat.one_lt_pow (Nat.succ_ne_zero d) (by norm_num)), rfl,
    lowZeroOne_one d, ?_⟩
  intro M hM
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
  rcases hM with rfl | rfl
  · exact lowZeroOne_of_lt_pow (k := 2) (by norm_num) (by decide) d
  · exact lowZeroOne_of_lt_pow (k := 6) (by norm_num) (by decide) d

/-- The gap-one witness at `a = 8`: `x = 282864854542` has `x`, `4⁸ x`, `4⁹ x` all with
ternary digits `0/1` (lengths 25, 35, 36). -/
theorem gapOne_witness :
    (∀ i < 25, 282864854542 / 3 ^ i % 3 ≤ 1) ∧
    (∀ i < 35, 4 ^ 8 * 282864854542 / 3 ^ i % 3 ≤ 1) ∧
    (∀ i < 36, 4 ^ 9 * 282864854542 / 3 ^ i % 3 ≤ 1) := by
  decide +kernel

/-- **`b = 1` is a real exception, even with `a` large**: `C(1, 4⁸, 4⁹)` contains the integer
`282864854542`.  So no gap-one version of `GapTwoTriples` holds. -/
theorem not_tripleTrivial_eight_one : ¬ TripleTrivial 8 1 := by
  rintro ⟨d, hd⟩
  obtain ⟨h0, h1, h2⟩ := gapOne_witness
  have hx : 282864854542 < 3 ^ 25 := by norm_num
  refine hd ⟨282864854542 % 3 ^ (d + 1), Finset.mem_range.2 (Nat.mod_lt _ (by positivity)),
    ?_, ?_, ?_⟩
  · rw [Nat.mod_mod_of_dvd _ (dvd_pow_self 3 (Nat.succ_ne_zero d))]
  · exact lowZeroOne_mod_iff.2 (lowZeroOne_of_lt_pow hx h0 d)
  · intro M hM
    rw [lowZeroOne_mul_mod_iff]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
    rcases hM with rfl | rfl
    · exact lowZeroOne_of_lt_pow (k := 35) (by norm_num) h1 d
    · exact lowZeroOne_of_lt_pow (k := 36) (by norm_num) h2 d

/-! ## The archimedean sibling -/

/-- **Lagarias 2009, Theorem 1.2** (arXiv:math/0512006; tier P, read 2026-10-06): uncountably many
real `λ > 0` have `⌊λ 2ⁿ⌋` omitting the ternary digit `2` for infinitely many `n`.  This is the
known-false sibling for any archimedean-only mechanism (rotation by `log₃ 2`, Baker discrepancy,
leading-digit counts): those inputs hold for every real `λ`, so a proof of Erdős #406 must use
that the low digits of `2ⁿ` follow `2ⁿ mod 3ᵏ`. -/
def Literature.LagariasRealSibling : Prop :=
  ¬ Set.Countable {l : ℝ | 0 < l ∧ {n : ℕ | 2 ∉ Nat.digits 3 ⌊l * 2 ^ n⌋₊}.Infinite}

/-! ## The wiring -/

/-- **Gap triples give Erdős #406.**  English proof: suppose infinitely many `n` have `2ⁿ`
omitting the ternary digit `2`.  Each such `n` is even (`2ⁿ ≡ 2 (mod 3)` for odd `n`).  Pick
`n₁ < n₂ < n₃` among them with `n₂ − n₁, n₃ − n₂ ≥ 2A`, and put `a = (n₂ − n₁)/2`,
`b = (n₃ − n₂)/2`, `x = 2^n₁`.  Then `x`, `4ᵃ x = 2^n₂`, `4ᵃ⁺ᵇ x = 2^n₃` have all digits `0/1`,
`x ≡ 1 (mod 3)`, and for every `d` the residue `x mod 3^(d+1)` is a depth-`d` witness (low
digits of `M x` depend only on `M x mod 3^(d+1)`).  This contradicts `TripleTrivial a b`.

Proved. -/
theorem erdos406_of_gapTriplesEventually (h : GapTriplesEventually) : Erdos406 := by
  obtain ⟨A, hA⟩ := h
  by_contra hinf
  have hS : Set.Infinite {n : ℕ | 2 ∉ Nat.digits 3 (2 ^ n)} := hinf
  -- members are even: the last ternary digit of `2ⁿ` is `2ⁿ % 3`
  have heven : ∀ n, 2 ∉ Nat.digits 3 (2 ^ n) → 2 ^ n % 3 = 1 := by
    intro n hn
    have h0 := lowZeroOne_of_two_not_mem hn 0 0 le_rfl
    simp only [pow_zero, Nat.div_one] at h0
    have : 2 ^ n % 3 ≠ 0 := by
      intro h3
      have : 3 ∣ 2 ^ n := Nat.dvd_of_mod_eq_zero h3
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this) (by norm_num)
    omega
  have hpar : ∀ n, 2 ^ n % 3 = 1 → Even n := by
    intro n hn
    by_contra hodd
    obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.1 hodd
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod] at hn
    norm_num at hn
  obtain ⟨n₁, hn₁⟩ := hS.nonempty
  obtain ⟨n₂, hn₂, h12⟩ := hS.exists_gt (n₁ + 2 * A)
  obtain ⟨n₃, hn₃, h23⟩ := hS.exists_gt (n₂ + 2 * A)
  obtain ⟨e₁, he₁⟩ := hpar n₁ (heven n₁ hn₁)
  obtain ⟨e₂, he₂⟩ := hpar n₂ (heven n₂ hn₂)
  obtain ⟨e₃, he₃⟩ := hpar n₃ (heven n₃ hn₃)
  obtain ⟨d, hd⟩ := hA (e₂ - e₁) (e₃ - e₂) (by omega) (by omega)
  have h4 : ∀ e, (4 : ℕ) ^ e = 2 ^ (e + e) := fun e => by rw [← two_mul, pow_mul]; norm_num
  have hM₁ : 4 ^ (e₂ - e₁) * 2 ^ n₁ = 2 ^ n₂ := by
    rw [h4, ← pow_add]; congr 1; omega
  have hM₂ : 4 ^ (e₂ - e₁ + (e₃ - e₂)) * 2 ^ n₁ = 2 ^ n₃ := by
    rw [h4, ← pow_add]; congr 1; omega
  refine hd ⟨2 ^ n₁ % 3 ^ (d + 1), Finset.mem_range.2 (Nat.mod_lt _ (by positivity)), ?_, ?_, ?_⟩
  · rw [Nat.mod_mod_of_dvd _ (dvd_pow_self 3 (Nat.succ_ne_zero d))]; exact heven n₁ hn₁
  · exact lowZeroOne_mod_iff.2 (lowZeroOne_of_two_not_mem hn₁ d)
  · intro M hM
    rw [lowZeroOne_mul_mod_iff]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
    rcases hM with rfl | rfl
    · rw [hM₁]; exact lowZeroOne_of_two_not_mem hn₂ d
    · rw [hM₂]; exact lowZeroOne_of_two_not_mem hn₃ d

theorem erdos406_of_gapTwoTriples (h : GapTwoTriples) : Erdos406 :=
  erdos406_of_gapTriplesEventually (gapTriplesEventually_of_gapTwoTriples h)

/-! ## The 3-adic form -/

/-- Ternary digit `i` of a 3-adic integer. -/
noncomputable def padicDigit (x : ℤ_[3]) (i : ℕ) : ℕ :=
  (PadicInt.toZModPow (i + 1) x).val / 3 ^ i

/-- The 3-adic Cantor set `Σ₃,₂̄`: every digit is `0` or `1`. -/
def InCantor (x : ℤ_[3]) : Prop := ∀ i, padicDigit x i ≤ 1

/-- Lagarias's 3-adic exceptional set (arXiv:math/0512006, (1.10)). -/
def ExceptionalSet : Set ℤ_[3] := {l | {n : ℕ | InCantor (2 ^ n * l)}.Infinite}

/-- **Gap triples empty the exceptional set.**  English proof: for `λ ≠ 0` in `E(ℤ₃)`, the
exponents `n` with `λ 2ⁿ ∈ Σ` share a parity (the lowest nonzero digit of `λ 2ⁿ` is `1`, and
multiplying by `2^odd ≡ 2 (mod 3)` makes it `2`).  Take three with both gaps `≥ 2A`, shift
`y = λ 2^n₁` by its 3-adic valuation to a unit, and its residues mod `3^(d+1)` witness
`Survives [4ᵃ, 4ᵃ⁺ᵇ] d` for every `d`.  So `E(ℤ₃) = {0}`, which contains Erdős #406 (`1 ∉ E`)
and Lagarias's Conjecture B (dimension zero) and answers his question whether `E(ℤ₃) = {0}`
(ABL I, §1.1: "we do not know whether E(ℤ₃) = {0} or not").

Believed, confidence 95%. -/
theorem exceptionalSet_eq_zero_of_gapTriplesEventually (h : GapTriplesEventually) :
    ExceptionalSet = {0} := by
  sorry

/-! ## Side finding: intermittency of `2ⁿ` -/

/-- Number of maximal runs of equal digits in the ternary expansion (ABL II's intermittency
`s₃`). -/
def intermittency (n : ℕ) : ℕ :=
  let L := Nat.digits 3 n
  L.length - ((L.zip L.tail).filter (fun p => p.1 = p.2)).length

/-- **`s₃(2ⁿ) → ∞`.**  ABL II §7 (arXiv:1508.05967): "it is not currently known whether
`b₃(2ⁿ) → ∞` holds as `n → ∞` or whether `s₃(2ⁿ) → ∞`".  The `s₃` half follows from Stewart's
Baker-method argument (Crelle 319, 1980): `2N = 3N − N = Σᵢ (nᵢ₋₁ − nᵢ) 3ⁱ` writes `2^(n+1)` with
`s₃(2ⁿ) + 1` signed terms of size `≤ 2`, no proper subsum vanishes (the lowest term is not
divisible by 3), and Stewart's iteration of linear forms in two logarithms then forces
`s₃(2ⁿ) ≫ log n / log log n`.  (The `b₃` half is as hard as "`2ⁿ` eventually has a ternary 0".)

Believed, confidence 85%: the adaptation is routine, but a published statement for signed
digits has not been traced.  Tier: our formulation. -/
def IntermittencyTendsToInfinity : Prop :=
  Filter.Tendsto (fun n => intermittency (2 ^ n)) Filter.atTop Filter.atTop

end NormalNumbers.ErdosTriples
