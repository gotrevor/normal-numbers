/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.FieldTheory.Finite.Basic
import NormalNumbers.LiteratureDigitsOfPowers

/-!
# The gap-tuple move does not port to zeroless powers of two

`/create` session 2026-10-07, second instance of `SmoothDigitOmission` after `ErdosTriples`.

**The base-10 analogue.**  For `n ≥ d`, `2ⁿ mod 10ᵈ` is divisible by `2ᵈ`, so the low digits of
powers of two live in the 10-adic ideal `e₅ ℤ₁₀ = {0} × ℤ₅`: residues `r mod 10ᵈ` with `2ᵈ ∣ r`.
A level-`d` residue has exactly five lifts (the next digit has a forced parity), four or five of
them nonzero, so the zeroless part grows like `4.5ᵈ` and has dimension `log₅ 4.5` in `ℤ₅`.  A
zeroless `2^n₁` followed by zeroless `2^n₂, …` gives a point of
`Survives10 [2^(n₂-n₁), …] d` at the depth `d = (digits of 2^n₁).length`, exactly as in the
ternary triples.

**Two kills.**

* *Supercritical.*  Each translate costs a factor `0.9`, against `5` lifts, so the random model
  needs `k ≥ 16` translates (`5 · 0.9¹⁶ < 1`) where base 3 needed `3`.  Measured
  (`experiments/zeroless-tuples/tuple10.py`): triples grow `≈ 3.65×` per digit (model
  `4.5 · 0.81 = 3.645`), 15 translates are critical, 16 die by depth 13 in every random sample.
  `survives10_four_sixteen_thirty` is the gap-`(2,2)` triple alive at depth 30, where the ternary
  `ErdosTriples.tripleTrivial_two_two` dies at depth 1.
* *Truncation (the structural kill).*  Base 3 used the full 3-adic expansion of `2^n₁`, so the
  death depth was free.  Here only `(digits of 2^n₁).length` digits are available, and a gap `g`
  with `φ(5ᵈ) ∣ g` makes `2ᵍ` act as the identity mod `10ᵈ`.  `not_tupleDeathAtLength`: for
  **every** tuple size `k` and gap floor `A`, the hypothesis the port needs is false.  The
  survivors are exponent sequences that converge 5-adically fast enough to outrun the length,
  i.e. `NestedZerolessChain`: one zeroless 10-adic integer with infinitely many truncations
  that are powers of two.

*Unproved premise left standing*: `NoNestedZerolessChain` (implied by the conjecture, see
`noNestedZerolessChain_of_finite`), plus 16-translate extinction for non-imitating gaps.
*Mechanism*: none.
-/

namespace NormalNumbers.ZerolessTuples

open NormalNumbers.Literature.DigitsOfPowers

/-- The decimal digits of `n` in places `0, …, d - 1` are all nonzero. -/
def LowNonzero (d n : ℕ) : Prop := ∀ i < d, n / 10 ^ i % 10 ≠ 0

instance (d n : ℕ) : Decidable (LowNonzero d n) := by
  unfold LowNonzero; infer_instance

/-- Some residue mod `10ᵈ` in the ideal `2ᵈ ∣ r` is zeroless to depth `d` together with all its
multiples `M * r`.  The base-10 counterpart of `ErdosTriples.Survives`. -/
def Survives10 (Ms : List ℕ) (d : ℕ) : Prop :=
  ∃ r < 10 ^ d, 2 ^ d ∣ r ∧ LowNonzero d r ∧ ∀ M ∈ Ms, LowNonzero d (M * r)

theorem div_pow_ten_mod_of_lt {n i d : ℕ} (hi : i < d) :
    n % 10 ^ d / 10 ^ i % 10 = n / 10 ^ i % 10 := by
  have h : 10 ^ d = 10 ^ i * 10 ^ (d - i) := by
    rw [← pow_add]; congr 1; omega
  rw [h, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact dvd_pow_self 10 (by omega)

theorem lowNonzero_congr {d n m : ℕ} (h : n % 10 ^ d = m % 10 ^ d) :
    LowNonzero d n ↔ LowNonzero d m := by
  unfold LowNonzero
  refine forall₂_congr fun i hi => ?_
  rw [← div_pow_ten_mod_of_lt (n := n) hi, ← div_pow_ten_mod_of_lt (n := m) hi, h]

/-- The single set never dies: every depth has a zeroless residue in the ideal (the classical
"some power of two ends in `d` nonzero digits").  Lift by the digit `2` or `1`, whichever keeps
the next power of two dividing. -/
theorem exists_lowNonzero (d : ℕ) : ∃ r < 10 ^ d, 2 ^ d ∣ r ∧ LowNonzero d r := by
  induction d with
  | zero => exact ⟨0, by norm_num, by norm_num, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ d ih =>
    obtain ⟨r, hr, ⟨q, rfl⟩, hnz⟩ := ih
    set j := if q % 2 = 0 then 2 else 1 with hj
    have hj1 : 1 ≤ j := by rw [hj]; split_ifs <;> norm_num
    have hj2 : j ≤ 2 := by rw [hj]; split_ifs <;> norm_num
    have h5 : 5 ^ d % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
    have heven : 2 ∣ q + j * 5 ^ d := by
      rw [hj]; split_ifs with h <;> omega
    refine ⟨2 ^ d * q + j * 10 ^ d, ?_, ?_, ?_⟩
    · have h10 : j * 10 ^ d ≤ 2 * 10 ^ d := Nat.mul_le_mul_right _ hj2
      have hp : 0 < 10 ^ d := by positivity
      rw [pow_succ]; linarith
    · obtain ⟨t, ht⟩ := heven
      refine ⟨t, ?_⟩
      have : 2 ^ d * q + j * 10 ^ d = 2 ^ d * (q + j * 5 ^ d) := by
        rw [show (10 : ℕ) ^ d = 2 ^ d * 5 ^ d by rw [← mul_pow]; norm_num]; ring
      rw [this, ht, pow_succ]; ring
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · have hmod : (2 ^ d * q + j * 10 ^ d) % 10 ^ d = 2 ^ d * q := by
          rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
        rw [← div_pow_ten_mod_of_lt hi, hmod]
        exact hnz i hi
      · have hpos : 0 < 10 ^ i := by positivity
        rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hr, zero_add,
          Nat.mod_eq_of_lt (by omega)]
        omega

/-- **Imitators.**  If every multiplier is `2ᵍ` with `d ≤ g` and `φ(5ᵈ) ∣ g`, it acts as the
identity mod `10ᵈ` on the ideal, so the tuple survives to depth `d` with any single-set point. -/
theorem survives10_of_imitators {d : ℕ} {Ms : List ℕ}
    (hMs : ∀ M ∈ Ms, ∃ g, M = 2 ^ g ∧ d ≤ g ∧ Nat.totient (5 ^ d) ∣ g) :
    Survives10 Ms d := by
  obtain ⟨r, hr, hdvd, hnz⟩ := exists_lowNonzero d
  refine ⟨r, hr, hdvd, hnz, fun M hM => ?_⟩
  obtain ⟨g, rfl, hdg, ⟨c, rfl⟩⟩ := hMs M hM
  refine (lowNonzero_congr ?_).mpr hnz
  have h5 : 2 ^ (Nat.totient (5 ^ d) * c) * r ≡ r [MOD 5 ^ d] := by
    have hcop : Nat.Coprime 2 (5 ^ d) := Nat.Coprime.pow_right d (by decide : Nat.Coprime 2 5)
    have := ((Nat.ModEq.pow_totient hcop).pow c).mul_right r
    rwa [← pow_mul, one_pow, one_mul] at this
  have h2 : 2 ^ (Nat.totient (5 ^ d) * c) * r ≡ r [MOD 2 ^ d] := by
    have ha : 2 ^ d ∣ 2 ^ (Nat.totient (5 ^ d) * c) * r :=
      Dvd.dvd.mul_right (pow_dvd_pow 2 hdg) r
    exact (Nat.modEq_zero_iff_dvd.mpr ha).trans (Nat.modEq_zero_iff_dvd.mpr hdvd).symm
  have hcop : Nat.Coprime (2 ^ d) (5 ^ d) := Nat.Coprime.pow d d (by decide : Nat.Coprime 2 5)
  have := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h2, h5⟩
  rwa [← mul_pow] at this

/-- Exponent lists whose first entry and consecutive gaps are all at least `A`. -/
def Gapped (A : ℕ) (es : List ℕ) : Prop := List.IsChain (fun x y => x + A ≤ y) (0 :: es)

theorem gapped_multiples (A c k m : ℕ) (hc : A ≤ c) :
    List.IsChain (fun x y => x + A ≤ y) (m * c :: (List.range' (m + 1) k).map (· * c)) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [List.range'_succ, List.map_cons, List.isChain_cons_cons]
    exact ⟨by nlinarith, ih (m + 1)⟩

/-- For every size, gap floor and depth there is a gapped tuple of imitators alive at that depth. -/
theorem exists_gapped_survivor (A d k : ℕ) :
    ∃ es : List ℕ, es.length = k ∧ Gapped A es ∧ Survives10 (es.map (2 ^ ·)) d := by
  set c := (A + d + 1) * Nat.totient (5 ^ d) with hc
  have hφ : 1 ≤ Nat.totient (5 ^ d) := Nat.totient_pos.mpr (by positivity)
  have hAc : A + d + 1 ≤ c := by rw [hc]; nlinarith
  refine ⟨(List.range' 1 k).map (· * c), by simp, ?_, survives10_of_imitators ?_⟩
  · simpa [Gapped] using gapped_multiples A c k 0 (by omega)
  · intro M hM
    simp only [List.map_map, List.mem_map, List.mem_range'_1, Function.comp] at hM
    obtain ⟨i, ⟨hi1, -⟩, rfl⟩ := hM
    refine ⟨i * c, rfl, ?_, ⟨i * (A + d + 1), by rw [hc]; ring⟩⟩
    calc d ≤ c := by omega
      _ ≤ i * c := Nat.le_mul_of_pos_left c hi1

/-- The hypothesis the base-10 port of `ErdosTriples.erdos406_of_gapTriplesEventually` needs: from
some size `k` and gap floor `A` on, every gapped `k`-tuple dies within the digit length of the
base power `2^n₁` (the only digits the zeroless hypothesis supplies). -/
def TupleDeathAtLength (k : ℕ) : Prop :=
  ∃ A N, ∀ n₁ ≥ N, ∀ es : List ℕ, es.length = k → Gapped A es →
    ¬ Survives10 (es.map (2 ^ ·)) (Nat.digits 10 (2 ^ n₁)).length

/-- **The port is dead at every tuple size.**  Imitating gaps (`φ(5ᵈ) ∣ g`) survive any finite
depth, so no gap floor makes tuples die within a prescribed length. -/
theorem not_tupleDeathAtLength (k : ℕ) : ¬ TupleDeathAtLength k := by
  rintro ⟨A, N, h⟩
  obtain ⟨es, hl, hg, hs⟩ := exists_gapped_survivor A (Nat.digits 10 (2 ^ N)).length k
  exact h N le_rfl es hl hg hs

/-- Supercriticality at gaps `(2, 2)`: `1, 4, 16` all zeroless to depth 30 (the witness has digits
in `{1, 2}`).  Contrast `ErdosTriples.tripleTrivial_two_two`, dead at depth 1 in base 3. -/
theorem survives10_four_sixteen_thirty : Survives10 [4, 16] 30 :=
  ⟨121122111112111211111212122112, by norm_num, by norm_num, by decide +kernel, by decide +kernel⟩

/-- Conjecture (90%, measured growth `≈ 3.65` per digit): base-10 triples never die. -/
def BaseTenTriplesSurvive : Prop :=
  ∀ a b, 1 ≤ a → 1 ≤ b → ∀ d, Survives10 [2 ^ a, 2 ^ (a + b)] d

/-- What the tuple method cannot see: a 10-adic integer with infinitely many low truncations that
are zeroless powers of two.  Consecutive members must satisfy `2^n' ≡ 2ⁿ mod 10^(len 2ⁿ)`, which
forces `φ(5^len) ∣ n' - n`, a 5-adically super-convergent exponent sequence whose every tuple is
an imitator at the available depth. -/
def NestedZerolessChain : Prop :=
  ∃ S : Set ℕ, S.Infinite ∧ (∀ n ∈ S, 0 ∉ Nat.digits 10 (2 ^ n)) ∧
    ∀ n ∈ S, ∀ n' ∈ S, n < n' → 2 ^ n' % 10 ^ (Nat.digits 10 (2 ^ n)).length = 2 ^ n

/-- The residual question (open; heuristically the chain's expected count is summable, 95%). -/
def NoNestedZerolessChain : Prop := ¬ NestedZerolessChain

theorem noNestedZerolessChain_of_finite (h : ZerolessPowersOfTwoFinite) :
    NoNestedZerolessChain := by
  rintro ⟨S, hS, hz, -⟩
  exact hS (h.subset fun n hn => hz n hn)

end NormalNumbers.ZerolessTuples
