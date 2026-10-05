/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Digits of powers and smooth numbers: one crux under four Numberphile problems

Source: the Numberphile sweep of 2026-10-05 (`~/personal/claude/knowledge/core/reference/numberphile/`).
Four popular open problems reduce to one integer-digit statement, recorded here as the open
node `SmoothDigitOmission`:

* **Erdős #406**: only finitely many `2ⁿ` avoid the ternary digit `2` (`Erdos406`).
* **Zeroless powers of two**: `2⁸⁶` is the last `2ⁿ` with no decimal `0` (`ZerolessPowersOfTwo`).
* **Multiplicative persistence ≤ 11** (277777788888899): the terminal-digit-`0` case, the one the
  2-adic method of Brier–Clavier–Gutsche–Naccache and Fonga does not reach, and the case every
  known persistence-11 number is in (`Persistence11`, `persistence_record`).
* **82000** (0/1 digits in bases 2–5) is a *sibling*, not an instance: it asks for independence of
  digit expansions across multiplicatively independent bases, with no smoothness in sight
  (`ZeroOneBases2to5`, `ZeroOneBases2to6`).

`SmoothDigitOmission` is the integer shadow of normality: it says an `S`-smooth number's base-`b`
digits behave randomly enough to use every digit, once `n` is large.  Its hypothesis (some prime of
`b` lies outside `S`) is the separating condition: `smoothDigitOmission_hyp_needed` shows the
statement fails without it.

Difficulty check (LEAN-NEW-MATH).  *Proved nearby*: Senge–Straus 1973 / Stewart 1980, the number of
nonzero base-`b` digits of `S`-smooth numbers tends to infinity (Baker's linear forms in
logarithms); Narkiewicz 1980's counting bound for Erdős #406; Lagarias 2009's metric and 3-adic
results (arXiv:math/0512006); computer checks far past any plausible exception (see each
docstring).  *Unproved premise*: `SmoothDigitOmission`, even for a single `(b, S, d)`.  *Mechanism*:
none known.  Linear forms give "many nonzero digits", never "every digit occurs".

Provenance tiers as in `Literature.lean`: **P** (paper held), **S** (secondary: abstract or our
docs), **M** (memory: not yet traced to a source; fetch before relying on it).
-/

namespace NormalNumbers.Literature.DigitsOfPowers

/-! ## The crux -/

/-- The `S`-smooth numbers (all prime factors in `S`) whose base-`b` digits omit `d`. -/
def SmoothOmitters (b : ℕ) (S : Finset ℕ) (d : ℕ) : Set ℕ :=
  {n | n ∈ Nat.factoredNumbers S ∧ d ∉ Nat.digits b n}

/-- **Open node: smooth numbers eventually use every digit.**  For a base `b ≥ 2` and a finite set
`S`, if some prime factor of `b` is outside `S`, then for each digit `d < b` only finitely many
`S`-smooth numbers omit `d` in base `b`.

Believed, confidence 85% for the full universal form (95% for each instance used below).
Heuristic: there are `≍ (log X)^|S|` `S`-smooth numbers up to `X`, and a random `log_b X`-digit
string omits a fixed digit with probability `X^{log_b (1 - 1/b)}`, so the expected count of
omitters converges.  The hypothesis rules out the structured counterexamples `m · bᵏ`
(`smoothDigitOmission_hyp_needed`).  Evidence: each instance below is checked numerically far
past its last known exception.  Tier: our formulation (the general form is folklore; source not
traced). -/
def SmoothDigitOmission : Prop :=
  ∀ b : ℕ, 2 ≤ b → ∀ S : Finset ℕ, (∃ p, p.Prime ∧ p ∣ b ∧ p ∉ S) →
    ∀ d, d < b → (SmoothOmitters b S d).Finite

/-- The hypothesis of `SmoothDigitOmission` is needed: with `b = 10` and `S = {2, 5}` (every prime
of the base in `S`), the powers `10ᵏ` are `S`-smooth and never use the digit `9`. -/
theorem smoothDigitOmission_hyp_needed : (SmoothOmitters 10 {2, 5} 9).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 10 ^ k)
    (Nat.pow_right_injective (by norm_num)) fun k => ⟨?_, ?_⟩
  · have h5 : 5 ^ k ∈ Nat.factoredNumbers {5} := by
      simpa using Nat.pow_mul_mem_factoredNumbers (s := ∅) (n := 1) Nat.prime_five k
        (by simp [Nat.factoredNumbers_empty])
    have := Nat.pow_mul_mem_factoredNumbers Nat.prime_two k h5
    simpa [← mul_pow] using this
  · have := Nat.digits_base_pow_mul (b := 10) (k := k) (m := 1) (by norm_num) (by norm_num)
    simp only [mul_one] at this
    rw [this]
    simp

/-! ## Instances -/

/-- **Erdős #406** (open; `formal-conjectures` `Erdos406.erdos_406` states it with
`answer(sorry)`): only finitely many powers of `2` use only the digits `0, 1` in base `3`.
Evidence: no exception beyond `n = 0, 2, 8` up to `n ≤ 2·3⁴⁵ ≈ 5.9·10²¹` (Saye, JIS 25 (2022),
arXiv:2202.13256; tier S). -/
def Erdos406 : Prop :=
  {n : ℕ | 2 ∉ Nat.digits 3 (2 ^ n)}.Finite

/-- **Zeroless powers of two** (open; OEIS A007377 lists `n` with `2ⁿ` zeroless, conjectured
finite with largest `86`).  Evidence: checked to `n = 10¹⁰` (Radcliffe 2022, per OEIS; tier S). -/
def ZerolessPowersOfTwo : Prop :=
  ∀ n : ℕ, 0 ∉ Nat.digits 10 (2 ^ n) → n ≤ 86

/-- The finiteness form of `ZerolessPowersOfTwo`, the shape `SmoothDigitOmission` delivers. -/
def ZerolessPowersOfTwoFinite : Prop :=
  {n : ℕ | 0 ∉ Nat.digits 10 (2 ^ n)}.Finite

theorem pow_two_mem_factoredNumbers (n : ℕ) : 2 ^ n ∈ Nat.factoredNumbers {2} := by
  simpa using Nat.pow_mul_mem_factoredNumbers (s := ∅) (n := 1) Nat.prime_two n
    (by simp [Nat.factoredNumbers_empty])

/-- Wired edge: the crux implies Erdős #406. -/
theorem erdos406_of_smoothDigitOmission (h : SmoothDigitOmission) : Erdos406 := by
  have hfin := h 3 (by norm_num) {2} ⟨3, Nat.prime_three, dvd_refl 3, by decide⟩ 2 (by norm_num)
  refine (hfin.preimage (Nat.pow_right_injective (le_refl 2)).injOn).subset ?_
  intro n hn
  exact ⟨pow_two_mem_factoredNumbers n, hn⟩

/-- Wired edge: the crux implies finitely many zeroless powers of two. -/
theorem zerolessPowersOfTwoFinite_of_smoothDigitOmission (h : SmoothDigitOmission) :
    ZerolessPowersOfTwoFinite := by
  have hfin := h 10 (by norm_num) {2} ⟨5, Nat.prime_five, by norm_num, by decide⟩ 0 (by norm_num)
  refine (hfin.preimage (Nat.pow_right_injective (le_refl 2)).injOn).subset ?_
  intro n hn
  exact ⟨pow_two_mem_factoredNumbers n, hn⟩

/-! ## Multiplicative persistence -/

/-- One digit-product step: a single digit is fixed (so `0` stays `0`; note `Nat.digits 10 0 = []`
would otherwise give product `1`), and a longer number maps to the product of its digits. -/
def digitProd (n : ℕ) : ℕ := if n < 10 then n else (Nat.digits 10 n).prod

/-- The terminal digit: `digitProd n < n` for `n ≥ 10`, so `n` iterations always reach a single
digit, which is then fixed. -/
def terminalDigit (n : ℕ) : ℕ := digitProd^[n] n

/-- **The persistence conjecture** (open; Sloane 1973; OEIS A003001): every number reaches a single
digit within `11` digit-product steps.  Evidence: no persistence-12 number below `2.67·10³⁰⁰⁰⁰`
(Peters 2023, per OEIS; tier S). -/
def Persistence11 : Prop :=
  ∀ n : ℕ, digitProd^[11] n < 10

/-- The record `277777788888899` needs exactly `11` steps and ends at `0`.  Every known
persistence-11 number ends at terminal digit `0` (OEIS A003001; tier S), which is why the 2-adic
method below, which needs a nonzero terminal digit, cannot reach the conjecture's real content. -/
theorem persistence_record :
    10 ≤ digitProd^[10] 277777788888899 ∧ digitProd^[11] 277777788888899 = 0 := by
  native_decide

/-- **Brier–Clavier–Gutsche–Naccache 2021** (arXiv:2110.04263, Theorem; tier P, paper held at
`~/personal/papers/2110.04263.pdf`, read 2026-10-05): terminal digit `1, 3, 7` or `9` forces
persistence `≤ 1`, and terminal digit `5` forces persistence `≤ 5`.  Proof by a modular sieve on
the exponential Diophantine equations attached to a finite backward graph. -/
def BrierOddTerminal : Prop :=
  ∀ n : ℕ, (terminalDigit n ∈ ({1, 3, 7, 9} : Finset ℕ) → digitProd^[1] n < 10) ∧
    (terminalDigit n = 5 → digitProd^[5] n < 10)

/-- **The nonzero-terminal target** (open).  Fonga (arXiv:2608.27802, Aug 2026; tier P, paper held)
proves Brier et al.'s 2-adic boundedness conjecture, so their procedure becomes finite for each
nonzero even terminal digit.  Not run, and a direct run is out of reach: feasibility study
`docs/PERSISTENCE-FEASIBILITY-2026-10-05.md` measures the first sieve stage at about `10¹⁸`
(terminal `2`) to `10²⁴` (terminal `6, 8`) modular checks, and the sieve is conclusive only if it
happens to close (a Hasse-principle-type property, not proved).  If it closes, Brier et al.'s
candidate graphs (reproduced in `experiments/persistence/graphs.py`) give the sharper bound in
`PersistenceNonzeroTerminal8`. -/
def PersistenceNonzeroTerminal : Prop :=
  ∀ n : ℕ, terminalDigit n ≠ 0 → digitProd^[11] n < 10

/-- The sharper form the candidate graphs predict: longest backward paths `6, 5, 8, 6` for terminal
digits `2, 4, 6, 8` (Brier et al. Table 3, reproduced 2026-10-05).  Open. -/
def PersistenceNonzeroTerminal8 : Prop :=
  ∀ n : ℕ, terminalDigit n ≠ 0 → digitProd^[8] n < 10

/-- The crux bounds persistence: with `b = 10`, a zeroless value of `digitProd` is `{2,3,5,7}`-smooth
and not divisible by `10`, so it lies in `SmoothOmitters 10 {2,3,7} 0` or
`SmoothOmitters 10 {3,5,7} 0`, both finite under the crux (`5 ∉ {2,3,7}`, `2 ∉ {3,5,7}`).  A chain
of length `k` has its values after step `1` all zeroless (a `0` digit sends the next value to `0`),
so after one step every long chain sits below the largest omitter `M`, and persistence is at most
`2 + max_{m ≤ M} persistence m`.

Believed, confidence 97%: the English proof above; the formal proof needs `digitProd n < n` for
`n ≥ 10` and the factorization of a digit product.  The crux gives a bound, not the value `11`; the
value comes from computation once `M` is known. -/
theorem persistence_bounded_of_smoothDigitOmission (h : SmoothDigitOmission) :
    ∃ B : ℕ, ∀ n : ℕ, digitProd^[B] n < 10 := by
  sorry

/-! ## The 82000 sibling -/

/-- All base-`b` digits of `n` are `0` or `1`. -/
def ZeroOneIn (b n : ℕ) : Prop := ∀ d ∈ Nat.digits b n, d ≤ 1

instance (b n : ℕ) : Decidable (ZeroOneIn b n) := by
  unfold ZeroOneIn; infer_instance

/-- `82000` uses only the digits `0, 1` in bases `2, 3, 4, 5`. -/
theorem zeroOneIn_82000 : ZeroOneIn 2 82000 ∧ ZeroOneIn 3 82000 ∧ ZeroOneIn 4 82000 ∧
    ZeroOneIn 5 82000 := by
  decide +kernel

/-- **82000 is the last** (open; OEIS A146025 conjectures `{0, 1, 82000}` complete).  Evidence:
none other below about `10^(1.1·10⁷)` (Klinkhamer 2015 search, per OEIS; tier S).  Theory:
Burrell–Yu, J. Number Theory 226 (2021), arXiv:1905.00832, bound the count of integers with 0/1
digits in two such bases (tier S). -/
def ZeroOneBases2to5 : Prop :=
  ∀ n : ℕ, 1 < n → ZeroOneIn 2 n → ZeroOneIn 3 n → ZeroOneIn 4 n → ZeroOneIn 5 n → n = 82000

/-- **No number beyond 1 does it for bases 2 through 6** (open; OEIS A258107).  A solution would be
`≡ 0` or `1 (mod 36)` (Singh 2026, OEIS comment; tier S). -/
def ZeroOneBases2to6 : Prop :=
  ∀ n : ℕ, 1 < n → ¬ (ZeroOneIn 2 n ∧ ZeroOneIn 3 n ∧ ZeroOneIn 4 n ∧ ZeroOneIn 5 n ∧
    ZeroOneIn 6 n)

/-- The base-6 question is implied by the base-5 one: `82000` fails in base 6. -/
theorem zeroOneBases2to6_of_2to5 (h : ZeroOneBases2to5) : ZeroOneBases2to6 := by
  rintro n hn ⟨h2, h3, h4, h5, h6⟩
  obtain rfl := h n hn h2 h3 h4 h5
  revert h6
  decide +kernel

end NormalNumbers.Literature.DigitsOfPowers
