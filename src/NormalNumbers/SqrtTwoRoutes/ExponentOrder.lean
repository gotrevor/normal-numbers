/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SqrtTwoRoutes.WordCertificate

/-!
# Early multiplicative-order hits along Pell convergents

For odd `n`, `p_n/q_n` is below `sqrt 2`, and `p_n` is a unit modulo the
odd denominator `q_n`.  The residue `r = p_n * 2^m mod q_n` proposes a
rational orbit point.  Its Pell approximation error is

`2^m / (q_n * (p_n + q_n * sqrt 2)) < 2^m / (2 * q_n^2)`.

The margin predicate below asks that this upper bound fit between the
rational orbit point and the top of the target word cell.  It is a sufficient
early-hit criterion; a full multiplicative period does not ensure the margin.
-/

namespace NormalNumbers.SqrtTwoRoutes

/-- A rational orbit point has enough one-sided margin for the Pell error
bound to keep it inside the word cell `(A/S, (A+1)/S)`. -/
def pellOrderMarginHit (p q S A m : ℕ) : Prop :=
  let r := p * 2 ^ m % q
  A * q < S * r ∧ S * 2 ^ m < 2 * q * ((A + 1) * q - S * r)

/-- The margin condition forces the exponent to lie in a short range:
`S*2^m < 2*q^2`.  The period itself may be much larger. -/
theorem pellOrderMarginHit_exponent_bound
    (p q S A m : ℕ) (hq : 0 < q)
    (hhit : pellOrderMarginHit p q S A m) :
    S * 2 ^ m < 2 * q ^ 2 := by
  dsimp [pellOrderMarginHit] at hhit
  obtain ⟨hlower, hmargin⟩ := hhit
  have hclear : (A + 1) * q - S * (p * 2 ^ m % q) < q := by
    rw [Nat.add_mul] at *
    simp only [one_mul] at *
    omega
  calc
    S * 2 ^ m < 2 * q * ((A + 1) * q - S * (p * 2 ^ m % q)) := hmargin
    _ < 2 * q ^ 2 := by
      have hmul := Nat.mul_lt_mul_of_pos_left hclear (by omega : 0 < 2 * q)
      simpa [pow_two, Nat.mul_assoc] using hmul

/-- Open uniform premise for the early-order selector: every binary word
cell has a margin hit at some odd Pell denominator.  For fixed odd `q_n`, the
residue depends only on `m` modulo the multiplicative order of `2`.  A hit
past one period can be reduced modulo that order: the residue stays fixed and
the error budget `2^m` decreases.  The horizon theorem therefore limits the
useful search to early exponents within a period. -/
@[blueprint (title := "Uniform early Pell multiplicative-order margin supply")]
def PellEarlyOrderMarginSupply : Prop :=
  ∀ L A : ℕ, A < 2 ^ L → ∃ n m : ℕ,
    n % 2 = 1 ∧ 0 < pellQ n ∧
      pellOrderMarginHit (Int.natAbs (pellP n))
        (Int.natAbs (pellQ n)) (2 ^ L) A m

/-- Explicitly open transfer statement for the selector.  For odd `n`,
`p_n/q_n` lies below `sqrt 2`; the Pell norm gives the error formula in the
module header, and the integer margin test is intended to place the exact
orbit in the word cell.  This declaration is a research premise, not a
proved theorem. -/
@[blueprint (title := "Open transfer from an early Pell residue margin to a word hit")]
def PellOrderMarginTransfer : Prop :=
  ∀ L A m n : ℕ, n % 2 = 1 → 0 < pellQ n → A < 2 ^ L →
    pellOrderMarginHit (Int.natAbs (pellP n))
      (Int.natAbs (pellQ n)) (2 ^ L) A m →
    orbit 2 (Real.sqrt 2) m ∈
      Set.Ioo ((A : ℝ) / (2 : ℝ) ^ L)
        (((A : ℝ) + 1) / (2 : ℝ) ^ L)

/-- Supply plus the stated transfer gives every binary cylinder hit. -/
@[blueprint (title := "Early Pell margin supply gives every binary cylinder")]
theorem pellEarlyOrderSupply_gives_word_hits
    (hsupply : PellEarlyOrderMarginSupply)
    (htransfer : PellOrderMarginTransfer) :
    ∀ L A : ℕ, A < 2 ^ L → ∃ m : ℕ,
      orbit 2 (Real.sqrt 2) m ∈
        Set.Ioo ((A : ℝ) / (2 : ℝ) ^ L)
          (((A : ℝ) + 1) / (2 : ℝ) ^ L) := by
  intro L A hA
  obtain ⟨n, m, hn, hq, hhit⟩ := hsupply L A hA
  exact ⟨m, htransfer L A m n hn hq hA hhit⟩

/-- The two open selector inputs would imply binary disjunctivity. -/
@[blueprint (title := "Early Pell margin supply and transfer imply sqrt(2) disjunctivity")]
theorem pellEarlyOrderSupply_implies_disjunctive
    (hsupply : PellEarlyOrderMarginSupply)
    (htransfer : PellOrderMarginTransfer) :
    IsDisjunctive 2 (Real.sqrt 2) := by
  intro a c ha hac hc
  have hgap : 0 < c - a := sub_pos.mpr hac
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one
    (show 0 < (c - a) / 2 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have hsmall : 2 / (2 : ℝ) ^ L < c - a := by
    have hL' : (1 / 2 : ℝ) ^ L < (c - a) / 2 := hL
    have hrewrite : (1 / 2 : ℝ) ^ L = 1 / (2 : ℝ) ^ L := by
      rw [one_div_pow]
    rw [hrewrite] at hL'
    have hpow : 0 < (2 : ℝ) ^ L := by positivity
    rw [div_lt_iff₀ hpow]
    have hmul := mul_lt_mul_of_pos_right hL' (by positivity : (0 : ℝ) < 2 * (2 : ℝ) ^ L)
    have hleft : (1 / (2 : ℝ) ^ L) * (2 * (2 : ℝ) ^ L) = 2 := by
      field_simp [ne_of_gt hpow]
    have hright : ((c - a) / 2) * (2 * (2 : ℝ) ^ L) = (c - a) * (2 : ℝ) ^ L := by ring
    nlinarith [hmul]
  let S : ℝ := (2 : ℝ) ^ L
  let A : ℕ := ⌊a * S⌋₊ + 1
  have hSpos : 0 < S := by dsimp [S]; positivity
  have hsmall' : 2 < (c - a) * S := by
    dsimp [S] at *
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ L)] at hsmall
    nlinarith
  have hfloorlo : (⌊a * S⌋₊ : ℝ) ≤ a * S := Nat.floor_le (by positivity)
  have hfloorhi : a * S < (⌊a * S⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hAlo : a < (A : ℝ) / S := by
    rw [lt_div_iff₀ hSpos]
    dsimp [A]
    push_cast
    exact hfloorhi
  have hAhi : ((A : ℝ) + 1) / S < c := by
    rw [div_lt_iff₀ hSpos]
    dsimp [A]
    push_cast
    nlinarith [hfloorlo, hsmall']
  have hAvalid : A < 2 ^ L := by
    have hAhi' : (A : ℝ) + 1 < (2 : ℝ) ^ L := by
      have hAhiMul := (div_lt_iff₀ hSpos).mp hAhi
      have hcS : c * S ≤ S := mul_le_of_le_one_left hSpos.le hc
      dsimp [S] at hAhiMul ⊢
      nlinarith [hcS]
    have hNat : A + 1 < 2 ^ L := by exact_mod_cast hAhi'
    omega
  obtain ⟨m, hcell⟩ :=
    pellEarlyOrderSupply_gives_word_hits hsupply htransfer L A hAvalid
  refine ⟨m, ?_⟩
  constructor
  · exact le_of_lt (lt_trans hAlo hcell.1)
  · exact lt_trans hcell.2 hAhi

/-- Exact values for two small Pell denominators used as positive and
negative controls for the early-order criterion. -/
theorem pell_order_control_pairs :
    pellPair 3 = (7, 5) ∧ pellPair 5 = (41, 29) := by
  norm_num [pellPair]

/-- The small denominator `q_3=5` has early hits with enough error margin
for both one-letter binary words.  These are controls for the selector,
not evidence for uniform supply. -/
theorem pell_order_positive_controls :
    pellOrderMarginHit 7 5 2 0 3 ∧ pellOrderMarginHit 7 5 2 1 1 := by
  norm_num [pellOrderMarginHit]

/-- At `q_5=29`, multiplication by 2 has full order 28, and its complete
residue cycle visits the rational `111` cell.  Yet no exponent satisfies the
required approximation margin.  This Pell-specific negative control does
not reopen the generic whole-period transport shortcut, already retired in
the Maze. -/
theorem pell_order_full_cycle_misses_margin_control :
    2 ^ 28 % 29 = 1 ∧
    (∀ d : ℕ, d ∣ 28 → d < 28 → 2 ^ d % 29 ≠ 1) ∧
    2 ^ 7 * 12 % 29 = 28 ∧
    (∀ m : ℕ, ¬ pellOrderMarginHit 41 29 8 7 m) := by
  constructor
  · norm_num
  constructor
  · intro d hd hlt
    interval_cases d <;> norm_num at *
  constructor
  · norm_num
  · intro m hhit
    have hm8 : m < 8 := by
      have hb := pellOrderMarginHit_exponent_bound 41 29 8 7 m (by norm_num) hhit
      by_contra hnot
      have hge : 8 ≤ m := by omega
      have hpow : 2 ^ 8 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hge
      norm_num at hb
      omega
    interval_cases m <;> norm_num [pellOrderMarginHit] at *

/-- At the q29 rational hit `m=7`, the convergent predicts the `111` cell,
but the exact sqrt(2) orbit is in `000`.  This explains the failed margin:
the approximation error crosses the upper endpoint. -/
@[blueprint (title := "A complete Pell residue period predicts the wrong binary word")]
theorem pell_order_q29_rational_hit_is_wrong_word :
    7 * 29 < 8 * (41 * 2 ^ 7 % 29) ∧
    41 * 2 ^ 7 % 29 < 29 ∧
    orbit 2 (Real.sqrt 2) 7 ∈ Set.Ioo (0 : ℝ) (1 / 8 : ℝ) := by
  have hcert : PellWordCertificate 3 0 7 3 4 9 := by
    norm_num [PellWordCertificate, pellWordNumerator, pellP, pellQ, pellPair]
  have hactual := pellWordCertificate_orbit_mem_Ioo hcert (by norm_num)
  norm_num at hactual
  refine ⟨by norm_num, by norm_num, ?_⟩
  simpa using hactual

end NormalNumbers.SqrtTwoRoutes
