/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ZeroOneBases
import NormalNumbers.Furstenberg

/-!
# `JointSlopeIndependence` is a four exponentials instance

`/create` follow-up, 2026-10-10.  The base-3 lever for 82000 (`ZeroOneBases.lean`, "What the
base-3 restriction buys") needs the length orbit `L ↦ (L log₃ 4, L log₅ 4)` to equidistribute in
`𝕋²`, i.e. `JointSlopeIndependence`.  Literature check: a relation
`p + q log₃ 4 + r log₅ 4 = 0` with `r ≠ 0` puts `t = r log₅ 4` (irrational) next to
`y = (log 3, log 5)` with all four of `e^{log 3}, e^{log 5}, e^{t log 3} = 3^{-p} 4^{-q},
e^{t log 5} = 4^r` rational, which is exactly what the four exponentials conjecture forbids.  The
`r = 0` case is unique factorization.  So the premise is **conditional on an open conjecture**
(Schneider 1957, Lang 1966; it follows from Schanuel), and is not a Baker-type statement: the
relation is a homogeneous *quadratic* form `p log 3 log 5 + q log 4 log 5 + r log 3 log 4`, and
linear forms in logarithms do not reach it.  The six exponentials theorem needs a third
independent `y`, which this single relation does not supply.

* `fourExponentials_jointSlopeIndependence`: the reduction, axiom-clean.
* The base-3 lever therefore sits behind four exponentials *and* a shrinking-target statement
  (targets of area `≈ 0.545^d`), and equidistribution alone gives no such statement.
-/

namespace NormalNumbers.ZeroOneBases

open Complex Furstenberg

/-- **Four exponentials conjecture** (open; Schneider 1957, Lang 1966; follows from Schanuel's
conjecture, Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups* (2000),
Exercise 1.8).  Wording as in google-deepmind/formal-conjectures
`FormalConjectures/Wikipedia/Exponentials.lean` (`Exponentials.four_exponentials_conjecture`),
the same statement `lean-formalizations` carries: if `x₀, x₁` and `y₀, y₁` are each
`ℚ`-linearly independent, some `e^{xᵢ yⱼ}` is transcendental. -/
def FourExponentialsConjecture : Prop :=
  ∀ (x : Fin 2 → ℂ) (y : Fin 2 → ℂ), LinearIndependent ℚ x → LinearIndependent ℚ y →
    ∃ i j : Fin 2, Transcendental ℚ (exp (x i * y j))

/-- Coprime bases `≥ 2` are multiplicatively independent. -/
theorem multIndep_of_coprime {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (h : Nat.Coprime p q) :
    MultIndep p q := by
  intro a b hab
  have ha : a = 0 := by
    by_contra ha
    have hdvd : p ∣ q ^ b := hab ▸ dvd_pow_self p ha
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right b h) hdvd
    omega
  subst ha
  refine ⟨rfl, ?_⟩
  exact (Nat.pow_eq_one.mp hab.symm).resolve_left (by omega)

theorem irrational_log_div_log_of_coprime {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h : Nat.Coprime p q) : Irrational (Real.log p / Real.log q) :=
  (multIndep_of_coprime hp hq h).irrational_log_div_log hp hq

/-- `1, x` are `ℚ`-independent in `ℂ` for irrational real `x`. -/
theorem linearIndependent_one_ofReal {x : ℝ} (hx : Irrational x) :
    LinearIndependent ℚ ![(1 : ℂ), (x : ℂ)] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  simp only [Rat.smul_def] at hst
  have hre := congrArg Complex.re hst
  simp at hre
  by_cases ht : t = 0
  · subst ht; simp at hre ⊢; exact hre
  · exfalso
    apply hx.ne_rat (-s / t)
    push_cast
    field_simp at hre ⊢
    linarith [hre]

/-- `a, b > 0` with `a / b` irrational are `ℚ`-independent in `ℂ`. -/
theorem linearIndependent_pair_ofReal {a b : ℝ} (hb : 0 < b) (hab : Irrational (a / b)) :
    LinearIndependent ℚ ![(a : ℂ), (b : ℂ)] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  simp only [Rat.smul_def] at hst
  have hre := congrArg Complex.re hst
  simp at hre
  by_cases hs : s = 0
  · subst hs; simp at hre ⊢; exact hre.resolve_right hb.ne'
  · exfalso
    apply hab.ne_rat (-t / s)
    push_cast
    field_simp at hre ⊢
    linarith [hre]

/-- `e^{z}` for `z = log` of a positive rational is algebraic. -/
theorem isAlgebraic_exp_log_rat (c : ℚ) (hc : 0 < c) :
    IsAlgebraic ℚ (exp ((Real.log (c : ℝ) : ℝ) : ℂ)) := by
  rw [← Complex.ofReal_exp, Real.exp_log (by exact_mod_cast hc)]
  have : ((c : ℝ) : ℂ) = algebraMap ℚ ℂ c := by simp
  rw [this]
  exact isAlgebraic_algebraMap c

/-- **The literature check, as a theorem**: `JointSlopeIndependence` is an instance of the four
exponentials conjecture. -/
theorem fourExponentials_jointSlopeIndependence (h4 : FourExponentialsConjecture) :
    JointSlopeIndependence := by
  intro p q r hrel
  have l3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have l4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have l5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hr : r = 0 := by
    by_contra hr
    set t : ℝ := r * (Real.log 4 / Real.log 5) with ht
    have hirr45 : Irrational (Real.log 4 / Real.log 5) := by
      simpa using irrational_log_div_log_of_coprime (p := 4) (q := 5) (by norm_num) (by norm_num)
        (by norm_num)
    have htirr : Irrational t := hirr45.intCast_mul hr
    have hirr35 : Irrational (Real.log 3 / Real.log 5) := by
      simpa using irrational_log_div_log_of_coprime (p := 3) (q := 5) (by norm_num) (by norm_num)
        (by norm_num)
    -- the two products that are not plain `log 3`, `log 5`
    have e3 : t * Real.log 3 = Real.log ((3 : ℚ) ^ (-p) * (4 : ℚ) ^ (-q) : ℚ) := by
      have hq : (r : ℝ) * (Real.log 4 / Real.log 5) = -p - q * (Real.log 4 / Real.log 3) := by
        linarith
      push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_zpow, Real.log_zpow, ht, hq]
      field_simp
      push_cast
      ring
    have e5 : t * Real.log 5 = Real.log ((4 : ℚ) ^ r : ℚ) := by
      push_cast
      rw [Real.log_zpow, ht]
      field_simp
    obtain ⟨i, j, htr⟩ := h4 ![(1 : ℂ), (t : ℂ)] ![(Real.log 3 : ℂ), (Real.log 5 : ℂ)]
      (linearIndependent_one_ofReal htirr) (linearIndependent_pair_ofReal l5 hirr35)
    apply htr
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, one_mul]
    · simpa using isAlgebraic_exp_log_rat 3 (by norm_num)
    · simpa using isAlgebraic_exp_log_rat 5 (by norm_num)
    · rw [← Complex.ofReal_mul, e3]
      exact isAlgebraic_exp_log_rat _ (by positivity)
    · rw [← Complex.ofReal_mul, e5]
      exact isAlgebraic_exp_log_rat _ (by positivity)
  subst hr
  have hirr43 : Irrational (Real.log 4 / Real.log 3) := by
    simpa using irrational_log_div_log_of_coprime (p := 4) (q := 3) (by norm_num) (by norm_num)
      (by norm_num)
  have hq : q = 0 := by
    by_contra hq
    apply hirr43.ne_rat (-p / q)
    push_cast
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    simp at hrel
    have h' : (p : ℝ) * Real.log 3 + q * Real.log 4 = 0 := by
      have : (p : ℝ) * Real.log 3 + q * Real.log 4 =
          (p + q * (Real.log 4 / Real.log 3)) * Real.log 3 := by
        field_simp
      rw [this, hrel, zero_mul]
    field_simp
    linear_combination h'
  subst hq
  simp at hrel
  exact ⟨by exact_mod_cast hrel, rfl, rfl⟩

end NormalNumbers.ZeroOneBases
