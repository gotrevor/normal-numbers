import NormalNumbers.ElliottSquarefull

/-!
# The squarefull convolution `u = μŨ ⋆ U`

Leaf 2, Case B, step (3) of the `DIRECTION.md` CURRENT DIRECTIVE — the *arithmetic* half.
`ElliottSquarefull.lean` proved the analytic half (`∑_{m ≤ Y} f m ≤ e²` for any nonnegative
multiplicative `f` vanishing at the primes with `f n ≤ 2/n`).  This file produces such an `f`.

Given a unimodular multiplicative `U`, let `cmExt U` be the **completely** multiplicative function
agreeing with `U` at the primes, `cmExt U n = ∏_{p^k ‖ n} (U p)^k`, and set

`u = (μ · cmExt U) ⋆ U`,  so that  `U = u ⋆ cmExt U`.

Then `u` is multiplicative, and at prime powers

`u 1 = 1`,  `u p = U p - U p = 0`,  `u (p^k) = U (p^k) - U p · U (p^(k-1))`  (`k ≥ 1`),

so `‖u (p^k)‖ ≤ 2` and `u` is supported on squarefull integers.  Hence `n ↦ ‖u n‖ / n` meets the
hypotheses of `ElliottSquarefull.sum_Icc_le_exp_two` exactly, and
`∑_{d ≤ Y} ‖u d‖ / d ≤ e²` **uniformly in `U` and `Y`**.

Note that `cmExt U` agrees with `U` at every prime, so all pretentious distances are untouched:
`pretentiousDistSq (cmExt U) h X = pretentiousDistSq U h X`, since `pretentiousDistSq` is a sum
over primes only.  The transfer proved in `ElliottPretentiousTransfer.lean` therefore survives the
expansion verbatim.

## Main results

* `cmExt` — the completely multiplicative extension; `cmExt_prime_pow`, `isMultiplicative_cmExt`.
* `squarefullPart` — `u`; `squarefullPart_prime_pow`, `norm_squarefullPart_le_two`,
  `squarefullPart_prime_eq_zero`.
* `sum_norm_squarefullPart_div_le_exp_two` — **`∑_{d ≤ Y} ‖u d‖/d ≤ e²`, absolutely.**
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace NormalNumbers.ElliottSquarefullConv

open ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.Moebius

noncomputable section

/-! ## A divisor-sum form of Dirichlet convolution -/

theorem mul_apply_divisors {R : Type*} [Semiring R] (f g : ArithmeticFunction R) (n : ℕ) :
    (f * g) n = ∑ d ∈ n.divisors, f d * g (n / d) := by
  rw [ArithmeticFunction.mul_apply, ← Nat.map_div_right_divisors, Finset.sum_map]
  rfl

/-! ## The completely multiplicative extension -/

/-- The completely multiplicative function agreeing with `U` at the primes. -/
def cmExt (U : ℕ → ℂ) : ArithmeticFunction ℂ where
  toFun n := if n = 0 then 0 else n.factorization.prod fun p k => U p ^ k
  map_zero' := by simp

theorem cmExt_apply {U : ℕ → ℂ} {n : ℕ} (hn : n ≠ 0) :
    cmExt U n = n.factorization.prod fun p k => U p ^ k := by
  simp [cmExt, hn]

@[simp] theorem cmExt_one (U : ℕ → ℂ) : cmExt U 1 = 1 := by
  rw [cmExt_apply one_ne_zero]
  simp

theorem cmExt_mul (U : ℕ → ℂ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    cmExt U (m * n) = cmExt U m * cmExt U n := by
  rw [cmExt_apply (Nat.mul_ne_zero hm hn), cmExt_apply hm, cmExt_apply hn,
    Nat.factorization_mul hm hn]
  exact Finsupp.prod_add_index' (fun p => pow_zero (U p)) (fun p a b => pow_add (U p) a b)

theorem isMultiplicative_cmExt (U : ℕ → ℂ) : (cmExt U).IsMultiplicative := by
  refine ⟨cmExt_one U, fun {m n} _ => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp [cmExt]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [cmExt]
  exact cmExt_mul U hm hn

theorem cmExt_prime_pow {U : ℕ → ℂ} {p : ℕ} (hp : p.Prime) (k : ℕ) :
    cmExt U (p ^ k) = U p ^ k := by
  rw [cmExt_apply (pow_ne_zero k hp.ne_zero), Nat.Prime.factorization_pow hp]
  simp [Finsupp.prod_single_index]

theorem norm_cmExt {U : ℕ → ℂ} (hU : ∀ p : ℕ, p.Prime → ‖U p‖ = 1) {n : ℕ} (hn : n ≠ 0) :
    ‖cmExt U n‖ = 1 := by
  rw [cmExt_apply hn, Finsupp.prod, norm_prod]
  refine Finset.prod_eq_one fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
  rw [norm_pow, hU p hpp, one_pow]

/-! ## The squarefull part -/

variable (U : ℕ → ℂ)

/-- The arithmetic-function packaging of `U` (value `0` at `0`). -/
def toAF (U : ℕ → ℂ) : ArithmeticFunction ℂ where
  toFun n := if n = 0 then 0 else U n
  map_zero' := by simp

@[simp] theorem toAF_apply {n : ℕ} (hn : n ≠ 0) : toAF U n = U n := by simp [toAF, hn]

/-- **The squarefull part** `u = (μ · Ũ) ⋆ U`, where `Ũ = cmExt U`.  It satisfies
`U = u ⋆ Ũ`, is supported on squarefull integers, and is `2`-bounded. -/
def squarefullPart (U : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ((μ : ArithmeticFunction ℂ).pmul (cmExt U)) * toAF U

theorem isMultiplicative_squarefullPart (hone : U 1 = 1)
    (hmul : ∀ x y : ℕ, Nat.Coprime x y → U (x * y) = U x * U y) :
    (squarefullPart U).IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.mul ?_ ?_
  · exact (isMultiplicative_moebius.intCast).pmul (isMultiplicative_cmExt U)
  · refine ⟨by simpa using hone, fun {m n} hcop => ?_⟩
    rcases eq_or_ne m 0 with rfl | hm
    · simp [toAF]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [toAF]
    rw [toAF_apply _ (Nat.mul_ne_zero hm hn), toAF_apply _ hm, toAF_apply _ hn]
    exact hmul m n hcop

/-- **The prime-power values.**  The `μ`-factor kills every exponent `≥ 2`, leaving two terms. -/
theorem squarefullPart_prime_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    squarefullPart U (p ^ k) = U (p ^ k) - U p * U (p ^ (k - 1)) := by
  classical
  have hpne : p ≠ 0 := hp.ne_zero
  set F : ℕ → ℂ := fun d =>
    ((μ : ArithmeticFunction ℂ).pmul (cmExt U)) d * toAF U (p ^ k / d) with hF
  rw [squarefullPart, mul_apply_divisors, Nat.sum_divisors_prime_pow hp (f := F)]
  have hdiv : ∀ i, i ≤ k → p ^ k / p ^ i = p ^ (k - i) := fun i hik =>
    Nat.pow_div hik hp.pos
  have h0 : F (p ^ 0) = U (p ^ k) := by
    rw [hF]
    simp only [pow_zero]
    rw [ArithmeticFunction.pmul_apply]
    rw [show p ^ k / 1 = p ^ k from Nat.div_one _, toAF_apply _ (pow_ne_zero _ hpne)]
    simp
  have h1 : F (p ^ 1) = -(U p * U (p ^ (k - 1))) := by
    rw [hF]
    simp only
    rw [ArithmeticFunction.pmul_apply, hdiv 1 hk,
      toAF_apply _ (pow_ne_zero _ hpne), pow_one]
    have hcm : cmExt U p = U p := by
      have := cmExt_prime_pow (U := U) hp 1
      simpa using this
    rw [hcm]
    have hmu : ((μ : ArithmeticFunction ℂ)) p = -1 := by
      simp [ArithmeticFunction.intCoe_apply, ArithmeticFunction.moebius_apply_prime hp]
    rw [hmu]
    ring
  have htail : ∀ i ∈ Finset.Ico 2 (k + 1), F (p ^ i) = 0 := by
    intro i hi
    have hi2 : 2 ≤ i := (Finset.mem_Ico.mp hi).1
    have hmz : (μ : ArithmeticFunction ℂ) (p ^ i) = 0 := by
      have hns : ¬ Squarefree (p ^ i) := by
        intro hsq
        have := (Nat.squarefree_pow_iff hp.ne_one (by omega)).mp hsq
        omega
      have := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns
      simp [ArithmeticFunction.intCoe_apply, this]
    rw [hF]
    simp only
    rw [ArithmeticFunction.pmul_apply, hmz, zero_mul, zero_mul]
  have hsplit : Finset.range (k + 1) = {0, 1} ∪ Finset.Ico 2 (k + 1) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_Ico]
    omega
  have hdisj : Disjoint ({0, 1} : Finset ℕ) (Finset.Ico 2 (k + 1)) := by
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton, Finset.mem_Ico]
    omega
  rw [hsplit, Finset.sum_union hdisj, Finset.sum_eq_zero htail, add_zero,
    Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1), h0, h1]
  ring

/-- `u p = 0`: the squarefull support. -/
theorem squarefullPart_prime_eq_zero (hone : U 1 = 1) {p : ℕ} (hp : p.Prime) :
    squarefullPart U p = 0 := by
  have h := squarefullPart_prime_pow U hp (k := 1) le_rfl
  simp only [pow_one, Nat.sub_self, pow_zero, hone, mul_one] at h
  simpa using h

/-- `‖u (p^k)‖ ≤ 2` for a unimodular `U` — the `2`-boundedness. -/
theorem norm_squarefullPart_prime_pow_le_two (hU : ∀ n : ℕ, 0 < n → ‖U n‖ = 1)
    {p : ℕ} (hp : p.Prime) (k : ℕ) : ‖squarefullPart U (p ^ k)‖ ≤ 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, squarefullPart]
    have : ((μ : ArithmeticFunction ℂ).pmul (cmExt U) * toAF U) 1
        = ((μ : ArithmeticFunction ℂ).pmul (cmExt U)) 1 * toAF U 1 :=
      ArithmeticFunction.mul_apply_one
    rw [this, ArithmeticFunction.pmul_apply, toAF_apply _ one_ne_zero]
    have h1 : ‖U 1‖ = 1 := hU 1 Nat.one_pos
    simp only [ArithmeticFunction.intCoe_apply, ArithmeticFunction.moebius_apply_one,
      cmExt_one, norm_mul]
    rw [h1]
    norm_num
  · rw [squarefullPart_prime_pow U hp hk]
    have h1 : ‖U (p ^ k)‖ = 1 := hU _ (pow_pos hp.pos k)
    have h2 : ‖U p‖ = 1 := hU p hp.pos
    have h3 : ‖U (p ^ (k - 1))‖ = 1 := hU _ (pow_pos hp.pos _)
    calc ‖U (p ^ k) - U p * U (p ^ (k - 1))‖
        ≤ ‖U (p ^ k)‖ + ‖U p * U (p ^ (k - 1))‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_mul, h1, h2, h3]; norm_num

/-! ## The absolute tail bound -/

/-- `n ↦ ‖u n‖ / n`, as an arithmetic function. -/
def normDivAF (u : ArithmeticFunction ℂ) : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else ‖u n‖ / (n : ℝ)
  map_zero' := by simp

theorem normDivAF_apply (u : ArithmeticFunction ℂ) {n : ℕ} (hn : n ≠ 0) :
    normDivAF u n = ‖u n‖ / (n : ℝ) := by simp [normDivAF, hn]

theorem normDivAF_nonneg (u : ArithmeticFunction ℂ) (n : ℕ) : 0 ≤ normDivAF u n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [normDivAF]
  · rw [normDivAF_apply u hn]
    positivity

theorem isMultiplicative_normDivAF {u : ArithmeticFunction ℂ} (hu : u.IsMultiplicative) :
    (normDivAF u).IsMultiplicative := by
  refine ⟨?_, fun {m n} hcop => ?_⟩
  · rw [normDivAF_apply u one_ne_zero, hu.map_one]
    norm_num
  · rcases eq_or_ne m 0 with rfl | hm
    · simp [normDivAF]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [normDivAF]
    rw [normDivAF_apply u (Nat.mul_ne_zero hm hn), normDivAF_apply u hm,
      normDivAF_apply u hn, hu.map_mul_of_coprime hcop, norm_mul]
    push_cast
    field_simp

/-- **The absolute squarefull tail bound.**  For every unimodular multiplicative `U` and every
scale `Y`, `∑_{d ≤ Y} ‖u d‖ / d ≤ e²`, where `u = (μ · cmExt U) ⋆ U`.

This is the uniformity that the refuted `‖g̃‖ = 1 ⋆ v` expansion could not deliver: the bound
depends on *nothing* — not on `U`, not on `Y`. -/
theorem sum_norm_squarefullPart_div_le_exp_two (hone : U 1 = 1)
    (hmul : ∀ x y : ℕ, Nat.Coprime x y → U (x * y) = U x * U y)
    (hU : ∀ n : ℕ, 0 < n → ‖U n‖ = 1) (Y : ℕ) :
    ∑ d ∈ Finset.Icc 1 Y, ‖squarefullPart U d‖ / (d : ℝ) ≤ Real.exp 2 := by
  classical
  have hmulu : (squarefullPart U).IsMultiplicative :=
    isMultiplicative_squarefullPart U hone hmul
  have hf := isMultiplicative_normDivAF hmulu
  have heq : ∑ d ∈ Finset.Icc 1 Y, ‖squarefullPart U d‖ / (d : ℝ)
      = ∑ d ∈ Finset.Icc 1 Y, normDivAF (squarefullPart U) d := by
    refine Finset.sum_congr rfl fun d hd => ?_
    have : d ≠ 0 := by have := (Finset.mem_Icc.mp hd).1; omega
    rw [normDivAF_apply _ this]
  rw [heq]
  refine NormalNumbers.ElliottSquarefull.sum_Icc_le_exp_two hf
    (normDivAF_nonneg _) ?_ ?_ Y
  · intro q hq k
    have hqk : (q ^ k : ℕ) ≠ 0 := pow_ne_zero k hq.ne_zero
    rw [normDivAF_apply _ hqk]
    have hcast : ((q ^ k : ℕ) : ℝ) = (q : ℝ) ^ k := by push_cast; ring
    rw [hcast]
    have hpos : (0 : ℝ) < (q : ℝ) ^ k := by
      have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
      positivity
    gcongr
    exact norm_squarefullPart_prime_pow_le_two U hU hq k
  · intro p hp
    rw [normDivAF_apply _ hp.ne_zero, squarefullPart_prime_eq_zero U hone hp]
    simp

end

end NormalNumbers.ElliottSquarefullConv
