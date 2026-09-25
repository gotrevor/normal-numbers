import NormalNumbers.ElliottCaseAThin
import NormalNumbers.ElliottProgression
import NormalNumbers.ElliottPretentiousTransfer
import NormalNumbers.ElliottRankin
import NormalNumbers.ElliottTruncAssemble

/-!
# Leaf 2: the assembly

This module assembles `Erdos67b.NonasymptoticLogElliott` from `AffineCMLogElliott`, i.e. it is the
former `NormalNumbers.ElliottLadder.nonasymptotic_of_affineCM`.  It lives here rather than in
`ElliottLadder` because it consumes `ElliottCaseAThin`, `ElliottSquarefullConv`,
`ElliottPretentiousTransfer` and `ElliottProgression`, all of which import `ElliottLadder`.

## The split, and why it is a split on ONE quantity

`ElliottEulerBound.primeDefect (normDivArith g₁) L = ∑_{p ≤ L} (1 − ‖g₁ p‖)/p` — the Euler-product
defect appearing in Case A is *literally* the Case-B sum `Σ_L(g₁)`.  So the dichotomy is
`le_or_lt` on a single real number, and `nonasymptotic_of_affineCM` below is **proved** from the
two halves, with no gap at the junction.

* `caseAScale a₁ b₁ X W` — the thin scale `L = a₁(⌊X/W⌋+1) − |b₁|`, the same `L` for both halves.
* `exists_caseA_thin_threshold` — Case A: defect large ⟹ done, for **all** `W`.
* `exists_caseB_threshold` — Case B: defect small ⟹ done, via cover + transfer + squarefull +
  progression.

## The obstruction found while assembling (lap 60) — now DISCHARGED (lap 62)

Case B expands `U₁(a₁n+b₁) = ∑_{d₁ ∣ a₁n+b₁} u₁(d₁) Ũ₁((a₁n+b₁)/d₁)` and applies
`AffineCMLogElliott` to each substituted pair `(a₁d₂, c₁; a₂d₁, c₂)`.  The determinant is preserved
exactly (`ElliottProgression.det_progression`), but the *dilations* `a₁d₂, a₂d₁` grow with `d₁,d₂`,
and `AffineCMLogElliott` produces its threshold `A₀` **per affine pair**.  So the `d`-sum must be
truncated at some `D` fixed before `g₁`, and `A₀` taken as the (finite) maximum over
`d₁, d₂ ≤ D` — which means Case B needs

> `exists_squarefull_tail` : for every `ε' > 0` there is a `D`, **independent of `U`**, with
> `∑_{D < d ≤ Y} ‖u d‖/d ≤ ε'` for every unimodular multiplicative `U` and every `Y`.

This is **strictly stronger** than `ElliottSquarefullConv.sum_norm_squarefullPart_div_le_exp_two`,
which bounds the *total* by `e²`.  A uniformly bounded total does not give uniformly small tails —
that is exactly the error that killed the `v`-expansion (`PENDING_WORK`, lap 54).  The difference
is that here it *is* true, and for a concrete reason: the local factors `1 + 2/(p(p−1))` are
absolute, so a Rankin shift is available —
`∑_{d > D} ‖u d‖/d ≤ D^{−1/4} ∑_d ‖u d‖/d^{3/4}` and the shifted Euler product
`∏_p (1 + ∑_{k ≥ 2} 2/p^{3k/4})` still converges, `3·2/4 = 3/2 > 1`.  So the obligation is real
work but not a wall; it is stated below and **proved** in `NormalNumbers.ElliottRankin`.
-/

open scoped BigOperators
open Finset

namespace NormalNumbers.ElliottLeafTwo

open Erdos67b ArithmeticFunction NormalNumbers.ElliottCaseA NormalNumbers.ElliottEulerBound
open NormalNumbers.ElliottLadder NormalNumbers.ElliottHall
open NormalNumbers.ElliottScaleWindow NormalNumbers.ElliottTruncScale
open NormalNumbers.ElliottTruncAssemble NormalNumbers.ElliottIterSqrt

noncomputable section

/-- The thin scale `L = a₁(⌊X/W⌋+1) − |b₁|`: the least value the affine form `a₁n+b₁` can take on
the window `X/W < n ≤ X`.  Both halves of the dichotomy are stated at this `L`. -/
def caseAScale (a₁ : ℕ) (b₁ : ℤ) (X W : ℕ) : ℕ := a₁ * (X / W + 1) - b₁.natAbs

/-! ## Half one: Case A (the defect is large) -/

/-- **Case A, all windows.**  If the Euler defect of `g₁` at the thin scale is at least `D₀` then
the correlation is already `≤ ε log W`, with `D₀` and `W₀` depending only on `(a₁, b₁, ε)`.

Proof (to be written): `ElliottCaseAThin.norm_elliottLogCorrelation_le_caseA_thin` gives
`‖corr‖ ≤ (a₁+|b₁|)(⌊log₂(Y/L)⌋+1)·2·hallConst·e^{1+B}·e^{−Σ_L} + |b₁|`.  It remains to bound
`Y/L ≤ c(a₁,b₁)·W`, so that `⌊log₂(Y/L)⌋+1 ≤ log W / log 2 + c'`, and then to choose
`D₀ = log(K/ε)` and `W₀` large enough to absorb the additive `|b₁|` and `c'`.  Both steps are the
same shape as the already-proved `ElliottCaseA.exists_caseA_threshold`; the only new ingredient is
the nat-division estimate `Y/L ≤ cW`. -/
theorem exists_caseA_thin_threshold {a₁ : ℕ} (ha₁ : 0 < a₁) (b₁ : ℤ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (D₀ : ℝ) (W₀ : ℕ), 2 ≤ W₀ ∧
      ∀ (g₁ g₂ : ℤ → ℂ), IsMultiplicativeOnPositiveInt g₁ →
        (∀ n : ℤ, ‖g₁ n‖ ≤ 1) → (∀ n : ℤ, ‖g₂ n‖ ≤ 1) →
        ∀ (a₂ : ℕ) (b₂ : ℤ) (X W : ℕ), W₀ ≤ W → W ≤ X →
          D₀ ≤ primeDefect (normDivArith g₁) (caseAScale a₁ b₁ X W) →
          ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W‖ ≤ ε * Real.log (W : ℝ) := by
  classical
  obtain ⟨D₀t, W₀t, hW₀t, hthick⟩ :=
    ElliottCaseA.exists_caseA_threshold ha₁ b₁ (θ := (1 : ℝ) / 2) (by norm_num) hε
  set b : ℕ := b₁.natAbs with hb
  set C : ℝ := ((a₁ + b : ℕ) : ℝ) with hC
  have hCpos : 0 < C := by
    rw [hC]; exact_mod_cast (by omega : 0 < a₁ + b)
  set κ : ℝ := 4 / Real.log 2 with hκ
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hκpos : 0 < κ := by rw [hκ]; positivity
  set E : ℝ := Real.exp (1 + Erdos67b.PrimeEstimates.mertensBound) with hE
  have hEpos : 0 < E := Real.exp_pos _
  set K : ℝ := C * (κ * (2 * hallConst * E)) with hK
  have hKpos : 0 < K := by
    rw [hK]; have := hallConst_pos; positivity
  refine ⟨max D₀t (Real.log (2 * K / ε)),
    max (max W₀t (2 * b + 3)) (max ((2 * b + 3) * (2 * b + 3))
      (⌈Real.exp (2 * (b : ℝ) / ε)⌉₊ + 2)), ?_, ?_⟩
  · exact le_trans (by omega) ((le_max_right _ _).trans (le_max_left _ _))
  intro g₁ g₂ hm₁ h₁ h₂ a₂ b₂ X W hW hWX hdefect
  have hW₀t : W₀t ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hWb : 2 * b + 3 ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hWsq : (2 * b + 3) * (2 * b + 3) ≤ W :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hWceil : ⌈Real.exp (2 * (b : ℝ) / ε)⌉₊ + 2 ≤ W :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  have hW2 : 2 ≤ W := by omega
  have hWpos : 0 < W := by omega
  have hX2 : 2 ≤ X := le_trans hW2 hWX
  have hlogW : 0 < Real.log (W : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < W))
  -- the constant remainder, shared by both branches
  have hrem : (b : ℝ) ≤ (ε / 2) * Real.log (W : ℝ) := by
    have hexpW : Real.exp (2 * (b : ℝ) / ε) ≤ (W : ℝ) := by
      refine le_trans (Nat.le_ceil _) ?_
      exact_mod_cast (by omega : ⌈Real.exp (2 * (b : ℝ) / ε)⌉₊ ≤ W)
    have hlog := Real.log_le_log (Real.exp_pos _) hexpW
    rw [Real.log_exp] at hlog
    have h2 := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ ε / 2)
    rw [show (ε / 2) * (2 * (b : ℝ) / ε) = (b : ℝ) by field_simp] at h2
    exact h2
  rcases le_or_gt (2 * b + 2) (X / W) with hq | hq
  · -- thin branch: the dyadic block count is `O(log W)`
    set q : ℕ := X / W with hqdef
    set L : ℕ := caseAScale a₁ b₁ X W with hLdef
    have hLeq : L = a₁ * (q + 1) - b := rfl
    have hbM : b + 1 ≤ a₁ * (q + 1) := by
      calc b + 1 ≤ q + 1 := by omega
        _ = 1 * (q + 1) := by ring
        _ ≤ a₁ * (q + 1) := Nat.mul_le_mul_right _ ha₁
    have hL1 : 1 ≤ L := by rw [hLeq]; omega
    have hratio : (a₁ * X + b) / L ≤ 4 * W :=
      ElliottCaseAThin.div_le_four_mul ha₁ hWpos hq
    -- the block count is at most `κ log W`
    have hcount : (((Nat.log 2 ((a₁ * X + b) / L) + 1 : ℕ)) : ℝ) ≤ κ * Real.log (W : ℝ) := by
      have h4W : Nat.log 2 ((a₁ * X + b) / L) ≤ Nat.log 2 (4 * W) :=
        Nat.log_mono_right hratio
      have h4 : Nat.log 2 (4 * W) = Nat.log 2 W + 2 := by
        have hw : W ≠ 0 := by omega
        have hw2 : W * 2 ≠ 0 := Nat.mul_ne_zero hw (by norm_num)
        have he : (4 : ℕ) * W = W * 2 * 2 := by ring
        rw [he, Nat.log_mul_base (by norm_num) hw2, Nat.log_mul_base (by norm_num) hw]
      have hNW : ((Nat.log 2 W : ℕ) : ℝ) ≤ Real.log (W : ℝ) / Real.log 2 := by
        rw [le_div_iff₀ hlog2]
        exact ElliottCaseAThin.natLog_mul_log_two_le (by omega)
      have h3 : (3 : ℝ) ≤ 3 * (Real.log (W : ℝ) / Real.log 2) := by
        have : (1 : ℝ) ≤ Real.log (W : ℝ) / Real.log 2 := by
          rw [le_div_iff₀ hlog2, one_mul]
          exact Real.log_le_log (by norm_num) (by exact_mod_cast hW2)
        linarith
      have hcast : (((Nat.log 2 ((a₁ * X + b) / L) + 1 : ℕ)) : ℝ) ≤ ((Nat.log 2 W : ℕ) : ℝ) + 3 := by
        have : Nat.log 2 ((a₁ * X + b) / L) + 1 ≤ Nat.log 2 W + 3 := by omega
        exact_mod_cast this
      rw [hκ]
      have : Real.log (W : ℝ) / Real.log 2 + 3 * (Real.log (W : ℝ) / Real.log 2)
          = 4 / Real.log 2 * Real.log (W : ℝ) := by field_simp; ring
      linarith [hcast, hNW, h3, this.le, this.ge]
    have hmaster := ElliottCaseAThin.norm_elliottLogCorrelation_le_caseA_thin
      hm₁ h₁ h₂ ha₁ b₁ a₂ b₂ (X := X) (W := W) hWpos (L := L) hL1 le_rfl
    have hexp : Real.exp (-primeDefect (normDivArith g₁) L) ≤ ε / (2 * K) := by
      have h1 : Real.exp (-primeDefect (normDivArith g₁) L) ≤
          Real.exp (-Real.log (2 * K / ε)) := by
        apply Real.exp_le_exp.mpr
        have := le_trans (le_max_right D₀t (Real.log (2 * K / ε))) hdefect
        linarith
      have h2 : Real.exp (-Real.log (2 * K / ε)) = ε / (2 * K) := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp
      linarith [h1, h2.le, h2.ge]
    have hexpnn : (0 : ℝ) ≤ Real.exp (-primeDefect (normDivArith g₁) L) := (Real.exp_pos _).le
    have hstep : C * ((((Nat.log 2 ((a₁ * X + b) / L) + 1 : ℕ)) : ℝ) *
        (2 * hallConst * E * Real.exp (-primeDefect (normDivArith g₁) L))) ≤
        (ε / 2) * Real.log (W : ℝ) := by
      have hh := hallConst_pos
      have h1 : C * ((((Nat.log 2 ((a₁ * X + b) / L) + 1 : ℕ)) : ℝ) *
          (2 * hallConst * E * Real.exp (-primeDefect (normDivArith g₁) L))) ≤
          C * ((κ * Real.log (W : ℝ)) * (2 * hallConst * E * (ε / (2 * K)))) := by
        gcongr
      refine h1.trans_eq ?_
      rw [hK]
      field_simp
    calc ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W‖
        ≤ C * ((((Nat.log 2 ((a₁ * X + b) / L) + 1 : ℕ)) : ℝ) *
            (2 * hallConst * E * Real.exp (-primeDefect (normDivArith g₁) L))) + (b : ℝ) := by
          rw [hC, hE, hb]; exact hmaster
      _ ≤ ε * Real.log (W : ℝ) := by linarith [hstep, hrem]
  · -- thick branch: `X/W` small forces `log X ≤ (3/2) log W`
    have hXlt : X < W * (2 * b + 3) := by
      have h1 : X < W * (X / W + 1) := ElliottCaseAThin.lt_mul_div_add_one hWpos
      have h2 : X / W + 1 ≤ 2 * b + 3 := by omega
      exact lt_of_lt_of_le h1 (Nat.mul_le_mul_left _ h2)
    have hthickineq : (1 / 2 : ℝ) * Real.log (X : ℝ) ≤ Real.log (W : ℝ) := by
      have hc : (X : ℝ) ≤ (W : ℝ) * ((2 * b + 3 : ℕ) : ℝ) := by
        have : (X : ℕ) ≤ W * (2 * b + 3) := hXlt.le
        exact_mod_cast this
      have hlogX : Real.log (X : ℝ) ≤ Real.log (W : ℝ) + Real.log ((2 * b + 3 : ℕ) : ℝ) := by
        have h0 : (0 : ℝ) < (W : ℝ) * ((2 * b + 3 : ℕ) : ℝ) := by
          have : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hWpos
          have : (0 : ℝ) < ((2 * b + 3 : ℕ) : ℝ) := by positivity
          positivity
        have := Real.log_le_log (by positivity : (0 : ℝ) < (X : ℝ)) hc
        rwa [Real.log_mul (by positivity) (by positivity)] at this
      have hsmall : Real.log ((2 * b + 3 : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * Real.log (W : ℝ) := by
        have hsq : (((2 * b + 3 : ℕ) : ℝ)) ^ 2 ≤ (W : ℝ) := by
          have : ((2 * b + 3) * (2 * b + 3) : ℕ) ≤ W := hWsq
          have := (Nat.cast_le (α := ℝ)).mpr this
          push_cast at this ⊢
          nlinarith [this]
        have := Real.log_le_log (by positivity) hsq
        rw [Real.log_pow] at this
        push_cast at this ⊢
        linarith
      linarith
    have hYdef : primeDefect (normDivArith g₁) (caseAScale a₁ b₁ X W) ≤
        primeDefect (normDivArith g₁) (a₁ * X + b₁.natAbs) := by
      refine ElliottHall.primeDefect_mono h₁ ?_
      have h1 : X / W + 1 ≤ X := by
        have : X / W ≤ X / 2 := Nat.div_le_div_left hW2 (by norm_num)
        omega
      have : a₁ * (X / W + 1) ≤ a₁ * X := Nat.mul_le_mul_left _ h1
      simp only [caseAScale]
      omega
    exact hthick g₁ g₂ hm₁ h₁ h₂ a₂ b₂ X W hW₀t hWX hthickineq
      (le_trans (le_trans (le_max_left D₀t _) hdefect) hYdef)

/-! ## The new obligation: a UNIFORMLY small squarefull tail -/

/-- **PROVED (lap 62, `ElliottRankin.exists_squarefull_tail_bound`).**  The squarefull tail is
uniformly small, with the truncation point `D` chosen **before** the function `U`.

This does *not* follow from `ElliottSquarefullConv.sum_norm_squarefullPart_div_le_exp_two` (a bound
on the total).  It is needed because `AffineCMLogElliott` hands out its threshold `A₀` per affine
pair, and the substituted pairs `(a₁d₂, a₂d₁)` grow with `d₁,d₂`, so only finitely many may be
used.  See this file's header for why it is nevertheless true: Rankin shift by `1/4`, the shifted
local factors `1 + ∑_{k≥2} 2/p^{3k/4}` still having a convergent prime sum since `3/2 > 1`.
That is exactly how it was proved. -/
theorem exists_squarefull_tail {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℕ, 1 ≤ D ∧
      ∀ U : ℕ → ℂ, U 1 = 1 →
        (∀ x y : ℕ, Nat.Coprime x y → U (x * y) = U x * U y) →
        (∀ n : ℕ, 0 < n → ‖U n‖ = 1) →
        ∀ Y : ℕ,
          ∑ d ∈ Finset.Icc (D + 1) Y,
              ‖NormalNumbers.ElliottSquarefullConv.squarefullPart U d‖ / (d : ℝ) ≤ ε :=
  NormalNumbers.ElliottRankin.exists_squarefull_tail_bound hε

/-! ## Half two: Case B (the defect is small) -/

/-- **Case B, all windows.**  If the Euler defect of `g₁` at the thin scale is at most `D₀` then the
correlation is `≤ ε log W`, given `AffineCMLogElliott`.

Route, now fully itemised, every ingredient proved except the two disclosed obligations:

1. `ElliottRandomize.exists_cover_pair_ge` — replace `g₁, g₂` by unimodular **multiplicative**
   `u₁, u₂` with a larger correlation, lifts of `g_i` at every prime `≤ Y`.  *Proved.*
2. `ElliottPretentiousTransfer.mrtNonpretentious_transfer` — carry the non-pretentiousness across,
   using the small defect: `MRTNonpretentious u₁ A' X` with `(A' : ℝ) ≤ A/3 − 2D₀`.  *Proved.*
3. `ElliottSquarefullConv.squarefullPart` — write `u_i = u_i' ⋆ cmExt u_i` with `cmExt u_i`
   unimodular **completely** multiplicative.  *Proved.*
4. `exists_squarefull_tail` — truncate the `(d₁,d₂)` sum at `D`, uniformly in `u_i`.  *Proved*
   (lap 62, by the Rankin shift).
5. `ElliottProgression.integerAffine_progression` + `det_progression` — for each `(d₁,d₂) ≤ D`,
   substitute `n = d₁d₂k + n₀` and apply `AffineCMLogElliott` to the pair `(a₁d₂, c₁; a₂d₁, c₂)`,
   whose determinant is *exactly* `a₁b₂ − a₂b₁ ≠ 0`.  Arithmetic *proved*; the window/weight
   reindexing (`X ↦ X/q` at fixed ratio, `1/(qk+n₀)` versus `1/(qk)`) is *open*.
6. `A₀ :=` the maximum of `h`'s thresholds over the finitely many pairs with `d₁, d₂ ≤ D`,
   together with the `A'` slack of step 2. -/
theorem exists_caseB_threshold (h : AffineCMLogElliott)
    {a₁ a₂ : ℕ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) {b₁ b₂ : ℤ}
    (hdet : (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ ≠ 0) {ε : ℝ} (hε : 0 < ε) (D₀ : ℝ) (k : ℕ) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧
      ∀ A X W : ℕ, A₀ ≤ A → A ≤ W → W ≤ X →
        X ≤ (thinScale a₁ b₁ X W) ^ (2 ^ k) →
        ∀ g₁ g₂ : ℤ → ℂ,
          IsMultiplicativeOnPositiveInt g₁ →
          IsMultiplicativeOnPositiveInt g₂ →
          (∀ n : ℤ, ‖g₁ n‖ ≤ 1) →
          (∀ n : ℤ, ‖g₂ n‖ ≤ 1) →
          (∀ q : ℕ, 0 < q → q ≤ A →
            ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
              |t| ≤ (A : ℝ) * X →
                (A : ℝ) ≤ pretentiousDistSqToTwist (restrictToNat g₁) χ t X) →
          primeDefect (normDivArith g₁) (thinScale a₁ b₁ X W) ≤ D₀ →
          ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W‖ ≤ ε * Real.log (W : ℝ) := by
  sorry

/-! ## The assembly -/

/-- **Leaf 2, assembled.**  `AffineCMLogElliott → NonasymptoticLogElliott`.

The proof is the dichotomy on the single real number `primeDefect (normDivArith g₁) L`, but at the
**truncated** window `W'' = truncRatio j X W` rather than at `W` — see `PENDING_WORK.md` (laps
71–75) for why.  In one line: Case A can only see the defect at the thin scale `L ≈ a₁X/W`, whereas
Case B's pretentious transfer needs it at `≈ X`, and the two differ by `≈ log(log X / log L)`,
which is unbounded when `W` is close to `X`.  Truncating the window from below at a `2^j`-th root
of `W` costs only `≤ 1 + 2log2 + (log W)/2^j ≤ (ε/2) log W` of harmonic mass and forces
`X ≤ L''^(2^(j+2))`, making the discrepancy an absolute constant in `ε`.

`j := max 1 ⌈8/ε⌉₊` works because `2^j ≥ j+1 ≥ 8/ε`. -/
theorem nonasymptotic_of_affineCM (h : AffineCMLogElliott) :
    Erdos67b.NonasymptoticLogElliott := by
  classical
  intro a₁ a₂ b₁ b₂ ha₁ ha₂ hdet ε hε
  set j : ℕ := max 1 ⌈8 / ε⌉₊ with hjdef
  have hj1 : 1 ≤ j := le_max_left _ _
  have hjpow : (8 : ℝ) / ε ≤ ((2 ^ j : ℕ) : ℝ) := by
    have h1 : (8 : ℝ) / ε ≤ (⌈(8 : ℝ) / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈(8 : ℝ) / ε⌉₊ : ℕ) ≤ j := le_max_right _ _
    have h3 : j + 1 ≤ 2 ^ j := Nat.succ_le_of_lt (Nat.lt_two_pow_self)
    have h4 : ((j : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast (by omega : j ≤ 2 ^ j)
    have h5 : ((⌈(8 : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast h2
    linarith
  obtain ⟨D₀, W₀, hW₀, hA⟩ := exists_caseA_thin_threshold ha₁ b₁ (ε := ε / 2) (by positivity)
  obtain ⟨A₀, hA₀, hB⟩ :=
    exists_caseB_threshold h ha₁ ha₂ hdet (ε := ε / 2) (by positivity) D₀ (j + 2)
  set c₁ : ℕ := 2 * (b₁.natAbs + 1) ^ 2 with hc₁
  set M₂ : ℕ := ⌈Real.exp (4 * (1 + 2 * Real.log 2) / ε)⌉₊ + 1 with hM₂
  refine ⟨max (max 4 (c₁ ^ (2 ^ j))) (max (W₀ * W₀ + A₀ * A₀) M₂), ?_, ?_⟩
  · exact le_trans (by omega) (le_max_left _ _)
  intro A X W hNA hAW hWX g₁ g₂ hm₁ hm₂ h₁ h₂ hpret
  have hNW : max (max 4 (c₁ ^ (2 ^ j))) (max (W₀ * W₀ + A₀ * A₀) M₂) ≤ W := le_trans hNA hAW
  have hW4 : 4 ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hNW
  have hWc₁ : c₁ ^ (2 ^ j) ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hNW
  have hWsq : W₀ * W₀ + A₀ * A₀ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hNW
  have hWM₂ : M₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hNW
  have hsqA₀ : A₀ ≤ A₀ * A₀ := Nat.le_mul_of_pos_left _ (by omega)
  have hsqW₀ : W₀ ≤ W₀ * W₀ := Nat.le_mul_of_pos_left _ (by omega)
  have hNA' : W₀ * W₀ + A₀ * A₀ ≤ A :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hNA
  have hA₀A : A₀ ≤ A := by omega
  -- the truncated window
  set W'' : ℕ := truncRatio j X W with hW''def
  have hW''le : W'' ≤ W := truncRatio_le j X W
  have hW''pos : 0 < W'' := truncRatio_pos hW4 hWX hj1
  have hsqle : Nat.sqrt W ≤ W'' := sqrt_le_truncRatio hj1 hW4 hWX
  have hW₀W'' : W₀ ≤ W'' := by
    have : W₀ ≤ Nat.sqrt W := Nat.le_sqrt'.mpr (by rw [pow_two]; exact le_trans (Nat.le_add_right _ _) hWsq)
    omega
  have hA₀W'' : A₀ ≤ W'' := by
    have : A₀ ≤ Nat.sqrt W := Nat.le_sqrt'.mpr (by rw [pow_two]; exact le_trans (Nat.le_add_left _ _) hWsq)
    omega
  have hW''X : W'' ≤ X := le_trans hW''le hWX
  have hlogW : 0 < Real.log (W : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < W))
  have hlogW'' : Real.log (W'' : ℝ) ≤ Real.log (W : ℝ) := by
    refine Real.log_le_log (by exact_mod_cast hW''pos) ?_
    exact_mod_cast hW''le
  have hlogW''nn : 0 ≤ Real.log (W'' : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ W''))
  -- the discarded mass is at most `(ε/2) log W`
  have hmassbd : ∑ m ∈ Finset.Icc (X / W + 1) (X / W''), (m : ℝ)⁻¹ ≤ (ε / 2) * Real.log (W : ℝ) := by
    refine le_trans (discarded_mass_bound hW4 hWX hj1) ?_
    have hconst : (1 : ℝ) + 2 * Real.log 2 ≤ (ε / 4) * Real.log (W : ℝ) := by
      have hexp : Real.exp (4 * (1 + 2 * Real.log 2) / ε) ≤ (W : ℝ) := by
        refine le_trans (Nat.le_ceil _) ?_
        exact_mod_cast (by omega : ⌈Real.exp (4 * (1 + 2 * Real.log 2) / ε)⌉₊ ≤ W)
      have hlog := Real.log_le_log (Real.exp_pos _) hexp
      rw [Real.log_exp] at hlog
      have h2 := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ ε / 4)
      rwa [show (ε / 4) * (4 * (1 + 2 * Real.log 2) / ε) = 1 + 2 * Real.log 2 by field_simp] at h2
    have hquot : Real.log (W : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ (ε / 8) * Real.log (W : ℝ) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ))]
      have hmul : (8 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) * ε := by
        have h := mul_le_mul_of_nonneg_right hjpow hε.le
        rwa [div_mul_cancel₀ _ (ne_of_gt hε)] at h
      have hnn : (0 : ℝ) ≤ (((2 ^ j : ℕ) : ℝ) * ε - 8) * Real.log (W : ℝ) :=
        mul_nonneg (by linarith) hlogW.le
      nlinarith [hnn]
    have hslack : (0 : ℝ) ≤ (ε / 8) * Real.log (W : ℝ) := by positivity
    linarith
  have htrunc := NormalNumbers.ElliottWindowTruncate.norm_le_truncated h₁ h₂ a₁ a₂ b₁ b₂
    (X := X) (W := W) (W'' := W'') hW''pos hW''le
  -- the dichotomy, at the truncated window
  have hdefeq : primeDefect (normDivArith g₁) (thinScale a₁ b₁ X W'')
      = primeDefect (normDivArith g₁) (caseAScale a₁ b₁ X W'') :=
    primeDefect_thinScale_eq (normDivArith g₁) (a₁ := a₁) b₁ X W''
  have hbranch : ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W''‖ ≤ (ε / 2) * Real.log (W : ℝ) := by
    rcases le_or_gt (primeDefect (normDivArith g₁) (thinScale a₁ b₁ X W'')) D₀ with hsmall | hlarge
    · -- Case B, at `A'' = min A W''`
      set A'' : ℕ := min A W'' with hA''
      have hA₀A'' : A₀ ≤ A'' := le_min hA₀A hA₀W''
      have hA''A : A'' ≤ A := min_le_left _ _
      have hA''W'' : A'' ≤ W'' := min_le_right _ _
      have hpret'' : ∀ q : ℕ, 0 < q → q ≤ A'' →
          ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, |t| ≤ (A'' : ℝ) * X →
            (A'' : ℝ) ≤ pretentiousDistSqToTwist (restrictToNat g₁) χ t X := by
        intro q hq hqA χ t ht
        have hA''R : (A'' : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA''A
        have ht' : |t| ≤ (A : ℝ) * X := by
          refine le_trans ht ?_
          exact mul_le_mul_of_nonneg_right hA''R (Nat.cast_nonneg _)
        exact le_trans hA''R (hpret q hq (le_trans hqA hA''A) χ t ht')
      have hpow : X ≤ (thinScale a₁ b₁ X W'') ^ (2 ^ (j + 2)) := by
        refine X_le_thinScale_pow ha₁ b₁ hW4 hWX hj1 ?_
        -- `iterSqrt j W ≥ c₁` because `W ≥ c₁^(2^j)`
        by_contra hc
        push_neg at hc
        have h1 : iterSqrt j W + 1 ≤ c₁ := by omega
        have h2 : W < (iterSqrt j W + 1) ^ (2 ^ j) := lt_iterSqrt_succ_pow j W
        have h3 : (iterSqrt j W + 1) ^ (2 ^ j) ≤ c₁ ^ (2 ^ j) := Nat.pow_le_pow_left h1 _
        omega
      refine le_trans (hB A'' X W'' hA₀A'' hA''W'' hW''X hpow g₁ g₂ hm₁ hm₂ h₁ h₂ hpret'' hsmall)
        (mul_le_mul_of_nonneg_left hlogW'' (by positivity))
    · -- Case A
      refine le_trans (hA g₁ g₂ hm₁ h₁ h₂ a₂ b₂ X W'' hW₀W'' hW''X ?_) ?_
      · rw [← hdefeq]; exact hlarge.le
      · exact mul_le_mul_of_nonneg_left hlogW'' (by positivity)
  calc ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W‖
      ≤ ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W''‖
        + ∑ m ∈ Finset.Icc (X / W + 1) (X / W''), (m : ℝ)⁻¹ := htrunc
    _ ≤ (ε / 2) * Real.log (W : ℝ) + (ε / 2) * Real.log (W : ℝ) := by linarith
    _ = ε * Real.log (W : ℝ) := by ring

end

end NormalNumbers.ElliottLeafTwo
