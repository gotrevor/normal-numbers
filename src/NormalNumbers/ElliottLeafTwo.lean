import NormalNumbers.ElliottCaseAThin
import NormalNumbers.ElliottProgression
import NormalNumbers.ElliottPretentiousTransfer
import NormalNumbers.ElliottRankin

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
open NormalNumbers.ElliottLadder

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
  sorry

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
    (hdet : (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ ≠ 0) {ε : ℝ} (hε : 0 < ε) (D₀ : ℝ) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧
      ∀ A X W : ℕ, A₀ ≤ A → A ≤ W → W ≤ X →
        ∀ g₁ g₂ : ℤ → ℂ,
          IsMultiplicativeOnPositiveInt g₁ →
          IsMultiplicativeOnPositiveInt g₂ →
          (∀ n : ℤ, ‖g₁ n‖ ≤ 1) →
          (∀ n : ℤ, ‖g₂ n‖ ≤ 1) →
          (∀ q : ℕ, 0 < q → q ≤ A →
            ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
              |t| ≤ (A : ℝ) * X →
                (A : ℝ) ≤ pretentiousDistSqToTwist (restrictToNat g₁) χ t X) →
          primeDefect (normDivArith g₁) (caseAScale a₁ b₁ X W) ≤ D₀ →
          ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W‖ ≤ ε * Real.log (W : ℝ) := by
  sorry

/-! ## The assembly -/

/-- **Leaf 2, assembled.**  `AffineCMLogElliott → NonasymptoticLogElliott`.

This proof has **no gap of its own**: it is exactly the dichotomy on the single real number
`primeDefect (normDivArith g₁) (caseAScale a₁ b₁ X W)`, plus the bookkeeping that makes `W ≥ W₀`
available (from `W₀ ≤ A₀' ≤ A ≤ W`).  Everything else is delegated to the two halves. -/
theorem nonasymptotic_of_affineCM (h : AffineCMLogElliott) :
    Erdos67b.NonasymptoticLogElliott := by
  intro a₁ a₂ b₁ b₂ ha₁ ha₂ hdet ε hε
  obtain ⟨D₀, W₀, hW₀, hA⟩ := exists_caseA_thin_threshold ha₁ b₁ hε
  obtain ⟨A₀, hA₀, hB⟩ := exists_caseB_threshold h ha₁ ha₂ hdet hε D₀
  refine ⟨max A₀ W₀, le_trans hA₀ (le_max_left _ _), ?_⟩
  intro A X W hAA hAW hWX g₁ g₂ hm₁ hm₂ h₁ h₂ hpret
  have hW₀W : W₀ ≤ W := le_trans (le_trans (le_max_right A₀ W₀) hAA) hAW
  have hA₀A : A₀ ≤ A := le_trans (le_max_left A₀ W₀) hAA
  rcases le_or_gt (primeDefect (normDivArith g₁) (caseAScale a₁ b₁ X W)) D₀ with hsmall | hlarge
  · exact hB A X W hA₀A hAW hWX g₁ g₂ hm₁ hm₂ h₁ h₂ hpret hsmall
  · exact hA g₁ g₂ hm₁ h₁ h₂ a₂ b₂ X W hW₀W hWX hlarge.le

end

end NormalNumbers.ElliottLeafTwo
