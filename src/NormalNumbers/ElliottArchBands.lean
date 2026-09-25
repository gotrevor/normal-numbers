import NormalNumbers.ElliottSmallShift

/-!
# Input (c′) split into bands: the soft band and the isolated wall

`ElliottTwistRepair` reduced the two-point Elliott leaf to

* **(c′)** `ArchimedeanCorrelationBoundAbove A η (smallShiftThreshold ρ)` — the Archimedean prime
  correlation bound on `T X < |v| ≤ A²X`, and
* **(d1)** `PrimeDensityAP` (via `CharacterClusterRigidity`), which carries no zero-free region.

This file cuts (c′) at `|v| = 1` into two inputs of *very* different depth and proves that the two
together give (c′).  The point of the cut is that it isolates the wall: the sub-unit band is
Mertens-with-a-shift and involves no zero-free region at all, while everything genuinely deep about
(c′) is confined to `ArchCorrLargeShift`.

## Why this is the right cut (route analysis, lap 95)

Write `C(v,X) = ∑_{p≤X} p^{-iv}/p`, `M(X) = ∑_{p≤X} 1/p ≈ L := log log X`, and recall
`C(v,X) = log ζ(1 + 1/log X + iv) + O(1)`.

* For `|v| ≤ 1` the truth is `‖C(v,X)‖ = log(1/|v|) + O(1)` (capped at `L`), because
  `ζ(σ+iv)` has its pole at distance `max(|v|, 1/log X)`.  This is `ShiftedMertensSmall`.  Against
  the honest threshold `T X = smallShiftThreshold ρ X`, whose defining window satisfies
  `log log (shortWindow ρ X) ≤ (1 − ρ/2)·L`, this yields `‖C‖ ≤ (1 − ρ/2)L + O(1)`, i.e. the
  proportional saving `η ≈ ρ/2`.  **No zero-free region.**
* For `|v| > 1` the required statement is a *power saving in the logarithm*:
  `‖C(v,X)‖ ≤ (1 − η)·L + O(1)`, equivalently `|ζ(1 + 1/log X + iv)| ≪ (log X)^{1-η}` over the
  whole polynomial-height range `|v| ≤ A²X`.  This is `ArchCorrLargeShift`.

## What lap 95 settled about the upper band (negative results, recorded so they are not retried)

1. **The trivial bound is not enough, and not by a constant.**  `|ζ(σ+it)| ≪ log t` for `σ ≥ 1`
   (Euler–Maclaurin; and even the sharp truncation `∑_{n≤X} n^{-1-1/log X} = (1−e^{-1})log X`)
   gives `log|ζ| ≤ L + O(1)`, i.e. `η = 0`.  A constant factor saving on `ζ` is only an *additive*
   `O(1)` saving on `C`, and the consumer needs a *proportional* one.
2. **The van der Corput second-derivative test is also only a constant factor.**  On a dyadic
   block `n ≍ N` it gives `∑ n^{-it} ≪ t^{1/2} + N t^{-1/2}`, a genuine saving exactly for
   `N > t^{1/2}`; summing `1/n`-weighted, the blocks above `t^{1/2}` contribute `O(1)` and the
   blocks below contribute the trivial `(1/2)log t`.  So `|ζ(1+it)| ≪ (1/2)log t`: again additive.
   The `k`-th derivative test replaces `1/2` by `1/k`, so a *power* saving needs `k ≍ (log t)^η`
   with constants uniform in `k` — that is Vinogradov's mean value theorem, not van der Corput.
   ⛔ **The `(c′-vdC)` route recorded in `PENDING_WORK.md` is therefore refuted as stated**: van der
   Corput alone cannot produce the proportional saving.
3. **The Halász-converse half of that route is also unusable as recorded.**  It proposed deriving a
   contradiction from `|∑_{n≤X} n^{-iv}| ≫ X`; but `∑_{n≤X} n^{-iv} = X^{1-iv}/(1-iv) + O(1+|v|)`
   *exactly* (Euler–Maclaurin), of size `≍ X/|v|`, so no van der Corput input is needed and no
   contradiction arises until `|v| ≥ (log X)^{η}` — i.e. the argument, even granted the
   Granville–Soundararajan lower bound, reproves only what item 1's trivial bound already gives.
4. **The true statement, and its constant.**  `|ζ(1+it)| ≪ (log t)^{2/3}` (Vinogradov–Korobov)
   gives `ArchCorrLargeShift A η K` for every `η < 1/3`.  So the upper band is true, with a
   concrete `η`, and the wall is exactly Vinogradov's mean value theorem.

**EA-1 boundary check.**  `ShiftedMertensSmall` at `|v| = 1` asserts `‖C‖ ≤ K`, true since
`ζ(1+i)` is finite and nonzero; at `|v| → 0` the bound `log(1/|v|) → ∞` is weaker than the trivial
`M(X) + O(1)`, so it cannot be violated.  `ArchCorrLargeShift` at its extreme `|v| = A²X` asserts
`‖C‖ ≤ (1−η)L + K` where the truth is `(2/3)L + O(1)`: it holds with room, for any `η < 1/3`.  At
the other extreme `|v| = 1+` the truth is `O(1)`, far below `(1−η)L`.  Both inputs pass.
-/

open Finset

namespace NormalNumbers.ElliottArchBands

open Erdos67b NormalNumbers.ElliottZetaOmegaPretentious NormalNumbers.ElliottTwistBootstrap
  NormalNumbers.ElliottTwistRepair NormalNumbers.ElliottSmallShift

noncomputable section

/-! ### The two bands -/

/-- **Input (c′-I), the sub-unit band.**  Mertens' theorem with a small Archimedean shift: for
`0 < |v| ≤ 1` the correlation is at most `log(1/|v|)` up to an absolute constant — it reflects the
pole of `ζ` at distance `max(|v|, 1/log X)`.

⚠ **Fidelity correction (lap 96).**  Lap 95 called this input "free of any zero-free region".
That is WRONG for `|v|` bounded away from `0`, and the correction is recorded here so it is not
re-asserted.  Splitting at `log Y = 1/|v|` handles `[2,Y]` by two-sided Mertens alone, but the
range `[Y,X]` needs genuine cancellation of `p^{-iv}`, and Mertens-level input cannot supply it:
Abel summation against `∑_{p≤u}1/p = log log u + B + E(u)` costs `|v|·∫|E|` over `log u ∈ [1/|v|,
log X]`, which is `O(1)` only if `E(u) = O(1/log²u)` — already PNT strength — and is
`≍ |v|·log(|v| log X)`, i.e. unbounded, for the absolute-constant `E` the repo has.  The interval
version of the same obstruction: chopping `[Y,X]` into the `≍ |v| log X` intervals where
`cos(v log p) ≤ 0` incurs one absolute Mertens error per interval.  So (c′-I) is de la Vallée
Poussin strength (classical zero-free region / PNT with error) — *strictly weaker than (c′-III)
below, but not elementary*.  `PrimeNumberTheoremAnd.{ZetaBounds, StrongPNT}` is where to source it. -/
def ShiftedMertensSmall (K : ℝ) : Prop :=
  ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X → ∀ v : ℝ, 0 < |v| → |v| ≤ 1 →
    ‖archCorr v X‖ ≤ Real.log (1 / |v|) + K

/-- **Input (c′-II), the whole super-unit band.**  A *proportional* saving on the Archimedean
correlation at unit or larger frequency, over the polynomial-height range.  Equivalent to a power
saving `|ζ(1 + 1/log X + iv)| ≪ (log X)^{1-η}` at `|v| ≍ X`; true for every `η < 1/3` by
Vinogradov–Korobov, and reachable by no `η > 0` from van der Corput alone (see the module
docstring).  Lap 96 splits it further, at `heightCut`, into a de la Vallée Poussin part and a
genuinely narrow Vinogradov part. -/
def ArchCorrLargeShift (A : ℕ) (η K : ℝ) : Prop :=
  ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X → ∀ v : ℝ, 1 < |v| → |v| ≤ (A : ℝ) * (A : ℝ) * X →
    ‖archCorr v X‖ ≤ (1 - η) * Real.log (Real.log (X : ℝ)) + K

/-! ### Lap 96: the wall is narrower than (c′-II) — it lives only at near-maximal height -/

/-- The height cut: `log log (heightCut ν X) = (1 − ν)·log log X` exactly, i.e.
`heightCut ν X = exp((log X)^{1-ν})`. -/
def heightCut (ν : ℝ) (X : ℕ) : ℝ :=
  Real.exp (Real.exp ((1 - ν) * Real.log (Real.log (X : ℝ))))

theorem logLog_heightCut (ν : ℝ) (X : ℕ) :
    Real.log (Real.log (heightCut ν X)) = (1 - ν) * Real.log (Real.log (X : ℝ)) := by
  rw [heightCut, Real.log_exp, Real.log_exp]

/-- **Input (c′-II-a), moderate height.**  The *shape-true* bound `‖archCorr v X‖ ≤ log log|v| +
O(1)` for `|v| > 1`.  This is the size of `log ζ(1 + 1/log X + iv)` under the **trivial** bound
`|ζ(σ+it)| ≪ log t` for `σ ≥ 1`; only the truncation `∑_{p≤X}` ↦ `∑_p` costs anything, and that
cost is de la Vallée Poussin strength, the same as (c′-I).  **No Vinogradov.**  Note it is stated
for *all* `v` with `1 < |v|`, which is safe: for `|v|` beyond polynomial height the right side is
larger than the trivial bound `M(X)` anyway. -/
def ArchCorrModerate (K : ℝ) : Prop :=
  ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X → ∀ v : ℝ, 1 < |v| →
    ‖archCorr v X‖ ≤ Real.log (Real.log (|v| + 16)) + K

/-- **Input (c′-II-a) at the exponent the in-repo zero-free region actually delivers.**

Identical to `ArchCorrModerate` except for the absolute factor `9`.  The factor is inherited from
`PNTPort.ZetaZeroFree9`'s region `σ ≥ 1 − A/(log|t|)^9`, and it is **free**: see
`archCorrLargeShift_of_moderate9_and_nearMax`, which absorbs it by moving the height cut from
`exp((log X)^{1−ν})` to `exp((log X)^{(1−ν)/9})`.  The far band was already Vinogradov, so widening
it costs nothing.

EP-1 provenance: **this is a THEOREM, not a cited input** —
`ElliottSliceCapModerate.exists_dampedSeriesBoundModerate9` +
`ElliottDamped.archCorrModerate9_of_dampedSeriesBound`. -/
def ArchCorrModerate9 (K : ℝ) : Prop :=
  ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X → ∀ v : ℝ, 1 < |v| →
    ‖archCorr v X‖ ≤ 9 * Real.log (Real.log (|v| + 16)) + K

/-- **Input (c′-II-b), THE WALL, and all that is left of it.**  A proportional saving, needed only
on the near-maximal-height band `exp((log X)^{1-ν}) < |v| ≤ A²X`.  This is the sole place where
`log log |v| ≍ log log X` and hence where the trivial bound on `ζ(1+it)` fails to save a
proportion; it is exactly the Vinogradov–Korobov site. -/
def ArchCorrNearMaxHeight (A : ℕ) (ν η K : ℝ) : Prop :=
  ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X → ∀ v : ℝ,
    heightCut ν X < |v| + 16 → |v| ≤ (A : ℝ) * (A : ℝ) * X →
      ‖archCorr v X‖ ≤ (1 - η) * Real.log (Real.log (X : ℝ)) + K

/-- **THE WALL, NARROWED.**  The super-unit band (c′-II) follows from the shape-true moderate bound
plus a proportional saving on the near-maximal-height band alone.  Combined with
`archimedeanCorrelationBoundAbove_of_bands`, the only Vinogradov-strength input the whole Elliott
consumer needs is `ArchCorrNearMaxHeight`, on `|v| > exp((log X)^{1-ν})`. -/
theorem archCorrLargeShift_of_moderate_and_nearMax {A : ℕ} {ν η₂ K₁ K₂ : ℝ}
    (hν : 0 < ν) (hν1 : ν < 1) (hη₂ : 0 < η₂)
    (hmod : ArchCorrModerate K₁) (hmax : ArchCorrNearMaxHeight A ν η₂ K₂) :
    ArchCorrLargeShift A (min ν η₂) (|K₁| + |K₂|) := by
  classical
  obtain ⟨X₁, hX₁2, hX₁⟩ := hmod
  obtain ⟨X₂, hX₂2, hX₂⟩ := hmax
  obtain ⟨X₃, hX₃2, hX₃⟩ := exists_logLog_ge 0
  refine ⟨max (max X₁ X₂) (max X₃ 2), le_trans (le_max_right _ _) (le_max_right _ _), ?_⟩
  intro X hX v hv1 hvA
  have hXX₁ : X₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXX₂ : X₂ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXX₃ : X₃ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  set L : ℝ := Real.log (Real.log (X : ℝ)) with hL
  have hL0 : (0 : ℝ) ≤ L := hX₃ X hXX₃
  have hm : min ν η₂ ≤ ν := min_le_left _ _
  have hm' : min ν η₂ ≤ η₂ := min_le_right _ _
  have hK₁ : K₁ ≤ |K₁| := le_abs_self _
  have hK₂ : K₂ ≤ |K₂| := le_abs_self _
  have hK₁0 : (0 : ℝ) ≤ |K₁| := abs_nonneg _
  have hK₂0 : (0 : ℝ) ≤ |K₂| := abs_nonneg _
  rcases le_or_gt (|v| + 16) (heightCut ν X) with hcut | hcut
  · -- moderate height: the shape-true bound already saves the proportion `ν`
    have hbound := hX₁ X hXX₁ v hv1
    have hpos : (0 : ℝ) < Real.log (|v| + 16) := Real.log_pos (by linarith [abs_nonneg v])
    have hstep : Real.log (Real.log (|v| + 16)) ≤ (1 - ν) * L := by
      have h1 : Real.log (|v| + 16) ≤ Real.log (heightCut ν X) :=
        Real.log_le_log (by linarith [abs_nonneg v]) hcut
      have := Real.log_le_log hpos h1
      rwa [logLog_heightCut] at this
    have hmono : (1 - ν) * L ≤ (1 - min ν η₂) * L := by nlinarith
    linarith
  · -- near-maximal height: the wall
    have hbound := hX₂ X hXX₂ v hcut hvA
    have hmono : (1 - η₂) * L ≤ (1 - min ν η₂) * L := by nlinarith
    linarith

/-- **THE WALL, NARROWED — with the coefficient 9 absorbed.**

Same conclusion as `archCorrLargeShift_of_moderate_and_nearMax`, from the factor-`9` moderate
bound.  The *only* change is that the near-maximal-height hypothesis is taken at the shifted
parameter `1 − (1−ν)/9`, i.e. the height cut moves from `exp((log X)^{1−ν})` to
`exp((log X)^{(1−ν)/9})`.

**Why the factor is free (EA-1 boundary check, verified at the extreme point before this was
written).**  Below the cut, `log log(|v|+16) ≤ (1 − (1 − (1−ν)/9))·L = ((1−ν)/9)·L`, so
`9·log log(|v|+16) ≤ (1−ν)·L` — *exactly* the same bound the unfactored version gets below its own
cut, with equality at the cut itself.  The proportional saving `ν` therefore survives intact; what
changes is only how much of the range is handed to `ArchCorrNearMaxHeight`.  Note
`1 − (1−ν)/9 ∈ (8/9, 1)` for `ν ∈ (0,1)`, so the Vinogradov band is strictly wider — and it was
already Vinogradov. -/
theorem archCorrLargeShift_of_moderate9_and_nearMax {A : ℕ} {ν η₂ K₁ K₂ : ℝ}
    (hν : 0 < ν) (hν1 : ν < 1) (hη₂ : 0 < η₂)
    (hmod : ArchCorrModerate9 K₁)
    (hmax : ArchCorrNearMaxHeight A (1 - (1 - ν) / 9) η₂ K₂) :
    ArchCorrLargeShift A (min ν η₂) (|K₁| + |K₂|) := by
  classical
  obtain ⟨X₁, hX₁2, hX₁⟩ := hmod
  obtain ⟨X₂, hX₂2, hX₂⟩ := hmax
  obtain ⟨X₃, hX₃2, hX₃⟩ := exists_logLog_ge 0
  refine ⟨max (max X₁ X₂) (max X₃ 2), le_trans (le_max_right _ _) (le_max_right _ _), ?_⟩
  intro X hX v hv1 hvA
  have hXX₁ : X₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXX₂ : X₂ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXX₃ : X₃ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  set L : ℝ := Real.log (Real.log (X : ℝ)) with hL
  have hL0 : (0 : ℝ) ≤ L := hX₃ X hXX₃
  have hm : min ν η₂ ≤ ν := min_le_left _ _
  have hm' : min ν η₂ ≤ η₂ := min_le_right _ _
  have hK₁ : K₁ ≤ |K₁| := le_abs_self _
  have hK₂ : K₂ ≤ |K₂| := le_abs_self _
  have hK₁0 : (0 : ℝ) ≤ |K₁| := abs_nonneg _
  have hK₂0 : (0 : ℝ) ≤ |K₂| := abs_nonneg _
  rcases le_or_gt (|v| + 16) (heightCut (1 - (1 - ν) / 9) X) with hcut | hcut
  · -- moderate height: the factor-9 bound still saves the proportion `ν`
    have hbound := hX₁ X hXX₁ v hv1
    have hpos : (0 : ℝ) < Real.log (|v| + 16) := Real.log_pos (by linarith [abs_nonneg v])
    have hstep : Real.log (Real.log (|v| + 16)) ≤ (1 - (1 - (1 - ν) / 9)) * L := by
      have h1 : Real.log (|v| + 16) ≤ Real.log (heightCut (1 - (1 - ν) / 9) X) :=
        Real.log_le_log (by linarith [abs_nonneg v]) hcut
      have := Real.log_le_log hpos h1
      rwa [logLog_heightCut] at this
    have hstep9 : 9 * Real.log (Real.log (|v| + 16)) ≤ (1 - ν) * L := by
      have hsimp : (1 - (1 - (1 - ν) / 9)) * L = ((1 - ν) / 9) * L := by ring
      rw [hsimp] at hstep
      linarith
    have hmono : (1 - ν) * L ≤ (1 - min ν η₂) * L := by nlinarith
    linarith
  · -- near-maximal height: the wall, on the widened band
    have hbound := hX₂ X hXX₂ v hcut hvA
    have hmono : (1 - η₂) * L ≤ (1 - min ν η₂) * L := by nlinarith
    linarith

/-! ### The short window, from above -/

/-- The window defining the threshold has `log log Y ≤ (1 − ρ/2)·log log X`, and `Y ≥ 2`.  This is
the *upper* companion of the mass estimate proved inside `exists_reductionScale`. -/
theorem shortWindow_bounds {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) {X : ℕ} (hX2 : 2 ≤ X)
    (hL2 : 2 * Real.log 2 ≤ Real.log (Real.log (X : ℝ))) :
    2 ≤ shortWindow ρ X ∧
      Real.log (Real.log ((shortWindow ρ X : ℕ) : ℝ))
        ≤ (1 - ρ / 2) * Real.log (Real.log (X : ℝ)) := by
  classical
  set L : ℝ := Real.log (Real.log (X : ℝ)) with hL
  set w : ℝ := Real.exp ((1 - ρ / 2) * L) with hw
  set z : ℝ := Real.exp w with hz
  set Y : ℕ := shortWindow ρ X with hY
  have hYdef : Y = ⌊z⌋₊ := by rw [hY, shortWindow, hz, hw, hL]
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hwexp : (1 - ρ / 2) * L ≥ Real.log 2 := by nlinarith
  have hw2 : (2 : ℝ) ≤ w := by
    rw [hw]
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp ((1 - ρ / 2) * L) := Real.exp_le_exp.mpr hwexp
  have hz2 : (2 : ℝ) ≤ z := by
    rw [hz]
    calc (2 : ℝ) ≤ w := hw2
      _ ≤ Real.exp w := by linarith [Real.add_one_le_exp w]
  have hY2 : 2 ≤ Y := by rw [hYdef]; exact Nat.le_floor (by exact_mod_cast hz2)
  refine ⟨hY2, ?_⟩
  have hYle : (Y : ℝ) ≤ z := by rw [hYdef]; exact Nat.floor_le (by linarith)
  have hlogY : Real.log (Y : ℝ) ≤ w := by
    have := Real.log_le_log (by positivity) hYle
    rwa [hz, Real.log_exp] at this
  have hYR : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY2
  have hlogYpos : 0 < Real.log (Y : ℝ) := Real.log_pos (by linarith)
  have := Real.log_le_log hlogYpos hlogY
  rwa [hw, Real.log_exp] at this

/-! ### The assembly -/

/-- **(c′) FROM THE TWO BANDS.**  The soft band below `|v| = 1` and the power-saving band above it
give the Archimedean correlation bound on the whole honest frequency range, with
`η = min (ρ/4) (η₁/2)`.

The proportional constant degrades by a factor `2` in each band: below `1` because the threshold
only buys `(1 − ρ/2)·log log X` and the additive constants have to be absorbed, above `1` because
`ArchCorrLargeShift`'s own additive constant has to be absorbed.  Both absorptions are legitimate
because `log log X → ∞`. -/
theorem archimedeanCorrelationBoundAbove_of_bands {A : ℕ} {K₀ η₁ K₁ ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hη₁ : 0 < η₁) (hη₁1 : η₁ ≤ 1)
    (hsmall : ShiftedMertensSmall K₀) (hlarge : ArchCorrLargeShift A η₁ K₁) :
    ArchimedeanCorrelationBoundAbove A (min ρ η₁ / 4) (smallShiftThreshold ρ) := by
  classical
  obtain ⟨Xs, hXs2, hXs⟩ := hsmall
  obtain ⟨Xl, hXl2, hXl⟩ := hlarge
  set B : ℝ := PrimeEstimates.mertensBound with hB
  have hB0 : 0 ≤ B := PrimeEstimates.mertensBound_nonneg
  set η : ℝ := min ρ η₁ / 4 with hη
  have hη0 : 0 < η := by rw [hη]; have := lt_min hρ hη₁; linarith
  have hη1 : η ≤ 1 := by
    rw [hη]; have := min_le_right ρ η₁; linarith
  -- the size of `log log X` we need
  set R : ℝ := max (2 * Real.log 2) ((4 * (|K₀| + |K₁| + B + 1)) / (min ρ η₁)) with hR
  obtain ⟨Xr, hXr2, hXr⟩ := exists_logLog_ge R
  refine ⟨max (max Xs Xl) (max Xr 2), le_trans (le_max_right _ _) (le_max_right _ _), ?_⟩
  intro X hX v hvT hvA
  have hXXs : Xs ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXXl : Xl ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXXr : Xr ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX2 : 2 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  set L : ℝ := Real.log (Real.log (X : ℝ)) with hL
  have hLR : R ≤ L := hXr X hXXr
  have hL2 : 2 * Real.log 2 ≤ L := le_trans (le_max_left _ _) hLR
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hminpos : 0 < min ρ η₁ := lt_min hρ hη₁
  have hbudget : 4 * (|K₀| + |K₁| + B + 1) ≤ (min ρ η₁) * L := by
    have := le_trans (le_max_right _ _) hLR
    rw [div_le_iff₀ hminpos] at this; linarith
  have hK₀ : K₀ ≤ |K₀| := le_abs_self _
  have hK₁ : K₁ ≤ |K₁| := le_abs_self _
  have hMX : L - B ≤ primeMass X := by
    have := abs_le.mp (abs_primeMass_sub_logLog_le hX2); linarith [this.1]
  have hMnn : 0 ≤ primeMass X := primeMass_nonneg X
  -- the target, uniformly in the band
  have hgoal : ∀ b : ℝ, b ≤ (1 - min ρ η₁ / 2) * L + (|K₀| + |K₁|) →
      b ≤ (1 - η) * primeMass X := by
    intro b hb
    have hηmin : η ≤ min ρ η₁ / 4 := le_of_eq hη
    have hstep : (1 - η) * (L - B) ≤ (1 - η) * primeMass X :=
      mul_le_mul_of_nonneg_left hMX (by linarith)
    nlinarith [hminpos, hbudget, mul_nonneg (le_of_lt hminpos) hL0]
  rcases le_or_gt |v| 1 with hv1 | hv1
  · -- soft band: `T X < |v| ≤ 1`
    have hTpos : 0 < smallShiftThreshold ρ X := by
      obtain ⟨hY2, _⟩ := shortWindow_bounds hρ hρ1 hX2 hL2
      have hYR : (2 : ℝ) ≤ ((shortWindow ρ X : ℕ) : ℝ) := by exact_mod_cast hY2
      have : 0 < Real.log ((shortWindow ρ X : ℕ) : ℝ) := Real.log_pos (by linarith)
      rw [smallShiftThreshold]; positivity
    have hv0 : 0 < |v| := lt_trans hTpos hvT
    have hbound := hXs X hXXs v hv0 hv1
    -- `log (1/|v|) ≤ log log Y ≤ (1 − ρ/2) L`
    obtain ⟨hY2, hYlog⟩ := shortWindow_bounds hρ hρ1 hX2 hL2
    have hYR : (2 : ℝ) ≤ ((shortWindow ρ X : ℕ) : ℝ) := by exact_mod_cast hY2
    have hlogYpos : 0 < Real.log ((shortWindow ρ X : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hinv : Real.log (1 / |v|) ≤ Real.log (1 / smallShiftThreshold ρ X) := by
      refine Real.log_le_log (by positivity) ?_
      exact one_div_le_one_div_of_le hTpos hvT.le
    have hTinv : (1 : ℝ) / smallShiftThreshold ρ X
        = Real.log ((shortWindow ρ X : ℕ) : ℝ) := by
      rw [smallShiftThreshold, one_div_one_div]
    rw [hTinv] at hinv
    refine hgoal _ (le_trans hbound ?_)
    have : Real.log (1 / |v|) ≤ (1 - ρ / 2) * L := le_trans hinv hYlog
    have hmono : (1 - ρ / 2) * L ≤ (1 - min ρ η₁ / 2) * L := by
      have : min ρ η₁ ≤ ρ := min_le_left _ _
      nlinarith
    have : |K₁| ≥ 0 := abs_nonneg _
    linarith
  · -- the wall band: `1 < |v| ≤ A²X`
    have hbound := hXl X hXXl v hv1 hvA
    refine hgoal _ (le_trans hbound ?_)
    have hmono : (1 - η₁) * L ≤ (1 - min ρ η₁ / 2) * L := by
      have h1 : min ρ η₁ ≤ η₁ := min_le_right _ _
      nlinarith
    have : |K₀| ≥ 0 := abs_nonneg _
    linarith

/-! ### The payoff: the two-point leaf on three inputs, only one of them deep -/

/-- **THE CONSUMER, ON THE BANDED INPUTS.**  `TwoPointElliottLog` now rests on exactly three
classical statements, and the zero-free region enters in only one of them:

| input | depth |
|---|---|
| `ElliottCharRigidity.PrimeDensityAP A` | Mertens in progressions; no zero-free region |
| `ShiftedMertensSmall K₀` | Mertens with a small shift; no zero-free region |
| `ArchCorrLargeShift A η₁ K₁` | **the wall**: a power saving on `ζ(1+it)`, i.e. Vinogradov |

Note the quantifier shape of the deep input: a *single* `η₁ > 0`, uniform in the threshold scale
`r`.  The `r`-dependence that (c′) needed is produced here, by the soft band. -/
theorem twoPointElliottLog_of_bands {b p q : ℕ} {t : ℝ} {K₀ η₁ K₁ : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q) (hu : (NormalNumbers.CastingOut.phase (t / b)).re < 1)
    (hη₁ : 0 < η₁) (hη₁1 : η₁ ≤ 1)
    (hdens : ∀ A : ℕ, ElliottCharRigidity.PrimeDensityAP A)
    (hsmall : ShiftedMertensSmall K₀)
    (hlarge : ∀ A : ℕ, ArchCorrLargeShift A η₁ K₁) :
    NormalNumbers.ElliottTwoPointLog.TwoPointElliottLog b p q t := by
  refine twoPointElliottLog_of_archimedean_and_primeDensity hp hq hpq hu hdens ?_
  intro A r hr hr1
  refine ⟨min r η₁ / 4, by have := lt_min hr hη₁; linarith, ?_⟩
  exact archimedeanCorrelationBoundAbove_of_bands hr hr1 hη₁ hη₁1 hsmall (hlarge A)

/-- **THE CONSUMER ON THE FINAL INPUT LIST (lap 96).**  `TwoPointElliottLog` on four classical
statements, of which exactly one is Vinogradov-strength and it is confined to frequencies of
near-maximal height `|v| > exp((log X)^{1-ν})`:

| input | depth |
|---|---|
| `ElliottCharRigidity.PrimeDensityAP A` | Mertens in progressions |
| `ShiftedMertensSmall K₀` | `\|v\| ≤ 1`; de la Vallée Poussin |
| `ArchCorrModerate K₁` | `\|v\| > 1`, shape-true `log log\|v\|`; de la Vallée Poussin |
| `ArchCorrNearMaxHeight A ν η₂ K₂` | **Vinogradov–Korobov**, near-maximal height only | -/
theorem twoPointElliottLog_of_three_bands {b p q : ℕ} {t : ℝ} {K₀ K₁ K₂ ν η₂ : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q)
    (hu : (NormalNumbers.CastingOut.phase (t / b)).re < 1)
    (hν : 0 < ν) (hν1 : ν < 1) (hη₂ : 0 < η₂) (hη₂1 : η₂ ≤ 1)
    (hdens : ∀ A : ℕ, ElliottCharRigidity.PrimeDensityAP A)
    (hsmall : ShiftedMertensSmall K₀)
    (hmod : ArchCorrModerate K₁)
    (hmax : ∀ A : ℕ, ArchCorrNearMaxHeight A ν η₂ K₂) :
    NormalNumbers.ElliottTwoPointLog.TwoPointElliottLog b p q t := by
  refine twoPointElliottLog_of_bands (η₁ := min ν η₂) (K₁ := |K₁| + |K₂|)
    hp hq hpq hu (lt_min hν hη₂) ?_ hdens hsmall ?_
  · exact le_trans (min_le_right _ _) hη₂1
  · intro A
    exact archCorrLargeShift_of_moderate_and_nearMax hν hν1 hη₂ hmod (hmax A)

/-- **THE LEDGER, WITH (c′-II-a) DISCHARGED.**  Same conclusion as
`twoPointElliottLog_of_three_bands`, but taking the *proved* `ArchCorrModerate9` in place of the
cited `ArchCorrModerate`, at the correspondingly widened Vinogradov band.

| input | status |
| --- | --- |
| `ElliottCharRigidity.PrimeDensityAP A` | Mertens in progressions — reachable from the in-repo `G4MertensAP.mertensRate_residueClass` (T3) |
| `ShiftedMertensSmall K₀` | **PROVED** (`ElliottSliceCap.exists_shiftedMertensSmall`, lap 112) |
| `ArchCorrModerate9 K₁` | **PROVED** (`ElliottSliceCapModerate.exists_archCorrModerate9`, lap 117) |
| `ArchCorrNearMaxHeight A (1−(1−ν)/9) η₂ K₂` | **Vinogradov–Korobov**, near-maximal height only — the designated cited axiom | -/
theorem twoPointElliottLog_of_moderate9 {b p q : ℕ} {t : ℝ} {K₀ K₁ K₂ ν η₂ : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q)
    (hu : (NormalNumbers.CastingOut.phase (t / b)).re < 1)
    (hν : 0 < ν) (hν1 : ν < 1) (hη₂ : 0 < η₂) (hη₂1 : η₂ ≤ 1)
    (hdens : ∀ A : ℕ, ElliottCharRigidity.PrimeDensityAP A)
    (hsmall : ShiftedMertensSmall K₀)
    (hmod : ArchCorrModerate9 K₁)
    (hmax : ∀ A : ℕ, ArchCorrNearMaxHeight A (1 - (1 - ν) / 9) η₂ K₂) :
    NormalNumbers.ElliottTwoPointLog.TwoPointElliottLog b p q t := by
  refine twoPointElliottLog_of_bands (η₁ := min ν η₂) (K₁ := |K₁| + |K₂|)
    hp hq hpq hu (lt_min hν hη₂) ?_ hdens hsmall ?_
  · exact le_trans (min_le_right _ _) hη₂1
  · intro A
    exact archCorrLargeShift_of_moderate9_and_nearMax hν hν1 hη₂ hmod (hmax A)

/-- **The near-max band is ANTITONE in the cut parameter.**  `heightCut ν X = exp((log X)^{1−ν})`
shrinks as `ν` grows, so a larger `ν` quantifies over *more* shifts `v`: the hypothesis gets
strictly stronger.

This makes machine-checked what lap 117's prose asserted.  `archCorrLargeShift_of_moderate9_and_nearMax`
needs `ArchCorrNearMaxHeight` at `1 − (1−ν)/9 > ν`, i.e. **strictly more** than the unfactored
`archCorrLargeShift_of_moderate_and_nearMax` needs at `ν` — the Vinogradov band genuinely widens,
and this lemma shows the implication runs the other way, so the widening cannot be bluffed away by
citing the narrower statement.

**EA-1: why the widened hypothesis is nonetheless TRUE.**  Vinogradov–Korobov gives
`|ζ(1+it)| ≪ (log t)^{2/3}`, hence `‖archCorr v X‖ ≤ (2/3)·log log|v| + O(1)` — and on the whole
range the `Prop` quantifies over, `|v| ≤ A²X` forces `log log|v| ≤ L + O(1)`.  So the bound
`(1−η)·L + K` holds for **every** `η ≤ 1/3` *irrespective of the lower cut*: the cut only removes
shifts from the range.  Widening the band from `ν` to `1 − (1−ν)/9` therefore costs nothing in
truth, only in the size of the region delegated to the cited axiom. -/
theorem archCorrNearMaxHeight_antitone {A : ℕ} {ν ν' η K : ℝ} (hνν : ν ≤ ν')
    (hmax : ArchCorrNearMaxHeight A ν' η K) : ArchCorrNearMaxHeight A ν η K := by
  obtain ⟨X₂, hX₂2, hX₂⟩ := hmax
  obtain ⟨X₃, hX₃2, hX₃⟩ := exists_logLog_ge 0
  refine ⟨max (max X₂ X₃) 2, le_max_right _ _, ?_⟩
  intro X hX v hcut hvA
  have hXX₂ : X₂ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXX₃ : X₃ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hL0 : (0 : ℝ) ≤ Real.log (Real.log (X : ℝ)) := hX₃ X hXX₃
  have hmono : heightCut ν' X ≤ heightCut ν X := by
    rw [heightCut, heightCut]
    refine Real.exp_le_exp.mpr (Real.exp_le_exp.mpr ?_)
    nlinarith
  exact hX₂ X hXX₂ v (lt_of_le_of_lt hmono hcut) hvA

end

end NormalNumbers.ElliottArchBands
