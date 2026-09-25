import NormalNumbers.ElliottTwistRepair
import NormalNumbers.ElliottCharRigidity

/-!
# Input (e) DISCHARGED by scale reduction

`ElliottTwistRepair` reduced `TwoPointElliottLog` to (c′) an Archimedean bound *above* a frequency
threshold and (e) `SmallShiftAlmostReal` *below* it, and flagged (e) as needing Abel summation
against a two-sided Mertens estimate.  It does not.  The survey found

  `Erdos67b.PrimeEstimates.abs_primeReciprocals_sub_log_log_le`
    : `|∑_{p≤X}1/p − log log X| ≤ mertensBound`   (two-sided, absolute constant),

and with it the whole small-shift band is handled by **scale reduction** on machinery that is
already proved, with no new analysis at all.

## The idea

For `|t|` in the problem band `1/log X ≲ |t| ≲ (log X)^{-1+ε}` the Archimedean twist is *not* a
bounded perturbation of `1` across `[2,X]` — that is exactly why the old `NearTrivialTwist` branch
died there.  But it *is* one across the shorter window `[2,Y]` with `log Y = 1/|t|`, and by
two-sided Mertens that shorter window still carries all but `ε·M(X) + O(1)` of the prime mass:

  `M(X) − M(Y) ≤ log log X − log log Y + 2·mertensBound ≤ ε·log log X + 2·mertensBound`.

So: run the *old, proved* argument at scale `Y`, and transport the conclusion to scale `X` at a
cost of the discarded mass.  The price is that the conclusion is no longer "within `O(1)` of a
real" but "within a small **proportion** `ρ` of `M(X)` of a real" — which is all the consumer ever
needed, because the rotation by `ζ ≠ 1` buys a *fixed proportion* `1 − Re ζ` of `M(X)`.

## Contents

* `abs_primeMass_sub_logLog_le` — two-sided Mertens in this file's notation.
* `AlmostRealTwistProp ρ` — the proportional form of `ElliottTwistRepair.AlmostRealTwist`, and
  `re_phase_mul_twistCorr_le_prop`, the one inequality the consumer runs on.
* `TwistAlmostRealPropDichotomy`, `uniformlyNonPretentious_zetaOmega_of_almostRealProp` — the
  consumer re-proved.  **Quantifier order is load-bearing**: `ρ` is chosen *after* `u`, so the
  dichotomy is asked for at every `ρ > 0`.
* `norm_twistCorr_sub_le` — the transport cost `‖C(X) − C(Y)‖ ≤ M(X) − M(Y)`.
* `ReductionScale ρ t X Y` — the two properties of the shorter window.
* `almostRealProp_or_far_of_reductionScale` — **the theorem**: rigidity at level `A` plus a
  reduction scale gives the repaired dichotomy at scale `X`.  No Archimedean input, no zero-free
  region: only `CharacterClusterRigidity`, which lap 91 proved from `PrimeDensityAP`.
-/

open Finset

namespace NormalNumbers.ElliottSmallShift

open Erdos67b NormalNumbers.ElliottZetaOmegaPretentious NormalNumbers.ElliottTwistBootstrap
  NormalNumbers.CastingOut NormalNumbers.ElliottTwoPointLog NormalNumbers.ElliottTwistRepair

noncomputable section

/-! ### Two-sided Mertens -/

/-- **Mertens' second theorem, two-sided**, in this campaign's notation. -/
theorem abs_primeMass_sub_logLog_le {X : ℕ} (hX : 2 ≤ X) :
    |primeMass X - Real.log (Real.log (X : ℝ))| ≤ PrimeEstimates.mertensBound := by
  have heq : primeMass X = PrimeEstimates.primeReciprocals X := by
    rw [primeMass, show (∑ p ∈ primesUpTo X, (p : ℝ)⁻¹) = characterTwistPrimeMass X from rfl,
      characterTwistPrimeMass_eq_primeReciprocals]
  rw [heq]
  exact PrimeEstimates.abs_primeReciprocals_sub_log_log_le hX

/-- The mass discarded by shrinking the window from `X` to `Y` is controlled by the drop in
`log log`. -/
theorem primeMass_sub_le_logLog_sub {X Y : ℕ} (hX : 2 ≤ X) (hY : 2 ≤ Y) :
    primeMass X - primeMass Y
      ≤ (Real.log (Real.log (X : ℝ)) - Real.log (Real.log (Y : ℝ)))
        + 2 * PrimeEstimates.mertensBound := by
  have h1 := abs_le.mp (abs_primeMass_sub_logLog_le hX)
  have h2 := abs_le.mp (abs_primeMass_sub_logLog_le hY)
  linarith [h1.2, h2.1]

/-! ### The proportional almost-real alternative -/

/-- **The easy alternative, in proportional form.**  `C` is within `ρ·M(X)` of a nonnegative real
number at most `M(X)`. -/
def AlmostRealTwistProp (ρ : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (X : ℕ) : Prop :=
  ∃ R : ℝ, 0 ≤ R ∧ R ≤ primeMass X ∧ ‖twistCorr χ t X - (R : ℂ)‖ ≤ ρ * primeMass X

theorem almostRealTwistProp_of_almostRealTwist {K ρ : ℝ} {q : ℕ}
    {χ : DirichletCharacter ℂ q} {t : ℝ} {X : ℕ} (h : AlmostRealTwist K χ t X)
    (hK : K ≤ ρ * primeMass X) : AlmostRealTwistProp ρ χ t X := by
  obtain ⟨R, hR0, hRM, hclose⟩ := h
  exact ⟨R, hR0, hRM, le_trans hclose hK⟩

/-- **The key inequality, proportional form.** -/
theorem re_phase_mul_twistCorr_le_prop {ρ : ℝ} {q : ℕ} {χ : DirichletCharacter ℂ q} {t : ℝ}
    {X : ℕ} (u : ℝ) (h : AlmostRealTwistProp ρ χ t X) :
    (phase u * twistCorr χ t X).re ≤ (max ((phase u).re) 0 + ρ) * primeMass X := by
  obtain ⟨R, hR0, hRM, hclose⟩ := h
  have hmx0 : (0 : ℝ) ≤ max ((phase u).re) 0 := le_max_right _ _
  have hsplit : phase u * twistCorr χ t X
      = phase u * (R : ℂ) + phase u * (twistCorr χ t X - (R : ℂ)) := by ring
  have hre1 : (phase u * (R : ℂ)).re = (phase u).re * R := by simp [Complex.mul_re]
  have hre2 : (phase u * (twistCorr χ t X - (R : ℂ))).re ≤ ρ * primeMass X := by
    refine le_trans (Complex.re_le_norm _) ?_
    rw [norm_mul, norm_phase, one_mul]
    exact hclose
  have hmain : (phase u).re * R ≤ max ((phase u).re) 0 * primeMass X := by
    calc (phase u).re * R ≤ max ((phase u).re) 0 * R :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hR0
      _ ≤ max ((phase u).re) 0 * primeMass X := mul_le_mul_of_nonneg_left hRM hmx0
  rw [hsplit, Complex.add_re, hre1]
  nlinarith

/-- The repaired dichotomy, with the proportional easy alternative. -/
def TwistAlmostRealPropDichotomy (A : ℕ) (δ ρ : ℝ) : Prop :=
  ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X → ∀ q : ℕ, 0 < q → q ≤ A →
    ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, |t| ≤ (A : ℝ) * X →
      AlmostRealTwistProp ρ χ t X ∨ ‖twistCorr χ t X‖ ≤ (1 - δ) * primeMass X

/-- **The consumer, on the proportional dichotomy.**  The quantifier order matters: `ρ` is chosen
after `u`, small compared with the fixed gap `1 − Re ζ`. -/
theorem uniformlyNonPretentious_zetaOmega_of_almostRealProp {u : ℝ} (hu : (phase u).re < 1)
    (hdich : ∀ A : ℕ, ∀ ρ : ℝ, 0 < ρ →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ TwistAlmostRealPropDichotomy A δ ρ) :
    UniformlyNonPretentious (zetaOmegaInt u) := by
  classical
  intro A
  set mx : ℝ := max ((phase u).re) 0 with hmx
  have hmx0 : (0 : ℝ) ≤ mx := le_max_right _ _
  have hmx1 : mx < 1 := by rw [hmx]; exact max_lt hu one_pos
  set ρ : ℝ := (1 - mx) / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  obtain ⟨δ, hδ, hδ1, hdichA⟩ := hdich A ρ hρ
  set m : ℝ := min ρ δ with hmdef
  have hmpos : 0 < m := lt_min hρ hδ
  obtain ⟨X₁, hX₁2, hX₁⟩ := hdichA
  obtain ⟨X₀, hX₀2, hX₀⟩ := exists_primeMass_ge ((A : ℝ) / m)
  refine ⟨max X₀ X₁, ?_⟩
  intro X hX q hq hqA χ s hs
  have hXX₀ : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXX₁ : X₁ ≤ X := le_trans (le_max_right _ _) hX
  have hMnn : 0 ≤ primeMass X := primeMass_nonneg X
  have hmass : (A : ℝ) / m ≤ primeMass X := hX₀ X hXX₀
  have hkey : (A : ℝ) ≤ m * primeMass X := by
    rw [div_le_iff₀ hmpos] at hmass; linarith [hmass]
  rw [zetaOmegaDistSq_eq]
  rcases hX₁ X hXX₁ q hq hqA χ s hs with har | hfar
  · have hre := re_phase_mul_twistCorr_le_prop u har
    have hmm : m * primeMass X ≤ ρ * primeMass X :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hMnn
    have hsum : mx + ρ = 1 - ρ := by rw [hρdef]; ring
    rw [hsum] at hre
    nlinarith
  · have hre : (phase u * twistCorr χ s X).re ≤ (1 - δ) * primeMass X := by
      refine le_trans (Complex.re_le_norm _) ?_
      rw [norm_mul, norm_phase, one_mul]
      exact hfar
    have hmd : m * primeMass X ≤ δ * primeMass X :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hMnn
    nlinarith

/-! ### Transport between scales -/

/-- **The transport cost.**  Shrinking the window changes the twist correlation by at most the
discarded prime mass. -/
theorem norm_twistCorr_sub_le {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) {X Y : ℕ}
    (hYX : Y ≤ X) :
    ‖twistCorr χ t X - twistCorr χ t Y‖ ≤ primeMass X - primeMass Y := by
  classical
  have hsub : primesUpTo Y ⊆ primesUpTo X := primesUpTo_mono hYX
  have hdiff : twistCorr χ t X - twistCorr χ t Y
      = ∑ p ∈ (primesUpTo X) \ (primesUpTo Y),
          (starRingEnd ℂ) (dirichletArchimedeanTwist χ t p) / (p : ℂ) := by
    rw [twistCorr, twistCorr, eq_comm, Finset.sum_sdiff_eq_sub hsub]
  have hmass : primeMass X - primeMass Y = ∑ p ∈ (primesUpTo X) \ (primesUpTo Y), (p : ℝ)⁻¹ := by
    rw [primeMass, primeMass, eq_comm, Finset.sum_sdiff_eq_sub hsub]
  rw [hdiff, hmass]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum ?_
  intro p hp
  have hpp : p.Prime := (mem_primesUpTo.mp (Finset.mem_sdiff.mp hp).1).1
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
  rw [norm_div, RCLike.norm_conj, Complex.norm_natCast]
  rw [inv_eq_one_div, div_le_div_iff_of_pos_right hpR]
  exact norm_dirichletArchimedeanTwist_le_one χ t hpp.pos

/-- **A reduction scale** for the frequency `t` at the window `X`: a shorter window `Y` on which
the Archimedean twist is a bounded perturbation of `1`, and which still carries all but a
`ρ`-proportion of the prime mass. -/
def ReductionScale (ρ : ℝ) (t : ℝ) (X Y : ℕ) : Prop :=
  2 ≤ Y ∧ Y ≤ X ∧ |t| * Real.log (Y : ℝ) ≤ 1 ∧ primeMass X - primeMass Y ≤ ρ * primeMass X

/-! ### The theorem -/

/-- **INPUT (e), DISCHARGED at every frequency that admits a reduction scale.**

Granted only `CharacterClusterRigidity` at level `A` — which lap 91 proved from Mertens in
progressions, with no zero-free region — a frequency possessing a reduction scale satisfies the
repaired dichotomy.  Nothing Archimedean enters. -/
theorem almostRealProp_or_far_of_reductionScale {A : ℕ} {θ ρ δ₀ : ℝ}
    (hrig : CharacterClusterRigidity A θ) (hθ : 0 < θ) (hδ₀ : 0 < δ₀) (hδ₀θ : δ₀ < θ)
    (hδ₀1 : δ₀ < 1) (hρ : 0 < ρ) (hρδ : ρ ≤ δ₀ / 2) :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X → ∀ q : ℕ, 0 < q → q ≤ A →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, ∀ Y : ℕ, ReductionScale ρ t X Y →
        AlmostRealTwistProp (2 * ρ) χ t X ∨
          ‖twistCorr χ t X‖ ≤ (1 - δ₀ / 2) * primeMass X := by
  classical
  obtain ⟨Kc, hKc⟩ := exists_charDefect_le
  obtain ⟨Kn, hKn⟩ := exists_norm_twistCorr_sub_primeMass_le
  obtain ⟨Xr, hXr2, hXr⟩ := hrig
  -- `Y` must be past the rigidity threshold and carry enough mass; both follow from `M(X)` large
  obtain ⟨Xm, hXm2, hXm⟩ := exists_primeMass_ge
    (max (max (|Kc| / (θ - δ₀)) ((|Kn| + 2 * primeMass A) / ρ)) (primeMass Xr + 1) / (1 - ρ))
  have hρ1 : ρ < 1 := by
    have : δ₀ / 2 < 1 := by linarith
    linarith
  refine ⟨max Xm Xr, le_trans hXm2 (le_max_left _ _), ?_⟩
  intro X hX q hq hqA χ t Y hscale
  obtain ⟨hY2, hYX, hYt, hYmass⟩ := hscale
  have hXXm : Xm ≤ X := le_trans (le_max_left _ _) hX
  have hX2 : 2 ≤ X := le_trans hXm2 hXXm
  have hMXnn : 0 ≤ primeMass X := primeMass_nonneg X
  have hMYnn : 0 ≤ primeMass Y := primeMass_nonneg Y
  have hbig := hXm X hXXm
  -- `M(Y) ≥ (1-ρ)·M(X)` is enough to inherit every largeness requirement
  have hMY : max (max (|Kc| / (θ - δ₀)) ((|Kn| + 2 * primeMass A) / ρ)) (primeMass Xr + 1)
      ≤ primeMass Y := by
    have h1 : max (max (|Kc| / (θ - δ₀)) ((|Kn| + 2 * primeMass A) / ρ)) (primeMass Xr + 1)
        ≤ (1 - ρ) * primeMass X := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - ρ)] at hbig
      linarith [hbig]
    have h2 : (1 - ρ) * primeMass X ≤ primeMass Y := by nlinarith
    linarith
  have hMYrig : primeMass Xr + 1 ≤ primeMass Y := le_trans (le_max_right _ _) hMY
  have hMYc : |Kc| / (θ - δ₀) ≤ primeMass Y :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hMY
  have hMYn : (|Kn| + 2 * primeMass A) / ρ ≤ primeMass Y :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hMY
  -- `Y ≥ Xr`: otherwise `M(Y) ≤ M(Xr)`, contradicting `M(Y) ≥ M(Xr) + 1`
  have hYXr : Xr ≤ Y := by
    by_contra hcon
    have : primeMass Y ≤ primeMass Xr := primeMass_mono (le_of_lt (not_le.mp hcon))
    linarith
  have htrans := norm_twistCorr_sub_le χ t hYX
  by_cases hfar : ‖twistCorr χ t Y‖ ≤ (1 - δ₀) * primeMass Y
  · -- the far alternative transports with the discarded mass
    right
    have h1 : ‖twistCorr χ t X‖ ≤ ‖twistCorr χ t Y‖ + (primeMass X - primeMass Y) := by
      have := norm_add_le (twistCorr χ t X - twistCorr χ t Y) (twistCorr χ t Y)
      simp only [sub_add_cancel] at this
      linarith [htrans]
    have h2 : (1 - δ₀) * primeMass Y ≤ (1 - δ₀) * primeMass X :=
      mul_le_mul_of_nonneg_left (primeMass_mono hYX) (by linarith)
    nlinarith
  · -- the clustering alternative: run the proved near-trivial argument at scale `Y`
    left
    rw [not_le] at hfar
    obtain ⟨β, hβ, hdef⟩ := exists_unimodular_twistDefect_le χ t hY2 hδ₀1 hfar.le
    have hchar := hKc q χ β t Y hY2 (le_of_eq hβ) hYt
    have hclust : twistDefect (fun p => (starRingEnd ℂ) (χ p)) β Y ≤ θ * primeMass Y := by
      have hKcabs : Kc ≤ |Kc| := le_abs_self Kc
      have hgap : |Kc| ≤ (θ - δ₀) * primeMass Y := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < θ - δ₀)] at hMYc; linarith [hMYc]
      calc twistDefect (fun p => (starRingEnd ℂ) (χ p)) β Y
          ≤ twistDefect (fun p => (starRingEnd ℂ) (dirichletArchimedeanTwist χ t p)) β Y + Kc :=
            hchar
        _ ≤ δ₀ * primeMass Y + (θ - δ₀) * primeMass Y := by linarith [hdef]
        _ = θ * primeMass Y := by ring
    have hprin : PrincipalAtGoodPrimes χ := hXr Y hYXr q hq hqA χ β hβ hclust
    have hnear := hKn q χ hq t Y hY2 ⟨hprin, hYt⟩
    have hmq : primeMass q ≤ primeMass A := primeMass_mono hqA
    -- transport to scale `X`, with `R = M(Y)`
    refine ⟨primeMass Y, hMYnn, primeMass_mono hYX, ?_⟩
    have hsplit : twistCorr χ t X - (primeMass Y : ℂ)
        = (twistCorr χ t X - twistCorr χ t Y) + (twistCorr χ t Y - (primeMass Y : ℂ)) := by ring
    have habs : |Kn| + 2 * primeMass A ≤ ρ * primeMass Y := by
      rw [div_le_iff₀ hρ] at hMYn; linarith [hMYn]
    have hKnabs : Kn ≤ |Kn| := le_abs_self Kn
    have hMYX : primeMass Y ≤ primeMass X := primeMass_mono hYX
    calc ‖twistCorr χ t X - (primeMass Y : ℂ)‖
        ≤ ‖twistCorr χ t X - twistCorr χ t Y‖ + ‖twistCorr χ t Y - (primeMass Y : ℂ)‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ ≤ (primeMass X - primeMass Y) + (Kn + 2 * primeMass q) := by linarith [htrans, hnear]
      _ ≤ ρ * primeMass X + ρ * primeMass Y := by linarith
      _ ≤ 2 * ρ * primeMass X := by nlinarith

/-! ### The reduction scale exists on the whole small-shift band -/

/-- `log log X` is eventually as large as we please. -/
theorem exists_logLog_ge (R : ℝ) :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X → R ≤ Real.log (Real.log (X : ℝ)) := by
  refine ⟨max 2 (⌈Real.exp (Real.exp R)⌉₊ + 1), le_max_left _ _, ?_⟩
  intro X hX
  have hXexp : Real.exp (Real.exp R) ≤ (X : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast le_trans (by omega)
      (le_trans (le_max_right 2 (⌈Real.exp (Real.exp R)⌉₊ + 1)) hX)
  have hlogX : Real.exp R ≤ Real.log (X : ℝ) := by
    have := Real.log_le_log (Real.exp_pos _) hXexp
    rwa [Real.log_exp] at this
  have := Real.log_le_log (Real.exp_pos _) hlogX
  rwa [Real.log_exp] at this

/-- **The short window** at level `ρ`: `log Y ≈ (log X)^{1−ρ/2}`, written through `exp`/`log` so
that no `rpow` inequality is ever needed. -/
def shortWindow (ρ : ℝ) (X : ℕ) : ℕ :=
  ⌊Real.exp (Real.exp ((1 - ρ / 2) * Real.log (Real.log (X : ℝ))))⌋₊

/-- **The frequency threshold, defined BY the window.**  With this definition the clause
`|t| · log Y ≤ 1` of `ReductionScale` holds by construction. -/
def smallShiftThreshold (ρ : ℝ) (X : ℕ) : ℝ := 1 / Real.log ((shortWindow ρ X : ℕ) : ℝ)

/-- **THE REMAINING PIECE OF (e).**  Every frequency below the threshold admits a reduction
scale.  Elementary: two-sided Mertens plus the floor estimate `⌊z⌋₊ > z − 1`. -/
theorem exists_reductionScale {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X → ∀ t : ℝ, |t| ≤ smallShiftThreshold ρ X →
      ReductionScale ρ t X (shortWindow ρ X) := by
  classical
  set B : ℝ := PrimeEstimates.mertensBound with hB
  have hB0 : 0 ≤ B := PrimeEstimates.mertensBound_nonneg
  set L₀ : ℝ := max (2 * Real.log 2) (2 * (Real.log 2 + 2 * B + ρ * B) / ρ) with hL₀
  obtain ⟨X₁, hX₁2, hX₁⟩ := exists_logLog_ge L₀
  refine ⟨max X₁ 2, le_max_right _ _, ?_⟩
  intro X hX t ht
  have hXX₁ : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hX2 : 2 ≤ X := le_trans hX₁2 hXX₁
  have hXR : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
  have hlogXpos : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  set L : ℝ := Real.log (Real.log (X : ℝ)) with hL
  have hLbig : L₀ ≤ L := hX₁ X hXX₁
  have hL2 : 2 * Real.log 2 ≤ L := le_trans (le_max_left _ _) hLbig
  have hLmass : 2 * (Real.log 2 + 2 * B + ρ * B) / ρ ≤ L := le_trans (le_max_right _ _) hLbig
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 0 ≤ L := by linarith
  -- the window and its two scales
  set w : ℝ := Real.exp ((1 - ρ / 2) * L) with hw
  set z : ℝ := Real.exp w with hz
  set Y : ℕ := shortWindow ρ X with hY
  have hYdef : Y = ⌊z⌋₊ := by rw [hY, shortWindow, hz, hw, hL]
  have hcoef : (0 : ℝ) < 1 - ρ / 2 := by linarith
  -- `w ≥ 2`
  have hwexp : (1 - ρ / 2) * L ≥ Real.log 2 := by nlinarith
  have hw2 : (2 : ℝ) ≤ w := by
    rw [hw]
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp ((1 - ρ / 2) * L) := Real.exp_le_exp.mpr hwexp
  have hz2 : (2 : ℝ) ≤ z := by
    rw [hz]
    calc (2 : ℝ) ≤ w := hw2
      _ ≤ Real.exp w := by linarith [Real.add_one_le_exp w]
  -- `Y ≥ 2`
  have hY2 : 2 ≤ Y := by rw [hYdef]; exact Nat.le_floor (by exact_mod_cast hz2)
  have hYR : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY2
  have hlogYpos : 0 < Real.log (Y : ℝ) := Real.log_pos (by linarith)
  -- `Y ≤ X`
  have hXeq : (X : ℝ) = Real.exp (Real.exp L) := by
    rw [hL, Real.exp_log hlogXpos, Real.exp_log (by positivity)]
  have hzX : z ≤ (X : ℝ) := by
    rw [hz, hXeq]
    refine Real.exp_le_exp.mpr ?_
    rw [hw]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hYX : Y ≤ X := by
    rw [hYdef]
    have : (⌊z⌋₊ : ℝ) ≤ (X : ℝ) := le_trans (Nat.floor_le (by linarith)) hzX
    exact_mod_cast this
  -- the frequency clause, true by construction of the threshold
  have hfreq : |t| * Real.log (Y : ℝ) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right ht hlogYpos.le
    rwa [smallShiftThreshold, ← hY, one_div, inv_mul_cancel₀ (ne_of_gt hlogYpos)] at this
  -- the mass clause
  have hYlow : z / 2 ≤ (Y : ℝ) := by
    have hfl : z - 1 < (⌊z⌋₊ : ℝ) := Nat.sub_one_lt_floor z
    rw [hYdef]
    push_cast
    linarith
  have hlogY : w - Real.log 2 ≤ Real.log (Y : ℝ) := by
    have h1 : Real.log (z / 2) ≤ Real.log (Y : ℝ) :=
      Real.log_le_log (by linarith) hYlow
    rwa [Real.log_div (by linarith) (by norm_num), hz, Real.log_exp] at h1
  have hwlog2 : w / 2 ≤ w - Real.log 2 := by
    have : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    linarith
  have hloglogY : (1 - ρ / 2) * L - Real.log 2 ≤ Real.log (Real.log (Y : ℝ)) := by
    have h1 : Real.log (w / 2) ≤ Real.log (Real.log (Y : ℝ)) :=
      Real.log_le_log (by linarith) (le_trans hwlog2 hlogY)
    rwa [Real.log_div (by linarith) (by norm_num), hw, Real.log_exp] at h1
  have hdrop : primeMass X - primeMass Y
      ≤ (L - Real.log (Real.log (Y : ℝ))) + 2 * B :=
    primeMass_sub_le_logLog_sub hX2 hY2
  have hMX : L - B ≤ primeMass X := by
    have := abs_le.mp (abs_primeMass_sub_logLog_le hX2); linarith [this.1]
  have hmass : primeMass X - primeMass Y ≤ ρ * primeMass X := by
    have hstep : L - Real.log (Real.log (Y : ℝ)) ≤ ρ / 2 * L + Real.log 2 := by
      nlinarith [hloglogY]
    have hbudget : Real.log 2 + 2 * B + ρ * B ≤ ρ / 2 * L := by
      rw [div_le_iff₀ hρ] at hLmass; linarith [hLmass]
    have hρM : ρ * (L - B) ≤ ρ * primeMass X := mul_le_mul_of_nonneg_left hMX hρ.le
    nlinarith
  exact ⟨hY2, hYX, hfreq, hmass⟩

/-! ### The full assembly: (c′) above the threshold, rigidity below it -/

theorem almostRealTwistProp_mono {ρ ρ' : ℝ} {q : ℕ} {χ : DirichletCharacter ℂ q} {t : ℝ} {X : ℕ}
    (h : AlmostRealTwistProp ρ χ t X) (hle : ρ ≤ ρ') : AlmostRealTwistProp ρ' χ t X := by
  obtain ⟨R, hR0, hRM, hclose⟩ := h
  exact ⟨R, hR0, hRM,
    le_trans hclose (mul_le_mul_of_nonneg_right hle (primeMass_nonneg X))⟩

/-- **THE DICHOTOMY, from (c′) and rigidity.**  Above the threshold the bootstrap plus the
Archimedean bound; below it the reduction scale plus rigidity.  Nothing else. -/
theorem twistAlmostRealPropDichotomy_of_inputs {A : ℕ} {η ρ θ δ₀ δ ρ' : ℝ}
    (harch : ArchimedeanCorrelationBoundAbove A η (smallShiftThreshold ρ))
    (hrig : CharacterClusterRigidity A θ) (hθ : 0 < θ)
    (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hδ₀ : 0 < δ₀) (hδ₀θ : δ₀ < θ) (hδ₀1 : δ₀ < 1) (hρδ : ρ ≤ δ₀ / 2)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδle : δ ≤ δ₀ / 2) (hρρ' : 2 * ρ ≤ ρ')
    (hboot : (A : ℝ) * Real.sqrt (2 * δ) < η) :
    TwistAlmostRealPropDichotomy A δ ρ' := by
  classical
  obtain ⟨Xa, hXa2, hXa⟩ := harch
  obtain ⟨Xs, hXs2, hXs⟩ := exists_reductionScale hρ hρ1
  obtain ⟨Xr, hXr2, hXr⟩ :=
    almostRealProp_or_far_of_reductionScale hrig hθ hδ₀ hδ₀θ hδ₀1 hρ hρδ
  set G : ℝ := η - (A : ℝ) * Real.sqrt (2 * δ) with hG
  have hGpos : 0 < G := by rw [hG]; linarith
  obtain ⟨Xm, hXm2, hXm⟩ := exists_primeMass_ge ((2 * primeMass A + 1) / G)
  refine ⟨max (max Xa Xs) (max Xr Xm),
    le_trans hXa2 (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro X hX q hq hqA χ t ht
  have hXXa : Xa ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXXs : Xs ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXXr : Xr ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXXm : Xm ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hX2 : 2 ≤ X := le_trans hXa2 hXXa
  have hMnn : 0 ≤ primeMass X := primeMass_nonneg X
  by_cases hsmall : |t| ≤ smallShiftThreshold ρ X
  · -- below the threshold: the reduction scale, then rigidity
    rcases hXr X hXXr q hq hqA χ t (shortWindow ρ X) (hXs X hXXs t hsmall) with har | hfar
    · exact Or.inl (almostRealTwistProp_mono har hρρ')
    · refine Or.inr (le_trans hfar ?_)
      exact mul_le_mul_of_nonneg_right (by linarith) hMnn
  · -- above the threshold: the bootstrap, then (c′)
    right
    rw [not_le] at hsmall
    set k : ℕ := q.totient with hk
    have hk1 : 1 ≤ k := Nat.totient_pos.mpr hq
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hkA : (k : ℝ) ≤ (A : ℝ) := by
      exact_mod_cast le_trans (Nat.totient_le q) hqA
    have habs : |(k : ℝ) * t| = (k : ℝ) * |t| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ))]
    have hfreq : smallShiftThreshold ρ X < |(k : ℝ) * t| := by
      rw [habs]; nlinarith [abs_nonneg t]
    have hvup : |(k : ℝ) * t| ≤ (A : ℝ) * (A : ℝ) * X := by
      rw [habs]
      have hAnn : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
      calc (k : ℝ) * |t| ≤ (A : ℝ) * ((A : ℝ) * X) :=
            mul_le_mul hkA ht (abs_nonneg t) hAnn
        _ = (A : ℝ) * (A : ℝ) * X := by ring
    refine norm_twistCorr_le_of_archCorr_le χ hq t hX2 hδ0.le hδ1
      (hXa X hXXa ((k : ℝ) * t) hfreq hvup) ?_
    have hbig : (2 * primeMass A + 1) / G ≤ primeMass X := hXm X hXXm
    have hGM : 2 * primeMass A + 1 ≤ G * primeMass X := by
      rw [div_le_iff₀ hGpos] at hbig; linarith [hbig]
    have hsqrt : (0 : ℝ) ≤ Real.sqrt (2 * δ) := Real.sqrt_nonneg _
    have hkle : (k : ℝ) * Real.sqrt (2 * δ) * primeMass X
        ≤ (A : ℝ) * Real.sqrt (2 * δ) * primeMass X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkA hsqrt) hMnn
    have hmq : primeMass q ≤ primeMass A := primeMass_mono hqA
    have hGexp : G * primeMass X
        = η * primeMass X - (A : ℝ) * Real.sqrt (2 * δ) * primeMass X := by rw [hG]; ring
    rw [hGexp] at hGM
    linarith

/-- Choosing every parameter, at a tolerance `ρ'` fixed by the consumer. -/
theorem exists_twistAlmostRealPropDichotomy {A : ℕ} {θ : ℝ} (hθ : 0 < θ)
    (hrig : CharacterClusterRigidity A θ)
    (harch : ∀ r : ℝ, 0 < r → r < 1 →
      ∃ η : ℝ, 0 < η ∧ ArchimedeanCorrelationBoundAbove A η (smallShiftThreshold r))
    {ρ' : ℝ} (hρ' : 0 < ρ') :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ TwistAlmostRealPropDichotomy A δ ρ' := by
  set δ₀ : ℝ := min (min (θ / 2) (1 / 2)) ρ' with hδ₀def
  have hδ₀ : 0 < δ₀ := lt_min (lt_min (by linarith) (by norm_num)) hρ'
  have hδ₀θ : δ₀ < θ := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith)
  have hδ₀1 : δ₀ < 1 :=
    lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by norm_num)
  have hδ₀ρ' : δ₀ ≤ ρ' := min_le_right _ _
  set ρ : ℝ := δ₀ / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  have hρ1 : ρ < 1 := by rw [hρdef]; linarith
  have hρδ : ρ ≤ δ₀ / 2 := le_of_eq hρdef
  have hρρ' : 2 * ρ ≤ ρ' := by rw [hρdef]; linarith
  obtain ⟨η, hη, harchρ⟩ := harch ρ hρ hρ1
  have hApos : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  set R : ℝ := η / (2 * ((A : ℝ) + 1)) with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  set δ : ℝ := min (min (δ₀ / 2) (1 / 2)) (R ^ 2 / 2) with hδdef
  have hδ0 : 0 < δ := lt_min (lt_min (by linarith) (by norm_num)) (by positivity)
  have hδ1 : δ < 1 :=
    lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by norm_num)
  have hδle : δ ≤ δ₀ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hboot : (A : ℝ) * Real.sqrt (2 * δ) < η := by
    have h2δ : 2 * δ ≤ R ^ 2 := by
      have : δ ≤ R ^ 2 / 2 := min_le_right _ _
      linarith
    have hsq : Real.sqrt (2 * δ) ≤ R := by
      have := Real.sqrt_le_sqrt h2δ
      rwa [Real.sqrt_sq hRpos.le] at this
    have hAnn : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
    have hmul : (A : ℝ) * Real.sqrt (2 * δ) ≤ (A : ℝ) * R :=
      mul_le_mul_of_nonneg_left hsq hAnn
    have hAR : (A : ℝ) * R < η := by
      rw [hR, mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  exact ⟨δ, hδ0, hδ1.le,
    twistAlmostRealPropDichotomy_of_inputs harchρ hrig hθ hρ hρ1 hδ₀ hδ₀θ hδ₀1 hρδ
      hδ0 hδ1 hδle hρρ' hboot⟩

/-- **THE PAYOFF, on (c′) and character-cluster rigidity.**  C1's two-point leaf in logarithmic
average, for every `ζ = e(t/b) ≠ 1`.  The small-shift band is *proved*, not assumed. -/
theorem twoPointElliottLog_of_archimedean_and_rigidity {b p q : ℕ} {t : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q) (hu : (phase (t / b)).re < 1)
    (hrig : ∀ A : ℕ, ∃ θ : ℝ, 0 < θ ∧ CharacterClusterRigidity A θ)
    (harch : ∀ (A : ℕ) (r : ℝ), 0 < r → r < 1 →
      ∃ η : ℝ, 0 < η ∧ ArchimedeanCorrelationBoundAbove A η (smallShiftThreshold r)) :
    TwoPointElliottLog b p q t := by
  refine twoPointElliottLog_of_nonPretentious hp hq hpq
    (uniformlyNonPretentious_zetaOmega_of_almostRealProp hu ?_)
  intro A ρ hρ
  obtain ⟨θ, hθ, hrigA⟩ := hrig A
  exact exists_twistAlmostRealPropDichotomy hθ hrigA (harch A) hρ

/-- **The same payoff, with rigidity replaced by its lap-91 source.**  The two remaining inputs are
now (c′) — the Archimedean bound above the threshold, the only zero-free-region site — and
`PrimeDensityAP`, Mertens in arithmetic progressions.  Both are honest classical statements, and
the threshold they are split at is consistent: at `|v|` just above `smallShiftThreshold ρ X` the
true size of `archCorr` is `≈ (1−ρ)·M(X)`, so (c′) holds there. -/
theorem twoPointElliottLog_of_archimedean_and_primeDensity {b p q : ℕ} {t : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q) (hu : (phase (t / b)).re < 1)
    (hdens : ∀ A : ℕ, ElliottCharRigidity.PrimeDensityAP A)
    (harch : ∀ (A : ℕ) (r : ℝ), 0 < r → r < 1 →
      ∃ η : ℝ, 0 < η ∧ ArchimedeanCorrelationBoundAbove A η (smallShiftThreshold r)) :
    TwoPointElliottLog b p q t :=
  twoPointElliottLog_of_archimedean_and_rigidity hp hq hpq hu
    (ElliottCharRigidity.exists_characterClusterRigidity_all hdens) harch

end

end NormalNumbers.ElliottSmallShift
