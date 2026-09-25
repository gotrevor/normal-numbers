import NormalNumbers.ElliottTwistRepair

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

end

end NormalNumbers.ElliottSmallShift
