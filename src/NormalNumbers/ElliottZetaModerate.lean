import NormalNumbers.ElliottZetaPole
import PNTPort.ZetaBounds

/-!
# The moderate-band `ζ'/ζ` bound, sourced from the in-repo de la Vallée Poussin material

The sub-unit cap clause (`ElliottSliceCap`) needed only the *pole* of `ζ` — no zero-free region.
The **moderate** band `|v| > 1` is different: there `s = 1 + δ + w + iv` is far from the pole and
the only thing that keeps `‖ζ'/ζ(s)‖` small is a zero-free region.

**EP-1 provenance.**  Searched before stating anything:
(i) `src/PNTPort/ZetaBounds.lean` — **HIT**: `LogDerivZetaBndUnif99 : LogDerivZetaBndUnifGenProp 9 9`
    gives `‖ζ'/ζ(σ+it)‖ ≤ C·(log|t|)^9` for every `σ ≥ 1 − A/(log|t|)^9` and every `|t| > 3`,
    sorry-free and `[propext, Classical.choice, Quot.sound]`-clean.
(ii) `src/NormalNumbers/G4*.lean`, `Erdos67b.PrimeEstimates` — nothing of this strength.
(iii) mathlib — has `riemannZeta_ne_zero_of_one_le_re` (the `1`-line only, no quantitative region).

So this file is a *repackaging*, not a new citation: it converts the `PNTPort` statement into the
shape `ElliottDamped`'s cap band consumes, and patches the compact leftover `1 ≤ |t| ≤ 3` by
continuity.

**The exponent 9 is deliberate and free.**  The cap band will be restated at
`T = (log(|v|+16))^{-9}`; the harmonic band (coefficient exactly `1`, lap 106) then delivers
`log(1/T) = 9·log log(|v|+16)`, i.e. the moderate input acquires an absolute constant `9`, which
`archCorrLargeShift_of_moderate_and_nearMax` absorbs by moving the height cut.  Since the far band
was already Vinogradov, nothing is lost.

**Boundary audit (EA-1).**  Both sides at the extremes of the quantified range:
* `|t| → ∞`, `σ → 1⁺`: LHS `‖ζ'/ζ‖` is genuinely `≍ (log|t|)^{...}` in the worst case the
  dVP region allows; RHS `C(log(|t|+16))^9 → ∞` faster.  True.
* `|t| = 1` (the left edge): LHS is a fixed finite number on the compact region; RHS is
  `C(log 17)^9 ≥ C·2.8^9 > C`.  True, with `C` taken as the compact-region bound.
* `σ → ∞`: LHS `→ 0` (the Dirichlet series converges to `−Λ(1) = 0`), RHS fixed.  True; the
  hypothesis `σ ≤ B` is therefore not needed for truth, only to run the compactness patch.
-/

open Complex Set

namespace NormalNumbers.ElliottZetaModerate

noncomputable section

/-! ### The compact patch `1 ≤ |Im s| ≤ 3` -/

/-- On the compact box `1 ≤ Re s ≤ B`, `1 ≤ |Im s| ≤ 3` the function `ζ'/ζ` is continuous
(`ζ ≠ 0` because `Re s ≥ 1` and `s ≠ 1`), hence bounded. -/
theorem exists_midband_bound (B : ℝ) :
    ∃ K > 0, ∀ s : ℂ, 1 ≤ s.re → s.re ≤ B → 1 ≤ |s.im| → |s.im| ≤ 3 →
      ‖logDeriv riemannZeta s‖ ≤ K := by
  set S : Set ℂ := {s | 1 ≤ s.re} ∩ ({s | s.re ≤ B} ∩ ({s | 1 ≤ |s.im|} ∩ {s | |s.im| ≤ 3}))
    with hS
  have hclosed : IsClosed S := by
    rw [hS]
    refine (isClosed_le continuous_const Complex.continuous_re).inter ?_
    refine (isClosed_le Complex.continuous_re continuous_const).inter ?_
    refine (isClosed_le continuous_const (Complex.continuous_im.abs)).inter ?_
    exact isClosed_le (Complex.continuous_im.abs) continuous_const
  have hbdd : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := |B| + 4)).subset ?_
    intro s hs
    obtain ⟨h1, h2, -, h4⟩ := hs
    simp only [Set.mem_setOf_eq] at h1 h2 h4
    have hB : B ≤ |B| := le_abs_self B
    have hre : |s.re| ≤ |B| := by rw [abs_le]; constructor <;> [linarith; linarith]
    have hnorm : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hcompact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have hne1 : ∀ s ∈ S, s ≠ 1 := by
    intro s hs h
    obtain ⟨-, -, h3, -⟩ := hs
    simp only [Set.mem_setOf_eq, h] at h3
    norm_num at h3
  have hcont : ContinuousOn (logDeriv riemannZeta) S := by
    intro s hs
    have hs1 : s ≠ 1 := hne1 s hs
    have h1 : 1 ≤ s.re := hs.1
    have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re h1
    have hanal : AnalyticAt ℂ riemannZeta s :=
      analyticOn_riemannZeta s (by simpa using hs1)
    exact ContinuousAt.continuousWithinAt
      (hanal.deriv.continuousAt.div hanal.continuousAt hz)
  obtain ⟨K₀, hK₀⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨|K₀| + 1, by positivity, ?_⟩
  intro s h1 h2 h3 h4
  have := hK₀ s ⟨h1, h2, h3, h4⟩
  have := le_abs_self K₀
  linarith

/-! ### The far part `|Im s| > 3`, straight from `PNTPort` -/

/-- `LogDerivZetaBndUnif99` restated for a point `s` of the closed half-plane `Re s ≥ 1`. -/
theorem exists_highband_bound :
    ∃ C > 0, ∀ s : ℂ, 1 ≤ s.re → 3 < |s.im| →
      ‖logDeriv riemannZeta s‖ ≤ C * (Real.log |s.im|) ^ (9 : ℕ) := by
  obtain ⟨A, hA, C, hC, hbd⟩ := _root_.LogDerivZetaBndUnif99
  refine ⟨C, hC, ?_⟩
  intro s h1 h3
  have hlog : 1 < Real.log |s.im| := by
    have h3' : (3 : ℝ) < |s.im| := h3
    have : Real.log 3 < Real.log |s.im| := Real.log_lt_log (by norm_num) h3'
    have he : (1 : ℝ) < Real.log 3 := by
      have hexp : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      have := Real.log_lt_log (Real.exp_pos 1) hexp
      rwa [Real.log_exp] at this
    linarith
  have hmem : s.re ∈ Ici (1 - A / Real.log |s.im| ^ (9 : ℝ)) := by
    have hpow : (0 : ℝ) < Real.log |s.im| ^ (9 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have hA0 : 0 < A := hA.1
    have : (0 : ℝ) < A / Real.log |s.im| ^ (9 : ℝ) := by positivity
    simp only [mem_Ici]
    linarith
  have := hbd s.re s.im h3 hmem
  rw [Complex.re_add_im] at this
  have hcast : (Real.log |s.im|) ^ (9 : ℝ) = (Real.log |s.im|) ^ (9 : ℕ) := by
    rw [← Real.rpow_natCast (Real.log |s.im|) 9]; norm_num
  rw [hcast] at this
  simpa [logDeriv_apply] using this

/-! ### The moderate-band bound -/

/-- **THE MODERATE-BAND `ζ'/ζ` BOUND.**  For `1 ≤ Re s ≤ B` and `|Im s| ≥ 1`,
`‖ζ'/ζ(s)‖ ≤ C·(log(|Im s| + 16))^9`.  This is the de la Vallée Poussin-strength input the
moderate cap clause consumes, and it is a **theorem**, from `_root_.LogDerivZetaBndUnif99`
(`|Im s| > 3`) plus continuity on the compact box `1 ≤ |Im s| ≤ 3`. -/
theorem exists_moderate_logDeriv_bound (B : ℝ) :
    ∃ C > 0, ∀ s : ℂ, 1 ≤ s.re → s.re ≤ B → 1 ≤ |s.im| →
      ‖logDeriv riemannZeta s‖ ≤ C * (Real.log (|s.im| + 16)) ^ (9 : ℕ) := by
  obtain ⟨C₁, hC₁, hhigh⟩ := exists_highband_bound
  obtain ⟨K, hK, hmid⟩ := exists_midband_bound B
  refine ⟨max C₁ K, lt_of_lt_of_le hC₁ (le_max_left _ _), ?_⟩
  intro s h1 h2 h3
  have hL : (1 : ℝ) ≤ Real.log (|s.im| + 16) := by
    have h17 : (17 : ℝ) ≤ |s.im| + 16 := by linarith
    have : Real.log 17 ≤ Real.log (|s.im| + 16) := Real.log_le_log (by norm_num) h17
    have he : (1 : ℝ) ≤ Real.log 17 := by
      have hexp : Real.exp 1 < 17 := by linarith [Real.exp_one_lt_d9]
      have := Real.log_lt_log (Real.exp_pos 1) hexp
      rw [Real.log_exp] at this; linarith
    linarith
  have hpow1 : (1 : ℝ) ≤ (Real.log (|s.im| + 16)) ^ (9 : ℕ) := one_le_pow₀ hL
  rcases le_or_gt |s.im| 3 with hle | hgt
  · have hb := hmid s h1 h2 h3 hle
    have : K ≤ max C₁ K := le_max_right _ _
    nlinarith [hK.le]
  · have hb := hhigh s h1 hgt
    have hmono : (Real.log |s.im|) ^ (9 : ℕ) ≤ (Real.log (|s.im| + 16)) ^ (9 : ℕ) := by
      refine pow_le_pow_left₀ ?_ ?_ 9
      · exact Real.log_nonneg (by linarith)
      · exact Real.log_le_log (by linarith) (by linarith)
    have hmax : C₁ ≤ max C₁ K := le_max_left _ _
    nlinarith [pow_nonneg (Real.log_nonneg (by linarith : (1:ℝ) ≤ |s.im|)) 9, hC₁.le]

end

end NormalNumbers.ElliottZetaModerate
