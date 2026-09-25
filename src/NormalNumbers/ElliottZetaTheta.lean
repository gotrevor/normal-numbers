import NormalNumbers.ElliottSliceCapModerate

/-!
# The moderate band at a GENERAL zero-free-region exponent

Laps 113–117 built the moderate band with the exponent `9` hard-wired, because that is what the
in-repo `PNTPort.ZetaZeroFree9` delivers.  Reading those proofs back, the exponent enters in
**exactly one place** — `log(1/T) = θ·log log(|v|+16)` — and every other ingredient
(`norm_slice_add_logDeriv_le`, `sum_log_rpow_le`, `norm_logWeightedSlice_le_trivial`,
`integral_le_const_add_log_add_const`) is exponent-blind.

So the whole chain is parametric in `θ`, and this file makes it so.  The payoff is not elegance:

**It turns the campaign's one remaining cited axiom into a literature-standard statement.**
`ElliottArchBands.ArchCorrNearMaxHeight` is a bespoke `Prop` about `archCorr`, which a reader must
take on trust as "being Vinogradov".  `ZetaLogDerivExponent θ` below is instead the *same shape* as
the in-repo, already-proved `PNTPort.LogDerivZetaBndUnif99` — a bound `‖ζ'/ζ‖ ≪ (log|t|)^θ` on
`Re s ≥ 1`.  The repo owns the instance `θ = 9`; Vinogradov–Korobov is the instance `θ = 2/3`.
Once the chain is parametric, the axiom to cite is "`ZetaLogDerivExponent θ` for some `θ < 1`",
which is checkable against the literature at a glance and which any future improvement to
`PNTPort.ZetaBounds` discharges automatically.

**EA-1 boundary audit of `ZetaLogDerivExponent θ`.**
* `|Im s| = 1` (left edge): LHS is a finite constant on the compact box; RHS is
  `C·(log 17)^θ ≥ C` for `θ ≥ 0`.  True.
* `|Im s| → ∞`: LHS is what the zero-free region gives; RHS `→ ∞`.  True for the θ that region
  supports, false for smaller θ — i.e. the `Prop` is exactly as strong as the region, which is the
  point.
* `Re s → ∞`: LHS `→ 0`; the hypothesis `Re s ≤ 3` is there only to run the compactness patch, not
  for truth.
* `θ` monotonicity: larger `θ` is a weaker hypothesis (`zetaLogDerivExponent_mono` below), so the
  campaign should cite the *largest* `θ` that still closes the consumer.  That threshold is
  `θ < 1`; see `ElliottZetaThetaLedger` (next lap).
-/

open Complex Set

namespace NormalNumbers.ElliottZetaTheta

open NormalNumbers.ElliottDamped NormalNumbers.ElliottZetaModerate

noncomputable section

/-- **A zero-free region of exponent `θ`, in the form this campaign consumes.**
`‖ζ'/ζ(s)‖ ≤ C·(log(|Im s|+16))^θ` on `1 ≤ Re s ≤ 3`, `|Im s| ≥ 1`.

`θ = 9` is a **theorem** here (`zetaLogDerivExponent_nine`, from `PNTPort.LogDerivZetaBndUnif99`).
`θ = 2/3` is Vinogradov–Korobov. -/
def ZetaLogDerivExponent (θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 3 → 1 ≤ |s.im| →
    ‖logDeriv riemannZeta s‖ ≤ C * (Real.log (|s.im| + 16)) ^ θ

/-- `log(|t|+16) ≥ 1` whenever `t` is real — the basic positivity every estimate here needs. -/
theorem one_le_log_add_sixteen (t : ℝ) : (1 : ℝ) ≤ Real.log (|t| + 16) := by
  have h16 : (16 : ℝ) ≤ |t| + 16 := by linarith [abs_nonneg t]
  have hmono := Real.log_le_log (by norm_num : (0:ℝ) < 16) h16
  have he : (1 : ℝ) ≤ Real.log 16 := by
    have hexp : Real.exp 1 < 16 := by linarith [Real.exp_one_lt_d9]
    have := Real.log_lt_log (Real.exp_pos 1) hexp
    rw [Real.log_exp] at this; linarith
  linarith

/-- **The exponent is a weakening parameter**: a smaller exponent is a stronger hypothesis.
So citing `ZetaLogDerivExponent θ` for the *largest* admissible `θ` is the honest thing to do. -/
theorem zetaLogDerivExponent_mono {θ θ' : ℝ} (hθ : θ ≤ θ') (h : ZetaLogDerivExponent θ) :
    ZetaLogDerivExponent θ' := by
  obtain ⟨C, hC, hbd⟩ := h
  refine ⟨C, hC, fun s h1 h3 him => le_trans (hbd s h1 h3 him) ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (one_le_log_add_sixteen s.im) hθ

/-- **`ZetaLogDerivExponent 9` IS A THEOREM** — the in-repo de la Vallée Poussin material, restated
in the parametric form.  This is the base case that keeps the parametric chain honest: it is not a
vacuous generalisation, the repo really owns an instance. -/
theorem zetaLogDerivExponent_nine : ZetaLogDerivExponent 9 := by
  obtain ⟨C, hC, hbd⟩ := exists_moderate_logDeriv_bound 3
  refine ⟨C, hC, fun s h1 h3 him => ?_⟩
  have hcast : (Real.log (|s.im| + 16)) ^ (9 : ℝ) = (Real.log (|s.im| + 16)) ^ (9 : ℕ) := by
    rw [← Real.rpow_natCast (Real.log (|s.im| + 16)) 9]; norm_num
  rw [hcast]
  exact hbd s h1 h3 him

/-! ### The cap band at a general exponent -/

/-- The cap-band cutoff at exponent `θ`: `(sliceTheta θ X v)⁻¹ = min ((log(|v|+16))^θ) (log X)`. -/
def sliceTheta (θ : ℝ) (X : ℕ) (v : ℝ) : ℝ :=
  max ((Real.log (|v| + 16)) ^ θ)⁻¹ (Real.log (X : ℝ))⁻¹

theorem one_le_logPow {θ : ℝ} (hθ : 0 ≤ θ) (v : ℝ) :
    (1 : ℝ) ≤ (Real.log (|v| + 16)) ^ θ :=
  Real.one_le_rpow (one_le_log_add_sixteen v) hθ

theorem sliceTheta_le_one {θ : ℝ} (hθ : 0 ≤ θ) {X : ℕ} (hX : 1048576 ≤ X) (v : ℝ) :
    sliceTheta θ X v ≤ 1 := by
  have hXR : (1048576 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX1 : 1 ≤ Real.log (X : ℝ) := by
    have h3 : Real.log 3 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) (by linarith)
    have hexp : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    have := Real.log_lt_log (Real.exp_pos 1) hexp
    rw [Real.log_exp] at this
    linarith
  rw [sliceTheta]
  refine max_le ?_ ?_
  · rw [inv_le_one_iff₀]; exact Or.inr (one_le_logPow hθ v)
  · rw [inv_le_one_iff₀]; exact Or.inr hlogX1

/-- The cap clause at exponent `θ`. -/
def SliceCapModerateTheta (θ C K : ℝ) : Prop :=
  ∀ (X Y : ℕ) (v : ℝ), 1048576 ≤ X → sliceCut X ≤ Y → 1 < |v| →
    ∀ w ∈ Set.Icc (0 : ℝ) (sliceTheta θ X v),
      ‖logWeightedSlice v X Y w‖ ≤ C * (sliceTheta θ X v)⁻¹ + K

/-- **The cap clause, at a general exponent.**  Verbatim the lap-115 two-branch argument with `9`
replaced by `θ`: the dVP branch when `(log(|v|+16))^θ ≤ log X`, the trivial branch otherwise. -/
theorem exists_sliceCapModerateTheta {θ : ℝ} (hθ : 0 ≤ θ) (h : ZetaLogDerivExponent θ) :
    ∃ C ≥ (1 : ℝ), ∃ K ≥ (0 : ℝ), SliceCapModerateTheta θ C K := by
  obtain ⟨C₀, hC₀, hmod⟩ := h
  refine ⟨max C₀ 1, le_max_right _ _,
    (1 + NormalNumbers.ElliottPrimePower.ppCost) + (Real.log 4 + 4), ?_, ?_⟩
  · have h1 := NormalNumbers.ElliottPrimePower.ppCost_nonneg
    have h2 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  intro X Y v hX hY hv1 w hw
  have hX2 : 2 ≤ X := by omega
  have hXR : (1048576 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX1 : 1 ≤ Real.log (X : ℝ) := by
    have h3 : Real.log 3 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) (by linarith)
    have hexp : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    have := Real.log_lt_log (Real.exp_pos 1) hexp
    rw [Real.log_exp] at this
    linarith
  have hlogX0 : 0 < Real.log (X : ℝ) := by linarith
  set a : ℝ := (Real.log (|v| + 16)) ^ θ with ha
  have ha1 : (1 : ℝ) ≤ a := one_le_logPow hθ v
  have ha0 : 0 < a := by linarith
  have hw0 : 0 ≤ w := hw.1
  have hT1 : sliceTheta θ X v ≤ 1 := sliceTheta_le_one hθ hX v
  have hwT : w ≤ sliceTheta θ X v := hw.2
  have hw1 : w ≤ 1 := le_trans hwT hT1
  have hTinv : (sliceTheta θ X v)⁻¹ = min a (Real.log (X : ℝ)) := by
    rcases le_total a (Real.log (X : ℝ)) with hle | hle
    · have hmax : sliceTheta θ X v = a⁻¹ := by
        rw [sliceTheta, ← ha]; exact max_eq_left (inv_anti₀ ha0 hle)
      rw [hmax, inv_inv, min_eq_left hle]
    · have hmax : sliceTheta θ X v = (Real.log (X : ℝ))⁻¹ := by
        rw [sliceTheta, ← ha]; exact max_eq_right (inv_anti₀ hlogX0 hle)
      rw [hmax, inv_inv, min_eq_right hle]
  have hCK : (1 : ℝ) ≤ max C₀ 1 := le_max_right _ _
  have hppn := NormalNumbers.ElliottPrimePower.ppCost_nonneg
  have hlog4 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  rcases le_total a (Real.log (X : ℝ)) with hcase | hcase
  · have hmin : min a (Real.log (X : ℝ)) = a := min_eq_left hcase
    set s : ℂ := NormalNumbers.ElliottBridge.sliceAbscissa X w v with hsdef
    have hre : s.re = 1 + (Real.log (X : ℝ))⁻¹ + w := by
      rw [hsdef]; exact NormalNumbers.ElliottBridge.sliceAbscissa_re w v
    have him : s.im = v := by rw [hsdef]; exact NormalNumbers.ElliottBridge.sliceAbscissa_im w v
    have hδ1 : (Real.log (X : ℝ))⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; exact Or.inr hlogX1
    have hre1 : 1 ≤ s.re := by
      rw [hre]; have : (0:ℝ) < (Real.log (X:ℝ))⁻¹ := by positivity
      linarith
    have hre3 : s.re ≤ 3 := by rw [hre]; linarith
    have him1 : 1 ≤ |s.im| := by rw [him]; linarith
    have hlogd := hmod s hre1 hre3 him1
    rw [him] at hlogd
    have harith := NormalNumbers.ElliottSliceCap.norm_slice_add_logDeriv_le hX hY v w hw0
    have htri : ‖logWeightedSlice v X Y w‖
        ≤ ‖logWeightedSlice v X Y w + logDeriv riemannZeta s‖ + ‖logDeriv riemannZeta s‖ := by
      simpa using norm_sub_le (logWeightedSlice v X Y w + logDeriv riemannZeta s)
        (logDeriv riemannZeta s)
    have hCmax : C₀ ≤ max C₀ 1 := le_max_left _ _
    rw [hTinv, hmin]
    have hprod : C₀ * a ≤ max C₀ 1 * a := mul_le_mul_of_nonneg_right hCmax ha0.le
    rw [← ha] at hlogd
    linarith [hlogd, harith, htri]
  · have hmin : min a (Real.log (X : ℝ)) = Real.log (X : ℝ) := min_eq_right hcase
    have htriv := norm_logWeightedSlice_le_trivial hX2 v Y hw0
    have hle : ((Real.log (X : ℝ))⁻¹ + w)⁻¹ ≤ Real.log (X : ℝ) := by
      have hpos : (0:ℝ) < (Real.log (X : ℝ))⁻¹ := by positivity
      calc ((Real.log (X : ℝ))⁻¹ + w)⁻¹ ≤ ((Real.log (X : ℝ))⁻¹)⁻¹ :=
            inv_anti₀ hpos (by linarith)
        _ = Real.log (X : ℝ) := inv_inv _
    rw [hTinv, hmin]
    have hprod : 1 * Real.log (X : ℝ) ≤ max C₀ 1 * Real.log (X : ℝ) :=
      mul_le_mul_of_nonneg_right hCK hlogX0.le
    rw [one_mul] at hprod
    linarith [htriv, hle]

/-! ### Integration, at a general exponent -/

/-- The full slice input at exponent `θ`; the harmonic clause is lap 106's `sum_log_rpow_le`
(coefficient exactly `1`), so only the cap clause has content. -/
def SliceBoundModerateTheta (θ C K : ℝ) : Prop :=
  ∀ (X Y : ℕ) (v : ℝ), 1048576 ≤ X → sliceCut X ≤ Y → 1 < |v| →
    (∀ w ∈ Set.Icc (0 : ℝ) (sliceTheta θ X v),
        ‖logWeightedSlice v X Y w‖ ≤ C * (sliceTheta θ X v)⁻¹ + K) ∧
    (∀ w ∈ Set.Icc (sliceTheta θ X v) 1, ‖logWeightedSlice v X Y w‖ ≤ w⁻¹ + K)

theorem sliceBoundModerateTheta_of_cap {θ C K : ℝ} (hK : 0 ≤ K)
    (h : SliceCapModerateTheta θ C K) :
    SliceBoundModerateTheta θ C (K + (Real.log 4 + 4)) := by
  intro X Y v hX hY hv1
  have hX2 : 2 ≤ X := by omega
  have hC0 : (0 : ℝ) ≤ Real.log 4 + 4 := by
    have : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · have := h X Y v hX hY hv1 w hw
    linarith
  · have hδT : (Real.log (X : ℝ))⁻¹ ≤ sliceTheta θ X v := le_max_right _ _
    have hXR2 : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
    have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
    have hδpos : (0 : ℝ) < (Real.log (X : ℝ))⁻¹ := by positivity
    have hw0 : 0 < w := lt_of_lt_of_le hδpos (le_trans hδT hw.1)
    have htriv := norm_logWeightedSlice_le_trivial hX2 v Y hw0.le
    have hmono : ((Real.log (X : ℝ))⁻¹ + w)⁻¹ ≤ w⁻¹ := inv_anti₀ hw0 (by linarith)
    linarith

/-- The damped bound at exponent `θ`: `‖dampedPrefix‖ ≤ θ·log log(|v|+16) + K`.  **The exponent
enters here and nowhere else**, through `log((log(|v|+16))^θ) = θ·log log(|v|+16)`. -/
def DampedSeriesBoundModerateTheta (θ K : ℝ) : Prop :=
  ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ (X Y : ℕ) (v : ℝ), X₀ ≤ X → X ≤ Y → 1 < |v| →
    ‖dampedPrefix v X Y‖ ≤ θ * Real.log (Real.log (|v| + 16)) + K

theorem dampedSeriesBoundModerateTheta_of_sliceBound {θ C K : ℝ} (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hC : 0 ≤ C) (h : SliceBoundModerateTheta θ C K) :
    DampedSeriesBoundModerateTheta θ (C + K + tailCost + cutCost) := by
  refine ⟨1048576, by norm_num, ?_⟩
  intro X Y v hX3 hXY hv1
  have hX : 2 ≤ X := by omega
  have hXR : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 3 ≤ X)
  have hlogX : 1 < Real.log (X : ℝ) := by
    have h3 : Real.log 3 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) hXR
    have : (1 : ℝ) < Real.log 3 := by
      have hexp : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      have := Real.log_lt_log (Real.exp_pos 1) hexp
      rwa [Real.log_exp] at this
    linarith
  have hδ0 : 0 < (Real.log (X : ℝ))⁻¹ := by positivity
  have hL : (1 : ℝ) ≤ Real.log (|v| + 16) := one_le_log_add_sixteen v
  have hL0 : 0 < Real.log (|v| + 16) := by linarith
  set a : ℝ := (Real.log (|v| + 16)) ^ θ with ha
  have ha1 : (1 : ℝ) ≤ a := one_le_logPow hθ v
  have ha0 : 0 < a := by linarith
  set T : ℝ := sliceTheta θ X v with hT
  have hδT : (Real.log (X : ℝ))⁻¹ ≤ T := le_max_right _ _
  have hLT : a⁻¹ ≤ T := le_max_left _ _
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hLT
  have hT1 : T ≤ 1 := sliceTheta_le_one hθ hX3 v
  set Y' : ℕ := max Y (sliceCut X) with hY'
  have hXY' : X ≤ Y' := le_trans hXY (le_max_left _ _)
  obtain ⟨hcap, hharm⟩ := h X Y' v hX3 (le_max_right _ _) hv1
  have hmain0 := norm_dampedPrefix_le_of_slice_le_const hX v Y' hδT hT1 hK hC hcap hharm
  have htr := norm_dampedPrefix_transfer hX v Y Y' hXY hXY'
  have hmain : ‖dampedPrefix v X Y‖ ≤ C + Real.log (1 / T) + K + tailCost + cutCost := by
    rw [cutCost] at *; linarith
  have hlogmono : Real.log (1 / T) ≤ θ * Real.log (Real.log (|v| + 16)) := by
    have hstep : Real.log (1 / T) ≤ Real.log a := by
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_iff₀ hT0]
      have hid : a⁻¹ * a = 1 := by field_simp
      nlinarith [hLT, ha0]
    have hpow : Real.log a = θ * Real.log (Real.log (|v| + 16)) := by
      rw [ha, Real.log_rpow hL0]
    linarith [hpow ▸ hstep]
  linarith [hmain, hlogmono]

/-- `‖archCorr v X‖ ≤ θ·log log(|v|+16) + K` on `|v| > 1`.  The damping step is exponent-blind. -/
def ArchCorrModerateTheta (θ K : ℝ) : Prop :=
  ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X → ∀ v : ℝ, 1 < |v| →
    ‖NormalNumbers.ElliottTwistBootstrap.archCorr v X‖
      ≤ θ * Real.log (Real.log (|v| + 16)) + K

theorem archCorrModerateTheta_of_dampedSeriesBound {θ K : ℝ}
    (h : DampedSeriesBoundModerateTheta θ K) : ArchCorrModerateTheta θ (K + dampingCost) := by
  obtain ⟨X₀, hX₀, h⟩ := h
  refine ⟨X₀, hX₀, ?_⟩
  intro X hXX₀ v hv1
  have hX : 2 ≤ X := le_trans hX₀ hXX₀
  have hd := h X X v hXX₀ le_rfl hv1
  have hs := norm_archCorr_sub_dampedPrefix_le' hX v X le_rfl
  calc ‖NormalNumbers.ElliottTwistBootstrap.archCorr v X‖
      ≤ ‖NormalNumbers.ElliottTwistBootstrap.archCorr v X - dampedPrefix v X X‖
        + ‖dampedPrefix v X X‖ := by
        simpa [add_comm] using
          norm_le_norm_add_norm_sub' (NormalNumbers.ElliottTwistBootstrap.archCorr v X)
            (dampedPrefix v X X)

    _ ≤ dampingCost + (θ * Real.log (Real.log (|v| + 16)) + K) := by linarith
    _ = θ * Real.log (Real.log (|v| + 16)) + (K + dampingCost) := by ring

/-- **THE WHOLE MODERATE CHAIN, PARAMETRIC IN `θ`.** -/
theorem exists_archCorrModerateTheta {θ : ℝ} (hθ : 0 ≤ θ) (h : ZetaLogDerivExponent θ) :
    ∃ K : ℝ, ArchCorrModerateTheta θ K := by
  obtain ⟨C, hC1, K, hK0, hcap⟩ := exists_sliceCapModerateTheta hθ h
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hlog4 : (0:ℝ) ≤ Real.log 4 + 4 := by
    have : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  exact ⟨_, archCorrModerateTheta_of_dampedSeriesBound
    (dampedSeriesBoundModerateTheta_of_sliceBound hθ (by linarith) hC0
      (sliceBoundModerateTheta_of_cap hK0 hcap))⟩

/-! ### THE PAYOFF: the bespoke wall axiom replaced by a standard statement about `ζ` -/

theorem five_le_exp_two : (5 : ℝ) ≤ Real.exp 2 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hpow : Real.exp 1 ^ (2 : ℕ) = Real.exp 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (1:ℝ)]

theorem seventeen_le_exp_five : (17 : ℝ) ≤ Real.exp 5 := by
  have h2 : (5 : ℝ) ≤ Real.exp 2 := five_le_exp_two
  have h3 : (4 : ℝ) ≤ Real.exp 3 := by
    have := Real.add_one_le_exp (3 : ℝ); linarith
  have hsplit : Real.exp 5 = Real.exp 2 * Real.exp 3 := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  nlinarith

/-- **THE WALL AXIOM, RESTATED AS A STANDARD FACT ABOUT `ζ`.**

`ZetaLogDerivExponent θ` with `θ < 1` implies `ArchCorrNearMaxHeight A ν (1−θ) K` for **every** `A`
and every cut `ν < 1`, with `K` uniform in `A` and `ν`.

This is the point of the whole file.  `ArchCorrNearMaxHeight` is a bespoke `Prop` about `archCorr`
that a reader has to take on faith as "being Vinogradov"; `ZetaLogDerivExponent θ` is the *same
shape* as the in-repo, already-proved `PNTPort.LogDerivZetaBndUnif99`, differing only in the
exponent.  The repo owns `θ = 9` (`zetaLogDerivExponent_nine`); **Vinogradov–Korobov is `θ = 2/3`**,
and `2/3 < 1`.  So the campaign's remaining debt is exactly:

> improve the in-repo zero-free-region exponent from `9` to anything below `1`.

**Why the cut `ν` is irrelevant** (this confirms lap 119's audit in Lean): the proof never uses the
lower cut except to force `|v| > 1`.  The saving comes entirely from `|v| ≤ A²X`, which gives
`log log(|v|+16) ≤ log 2 + log log X` — so a bound `θ·log log(|v|+16) + K₁` is already
`θ·L + (θ log 2 + K₁)`, i.e. a proportional saving of `1 − θ` on the *whole* range.

**EA-1 boundary check.**  At `|v| = A²X` (the extreme the `Prop` allows) the two sides are
`θ·(L + log 2) + K₁` against `θ·L + K`: equality is attained at `K = θ log 2 + K₁`, so the constant
is sharp for this argument and cannot be shaved.  At the lower end `|v| → 1⁺` the left side is
`O(1)`, far below.  Both pass. -/
theorem archCorrNearMaxHeight_of_exponent {θ : ℝ} (hθ0 : 0 ≤ θ) (h : ZetaLogDerivExponent θ) :
    ∃ K : ℝ, ∀ (A : ℕ) (ν : ℝ), ν < 1 →
      NormalNumbers.ElliottArchBands.ArchCorrNearMaxHeight A ν (1 - θ) K := by
  obtain ⟨K₁, X₀, hX₀2, hmod⟩ := exists_archCorrModerateTheta hθ0 h
  refine ⟨θ * Real.log 2 + K₁, ?_⟩
  intro A ν hν1
  obtain ⟨X₃, hX₃2, hX₃⟩ :=
    NormalNumbers.ElliottSmallShift.exists_logLog_ge (2 / (1 - ν))
  refine ⟨max (max X₀ X₃) (max (A * A + 16) 2),
    le_trans (le_max_right _ _) (le_max_right _ _), ?_⟩
  intro X hX v hcut hvA
  have hXX₀ : X₀ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXX₃ : X₃ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXA : A * A + 16 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX2 : 2 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  set L : ℝ := Real.log (Real.log (X : ℝ)) with hLdef
  have hLge : 2 / (1 - ν) ≤ L := hX₃ X hXX₃
  have hν0 : (0 : ℝ) < 1 - ν := by linarith
  have hL2 : (2 : ℝ) ≤ (1 - ν) * L := by
    rw [div_le_iff₀ hν0] at hLge
    linarith [hLge, mul_comm (1 - ν) L]
  -- the cut is above `17`, which forces `|v| > 1`
  have hcut17 : (17 : ℝ) ≤ NormalNumbers.ElliottArchBands.heightCut ν X := by
    rw [NormalNumbers.ElliottArchBands.heightCut]
    refine le_trans seventeen_le_exp_five (Real.exp_le_exp.mpr ?_)
    refine le_trans five_le_exp_two (Real.exp_le_exp.mpr ?_)
    linarith
  have hv1 : (1 : ℝ) < |v| := by
    have := lt_of_le_of_lt hcut17 hcut
    linarith
  -- the range bound `|v| ≤ A²X` gives the proportional saving
  have hXR : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hAX : (A : ℝ) * (A : ℝ) * X + 16 ≤ (X : ℝ) * X := by
    have hAXn : ((A * A + 16 : ℕ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast hXA
    push_cast at hAXn
    nlinarith
  have hbound : |v| + 16 ≤ (X : ℝ) * X := by linarith
  have hlogv : Real.log (|v| + 16) ≤ 2 * Real.log (X : ℝ) := by
    have h1 : Real.log (|v| + 16) ≤ Real.log ((X : ℝ) * X) :=
      Real.log_le_log (by linarith [abs_nonneg v]) hbound
    rwa [Real.log_mul (by linarith) (by linarith), ← two_mul] at h1
  have hLpos : (0 : ℝ) < Real.log (|v| + 16) := by
    have := one_le_log_add_sixteen v; linarith
  have hloglog : Real.log (Real.log (|v| + 16)) ≤ Real.log 2 + L := by
    have h1 : Real.log (Real.log (|v| + 16)) ≤ Real.log (2 * Real.log (X : ℝ)) :=
      Real.log_le_log hLpos hlogv
    rw [Real.log_mul (by norm_num) (ne_of_gt hlogX), ← hLdef] at h1
    exact h1
  have hmodb := hmod X hXX₀ v hv1
  have hstep : θ * Real.log (Real.log (|v| + 16)) ≤ θ * (Real.log 2 + L) :=
    mul_le_mul_of_nonneg_left hloglog hθ0
  have : (1 - (1 - θ)) * L = θ * L := by ring
  rw [this]
  linarith

end

end NormalNumbers.ElliottZetaTheta
