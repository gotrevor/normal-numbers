import NormalNumbers.ElliottSliceCap
import NormalNumbers.ElliottZetaModerate

/-!
# (c′-II-a) cap clause: the moderate-band cap bound is a theorem

Mirror of `ElliottSliceCap.exists_sliceCapSmall` on the band `|v| > 1`.  Two facts make it short:

* `ElliottSliceCap.norm_slice_add_logDeriv_le` is **band-agnostic** — it bounds
  `‖logWeightedSlice v X Y w + ζ'/ζ(sliceAbscissa X w v)‖` by `1 + ppCost` for *every* `v` and
  every `w ≥ 0`, so only the analytic input changes;
* the analytic input is `ElliottZetaModerate.exists_moderate_logDeriv_bound` (lap 113), which is
  itself a theorem, from the in-repo `PNTPort.LogDerivZetaBndUnif99`.

**The two-branch split.**  `(sliceT9 X v)⁻¹ = min ((log(|v|+16))^9) (log X)`.
* If `(log(|v|+16))^9 ≤ log X` the min is `(log(|v|+16))^9` and the **dVP** bound covers it.
* Otherwise the min is `log X` and the **trivial** bound `norm_logWeightedSlice_le_trivial`
  covers it — no `ζ'/ζ` is needed in that branch at all.

**Boundary audit (EA-1).**  At the junction `(log(|v|+16))^9 = log X` the branches give
`C₀·log X + (1+ppCost)` and `log X + (log 4 + 4)`; both are `≤ C·(sliceT9)⁻¹ + K` with the stated
`C, K`, so the split has no gap.  At the left edge `|v| → 1⁺` the constraint is the dVP branch
with `(log 17)^9 ≈ 2.8^9`, finite and `≥ 1`; at `|v| → ∞` with `X` fixed the trivial branch takes
over and the claim degenerates to `‖slice‖ ≤ C·log X + K`, which is true and weak — correctly so,
since no saving is available there (that regime is the Vinogradov wall, handled by
`ArchCorrNearMaxHeight`).
-/

open Finset

namespace NormalNumbers.ElliottSliceCapModerate

open NormalNumbers.ElliottDamped NormalNumbers.ElliottSliceCap NormalNumbers.ElliottZetaModerate
open NormalNumbers.ElliottPrimePower NormalNumbers.ElliottBridge

noncomputable section

/-- `sliceT9 X v ≤ 1` whenever `X ≥ 3`: both branches of the `max` are reciprocals of reals `≥ 1`
(`(log(|v|+16))^9 ≥ (log 17)^9 ≥ 1` and `log X ≥ 1`). -/
theorem sliceT9_le_one {X : ℕ} (hX : 1048576 ≤ X) (v : ℝ) : sliceT9 X v ≤ 1 := by
  have hXR : (1048576 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX1 : 1 ≤ Real.log (X : ℝ) := by
    have h3 : Real.log 3 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) (by linarith)
    have hexp : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    have := Real.log_lt_log (Real.exp_pos 1) hexp
    rw [Real.log_exp] at this
    linarith
  have hL : (1 : ℝ) ≤ Real.log (|v| + 16) := by
    have h16 : (16 : ℝ) ≤ |v| + 16 := by linarith [abs_nonneg v]
    have hmono := Real.log_le_log (by norm_num : (0:ℝ) < 16) h16
    have he : (1 : ℝ) ≤ Real.log 16 := by
      have hexp : Real.exp 1 < 16 := by linarith [Real.exp_one_lt_d9]
      have := Real.log_lt_log (Real.exp_pos 1) hexp
      rw [Real.log_exp] at this; linarith
    linarith
  have hpow : (1 : ℝ) ≤ (Real.log (|v| + 16)) ^ (9 : ℕ) := one_le_pow₀ hL
  rw [sliceT9]
  refine max_le ?_ ?_
  · rw [inv_le_one_iff₀]; exact Or.inr hpow
  · rw [inv_le_one_iff₀]; exact Or.inr hlogX1

/-- **(c′-II-a) CAP CLAUSE IS A THEOREM.** -/
theorem exists_sliceCapModerate9 : ∃ C ≥ (1 : ℝ), ∃ K ≥ (0 : ℝ), SliceCapModerate9 C K := by
  obtain ⟨C₀, hC₀, hmod⟩ := exists_moderate_logDeriv_bound 3
  refine ⟨max C₀ 1, le_max_right _ _, (1 + ppCost) + (Real.log 4 + 4), ?_, ?_⟩
  · have h1 := ppCost_nonneg
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
  have hL : (1 : ℝ) ≤ Real.log (|v| + 16) := by
    have h17 : (17 : ℝ) ≤ |v| + 16 := by linarith [abs_nonneg v]
    have := Real.log_le_log (by norm_num : (0:ℝ) < 17) h17
    have he : (1 : ℝ) ≤ Real.log 17 := by
      have hexp : Real.exp 1 < 17 := by linarith [Real.exp_one_lt_d9]
      have := Real.log_lt_log (Real.exp_pos 1) hexp
      rw [Real.log_exp] at this; linarith
    linarith
  set a : ℝ := (Real.log (|v| + 16)) ^ (9 : ℕ) with ha
  have ha1 : (1 : ℝ) ≤ a := one_le_pow₀ hL
  have ha0 : 0 < a := by linarith
  have hw0 : 0 ≤ w := hw.1
  have hT1 : sliceT9 X v ≤ 1 := sliceT9_le_one hX v
  have hwT : w ≤ sliceT9 X v := hw.2
  have hw1 : w ≤ 1 := le_trans hwT hT1
  -- `(sliceT9 X v)⁻¹ = min a (log X)`
  have hTinv : (sliceT9 X v)⁻¹ = min a (Real.log (X : ℝ)) := by
    rcases le_total a (Real.log (X : ℝ)) with h | h
    · have hmax : sliceT9 X v = a⁻¹ := by
        rw [sliceT9, ← ha]; exact max_eq_left (inv_anti₀ ha0 h)
      rw [hmax, inv_inv, min_eq_left h]
    · have hmax : sliceT9 X v = (Real.log (X : ℝ))⁻¹ := by
        rw [sliceT9, ← ha]; exact max_eq_right (inv_anti₀ hlogX0 h)
      rw [hmax, inv_inv, min_eq_right h]
  have hmin_nonneg : 0 ≤ min a (Real.log (X : ℝ)) := le_min ha0.le hlogX0.le
  have hCK : (1 : ℝ) ≤ max C₀ 1 := le_max_right _ _
  have hppn := ppCost_nonneg
  have hlog4 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  rcases le_total a (Real.log (X : ℝ)) with hcase | hcase
  · -- dVP branch
    have hmin : min a (Real.log (X : ℝ)) = a := min_eq_left hcase
    set s : ℂ := sliceAbscissa X w v with hsdef
    have hre : s.re = 1 + (Real.log (X : ℝ))⁻¹ + w := by rw [hsdef]; exact sliceAbscissa_re w v
    have him : s.im = v := by rw [hsdef]; exact sliceAbscissa_im w v
    have hδ1 : (Real.log (X : ℝ))⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; exact Or.inr hlogX1
    have hre1 : 1 ≤ s.re := by
      rw [hre]; have : (0:ℝ) < (Real.log (X:ℝ))⁻¹ := by positivity
      linarith
    have hre3 : s.re ≤ 3 := by rw [hre]; linarith
    have him1 : 1 ≤ |s.im| := by rw [him]; linarith
    have hlogd := hmod s hre1 hre3 him1
    rw [him] at hlogd
    have harith := norm_slice_add_logDeriv_le hX hY v w hw0
    have htri : ‖logWeightedSlice v X Y w‖
        ≤ ‖logWeightedSlice v X Y w + logDeriv riemannZeta s‖ + ‖logDeriv riemannZeta s‖ := by
      simpa using norm_sub_le (logWeightedSlice v X Y w + logDeriv riemannZeta s)
        (logDeriv riemannZeta s)
    have hCmax : C₀ ≤ max C₀ 1 := le_max_left _ _
    rw [hTinv, hmin]
    have hprod : C₀ * a ≤ max C₀ 1 * a := mul_le_mul_of_nonneg_right hCmax ha0.le
    linarith [hlogd, harith, htri]
  · -- trivial branch
    have hmin : min a (Real.log (X : ℝ)) = Real.log (X : ℝ) := min_eq_right hcase
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

end

end NormalNumbers.ElliottSliceCapModerate
