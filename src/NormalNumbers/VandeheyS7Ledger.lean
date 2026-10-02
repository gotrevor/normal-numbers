/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-LG: the height ledger, and why big output digits are RARE

S7-HT identified the width floor as a *height* question: `width ≍ |det Φ| / d²`, so
`width ≥ η` is `d ≤ R`, and the height moves by an explicit factor at each half-step —
a read multiplies `d` by `denRatio + a − 1 ≤ a + 5`, an emission multiplies it by
`mob 0 ≤ 1/b`.  This module *telescopes* that ledger and reads off its first real consequence.

The identity to hold in mind is

    d_n  =  d_2 · ∏_{k<n} (r_{k+2} + a_{k+2} − 1) · ∏_{emissions} mob 0 ,

and the unconditional lower bound `d_n ≥ √(|det Φ|/6)` (`d_runState_ge`, "the output can never
get ahead of the input") turns it into a **one-sided ledger inequality**:

    ∏_{k<n} b_k  ≤  (d_2 / √(|det Φ|/6)) · ∏_{k<n} (a_{k+2} + 5)          `prod_emitFac_le`

i.e. **the emitted log-digit mass never exceeds the read log-digit mass, plus a constant.**
Taking logs and Chebyshev:

    #{k < n : the digit emitted at step k+2 is ≥ T}  ·  log T
        ≤  C(Φ, x)  +  Σ_{k<n} log (a_{k+2} + 5)                          `card_bigEmit_le`

So along ANY run, a large output digit costs log-mass that must have been paid in by the input.
For an input `x` whose log-digit averages are bounded — which is what CF-normality of `x` buys —
the frequency of steps emitting a digit `≥ T` is `O(1 / log T)`, hence `→ 0` as `T → ∞`.

This is the burst side of the width-frequency question left open by S7-HT.  It is unconditional:
no hypothesis on `Φ` beyond `det Φ ≠ 0`, none on `x`, none on normality.
-/
import NormalNumbers.VandeheyS7Height

namespace NormalNumbers.VandeheyS7

open Set Finset NormalNumbers

namespace MapState

/-! ## The emitted factor of one step -/

/-- The digit emitted at step `n` of the run, as a real number `≥ 1` (`1` if nothing is emitted). -/
noncomputable def emitFac (Φ : MapState) (x : ℝ) (n : ℕ) : ℝ :=
  max 1 (((runWord Φ x n).headI : ℕ) : ℝ)

lemma one_le_emitFac (Φ : MapState) (x : ℝ) (n : ℕ) : 1 ≤ emitFac Φ x n := le_max_left _ _

lemma emitFac_pos (Φ : MapState) (x : ℝ) (n : ℕ) : 0 < emitFac Φ x n :=
  lt_of_lt_of_le zero_lt_one (one_le_emitFac Φ x n)

/-- If a digit `b` is emitted at step `n`, then `emitFac = b`. -/
lemma emitFac_eq_of_emit {Φ : MapState} {x : ℝ} {n b : ℕ} (hb : 1 ≤ b)
    (hw : runWord Φ x n = [b]) : emitFac Φ x n = (b : ℝ) := by
  have hb1 : (1:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
  rw [emitFac, hw]
  simp only [List.headI]
  exact max_eq_right hb1

/-- **One step of the ledger.**  The emitted digit is paid for out of the height. -/
theorem d_succ_mul_emitFac_le (Φ : MapState) (x : ℝ) (n : ℕ) :
    (runState Φ x (n + 1)).d * emitFac Φ x n
      ≤ ((runState Φ x n).comp (readAt x n)).d := by
  set t := (runState Φ x n).comp (readAt x n) with ht
  by_cases h : Emittable t
  · obtain ⟨b, hemit, hword⟩ := step_emitStep h
    have hb : 1 ≤ b := hemit.1
    have hb1 : (1:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
    have hrw : runWord Φ x n = [b] := hword
    have hst : runState Φ x (n + 1) = (step t).1 := rfl
    have hdu : ((step t).1).d = t.mob 0 * t.d := d_emit hemit
    have hmob : t.mob 0 ≤ 1 / (b:ℝ) := (emit_mob_zero_mem hemit).2
    rw [emitFac_eq_of_emit hb hrw, hst, hdu]
    have htd : 0 < t.d := t.hd
    calc t.mob 0 * t.d * (b:ℝ) ≤ (1 / (b:ℝ)) * t.d * (b:ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact mul_le_mul_of_nonneg_right hmob htd.le
      _ = t.d := by field_simp
  · have hrw : runWord Φ x n = [] := by
      show (step t).2 = []
      rw [step_of_not_emittable h]
    have hst : runState Φ x (n + 1) = t := by
      show (step t).1 = t
      rw [step_of_not_emittable h]
    rw [hst, emitFac, hrw]
    simp

/-! ## The read half -/

/-- **One read costs at most `a + 5`.**  Uses the denominator band from step 2 on. -/
theorem d_comp_read_le (Φ : MapState) (x : ℝ) (n : ℕ) :
    ((runState Φ x (n + 2)).comp (readAt x (n + 2))).d
      ≤ (runState Φ x (n + 2)).d * (((inDigit x (n + 2) : ℕ) : ℝ) + 5) := by
  have hband : (runState Φ x (n + 2)).denRatio ≤ 6 := denRatio_runState_le_six Φ x n
  have heq := d_comp_readMap (runState Φ x (n + 2)) (one_le_inDigit_real x (n + 2))
  rw [readAt, heq]
  have hd : 0 < (runState Φ x (n + 2)).d := (runState Φ x (n + 2)).hd
  apply mul_le_mul_of_nonneg_left _ hd.le
  linarith

/-! ## The telescoped ledger -/

/-- **The ledger, telescoped.**  Everything the run has emitted since step 2 is paid for by what
it has read since step 2. -/
theorem d_mul_prod_emitFac_le (Φ : MapState) (x : ℝ) (n : ℕ) :
    (runState Φ x (n + 2)).d * ∏ k ∈ range n, emitFac Φ x (k + 2)
      ≤ (runState Φ x 2).d * ∏ k ∈ range n, (((inDigit x (k + 2) : ℕ) : ℝ) + 5) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := d_succ_mul_emitFac_le Φ x (n + 2)
    have hread := d_comp_read_le Φ x n
    have hchain : (runState Φ x (n + 3)).d * emitFac Φ x (n + 2)
        ≤ (runState Φ x (n + 2)).d * (((inDigit x (n + 2) : ℕ) : ℝ) + 5) := by
      have : (n + 2) + 1 = n + 3 := by ring
      rw [this] at hstep
      linarith
    have hPpos : (0:ℝ) < ∏ k ∈ range n, emitFac Φ x (k + 2) :=
      Finset.prod_pos (fun k _ => emitFac_pos Φ x (k + 2))
    have hApos : (0:ℝ) < (((inDigit x (n + 2) : ℕ) : ℝ) + 5) := by
      have := one_le_inDigit_real x (n + 2); linarith
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have hleft : (runState Φ x (n + 1 + 2)).d *
        ((∏ k ∈ range n, emitFac Φ x (k + 2)) * emitFac Φ x (n + 2))
        = ((runState Φ x (n + 3)).d * emitFac Φ x (n + 2))
            * (∏ k ∈ range n, emitFac Φ x (k + 2)) := by
      have h3 : n + 1 + 2 = n + 3 := by ring
      rw [h3]; ring
    rw [hleft]
    calc ((runState Φ x (n + 3)).d * emitFac Φ x (n + 2))
            * (∏ k ∈ range n, emitFac Φ x (k + 2))
        ≤ ((runState Φ x (n + 2)).d * (((inDigit x (n + 2) : ℕ) : ℝ) + 5))
            * (∏ k ∈ range n, emitFac Φ x (k + 2)) :=
          mul_le_mul_of_nonneg_right hchain hPpos.le
      _ = ((runState Φ x (n + 2)).d * ∏ k ∈ range n, emitFac Φ x (k + 2))
            * (((inDigit x (n + 2) : ℕ) : ℝ) + 5) := by ring
      _ ≤ ((runState Φ x 2).d * ∏ k ∈ range n, (((inDigit x (k + 2) : ℕ) : ℝ) + 5))
            * (((inDigit x (n + 2) : ℕ) : ℝ) + 5) :=
          mul_le_mul_of_nonneg_right ih hApos.le
      _ = (runState Φ x 2).d *
            ((∏ k ∈ range n, (((inDigit x (k + 2) : ℕ) : ℝ) + 5))
              * (((inDigit x (n + 2) : ℕ) : ℝ) + 5)) := by ring

/-- **The emitted mass is bounded by the read mass.**  The unconditional height floor
`d ≥ √(|det Φ|/6)` removes the state from the ledger entirely. -/
theorem prod_emitFac_le (Φ : MapState) (x : ℝ) (n : ℕ) :
    Real.sqrt (|Φ.det| / 6) * ∏ k ∈ range n, emitFac Φ x (k + 2)
      ≤ (runState Φ x 2).d * ∏ k ∈ range n, (((inDigit x (k + 2) : ℕ) : ℝ) + 5) := by
  have hlow : Real.sqrt (|Φ.det| / 6) ≤ (runState Φ x (n + 2)).d := d_runState_ge Φ x n
  have hPpos : (0:ℝ) < ∏ k ∈ range n, emitFac Φ x (k + 2) :=
    Finset.prod_pos (fun k _ => emitFac_pos Φ x (k + 2))
  refine le_trans ?_ (d_mul_prod_emitFac_le Φ x n)
  exact mul_le_mul_of_nonneg_right hlow hPpos.le

/-! ## Log form, and the rarity of big output digits -/

/-- The constant of the ledger: the state's height at step 2 against the universal floor. -/
noncomputable def ledgerConst (Φ : MapState) (x : ℝ) : ℝ :=
  Real.log ((runState Φ x 2).d) - Real.log (Real.sqrt (|Φ.det| / 6))

/-- **The ledger in log form.** -/
theorem sum_log_emitFac_le (Φ : MapState) (x : ℝ) (n : ℕ) :
    ∑ k ∈ range n, Real.log (emitFac Φ x (k + 2))
      ≤ ledgerConst Φ x + ∑ k ∈ range n, Real.log ((((inDigit x (k + 2) : ℕ) : ℝ) + 5)) := by
  have hdet : (0:ℝ) < |Φ.det| := abs_pos.mpr Φ.hdet
  have hs : (0:ℝ) < Real.sqrt (|Φ.det| / 6) := Real.sqrt_pos.mpr (by positivity)
  have hd2 : (0:ℝ) < (runState Φ x 2).d := (runState Φ x 2).hd
  have hP : (0:ℝ) < ∏ k ∈ range n, emitFac Φ x (k + 2) :=
    Finset.prod_pos (fun k _ => emitFac_pos Φ x (k + 2))
  have hQ : (0:ℝ) < ∏ k ∈ range n, (((inDigit x (k + 2) : ℕ) : ℝ) + 5) := by
    refine Finset.prod_pos (fun k _ => ?_)
    have := one_le_inDigit_real x (k + 2); linarith
  have hmain := prod_emitFac_le Φ x n
  have hlog := Real.log_le_log (by positivity) hmain
  rw [Real.log_mul hs.ne' hP.ne', Real.log_mul hd2.ne' hQ.ne'] at hlog
  rw [Real.log_prod (fun k _ => (emitFac_pos Φ x (k + 2)).ne'),
    Real.log_prod (fun k _ => by
      have := one_le_inDigit_real x (k + 2)
      exact (by linarith : (0:ℝ) < (((inDigit x (k + 2) : ℕ) : ℝ) + 5)).ne')] at hlog
  rw [ledgerConst]
  linarith

/-- **Big output digits are rare.**  The number of steps before `n` emitting a digit `≥ T`
is at most `(ledgerConst + read log-mass) / log T`.  Unconditional. -/
theorem card_bigEmit_le (Φ : MapState) (x : ℝ) (n : ℕ) {T : ℝ} (hT : 1 < T) :
    (((range n).filter (fun k => T ≤ emitFac Φ x (k + 2))).card : ℝ) * Real.log T
      ≤ ledgerConst Φ x + ∑ k ∈ range n, Real.log ((((inDigit x (k + 2) : ℕ) : ℝ) + 5)) := by
  have hlogT : 0 < Real.log T := Real.log_pos hT
  set S := (range n).filter (fun k => T ≤ emitFac Φ x (k + 2)) with hS
  have hsub : S ⊆ range n := Finset.filter_subset _ _
  have h1 : (S.card : ℝ) * Real.log T ≤ ∑ k ∈ S, Real.log (emitFac Φ x (k + 2)) := by
    have hconst : ∑ _k ∈ S, Real.log T = (S.card : ℝ) * Real.log T := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [← hconst]
    refine Finset.sum_le_sum (fun k hk => ?_)
    have hk' : T ≤ emitFac Φ x (k + 2) := by
      have := Finset.mem_filter.mp (hS ▸ hk)
      exact this.2
    exact Real.log_le_log (by linarith) hk'
  have h2 : ∑ k ∈ S, Real.log (emitFac Φ x (k + 2))
      ≤ ∑ k ∈ range n, Real.log (emitFac Φ x (k + 2)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => ?_)
    exact Real.log_nonneg (one_le_emitFac Φ x (k + 2))
  have h3 := sum_log_emitFac_le Φ x n
  linarith

end MapState

section Audit

#print axioms MapState.d_succ_mul_emitFac_le
#print axioms MapState.d_comp_read_le
#print axioms MapState.d_mul_prod_emitFac_le
#print axioms MapState.prod_emitFac_le
#print axioms MapState.sum_log_emitFac_le
#print axioms MapState.card_bigEmit_le

end Audit

end NormalNumbers.VandeheyS7
