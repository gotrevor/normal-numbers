/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyLRTail
import NormalNumbers.VandeheyTransport
import NormalNumbers.VandeheyRunClock
import NormalNumbers.VandeheyLRPattern

/-!
# The letter-level occurrence limit for the Raney machine

`VandeheyRunClock.mobiusUniformFreq_of_runClock` leaves exactly one obligation: an
`x`-independent Cesàro limit for the image's CF-occurrence count sampled along the run clock.
This file supplies the **letter-level** half of it — everything that the output-frequency engine
can see — namely: for each parity `b`, the number of occurrences of the pattern word
`patWord b v` in the letter word emitted by the first `n` input digits has an `x`-independent
Cesàro limit.

All six hypotheses of the engine are now available for the concrete machine:
`jointStateFreq_lrDelta`/`subWindow_rhoLR` (lap 6), `lr_trigger_bounds` (the alternation witness
is `patWord_alternation`), `lr_htail` (`VandeheyLRTail`), and `lr_hcof` — which is itself a
corollary of the lower Lemma 2.2, since a machine that emits `≥ (n − 2D − 6)/2` letters on `n`
genuine digits certainly emits unboundedly many.

What is left after this file is the **run dictionary bookkeeping**: converting a count of
pattern occurrences in the letter word into a count of CF occurrences in the image, which is
`VandeheyLRPattern.card_cf_eq_card_patWord` plus `O(1)` end corrections.  Those are the two
disclosed `sorry`s below (`cesaro_of_bounded_diff` is proved; the two bridges are not).
-/

namespace NormalNumbers.VandeheyLR

open Filter Mat2 VandeheyAut VandeheyOut

variable {D : ℕ}

/-! ## A reusable Cesàro-slack lemma -/

/-- **Cesàro limits ignore a bounded difference.**  Used throughout the run-clock bookkeeping,
where every reindexing (the leading `R`-run of the image, the incomplete final run, the
`[1, N)` index offset of the run dictionary) costs a constant. -/
theorem cesaro_of_bounded_diff {F G : ℕ → ℝ} {C L : ℝ}
    (hdiff : ∀ n, |F n - G n| ≤ C)
    (hG : Tendsto (fun n => G n / n) atTop (nhds L)) :
    Tendsto (fun n => F n / n) atTop (nhds L) := by
  have hzero : Tendsto (fun n : ℕ => F n / n - G n / n) atTop (nhds 0) := by
    have hconst : Tendsto (fun n : ℕ => |C| / n) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat |C|
    refine squeeze_zero_norm' ?_ hconst
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_sub_div_same, Real.norm_eq_abs, abs_div, abs_of_pos hnr]
    refine div_le_div_of_nonneg_right ?_ hnr.le
    exact (hdiff n).trans (le_abs_self C)
  have := hG.add hzero
  rw [add_zero] at this
  refine this.congr ?_
  intro n
  ring

/-! ## The start state, as a determinant-`+D` Raney state -/

/-- The start state `diag(D,1)` has determinant exactly `+D`, so it lives in `RPlus D` — which is
what the joint-frequency input (`jointStateFreq_lrDelta`) is stated for. -/
def startPlus (hD : 0 < D) : RPlus D :=
  ⟨⟨(D : ℤ), 0, 0, 1⟩, isRD_diag hD, by simp [det]⟩

@[simp] lemma startPlus_toRState (hD : 0 < D) :
    (startPlus hD).toRState = startState hD := rfl

/-! ## `hcof` from the lower Lemma 2.2 -/

/-- **The letter output is unbounded.**  A corollary of `genuine_length_le`: `n` genuine input
digits force at least `(n − 2D − 6)/2` output letters. -/
theorem lr_hcof (hD : 0 < D) {y : ℝ} (hirr : Irrational y) (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) : ∃ n, j < outLen (lrDelta hD) (lrOutN hD) (startState hD) y n := by
  classical
  refine ⟨2 * j + 2 * D + 8, ?_⟩
  set n : ℕ := 2 * j + 2 * D + 8 with hn
  have hgen : ∀ e ∈ cfWord y n, 1 ≤ e := by
    intro e he
    obtain ⟨i, -, hi⟩ : ∃ i < n, cfDigit y i = e := by simpa [cfWord] using he
    exact hi ▸ one_le_cfDigit y hirr hy i
  have hgrow := genuine_length_le hD (startState hD) (cfWord y n) hgen
  rw [← length_blocksOf_eq hD (startState hD) (cfWord y n)] at hgrow
  have hlen : (cfWord y n).length = n := by simp [cfWord]
  have hout : outLen (lrDelta hD) (lrOutN hD) (startState hD) y n
      = (blocksOf (lrDelta hD) (lrOutN hD) (startState hD) (cfWord y n)).length := by
    rw [outLen, outWord_eq_blocksOf]
  rw [hlen] at hgrow
  omega

/-! ## The pattern word in the engine's alphabet -/

/-- The pattern word, encoded into the output alphabet `ℕ` of the engine. -/
def patN (b : Bool) (v : List ℕ) : List ℕ := (patWord b v).map encLetter

lemma patN_length (b : Bool) (v : List ℕ) : (patN b v).length = v.sum + 2 := by
  rw [patN, List.length_map, patWord_length]

/-- The encoded pattern alternates at index `0` — the trigger bound's hypothesis. -/
lemma patN_alternation (b : Bool) (a : ℕ) (v : List ℕ) (ha : 1 ≤ a) :
    (patN b (a :: v))[0]? ≠ (patN b (a :: v))[1]? := by
  intro hcon
  refine patWord_alternation b a v ha ?_
  have h0 : (patN b (a :: v))[0]? = (patWord b (a :: v))[0]?.map encLetter := by
    rw [patN, List.getElem?_map]
  have h1 : (patN b (a :: v))[1]? = (patWord b (a :: v))[1]?.map encLetter := by
    rw [patN, List.getElem?_map]
  rw [h0, h1] at hcon
  exact Option.map_injective encLetter_injective hcon

/-! ## The letter-level Cesàro limit -/

/-- **The letter-level occurrence limit.**  For every genuine CF word `v` and every parity `b`,
the number of occurrences of the pattern `patWord b v` in the letter word emitted by the first
`n` input digits has a Cesàro limit that does not depend on the CF-normal input.

This is the whole output-frequency engine applied to the concrete machine: nothing about the
image's continued fraction enters yet. -/
theorem exists_tendsto_countOccurrences_patN (D : ℕ) [Fact (Nat.Prime D)] (hD : 0 < D)
    (a : ℕ) (v : List ℕ) (ha : 1 ≤ a) (b : Bool) :
    ∃ L : ℝ, ∀ y : ℝ, IsCFNormal y → y ∈ Set.Ioo (0 : ℝ) 1 →
      Tendsto (fun n => (countOccurrences (patN b (a :: v))
        (outWord (lrDelta hD) (lrOutN hD) (startState hD) y n) : ℝ) / n) atTop (nhds L) := by
  classical
  set V : List ℕ := patN b (a :: v) with hV
  have hVlen : 1 + 1 < V.length := by
    rw [hV, patN_length]
    have : 1 ≤ (a :: v).sum := by
      simp only [List.sum_cons]
      omega
    omega
  have halt : V[0]? ≠ V[0 + 1]? := by
    simpa using patN_alternation b a v ha
  obtain ⟨hkK, hK⟩ := lr_trigger_bounds hD V 0 (by omega) halt
  obtain ⟨L, hL⟩ := exists_tendsto_trigTotal (k := kOut (lrDelta hD) (lrOutN hD) V)
    (K := 2 * D + 2 + V.length) (lrDelta hD) (startState hD)
    (by simpa using jointStateFreq_lrDelta D hD (startPlus hD))
    (by simpa using subWindow_rhoLR D hD (startPlus hD))
    (fun q t => hkK q t) (fun t y J => hK t y J) (lr_htail hD V)
  refine ⟨L, fun y hy hy01 => ?_⟩
  have hirr : Irrational y := by
    by_contra h
    exact Literature.not_isCFNormal_of_not_irrational h hy
  have hcof := lr_hcof hD hirr hy01
  have hdig : ∀ m, 1 ≤ cfDigit y m := fun m => one_le_cfDigit y hirr hy01 m
  have hVne : V ≠ [] := by
    intro h
    rw [h] at hVlen
    simp at hVlen
  refine tendsto_countOccurrences_outWord_of_fireOut y hcof hVne ?_
  refine (hL y hy hdig).congr ?_
  intro n
  rw [trigTotal, Nat.cast_sum]
  refine congrArg (· / (n : ℝ)) ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fireTotal_kOut_eq_fireOut (lrDelta hD) (lrOutN hD) (startState hD) y hcof V i]

end NormalNumbers.VandeheyLR

section
open NormalNumbers.VandeheyLR
#print axioms cesaro_of_bounded_diff
#print axioms lr_hcof
#print axioms patN_alternation
#print axioms exists_tendsto_countOccurrences_patN
end
