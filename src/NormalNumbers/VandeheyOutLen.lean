/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyOutputFreq
import NormalNumbers.VandeheyOutputWord

/-!
# `hlen` is a corollary of `hjs`: the output length is a Birkhoff sum

Vandehey's Lemma 6.1 (`ℓ(n) = c·n(1 + o(1))`) is not an analytic leaf.  The output length

    `outLen δ out s₀ x n = Σ_{i<n} |out (stateAt δ s₀ x i) (cfDigit x i)|`

is literally a state-restricted weighted count at window length `1`, i.e.

    `outLen δ out s₀ x n = Σ_{t : S} wCount δ s₀ t (fun w => |out t w.headI|) 1 x n`,

so the single-length engine `VandeheyOut.tendsto_wCount_div` — which runs on `hjs` and `hρ`
alone — gives the Cesàro limit directly, with the `x`-independent value

    `c = Σ_{t} wLimit ρ t (fun w => |out t w.headI|) 1`.

The only extra hypothesis is that each block has bounded length (`hB`), which is the trigger
bound the concrete `L/R` machine already satisfies.  Positivity of `c` is a separate, purely
combinatorial matter and is *not* needed for the limit itself.
-/

namespace NormalNumbers.VandeheyOut

open Filter VandeheyAut VandeheyRenewal

variable {S : Type*} [DecidableEq S] [Fintype S]

variable (δ : S → ℕ → S) (out : S → ℕ → List ℕ) (s₀ : S)

/-- The per-state block-length weight, as a length-`1` window function. -/
noncomputable def blockLen (out : S → ℕ → List ℕ) (t : S) (w : List ℕ) : ℝ :=
  ((out t w.headI).length : ℝ)

lemma blockLen_nonneg (t : S) (w : List ℕ) : 0 ≤ blockLen out t w := by
  unfold blockLen; positivity

lemma blockLen_le {B : ℕ} (hB : ∀ t j, (out t j).length ≤ B) (t : S) (w : List ℕ) :
    blockLen out t w ≤ (B : ℝ) := by
  unfold blockLen
  exact_mod_cast hB t w.headI

/-- The output length is the sum of the block lengths. -/
lemma outLen_eq_sum (x : ℝ) (n : ℕ) :
    outLen δ out s₀ x n = ∑ i ∈ Finset.range n, (outBlock δ out s₀ x i).length := by
  induction n with
  | zero => simp [outLen, outWord]
  | succ n ih =>
    rw [outLen, outWord_succ, List.length_append, ← outLen, ih, Finset.sum_range_succ]

/-- **The output length is a Birkhoff sum of a bounded window/state function.** -/
lemma outLen_eq_sum_wCount (x : ℝ) (n : ℕ) :
    (outLen δ out s₀ x n : ℝ)
      = ∑ t : S, wCount δ s₀ t (blockLen out t) 1 x n := by
  rw [outLen_eq_sum]
  push_cast
  simp only [wCount, blockLen, cfWindow_one, List.headI]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [outBlock]

/-- **`hlen` from `hjs`** (Vandehey Lemma 6.1).  For a transducer whose blocks have bounded
length, the output length has an `x`-independent Cesàro limit along every CF-normal orbit —
with no ergodic theory beyond what `JointStateFreq` already carries. -/
theorem tendsto_outLen_div {ρ : List ℕ → S → ℝ} (hjs : JointStateFreq δ s₀ ρ)
    (hρ : SubWindow ρ) {B : ℕ} (hB : ∀ t j, (out t j).length ≤ B) {x : ℝ} (hx : IsCFNormal x) :
    Tendsto (fun n => (outLen δ out s₀ x n : ℝ) / n) atTop
      (nhds (∑ t : S, wLimit ρ t (blockLen out t) 1)) := by
  have hsum : ∀ n : ℕ, (outLen δ out s₀ x n : ℝ) / n
      = ∑ t : S, wCount δ s₀ t (blockLen out t) 1 x n / n := by
    intro n
    rw [outLen_eq_sum_wCount, Finset.sum_div]
  refine Tendsto.congr (fun n => (hsum n).symm) ?_
  refine tendsto_finsetSum _ fun t _ => ?_
  exact tendsto_wCount_div δ s₀ hjs t hρ (C := (B : ℝ)) one_pos
    (blockLen_nonneg out t) (blockLen_le out hB t) hx

/-- The limit is nonnegative; the concrete machine supplies strict positivity separately. -/
lemma outLenLimit_nonneg {ρ : List ℕ → S → ℝ} (hρ : SubWindow ρ) {B : ℕ}
    (hB : ∀ t j, (out t j).length ≤ B) :
    0 ≤ ∑ t : S, wLimit ρ t (blockLen out t) 1 :=
  Finset.sum_nonneg fun t _ =>
    wLimit_nonneg (C := (B : ℝ)) hρ (blockLen_nonneg out t) (blockLen_le out hB t)

/-! ## `hc`: strict positivity of the output rate -/

/-- The joint counts over all states partition the window count. -/
lemma sum_jointCount_eq_winCard (x : ℝ) (q : List ℕ) (n : ℕ) :
    ∑ t : S, jointCount δ s₀ t q x n = winCard q x n := by
  classical
  rw [winCard, Finset.card_eq_sum_card_fiberwise
    (f := fun i => stateAt δ s₀ x i) (t := (Finset.univ : Finset S)) (fun i _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [jointCount, jointSet]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  tauto

/-- **The joint law splits the window law**: summing over the (finite) state set recovers the
Gauss mass of the window. -/
lemma sum_rho_eq_gauss {ρ : List ℕ → S → ℝ} (hjs : JointStateFreq δ s₀ ρ) {q : List ℕ}
    (hq : q ≠ []) (hqpos : ∀ a ∈ q, 1 ≤ a) :
    ∑ t : S, ρ q t = (gaussMeasure (cfCylinder q)).toReal := by
  obtain ⟨x, hx⟩ := exists_isCFNormal
  have h1 : Tendsto (fun n => ∑ t : S, (jointCount δ s₀ t q x n : ℝ) / n) atTop
      (nhds (∑ t : S, ρ q t)) :=
    tendsto_finsetSum _ fun t _ => hjs t q hq hqpos x hx
  have h2 : Tendsto (fun n => (winCard q x n : ℝ) / n) atTop
      (nhds (gaussMeasure (cfCylinder q)).toReal) := by
    simpa [winCard] using tendsto_windowFreq hx q hq hqpos
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  rw [← Finset.sum_div]
  congr 1
  exact_mod_cast (sum_jointCount_eq_winCard δ s₀ x q n).symm

omit [DecidableEq S] in
/-- A single word bounds the `x`-independent limit from below (`Q = {w}`). -/
lemma le_wLimit_single {ρ : List ℕ → S → ℝ} {t : S} {a : List ℕ → ℝ} {C : ℝ} {m : ℕ}
    (hρ : SubWindow ρ) (ha0 : ∀ w, 0 ≤ a w) (haC : ∀ w, a w ≤ C) {w : List ℕ}
    (hw : w ∈ allWords m) : a w * ρ w t ≤ wLimit ρ t a m :=
  le_csSup (wLimit_set_bddAbove (C := C) hρ haC ha0) ⟨{w}, by simpa using hw, by simp⟩

/-- **`hc` for any transducer that never stalls on some digit.**  If one genuine digit `j`
makes *every* state emit a nonempty block, then the output rate is at least the Gauss mass of
the cylinder `I_[j]`, hence strictly positive. -/
theorem outLenLimit_pos {ρ : List ℕ → S → ℝ} (hjs : JointStateFreq δ s₀ ρ) (hρ : SubWindow ρ)
    {B : ℕ} (hB : ∀ t j, (out t j).length ≤ B) {j : ℕ} (hj : 1 ≤ j)
    (hne : ∀ t : S, out t j ≠ []) :
    0 < ∑ t : S, wLimit ρ t (blockLen out t) 1 := by
  have hqne : ([j] : List ℕ) ≠ [] := by simp
  have hqpos : ∀ a ∈ ([j] : List ℕ), 1 ≤ a := by
    intro a ha; simp only [List.mem_singleton] at ha; omega
  have hmem : ([j] : List ℕ) ∈ allWords 1 := ⟨rfl, hqpos⟩
  have hstep : ∀ t : S, ρ [j] t ≤ wLimit ρ t (blockLen out t) 1 := by
    intro t
    have h1 : blockLen out t [j] * ρ [j] t ≤ wLimit ρ t (blockLen out t) 1 :=
      le_wLimit_single (C := (B : ℝ)) hρ (blockLen_nonneg out t) (blockLen_le out hB t) hmem
    have h2 : (1 : ℝ) ≤ blockLen out t [j] := by
      have : 1 ≤ (out t j).length := List.length_pos_iff.mpr (hne t)
      simpa [blockLen] using (by exact_mod_cast this : (1 : ℝ) ≤ ((out t j).length : ℝ))
    refine le_trans ?_ h1
    exact le_mul_of_one_le_left (hρ [j] t).1 h2
  have hsum : ∑ t : S, ρ [j] t = (gaussMeasure (cfCylinder [j])).toReal :=
    sum_rho_eq_gauss δ s₀ hjs hqne hqpos
  have hpos : 0 < (gaussMeasure (cfCylinder [j])).toReal :=
    gaussMeasure_cfCylinder_toReal_pos _ hqne hqpos
  calc (0 : ℝ) < ∑ t : S, ρ [j] t := by rw [hsum]; exact hpos
    _ ≤ ∑ t : S, wLimit ρ t (blockLen out t) 1 := Finset.sum_le_sum fun t _ => hstep t

end NormalNumbers.VandeheyOut

section
open NormalNumbers.VandeheyOut
#print axioms outLen_eq_sum_wCount
#print axioms tendsto_outLen_div
#print axioms sum_rho_eq_gauss
#print axioms outLenLimit_pos
end
