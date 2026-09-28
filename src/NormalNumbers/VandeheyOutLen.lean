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

open Filter VandeheyAut

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

end NormalNumbers.VandeheyOut

section
open NormalNumbers.VandeheyOut
#print axioms outLen_eq_sum_wCount
#print axioms tendsto_outLen_div
end
