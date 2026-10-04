/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.FiniteStateSelection

/-!
# Stretch conjectures for the finite-state / pushdown relabeling lane

Companion to `FiniteStateSelection` (headlines `pulariDPDTQuestion_of_lit`,
`pulariWeakening_of_lit`).  Audit: `docs/FINITE-STATE-AUDIT-2026-10-04.md`.

* Small bases.  The counting core `length_le_four_mul_count_zero` gives zero-frequency `≥ 1/4`,
  which separates from `1/k` only for `k ≥ 5`.  Numerics (the audit's probe, prefixes of
  `w₁w̃₁⋯w_Nw̃_N`) put the true frequency near `1/2` for `k = 3,4,5,7` (0.5030, 0.5020, 0.5027,
  0.5040) — the heuristic is that the coder's stack drifts at rate `(k−2)/k` on `wₙ` and the mirror
  half then cancels `(|wₙ| + |red wₙ|)/2 ≈ (k−1)/k · |wₙ|` letters, giving `(1/k + (k−1)/k)/2 = 1/2`.
  `ZeroFreqHalf` freezes that; `pulariDPDTQuestion_of_zeroFreqHalf` wires it to Q-DPDT for `k ≥ 3`.
* Base 2.  The free product of two copies of `ℤ/2` is the infinite dihedral group: no drift, the
  heuristic gives exactly `1/2 = 1/k`, and the probe's 0.5147 does not separate.  The mechanism has
  no purchase; `PulariDPDTBaseTwo` is an open node.
* Dimension zero.  `PulariDPDTDimZero`: can a DPDT relabeling push `dim^f` of a normal point all
  the way to `0`?  Open node.
* Non-synchronous sibling.  `delayEnum` (emit the previous letter: a two-state finite-state
  transducer, levelwise surjective one level down) has `k ∣ k^n a_n` for every `n ≥ 1`, so its
  scaled sequence is never `k`-adically equidistributed (`not_kAdicEquidist_delayEnum`), while a
  normal point is still `delayEnum`-normal (`isFNormal_delayEnum_of_normal`).  That is why
  `pulariWeakening_of_lit` is stated for SYNCHRONOUS relabelings: with a one-letter delay the
  scaling `k^n` no longer matches the output resolution.
-/

noncomputable section

open Filter Topology

namespace NormalNumbers.FiniteState

variable {k : ℕ}

/-- **Open node (confidence 60%).**  The coder's names of the Carton–Perifel sequence have
zero-frequency exactly `1/2`.  Evidence: the probe in the audit doc (four bases, control: the
same coder on the non-mirrored lexicographic concatenation gives 0.1765 at `k = 5`, so the `1/2`
is produced by the mirror halves, not by the coder alone). -/
def ZeroFreqHalf (k : ℕ) [NeZero k] : Prop :=
  Tendsto (fun n : ℕ => ((pre (encSeq (cpSeq k)) n).count 0 : ℝ) / n) atTop (𝓝 (1 / 2))

/-- **Leaf (95%).**  Zero-frequency `1/2 ≠ 1/k` (for `k ≥ 3`) rules out normality. -/
theorem not_isNormal_of_zeroFreqHalf [NeZero k] (hk : 3 ≤ k) (h : ZeroFreqHalf k) :
    ¬ IsNormalSequence k fun i => (encSeq (cpSeq k) i : ℕ) := by
  sorry

/-- Wiring: `ZeroFreqHalf` answers Pulari's Q-DPDT in every base `k ≥ 3`. -/
theorem pulariDPDTQuestion_of_zeroFreqHalf [NeZero k] (hk : 3 ≤ k) (h : ZeroFreqHalf k)
    (hFS : Literature.fsDim_one_isNormal) :
    PulariDPDTQuestion k := by
  obtain ⟨hse, hx, hint, hkad, hdim⟩ :=
    mirrorEnum_cpReal_facts_of_not_normal (by omega) (not_isNormal_of_zeroFreqHalf hk h)
      (isNormal_cpSeq (by omega)) hFS
  exact ⟨mirrorEnum k, hse, isDPDTEnum_mirror, cpReal k, hx, hint, hkad, hdim⟩

/-- **Open node.**  Pulari's Q-DPDT in base 2, where the free-reduction mechanism does not
separate (no drift on the infinite dihedral group). -/
def PulariDPDTBaseTwo : Prop := PulariDPDTQuestion 2

/-- **Open node (confidence 40% for "yes").**  A DPDT separator enumerator and a point whose
scaled best-from-below sequence is `k`-adically equidistributed with `dim^f_FS(x) = 0`. -/
def PulariDPDTDimZero (k : ℕ) : Prop :=
  ∃ f : List (Fin k) → ℝ, IsSepEnum f ∧ IsDPDTEnum f ∧ ∃ x ∈ Set.Ico (0 : ℝ) 1,
    (∀ n, ((scaled f x n : ℤ) : ℝ) = (k : ℝ) ^ n * bestBelow f x n) ∧
      KAdicEquidist k (scaled f x) ∧ fDim f x = 0

/-! ## The non-synchronous sibling -/

/-- One-letter-delay relabeling `f(w) = grid(w without its last letter)`: computed by a two-state
FST that emits the previously read letter; image = all grid points (one level down). -/
def delayEnum (k : ℕ) (w : List (Fin k)) : ℝ := grid k w.dropLast

/-- **Leaf (90%).**  For the delay relabeling, `k^n a_n^f(x) = k ⌊k^{n-1} x⌋` for `n ≥ 1`, so it
is divisible by `k`. -/
theorem k_dvd_scaled_delayEnum (hk : 2 ≤ k) (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) (n : ℕ)
    (hn : 1 ≤ n) : (k : ℤ) ∣ scaled (delayEnum k) x n := by
  sorry

/-- **Leaf (92%).**  Hence the delay relabeling's scaled sequence is never `k`-adically
equidistributed (residue `1` mod `k` is never hit for `n ≥ 1`). -/
theorem not_kAdicEquidist_delayEnum (hk : 2 ≤ k) (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    ¬ KAdicEquidist k (scaled (delayEnum k) x) := by
  sorry

/-- **Leaf (80%).**  A normal point is `delayEnum`-normal: the delay costs one letter per name, so
`K^{T,f}_δ(x)` and the standard approximation complexity differ by `O(1)` after composing with the
delay transducer and its finite-state right inverse (append any letter). -/
theorem isFNormal_delayEnum_of_normal (hk : 2 ≤ k) (S : ℕ → Fin k)
    (hn : IsNormalSequence k fun i => (S i : ℕ)) :
    IsFNormal (delayEnum k) (realOfDigits k fun i => (S i : ℕ)) := by
  sorry

end NormalNumbers.FiniteState
