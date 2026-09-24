import NormalNumbers.Walsh

/-!
# Abelian normality in base two: the symmetrized Walsh dual

Campbell (arXiv:2603.04396, `papers/campbell-2026-abelian-normal.md`) calls a digit sequence
*abelian-normal* when subwords are counted up to permutation: in base two, the number of ones in
a sliding window of length `L` must have the Binomial(`L`, 1/2) law.  Every normal sequence is
abelian-normal.

`Walsh.isNormalSequence_two_iff_parityMean` says binary normality is the vanishing of every
parity correlation `parityMean s S`.  The headline here says abelian normality is the vanishing of
their **symmetrized** sums `∑_{S ⊆ range L, |S| = j} parityMean s S`: the characters averaged over
permutations of window positions.  Proof shape (finite linear algebra, no inversion needed):
`∑_{|S| = j} parityChar s S n` is the Krawtchouk polynomial `K_j` of `onesCount s L n`, and
`∑_w K_j(w) · choose L w = 0` for `j ≥ 1`; conversely the indicator of `onesCount = w` expands in
`blockSign` exactly as in `Walsh.lean`, and summing over the `choose L w` words with `w` ones
collapses the `S`-coefficient to a function of `|S|`.

Finite-level companions (word frequencies at a fixed length, `ℚ`-valued):
* `rigid_three`: at length 3, stationarity plus abelian balance at lengths ≤ 3 forces uniform.
* `separation_four`: at length 4 there is a nonnegative stationary word measure, abelian-balanced
  at every length ≤ 4, that is not uniform.  (Probe 2026-09-23: the solution space has dimension
  1 at L = 4, 5 at L = 5, 16 at L = 6, 42 at L = 7.)
-/

open Finset Filter Topology

namespace NormalNumbers.Abelian

open NormalNumbers.Walsh

/-- Number of ones in the length-`L` window of `s` starting at `n`. -/
def onesCount (s : ℕ → ℕ) (L n : ℕ) : ℕ := (windowSet s L n).card

/-- Frequency, among the first `N` positions, of windows of length `L` holding exactly `j` ones. -/
noncomputable def onesFreq (s : ℕ → ℕ) (L j N : ℕ) : ℝ :=
  (((range N).filter (fun n => onesCount s L n = j)).card : ℝ) / N

/-- Base-two abelian normality: window one-counts are asymptotically Binomial(`L`, 1/2). -/
def IsAbelianNormalTwo (s : ℕ → ℕ) : Prop :=
  ∀ L j : ℕ, j ≤ L → Tendsto (onesFreq s L j) atTop (𝓝 ((L.choose j : ℝ) / 2 ^ L))

/-- The symmetrized parity correlation: all `j`-subsets of a length-`L` window. -/
noncomputable def symParityMean (s : ℕ → ℕ) (L j N : ℕ) : ℝ :=
  ∑ S ∈ (range L).powersetCard j, parityMean s S N

/-- **Headline.**  Abelian normality in base two is the vanishing of the symmetrized parity
correlations. -/
theorem isAbelianNormalTwo_iff_symParityMean (s : ℕ → ℕ) (hs : ∀ m, s m < 2) :
    IsAbelianNormalTwo s ↔
      ∀ L j : ℕ, 1 ≤ j → j ≤ L → Tendsto (symParityMean s L j) atTop (𝓝 0) := by
  sorry

/-- Normal implies abelian-normal (corollary of the headline and the Walsh criterion). -/
theorem isAbelianNormalTwo_of_isNormalSequence (s : ℕ → ℕ) (hs : ∀ m, s m < 2)
    (h : IsNormalSequence 2 s) : IsAbelianNormalTwo s := by
  sorry

/-! ## Finite level: word frequencies at a fixed length -/

/-- Frequencies of binary words of length `L`. -/
abbrev WordFreq (L : ℕ) := (Fin L → Fin 2) → ℚ

/-- Number of ones among the first `k` letters of `w`. -/
def prefixOnes {L : ℕ} (w : Fin L → Fin 2) (k : ℕ) : ℕ :=
  ((univ : Finset (Fin L)).filter (fun i : Fin L => i.val < k ∧ w i = 1)).card

/-- Shift-invariance: the `(L-1)`-prefix and `(L-1)`-suffix marginals agree. -/
def Stationary {L : ℕ} (p : WordFreq (L + 1)) : Prop :=
  ∀ u : Fin L → Fin 2,
    ∑ a : Fin 2, p (Fin.snoc u a) = ∑ a : Fin 2, p (Fin.cons a u)

/-- Abelian balance at every prefix length `k ≤ L`. -/
def AbelianUpTo {L : ℕ} (p : WordFreq L) : Prop :=
  ∀ k j : ℕ, k ≤ L → j ≤ k →
    ∑ w ∈ univ.filter (fun w : Fin L → Fin 2 => prefixOnes w k = j), p w =
      (k.choose j : ℚ) / 2 ^ k

/-- At length 3, stationarity and abelian balance force the uniform word measure. -/
theorem rigid_three (p : WordFreq 3) (hst : Stationary p) (hab : AbelianUpTo p) :
    p = fun _ => (1 : ℚ) / 8 := by
  sorry

/-- At length 4, abelian balance does not force uniformity. -/
theorem separation_four :
    ∃ p : WordFreq 4, (∀ w, 0 ≤ p w) ∧ Stationary p ∧ AbelianUpTo p ∧
      p ≠ fun _ => (1 : ℚ) / 16 := by
  sorry

end NormalNumbers.Abelian
