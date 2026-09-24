import NormalNumbers.AbelianKrawtchouk

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


theorem onesCount_le (s : ℕ → ℕ) (L n : ℕ) : onesCount s L n ≤ L := by
  simpa [onesCount] using Finset.card_le_card (windowSet_subset s L n)

/-- **Pointwise.**  The symmetrized character sum is a Krawtchouk coefficient of the
window weight. -/
theorem sum_parityChar_powersetCard (s : ℕ → ℕ) (hs : ∀ m, s m < 2) (L j n : ℕ) :
    ∑ S ∈ (range L).powersetCard j, parityChar s S n = kraw L j (onesCount s L n) := by
  have h : ∀ S ∈ (range L).powersetCard j,
      parityChar s S n = (-1 : ℝ) ^ (S ∩ windowSet s L n).card := by
    intro S hS
    exact parityChar_eq_pow s hs (Finset.mem_powersetCard.mp hS).1 n
  rw [Finset.sum_congr rfl h, onesCount]
  exact sum_powersetCard_neg_one_pow L j (windowSet_subset s L n)

/-- The raw (undivided) symmetrized character sum. -/
noncomputable def symCharSum (s : ℕ → ℕ) (L j N : ℕ) : ℝ :=
  ∑ n ∈ range N, ∑ S ∈ (range L).powersetCard j, parityChar s S n

theorem symParityMean_eq_div (s : ℕ → ℕ) (L j N : ℕ) :
    symParityMean s L j N = symCharSum s L j N / N := by
  rw [symParityMean, symCharSum, Finset.sum_comm, Finset.sum_div]
  exact Finset.sum_congr rfl (fun S _ => rfl)

theorem symCharSum_eq (s : ℕ → ℕ) (hs : ∀ m, s m < 2) (L j N : ℕ) :
    symCharSum s L j N
      = ∑ w ∈ range (L + 1), kraw L j w *
          (((range N).filter (fun n => onesCount s L n = w)).card : ℝ) := by
  rw [symCharSum, Finset.sum_congr rfl (fun n _ => sum_parityChar_powersetCard s hs L j n)]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun n => onesCount s L n)
    (t := range (L + 1)) (fun n _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (onesCount_le s L n)))]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.sum_congr rfl (fun n hn => by rw [(Finset.mem_filter.mp hn).2]),
    Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **The forward transform.**  The symmetrized parity correlation is a Krawtchouk combination
of the window-weight frequencies. -/
theorem symParityMean_eq (s : ℕ → ℕ) (hs : ∀ m, s m < 2) (L j N : ℕ) :
    symParityMean s L j N = ∑ w ∈ range (L + 1), kraw L j w * onesFreq s L w N := by
  rw [symParityMean_eq_div, symCharSum_eq s hs, Finset.sum_div]
  exact Finset.sum_congr rfl (fun w _ => by rw [onesFreq, mul_div_assoc])

/-- **The inverse transform.**  The window-weight frequency is a Krawtchouk combination of the
symmetrized parity correlations. -/
theorem onesFreq_eq (s : ℕ → ℕ) (hs : ∀ m, s m < 2) (L w N : ℕ) :
    (2 : ℝ) ^ L * onesFreq s L w N
      = ∑ j ∈ range (L + 1), kraw L w j * symParityMean s L j N := by
  have key : ∑ j ∈ range (L + 1), kraw L w j * symCharSum s L j N
      = (2 : ℝ) ^ L * (((range N).filter (fun n => onesCount s L n = w)).card : ℝ) := by
    have h1 : ∀ j ∈ range (L + 1), kraw L w j * symCharSum s L j N
        = ∑ n ∈ range N, kraw L w j * ∑ S ∈ (range L).powersetCard j, parityChar s S n := by
      intro j _; rw [symCharSum, Finset.mul_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    have h2 : ∀ n ∈ range N,
        ∑ j ∈ range (L + 1), kraw L w j * ∑ S ∈ (range L).powersetCard j, parityChar s S n
          = if onesCount s L n = w then (2 : ℝ) ^ L else 0 := by
      intro n _
      have hstep : ∀ j ∈ range (L + 1),
          kraw L w j * ∑ S ∈ (range L).powersetCard j, parityChar s S n
            = kraw L w j *
              ∑ S ∈ (range L).powersetCard j, (-1 : ℝ) ^ (S ∩ windowSet s L n).card := by
        intro j _
        congr 1
        refine Finset.sum_congr rfl (fun S hS => ?_)
        exact parityChar_eq_pow s hs (Finset.mem_powersetCard.mp hS).1 n
      rw [Finset.sum_congr rfl hstep]
      simp only [onesCount]
      exact sum_kraw_mul_sum L w (windowSet_subset s L n)
    rw [Finset.sum_congr rfl h2, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
      add_zero, nsmul_eq_mul, mul_comm]
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ range (L + 1)) => by
    rw [symParityMean_eq_div s L j N, ← mul_div_assoc]), ← Finset.sum_div, key, onesFreq,
    mul_div_assoc]

/-- The empty symmetrized correlation is identically one (for `N ≥ 1`). -/
theorem tendsto_symParityMean_zero (s : ℕ → ℕ) (L : ℕ) :
    Tendsto (symParityMean s L 0) atTop (𝓝 1) := by
  have h : ∀ N : ℕ, 1 ≤ N → symParityMean s L 0 N = 1 := by
    intro N hN
    rw [symParityMean, Finset.powersetCard_zero, Finset.sum_singleton, parityMean]
    simp only [parityChar_empty, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact div_self (Nat.cast_ne_zero.mpr (by omega))
  exact Tendsto.congr' (eventually_atTop.mpr ⟨1, fun N hN => (h N hN).symm⟩) tendsto_const_nhds

/-- **Headline.**  Abelian normality in base two is the vanishing of the symmetrized parity
correlations. -/
theorem isAbelianNormalTwo_iff_symParityMean (s : ℕ → ℕ) (hs : ∀ m, s m < 2) :
    IsAbelianNormalTwo s ↔
      ∀ L j : ℕ, 1 ≤ j → j ≤ L → Tendsto (symParityMean s L j) atTop (𝓝 0) := by
  constructor
  · intro hab L j hj _
    have hlim : Tendsto (fun N => ∑ w ∈ range (L + 1), kraw L j w * onesFreq s L w N) atTop
        (𝓝 (∑ w ∈ range (L + 1), kraw L j w * ((L.choose w : ℝ) / 2 ^ L))) :=
      tendsto_finsetSum _ (fun w hw => tendsto_const_nhds.mul
        (hab L w (by simpa [Nat.lt_succ_iff] using hw)))
    have hzero : ∑ w ∈ range (L + 1), kraw L j w * ((L.choose w : ℝ) / 2 ^ L) = 0 := by
      rw [Finset.sum_congr rfl (fun w (_ : w ∈ range (L + 1)) => by
        rw [← mul_div_assoc]), ← Finset.sum_div, sum_kraw_mul_choose L j hj, zero_div]
    rw [hzero] at hlim
    exact hlim.congr (fun N => (symParityMean_eq s hs L j N).symm)
  · intro hsym L w hw
    have hlim : Tendsto (fun N => ∑ j ∈ range (L + 1), kraw L w j * symParityMean s L j N) atTop
        (𝓝 ((L.choose w : ℝ))) := by
      have hsplit : ∀ N : ℕ, ∑ j ∈ range (L + 1), kraw L w j * symParityMean s L j N
          = (∑ i ∈ range L, kraw L w (i + 1) * symParityMean s L (i + 1) N)
            + kraw L w 0 * symParityMean s L 0 N :=
        fun N => Finset.sum_range_succ' _ L
      have htail : Tendsto (fun N => ∑ i ∈ range L, kraw L w (i + 1) * symParityMean s L (i + 1) N)
          atTop (𝓝 0) := by
        have := tendsto_finsetSum (range L)
          (f := fun i N => kraw L w (i + 1) * symParityMean s L (i + 1) N)
          (a := fun _ => (0 : ℝ))
          (fun i hi => by
            simpa using (tendsto_const_nhds (x := kraw L w (i + 1))).mul
              (hsym L (i + 1) (Nat.le_add_left 1 i) (by simpa using Finset.mem_range.mp hi)))
        simpa using this
      have hhead : Tendsto (fun N => kraw L w 0 * symParityMean s L 0 N) atTop
          (𝓝 ((L.choose w : ℝ))) := by
        have h0 := (tendsto_const_nhds (x := kraw L w 0) (f := atTop (α := ℕ))).mul
          (tendsto_symParityMean_zero s L)
        rw [mul_one] at h0
        rw [← kraw_weight_zero L w]
        exact h0
      have := htail.add hhead
      rw [zero_add] at this
      exact this.congr (fun N => (hsplit N).symm)
    have hpow : (2 : ℝ) ^ L ≠ 0 := by positivity
    have := hlim.div_const ((2 : ℝ) ^ L)
    refine this.congr (fun N => ?_)
    rw [← onesFreq_eq s hs L w N]
    field_simp

/-- Normal implies abelian-normal (corollary of the headline and the Walsh criterion). -/
theorem isAbelianNormalTwo_of_isNormalSequence (s : ℕ → ℕ) (hs : ∀ m, s m < 2)
    (h : IsNormalSequence 2 s) : IsAbelianNormalTwo s := by
  refine (isAbelianNormalTwo_iff_symParityMean s hs).mpr (fun L j hj _ => ?_)
  have hpar := (isNormalSequence_two_iff_parityMean s hs).mp h
  have := tendsto_finsetSum ((range L).powersetCard j)
    (f := fun S N => parityMean s S N) (a := fun _ => (0 : ℝ))
    (fun S hS => hpar S (Finset.card_pos.mp (by
      rw [(Finset.mem_powersetCard.mp hS).2]; omega)))
  have h0 : (∑ _S ∈ (range L).powersetCard j, (0 : ℝ)) = 0 := Finset.sum_const_zero
  rw [h0] at this
  exact this.congr (fun N => rfl)

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
