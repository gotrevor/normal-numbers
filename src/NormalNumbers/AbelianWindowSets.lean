import NormalNumbers.AbelianNormal

/-!
# C4: which sets of window lengths can a binary sequence be abelian-normal at, exactly?

Conjecture C4 (`CONJECTURES-2026-09-23-casting-out-and-rungs.md`): for every `S ⊆ {L ≥ 1}` with
`S = ∅` or `1 ∈ S` — infinite `S` included — some binary sequence is abelian at exactly the
lengths in `S`.  The one forced implication is `abelianAt_one_of_abelianAt` (the mean of
Binomial(`L`, 1/2) forces digit density 1/2).  Probe: `probes/abelian_window_sets.py` (finite `S`,
`k ≤ 8`, Markov perturbations of the uniform measure).  See `KICKOFF-2026-09-24-c4.md`.
-/

open Finset Filter Topology

namespace NormalNumbers.Abelian

open NormalNumbers.Walsh

/-- Abelian at the single window length `L`: one-counts of length-`L` windows are
asymptotically Binomial(`L`, 1/2). -/
def IsAbelianAt (s : ℕ → ℕ) (L : ℕ) : Prop :=
  ∀ j : ℕ, j ≤ L → Tendsto (onesFreq s L j) atTop (𝓝 ((L.choose j : ℝ) / 2 ^ L))

/-! ## Per-length version of the symmetrized criterion -/

/-- One direction of `isAbelianNormalTwo_iff_symParityMean`, at a single window length. -/
theorem symParityMean_tendsto_zero_of_abelianAt (s : ℕ → ℕ) (hs : ∀ m, s m < 2) (L : ℕ)
    (h : IsAbelianAt s L) (j : ℕ) (hj : 1 ≤ j) :
    Tendsto (symParityMean s L j) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N => ∑ w ∈ range (L + 1), kraw L j w * onesFreq s L w N) atTop
      (𝓝 (∑ w ∈ range (L + 1), kraw L j w * ((L.choose w : ℝ) / 2 ^ L))) :=
    tendsto_finsetSum _ (fun w hw => tendsto_const_nhds.mul
      (h w (by simpa [Nat.lt_succ_iff] using hw)))
  have hzero : ∑ w ∈ range (L + 1), kraw L j w * ((L.choose w : ℝ) / 2 ^ L) = 0 := by
    rw [Finset.sum_congr rfl (fun w (_ : w ∈ range (L + 1)) => by
      rw [← mul_div_assoc]), ← Finset.sum_div, sum_kraw_mul_choose L j hj, zero_div]
  rw [hzero] at hlim
  exact hlim.congr (fun N => (symParityMean_eq s hs L j N).symm)

/-- The converse, at a single window length. -/
theorem abelianAt_of_symParityMean (s : ℕ → ℕ) (hs : ∀ m, s m < 2) (L : ℕ)
    (hsym : ∀ j : ℕ, 1 ≤ j → j ≤ L → Tendsto (symParityMean s L j) atTop (𝓝 0)) :
    IsAbelianAt s L := by
  intro w hw
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
            (hsym (i + 1) (Nat.le_add_left 1 i) (by simpa using Finset.mem_range.mp hi)))
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

/-! ## The shift estimate -/

/-- The sign of the digit at position `m`. -/
noncomputable def digitSign (s : ℕ → ℕ) (m : ℕ) : ℝ := (-1 : ℝ) ^ s m

theorem parityChar_singleton (s : ℕ → ℕ) (i n : ℕ) :
    parityChar s {i} n = digitSign s (n + i) := by
  simp [parityChar, digitSign]

theorem abs_digitSign (s : ℕ → ℕ) (m : ℕ) : |digitSign s m| = 1 := by
  simp [digitSign, abs_pow]

/-- Shifting the summation window changes the sum by at most `2 i`. -/
theorem abs_shift_sum_sub (s : ℕ → ℕ) (N i : ℕ) :
    |(∑ n ∈ range N, digitSign s (n + i)) - ∑ n ∈ range N, digitSign s n| ≤ 2 * i := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hstep : (∑ n ∈ range N, digitSign s (n + (i + 1)))
          = (∑ n ∈ range N, digitSign s (n + i)) + digitSign s (N + i) - digitSign s i := by
        have h1 : ∑ n ∈ range (N + 1), digitSign s (n + i)
            = (∑ n ∈ range N, digitSign s (n + i)) + digitSign s (N + i) :=
          Finset.sum_range_succ _ N
        have h2 : ∑ n ∈ range (N + 1), digitSign s (n + i)
            = (∑ n ∈ range N, digitSign s (n + 1 + i)) + digitSign s (0 + i) :=
          Finset.sum_range_succ' _ N
        have h3 : ∀ n : ℕ, n + 1 + i = n + (i + 1) := by intro n; omega
        simp only [h3, Nat.zero_add] at h2
        linarith [h1, h2]
      rw [hstep]
      have hb1 := abs_digitSign s (N + i)
      have hb2 := abs_digitSign s i
      have hle : |digitSign s (N + i) - digitSign s i| ≤ 2 := by
        have h := abs_add_le (digitSign s (N + i)) (-digitSign s i)
        rw [← sub_eq_add_neg, abs_neg, hb1, hb2] at h
        linarith
      have hsplitabs : (∑ n ∈ range N, digitSign s (n + i)) + digitSign s (N + i) - digitSign s i
              - ∑ n ∈ range N, digitSign s n
            = ((∑ n ∈ range N, digitSign s (n + i)) - ∑ n ∈ range N, digitSign s n)
              + (digitSign s (N + i) - digitSign s i) := by ring
      rw [hsplitabs]
      have := abs_add_le ((∑ n ∈ range N, digitSign s (n + i)) - ∑ n ∈ range N, digitSign s n)
        (digitSign s (N + i) - digitSign s i)
      have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith

/-! ## Necessity: abelian at `L` forces abelian at `1` -/

theorem symParityMean_one_eq (s : ℕ → ℕ) (L N : ℕ) :
    symParityMean s L 1 N = ∑ i ∈ range L, parityMean s {i} N := by
  rw [symParityMean, Finset.powersetCard_one, Finset.sum_map]
  rfl

theorem parityMean_singleton (s : ℕ → ℕ) (i N : ℕ) :
    parityMean s {i} N = (∑ n ∈ range N, digitSign s (n + i)) / N := by
  rw [parityMean]
  congr 1
  exact Finset.sum_congr rfl (fun n _ => parityChar_singleton s i n)

/-- The window-length-`L` first symmetrized correlation is `L` times the digit-sign mean, up to
a boundary error of order `L ^ 2 / N`. -/
theorem abs_symParityMean_one_sub (s : ℕ → ℕ) (L N : ℕ) :
    |symParityMean s L 1 N - L * parityMean s {0} N| ≤ 2 * L ^ 2 / N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [symParityMean_one_eq, parityMean]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hrw : symParityMean s L 1 N - L * parityMean s {0} N
      = (∑ i ∈ range L, ((∑ n ∈ range N, digitSign s (n + i))
          - ∑ n ∈ range N, digitSign s n)) / N := by
    rw [symParityMean_one_eq, Finset.sum_congr rfl (fun i (_ : i ∈ range L) =>
      parityMean_singleton s i N), parityMean_singleton s 0 N]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    field_simp
    ring
  rw [hrw, abs_div, abs_of_pos hNpos]
  have hnum : |∑ i ∈ range L, ((∑ n ∈ range N, digitSign s (n + i))
      - ∑ n ∈ range N, digitSign s n)| ≤ 2 * (L : ℝ) ^ 2 := by
    calc |∑ i ∈ range L, ((∑ n ∈ range N, digitSign s (n + i))
            - ∑ n ∈ range N, digitSign s n)|
        ≤ ∑ i ∈ range L, |(∑ n ∈ range N, digitSign s (n + i))
            - ∑ n ∈ range N, digitSign s n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ range L, 2 * (L : ℝ) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          refine (abs_shift_sum_sub s N i).trans ?_
          have : (i : ℝ) ≤ (L : ℝ) := by
            exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hi))
          linarith
      _ = 2 * (L : ℝ) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  gcongr

/-- **NECESSITY.**  Abelian at any length `L ≥ 1` forces abelian at length 1. -/
theorem abelianAt_one_of_abelianAt' (s : ℕ → ℕ) (hs : ∀ m, s m < 2) (L : ℕ) (hL : 1 ≤ L)
    (h : IsAbelianAt s L) : IsAbelianAt s 1 := by
  have hsym := symParityMean_tendsto_zero_of_abelianAt s hs L h 1 le_rfl
  -- the boundary error tends to zero
  have herr : Tendsto (fun N : ℕ => 2 * (L : ℝ) ^ 2 / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hLmean : Tendsto (fun N : ℕ => (L : ℝ) * parityMean s {0} N) atTop (𝓝 0) := by
    have hdiff : Tendsto (fun N : ℕ => (L : ℝ) * parityMean s {0} N - symParityMean s L 1 N)
        atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ herr
      filter_upwards with N
      have := abs_symParityMean_one_sub s L N
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact this
    have := hdiff.add hsym
    simpa using this
  have hLne : (L : ℝ) ≠ 0 := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    exact ne_of_gt this
  have hmean : Tendsto (fun N : ℕ => parityMean s {0} N) atTop (𝓝 0) := by
    have h2 := hLmean.div_const (L : ℝ)
    rw [zero_div] at h2
    refine h2.congr (fun N => ?_)
    field_simp
  refine abelianAt_of_symParityMean s hs 1 (fun j hj1 hjle => ?_)
  have hj : j = 1 := le_antisymm hjle hj1
  subst hj
  refine hmean.congr (fun N => ?_)
  rw [symParityMean_one_eq]
  simp

/-- **NECESSITY (ratified).**  Abelian at any length forces abelian at length 1. -/
theorem abelianAt_one_of_abelianAt (s : ℕ → ℕ) (hs : ∀ m, s m < 2) (L : ℕ) (hL : 1 ≤ L)
    (h : IsAbelianAt s L) : IsAbelianAt s 1 :=
  abelianAt_one_of_abelianAt' s hs L hL h

/-- **C4 (ratified headline).**  Every admissible set of window lengths is realized exactly. -/
theorem c4_realizable (S : Set ℕ) (hS : ∀ L ∈ S, 1 ≤ L) (hadm : S = ∅ ∨ 1 ∈ S) :
    ∃ s : ℕ → ℕ, (∀ m, s m < 2) ∧ ∀ L : ℕ, 1 ≤ L → (IsAbelianAt s L ↔ L ∈ S) := by
  sorry

end NormalNumbers.Abelian
