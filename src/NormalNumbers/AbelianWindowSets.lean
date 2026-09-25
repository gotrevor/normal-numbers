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

/-! ## Window frequencies of a periodic sequence

For a sequence of period `D`, the length-`L` window one-count depends only on the starting
position mod `D`, so the frequency of weight `j` converges to the exact rational
`#{r < D : onesCount s L r = j} / D`.  This is the bridge from finite combinatorics on cyclic
words to `IsAbelianAt`, and it is what makes periodic witnesses usable. -/

section Periodic

variable (p : ℕ → Prop) [DecidablePred p]

/-- Indicator of `p`, as a real-valued function. -/
noncomputable def ind (n : ℕ) : ℝ := if p n then 1 else 0

theorem ind_nonneg (n : ℕ) : 0 ≤ ind p n := by unfold ind; split <;> norm_num

theorem ind_le_one (n : ℕ) : ind p n ≤ 1 := by unfold ind; split <;> norm_num

theorem sum_ind_eq_card (M : ℕ) :
    ∑ n ∈ range M, ind p n = (((range M).filter p).card : ℝ) := by
  rw [Finset.card_filter]
  push_cast
  simp [ind]

theorem sum_ind_le (M : ℕ) : ∑ n ∈ range M, ind p n ≤ M := by
  calc ∑ n ∈ range M, ind p n ≤ ∑ _n ∈ range M, (1 : ℝ) :=
        Finset.sum_le_sum (fun n _ => ind_le_one p n)
    _ = M := by simp

theorem sum_ind_nonneg (M : ℕ) : 0 ≤ ∑ n ∈ range M, ind p n :=
  Finset.sum_nonneg (fun n _ => ind_nonneg p n)

variable {p}

/-- A `D`-periodic predicate is invariant under shifts by multiples of `D`. -/
theorem ind_shift_mul (D : ℕ) (hp : ∀ n, p (n + D) ↔ p n) (q n : ℕ) :
    ind p (q * D + n) = ind p n := by
  induction q with
  | zero => simp
  | succ q ih =>
      have : (q + 1) * D + n = (q * D + n) + D := by ring
      rw [this]
      unfold ind
      simp only [hp (q * D + n)]
      exact ih

/-- The indicator sum over `q` full periods. -/
theorem sum_ind_period (D : ℕ) (hp : ∀ n, p (n + D) ↔ p n) (q : ℕ) :
    ∑ n ∈ range (q * D), ind p n = q * ∑ n ∈ range D, ind p n := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hrw : (q + 1) * D = q * D + D := by ring
      rw [hrw, Finset.sum_range_add, ih]
      have : ∀ n ∈ range D, ind p (q * D + n) = ind p n :=
        fun n _ => ind_shift_mul D hp q n
      rw [Finset.sum_congr rfl this]
      push_cast; ring

/-- The empirical frequency of a `D`-periodic predicate converges to its exact period average. -/
theorem tendsto_ind_freq (D : ℕ) (hD : 0 < D) (hp : ∀ n, p (n + D) ↔ p n) :
    Tendsto (fun N : ℕ => (((range N).filter p).card : ℝ) / N) atTop
      (𝓝 ((((range D).filter p).card : ℝ) / D)) := by
  set C : ℝ := ∑ n ∈ range D, ind p n with hC
  have hCle : C ≤ D := sum_ind_le p D
  have hCnn : 0 ≤ C := sum_ind_nonneg p D
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  -- pointwise bound
  have hbound : ∀ N : ℕ, 0 < N →
      |(∑ n ∈ range N, ind p n) / N - C / D| ≤ 2 * D / N := by
    intro N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    obtain ⟨q, t, htD, hNq⟩ : ∃ q t, t < D ∧ N = q * D + t :=
      ⟨N / D, N % D, Nat.mod_lt _ hD, (Nat.div_add_mod' N D).symm⟩
    have hsum : ∑ n ∈ range N, ind p n = q * C + ∑ n ∈ range t, ind p (q * D + n) := by
      rw [hNq, Finset.sum_range_add, sum_ind_period D hp q]
    have htail : 0 ≤ ∑ n ∈ range t, ind p (q * D + n) := by
      exact Finset.sum_nonneg (fun n _ => ind_nonneg p _)
    have htail2 : ∑ n ∈ range t, ind p (q * D + n) ≤ t := by
      calc ∑ n ∈ range t, ind p (q * D + n) ≤ ∑ _n ∈ range t, (1 : ℝ) :=
            Finset.sum_le_sum (fun n _ => ind_le_one p _)
        _ = t := by simp
    have hNRq : (N : ℝ) = q * D + t := by rw [hNq]; push_cast; ring
    have htR : (t : ℝ) ≤ D := by exact_mod_cast htD.le
    have hkey : (∑ n ∈ range N, ind p n) - (N : ℝ) * (C / D)
        = (∑ n ∈ range t, ind p (q * D + n)) - t * (C / D) := by
      rw [hsum, hNRq]
      field_simp
      ring
    have habs : |(∑ n ∈ range N, ind p n) - (N : ℝ) * (C / D)| ≤ 2 * D := by
      rw [hkey]
      have h1 : |(∑ n ∈ range t, ind p (q * D + n))| ≤ D := by
        rw [abs_of_nonneg htail]; linarith
      have h2 : |(t : ℝ) * (C / D)| ≤ D := by
        rw [abs_of_nonneg (by positivity)]
        have : (C / D) ≤ 1 := by rw [div_le_one hDR]; exact hCle
        nlinarith [Nat.cast_nonneg (α := ℝ) t]
      calc |(∑ n ∈ range t, ind p (q * D + n)) - t * (C / D)|
          ≤ |(∑ n ∈ range t, ind p (q * D + n))| + |(t : ℝ) * (C / D)| := by
            have := abs_add_le (∑ n ∈ range t, ind p (q * D + n)) (-((t : ℝ) * (C / D)))
            rw [← sub_eq_add_neg, abs_neg] at this
            exact this
        _ ≤ 2 * D := by linarith
    have hsplit : (∑ n ∈ range N, ind p n) / N - C / D
        = ((∑ n ∈ range N, ind p n) - N * (C / D)) / N := by field_simp
    rw [hsplit, abs_div, abs_of_pos hNR]
    gcongr
  have herr : Tendsto (fun N : ℕ => 2 * (D : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hmain : Tendsto (fun N : ℕ => (∑ n ∈ range N, ind p n) / N) atTop (𝓝 (C / D)) := by
    rw [← sub_zero (C / D)]
    have := squeeze_zero_norm'
      (eventually_atTop.mpr ⟨1, fun N (hN : 1 ≤ N) => by
        show ‖(∑ n ∈ range N, ind p n) / N - C / D‖ ≤ 2 * (D : ℝ) / N
        rw [Real.norm_eq_abs]; exact hbound N (by omega)⟩) herr
    simpa using this.add (tendsto_const_nhds (x := C / D))
  have hCcard : C = (((range D).filter p).card : ℝ) := sum_ind_eq_card p D
  rw [← hCcard]
  exact hmain.congr (fun N => by rw [sum_ind_eq_card])

end Periodic

/-- A `D`-periodic sequence has `D`-periodic window one-counts. -/
theorem onesCount_periodic (s : ℕ → ℕ) (D : ℕ) (hper : ∀ n, s (n + D) = s n) (L n : ℕ) :
    onesCount s L (n + D) = onesCount s L n := by
  unfold onesCount windowSet
  congr 1
  refine Finset.filter_congr (fun i _ => ?_)
  have : n + D + i = n + i + D := by ring
  rw [this, hper]

/-- **The periodic window law.**  The length-`L` weight-`j` frequency of a `D`-periodic sequence
converges to the exact rational `#{r < D : onesCount s L r = j} / D`. -/
theorem tendsto_onesFreq_periodic (s : ℕ → ℕ) (D : ℕ) (hD : 0 < D) (hper : ∀ n, s (n + D) = s n)
    (L j : ℕ) :
    Tendsto (onesFreq s L j) atTop
      (𝓝 ((((range D).filter (fun r => onesCount s L r = j)).card : ℝ) / D)) := by
  have hp : ∀ n, (onesCount s L (n + D) = j) ↔ (onesCount s L n = j) := by
    intro n; rw [onesCount_periodic s D hper L n]
  exact tendsto_ind_freq D hD hp

/-- Abelian-ness at `L` for a periodic sequence is the exact finite condition on its cyclic
window counts. -/
theorem isAbelianAt_periodic_iff (s : ℕ → ℕ) (D : ℕ) (hD : 0 < D) (hper : ∀ n, s (n + D) = s n)
    (L : ℕ) :
    IsAbelianAt s L ↔ ∀ j ≤ L,
      (((range D).filter (fun r => onesCount s L r = j)).card : ℝ) / D
        = (L.choose j : ℝ) / 2 ^ L := by
  constructor
  · intro h j hj
    exact tendsto_nhds_unique (tendsto_onesFreq_periodic s D hD hper L j) (h j hj)
  · intro h j hj
    rw [← h j hj]
    exact tendsto_onesFreq_periodic s D hD hper L j

/-! ## Realizability: the empty set -/

/-- The all-zeros sequence has every window one-count equal to `0`. -/
theorem onesCount_zero_fun (L n : ℕ) : onesCount (fun _ => 0) L n = 0 := by
  simp [onesCount, windowSet]

theorem onesFreq_zero_fun (L N : ℕ) (hN : 1 ≤ N) : onesFreq (fun _ => 0) L 0 N = 1 := by
  rw [onesFreq]
  have : (range N).filter (fun n => onesCount (fun _ => 0) L n = 0) = range N := by
    apply Finset.filter_true_of_mem
    intro n _
    exact onesCount_zero_fun L n
  rw [this, Finset.card_range]
  exact div_self (Nat.cast_ne_zero.mpr (by omega))

/-- The all-zeros sequence is abelian at no length `L ≥ 1`. -/
theorem not_isAbelianAt_zero_fun (L : ℕ) (hL : 1 ≤ L) :
    ¬ IsAbelianAt (fun _ => 0) L := by
  intro h
  have h0 := h 0 (Nat.zero_le _)
  have h1 : Tendsto (onesFreq (fun _ => 0) L 0) atTop (𝓝 1) :=
    Tendsto.congr' (eventually_atTop.mpr ⟨1, fun N hN => (onesFreq_zero_fun L N hN).symm⟩)
      tendsto_const_nhds
  have heq : ((L.choose 0 : ℝ) / 2 ^ L) = 1 := tendsto_nhds_unique h0 h1
  rw [Nat.choose_zero_right] at heq
  have hpow : (1 : ℝ) < 2 ^ L := by
    refine one_lt_pow₀ (by norm_num) (by omega)
  rw [Nat.cast_one, div_eq_one_iff_eq (by positivity)] at heq
  linarith

/-! ## Realizability: the hard branch

The remaining obligation.  Written in the symmetrized coordinates of `AbelianNormal.lean`, for a
sequence whose parity correlations `c T = lim_N parityMean s T N` all exist,

  `IsAbelianAt s L  ↔  ∀ 1 ≤ j ≤ L, F j L = 0`,  where  `F j L = ∑_{T ⊆ [0,L), |T| = j} c T`.

Shift invariance makes `c` a function of the *shape* of `T`.  For a process whose only nonzero
correlations are on pairs, `F 1 L = L * c {0}` and `F 2 L = ∑_{d=1}^{L-1} (L - d) * ρ d` with
`ρ d = c {0, d}`, and the second difference is `F 2 (L+1) - 2 * F 2 L + F 2 (L-1) = ρ L`.  So
`F 2` is an ARBITRARY sequence vanishing at `0` and `1` — which is exactly the shape of the
admissibility hypothesis `S = ∅ ∨ 1 ∈ S`.  That is the mechanism C4 rests on.

Obstruction found this lap: an exactly-pair-correlated stationary `±1` process does not exist
(positivity of the length-`n` Fourier expansion `2^{-n}(1 + ∑_{a<b} ρ(b-a) x_a x_b)` fails once
`n * ∑_d |ρ d| > 1`).  So the higher `F j` cannot be killed correlation-by-correlation; they must
be killed as symmetrized *sums*.  Block-i.i.d. processes (i.i.d. blocks of length `m`, uniform
random offset) do kill every `c T` whose trace on some block has odd size, leaving `ρ̃ d =
ρ d * (m - d) / m` supported on `d < m`; but then `F 2` is eventually affine, so a single scale
`m` can only realize `S` that is cofinite-or-bounded in a rigid way.  Infinite `S` needs
infinitely many scales. -/

/-- **C4, hard branch.**  Every set of window lengths containing `1` is realized exactly. -/
theorem c4_realizable_of_mem_one (S : Set ℕ) (hS : ∀ L ∈ S, 1 ≤ L) (h1 : 1 ∈ S) :
    ∃ s : ℕ → ℕ, (∀ m, s m < 2) ∧ ∀ L : ℕ, 1 ≤ L → (IsAbelianAt s L ↔ L ∈ S) := by
  sorry

/-- **C4 (ratified headline).**  Every admissible set of window lengths is realized exactly. -/
theorem c4_realizable (S : Set ℕ) (hS : ∀ L ∈ S, 1 ≤ L) (hadm : S = ∅ ∨ 1 ∈ S) :
    ∃ s : ℕ → ℕ, (∀ m, s m < 2) ∧ ∀ L : ℕ, 1 ≤ L → (IsAbelianAt s L ↔ L ∈ S) := by
  rcases hadm with rfl | h1
  · refine ⟨fun _ => 0, fun m => by norm_num, fun L hL => ?_⟩
    simp only [Set.mem_empty_iff_false, iff_false]
    exact not_isAbelianAt_zero_fun L hL
  · exact c4_realizable_of_mem_one S hS h1

end NormalNumbers.Abelian
