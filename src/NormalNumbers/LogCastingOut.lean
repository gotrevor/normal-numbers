/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ElliottLedger
import NormalNumbers.PairDecoupleTwoPoint
import NormalNumbers.SwingC1Log

/-!
# The logarithmic rung (E2): audit verdicts as Lean data

`docs/ENGINE-PROPOSALS-2026-10-04.md` §E2 proposed a rung between `count ≥ N^{1-ε}` and normality:
word frequencies under the weights `1/n`, with a log-averaged casting-out route that would consume
`ElliottTwoPointLog.TwoPointElliottLog` (which `ElliottLedger` reduces to one zeta-exponent input).
The audit (`docs/LOG-AVERAGE-AUDIT-2026-10-04.md`) records three findings, each stated here.

1. **The rung is distinct** (`tendsto_logFreq_dyadicBit`, `not_tendsto_natFreq_dyadicBit`).  The
   binary sequence whose digit `n` is `1` iff `⌊log₂(n+1)⌋` is even has logarithmic digit
   frequency `1/2` and no natural digit frequency at all.  So a log-averaged statement is never a
   natural-average statement in disguise.
2. **Consuming `TwoPointElliottLog` moves nothing on the casting-out route**
   (`twoPointWeightedLog_iff_weightDecoupleLog_of_zetaExponent`).  The log twin of the C1 pair
   leaf splits as `TwoPointElliottLog ∧ WeightDecoupleLog` exactly as the natural one does, and
   given the ledger's input the split is an *equivalence*: the whole crux sits in
   `WeightDecoupleLog`, the log twin of `PairDecoupleProve.multiElliott_all` (growing-depth
   Elliott with trivial product, open even at fixed depth `K = 2`).  Carries do not care how the
   positions are weighted (`SwingC1LogCarry.carry_correction_unbounded`).
3. **On the direct digit route the gap is uniformity in depth.**  The depth-`K` truncation of
   `e(h·bⁿ·G4_b)` is a `K`-point correlation of `ζ_k^ω` whose product is a nontrivial root of
   unity to the power `ω`; for FIXED `K` Tao–Teräväinen (2019) give log-averaged vanishing
   (`TaoTeravainen2019FixedDepth`, cited).  The reopen condition is the growing-depth version
   `GrowingDepthLogElliott`.

Prior art for the "unconstructed constant" claim: `TaoTeravainen2019LiouvilleThree` (log densities
of all Liouville sign patterns of length `≤ 3`), a carry-free constant with log 3-word frequencies.
-/

open Finset Filter Topology

namespace NormalNumbers.LogCastingOut

noncomputable section

/-! ## 1. The rung is distinct -/

/-- Digit `n` is `1` iff `⌊log₂ (n+1)⌋` is even, i.e. `n + 1 ∈ [4^k, 2·4^k)` for some `k`. -/
def dyadicBit (n : ℕ) : ℕ := if Even (Nat.log 2 (n + 1)) then 1 else 0

/-- Natural frequency of the digit `d` among the first `N` terms. -/
def natFreq (s : ℕ → ℕ) (d N : ℕ) : ℝ :=
  (((range N).filter (fun n => s n = d)).card : ℝ) / N

/-- Logarithmic frequency of the digit `d` among the first `N` terms (weights `1/(n+1)`, the
convention of `CastingOut.digitFreqLog`). -/
def logFreq (s : ℕ → ℕ) (d N : ℕ) : ℝ :=
  (∑ n ∈ (range N).filter (fun n => s n = d), (1 : ℝ) / (n + 1)) /
    ∑ n ∈ range N, (1 : ℝ) / (n + 1)

/-- The sign `±1` on the positive integer `m`, by the parity of `⌊log₂ m⌋`. -/
def sgn (m : ℕ) : ℝ := if Even (Nat.log 2 m) then 1 else -1

/-- Harmonic mass of the dyadic block `[2^j, 2^{j+1})`. -/
def blockMass (j : ℕ) : ℝ := ∑ m ∈ (Ico (2 ^ j) (2 ^ (j + 1)) : Finset ℕ), (1 : ℝ) / m

/-- Alternating sum of the first `J` block masses. -/
def altSum (J : ℕ) : ℝ := ∑ j ∈ range J, (-1 : ℝ) ^ j * blockMass j

/-- `Σ_{m=1}^{M} sgn(m)/m`. -/
def signedHarm (M : ℕ) : ℝ := ∑ m ∈ Ico 1 (M + 1), sgn m / m

lemma sgn_eq (m : ℕ) : sgn m = (-1 : ℝ) ^ Nat.log 2 m := by
  unfold sgn
  rcases Nat.even_or_odd (Nat.log 2 m) with h | h
  · rw [if_pos h, h.neg_one_pow]
  · rw [if_neg (Nat.not_even_iff_odd.mpr h), h.neg_one_pow]

lemma sum_Ico_double (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ m ∈ Ico (2 * a) (2 * b), f m = ∑ k ∈ Ico a b, (f (2 * k) + f (2 * k + 1)) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [show 2 * (b + 1) = 2 * b + 1 + 1 by ring,
      Finset.sum_Ico_succ_top (a := 2 * a) (b := 2 * b + 1) (by omega),
      Finset.sum_Ico_succ_top (a := 2 * a) (b := 2 * b) (by omega), ih,
      Finset.sum_Ico_succ_top (a := a) (b := b) hab]
    ring

lemma blockMass_nonneg (j : ℕ) : 0 ≤ blockMass j :=
  Finset.sum_nonneg fun m _ => by positivity

lemma blockMass_zero : blockMass 0 = 1 := by
  simp [blockMass]

lemma blockMass_succ_le (j : ℕ) : blockMass (j + 1) ≤ blockMass j := by
  have hle : 2 ^ j ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ j)
  have e := sum_Ico_double (fun m => (1 : ℝ) / m) hle
  rw [← pow_succ', ← pow_succ'] at e
  unfold blockMass
  rw [e]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk1 : (1 : ℝ) ≤ k := by
    have := (Finset.mem_Ico.mp hk).1
    exact_mod_cast le_trans Nat.one_le_two_pow this
  push_cast
  have h1 : (1 : ℝ) / (2 * k + 1) ≤ 1 / (2 * k) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have h2 : (1 : ℝ) / (2 * k) + 1 / (2 * k) = 1 / k := by
    field_simp; ring
  linarith

lemma altSum_succ (J : ℕ) : altSum (J + 1) = altSum J + (-1 : ℝ) ^ J * blockMass J :=
  Finset.sum_range_succ _ _

lemma altSum_two_mul_succ (i : ℕ) :
    altSum (2 * i + 1) = altSum (2 * i) + blockMass (2 * i) := by
  rw [altSum_succ, (Even.neg_one_pow ⟨i, by ring⟩ : (-1 : ℝ) ^ (2 * i) = 1), one_mul]

lemma altSum_two_mul_add_two (i : ℕ) :
    altSum (2 * i + 1 + 1) = altSum (2 * i + 1) - blockMass (2 * i + 1) := by
  rw [altSum_succ, (Odd.neg_one_pow ⟨i, rfl⟩ : (-1 : ℝ) ^ (2 * i + 1) = -1)]
  ring

/-- The alternating-series invariant: even partial sums are `≥ 0`, odd ones `≤ 1`. -/
lemma altSum_bounds (i : ℕ) : 0 ≤ altSum (2 * i) ∧ altSum (2 * i) + blockMass (2 * i) ≤ 1 := by
  induction i with
  | zero => simp [altSum, blockMass_zero]
  | succ i ih =>
    obtain ⟨h0, h1⟩ := ih
    have e : altSum (2 * (i + 1)) = altSum (2 * i) + blockMass (2 * i) - blockMass (2 * i + 1) := by
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, altSum_two_mul_add_two,
        altSum_two_mul_succ]
    have m1 := blockMass_succ_le (2 * i)
    have m2 := blockMass_succ_le (2 * i + 1)
    rw [e, show 2 * (i + 1) = 2 * i + 1 + 1 by ring]
    constructor <;> linarith

/-- Block decomposition of the signed harmonic sum. -/
lemma signedHarm_eq (M : ℕ) (hM : 1 ≤ M) :
    signedHarm M = altSum (Nat.log 2 M) +
      (-1 : ℝ) ^ (Nat.log 2 M) * ∑ m ∈ (Ico (2 ^ Nat.log 2 M) (M + 1) : Finset ℕ), (1 : ℝ) / m := by
  induction M, hM using Nat.le_induction with
  | base => simp [signedHarm, altSum, sgn]
  | succ M hM ih =>
    set j := Nat.log 2 M with hj
    have hlo : 2 ^ j ≤ M := Nat.pow_log_le_self 2 (by omega)
    have hhi : M < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) M
    have hstep : signedHarm (M + 1) = signedHarm M + sgn (M + 1) / ((M + 1 : ℕ) : ℝ) := by
      unfold signedHarm
      rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ M + 1)]
    rcases Nat.lt_or_ge (M + 1) (2 ^ (j + 1)) with h | h
    · have hj' : Nat.log 2 (M + 1) = j := Nat.log_eq_of_pow_le_of_lt_pow (by omega) h
      rw [hstep, ih, sgn_eq, hj', Finset.sum_Ico_succ_top (by omega : 2 ^ j ≤ M + 1)]
      ring
    · have hM1 : M + 1 = 2 ^ (j + 1) := by omega
      have hj' : Nat.log 2 (M + 1) = j + 1 := by rw [hM1, Nat.log_pow (by norm_num)]
      have e1 : ∑ m ∈ (Ico (2 ^ j) (M + 1) : Finset ℕ), (1 : ℝ) / m = blockMass j := by
        rw [hM1]; rfl
      have e2 : ∑ m ∈ (Ico (2 ^ (j + 1)) (M + 1 + 1) : Finset ℕ), (1 : ℝ) / m = 1 / ((M + 1 : ℕ) : ℝ) := by
        rw [← hM1, Finset.sum_Ico_succ_top le_rfl, Finset.Ico_self, Finset.sum_empty, zero_add]
      rw [hstep, ih, sgn_eq, hj', altSum_succ, e1, e2]
      ring

/-- **The signed harmonic sum stays in `[0, 1]`.** -/
theorem signedHarm_mem (M : ℕ) : 0 ≤ signedHarm M ∧ signedHarm M ≤ 1 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [signedHarm]
  set j := Nat.log 2 M with hj
  have hhi : M < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) M
  set P := ∑ m ∈ (Ico (2 ^ j) (M + 1) : Finset ℕ), (1 : ℝ) / m with hPdef
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun m _ => by positivity
  have hPB : P ≤ blockMass j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl (by omega))
      fun m _ _ => by positivity
  rw [signedHarm_eq M hM, ← hj, ← hPdef]
  obtain ⟨i, hi | hi⟩ := Nat.even_or_odd' j
  · have hb := altSum_bounds i
    rw [← hi] at hb
    rw [hi, (Even.neg_one_pow ⟨i, by ring⟩ : (-1 : ℝ) ^ (2 * i) = 1), one_mul, ← hi]
    constructor <;> linarith [hb.1, hb.2]
  · have hb := altSum_bounds i
    have hb2 := altSum_bounds (i + 1)
    have e1 := altSum_two_mul_succ i
    have e2 := altSum_two_mul_add_two i
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring] at hb2
    rw [hi, (Odd.neg_one_pow ⟨i, rfl⟩ : (-1 : ℝ) ^ (2 * i + 1) = -1)]
    rw [hi] at hPB
    constructor <;> nlinarith [hb.1, hb.2, hb2.1, hb2.2]

lemma cast_dyadicBit (n : ℕ) :
    (dyadicBit n : ℝ) = if dyadicBit n = 1 then 1 else 0 := by
  unfold dyadicBit; split_ifs <;> simp_all

lemma signedHarm_eq_range (N : ℕ) :
    signedHarm N = ∑ n ∈ range N, (2 * (dyadicBit n : ℝ) - 1) / (n + 1) := by
  unfold signedHarm
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold sgn dyadicBit
  rw [show 1 + n = n + 1 by ring]
  split_ifs <;> push_cast <;> ring

lemma logNum_eq (N : ℕ) :
    ∑ n ∈ (range N).filter (fun n => dyadicBit n = 1), (1 : ℝ) / (n + 1)
      = ∑ n ∈ range N, (dyadicBit n : ℝ) / (n + 1) := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [cast_dyadicBit n]
  split_ifs <;> simp

/-- **The digit `1` has logarithmic frequency `1/2`.** -/
theorem tendsto_logFreq_dyadicBit :
    Tendsto (logFreq dyadicBit 1) atTop (𝓝 (1 / 2)) := by
  set H : ℕ → ℝ := fun N => ∑ n ∈ range N, (1 : ℝ) / (n + 1) with hHdef
  have hH : Tendsto H atTop atTop := Real.tendsto_sum_range_one_div_nat_succ_atTop
  have hform : ∀ N, 0 < H N → logFreq dyadicBit 1 N = 1 / 2 + signedHarm N / (2 * H N) := by
    intro N hN
    have hsplit : signedHarm N = 2 * (∑ n ∈ range N, (dyadicBit n : ℝ) / (n + 1)) - H N := by
      rw [signedHarm_eq_range, hHdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    unfold logFreq
    rw [logNum_eq]
    change (∑ n ∈ range N, (dyadicBit n : ℝ) / (n + 1)) / H N = _
    rw [hsplit]
    field_simp
    ring
  have hsmall : Tendsto (fun N => signedHarm N / (2 * H N)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun N => (1 / 2 : ℝ) * (H N)⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp hH).const_mul (1 / 2 : ℝ)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv ?_ ?_
    · filter_upwards [hH.eventually_gt_atTop 0] with N hN
      exact div_nonneg (signedHarm_mem N).1 (by positivity)
    · filter_upwards [hH.eventually_gt_atTop 0] with N hN
      rw [div_le_iff₀ (by positivity)]
      have := (signedHarm_mem N).2
      field_simp
      linarith
  have := (tendsto_const_nhds (x := (1 / 2 : ℝ))).add hsmall
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [hH.eventually_gt_atTop 0] with N hN
  exact (hform N hN).symm

lemma card_filter_dyadicBit (N : ℕ) :
    ((((range N).filter (fun n => dyadicBit n = 1)).card : ℕ) : ℝ)
      = ∑ n ∈ range N, (dyadicBit n : ℝ) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [cast_dyadicBit n]

/-- **The digit `1` has no natural frequency.**  With `tendsto_logFreq_dyadicBit`, the
logarithmic rung is strictly weaker than the natural one. -/
theorem not_tendsto_natFreq_dyadicBit (c : ℝ) :
    ¬ Tendsto (natFreq dyadicBit 1) atTop (𝓝 c) := by
  intro h
  have hlog : Tendsto (logFreq dyadicBit 1) atTop (𝓝 c) := by
    have h' : Tendsto (fun N => (∑ n ∈ range N, (dyadicBit n : ℝ)) / N) atTop (𝓝 c) :=
      h.congr fun N => by rw [natFreq, card_filter_dyadicBit]
    refine (CastingOut.tendsto_logAvg_of_tendsto_avg _ c h').congr fun N => ?_
    rw [logFreq, logNum_eq]
  have hc : c = 1 / 2 := tendsto_nhds_unique hlog tendsto_logFreq_dyadicBit
  subst hc
  obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.mp h) (1 / 10) (by norm_num)
  set P := 2 ^ (2 * N0 + 1) with hPdef
  have hP : N0 + 2 ≤ P := by
    have := Nat.lt_two_pow_self (n := 2 * N0 + 1)
    omega
  have hP2 : 2 ^ (2 * N0 + 1 + 1) = 2 * P := by rw [pow_succ]; ring
  set N1 := P - 1 with hN1
  set N2 := 2 * P - 1 with hN2
  have hfilter : (range N2).filter (fun n => dyadicBit n = 1)
      = (range N1).filter (fun n => dyadicBit n = 1) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hn, hb⟩
      refine ⟨?_, hb⟩
      by_contra hge
      have hlog2 : Nat.log 2 (n + 1) = 2 * N0 + 1 :=
        Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by rw [hP2]; omega)
      have hodd : ¬ Even (Nat.log 2 (n + 1)) := by
        rw [hlog2, Nat.not_even_iff_odd]; exact ⟨N0, rfl⟩
      simp [dyadicBit, hodd] at hb
    · rintro ⟨hn, hb⟩; exact ⟨by omega, hb⟩
  set C : ℝ := (((range N1).filter (fun n => dyadicBit n = 1)).card : ℝ) with hC
  have hN1pos : (0 : ℝ) < N1 := by exact_mod_cast (show 0 < N1 by omega)
  have hN2eq : (N2 : ℝ) = 2 * N1 + 1 := by
    have : N2 = 2 * N1 + 1 := by omega
    exact_mod_cast this
  have f1 := hN0 N1 (by omega)
  have f2 := hN0 N2 (by omega)
  rw [Real.dist_eq, abs_lt] at f1 f2
  have e1 : natFreq dyadicBit 1 N1 = C / N1 := rfl
  have e2 : natFreq dyadicBit 1 N2 = C / N2 := by rw [natFreq, hfilter]
  rw [e1, div_sub' (ne_of_gt hN1pos)] at f1
  rw [e2, hN2eq, div_sub' (by positivity)] at f2
  obtain ⟨-, f1⟩ := f1
  obtain ⟨f2, -⟩ := f2
  rw [div_lt_iff₀ hN1pos] at f1
  rw [lt_div_iff₀ (by positivity)] at f2
  nlinarith

/-! ## 2. The casting-out pair route, logarithmically: consuming the ledger moves nothing -/

open NormalNumbers.CastingOut Erdos67b

/-- Logarithmic correlation over the ledger's window `2 ≤ n ≤ X`, weights `1/n`. -/
def logCorr (F : ℕ → ℂ) (X : ℕ) : ℂ :=
  ∑ n ∈ elliottLogWindow X X, (harmonicWeight n : ℂ) * F n

/-- Logarithmic mean, normalised by `log X` exactly as `TwoPointElliottLog` is. -/
def logMean (F : ℕ → ℂ) (X : ℕ) : ℂ := logCorr F X / (Real.log X : ℂ)

lemma norm_logMean (F : ℕ → ℂ) (X : ℕ) : ‖logMean F X‖ = ‖logCorr F X‖ / Real.log X := by
  rw [logMean, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_natCast_nonneg X)]

/-- The ledger's correlation is the log mean of the C1 two-point factor. -/
lemma elliottLogCorrelation_eq_logCorr (b p q : ℕ) (t : ℝ) (X : ℕ) :
    elliottLogCorrelation (ElliottTwoPointLog.zetaOmegaInt (t / b))
        (fun z => (starRingEnd ℂ) (ElliottTwoPointLog.zetaOmegaInt (t / b) z)) p q 1 1 X X
      = logCorr (twoPointFactor b p q t) X := by
  unfold elliottLogCorrelation logCorr
  refine Finset.sum_congr rfl fun n _ => ?_
  have h1 : integerAffine p 1 n = ((p * n + 1 : ℕ) : ℤ) := by
    simp only [integerAffine]; push_cast; ring
  have h2 : integerAffine q 1 n = ((q * n + 1 : ℕ) : ℤ) := by
    simp only [integerAffine]; push_cast; ring
  rw [h1, h2]
  simp only [ElliottTwoPointLog.zetaOmegaInt_natCast (show 0 < p * n + 1 by omega),
    ElliottTwoPointLog.zetaOmegaInt_natCast (show 0 < q * n + 1 by omega), twoPointFactor]
  ring

/-- `TwoPointElliottLog` is exactly "the log mean of the two-point factor tends to `0`". -/
theorem twoPointElliottLog_iff (b p q : ℕ) (t : ℝ) :
    ElliottTwoPointLog.TwoPointElliottLog b p q t ↔
      Tendsto (fun X => logMean (twoPointFactor b p q t) X) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero, ElliottTwoPointLog.TwoPointElliottLog]
  refine ⟨fun h => h.congr fun X => ?_, fun h => h.congr fun X => ?_⟩
  · rw [norm_logMean, elliottLogCorrelation_eq_logCorr]
  · rw [norm_logMean, elliottLogCorrelation_eq_logCorr]

lemma one_le_log_of_three_le {X : ℕ} (hX : 3 ≤ X) : 1 ≤ Real.log X := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h3 : (3 : ℝ) ≤ X := by exact_mod_cast hX
  have := Real.exp_one_lt_d9
  linarith

/-- Unit-bounded sequences have log mean at most `2` once `X ≥ 3`. -/
lemma norm_logMean_le_two (F : ℕ → ℂ) (hF : ∀ n, ‖F n‖ ≤ 1) {X : ℕ} (hX : 3 ≤ X) :
    ‖logMean F X‖ ≤ 2 := by
  have hlog := one_le_log_of_three_le hX
  have hmass : ‖logCorr F X‖ ≤ 1 + Real.log X := by
    calc ‖logCorr F X‖ ≤ ∑ n ∈ elliottLogWindow X X, ‖(harmonicWeight n : ℂ) * F n‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Icc 1 X, ((n : ℝ))⁻¹ := by
          refine le_trans (Finset.sum_le_sum fun n _ => ?_)
            (Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => by positivity)
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (harmonicWeight_nonneg n)]
            exact mul_le_of_le_one_right (harmonicWeight_nonneg n) (hF n)
          · have := mem_elliottLogWindow.mp hn
            exact Finset.mem_Icc.mpr ⟨this.1, this.2.1⟩
      _ = (harmonic X : ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; rfl
      _ ≤ 1 + Real.log X := harmonic_le_one_add_log X
  rw [norm_logMean, div_le_iff₀ (by linarith)]
  linarith

lemma tendsto_logMean_mul_zero {F W : ℕ → ℂ} (hW : ∀ n, ‖W n‖ ≤ 1)
    (hF : Tendsto (fun X => logMean F X) atTop (𝓝 0)) :
    Tendsto (fun X => logMean F X * logMean W X) atTop (𝓝 0) := by
  have hn := (tendsto_zero_iff_norm_tendsto_zero.mp hF).const_mul 2
  rw [mul_zero] at hn
  refine squeeze_zero_norm' ?_ hn
  filter_upwards [eventually_ge_atTop 3] with X hX
  rw [norm_mul, mul_comm 2]
  exact mul_le_mul_of_nonneg_left (norm_logMean_le_two W hW hX) (norm_nonneg _)

/-- The log twin of `CastingOut.TwoPointWeighted`: the leading-digit-peeled pair correlation. -/
def TwoPointWeightedLog (b p q : ℕ) (t : ℝ) : Prop :=
  Tendsto (fun X => logMean (fun n => twoPointFactor b p q t n * peelWeight b p q t n) X)
    atTop (𝓝 0)

/-- The log twin of `CastingOut.WeightDecouple`. -/
def WeightDecoupleLog (b p q : ℕ) (t : ℝ) : Prop :=
  Tendsto (fun X =>
      logMean (fun n => twoPointFactor b p q t n * peelWeight b p q t n) X
        - logMean (twoPointFactor b p q t) X * logMean (peelWeight b p q t) X)
    atTop (𝓝 0)

/-- **The log split.**  The ledger's statement plus the log decoupling give the log pair leaf. -/
theorem twoPointWeightedLog_of_split {b p q : ℕ} {t : ℝ}
    (hE : ElliottTwoPointLog.TwoPointElliottLog b p q t) (hW : WeightDecoupleLog b p q t) :
    TwoPointWeightedLog b p q t := by
  have hprod := tendsto_logMean_mul_zero (fun n => le_of_eq (norm_peelWeight b p q t n))
    ((twoPointElliottLog_iff b p q t).mp hE)
  have := hW.add hprod
  rw [zero_add] at this
  exact this.congr fun X => by ring

/-- **The converse.**  Given the ledger's statement, the log pair leaf gives the decoupling back. -/
theorem weightDecoupleLog_of_twoPointWeightedLog {b p q : ℕ} {t : ℝ}
    (hE : ElliottTwoPointLog.TwoPointElliottLog b p q t) (h : TwoPointWeightedLog b p q t) :
    WeightDecoupleLog b p q t := by
  have hprod := tendsto_logMean_mul_zero (fun n => le_of_eq (norm_peelWeight b p q t n))
    ((twoPointElliottLog_iff b p q t).mp hE)
  have := h.sub hprod
  rw [sub_zero] at this
  exact this

theorem twoPointWeightedLog_iff_weightDecoupleLog {b p q : ℕ} {t : ℝ}
    (hE : ElliottTwoPointLog.TwoPointElliottLog b p q t) :
    TwoPointWeightedLog b p q t ↔ WeightDecoupleLog b p q t :=
  ⟨weightDecoupleLog_of_twoPointWeightedLog hE, twoPointWeightedLog_of_split hE⟩

/-- **E2's consumer, wired to the ledger, is an equivalence.**  Under the ledger's single input
(`ZetaLogDerivExponent θ`, `θ < 1`; Vinogradov–Korobov gives `θ = 2/3`) the log pair leaf of the
casting-out route is EQUIVALENT to the log decoupling.  Consuming `TwoPointElliottLog` therefore
removes none of the crux: all of it sits in `WeightDecoupleLog`, the log twin of
`PairDecoupleProve.multiElliott_all` (Elliott for `4K` forms, `K → ∞`, trivial product; open in
log average already at `K = 2`). -/
theorem twoPointWeightedLog_iff_weightDecoupleLog_of_zetaExponent {b p q : ℕ} {t θ : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q) (hu : (phase (t / b)).re < 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (h : ElliottZetaTheta.ZetaLogDerivExponent θ) :
    TwoPointWeightedLog b p q t ↔ WeightDecoupleLog b p q t :=
  twoPointWeightedLog_iff_weightDecoupleLog
    (ElliottLedger.twoPointElliottLog_of_zetaExponent hp hq hpq hu hθ0 hθ1 h)

/-! ## 3. The direct digit route: fixed depth is cited, growing depth is the reopen condition -/

/-- Depth-`K` truncation of `e(h·bⁿ·G4_b)`: `bⁿ G4_b ≡ Σ_{k≥0} ω(n+1+k)·b^{-(k+1)} (mod 1)`, so
the phase factors as `∏_{k<K} ζ_k^{ω(n+1+k)}`, `ζ_k = e(h/b^{k+1})`. -/
def digitTruncPhase (b : ℕ) (h : ℤ) (K n : ℕ) : ℂ :=
  ∏ k ∈ range K, phase ((h : ℝ) / (b : ℝ) ^ (k + 1)) ^ omegaNat (n + 1 + k)

/-- **Tao–Teräväinen 2019, at fixed depth** (Duke Math. J. 168 (2019), arXiv:1708.02610, the
structure theorem's vanishing case: if `g₀⋯g_k` does not weakly pretend to be a Dirichlet
character, the log-averaged correlation vanishes).  Here `g_k = ζ_k^ω`, whose product is
`ζ^ω` with `ζ = e(h(b^K − 1)/((b − 1)b^K))`, a root of unity `≠ 1` when `b ∤ h` and `K ≥ 1`,
hence not weakly pretentious.  Specialised to the shifts `n+1, …, n+K` and the full window
`2 ≤ n ≤ X`.  Cited, not proved; needs a referee for the passage from TT's generalised limits at
scale `[x/ω(x), x]` to the full window, and for the weak-pretentiousness check. -/
def TaoTeravainen2019FixedDepth (b : ℕ) : Prop :=
  ∀ h : ℤ, ¬ (b : ℤ) ∣ h → ∀ K : ℕ, 1 ≤ K →
    Tendsto (fun X => logMean (digitTruncPhase b h K) X) atTop (𝓝 0)

/-- **REOPEN CONDITION for the log rung of `G4_b`.**  The same correlation with the depth `K(X)`
growing fast enough that the discarded digits (mass `≍ b^{-K}·log log X`) are negligible, and no
faster than `b^K ≤ log X`.  Tao–Teräväinen give each fixed `K` with no uniformity in `K`; this asks
for exactly that uniformity.  Open. -/
def GrowingDepthLogElliott (b : ℕ) : Prop :=
  ∀ h : ℤ, ¬ (b : ℤ) ∣ h → ∀ K : ℕ → ℕ,
    (∀ᶠ X : ℕ in atTop, Real.log (Real.log X) ^ 2 ≤ (b : ℝ) ^ K X) →
    (∀ᶠ X : ℕ in atTop, (b : ℝ) ^ K X ≤ Real.log X) →
    Tendsto (fun X => logMean (digitTruncPhase b h (K X)) X) atTop (𝓝 0)

/-! ## 4. Prior art: log word frequencies of a carry-free unconstructed constant -/

/-- **Tao–Teräväinen 2019** (Duke Math. J. 168, arXiv:1708.02610; abstract: "the conjectured
logarithmic density of all sign patterns of the Liouville function of length up to three").
Every pattern `ε ∈ {±1}³` of `(λ(n+1), λ(n+2), λ(n+3))` has logarithmic density `1/8`; here
`λ(m) = 1 ↔ Ω(m)` even, and the weight is `1/(n+1)` (differs from `1/n` by a summable amount).
So the binary constant `Σ [λ(n) = 1] 2^{-n}`, defined without a construction and carry-free, has
log-averaged 3-word frequencies `1/8`.  Cited, not proved. -/
def TaoTeravainen2019LiouvilleThree : Prop :=
  ∀ ε : Fin 3 → Bool,
    Tendsto (fun N =>
        (∑ n ∈ (range N).filter
            (fun n => ∀ j : Fin 3, (Even (ArithmeticFunction.cardFactors (n + 1 + j)) ↔ ε j = true)),
          (1 : ℝ) / (n + 1)) / ∑ n ∈ range N, (1 : ℝ) / (n + 1))
      atTop (𝓝 (1 / 8))

end

end NormalNumbers.LogCastingOut
