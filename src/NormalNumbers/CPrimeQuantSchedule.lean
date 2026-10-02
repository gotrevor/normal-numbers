/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CPrimeQuantStatement

/-!
# Quantitative C′: the fixed-`u` schedule (build gap 1)

`PrimeModelFamilyGraded` with the band parameter `u_N → ∞` replaced by a **fixed** `u ≥ 10`:
cutoffs `y_j = ⌊N^{u⁻²2⁻ʲ}⌋` (`yG u`), tiers `u_b = u + b` (`uuG P u`); the site count `JG`,
bottom cutoff `yBotG`, Markov thresholds `TG` and `cIdx` are reused from `FamilyGraded`
unchanged.  Mechanical port (2026-10-02); the only mathematical changes:

* `recipSumIoc_yG_le` now reads `S_P(y_j, N) ≤ ε_N·(j + 2 + 2log₂u)` — the root chain with the
  fresh-mass surrogate `ε_N = epsG P N` left explicit (no `ε_N u² ≤ 1`);
* `aG_ge_invL3` takes `u² ≤ L₃N` as a hypothesis (eventually true for fixed `u`).

`windowMean_le_terms` (the pointwise five-term bound) holds for every `u ≥ 10` with **no**
fresh-mass hypothesis.  The limsup bounds of the five terms are the remaining leaves
(`CPrimeQuant.lean`).
-/

set_option linter.unusedSectionVars false

open Finset Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeModel.QuantSchedule

open NormalNumbers.PrimeModel.FamilyGraded

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel.Params NormalNumbers.PrimeModel.KMT
open NormalNumbers.PrimeModel.Family NormalNumbers.PrimeModel.FamilyIter
open NormalNumbers.PrimeModel.SqrtFresh NormalNumbers.PrimeModel.BlockSieve
open NormalNumbers.PrimeModel.PhaseFactor NormalNumbers.PrimeModel.DensityMass

variable (P : ℕ → Prop) [DecidablePred P] (u : ℕ)
include P u

/-! ## The schedule -/

/-- The top cutoff exponent `a_N = u_N^{−2}`. -/
noncomputable def aG (N : ℕ) : ℝ := 1 / ((u : ℝ)) ^ 2

/-- The site cutoffs `y_j = ⌊N^{a_N 2^{−j}}⌋`. -/
noncomputable def yG (N j : ℕ) : ℕ := ⌊(N : ℝ) ^ (aG u N * (1 / 2) ^ j)⌋₊

/-- The level count of the dyadic block family, `L_N = ⌊log₂ log₂ y_{J−1}⌋` clipped at `2`.
It must be read off the **bottom site cutoff** `y_{J−1}`, not off `yBotG`: admissibility pins
`L` from both sides — `2^L ≤ log₂ y_{J−1}` (else some band's dyadic chain drops below `2`) and
`2^{L+1} > log₂ y_{J−1}` (else the bottom band's chain never descends to `2J`).  `yBotG` is far
below `y_{J−1}` when the `min` in `JG` is taken at the mass branch, and the second clause then
fails; this is the one place where the uniform lower end cannot be used. -/
noncomputable def LG (N : ℕ) : ℕ :=
  max 2 ⌊Real.log (Real.log (yG u N (JG P N - 1)) / Real.log 2) / Real.log 2⌋₊

/-- The band floors: `lo b = y_{b+1}`, and `2J` on the bottom band. -/
noncomputable def loG (N : ℕ) : Fin (JG P N) → ℕ :=
  fun b => if (b : ℕ) + 1 < JG P N then yG u N ((b : ℕ) + 1) else 2 * JG P N

/-- The graded tier weights `u_b = u_N + b`: this is what removes the factor `J` from E4b. -/
noncomputable def uuG (N : ℕ) : Fin (JG P N) → ℕ := fun b => u + (b : ℕ)

/-! ## The bottom cutoff diverges -/

omit P u in
/-- `2 log t ≤ t^{3/10}` eventually. -/
private theorem two_log_le_rpow : ∀ᶠ t : ℝ in atTop, 2 * Real.log t ≤ t ^ (3 / 10 : ℝ) := by
  have h := tendsto_log_div_rpow (r := (3 / 10 : ℝ)) (by norm_num)
  filter_upwards [h.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
    eventually_gt_atTop (0 : ℝ)] with t ht htp
  have hp : (0 : ℝ) < t ^ (3 / 10 : ℝ) := Real.rpow_pos_of_pos htp _
  rw [div_lt_iff₀ hp] at ht
  linarith

/-! ## The fresh-mass surrogate -/




/-! ## Schedule facts used by the term estimates -/

theorem JG_le_L3 : ∀ᶠ N : ℕ in atTop, (JG P N : ℝ) ≤ L3 N := by
  filter_upwards [L3_tendsto.eventually_ge_atTop 0] with N hL
  have h2 : ((J1 N : ℕ) : ℝ) ≤ L3 N := Nat.floor_le (by linarith)
  have h3 : (JG P N : ℝ) ≤ ((J1 N : ℕ) : ℝ) := by exact_mod_cast JG_le_J1 P N
  linarith


theorem aG_pos {N : ℕ} (hu : 1 ≤ u) : 0 < aG u N := by
  have : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  rw [aG]; positivity

theorem aG_ge_invL3 {N : ℕ} (hL3 : 0 < L3 N) (huL : (u : ℝ) ^ 2 ≤ L3 N) (hu : 1 ≤ u) : 1 / L3 N ≤ aG u N := by
  have hu1 : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  rw [aG]
  exact one_div_le_one_div_of_le (by nlinarith) huL

/-- Every site cutoff dominates the bottom cutoff — the uniform lower end of the schedule. -/
theorem yBotG_le_yG_nat (hu : 10 ≤ u) : ∀ᶠ N : ℕ in atTop,
    ∀ j : ℕ, j ≤ J1 N → yBotG N ≤ yG u N j := by
  filter_upwards [L3_tendsto.eventually_gt_atTop (0 : ℝ),
    Eventually.of_forall (fun _ => (by omega : 1 ≤ u)),
    eventually_ge_atTop 1, L3_tendsto.eventually_ge_atTop ((u : ℝ) ^ 2)] with N hL3 hu hN huL j hj
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hexp : aMinG N ≤ aG u N * (1 / 2) ^ (j : ℕ) := by
    rw [aMinG]
    have h1 : (1 / L3 N) * (1 / 2 : ℝ) ^ (J1 N) ≤ aG u N * (1 / 2 : ℝ) ^ (J1 N) :=
      mul_le_mul_of_nonneg_right (aG_ge_invL3 P u hL3 huL hu) (by positivity)
    have h2 : (aG u N) * (1 / 2 : ℝ) ^ (J1 N) ≤ aG u N * (1 / 2 : ℝ) ^ (j : ℕ) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj) (aG_pos P u hu).le
    linarith
  exact Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hN1 hexp)

theorem yBotG_le_yG (hu : 10 ≤ u) : ∀ᶠ N : ℕ in atTop,
    ∀ j : Fin (JG P N), yBotG N ≤ yG u N (j : ℕ) := by
  filter_upwards [yBotG_le_yG_nat P u hu] with N h j
  exact h (j : ℕ) (le_trans (le_of_lt j.2) (JG_le_J1 P N))

/-- **The short root chain at site `j`.**  `log N / log y_j ≤ 2^{j+1} u_N²`, so the chain from
`y_j` up to `N` needs at most `j + 2 + 2 log₂ u_N` halvings, and with `ε_N ≤ u_N^{−2}` the fresh
mass above `y_j` is at most `(j + 2 + 2 log₂ u_N)/u_N²`.  This is the estimate that the BOTTOM
cutoff cannot supply (there the chain is `≍ L₃N` long); it is available at every site because the
site exponents are `a_N 2^{-j}` with `a_N = u_N^{-2}`. -/
theorem recipSumIoc_yG_le (hu : 10 ≤ u) : ∀ᶠ N : ℕ in atTop,
    ∀ j : ℕ, j ≤ J1 N →
      recipSumIoc P (yG u N j) N
        ≤ epsG P N * ((j : ℝ) + 2 + 2 * Real.log (u : ℝ) / Real.log 2) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [yBotG_le_yG_nat P u hu, yBotG_tendsto.eventually_ge_atTop 4,
    Eventually.of_forall (fun _ => (by omega : 2 ≤ u)), eventually_ge_atTop 16]
    with N hyb hy4 hu2 hN16 j hj
  have hu2r : (2 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu2
  have hNr : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN16
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN : (0 : ℝ) < Real.log N := Real.log_pos (by linarith)
  have hy4' : 4 ≤ yG u N j := le_trans hy4 (hyb j hj)
  have hy4r : (4 : ℝ) ≤ ((yG u N j : ℕ) : ℝ) := by exact_mod_cast hy4'
  -- the real cutoff `x` and its logarithm `A`
  set e : ℝ := aG u N * (1 / 2) ^ j with hedef
  have haG : aG u N = 1 / (u : ℝ) ^ 2 := rfl
  have hapos : (0 : ℝ) < aG u N := by rw [haG]; positivity
  have hepos : (0 : ℝ) < e := by rw [hedef]; positivity
  set x : ℝ := (N : ℝ) ^ e with hxdef
  have hxpos : (0 : ℝ) < x := Real.rpow_pos_of_pos hN0 _
  have hyx : ((yG u N j : ℕ) : ℝ) ≤ x := Nat.floor_le hxpos.le
  have hxhalf : x / 2 ≤ ((yG u N j : ℕ) : ℝ) := by
    have h1 : x - 1 < ((yG u N j : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one x
      simpa [yG, hxdef, hedef] using (by linarith [Nat.lt_succ_floor x, Nat.lt_floor_add_one x] :
        x - 1 < ((⌊x⌋₊ : ℕ) : ℝ))
    have h2 : (2 : ℝ) ≤ x := by linarith [hy4r, hyx]
    linarith
  set A : ℝ := e * Real.log N with hAdef
  have hlogx : Real.log x = A := by rw [hxdef, Real.log_rpow hN0, hAdef]
  have hlogy_le : Real.log (yG u N j) ≤ A := by
    rw [← hlogx]; exact Real.log_le_log (by linarith) hyx
  have hlogy_ge : A - Real.log 2 ≤ Real.log (yG u N j) := by
    have h := Real.log_le_log (by positivity) hxhalf
    rw [Real.log_div (ne_of_gt hxpos) (by norm_num), hlogx] at h
    linarith
  have hlog4 : Real.log 4 ≤ Real.log (yG u N j) := Real.log_le_log (by norm_num) hy4r
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hApos : 2 * Real.log 2 ≤ A := by linarith
  have hlogy_half : A / 2 ≤ Real.log (yG u N j) := by linarith
  have hlogypos : (0 : ℝ) < Real.log (yG u N j) := by linarith
  -- `y_j < N`
  have hyN : yG u N j < N := by
    have he4 : e ≤ 1 / 4 := by
      rw [hedef, haG]
      have h1 : ((1 : ℝ) / 2) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have h2 : (4 : ℝ) ≤ (u : ℝ) ^ 2 := by nlinarith
      have : (1 : ℝ) / (u : ℝ) ^ 2 ≤ 1 / 4 :=
        one_div_le_one_div_of_le (by norm_num) h2
      nlinarith [pow_nonneg (show (0:ℝ) ≤ 1/2 by norm_num) j,
        one_div_nonneg.mpr (show (0:ℝ) ≤ (u : ℝ) ^ 2 by positivity)]
    have hxlt : x < (N : ℝ) := by
      have h1 : x ≤ (N : ℝ) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) he4
      have h2 : (N : ℝ) ^ ((1 : ℝ) / 4) < (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
      rw [Real.rpow_one] at h2
      linarith
    have : ((yG u N j : ℕ) : ℝ) < (N : ℝ) := lt_of_le_of_lt hyx hxlt
    exact_mod_cast this
  -- the chain
  have hchain := SqrtFresh.recipSumIoc_le_rootChain P (ρ := epsG P N) (epsG_nonneg P N)
    (Z := yBotG N) (y := yG u N j) (M := N) (by omega) (hyb j hj) hyN
    (fun q hq => recipSumIoc_le_epsG P N hy4 hq)
  -- the chain length
  set K : ℕ := ⌈Real.log (Real.log N / Real.log (yG u N j)) / Real.log 2⌉₊ with hKdef
  set B : ℝ := ((j : ℝ) + 1) + 2 * Real.log (u : ℝ) / Real.log 2 with hBdef
  have hBnn : (0 : ℝ) ≤ B := by
    have : (0 : ℝ) ≤ Real.log (u : ℝ) := Real.log_nonneg (by linarith)
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    rw [hBdef]; positivity
  have hratio : Real.log N / Real.log (yG u N j) ≤ 2 * 2 ^ j * (u : ℝ) ^ 2 := by
    rw [div_le_iff₀ hlogypos]
    have h1 : A / 2 ≤ Real.log (yG u N j) := hlogy_half
    have hA : A = Real.log N / (2 ^ j * (u : ℝ) ^ 2) := by
      rw [hAdef, hedef, haG]
      have h2 : ((1 : ℝ) / 2) ^ j = 1 / 2 ^ j := by rw [div_pow, one_pow]
      rw [h2]
      field_simp
    have hden : (0 : ℝ) < 2 ^ j * (u : ℝ) ^ 2 := by positivity
    rw [hA, div_div, div_le_iff₀ (by positivity)] at h1
    linarith
  have hKle : (K : ℝ) ≤ B + 1 := by
    have hpos : (0 : ℝ) < Real.log N / Real.log (yG u N j) := by positivity
    have hlogratio : Real.log (Real.log N / Real.log (yG u N j))
        ≤ Real.log (2 * 2 ^ j * (u : ℝ) ^ 2) := Real.log_le_log hpos hratio
    have heval : Real.log (2 * 2 ^ j * (u : ℝ) ^ 2)
        = ((j : ℝ) + 1) * Real.log 2 + 2 * Real.log (u : ℝ) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
        Real.log_pow, Real.log_pow]
      push_cast; ring
    have ht : Real.log (Real.log N / Real.log (yG u N j)) / Real.log 2 ≤ B := by
      rw [div_le_iff₀ hlog2, hBdef]
      rw [heval] at hlogratio
      have : 2 * Real.log (u : ℝ) / Real.log 2 * Real.log 2
          = 2 * Real.log (u : ℝ) := by field_simp
      nlinarith [hlogratio, this]
    have hyle : Real.log (yG u N j) ≤ Real.log N :=
      Real.log_le_log (by linarith) (by exact_mod_cast hyN.le)
    have h0t : (0 : ℝ) ≤ Real.log (Real.log N / Real.log (yG u N j)) / Real.log 2 := by
      refine div_nonneg (Real.log_nonneg ?_) hlog2.le
      rw [le_div_iff₀ hlogypos]
      linarith
    have hKlt : (K : ℝ)
        < Real.log (Real.log N / Real.log (yG u N j)) / Real.log 2 + 1 := by
      rw [hKdef]; exact Nat.ceil_lt_add_one h0t
    linarith
  -- assemble
  have hfinal : recipSumIoc P (yG u N j) N ≤ epsG P N * (B + 1) := by
    refine hchain.trans ?_
    exact mul_le_mul_of_nonneg_left hKle (epsG_nonneg P N)
  have hBC : B + 1 = (j : ℝ) + 2 + 2 * Real.log (u : ℝ) / Real.log 2 := by
    rw [hBdef]; ring
  rw [hBC] at hfinal
  exact hfinal

/-! ### Two elementary numeric lemmas -/

omit P u in
private theorem one_add_div_four_sq_le (j : ℕ) : (1 + (j : ℝ) / 4) ^ 2 ≤ 2 ^ j := by
  induction j with
  | zero => norm_num
  | succ n ih =>
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    push_cast
    rw [show ((2 : ℝ)) ^ (n + 1) = 2 * 2 ^ n from by ring]
    nlinarith [ih, hn, sq_nonneg ((n : ℝ) / 4)]

omit P u in
private theorem one_add_div_four_le_sqrt (j : ℕ) : 1 + (j : ℝ) / 4 ≤ Real.sqrt (2 ^ j) := by
  have h := Real.sqrt_le_sqrt (one_add_div_four_sq_le j)
  rwa [Real.sqrt_sq (by positivity)] at h

omit P u in
private theorem geom_sum_le_two {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ i ≤ 2 := by
  have hg := geom_sum_mul r n
  have hpow : (0 : ℝ) ≤ r ^ n := by positivity
  have hs : (0 : ℝ) ≤ ∑ i ∈ Finset.range n, r ^ i :=
    Finset.sum_nonneg fun i _ => by positivity
  nlinarith [hg, hpow, hs]

/-! ## The five terms -/

/-- E1, the per-site transfer error. -/
noncomputable def termE1 (h : ℤ) (N : ℕ) : ℝ :=
  ∑ j : Fin (JG P N), siteBudget h j.val
    * (2 * recipSumIoc P (yG u N j) N + ((JG P N : ℕ) : ℝ) / N)

/-- E4a, the discarded radical mass, at the sharp per-site exponent. -/
noncomputable def termE4a (N : ℕ) : ℝ :=
  2 * ∑ j : Fin (JG P N),
    Real.exp 20 / (TG N j) ^ (1 / (2 * Real.log (yG u N j)))

/-- E4b, the sieve defect. -/
noncomputable def termE4b (N : ℕ) : ℝ :=
  2 * (0.3 * ∑ b : Fin (JG P N), Real.exp (-(uuG P u N b : ℝ)))

/-- E4c, the CRT remainder. -/
noncomputable def termE4c (N : ℕ) : ℝ :=
  2 * ((primorial (2 * JG P N) : ℕ) : ℝ) * (∏ j : Fin (JG P N), (Nat.floor (TG N j) : ℝ))
    * (gradedLevel Finset.univ (fun b : Fin (JG P N) => (b : ℕ) + 1) (uuG P u N)
        (fun b : Fin (JG P N) => ((yG u N b : ℕ) : ℝ))) ^ 2 / N

/-- E5, the phase contraction, at the **near-top** cutoff `y_{c(h)}`. -/
noncomputable def termE5 (h : ℤ) (N : ℕ) : ℝ :=
  Real.exp (2 * JG P N)
    * Real.exp (- ∑ p ∈ (midPrimes P (2 * JG P N) (yG u N 0)).filter
        (fun p => p ≤ yG u N (cIdx P h N)), (1 : ℝ) / (p : ℝ))

/-- The site cutoffs decrease with the index. -/
theorem yG_antitone {N : ℕ} (hN : 1 ≤ N) {i j : ℕ} (hij : i ≤ j) :
    yG u N j ≤ yG u N i := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  refine Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hN1 ?_)
  have hpow : ((1 : ℝ) / 2) ^ j ≤ ((1 : ℝ) / 2) ^ i :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
  have ha : (0 : ℝ) ≤ aG u N := by rw [aG]; positivity
  exact mul_le_mul_of_nonneg_left hpow ha


/-! ## The five limits (open leaves) -/

omit P u in
/-- **Open leaf G5c-2 (E1).**  `∑_j a_j (2 S_P(y_j, N) + J/N) → 0`: the root chain
(`SqrtFresh.recipSumIoc_le_rootChain`) gives `S_P(y_j, N) ≤ ε_N (j + 2 log₂ u_N + 1)`, and
`u_N ≤ ε_N^{−1/2}` makes `ε_N log u_N → 0`. -/
private theorem two_add_le_two_pow (j : ℕ) : ((j : ℝ) + 2) ≤ 2 ^ (j + 1) := by
  induction j with
  | zero => norm_num
  | succ n ih =>
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
    push_cast
    rw [show ((2 : ℝ)) ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) from by ring]
    push_cast at ih
    linarith

omit P u in
private theorem sum_half_succ_le (k : ℕ) : ∑ j ∈ Finset.range k, ((1 : ℝ) / 2) ^ (j + 1) ≤ 1 := by
  have h := sum_geometric_two_le k
  calc ∑ j ∈ Finset.range k, ((1 : ℝ) / 2) ^ (j + 1)
      = (1 / 2) * ∑ j ∈ Finset.range k, ((1 : ℝ) / 2) ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [pow_succ]; ring
    _ ≤ (1 / 2) * 2 := by linarith
    _ = 1 := by norm_num

omit P u in
/-- The site weights absorb the growing chain length: `∑_j 4^{−j−1}(j + 2 + 2L) ≤ 1 + 2L`. -/
private theorem sum_quarter_weight_le {L : ℝ} (hL : 0 ≤ L) (k : ℕ) :
    ∑ j ∈ Finset.range k, ((1 : ℝ) / 4) ^ (j + 1) * ((j : ℝ) + 2 + 2 * L) ≤ 1 + 2 * L := by
  have hterm : ∀ j ∈ Finset.range k,
      ((1 : ℝ) / 4) ^ (j + 1) * ((j : ℝ) + 2 + 2 * L) ≤ (1 + 2 * L) * ((1 : ℝ) / 2) ^ (j + 1) := by
    intro j _
    have hq : ((1 : ℝ) / 4) ^ (j + 1) = ((1 : ℝ) / 2) ^ (j + 1) * ((1 : ℝ) / 2) ^ (j + 1) := by
      rw [← mul_pow]; norm_num
    have hp : (0 : ℝ) < ((1 : ℝ) / 2) ^ (j + 1) := by positivity
    have hinv : ((1 : ℝ) / 2) ^ (j + 1) * (2 : ℝ) ^ (j + 1) = 1 := by
      rw [← mul_pow]; norm_num
    have h1 : ((1 : ℝ) / 4) ^ (j + 1) * ((j : ℝ) + 2)
        ≤ ((1 : ℝ) / 2) ^ (j + 1) := by
      rw [hq]
      calc ((1 : ℝ) / 2) ^ (j + 1) * ((1 : ℝ) / 2) ^ (j + 1) * ((j : ℝ) + 2)
          ≤ ((1 : ℝ) / 2) ^ (j + 1) * ((1 : ℝ) / 2) ^ (j + 1) * 2 ^ (j + 1) :=
            mul_le_mul_of_nonneg_left (two_add_le_two_pow j) (by positivity)
        _ = ((1 : ℝ) / 2) ^ (j + 1) := by rw [mul_assoc, hinv, mul_one]
    have h2 : ((1 : ℝ) / 4) ^ (j + 1) * (2 * L) ≤ ((1 : ℝ) / 2) ^ (j + 1) * (2 * L) := by
      refine mul_le_mul_of_nonneg_right ?_ (by linarith)
      rw [hq]
      nlinarith [hp, pow_le_one₀ (show (0:ℝ) ≤ 1/2 by norm_num) (show (1:ℝ)/2 ≤ 1 by norm_num)
        (n := j + 1)]
    nlinarith [h1, h2]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  nlinarith [sum_half_succ_le k, hL,
    Finset.sum_nonneg (fun j (_ : j ∈ Finset.range k) =>
      pow_nonneg (show (0:ℝ) ≤ 1/2 by norm_num) (j + 1))]

/-- `J_N / N → 0`. -/
theorem JG_div_tendsto (hP : DivergentRecip P) :
    Tendsto (fun N : ℕ => (JG P N : ℝ) / N) atTop (𝓝 0) := by
  have hlogdiv : Tendsto (fun N : ℕ => Real.log N / (N : ℝ)) atTop (𝓝 0) := by
    have h1 := (tendsto_log_div_rpow (r := (1 : ℝ)) (by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Function.comp_def] using h1
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hlogdiv
  · positivity
  filter_upwards [JG_le_L3 P u, L2_tendsto.eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop 3] with N hJ hL2 hN3
  have hNr : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hlogN : (0 : ℝ) < Real.log N := Real.log_pos (by linarith)
  have hL2le : L2 N ≤ Real.log N := by
    have h := Real.log_le_sub_one_of_pos hlogN
    have : L2 N = Real.log (Real.log N) := rfl
    rw [this]; linarith
  have hL3le : L3 N ≤ L2 N := by
    rw [L3_eq N]
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < L2 N by linarith)
    linarith
  exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg N)

/-- **Open leaf G5c-3 (E4a).**  `log T_j / (2 log y_j) = 2^{j/2} u_N²/32`, so the sum is
`2 e^{20} ∑_j exp(−2^{j/2} u_N²/32) → 0`.  This is the term the ungraded Markov range made
diverge like `J e^{20}`. -/
theorem termE4a_le (hu : 10 ≤ u) : ∀ᶠ N : ℕ in atTop,
    termE4a P u N ≤ 4 * Real.exp 20 * Real.exp (-((u : ℝ) ^ 2 / 32)) := by
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    have h1 : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
    have h2 := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at h2
  filter_upwards [yBotG_le_yG P u hu, yBotG_tendsto.eventually_ge_atTop 3,
    Eventually.of_forall (fun _ => (by omega : 10 ≤ u)),
    L3_tendsto.eventually_gt_atTop (0 : ℝ), eventually_ge_atTop 3] with N hyb hyb3 hu hL3 hN3
  have hNr : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hlogN : (1 : ℝ) ≤ Real.log N := le_trans hlog3 (Real.log_le_log (by norm_num) hNr)
  have hu1 : 1 ≤ u := by omega
  have hu10' : (10 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have hapos : 0 < aG u N := aG_pos P u hu1
  have haGval : aG u N = 1 / (u : ℝ) ^ 2 := rfl
  have hu10 : (10 : ℝ) ≤ u := hu10'
  -- the geometric ratio
  set r : ℝ := Real.exp (-(u ^ 2 / 128)) with hrdef
  have hr0 : (0 : ℝ) ≤ r := (Real.exp_pos _).le
  have hrhalf : r ≤ 1 / 2 := by
    rw [hrdef, show (1 : ℝ) / 2 = Real.exp (Real.log (1 / 2)) from
      (Real.exp_log (by norm_num)).symm]
    refine Real.exp_le_exp.mpr ?_
    have hl2 : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
      rw [Real.log_div one_ne_zero two_ne_zero, Real.log_one]; ring
    have hlog2 : Real.log 2 ≤ 7 / 10 := le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num))
    rw [hl2]
    nlinarith
  -- the per-site bound
  have hterm : ∀ j : Fin (JG P N),
      Real.exp 20 / (TG N (j : ℕ)) ^ (1 / (2 * Real.log (yG u N (j : ℕ))))
        ≤ Real.exp 20 * Real.exp (-(u ^ 2 / 32)) * r ^ (j : ℕ) := by
    intro j
    have hy3 : 3 ≤ yG u N (j : ℕ) := le_trans hyb3 (hyb j)
    have hy3r : (3 : ℝ) ≤ ((yG u N (j : ℕ) : ℕ) : ℝ) := by exact_mod_cast hy3
    have hylog : (1 : ℝ) ≤ Real.log (yG u N (j : ℕ)) :=
      le_trans hlog3 (Real.log_le_log (by norm_num) hy3r)
    -- upper bound on `log y_j`
    set A : ℝ := aG u N * (1 / 2) ^ (j : ℕ) * Real.log N with hAdef
    have hyub : Real.log (yG u N (j : ℕ)) ≤ A := by
      have hfl : ((yG u N (j : ℕ) : ℕ) : ℝ) ≤ (N : ℝ) ^ (aG u N * (1 / 2) ^ (j : ℕ)) :=
        Nat.floor_le (Real.rpow_nonneg hN0.le _)
      have := Real.log_le_log (by linarith) hfl
      rwa [Real.log_rpow hN0, ← hAdef] at this
    have hA1 : (1 : ℝ) ≤ A := le_trans hylog hyub
    -- the Markov threshold is ≥ 1 and the exponent comparison
    have hTexp : (0 : ℝ) ≤ (1 / 16) * Real.sqrt ((1 / 2) ^ (j : ℕ)) := by positivity
    have hT1 : (1 : ℝ) ≤ TG N (j : ℕ) := Real.one_le_rpow hN1 hTexp
    have hexpo : 1 / (2 * A) ≤ 1 / (2 * Real.log (yG u N (j : ℕ))) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    have hTmono : (TG N (j : ℕ)) ^ (1 / (2 * A))
        ≤ (TG N (j : ℕ)) ^ (1 / (2 * Real.log (yG u N (j : ℕ)))) :=
      Real.rpow_le_rpow_of_exponent_le hT1 hexpo
    -- evaluate `T_j^{1/(2A)}`
    have hp : (0 : ℝ) < (2 : ℝ) ^ (j : ℕ) := by positivity
    have hinv : ((1 : ℝ) / 2) ^ (j : ℕ) = ((2 : ℝ) ^ (j : ℕ))⁻¹ := by
      rw [div_pow, one_pow, ← one_div, one_div]
    have hsqrt : Real.sqrt ((1 / 2 : ℝ) ^ (j : ℕ)) * 2 ^ (j : ℕ) = Real.sqrt (2 ^ (j : ℕ)) := by
      have hsp : (0 : ℝ) < Real.sqrt ((2 : ℝ) ^ (j : ℕ)) := Real.sqrt_pos.mpr hp
      have hsq : Real.sqrt ((2 : ℝ) ^ (j : ℕ)) * Real.sqrt ((2 : ℝ) ^ (j : ℕ)) = 2 ^ (j : ℕ) :=
        Real.mul_self_sqrt hp.le
      have hrw : Real.sqrt (((2 : ℝ) ^ (j : ℕ))⁻¹) * 2 ^ (j : ℕ)
          = (Real.sqrt ((2 : ℝ) ^ (j : ℕ)))⁻¹
            * (Real.sqrt ((2 : ℝ) ^ (j : ℕ)) * Real.sqrt ((2 : ℝ) ^ (j : ℕ))) := by
        rw [Real.sqrt_inv, hsq]
      rw [hinv, hrw, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hsp), one_mul]
    have hval : (TG N (j : ℕ)) ^ (1 / (2 * A))
        = Real.exp (u ^ 2 * Real.sqrt (2 ^ (j : ℕ)) / 32) := by
      rw [TG, ← Real.rpow_mul hN0.le, Real.rpow_def_of_pos hN0]
      congr 1
      rw [hAdef, haGval, ← hsqrt, hinv]
      have hu0 : (0 : ℝ) < u := by linarith
      have hlogNpos : (0 : ℝ) < Real.log N := by linarith
      field_simp
      ring
    -- assemble
    have hlow : Real.exp (u ^ 2 * (1 + (j : ℕ) / 4) / 32)
        ≤ (TG N (j : ℕ)) ^ (1 / (2 * Real.log (yG u N (j : ℕ)))) := by
      refine le_trans ?_ hTmono
      rw [hval]
      refine Real.exp_le_exp.mpr ?_
      have := one_add_div_four_le_sqrt (j : ℕ)
      nlinarith [sq_nonneg u]
    have hpos : (0 : ℝ) < Real.exp (u ^ 2 * (1 + (j : ℕ) / 4) / 32) := Real.exp_pos _
    have hstep : Real.exp 20 / (TG N (j : ℕ)) ^ (1 / (2 * Real.log (yG u N (j : ℕ))))
        ≤ Real.exp 20 / Real.exp (u ^ 2 * (1 + (j : ℕ) / 4) / 32) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le hpos hlow
    refine hstep.trans (le_of_eq ?_)
    rw [hrdef, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_sub]
    ring_nf
    rw [Real.exp_add]
  -- sum up
  rw [termE4a]
  have hsum : ∑ j : Fin (JG P N),
      Real.exp 20 / (TG N (j : ℕ)) ^ (1 / (2 * Real.log (yG u N (j : ℕ))))
      ≤ ∑ j : Fin (JG P N), (Real.exp 20 * Real.exp (-(u ^ 2 / 32))) * r ^ (j : ℕ) :=
    Finset.sum_le_sum fun j _ => by simpa [mul_assoc] using hterm j
  have hgeo : ∑ j : Fin (JG P N), (Real.exp 20 * Real.exp (-(u ^ 2 / 32))) * r ^ (j : ℕ)
      ≤ (Real.exp 20 * Real.exp (-(u ^ 2 / 32))) * 2 := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Fin.sum_univ_eq_sum_range (fun i => r ^ i) (JG P N)]
    exact geom_sum_le_two hr0 hrhalf _
  nlinarith [hsum, hgeo, Real.exp_pos (20 : ℝ), Real.exp_pos (-(u ^ 2 / 32))]

/-- **Open leaf G5c-4 (E4b).**  `∑_b e^{−(u_N + b)} ≤ 1.6 e^{−u_N} → 0` — no `J` factor,
because the tier weights are graded. -/
theorem sum_uuG_le (N : ℕ) :
    ∑ b : Fin (JG P N), Real.exp (-(uuG P u N b : ℝ))
      ≤ 1.6 * Real.exp (-(u : ℝ)) := by
  have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hr0 : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
  have hrval : Real.exp (-1) < 3 / 8 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have hr1 : Real.exp (-1) < 1 := by linarith
  have hsplit : ∑ b : Fin (JG P N), Real.exp (-(uuG P u N b : ℝ))
      = Real.exp (-(u : ℝ)) * ∑ b ∈ Finset.range (JG P N), (Real.exp (-1)) ^ b := by
    rw [Finset.mul_sum]
    rw [show (∑ b : Fin (JG P N), Real.exp (-(uuG P u N b : ℝ)))
        = ∑ b : Fin (JG P N), Real.exp (-((u + (b : ℕ) : ℕ) : ℝ)) from rfl,
      Fin.sum_univ_eq_sum_range (fun i => Real.exp (-((u + i : ℕ) : ℝ))) (JG P N)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    push_cast
    ring_nf
  rw [hsplit]
  have hgeom : ∑ b ∈ Finset.range (JG P N), (Real.exp (-1)) ^ b ≤ 1.6 := by
    have hg := geom_sum_mul (Real.exp (-1)) (JG P N)
    have hpow : (0 : ℝ) ≤ (Real.exp (-1)) ^ (JG P N) := by positivity
    have hsum0 : (0 : ℝ) ≤ ∑ b ∈ Finset.range (JG P N), (Real.exp (-1)) ^ b :=
      Finset.sum_nonneg fun b _ => by positivity
    nlinarith [hg, hpow, hsum0, hrval]
  calc Real.exp (-(u : ℝ)) * ∑ b ∈ Finset.range (JG P N), (Real.exp (-1)) ^ b
      ≤ Real.exp (-(u : ℝ)) * 1.6 :=
        mul_le_mul_of_nonneg_left hgeom (Real.exp_pos _).le
    _ = 1.6 * Real.exp (-(u : ℝ)) := by ring

/-! ### E4c: the CRT remainder -/

omit P u in
private theorem sqrt_half_pow_le (j : ℕ) :
    Real.sqrt (((1 : ℝ) / 2) ^ j) ≤ ((3 : ℝ) / 4) ^ j := by
  have hsq : (((3 : ℝ) / 4) ^ j) ^ 2 = ((9 : ℝ) / 16) ^ j := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [show ((3 : ℝ) / 4) ^ j = Real.sqrt ((((3 : ℝ) / 4) ^ j) ^ 2) from
    (Real.sqrt_sq (by positivity)).symm]
  refine Real.sqrt_le_sqrt ?_
  rw [hsq]
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) j

omit P u in
private theorem add_two_le_three_half_pow (b : ℕ) : ((b : ℝ) + 2) ≤ 3 * ((3 : ℝ) / 2) ^ b := by
  induction b with
  | zero => norm_num
  | succ n ih =>
    have hp : (0 : ℝ) < ((3 : ℝ) / 2) ^ n := by positivity
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    push_cast
    rw [pow_succ]
    nlinarith

omit P u in
private theorem sum_three_quarter_le (k : ℕ) :
    ∑ j ∈ Finset.range k, ((3 : ℝ) / 4) ^ j ≤ 4 := by
  have hg := geom_sum_mul ((3 : ℝ) / 4) k
  have hpow : (0 : ℝ) ≤ ((3 : ℝ) / 4) ^ k := by positivity
  have hs : (0 : ℝ) ≤ ∑ j ∈ Finset.range k, ((3 : ℝ) / 4) ^ j :=
    Finset.sum_nonneg fun j _ => by positivity
  nlinarith [hg, hpow, hs]

omit P u in
private theorem sum_succ_half_le (k : ℕ) :
    ∑ b ∈ Finset.range k, (((b : ℝ) + 1) * ((1 : ℝ) / 2) ^ b) ≤ 12 := by
  have hterm : ∀ b ∈ Finset.range k,
      ((b : ℝ) + 1) * ((1 : ℝ) / 2) ^ b ≤ 3 * ((3 : ℝ) / 4) ^ b := by
    intro b _
    have h1 := add_two_le_three_half_pow b
    have h2 : (0 : ℝ) < ((1 : ℝ) / 2) ^ b := by positivity
    have h3 : ((3 : ℝ) / 2) ^ b * ((1 : ℝ) / 2) ^ b = ((3 : ℝ) / 4) ^ b := by
      rw [← mul_pow]; norm_num
    nlinarith
  calc ∑ b ∈ Finset.range k, (((b : ℝ) + 1) * ((1 : ℝ) / 2) ^ b)
      ≤ ∑ b ∈ Finset.range k, 3 * ((3 : ℝ) / 4) ^ b := Finset.sum_le_sum hterm
    _ = 3 * ∑ b ∈ Finset.range k, ((3 : ℝ) / 4) ^ b := by rw [Finset.mul_sum]
    _ ≤ 3 * 4 := mul_le_mul_of_nonneg_left (sum_three_quarter_le k) (by norm_num)
    _ = 12 := by norm_num

omit P u in
/-- `log N ≥ (1 + L₂N/2)²`, i.e. `log N` dwarfs every polynomial in `L₂N`.  (From
`log N = exp(L₂N) = exp(L₂N/2)²` and `1 + x ≤ exp x`.) -/
private theorem log_ge_sq {N : ℕ} (hlogN : 0 < Real.log (N : ℝ)) (hL2 : 0 ≤ L2 N) :
    (1 + L2 N / 2) ^ 2 ≤ Real.log (N : ℝ) := by
  have h1 : L2 N / 2 + 1 ≤ Real.exp (L2 N / 2) := Real.add_one_le_exp _
  have h2 : Real.exp (L2 N) = (Real.exp (L2 N / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (L2 N) = Real.log (N : ℝ) := by
    simp only [L2]; exact Real.exp_log hlogN
  have h4 : (1 + L2 N / 2) ^ 2 ≤ (Real.exp (L2 N / 2)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  rw [← h3, h2]
  exact h4

/-! ## Theorem C′ -/

/-! ### E5: the phase contraction at the near-top cutoff -/

/-- Every site cutoff is below `N`: the exponent `a_N 2^{−j}` is at most `1`. -/
theorem yG_le_self (hu : 10 ≤ u) : ∀ᶠ N : ℕ in atTop, ∀ j : ℕ, yG u N j ≤ N := by
  filter_upwards [Eventually.of_forall (fun _ => (by omega : 1 ≤ u)),
    eventually_ge_atTop 1] with N hu hN j
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hu1 : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have husq : (1 : ℝ) ≤ (u : ℝ) ^ 2 := by nlinarith
  have ha1 : aG u N ≤ 1 := by
    rw [aG, div_le_one (by linarith)]; linarith
  have hnn : (0 : ℝ) ≤ aG u N := by rw [aG]; positivity
  have hhalf0 : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ j :=
    pow_nonneg (by norm_num) j
  have hhalf : ((1 : ℝ) / 2) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hexp : aG u N * ((1 : ℝ) / 2) ^ j ≤ 1 := by nlinarith
  have hstep : ((N : ℝ)) ^ (aG u N * ((1 : ℝ) / 2) ^ j) ≤ (N : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 hexp
  rw [Real.rpow_one] at hstep
  have hfl : ⌊((N : ℝ)) ^ (aG u N * ((1 : ℝ) / 2) ^ j)⌋₊ ≤ ⌊(N : ℝ)⌋₊ := Nat.floor_le_floor hstep
  simpa [yG] using hfl

/-- The graded twin of `tail_fresh`: the two-branch argument of the `min` in `JG`. -/
theorem tail_graded (hfm : ∀ᶠ N : ℕ in atTop, recipSumIoc P N (2 * N) ≤ 1)
    (hP : DivergentRecip P) :
    Tendsto (fun N : ℕ => (recipSumLe P (2 * N) + 5 * (JG P N : ℝ) + 12) / (4 : ℝ) ^ JG P N)
      atTop (𝓝 0) := by
  set ρ : ℝ := Real.log 4 - 1 with hρdef
  have hlog4 : 1 < Real.log 4 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  have hf : Tendsto (fun N : ℕ => (13 * (JG P N : ℝ) + 21) / (4 : ℝ) ^ (JG P N))
      atTop (𝓝 0) := by
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 4)
    have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1 : ℝ) < 4)
    have hsum : Tendsto
        (fun n : ℕ => 13 * ((n : ℝ) ^ 1 / (4 : ℝ) ^ n) + 21 * ((n : ℝ) ^ 0 / (4 : ℝ) ^ n))
        atTop (𝓝 0) := by
      simpa using (h1.const_mul (13 : ℝ)).add (h0.const_mul (21 : ℝ))
    refine Tendsto.congr (fun N => ?_) (hsum.comp (JG_tendsto P hP))
    simp only [Function.comp_apply, pow_one, pow_zero]
    ring
  have hgt : Tendsto (fun N : ℕ => 120 * (L2 N) ^ (-ρ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (L2 N) ^ (-ρ)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop hρ0).comp L2_tendsto
      simpa [Function.comp_def] using this
    simpa using h1.const_mul (120 : ℝ)
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ (by simpa using hf.add hgt)
  · have := recipSumLe_nonneg P (2 * N)
    positivity
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500, JG_le_L3 P u,
    yBotG_le_self, hfm] with N hN hL hJle hyN hfm2
  obtain ⟨hu1, hu2, -⟩ := L3_bounds hL
  have ht0 : 0 < L2 N := by linarith
  have hulog : L3 N = Real.log (L2 N) := L3_eq N
  have hrp : (0 : ℝ) < (L2 N) ^ (-ρ) := Real.rpow_pos_of_pos ht0 _
  have hpow0 : (0 : ℝ) < (4 : ℝ) ^ (JG P N) := by positivity
  have hfnn : (0 : ℝ) ≤ (13 * (JG P N : ℝ) + 21) / (4 : ℝ) ^ (JG P N) := by positivity
  have hgnn : (0 : ℝ) ≤ 120 * (L2 N) ^ (-ρ) := by positivity
  rcases le_total (J1 N) (⌊recipSumLe P N / 8⌋₊) with hcase | hcase
  · have hJlow : L3 N - 1 ≤ (JG P N : ℝ) := JG_lower P hcase (by linarith)
    have hpow : (L2 N) ^ Real.log 4 / 4 ≤ (4 : ℝ) ^ (JG P N) := by
      have h1 : (4 : ℝ) ^ (JG P N) = (4 : ℝ) ^ ((JG P N : ℕ) : ℝ) := (Real.rpow_natCast 4 _).symm
      have h2 : (4 : ℝ) ^ (L3 N - 1) ≤ (4 : ℝ) ^ ((JG P N : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have h3 : (4 : ℝ) ^ (L3 N - 1) = (L2 N) ^ Real.log 4 / 4 := by
        rw [Real.rpow_sub (by norm_num), Real.rpow_one]
        congr 1
        rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 4), Real.rpow_def_of_pos ht0, hulog]
        congr 1
        ring
      rw [h1, ← h3]; exact h2
    have hL2two : L2 (2 * N) ≤ L2 N + 1 := by
      have hlogN : 1 < Real.log N := logN_gt_one hN
      have hlog2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
      have hNne : ((N : ℝ)) ≠ 0 := by
        have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        exact ne_of_gt (by linarith)
      have hlog2N : Real.log ((2 * N : ℕ) : ℝ) = Real.log 2 + Real.log N := by
        rw [hcast, Real.log_mul (by norm_num) hNne]
      have hlog2Npos : 0 < Real.log ((2 * N : ℕ) : ℝ) := by rw [hlog2N]; linarith
      have h1 : Real.log ((2 * N : ℕ) : ℝ) ≤ 2 * Real.log N := by rw [hlog2N]; linarith
      have h2 : L2 (2 * N) ≤ Real.log (2 * Real.log N) := Real.log_le_log hlog2Npos h1
      rw [Real.log_mul (by norm_num) (by linarith)] at h2
      have h4 : Real.log (Real.log N) = L2 N := rfl
      linarith [h2, h4.le, h4.ge]
    have hcrude : recipSumLe P (2 * N) ≤ 12 * L2 (2 * N) + 21 :=
      NormalNumbers.PrimeModel.FamilySharp.recipSumLe_le_crude P (by omega)
    have hnum : recipSumLe P (2 * N) + 5 * (JG P N : ℝ) + 12 ≤ 30 * L2 N := by
      have h5 : (JG P N : ℝ) ≤ L3 N := hJle
      linarith
    have h30 : (0 : ℝ) ≤ 30 * L2 N := by linarith
    have hstep : (recipSumLe P (2 * N) + 5 * (JG P N : ℝ) + 12) / (4 : ℝ) ^ (JG P N)
        ≤ (30 * L2 N) / ((L2 N) ^ Real.log 4 / 4) :=
      div_le_div₀ h30 hnum (by positivity) hpow
    have hfin : (30 * L2 N) / ((L2 N) ^ Real.log 4 / 4) = 120 * (L2 N) ^ (-ρ) := by
      rw [hρdef, show -(Real.log 4 - 1) = 1 - Real.log 4 by ring, Real.rpow_sub ht0,
        Real.rpow_one]
      field_simp
      norm_num
    linarith [hstep, hfin.le, hfin.ge, hfnn]
  · have hJeq : JG P N = ⌊recipSumLe P N / 8⌋₊ := min_eq_right hcase
    have hSlt : recipSumLe P N < 8 * (JG P N : ℝ) + 8 := by
      have := Nat.lt_floor_add_one (recipSumLe P N / 8)
      rw [← hJeq] at this
      linarith
    have hsplit : recipSumLe P (2 * N)
        = recipSumLe P N + recipSumIoc P N (2 * N) :=
      recipSumLe_add_recipSumIoc P (by omega)
    have hnum : recipSumLe P (2 * N) + 5 * (JG P N : ℝ) + 12 ≤ 13 * (JG P N : ℝ) + 21 := by
      rw [hsplit]; linarith
    have hstep : (recipSumLe P (2 * N) + 5 * (JG P N : ℝ) + 12) / (4 : ℝ) ^ (JG P N)
        ≤ (13 * (JG P N : ℝ) + 21) / (4 : ℝ) ^ (JG P N) :=
      div_le_div_of_nonneg_right hnum hpow0.le
    linarith [hstep, hgnn]


/-! ## Admissibility of the schedule -/

omit P u in
/-- `⌊t²⌋^{1/c} ≤ ⌊t⌋` once `t ≥ 4` and `c ≥ 4`: one dyadic cut of a band's cutoff lands below
the next site cutoff.  The `c ≥ 4` (i.e. `L ≥ 2`) is what absorbs the two floors. -/
private theorem cut_le_next {t c : ℝ} (ht : 4 ≤ t) (hc : 4 ≤ c) :
    ((⌊t ^ (2 : ℕ)⌋₊ : ℕ) : ℝ) ^ ((1 : ℝ) / c) ≤ ((⌊t⌋₊ : ℕ) : ℝ) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hc0 : (0 : ℝ) < c := by linarith
  have hsq : ((⌊t ^ (2 : ℕ)⌋₊ : ℕ) : ℝ) ≤ t ^ (2 : ℕ) := Nat.floor_le (by positivity)
  have h1 : ((⌊t ^ (2 : ℕ)⌋₊ : ℕ) : ℝ) ^ ((1 : ℝ) / c) ≤ (t ^ (2 : ℕ)) ^ ((1 : ℝ) / c) :=
    Real.rpow_le_rpow (by positivity) hsq (by positivity)
  have h2 : (t ^ (2 : ℕ)) ^ ((1 : ℝ) / c) = t ^ ((2 : ℝ) / c) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht0.le]
    congr 1
    push_cast
    ring
  have hexp : (2 : ℝ) / c ≤ (1 : ℝ) / 2 := by
    rw [div_le_iff₀ hc0]; linarith
  have h3 : t ^ ((2 : ℝ) / c) ≤ t ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le ht1 hexp
  have h5 : Real.sqrt t ≤ t / 2 := by
    rw [show t / 2 = Real.sqrt ((t / 2) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h6 : t - 1 ≤ ((⌊t⌋₊ : ℕ) : ℝ) := by linarith [Nat.lt_floor_add_one t]
  calc ((⌊t ^ (2 : ℕ)⌋₊ : ℕ) : ℝ) ^ ((1 : ℝ) / c) ≤ (t ^ (2 : ℕ)) ^ ((1 : ℝ) / c) := h1
    _ = t ^ ((2 : ℝ) / c) := h2
    _ ≤ t ^ ((1 : ℝ) / 2) := h3
    _ = Real.sqrt t := (Real.sqrt_eq_rpow t).symm
    _ ≤ t / 2 := h5
    _ ≤ t - 1 := by linarith
    _ ≤ ((⌊t⌋₊ : ℕ) : ℝ) := h6

/-- **The cut depth is pinned from both sides.**  `L_N ≥ 2`, and
`2^{L_N} ≤ log₂ y_{J−1} < 2^{L_N + 1}`.  The lower bound keeps every band's dyadic chain above
`2` (`hcut2`); the upper bound makes the bottom band's chain descend below `4 ≤ 2J`
(`hcutlo` at `b = J−1`).  Both hold because `L_N` is read off `y_{J−1}` itself. -/
theorem LG_spec (hu : 10 ≤ u) (hP : DivergentRecip P) : ∀ᶠ N : ℕ in atTop,
    (4 : ℝ) ≤ (2 : ℝ) ^ (LG P u N)
    ∧ (2 : ℝ) ^ (LG P u N) * Real.log 2 ≤ Real.log ((yG u N (JG P N - 1) : ℕ) : ℝ)
    ∧ Real.log ((yG u N (JG P N - 1) : ℕ) : ℝ) < 2 * ((2 : ℝ) ^ (LG P u N)) * Real.log 2 := by
  filter_upwards [yBotG_le_yG_nat P u hu, yBotG_tendsto.eventually_ge_atTop 16,
    (JG_tendsto P hP).eventually_ge_atTop 2] with N hybot hy16 hJ2
  have hJ1le : JG P N ≤ J1 N := JG_le_J1 P N
  have hy16' : 16 ≤ yG u N (JG P N - 1) := le_trans hy16 (hybot _ (by omega))
  have hyb16 : (16 : ℝ) ≤ ((yG u N (JG P N - 1) : ℕ) : ℝ) := by exact_mod_cast hy16'
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hlogyb : 4 * Real.log 2 ≤ Real.log ((yG u N (JG P N - 1) : ℕ) : ℝ) := by
    rw [← hlog16]; exact Real.log_le_log (by norm_num) hyb16
  have hW4 : (4 : ℝ) ≤ Real.log ((yG u N (JG P N - 1) : ℕ) : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]; linarith
  have hW0 : (0 : ℝ) < Real.log ((yG u N (JG P N - 1) : ℕ) : ℝ) / Real.log 2 := by linarith
  have hlogW : 2 * Real.log 2
      ≤ Real.log (Real.log ((yG u N (JG P N - 1) : ℕ) : ℝ) / Real.log 2) := by
    rw [← hlog4]; exact Real.log_le_log (by norm_num) hW4
  have hratio : (2 : ℝ)
      ≤ Real.log (Real.log ((yG u N (JG P N - 1) : ℕ) : ℝ) / Real.log 2) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]; linarith
  have hfl2 : 2 ≤ ⌊Real.log (Real.log ((yG u N (JG P N - 1) : ℕ) : ℝ) / Real.log 2)
      / Real.log 2⌋₊ := Nat.le_floor (by exact_mod_cast hratio)
  have hLeq : LG P u N = ⌊Real.log (Real.log ((yG u N (JG P N - 1) : ℕ) : ℝ) / Real.log 2)
      / Real.log 2⌋₊ := max_eq_right hfl2
  have hL2 : 2 ≤ LG P u N := le_max_left 2 _
  have hpowdef : ((2 : ℝ)) ^ (LG P u N) = Real.exp (Real.log 2 * ((LG P u N : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast (2 : ℝ) (LG P u N), Real.rpow_def_of_pos (by norm_num)]
  have hLle : ((LG P u N : ℕ) : ℝ)
      ≤ Real.log (Real.log ((yG u N (JG P N - 1) : ℕ) : ℝ) / Real.log 2) / Real.log 2 := by
    rw [hLeq]; exact Nat.floor_le (by linarith)
  have hLlt : Real.log (Real.log ((yG u N (JG P N - 1) : ℕ) : ℝ) / Real.log 2) / Real.log 2
      < ((LG P u N : ℕ) : ℝ) + 1 := by
    rw [hLeq]; exact Nat.lt_floor_add_one _
  refine ⟨?_, ?_, ?_⟩
  · calc (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ (LG P u N) := pow_le_pow_right₀ (by norm_num) hL2
  · have h1 : Real.log 2 * ((LG P u N : ℕ) : ℝ)
        ≤ Real.log (Real.log ((yG u N (JG P N - 1) : ℕ) : ℝ) / Real.log 2) := by
      rw [le_div_iff₀ hlog2] at hLle; linarith
    have h2 : (2 : ℝ) ^ (LG P u N)
        ≤ Real.log ((yG u N (JG P N - 1) : ℕ) : ℝ) / Real.log 2 := by
      rw [hpowdef]
      calc Real.exp (Real.log 2 * ((LG P u N : ℕ) : ℝ))
          ≤ Real.exp (Real.log (Real.log ((yG u N (JG P N - 1) : ℕ) : ℝ) / Real.log 2)) :=
            Real.exp_le_exp.mpr h1
        _ = _ := Real.exp_log hW0
    rw [le_div_iff₀ hlog2] at h2; linarith
  · have h1 : Real.log (Real.log ((yG u N (JG P N - 1) : ℕ) : ℝ) / Real.log 2)
        < Real.log 2 * (((LG P u N : ℕ) : ℝ) + 1) := by
      rw [div_lt_iff₀ hlog2] at hLlt; linarith
    have hexp : Real.exp (Real.log 2 * (((LG P u N : ℕ) : ℝ) + 1)) = 2 * (2 : ℝ) ^ (LG P u N) := by
      rw [mul_add, mul_one, Real.exp_add, hpowdef, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring
    have h2 : Real.log ((yG u N (JG P N - 1) : ℕ) : ℝ) / Real.log 2
        < 2 * ((2 : ℝ) ^ (LG P u N)) := by
      calc Real.log ((yG u N (JG P N - 1) : ℕ) : ℝ) / Real.log 2
          = Real.exp (Real.log (Real.log ((yG u N (JG P N - 1) : ℕ) : ℝ) / Real.log 2)) :=
            (Real.exp_log hW0).symm
        _ < Real.exp (Real.log 2 * (((LG P u N : ℕ) : ℝ) + 1)) := Real.exp_lt_exp.mpr h1
        _ = _ := hexp
    rw [div_lt_iff₀ hlog2] at h2; linarith


/-- **Leaf G5c-1 — PROVED.**  The schedule is pointwise admissible for
`window_bound_schedule`.  Every clause is an inequality between the explicit schedule functions;
none involves the model or the sieve.  The two substantive ones are the dyadic-cut clauses, and
they are what pins `LG` to the **bottom site cutoff** (see `LG_spec`). -/
theorem schedule_admissible (hu : 10 ≤ u) (hP : DivergentRecip P) :
    ∀ᶠ N : ℕ in atTop,
    1 ≤ JG P N
    ∧ (∀ i j : Fin (JG P N), i ≤ j → yG u N j ≤ yG u N i)
    ∧ (∀ j : Fin (JG P N), 2 * JG P N ≤ yG u N j)
    ∧ (∀ j : Fin (JG P N), 2 ≤ Real.log (yG u N j))
    ∧ (∀ (b : Fin (JG P N)) (hb : (b : ℕ) + 1 < JG P N),
        loG P u N b = yG u N ((b : ℕ) + 1))
    ∧ (∀ b : Fin (JG P N), (b : ℕ) + 1 = JG P N → loG P u N b = 2 * JG P N)
    ∧ (∀ b : Fin (JG P N),
        cut (fun b : Fin (JG P N) => ((yG u N b : ℕ) : ℝ)) b (LG P u N) ≤ (loG P u N b : ℝ))
    ∧ (∀ b : Fin (JG P N),
        2 ≤ cut (fun b : Fin (JG P N) => ((yG u N b : ℕ) : ℝ)) b (LG P u N))
    ∧ (∑ b : Fin (JG P N), Real.exp (-(uuG P u N b : ℝ)) ≤ 1)
    ∧ (∀ j : Fin (JG P N), 1 ≤ TG N j)
    ∧ (∀ j : Fin (JG P N), yBotG N ≤ yG u N j) := by
  filter_upwards [yBotG_le_yG_nat P u hu, yBotG_le_yG P u hu,
    yBotG_tendsto.eventually_ge_atTop 16, twoJ1_lt_yBotG,
    (JG_tendsto P hP).eventually_ge_atTop 2,
    Eventually.of_forall (fun _ => (by omega : 1 ≤ u)),
    LG_spec P u hu hP, eventually_ge_atTop 1]
    with N hybotn hybotf hy16 htwoJ hJ2 hu1 hLs hN1
  obtain ⟨hL4, hLlo, hLhi⟩ := hLs
  have hJ1le : JG P N ≤ J1 N := JG_le_J1 P N
  have hN1r : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hJ2r : (2 : ℝ) ≤ ((JG P N : ℕ) : ℝ) := by exact_mod_cast hJ2
  have hmono' : ∀ i j : ℕ, i ≤ j → yG u N j ≤ yG u N i := fun i j hij =>
    yG_antitone P u hN1 hij
  have hy16j : ∀ j : ℕ, j ≤ J1 N → 16 ≤ yG u N j := fun j hj => le_trans hy16 (hybotn j hj)
  have hy16r : ∀ j : ℕ, j ≤ J1 N → (16 : ℝ) ≤ ((yG u N j : ℕ) : ℝ) := by
    intro j hj; exact_mod_cast hy16j j hj
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hlogy : ∀ j : ℕ, j ≤ J1 N → 4 * Real.log 2 ≤ Real.log ((yG u N j : ℕ) : ℝ) := by
    intro j hj
    rw [← hlog16]
    exact Real.log_le_log (by norm_num) (hy16r j hj)
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i j hij => hmono' _ _ (Fin.le_def.mp hij)
  · intro j
    have h1 := hybotn (j : ℕ) (by omega)
    omega
  · intro j
    have := hlogy (j : ℕ) (by omega)
    linarith [Real.log_two_gt_d9]
  · intro b hb
    simp only [loG, if_pos hb]
  · intro b hb
    simp only [loG, if_neg (by omega : ¬ ((b : ℕ) + 1 < JG P N))]
  · -- `hcutlo`: the dyadic chain of band `b` reaches below `lo b`
    intro b
    by_cases hb : (b : ℕ) + 1 < JG P N
    · simp only [loG, if_pos hb, cut]
      have hj1 : (b : ℕ) + 1 ≤ J1 N := by omega
      have ht16 : (16 : ℝ) ≤ (N : ℝ) ^ (aG u N * ((1 : ℝ) / 2) ^ ((b : ℕ) + 1)) := by
        refine le_trans (hy16r _ hj1) ?_
        exact Nat.floor_le (by positivity)
      have hsq : (N : ℝ) ^ (aG u N * ((1 : ℝ) / 2) ^ (b : ℕ))
          = ((N : ℝ) ^ (aG u N * ((1 : ℝ) / 2) ^ ((b : ℕ) + 1))) ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast ((N : ℝ) ^ (aG u N * ((1 : ℝ) / 2) ^ ((b : ℕ) + 1))) 2,
          ← Real.rpow_mul (by positivity)]
        congr 1
        push_cast
        ring
      have hyj : yG u N (b : ℕ)
          = ⌊((N : ℝ) ^ (aG u N * ((1 : ℝ) / 2) ^ ((b : ℕ) + 1))) ^ (2 : ℕ)⌋₊ := by
        simp only [yG]; rw [hsq]
      have hyj1 : yG u N ((b : ℕ) + 1)
          = ⌊(N : ℝ) ^ (aG u N * ((1 : ℝ) / 2) ^ ((b : ℕ) + 1))⌋₊ := rfl
      rw [hyj, hyj1]
      exact cut_le_next (by linarith) hL4
    · have hbe : (b : ℕ) = JG P N - 1 := by omega
      have hlo : loG P u N b = 2 * JG P N := by simp only [loG, if_neg hb]
      rw [hlo]
      simp only [cut, hbe]
      refine le_of_lt ?_
      have hyb0 : (0 : ℝ) < ((yG u N (JG P N - 1) : ℕ) : ℝ) := by
        have := hy16r (JG P N - 1) (by omega); linarith
      have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
      have hlt : Real.log ((yG u N (JG P N - 1) : ℕ) : ℝ) * ((1 : ℝ) / 2 ^ (LG P u N))
          < Real.log 4 := by
        rw [hlog4, mul_one_div, div_lt_iff₀ (by positivity)]
        linarith
      calc ((yG u N (JG P N - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / 2 ^ (LG P u N))
          = Real.exp (Real.log ((yG u N (JG P N - 1) : ℕ) : ℝ) * ((1 : ℝ) / 2 ^ (LG P u N))) :=
            Real.rpow_def_of_pos hyb0 _
        _ < Real.exp (Real.log 4) := Real.exp_lt_exp.mpr hlt
        _ = 4 := Real.exp_log (by norm_num)
        _ ≤ ((2 * JG P N : ℕ) : ℝ) := by push_cast; linarith
  · -- `hcut2`: the dyadic chain never drops below `2`
    intro b
    simp only [cut]
    have hyb0 : (0 : ℝ) < ((yG u N (b : ℕ) : ℕ) : ℝ) := by
      have := hy16r (b : ℕ) (by omega); linarith
    have hmo : ((yG u N (JG P N - 1) : ℕ) : ℝ) ≤ ((yG u N (b : ℕ) : ℕ) : ℝ) := by
      have : yG u N (JG P N - 1) ≤ yG u N (b : ℕ) := hmono' _ _ (by omega)
      exact_mod_cast this
    have hlogmo : Real.log ((yG u N (JG P N - 1) : ℕ) : ℝ)
        ≤ Real.log ((yG u N (b : ℕ) : ℕ) : ℝ) := by
      refine Real.log_le_log ?_ hmo
      have := hy16r (JG P N - 1) (by omega); linarith
    have hge : Real.log 2
        ≤ Real.log ((yG u N (b : ℕ) : ℕ) : ℝ) * ((1 : ℝ) / 2 ^ (LG P u N)) := by
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      linarith
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log ((yG u N (b : ℕ) : ℕ) : ℝ) * ((1 : ℝ) / 2 ^ (LG P u N))) :=
          Real.exp_le_exp.mpr hge
      _ = _ := (Real.rpow_def_of_pos hyb0 _).symm
  · -- `∑_b e^{−u_b} ≤ 1`
    have hs := sum_uuG_le P u N
    have hue : Real.exp (-(u : ℝ)) ≤ Real.exp (-1) := by
      refine Real.exp_le_exp.mpr ?_
      have : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu1
      linarith
    have hprod : Real.exp (-1 : ℝ) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]; norm_num
    have hpos : (0 : ℝ) < Real.exp (-1 : ℝ) := Real.exp_pos _
    have hbound : Real.exp (-1 : ℝ) ≤ 0.625 := by
      nlinarith [Real.exp_one_gt_d9, hprod, hpos]
    linarith
  · intro j
    have hnn : (0 : ℝ) ≤ (1 / 16 : ℝ) * Real.sqrt (((1 : ℝ) / 2) ^ (j : ℕ)) := by positivity
    have := Real.rpow_le_rpow_of_exponent_le hN1r hnn
    rw [Real.rpow_zero] at this
    simpa [TG] using this
  · exact hybotf

/-! ## The pointwise window bound on the schedule -/

/-- The graded window bound, with the `j₀`-dependence of E5 removed by monotonicity: every site
cutoff dominates `yBot N`, so the contraction collected below `y_{j₀}` is at least the one
collected below `yBot N`. -/
theorem windowMean_le_terms (hu : 10 ≤ u) (hP : DivergentRecip P)
    (h : ℤ) : ∀ᶠ N : ℕ in atTop,
    (∀ hh : NontrivialWindow (JG P N) h, 0 < N →
      ‖windowMeanS P (JG P N) h N‖
        ≤ termE1 P u h N + (termE4a P u N + termE4b P u N + termE4c P u N) + termE5 P u h N) := by
  filter_upwards [schedule_admissible P u hu hP, eventually_ge_atTop 1] with N hadm hN1
  obtain ⟨hk, hmono, hmy, hylog, hloin, hlotop, hcutlo, hcut2, hT1, hT, hybot⟩ := hadm
  intro hntw hN
  obtain ⟨j₀, hjb, hbound⟩ := window_bound_schedule P (k := JG P N) (L := LG P u N) hk
    (fun j => yG u N j) hmono hmy hylog (loG P u N) hloin hlotop hcutlo hcut2
    (uuG P u N) hT1 hT h hntw N hN

  rw [termE1, termE4a, termE4b, termE4c, termE5]
  refine hbound.trans (add_le_add (le_refl _) ?_)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg ?_)) (by positivity)
  have hjc : (j₀ : ℕ) ≤ cIdx P h N := by
    rw [cIdx]
    exact le_min hjb (by omega)
  have hyc : yG u N (cIdx P h N) ≤ yG u N (j₀ : ℕ) := yG_antitone P u hN1 hjc
  have hsub : ((midPrimes P (2 * JG P N) (yG u N 0)).filter (fun p => p ≤ yG u N (cIdx P h N)))
      ⊆ ((midPrimes P (2 * JG P N) (yG u N 0)).filter
        (fun p => p ≤ yG u N (j₀ : ℕ))) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, le_trans hp.2 hyc⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)


/-- **Leaf G5c-5 (E4c) — PROVED.**  Every factor is `N^{o(1)}` and the `1/N` wins:

* `(2J)# ≤ 4^{2J} ≤ N^{0.09}` since `J ≤ L₃N ≤ L₂N/2` while `log N ≥ (L₂N/2)²`;
* `∏_j ⌊T_j⌋ ≤ ∏_j N^{2^{−j/2}/16} ≤ N^{0.25}` since `√(2^{−j}) ≤ (3/4)^j` sums to `≤ 4`;
* `R² ≤ N^{0.09}` since `log R = ∑_b (128(b+1) + 4u_b + 14) log y_b
  ≤ (142 + 4u_N)·a_N·log N·∑_b (b+1)2^{−b} ≤ 12(142+4u_N)/u_N²·log N`, and the graded support
  level is what makes this `o(log N)` — the constant class count gave `128 J log y_0` instead.

So `termE4c ≤ 2 N^{0.09+0.25+0.09-1} ≤ 2 N^{−1/2} → 0`. -/
theorem termE4c_tendsto (hu : 3000 ≤ u) (hP : DivergentRecip P) :
    Tendsto (termE4c P u) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun N : ℕ => 2 * Real.exp (-(0.5 : ℝ) * Real.log (N : ℝ)))
      atTop (𝓝 0) := by
    have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h1 : Tendsto (fun N : ℕ => -(0.5 : ℝ) * Real.log (N : ℝ)) atTop atBot := by
      have h2 : Tendsto (fun N : ℕ => (0.5 : ℝ) * Real.log (N : ℝ)) atTop atTop :=
        Filter.Tendsto.const_mul_atTop (by norm_num) hlog
      have h3 := tendsto_neg_atTop_atBot.comp h2
      refine h3.congr fun N => ?_
      simp only [Function.comp_apply]
      ring
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (2 : ℝ)
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hmaj
  · rw [termE4c]
    have h1 : (0:ℝ) ≤ ∏ j : Fin (JG P N), (Nat.floor (TG N j) : ℝ) :=
      Finset.prod_nonneg fun j _ => Nat.cast_nonneg _
    positivity
  filter_upwards [yBotG_le_yG_nat P u (by omega), yBotG_tendsto.eventually_ge_atTop 16,
    Eventually.of_forall (fun _ => (by omega : 3000 ≤ u)), JG_le_L3 P u,
    L2_tendsto.eventually_ge_atTop (2500 : ℝ), eventually_ge_atTop 3]
    with N hybot hy16 hu3000 hJL3 hL2 hN3
  have hJ1le : JG P N ≤ J1 N := JG_le_J1 P N
  have hNr : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN : (0 : ℝ) < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hu3000r : (3000 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu3000
  obtain ⟨hL3one, hL3half, -⟩ := L3_bounds hL2
  -- (a) the primorial
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hlog4le : Real.log (4 : ℝ) ≤ 1.3863 := by
    have := Real.log_two_lt_d9; rw [hlog4]; linarith
  have hlog4nn : (0 : ℝ) ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hJ0 : (0 : ℝ) ≤ ((JG P N : ℕ) : ℝ) := Nat.cast_nonneg _
  have hE := log_ge_sq (N := N) hlogN (by linarith)
  have hAexp : 2 * ((JG P N : ℕ) : ℝ) * Real.log 4 ≤ 0.09 * Real.log (N : ℝ) := by
    have s2 : ((JG P N : ℕ) : ℝ) ≤ L2 N / 2 := le_trans hJL3 hL3half
    have s4 : 2 * ((JG P N : ℕ) : ℝ) * Real.log 4 ≤ 1.3863 * L2 N := by nlinarith
    nlinarith [hE, hL2, mul_nonneg (by linarith : (0:ℝ) ≤ L2 N - 2500)
      (by linarith : (0:ℝ) ≤ L2 N)]
  have hA : ((primorial (2 * JG P N) : ℕ) : ℝ) ≤ Real.exp (0.09 * Real.log (N : ℝ)) := by
    refine le_trans (primorial_le_four_pow_real _) ?_
    have hpow : (4 : ℝ) ^ (2 * JG P N) = Real.exp (2 * ((JG P N : ℕ) : ℝ) * Real.log 4) := by
      rw [← Real.rpow_natCast (4 : ℝ) (2 * JG P N), Real.rpow_def_of_pos (by norm_num)]
      congr 1; push_cast; try ring
    rw [hpow]
    exact Real.exp_le_exp.mpr hAexp
  -- (b) the Markov thresholds
  have hTeq : ∀ j : ℕ, TG N j
      = Real.exp ((1 / 16 : ℝ) * Real.sqrt (((1 : ℝ) / 2) ^ j) * Real.log (N : ℝ)) := by
    intro j
    rw [TG, Real.rpow_def_of_pos hNpos]
    congr 1; ring
  have hB : (∏ j : Fin (JG P N), (Nat.floor (TG N j) : ℝ))
      ≤ Real.exp (0.25 * Real.log (N : ℝ)) := by
    have h1 : (∏ j : Fin (JG P N), (Nat.floor (TG N j) : ℝ))
        ≤ ∏ j : Fin (JG P N), TG N j :=
      Finset.prod_le_prod (fun j _ => Nat.cast_nonneg _)
        (fun j _ => Nat.floor_le (by rw [hTeq]; positivity))
    have h2 : (∏ j : Fin (JG P N), TG N j)
        = Real.exp (∑ j : Fin (JG P N),
            (1 / 16 : ℝ) * Real.sqrt (((1 : ℝ) / 2) ^ (j : ℕ)) * Real.log (N : ℝ)) := by
      rw [Real.exp_sum]
      exact Finset.prod_congr rfl (fun j _ => hTeq _)
    have h3 : (∑ j : Fin (JG P N),
        (1 / 16 : ℝ) * Real.sqrt (((1 : ℝ) / 2) ^ (j : ℕ)) * Real.log (N : ℝ))
        ≤ 0.25 * Real.log (N : ℝ) := by
      have hs : (∑ j : Fin (JG P N), (1 / 16 : ℝ) * Real.sqrt (((1 : ℝ) / 2) ^ (j : ℕ)))
          ≤ 0.25 := by
        rw [Fin.sum_univ_eq_sum_range
          (fun i => (1 / 16 : ℝ) * Real.sqrt (((1 : ℝ) / 2) ^ i)) (JG P N)]
        have hb : ∑ i ∈ Finset.range (JG P N), (1 / 16 : ℝ) * Real.sqrt (((1 : ℝ) / 2) ^ i)
            ≤ (1 / 16 : ℝ) * ∑ i ∈ Finset.range (JG P N), ((3 : ℝ) / 4) ^ i := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (sqrt_half_pow_le i) (by norm_num)
        have := sum_three_quarter_le (JG P N)
        linarith
      calc (∑ j : Fin (JG P N),
            (1 / 16 : ℝ) * Real.sqrt (((1 : ℝ) / 2) ^ (j : ℕ)) * Real.log (N : ℝ))
          = (∑ j : Fin (JG P N), (1 / 16 : ℝ) * Real.sqrt (((1 : ℝ) / 2) ^ (j : ℕ)))
              * Real.log (N : ℝ) := by rw [Finset.sum_mul]
        _ ≤ 0.25 * Real.log (N : ℝ) := mul_le_mul_of_nonneg_right hs hlogN.le
    rw [h2] at h1
    exact le_trans h1 (Real.exp_le_exp.mpr h3)
  -- (c) the graded support level
  have hlogy : ∀ b : Fin (JG P N), Real.log ((yG u N (b : ℕ) : ℕ) : ℝ)
      ≤ aG u N * ((1 : ℝ) / 2) ^ (b : ℕ) * Real.log (N : ℝ) := by
    intro b
    have h16 : (16 : ℝ) ≤ ((yG u N (b : ℕ) : ℕ) : ℝ) := by
      have : 16 ≤ yG u N (b : ℕ) := le_trans hy16 (hybot _ (by omega))
      exact_mod_cast this
    have hle : ((yG u N (b : ℕ) : ℕ) : ℝ)
        ≤ (N : ℝ) ^ (aG u N * ((1 : ℝ) / 2) ^ (b : ℕ)) := Nat.floor_le (by positivity)
    have := Real.log_le_log (by linarith) hle
    rwa [Real.log_rpow hNpos] at this
  have haG : aG u N = 1 / (u : ℝ) ^ 2 := rfl
  have haGpos : (0 : ℝ) < aG u N := by rw [haG]; positivity
  set C : ℝ := (142 + 4 * (u : ℝ)) * (aG u N * Real.log (N : ℝ)) with hCdef
  have hC0 : (0 : ℝ) ≤ C := by rw [hCdef]; positivity
  have hCsmall : C * 12 ≤ 0.045 * Real.log (N : ℝ) := by
    have hu0 : (0 : ℝ) < (u : ℝ) := by linarith
    have hkey : (142 + 4 * (u : ℝ)) * aG u N * 12 ≤ 0.045 := by
      have h1 : (142 + 4 * (u : ℝ)) * (1 / (u : ℝ) ^ 2) * 12
          = (142 * 12 + 48 * (u : ℝ)) / (u : ℝ) ^ 2 := by
        field_simp; ring
      rw [haG, h1, div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (show (0:ℝ) ≤ (u : ℝ) - 3000 by linarith)
        (show (0:ℝ) ≤ (u : ℝ) by linarith)]
    have hrw : C * 12
        = ((142 + 4 * (u : ℝ)) * aG u N * 12) * Real.log (N : ℝ) := by
      rw [hCdef]; ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_right hkey hlogN.le
  have hgl : gradedLevel (Finset.univ : Finset (Fin (JG P N)))
      (fun b : Fin (JG P N) => (b : ℕ) + 1) (uuG P u N)
      (fun b : Fin (JG P N) => ((yG u N b : ℕ) : ℝ))
      ≤ Real.exp (0.045 * Real.log (N : ℝ)) := by
    simp only [gradedLevel]
    refine Real.exp_le_exp.mpr ?_
    have hterm : ∀ b ∈ (Finset.univ : Finset (Fin (JG P N))),
        (128 * ((((b : ℕ) + 1 : ℕ)) : ℝ) + 4 * ((uuG P u N b : ℕ) : ℝ) + 14)
            * Real.log ((yG u N (b : ℕ) : ℕ) : ℝ)
          ≤ C * (((b : ℕ) : ℝ) + 1) * ((1 : ℝ) / 2) ^ (b : ℕ) := by
      intro b _
      have huu : ((uuG P u N b : ℕ) : ℝ) = (u : ℝ) + ((b : ℕ) : ℝ) := by
        simp only [uuG]; push_cast; ring
      have hb0 : (0 : ℝ) ≤ ((b : ℕ) : ℝ) := Nat.cast_nonneg _
      have hcoef : (128 * ((((b : ℕ) + 1 : ℕ)) : ℝ) + 4 * ((uuG P u N b : ℕ) : ℝ) + 14)
          ≤ (142 + 4 * (u : ℝ)) * (((b : ℕ) : ℝ) + 1) := by
        rw [huu]; push_cast; nlinarith
      have hcnn : (0 : ℝ)
          ≤ 128 * ((((b : ℕ) + 1 : ℕ)) : ℝ) + 4 * ((uuG P u N b : ℕ) : ℝ) + 14 := by positivity
      have hrhs : (0 : ℝ) ≤ aG u N * ((1 : ℝ) / 2) ^ (b : ℕ) * Real.log (N : ℝ) := by
        positivity
      calc (128 * ((((b : ℕ) + 1 : ℕ)) : ℝ) + 4 * ((uuG P u N b : ℕ) : ℝ) + 14)
            * Real.log ((yG u N (b : ℕ) : ℕ) : ℝ)
          ≤ (128 * ((((b : ℕ) + 1 : ℕ)) : ℝ) + 4 * ((uuG P u N b : ℕ) : ℝ) + 14)
              * (aG u N * ((1 : ℝ) / 2) ^ (b : ℕ) * Real.log (N : ℝ)) :=
            mul_le_mul_of_nonneg_left (hlogy b) hcnn
        _ ≤ ((142 + 4 * (u : ℝ)) * (((b : ℕ) : ℝ) + 1))
              * (aG u N * ((1 : ℝ) / 2) ^ (b : ℕ) * Real.log (N : ℝ)) :=
            mul_le_mul_of_nonneg_right hcoef hrhs
        _ = C * (((b : ℕ) : ℝ) + 1) * ((1 : ℝ) / 2) ^ (b : ℕ) := by rw [hCdef]; ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hfin : ∑ b : Fin (JG P N), (C * (((b : ℕ) : ℝ) + 1) * ((1 : ℝ) / 2) ^ (b : ℕ))
        ≤ C * 12 := by
      rw [Fin.sum_univ_eq_sum_range
        (fun i => C * ((i : ℝ) + 1) * ((1 : ℝ) / 2) ^ i) (JG P N)]
      have hrw : ∑ i ∈ Finset.range (JG P N), C * ((i : ℝ) + 1) * ((1 : ℝ) / 2) ^ i
          = C * ∑ i ∈ Finset.range (JG P N), (((i : ℝ) + 1) * ((1 : ℝ) / 2) ^ i) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [hrw]
      exact mul_le_mul_of_nonneg_left (sum_succ_half_le (JG P N)) hC0
    linarith
  have hC : (gradedLevel (Finset.univ : Finset (Fin (JG P N)))
      (fun b : Fin (JG P N) => (b : ℕ) + 1) (uuG P u N)
      (fun b : Fin (JG P N) => ((yG u N b : ℕ) : ℝ))) ^ 2
      ≤ Real.exp (0.09 * Real.log (N : ℝ)) := by
    have h0 : (0 : ℝ) ≤ gradedLevel (Finset.univ : Finset (Fin (JG P N)))
        (fun b : Fin (JG P N) => (b : ℕ) + 1) (uuG P u N)
        (fun b : Fin (JG P N) => ((yG u N b : ℕ) : ℝ)) := by
      rw [gradedLevel]; exact (Real.exp_pos _).le
    calc (gradedLevel (Finset.univ : Finset (Fin (JG P N)))
          (fun b : Fin (JG P N) => (b : ℕ) + 1) (uuG P u N)
          (fun b : Fin (JG P N) => ((yG u N b : ℕ) : ℝ))) ^ 2
        ≤ (Real.exp (0.045 * Real.log (N : ℝ))) ^ 2 := pow_le_pow_left₀ h0 hgl 2
      _ = Real.exp (0.09 * Real.log (N : ℝ)) := by
          rw [sq, ← Real.exp_add]; congr 1; ring
  -- assemble
  have hApos : (0 : ℝ) ≤ ((primorial (2 * JG P N) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hBpos : (0 : ℝ) ≤ ∏ j : Fin (JG P N), (Nat.floor (TG N j) : ℝ) :=
    Finset.prod_nonneg fun j _ => Nat.cast_nonneg _
  have hCpos : (0 : ℝ) ≤ (gradedLevel (Finset.univ : Finset (Fin (JG P N)))
      (fun b : Fin (JG P N) => (b : ℕ) + 1) (uuG P u N)
      (fun b : Fin (JG P N) => ((yG u N b : ℕ) : ℝ))) ^ 2 := by positivity
  have hprod : ((primorial (2 * JG P N) : ℕ) : ℝ)
      * (∏ j : Fin (JG P N), (Nat.floor (TG N j) : ℝ))
      * (gradedLevel (Finset.univ : Finset (Fin (JG P N)))
          (fun b : Fin (JG P N) => (b : ℕ) + 1) (uuG P u N)
          (fun b : Fin (JG P N) => ((yG u N b : ℕ) : ℝ))) ^ 2
      ≤ Real.exp (0.43 * Real.log (N : ℝ)) := by
    have h1 : ((primorial (2 * JG P N) : ℕ) : ℝ)
        * (∏ j : Fin (JG P N), (Nat.floor (TG N j) : ℝ))
        ≤ Real.exp (0.09 * Real.log (N : ℝ)) * Real.exp (0.25 * Real.log (N : ℝ)) :=
      mul_le_mul hA hB hBpos (Real.exp_pos _).le
    calc ((primorial (2 * JG P N) : ℕ) : ℝ)
          * (∏ j : Fin (JG P N), (Nat.floor (TG N j) : ℝ))
          * (gradedLevel (Finset.univ : Finset (Fin (JG P N)))
              (fun b : Fin (JG P N) => (b : ℕ) + 1) (uuG P u N)
              (fun b : Fin (JG P N) => ((yG u N b : ℕ) : ℝ))) ^ 2
        ≤ (Real.exp (0.09 * Real.log (N : ℝ)) * Real.exp (0.25 * Real.log (N : ℝ)))
            * Real.exp (0.09 * Real.log (N : ℝ)) :=
          mul_le_mul h1 hC hCpos (by positivity)
      _ = Real.exp (0.43 * Real.log (N : ℝ)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hinv : Real.exp (-(Real.log (N : ℝ))) = 1 / (N : ℝ) := by
    rw [Real.exp_neg, Real.exp_log hNpos, one_div]
  calc termE4c P u N
      = 2 * (((primorial (2 * JG P N) : ℕ) : ℝ)
          * (∏ j : Fin (JG P N), (Nat.floor (TG N j) : ℝ))
          * (gradedLevel (Finset.univ : Finset (Fin (JG P N)))
              (fun b : Fin (JG P N) => (b : ℕ) + 1) (uuG P u N)
              (fun b : Fin (JG P N) => ((yG u N b : ℕ) : ℝ))) ^ 2) * (1 / (N : ℝ)) := by
        rw [termE4c]; ring
    _ ≤ 2 * Real.exp (0.43 * Real.log (N : ℝ)) * (1 / (N : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hprod (by norm_num : (0:ℝ) ≤ 2)
        exact mul_le_mul_of_nonneg_right this (by positivity)
    _ = 2 * (Real.exp (0.43 * Real.log (N : ℝ)) * Real.exp (-(Real.log (N : ℝ)))) := by
        rw [hinv]; ring
    _ = 2 * Real.exp (-(0.57 : ℝ) * Real.log (N : ℝ)) := by
        rw [← Real.exp_add]; congr 2; ring
    _ ≤ 2 * Real.exp (-(0.5 : ℝ) * Real.log (N : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        nlinarith [hlogN.le]


/-- **Leaf G5c-6 (E5) — PROVED.**  Astra (8.6).  At the near-top cutoff `y_c`,
`c = cIdx P h N ≤ log₄|h|`:

    ∑_{p ∈ P, 2J < p ≤ y_c} 1/p = S_P(y_c) − S_P(2J)
                                = (S_P(N) − S_P(y_c,N)) − S_P(2J)
                                ≥ 8J − 1 − (12 L₂(2J) + 21),

from `JG_le_mass` (`8J ≤ S_P(N)`), the **short** root chain `recipSumIoc_yG_le`
(`S_P(y_c,N) ≤ (c + 2 + 2 log₂ u_N)/u_N² ≤ 1` once `u_N ≥ log₄|h| + 5`) and Mertens
(`FamilySharp.recipSumLe_le_crude`).  With `L₂(2J) ≤ log(2J)` this gives

    E5 ≤ e^{2J} · e^{−8J + 22 + 12 log 2J} = e^{22} (2J)^{12} / (e^6)^J → 0.

The `e^{22}` and the twelfth power are pure slack; the point is that the linear term `−6J`
survives, which is exactly what tying `J_N` to the **full** mass `S_P(N)` bought. -/
theorem termE5_tendsto (hu : 3000 ≤ u) (hP : DivergentRecip P) (h : ℤ) {E : ℝ} (hE0 : 0 ≤ E)
    (hE : ∀ᶠ N : ℕ in atTop, epsG P N ≤ E) :
    Tendsto (termE5 P u h) atTop (𝓝 0) := by
  set K : ℝ := E * (((Nat.log 4 h.natAbs : ℕ) : ℝ) + 2 + 3 * (u : ℝ)) with hKdef
  have he6 : (1 : ℝ) < Real.exp 6 := by
    have := Real.add_one_lt_exp (show (6 : ℝ) ≠ 0 by norm_num)
    linarith
  have hmaj : Tendsto
      (fun m : ℕ => Real.exp (22 + K) * (2 * (m : ℝ)) ^ 12 / (Real.exp 6) ^ m) atTop (𝓝 0) := by
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 12 he6
    have h2 : Tendsto
        (fun m : ℕ => (Real.exp (22 + K) * 2 ^ 12) * ((m : ℝ) ^ 12 / (Real.exp 6) ^ m))
        atTop (𝓝 0) := by simpa using h1.const_mul (Real.exp (22 + K) * 2 ^ 12)
    refine h2.congr fun m => ?_
    rw [mul_pow]; ring
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ (hmaj.comp (JG_tendsto P hP))
  · simp only [termE5]; positivity
  filter_upwards [recipSumIoc_yG_le P u (by omega), yBotG_le_yG_nat P u (by omega), twoJ1_lt_yBotG,
    yG_le_self P u (by omega), (JG_tendsto P hP).eventually_ge_atTop 2,
    hE, eventually_ge_atTop 1] with N hchain hybot htwoJ hyself hJ2 hEN hN1
  -- the index of the contracting site
  have hJ1le : JG P N ≤ J1 N := JG_le_J1 P N
  have hcJ : cIdx P h N ≤ JG P N - 1 := min_le_right _ _
  have hcC0 : cIdx P h N ≤ Nat.log 4 h.natAbs := min_le_left _ _
  have hcJ1 : cIdx P h N ≤ J1 N := by omega
  have hy0 : yG u N (cIdx P h N) ≤ yG u N 0 := yG_antitone P u hN1 (Nat.zero_le _)
  have h2Jy : 2 * JG P N ≤ yG u N (cIdx P h N) := by
    have := hybot (cIdx P h N) hcJ1
    omega
  have hycN : yG u N (cIdx P h N) ≤ N := hyself _
  -- the index set of E5 is the mass on `(2J, y_c]`
  have hset : ((midPrimes P (2 * JG P N) (yG u N 0)).filter
      (fun p => p ≤ yG u N (cIdx P h N)))
      = (Finset.Ioc (2 * JG P N) (yG u N (cIdx P h N))).filter (fun p => p.Prime ∧ P p) := by
    ext p
    simp only [Finset.mem_filter, mem_midPrimes, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hp, hPp, hlt, -⟩, hle⟩
      exact ⟨⟨hlt, hle⟩, hp, hPp⟩
    · rintro ⟨⟨hlt, hle⟩, hp, hPp⟩
      exact ⟨⟨hp, hPp, hlt, le_trans hle hy0⟩, hle⟩
  have hsum : ∑ p ∈ ((midPrimes P (2 * JG P N) (yG u N 0)).filter
      (fun p => p ≤ yG u N (cIdx P h N))), (1 : ℝ) / (p : ℝ)
      = recipSumIoc P (2 * JG P N) (yG u N (cIdx P h N)) := by
    rw [hset]; rfl
  -- numeric preliminaries
  have hJ2r : (2 : ℝ) ≤ ((JG P N : ℕ) : ℝ) := by exact_mod_cast hJ2
  have h2Jgt : (1 : ℝ) < ((2 * JG P N : ℕ) : ℝ) := by push_cast; linarith
  have hlog2J : (0 : ℝ) < Real.log ((2 * JG P N : ℕ) : ℝ) := Real.log_pos h2Jgt
  have hL2le : L2 (2 * JG P N) ≤ Real.log ((2 * JG P N : ℕ) : ℝ) := by
    have := Real.log_le_sub_one_of_pos hlog2J
    simp only [L2]
    linarith
  have hcrude : recipSumLe P (2 * JG P N) ≤ 12 * L2 (2 * JG P N) + 21 :=
    NormalNumbers.PrimeModel.FamilySharp.recipSumLe_le_crude P (by omega)
  -- the short root chain kills the mass above `y_c`
  have htail : recipSumIoc P (yG u N (cIdx P h N)) N ≤ K := by
    have hu0 : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast (by omega : 1 ≤ u)
    have hcr : ((cIdx P h N : ℕ) : ℝ) ≤ ((Nat.log 4 h.natAbs : ℕ) : ℝ) := by exact_mod_cast hcC0
    have hulog : Real.log (u : ℝ) ≤ (u : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by linarith)
    have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hdiv : 2 * Real.log (u : ℝ) / Real.log 2 ≤ 3 * (u : ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (u : ℝ)) (by linarith : (0 : ℝ) ≤ Real.log 2 - 0.6931471803),
        Real.log_nonneg hu0]
    have hlogu0 : 0 ≤ 2 * Real.log (u : ℝ) / Real.log 2 :=
      div_nonneg (by linarith [Real.log_nonneg hu0]) (by linarith)
    have heps0 := epsG_nonneg P N
    refine (hchain _ hcJ1).trans ?_
    rw [hKdef]
    have hin : ((cIdx P h N : ℕ) : ℝ) + 2 + 2 * Real.log (u : ℝ) / Real.log 2
        ≤ ((Nat.log 4 h.natAbs : ℕ) : ℝ) + 2 + 3 * (u : ℝ) := by linarith
    calc epsG P N * (((cIdx P h N : ℕ) : ℝ) + 2 + 2 * Real.log (u : ℝ) / Real.log 2)
        ≤ E * (((cIdx P h N : ℕ) : ℝ) + 2 + 2 * Real.log (u : ℝ) / Real.log 2) :=
          mul_le_mul_of_nonneg_right hEN (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hin hE0
  have hmass : 8 * ((JG P N : ℕ) : ℝ) ≤ recipSumLe P N := JG_le_mass P N
  have hsplit1 : recipSumLe P (yG u N (cIdx P h N))
      = recipSumLe P (2 * JG P N) + recipSumIoc P (2 * JG P N) (yG u N (cIdx P h N)) :=
    recipSumLe_add_recipSumIoc P h2Jy
  have hsplit2 : recipSumLe P N
      = recipSumLe P (yG u N (cIdx P h N)) + recipSumIoc P (yG u N (cIdx P h N)) N :=
    recipSumLe_add_recipSumIoc P hycN
  have hSigma : 8 * ((JG P N : ℕ) : ℝ) - (22 + K) - 12 * Real.log ((2 * JG P N : ℕ) : ℝ)
      ≤ recipSumIoc P (2 * JG P N) (yG u N (cIdx P h N)) := by linarith
  -- assemble
  simp only [Function.comp_apply, termE5]
  rw [hsum]
  have hstep : Real.exp (-recipSumIoc P (2 * JG P N) (yG u N (cIdx P h N)))
      ≤ Real.exp (-(8 * ((JG P N : ℕ) : ℝ) - (22 + K)
          - 12 * Real.log ((2 * JG P N : ℕ) : ℝ))) :=
    Real.exp_le_exp.mpr (by linarith)
  have hxpos : (0 : ℝ) < 2 * ((JG P N : ℕ) : ℝ) := by linarith
  have hlogpow : Real.exp (12 * Real.log (2 * ((JG P N : ℕ) : ℝ)))
      = (2 * ((JG P N : ℕ) : ℝ)) ^ (12 : ℕ) := by
    rw [show (12 : ℝ) * Real.log (2 * ((JG P N : ℕ) : ℝ))
        = Real.log ((2 * ((JG P N : ℕ) : ℝ)) ^ (12 : ℕ)) by rw [Real.log_pow]; push_cast; ring]
    exact Real.exp_log (pow_pos hxpos 12)
  have hfact : Real.exp (2 * ((JG P N : ℕ) : ℝ))
      * Real.exp (-(8 * ((JG P N : ℕ) : ℝ) - (22 + K)
          - 12 * Real.log ((2 * JG P N : ℕ) : ℝ)))
      = Real.exp (22 + K) * (2 * ((JG P N : ℕ) : ℝ)) ^ 12 / (Real.exp 6) ^ (JG P N) := by
    have hx : ((2 * JG P N : ℕ) : ℝ) = 2 * ((JG P N : ℕ) : ℝ) := by push_cast; ring
    rw [hx, ← Real.exp_add,
      show 2 * ((JG P N : ℕ) : ℝ) + -(8 * ((JG P N : ℕ) : ℝ) - (22 + K)
          - 12 * Real.log (2 * ((JG P N : ℕ) : ℝ)))
        = ((22 + K) + 12 * Real.log (2 * ((JG P N : ℕ) : ℝ))) - ((JG P N : ℕ) : ℝ) * 6 by ring,
      Real.exp_sub, Real.exp_add, hlogpow, Real.exp_nat_mul]
  calc Real.exp (2 * ((JG P N : ℕ) : ℝ))
        * Real.exp (-recipSumIoc P (2 * JG P N) (yG u N (cIdx P h N)))
      ≤ Real.exp (2 * ((JG P N : ℕ) : ℝ))
        * Real.exp (-(8 * ((JG P N : ℕ) : ℝ) - (22 + K)
            - 12 * Real.log ((2 * JG P N : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hstep (Real.exp_pos _).le
    _ = _ := hfact

/-! ## Quantitative leaves (limsup bounds at fixed `u`) -/

omit u in
/-- Bounded square-root fresh mass bounds the surrogate `ε_N` eventually. -/
theorem epsG_eventually_le {ρ : ℝ} (hS : Quant.SqrtFreshMassLe P ρ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, epsG P N ≤ ρ + ε := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hS ε hε)
  filter_upwards [yBotG_tendsto.eventually_ge_atTop T] with N hN
  exact epsG_le P (fun q hq => hT q (le_trans hN hq))

omit P u in
/-- **The capped site weights.**  With `k = log₄|h| + 1` and `c ≥ 2`,
`∑_j min(2, 4π|h|4^{−j−1}) (j + c) ≤ 2k(k + c) + 4π(k + c)`: the sites below `k` pay the cap `2`,
the sites above pay a geometric series. -/
theorem sum_siteBudget_weight (h : ℤ) (J : ℕ) {c : ℝ} (hc : 2 ≤ c) :
    ∑ j : Fin J, siteBudget h j.val * ((j : ℝ) + c)
      ≤ 2 * ((Nat.log 4 h.natAbs + 1 : ℕ) : ℝ) * (((Nat.log 4 h.natAbs + 1 : ℕ) : ℝ) + c)
        + 4 * Real.pi * (((Nat.log 4 h.natAbs + 1 : ℕ) : ℝ) + c) := by
  set k : ℕ := Nat.log 4 h.natAbs + 1 with hk
  have hhk : (|(h : ℝ)|) ≤ (4 : ℝ) ^ k := by
    have h1 : h.natAbs < 4 ^ k := Nat.lt_pow_succ_log_self (by norm_num) _
    have h2 : (|(h : ℝ)|) = (h.natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h2]; exact_mod_cast h1.le
  set G : ℕ → ℝ := fun j => if j < k then 2 * ((j : ℝ) + c)
    else Real.pi * ((1 : ℝ) / 4) ^ (j - k) * ((j : ℝ) + c) with hG
  have hG0 : ∀ j, 0 ≤ G j := by
    intro j; simp only [hG]; split_ifs
    · have : (0:ℝ) ≤ j := Nat.cast_nonneg j; nlinarith
    · have : (0:ℝ) ≤ j := Nat.cast_nonneg j; positivity
  have hpt : ∀ j : ℕ, siteBudget h j * ((j : ℝ) + c) ≤ G j := by
    intro j
    have hjc : (0 : ℝ) ≤ (j : ℝ) + c := by have : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith
    simp only [hG]; split_ifs with hj
    · exact mul_le_mul_of_nonneg_right (siteBudget_le_two h j) hjc
    · refine mul_le_mul_of_nonneg_right ((siteBudget_le_lin h j).trans ?_) hjc
      push_neg at hj
      have hpow : (4 : ℝ) ^ (j + 1) = 4 * (4 : ℝ) ^ (j - k) * (4 : ℝ) ^ k := by
        rw [mul_assoc, ← pow_add, show j - k + k = j by omega, pow_succ]; ring
      have e1 : 4 * Real.pi * |(h : ℝ)| * ((1 : ℝ) / 4) ^ (j + 1)
          = Real.pi * ((1 : ℝ) / 4) ^ (j - k) * (|(h : ℝ)| / (4 : ℝ) ^ k) := by
        rw [div_pow, div_pow, one_pow, one_pow, hpow]; field_simp
      rw [e1]
      have : |(h : ℝ)| / (4 : ℝ) ^ k ≤ 1 := by
        rw [div_le_one (by positivity)]; exact hhk
      have hp : 0 ≤ Real.pi * ((1 : ℝ) / 4) ^ (j - k) := by positivity
      calc Real.pi * ((1 : ℝ) / 4) ^ (j - k) * (|(h : ℝ)| / (4 : ℝ) ^ k)
          ≤ Real.pi * ((1 : ℝ) / 4) ^ (j - k) * 1 := mul_le_mul_of_nonneg_left this hp
        _ = _ := by ring
  rw [Fin.sum_univ_eq_sum_range (fun j => siteBudget h j * ((j : ℝ) + c)) J]
  refine (Finset.sum_le_sum fun j _ => hpt j).trans ?_
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr
    (Nat.le_add_left J k)) (fun j _ _ => hG0 j)).trans ?_
  rw [Finset.sum_range_add]
  have hA : ∑ j ∈ Finset.range k, G j ≤ 2 * (k : ℝ) * ((k : ℝ) + c) := by
    have : ∀ j ∈ Finset.range k, G j ≤ 2 * ((k : ℝ) + c) := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      simp only [hG, if_pos hj']
      have : (j : ℝ) ≤ k := by exact_mod_cast hj'.le
      linarith
    refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hB : ∑ i ∈ Finset.range J, G (k + i) ≤ 4 * Real.pi * ((k : ℝ) + c) := by
    have heq : ∀ i ∈ Finset.range J, G (k + i)
        = 4 * Real.pi * (((1 : ℝ) / 4) ^ (i + 1) * ((i : ℝ) + 2 + 2 * (((k : ℝ) + c - 2) / 2))) := by
      intro i _
      simp only [hG, if_neg (by omega : ¬ k + i < k), show k + i - k = i by omega]
      push_cast; rw [pow_succ]; ring
    rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
    have hL : (0 : ℝ) ≤ ((k : ℝ) + c - 2) / 2 := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
    have := sum_quarter_weight_le hL J
    have hpi : 0 ≤ 4 * Real.pi := by positivity
    calc 4 * Real.pi * ∑ i ∈ Finset.range J, ((1 : ℝ) / 4) ^ (i + 1)
          * ((i : ℝ) + 2 + 2 * (((k : ℝ) + c - 2) / 2))
        ≤ 4 * Real.pi * (1 + 2 * (((k : ℝ) + c - 2) / 2)) := mul_le_mul_of_nonneg_left this hpi
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hpi; linarith
  linarith

/-- **E1 at fixed `u`.**  If `ε_N ≤ E` eventually, the transfer term is eventually at most
`2E·(2k(k+c) + 4π(k+c)) + (4π|h|/3)·J/N` with `k = log₄|h|+1`, `c = 2 + 3u`. -/
theorem termE1_le (hu : 10 ≤ u) (h : ℤ) {E : ℝ} (hE0 : 0 ≤ E)
    (hE : ∀ᶠ N : ℕ in atTop, epsG P N ≤ E) : ∀ᶠ N : ℕ in atTop,
    termE1 P u h N ≤ 2 * E * (2 * ((Nat.log 4 h.natAbs + 1 : ℕ) : ℝ)
        * (((Nat.log 4 h.natAbs + 1 : ℕ) : ℝ) + (2 + 3 * (u : ℝ)))
        + 4 * Real.pi * (((Nat.log 4 h.natAbs + 1 : ℕ) : ℝ) + (2 + 3 * (u : ℝ))))
      + (4 * Real.pi * |(h : ℝ)| / 3) * ((JG P N : ℝ) / N) := by
  filter_upwards [recipSumIoc_yG_le P u hu, hE] with N hchain hEN
  have hu0 : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast (by omega : 1 ≤ u)
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hulog : Real.log (u : ℝ) ≤ (u : ℝ) - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hdiv : 2 * Real.log (u : ℝ) / Real.log 2 ≤ 3 * (u : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (u : ℝ))
      (by linarith : (0 : ℝ) ≤ Real.log 2 - 0.6931471803), Real.log_nonneg hu0]
  have heps0 := epsG_nonneg P N
  have hsite : ∀ j : Fin (JG P N), siteBudget h j.val
      * (2 * recipSumIoc P (yG u N j) N + ((JG P N : ℕ) : ℝ) / N)
      ≤ 2 * E * (siteBudget h j.val * ((j : ℝ) + (2 + 3 * (u : ℝ))))
        + siteBudget h j.val * (((JG P N : ℕ) : ℝ) / N) := by
    intro j
    have hj : (j : ℕ) ≤ J1 N := le_trans (le_of_lt j.2) (JG_le_J1 P N)
    have hR := hchain (j : ℕ) hj
    have hin : ((j : ℕ) : ℝ) + 2 + 2 * Real.log (u : ℝ) / Real.log 2
        ≤ ((j : ℕ) : ℝ) + (2 + 3 * (u : ℝ)) := by linarith
    have hR' : recipSumIoc P (yG u N j) N ≤ E * (((j : ℕ) : ℝ) + (2 + 3 * (u : ℝ))) := by
      refine hR.trans ((mul_le_mul_of_nonneg_right hEN ?_).trans
        (mul_le_mul_of_nonneg_left hin hE0))
      have : (0:ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
      have : 0 ≤ 2 * Real.log (u : ℝ) / Real.log 2 :=
        div_nonneg (by linarith [Real.log_nonneg hu0]) (by linarith)
      linarith
    have hb := siteBudget_nonneg h j.val
    nlinarith [mul_le_mul_of_nonneg_left hR' hb]
  rw [termE1]
  refine (Finset.sum_le_sum fun j _ => hsite j).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have h1 := sum_siteBudget_weight h (JG P N) (c := 2 + 3 * (u : ℝ)) (by linarith)
  have h2 := sum_siteBudget_le h (JG P N)
  have hJN : (0 : ℝ) ≤ ((JG P N : ℕ) : ℝ) / N := by positivity
  have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 * E)
  have := mul_le_mul_of_nonneg_right h2 hJN
  linarith

/-- **E4b at fixed `u`**: the sieve defect is at most `e^{−u}`. -/
theorem termE4b_le (N : ℕ) : termE4b P u N ≤ Real.exp (-(u : ℝ)) := by
  have hs := sum_uuG_le P u N
  rw [termE4b]
  have : 0 ≤ Real.exp (-(u : ℝ)) := (Real.exp_pos _).le
  linarith

end NormalNumbers.PrimeModel.QuantSchedule
