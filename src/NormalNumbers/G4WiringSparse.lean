import NormalNumbers.G4Mertens
import NormalNumbers.G4WiringCRT
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Sparse prime subsets: `IsNormal 4 (c_𝒫 4)` from KMT 2023 Prop 4.3
(DESIGN-2026-09-19-bcr-wiring.md §5; KB verdict §4d)

Klurman–Mangerel–Teräväinen (arXiv:2304.05344, Prop. 4.3) bound ordinary-average `k`-point
correlations of 1-bounded multiplicative functions at every scale by truncated pretentious
distances.  For `G₄` itself the leading site `i^ω` is never close to constant on `[x^ε, x]`, so
the bound is empty.  For the subset constant `c_𝒫(4) = ∑_{p ∈ 𝒫} 1/(4^p − 1) = ∑_n ω_𝒫(n) 4^{-n}`
with `𝒫` of **relative density `0`** among the primes and `∑_{p ∈ 𝒫} 1/p = ∞`, every window
phase `e(h 4^{-j} ω_𝒫(n+j))` is close to `1` on `[x^ε, x]` (distance `≪ ∑_{x^ε<p≤x, p∈𝒫} 1/p → 0`)
and far from every `χ n^{it}` on `[1, x^ε]` (distance² `≫ ∑_{p ≤ x^ε, p ∈ 𝒫} 1/p → ∞`), so the
fixed-`J` window means vanish at every scale.  That is the frozen input `KMT_sparse`.

Two schedules are needed to pass from fixed `J` to `J = J_N → ∞`:
* the **tail** (L1) needs `J_N` large enough that `∑_{j>J_N} ω_𝒫(n+j) 4^{-j} → 0`; the crude bound
  `ω_𝒫 ≤ ω ≤ log₂` gives this for `windowJ N = ⌈log₂ log₂ N⌉ + 1`, the same schedule as `G₄`;
* the **KMT means** need the fixed-`J` convergence to survive `J = J_N`; the implied constant in
  Prop. 4.3 depends on `k = J`, so this is a genuine extra hypothesis, `KMT_along 𝒫 Jsched`.

`KMT_along` for `Jsched = windowJ` is what the wiring consumes.  Turning `KMT_sparse` (fixed `J`)
into `KMT_along` is the open analytic step: track the `k`-dependence of Prop 4.3 and choose `𝒫`
sparse enough (existence), or prove it for all `𝒫` with a stated sparsity rate.
-/

open Filter Topology Finset
open scoped BigOperators

namespace NormalNumbers.G4Sparse

open NormalNumbers.PrimeLambert NormalNumbers.G4

variable (S : ℕ → Prop) [DecidablePred S]

/-- The truncated subset tail `∑_{1 ≤ j ≤ J} ω_S(n+j) 4^{-j}`. -/
noncomputable def truncTailS (J n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, omegaS S (n + j + 1) / (4 : ℝ) ^ (j + 1)

/-- Prefix window mean `(1/N) ∑_{n<N} ∏_{j≤J} e(h 4^{-j} ω_S(n+j))`. -/
noncomputable def windowMeanS (J : ℕ) (h : ℤ) (N : ℕ) : ℂ :=
  prefixMean (fun n => ePhase (h * truncTailS S J n)) N

/-- `S` has relative density `0` among the primes: `#{p ≤ x : p ∈ S} / π(x) → 0`. -/
def RelDensityZero : Prop :=
  Tendsto (fun x : ℕ => ((x.primesBelow.filter S).card : ℝ) / (x.primesBelow.card : ℝ))
    atTop (𝓝 0)

/-- `∑_{p ∈ S} 1/p = ∞`. -/
def DivergentRecip : Prop :=
  ¬ Summable (fun p : ℕ => if p.Prime ∧ S p then (1 : ℝ) / p else 0)

/-- Some site `j ≤ J` carries a nontrivial phase `h 4^{-j} ∉ ℤ`.  Without this the window product
is identically `1` and the mean does not vanish. -/
def NontrivialWindow (J : ℕ) (h : ℤ) : Prop :=
  ∃ j, 1 ≤ j ∧ j ≤ J ∧ ¬ (∃ m : ℤ, (h : ℝ) / (4 : ℝ) ^ j = m)

/-- **Frozen input** (KMT 2023 Prop. 4.3 specialised: shifts `n+1, …, n+J`, `χ = 1`, `t = 0`,
fixed `J`): for `S` of relative density `0` with divergent reciprocal sum, every nontrivial
fixed-`J` window mean vanishes.  A theorem in the literature (for the stated class of `S`), not a
conjecture; the specialisation and the `k`-dependence are recorded in the design doc §5. -/
def KMT_sparse : Prop :=
  ∀ J : ℕ, ∀ h : ℤ, h ≠ 0 → NontrivialWindow J h →
    Tendsto (windowMeanS S J h) atTop (𝓝 0)

/-- The diagonal form actually consumed by the wiring: the window means vanish along a schedule
`Jsched N → ∞`.  For `Jsched = windowJ` this is `KMT_sparse` plus a rate uniform in `k = J`. -/
def KMT_along (Jsched : ℕ → ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → Tendsto (fun N => windowMeanS S (Jsched N) h N) atTop (𝓝 0)

/-- The tail is negligible in mean along the schedule (L1 for the subset weight). -/
def TailOK (Jsched : ℕ → ℕ) : Prop :=
  Tendsto (fun N : ℕ =>
    (∑ n ∈ Finset.range N, |(TWeight.subset S).tailB 4 n - truncTailS S (Jsched N) n|) / N)
    atTop (𝓝 0)

/-! ### L1 for the subset weight, by the crude bound `ω_S ≤ ω ≤ log₂` -/

/-- `|tailB n − truncTailS J n| ≤ (log₂(n + J + 2) + J + 3) / 4^J`, as for `G₄`
(`omegaS_le_omegaR` + `omegaR_le_log`). -/
theorem tail_error_le_subset (J n : ℕ) :
    |(TWeight.subset S).tailB 4 n - truncTailS S J n|
      ≤ ((Nat.log 2 (n + J + 2) : ℝ) + J + 3) / (4 : ℝ) ^ J := by
  set A : ℝ := (Nat.log 2 (n + J + 2) : ℝ) with hA
  have hsum : Summable (fun i : ℕ => omegaS S (n + i + 1) / (4 : ℝ) ^ (i + 1)) := by
    have h := TWeight.summable_tailB (W := TWeight.subset S) (b := 4) (by norm_num) n
    exact h.congr (fun i => by rw [TWeight.subset_wN]; norm_num)
  have hsplit := hsum.sum_add_tsum_nat_add J
  have hdiff : (TWeight.subset S).tailB 4 n - truncTailS S J n
      = ∑' t : ℕ, omegaS S (n + (t + J) + 1) / (4 : ℝ) ^ (t + J + 1) := by
    have htB : (TWeight.subset S).tailB 4 n
        = ∑' i : ℕ, omegaS S (n + i + 1) / (4 : ℝ) ^ (i + 1) := by
      rw [TWeight.tailB]; exact tsum_congr fun i => by rw [TWeight.subset_wN]; norm_num
    rw [htB, truncTailS, ← hsplit]
    ring
  have hterm : ∀ t : ℕ, omegaS S (n + (t + J) + 1) / (4 : ℝ) ^ (t + J + 1)
      ≤ (1 / (4 : ℝ) ^ J) * ((A + J + t) / 2 ^ (t + 1)) := by
    intro t
    rw [show n + (t + J) + 1 = n + J + t + 1 from by ring]
    have h1 : omegaS S (n + J + t + 1) ≤ (Nat.log 2 (n + J + t + 1) : ℝ) := by
      refine le_trans (omegaS_le_omegaR (S := S) _) ?_
      exact_mod_cast omegaR_le_log (n + J + t + 1)
    have h2 : (Nat.log 2 (n + J + t + 1) : ℝ) ≤ A + t := by
      have := log_add_le (n + J) t
      have hmono : Nat.log 2 (n + J + 1) ≤ Nat.log 2 (n + J + 2) :=
        Nat.log_mono_right (by omega)
      have : Nat.log 2 (n + J + t + 1) ≤ Nat.log 2 (n + J + 2) + t := by omega
      rw [hA]; exact_mod_cast this
    have hnum : omegaS S (n + J + t + 1) ≤ A + J + t := by
      have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
      linarith
    have hden : (2 : ℝ) ^ (t + 1) * 4 ^ J ≤ 4 ^ (t + J + 1) := by
      have : (2 : ℝ) ^ (t + 1) ≤ 4 ^ (t + 1) := by
        gcongr <;> norm_num
      calc (2 : ℝ) ^ (t + 1) * 4 ^ J ≤ 4 ^ (t + 1) * 4 ^ J := by gcongr
        _ = 4 ^ (t + J + 1) := by rw [← pow_add]; ring_nf
    have hnn : (0 : ℝ) ≤ A + J + t := by
      have : (0 : ℝ) ≤ A := by rw [hA]; positivity
      have : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
      have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
      positivity
    have hpos1 : (0:ℝ) < 4 ^ (t + J + 1) := by positivity
    have hpos2 : (0:ℝ) < 2 ^ (t + 1) * (4:ℝ) ^ J := by positivity
    rw [one_div, inv_mul_eq_div, div_div, div_le_div_iff₀ hpos1 hpos2]
    nlinarith [hnum, hden, hnn, omegaS_nonneg (S := S) (n + J + t + 1), hpos1.le, hpos2.le]
  have hAJ : (0 : ℝ) ≤ A + J := by
    have h1 : (0 : ℝ) ≤ A := by rw [hA]; positivity
    have h2 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
    linarith
  have hmajsum0 : Summable (fun t : ℕ => ((A + J) + (t : ℝ)) / 2 ^ (t + 1)) := by
    have := (summable_geom_shift.mul_left (A + J)).add summable_i_geom
    refine this.congr (fun i => ?_); ring
  have hmajsum : Summable (fun t : ℕ => (1 / (4 : ℝ) ^ J) * (((A + J) + (t : ℝ)) / 2 ^ (t + 1))) :=
    hmajsum0.mul_left _
  have hmaj : ∑' t : ℕ, ((A + J) + (t : ℝ)) / 2 ^ (t + 1) = A + J + 1 := by
    have h := tsum_majorant (A + J) 0
    simpa using h
  have hLsum : Summable (fun t : ℕ => omegaS S (n + (t + J) + 1) / (4 : ℝ) ^ (t + J + 1)) := by
    have := (summable_nat_add_iff J).mpr hsum
    exact this.congr (fun t => by rw [show t + J + 1 = t + J + 1 from rfl])
  have hterm' : ∀ t : ℕ, omegaS S (n + (t + J) + 1) / (4 : ℝ) ^ (t + J + 1)
      ≤ (1 / (4 : ℝ) ^ J) * (((A + J) + (t : ℝ)) / 2 ^ (t + 1)) := by
    intro t; have := hterm t; linarith [this]
  rw [hdiff, abs_of_nonneg (tsum_nonneg (fun t => by
    have := omegaS_nonneg (S := S) (n + (t + J) + 1); positivity))]
  calc ∑' t : ℕ, omegaS S (n + (t + J) + 1) / (4 : ℝ) ^ (t + J + 1)
      ≤ ∑' t : ℕ, (1 / (4 : ℝ) ^ J) * (((A + J) + (t : ℝ)) / 2 ^ (t + 1)) :=
        Summable.tsum_le_tsum hterm' hLsum hmajsum
    _ = (1 / (4 : ℝ) ^ J) * (A + J + 1) := by rw [tsum_mul_left, hmaj]
    _ ≤ (A + J + 3) / (4 : ℝ) ^ J := by
        rw [one_div, inv_mul_eq_div]
        gcongr
        linarith

/-- The crude schedule works for every `S`: `TailOK S windowJ`. -/
theorem tailOK_windowJ : TailOK S windowJ := by
  rw [TailOK]
  refine squeeze_zero' (Eventually.of_forall (fun N => ?_)) ?_ tail_error_uniform
  · exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Nat.cast_nonneg N)
  · filter_upwards [eventually_gt_atTop 0] with N hN
    set J := windowJ N with hJ
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_iff₀ hNR]
    calc ∑ n ∈ Finset.range N, |(TWeight.subset S).tailB 4 n - truncTailS S J n|
        ≤ ∑ _n ∈ Finset.range N, ((Nat.log 2 (2 * N + J + 2) : ℝ) + J + 3) / (4 : ℝ) ^ J := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          have hnlt : n < N := Finset.mem_range.mp hn
          refine le_trans (tail_error_le_subset S J n) ?_
          have hmono : Nat.log 2 (n + J + 2) ≤ Nat.log 2 (2 * N + J + 2) :=
            Nat.log_mono_right (by omega)
          have hc : (Nat.log 2 (n + J + 2) : ℝ) ≤ (Nat.log 2 (2 * N + J + 2) : ℝ) := by
            exact_mod_cast hmono
          gcongr
      _ = ((Nat.log 2 (2 * N + J + 2) : ℝ) + J + 3) / (4 : ℝ) ^ J * N := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]; ring

/-! ### Assembly (W1 + W3 directly on prefix means; no W4) -/

/-- The orbit of `c_S(4)` is the subset tail mod one (`coe_tailB` + `lambert_subset`). -/
theorem orbit_eq_fract_tailB_subset (n : ℕ) :
    orbit 4 (subsetLambert S 4) n = Int.fract ((TWeight.subset S).tailB 4 n) := by
  rw [TWeight.tailB_eq (W := TWeight.subset S) (b := 4) (by norm_num) n,
    TWeight.lambert_subset (b := 4) S]
  rw [Int.fract_sub_natCast, orbit, mul_comm]

/-- Prefix Fourier means of the orbit vanish: `TailOK` + `KMT_along`. -/
theorem prefix_fourier_tendsto_zero (Jsched : ℕ → ℕ) (hTail : TailOK S Jsched)
    (hKMT : KMT_along S Jsched) (h : ℤ) (hh : h ≠ 0) :
    Tendsto (prefixMean (fun n => ePhase (h * orbit 4 (subsetLambert S 4) n))) atTop (𝓝 0) := by
  set F : ℕ → ℂ := fun n => ePhase (h * orbit 4 (subsetLambert S 4) n) with hF
  have hFtail : ∀ n : ℕ, F n = ePhase (h * (TWeight.subset S).tailB 4 n) := by
    intro n
    have hshift : (h : ℝ) * Int.fract ((TWeight.subset S).tailB 4 n)
        = (h : ℝ) * (TWeight.subset S).tailB 4 n
          + ((-(h * ⌊(TWeight.subset S).tailB 4 n⌋) : ℤ) : ℝ) := by
      rw [Int.fract]; push_cast; ring
    rw [hF]
    simp only
    rw [orbit_eq_fract_tailB_subset, hshift, ePhase_add_int]
  have hgoal : Tendsto (fun N => prefixMean F N - windowMeanS S (Jsched N) h N) atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
      (g := fun N : ℕ => 4 * Real.pi * |(h : ℝ)| *
        ((∑ n ∈ Finset.range N,
            |(TWeight.subset S).tailB 4 n - truncTailS S (Jsched N) n|) / N)) ?_
      (by simpa using hTail.const_mul (4 * Real.pi * |(h : ℝ)|))
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    set J := Jsched N with hJ
    have hsub : prefixMean F N - windowMeanS S J h N
        = (∑ n ∈ Finset.range N,
            (ePhase (h * (TWeight.subset S).tailB 4 n) - ePhase (h * truncTailS S J n))) / N := by
      rw [prefixMean, windowMeanS, prefixMean, ← sub_div, ← Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_congr rfl (fun n _ => by rw [hFtail n])
    rw [hsub, norm_div, Complex.norm_natCast]
    rw [div_le_iff₀ hNR, mul_assoc, div_mul_cancel₀ _ (ne_of_gt hNR)]
    calc ‖∑ n ∈ Finset.range N,
            (ePhase (h * (TWeight.subset S).tailB 4 n) - ePhase (h * truncTailS S J n))‖
        ≤ ∑ n ∈ Finset.range N,
            ‖ePhase (h * (TWeight.subset S).tailB 4 n) - ePhase (h * truncTailS S J n)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range N, 4 * Real.pi * |(h : ℝ)| *
            |(TWeight.subset S).tailB 4 n - truncTailS S J n| := by
          refine Finset.sum_le_sum (fun n _ => ?_)
          calc ‖ePhase (h * (TWeight.subset S).tailB 4 n) - ePhase (h * truncTailS S J n)‖
              ≤ 4 * Real.pi *
                  |(h : ℝ) * (TWeight.subset S).tailB 4 n - (h : ℝ) * truncTailS S J n| :=
                norm_ePhase_sub _ _
            _ = 4 * Real.pi * |(h : ℝ)| *
                  |(TWeight.subset S).tailB 4 n - truncTailS S J n| := by
                rw [← mul_sub, abs_mul]; ring
      _ = 4 * Real.pi * |(h : ℝ)| *
            ∑ n ∈ Finset.range N, |(TWeight.subset S).tailB 4 n - truncTailS S J n| := by
          rw [Finset.mul_sum]
  have := (hKMT h hh).add hgoal
  simpa using this

/-- **Wiring theorem**: normality of `c_S(4)` from the diagonal KMT input along any schedule with a
negligible tail. -/
theorem isNormal_subsetLambert_of_KMT_along (Jsched : ℕ → ℕ) (hTail : TailOK S Jsched)
    (hKMT : KMT_along S Jsched) : IsNormal 4 (subsetLambert S 4) := by
  rw [isNormal_iff_equidistributed_orbit 4 (by norm_num)]
  refine equidistributed_of_weyl _ (orbit_mem_Ico 4 _) ?_
  intro h hh
  have hpre := prefix_fourier_tendsto_zero S Jsched hTail hKMT h hh
  have heq : fourierMean (orbit 4 (subsetLambert S 4)) h
      = prefixMean (fun n => ePhase (h * orbit 4 (subsetLambert S 4) n)) := by
    funext n
    rw [fourierMean, prefixMean]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [ePhase]
    congr 1
    push_cast
    ring
  rw [heq]
  exact hpre

/-- Specialised to the crude schedule: only the diagonal KMT input remains. -/
theorem isNormal_subsetLambert_of_KMT_windowJ (hKMT : KMT_along S windowJ) :
    IsNormal 4 (subsetLambert S 4) :=
  isNormal_subsetLambert_of_KMT_along S windowJ (tailOK_windowJ S) hKMT

/-! ### The existence statement -/

/-! ### Sub-leaves for `exists_relDensityZero_divergent` (the π-indexed construction)

`m k = log₂ log₂ k + 1`; keep the `k`-th prime (0-indexed, `k = π'(p) = #{q < p : q prime}`)
exactly when `m k ∣ k`.  Density is combinatorial in `k`; divergence needs only Chebyshev's
lower bound through `nth_prime_le_mul_log`. -/

namespace SparseExists

open Nat

/-- The slowly growing modulus `m k = log₂ log₂ k + 1`; constant `= μ a` on the dyadic block
`[2^a, 2^{a+1})`, where `μ a = log₂ a + 1`. -/
def mu (a : ℕ) : ℕ := Nat.log 2 a + 1

/-- `m k = μ (log₂ k)`. -/
def modulus (k : ℕ) : ℕ := mu (Nat.log 2 k)

/-- The index set `A = {k : m k ∣ k}`. -/
def Keep (k : ℕ) : Prop := modulus k ∣ k

instance : DecidablePred Keep := fun k => inferInstanceAs (Decidable (modulus k ∣ k))

/-- The prime subset: keep the `k`-th prime iff `k ∈ A`. -/
def PSet (p : ℕ) : Prop := p.Prime ∧ Keep (Nat.count Nat.Prime p)

instance : DecidablePred PSet := fun p =>
  inferInstanceAs (Decidable (p.Prime ∧ Keep (Nat.count Nat.Prime p)))

/-! #### (a) the Chebyshev input: `p_k ≤ 20 k log k` -/

/-- `π (p_k) = k + 1`. -/
theorem primeCounting_nth_prime (k : ℕ) : Nat.primeCounting (Nat.nth Nat.Prime k) = k + 1 := by
  rw [Nat.primeCounting_eq_primeCounting'_succ, Nat.primeCounting', Nat.count_succ]
  simp [Nat.prime_nth_prime k]
  exact Nat.primeCounting'_nth_eq k

/-- Chebyshev's lower bound, read at `p = p_k`: `p log 2 ≤ (k+3) log p`. -/
theorem nth_prime_mul_log_two_le (k : ℕ) :
    (Nat.nth Nat.Prime k : ℝ) * Real.log 2 ≤ ((k : ℝ) + 3) * Real.log (Nat.nth Nat.Prime k) := by
  set p := Nat.nth Nat.Prime k with hp
  have hp2 : 2 ≤ p := (Nat.prime_nth_prime k).two_le
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hlogpos : 0 < Real.log p := Real.log_pos (by linarith)
  have hche := Chebyshev.pi_ge p
  rw [primeCounting_nth_prime k] at hche
  have h1 : ((p : ℝ) * Real.log 2 - Real.log ((p : ℝ) + 1)) ≤ ((k : ℝ) + 1) * Real.log p := by
    rw [div_le_iff₀ hlogpos] at hche
    push_cast at hche ⊢
    linarith
  have h2 : Real.log ((p : ℝ) + 1) ≤ 2 * Real.log p := by
    have hsq : ((p : ℝ) + 1) ≤ (p : ℝ) ^ 2 := by nlinarith
    calc Real.log ((p : ℝ) + 1) ≤ Real.log ((p : ℝ) ^ 2) := Real.log_le_log (by linarith) hsq
      _ = 2 * Real.log p := by rw [Real.log_pow]; push_cast; ring
  linarith

/-- Crude self-bounding consequence: `p_k ≤ 9 (k+3)²`. -/
theorem nth_prime_le_sq (k : ℕ) : (Nat.nth Nat.Prime k : ℝ) ≤ 9 * ((k : ℝ) + 3) ^ 2 := by
  set p := Nat.nth Nat.Prime k with hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_nth_prime k).two_le
  have hs : Real.sqrt p * Real.sqrt p = (p : ℝ) := Real.mul_self_sqrt (by linarith)
  have hspos : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
  have hlog : Real.log p ≤ 2 * Real.sqrt p := by
    have h1 : Real.log (Real.sqrt p) ≤ Real.sqrt p - 1 := Real.log_le_sub_one_of_pos hspos
    have h2 : Real.log (Real.sqrt p) = Real.log p / 2 := Real.log_sqrt (by linarith)
    linarith [h2 ▸ h1]
  have h2 := Real.log_two_gt_d9
  have hst := nth_prime_mul_log_two_le k
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hsle : Real.sqrt p ≤ 3 * ((k : ℝ) + 3) := by nlinarith [hst, hlog, hs, hspos]
  nlinarith [hs, hsle, hspos]

/-- **(a)** `p_k ≤ 20 k log k` for `k ≥ 16`, from `Chebyshev.pi_ge` alone. -/
theorem nth_prime_le_mul_log (k : ℕ) (hk : 16 ≤ k) :
    (Nat.nth Nat.Prime k : ℝ) ≤ 20 * k * Real.log k := by
  set p := Nat.nth Nat.Prime k with hp
  have hkR : (16 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_nth_prime k).two_le
    linarith
  have hlogk : 2.7 ≤ Real.log k := by
    have hle : Real.log 16 ≤ Real.log k := Real.log_le_log (by norm_num) (by linarith)
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    linarith [h16 ▸ hle]
  have h9 : Real.log 9 ≤ 2 * Real.log k := by
    have hle : Real.log 9 ≤ Real.log ((k : ℝ) ^ 2) := Real.log_le_log (by norm_num) (by nlinarith)
    rw [Real.log_pow] at hle; push_cast at hle; linarith
  have hk3 : Real.log ((k : ℝ) + 3) ≤ Real.log 2 + Real.log k := by
    have h : Real.log ((k : ℝ) + 3) ≤ Real.log (2 * (k : ℝ)) :=
      Real.log_le_log (by linarith) (by linarith)
    rwa [Real.log_mul (by norm_num) (by linarith)] at h
  have hple := nth_prime_le_sq k
  have hlp : Real.log p ≤ 4.6 * Real.log k := by
    have hmono : Real.log p ≤ Real.log (9 * ((k : ℝ) + 3) ^ 2) := Real.log_le_log hppos hple
    have hexp : Real.log (9 * ((k : ℝ) + 3) ^ 2) = Real.log 9 + 2 * Real.log ((k : ℝ) + 3) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    rw [hexp] at hmono
    linarith
  have hst := nth_prime_mul_log_two_le k
  nlinarith [hst, hlp, hlogk, h2, hkR]

theorem mu_pos (a : ℕ) : 0 < mu a := Nat.succ_pos _

/-! #### (b) the density count -/

/-- Multiples of `M` in `[x, y)`: at most `(y-x)/M + 2`. -/
theorem card_multiples_le (M x y : ℕ) (hM : 0 < M) (hxy : x ≤ y) :
    (((Finset.Ico x y).filter (fun k => M ∣ k)).card : ℝ) ≤ ((y : ℝ) - x) / M + 2 := by
  have hmap : ∀ k ∈ (Finset.Ico x y).filter (fun k => M ∣ k), k / M ∈ Finset.Icc (x / M) (y / M) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Ico] at hk
    exact Finset.mem_Icc.mpr ⟨Nat.div_le_div_right hk.1.1, Nat.div_le_div_right hk.1.2.le⟩
  have hinj : Set.InjOn (fun k => k / M) ((Finset.Ico x y).filter (fun k => M ∣ k) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
    have ha' : M * (a / M) = a := Nat.mul_div_cancel' ha.2
    have hb' : M * (b / M) = b := Nat.mul_div_cancel' hb.2
    simp only at hab
    rw [← ha', ← hb', hab]
  have hcard := Finset.card_le_card_of_injOn (fun k => k / M) hmap hinj
  rw [Nat.card_Icc] at hcard
  have hMR : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have h1 : ((y / M : ℕ) : ℝ) ≤ (y : ℝ) / M := by
    rw [le_div_iff₀ hMR]
    have := Nat.div_mul_le_self y M
    exact_mod_cast this
  have h2 : (x : ℝ) / M - 1 ≤ ((x / M : ℕ) : ℝ) := by
    have hdm := Nat.div_add_mod x M
    have hmod := Nat.mod_lt x hM
    have hx : x < (x / M + 1) * M := by nlinarith [hdm, hmod]
    have hxR : (x : ℝ) < (((x / M : ℕ) : ℝ) + 1) * M := by
      have := (Nat.cast_lt (α := ℝ)).mpr hx
      push_cast at this
      linarith
    rw [sub_le_iff_le_add, div_le_iff₀ hMR]
    linarith
  have hle : x / M ≤ y / M + 1 := le_trans (Nat.div_le_div_right hxy) (by omega)
  have hc : (((Finset.Ico x y).filter (fun k => M ∣ k)).card : ℝ)
      ≤ ((y / M : ℕ) : ℝ) - ((x / M : ℕ) : ℝ) + 1 := by
    have hcast := (Nat.cast_le (α := ℝ)).mpr hcard
    rw [Nat.cast_sub hle] at hcast
    push_cast at hcast
    linarith
  have hdiv : ((y:ℝ) - x) / M = (y:ℝ)/M - (x:ℝ)/M := by ring
  linarith

theorem keepCount_le (m₀ K : ℕ) (hm : 0 < m₀) (hK : 1 ≤ K) :
    ((((Finset.range K).filter Keep).card : ℝ))
      ≤ (2 : ℝ) ^ (2 ^ (m₀ - 1)) + 2 * K / m₀ + 2 * (Nat.log 2 K + 1) := by
  set a₀ := 2 ^ (m₀ - 1) with ha₀
  set L := Nat.log 2 K with hL
  have hmR : (0:ℝ) < (m₀:ℝ) := by exact_mod_cast hm
  -- covering
  have hsub : (Finset.range K).filter Keep ⊆ (Finset.range (2 ^ a₀)) ∪
      (Finset.Ico a₀ (L + 1)).biUnion
        (fun a => (Finset.Ico (2 ^ a) (2 ^ (a + 1))).filter (fun k => mu a ∣ k)) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkK, hkeep⟩ := hk
    by_cases hsmall : k < 2 ^ a₀
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr hsmall)
    · push_neg at hsmall
      have hk0 : k ≠ 0 := by
        have : 0 < 2 ^ a₀ := Nat.two_pow_pos a₀
        omega
      set a := Nat.log 2 k with ha
      have hlow : 2 ^ a ≤ k := Nat.pow_log_le_self 2 hk0
      have hhigh : k < 2 ^ (a + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
      have haa₀ : a₀ ≤ a := Nat.le_log_of_pow_le (by norm_num) hsmall
      have haL : a ≤ L := Nat.log_mono_right (by omega)
      refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a, Finset.mem_Ico.mpr ⟨haa₀, by omega⟩, ?_⟩)
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hlow, hhigh⟩, ?_⟩
      have : modulus k = mu a := by rw [modulus, ha]
      rw [Keep, this] at hkeep
      exact hkeep
  have hcard1 := Finset.card_le_card hsub
  have hcard2 := (Finset.card_union_le (Finset.range (2 ^ a₀))
    ((Finset.Ico a₀ (L + 1)).biUnion
      (fun a => (Finset.Ico (2 ^ a) (2 ^ (a + 1))).filter (fun k => mu a ∣ k))))
  have hcard3 := Finset.card_biUnion_le (s := Finset.Ico a₀ (L + 1))
    (t := fun a => (Finset.Ico (2 ^ a) (2 ^ (a + 1))).filter (fun k => mu a ∣ k))
  have hchain : ((((Finset.range K).filter Keep).card : ℝ)) ≤ ((2 ^ a₀ : ℕ) : ℝ) +
      ∑ a ∈ Finset.Ico a₀ (L + 1),
        (((Finset.Ico (2 ^ a) (2 ^ (a + 1))).filter (fun k => mu a ∣ k)).card : ℝ) := by
    have h : ((Finset.range K).filter Keep).card ≤ 2 ^ a₀ +
        ∑ a ∈ Finset.Ico a₀ (L + 1),
          ((Finset.Ico (2 ^ a) (2 ^ (a + 1))).filter (fun k => mu a ∣ k)).card := by
      refine (hcard1.trans hcard2).trans ?_
      rw [Finset.card_range]
      exact Nat.add_le_add_left hcard3 _
    have := (Nat.cast_le (α := ℝ)).mpr h
    push_cast at this ⊢
    simpa using this
  -- each block
  have hblock : ∀ a ∈ Finset.Ico a₀ (L + 1),
      (((Finset.Ico (2 ^ a) (2 ^ (a + 1))).filter (fun k => mu a ∣ k)).card : ℝ)
        ≤ (2 : ℝ) ^ a / m₀ + 2 := by
    intro a ha
    rw [Finset.mem_Ico] at ha
    have ha0 : a ≠ 0 := by
      have : 0 < a₀ := Nat.two_pow_pos _
      omega
    have hmu : m₀ ≤ mu a := by
      have : m₀ - 1 ≤ Nat.log 2 a := Nat.le_log_of_pow_le (by norm_num) ha.1
      rw [mu]; omega
    have hle := card_multiples_le (mu a) (2 ^ a) (2 ^ (a + 1)) (mu_pos a)
      (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hdiff : ((2 ^ (a + 1) : ℕ) : ℝ) - ((2 ^ a : ℕ) : ℝ) = (2 : ℝ) ^ a := by
      push_cast; ring
    rw [hdiff] at hle
    refine hle.trans ?_
    have hmuR : (m₀ : ℝ) ≤ (mu a : ℝ) := by exact_mod_cast hmu
    have : (2 : ℝ) ^ a / (mu a) ≤ (2 : ℝ) ^ a / m₀ := by
      apply div_le_div_of_nonneg_left (by positivity) hmR hmuR
    linarith
  have hsum := Finset.sum_le_sum hblock
  -- the geometric sum
  have hgeo : ∑ a ∈ Finset.Ico a₀ (L + 1), ((2 : ℝ) ^ a / m₀ + 2)
      ≤ 2 * K / m₀ + 2 * (L + 1) := by
    have hsub2 : Finset.Ico a₀ (L + 1) ⊆ Finset.range (L + 1) := by
      intro a ha; rw [Finset.mem_Ico] at ha; exact Finset.mem_range.mpr ha.2
    have hnn : ∀ a, (0:ℝ) ≤ (2 : ℝ) ^ a / m₀ + 2 := by intro a; positivity
    have h1 : ∑ a ∈ Finset.Ico a₀ (L + 1), ((2 : ℝ) ^ a / m₀ + 2)
        ≤ ∑ a ∈ Finset.range (L + 1), ((2 : ℝ) ^ a / m₀ + 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun i _ _ => hnn i)
    have h2 : ∑ a ∈ Finset.range (L + 1), ((2 : ℝ) ^ a / m₀ + 2)
        = (∑ a ∈ Finset.range (L + 1), (2 : ℝ) ^ a) / m₀ + 2 * (L + 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const, Finset.card_range]
      push_cast
      ring
    have h3 : ∑ a ∈ Finset.range (L + 1), (2 : ℝ) ^ a = 2 ^ (L + 1) - 1 := by
      rw [geom_sum_eq (by norm_num)]
      ring
    have h4 : (2 : ℝ) ^ (L + 1) ≤ 2 * K := by
      have : (2 : ℕ) ^ L ≤ K := Nat.pow_log_le_self 2 (by omega)
      have := (Nat.cast_le (α := ℝ)).mpr this
      push_cast at this
      have : (2:ℝ) ^ (L + 1) = 2 * 2 ^ L := by ring
      nlinarith [this, (Nat.cast_le (α := ℝ)).mpr (Nat.pow_log_le_self 2 (show K ≠ 0 by omega))]
    rw [h2, h3] at h1
    have : ((2:ℝ) ^ (L+1) - 1) / m₀ ≤ 2 * K / m₀ := by
      apply div_le_div_of_nonneg_right _ hmR.le
      linarith
    linarith
  linarith [hchain, hsum, hgeo, (by push_cast; ring_nf : ((2 ^ a₀ : ℕ) : ℝ) = (2:ℝ) ^ a₀)]

theorem tendsto_natLog_div :
    Filter.Tendsto (fun K : ℕ => ((Nat.log 2 K : ℝ) + 1) / K) Filter.atTop (𝓝 0) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hinv : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  have hcomb : Tendsto (fun x : ℝ => (1 / Real.log 2) * (Real.log x / x) + 1 / x) atTop (𝓝 0) := by
    have := (hdiv.const_mul (1 / Real.log 2)).add hinv
    simpa using this
  have hnat : Tendsto (fun K : ℕ => (1 / Real.log 2) * (Real.log K / K) + 1 / (K:ℝ))
      atTop (𝓝 0) := hcomb.comp tendsto_natCast_atTop_atTop
  refine squeeze_zero' ?_ ?_ hnat
  · filter_upwards [eventually_ge_atTop 1] with K hK
    positivity
  · filter_upwards [eventually_ge_atTop 1] with K hK
    have hKR : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
    have hKpos : (0:ℝ) < (K:ℝ) := by linarith
    have hL : ((Nat.log 2 K : ℝ)) ≤ Real.log K / Real.log 2 := by
      have h2 : (2:ℕ) ^ Nat.log 2 K ≤ K := Nat.pow_log_le_self 2 (by omega)
      have h2R : (2:ℝ) ^ (Nat.log 2 K) ≤ (K:ℝ) := by exact_mod_cast h2
      have := Real.log_le_log (by positivity) h2R
      rw [Real.log_pow] at this
      rw [le_div_iff₀ hlog2]
      linarith
    rw [div_le_iff₀ hKpos]
    have hexp : ((1 / Real.log 2) * (Real.log K / K) + 1 / (K:ℝ)) * K
        = Real.log K / Real.log 2 + 1 := by
      field_simp
    rw [hexp]
    linarith

theorem tendsto_keepCount_div : Filter.Tendsto
    (fun K : ℕ => ((((Finset.range K).filter Keep).card : ℝ)) / K) Filter.atTop (𝓝 0) := by
  refine tendsto_order.mpr ⟨fun a ha => ?_, fun ε hε => ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with K hK
    have : (0:ℝ) ≤ ((((Finset.range K).filter Keep).card : ℝ)) / K := by positivity
    linarith
  · set m₀ := ⌈8 / ε⌉₊ + 1 with hm₀
    have hm₀pos : 0 < m₀ := by omega
    have hm₀R : (8 / ε) ≤ (m₀ : ℝ) := by
      have := Nat.le_ceil (8 / ε)
      rw [hm₀]
      push_cast
      linarith
    have hm₀R' : (0:ℝ) < (m₀ : ℝ) := by exact_mod_cast hm₀pos
    have hfrac : 2 / (m₀ : ℝ) ≤ ε / 4 := by
      rw [div_le_div_iff₀ hm₀R' (by norm_num)]
      have h8 : 8 ≤ ε * m₀ := by
        rw [div_le_iff₀ hε] at hm₀R
        linarith
      linarith
    set c : ℝ := (2 : ℝ) ^ (2 ^ (m₀ - 1)) with hc
    have h1 : Tendsto (fun K : ℕ => c / (K:ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat c
    have h2 : Tendsto (fun K : ℕ => 2 * (((Nat.log 2 K : ℝ) + 1) / K)) atTop (𝓝 0) := by
      have := tendsto_natLog_div.const_mul 2
      simpa using this
    have hadd : Tendsto (fun K : ℕ => c / (K:ℝ) + 2 * (((Nat.log 2 K : ℝ) + 1) / K))
        atTop (𝓝 0) := by simpa using h1.add h2
    have hsmall := hadd.eventually_lt_const (show (0:ℝ) < ε / 2 by linarith)
    filter_upwards [hsmall, eventually_ge_atTop 1] with K hKs hK1
    have hKpos : (0:ℝ) < (K:ℝ) := by
      have : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK1
      linarith
    have hb := keepCount_le m₀ K hm₀pos hK1
    rw [div_lt_iff₀ hKpos]
    have hexp : c / K + 2 * (((Nat.log 2 K : ℝ) + 1) / K) < ε / 2 := hKs
    have hlt : c + 2 * ((Nat.log 2 K : ℝ) + 1) < (ε / 2) * K := by
      have heq : c / K + 2 * (((Nat.log 2 K : ℝ) + 1) / K)
          = (c + 2 * ((Nat.log 2 K : ℝ) + 1)) / K := by field_simp
      rw [heq, div_lt_iff₀ hKpos] at hexp
      linarith
    calc ((((Finset.range K).filter Keep).card : ℝ))
        ≤ c + 2 * K / m₀ + 2 * ((Nat.log 2 K : ℝ) + 1) := by
          rw [hc]; push_cast at hb ⊢; linarith
      _ < (ε / 2) * K + 2 * K / m₀ := by linarith
      _ ≤ ε * K := by
          have : 2 * (K:ℝ) / m₀ = (2 / m₀) * K := by ring
          rw [this]
          nlinarith [hfrac, hKpos]

/-! #### (c) the divergent harmonic sum along `A` -/

/-- The harmonic weight along `A`: `1/(k log k)` on `A`, `0` off it. -/
noncomputable def harm (k : ℕ) : ℝ := if Keep k then 1 / ((k : ℝ) * Real.log k) else 0

theorem harm_nonneg (k : ℕ) : 0 ≤ harm k := by
  unfold harm
  split
  · positivity
  · exact le_rfl


/-- On the dyadic block `[2^a, 2^{a+1})` the modulus is constant `= μ a`. -/
theorem modulus_eq_of_mem (a k : ℕ) (h1 : 2 ^ a ≤ k) (h2 : k < 2 ^ (a + 1)) :
    modulus k = mu a := by
  have : Nat.log 2 k = a := by
    rw [Nat.log_eq_iff (by omega)]
    exact ⟨h1, h2⟩
  rw [modulus, this]


/-- Lower bound on the number of multiples of `M` inside the dyadic block. -/
theorem card_block (a : ℕ) :
    ((2 ^ a : ℝ)) / (mu a) - 3 ≤
      ((Finset.Ico (2 ^ a / mu a + 1) (2 ^ (a + 1) / mu a)).card : ℝ) := by
  set M := mu a with hM
  have hMpos : 0 < M := mu_pos a
  have hpow : (2:ℕ) ^ (a + 1) = 2 ^ a * 2 := pow_succ 2 a
  set q := 2 ^ a / M with hq
  set A := q + 1 with hA
  have hdm := Nat.div_add_mod (2 ^ a) M
  have hmod := Nat.mod_lt (2 ^ a) hMpos
  have hkey : A + q ≤ 2 ^ a * 2 / M + 2 := by
    have h3 : 2 * 2 ^ a = 2 ^ a * 2 := by ring
    have h2 : 2 * (2 ^ a / M) ≤ 2 ^ a * 2 / M := by
      rw [← h3]; exact Nat.mul_div_le_mul_div_assoc 2 (2 ^ a) M
    omega
  rw [hpow]
  have hcard : (Finset.Ico A (2 ^ a * 2 / M)).card = 2 ^ a * 2 / M - A := Nat.card_Ico _ _
  have hnat : q ≤ (Finset.Ico A (2 ^ a * 2 / M)).card + 2 := by omega
  have hqr : ((2 : ℝ) ^ a) / M ≤ (q : ℝ) + 1 := by
    have hMR : (0:ℝ) < (M:ℝ) := by exact_mod_cast hMpos
    have hlt : (2:ℕ) ^ a < (q + 1) * M := by nlinarith [hdm, hmod]
    have hlt' := (Nat.cast_lt (α := ℝ)).mpr hlt
    rw [div_le_iff₀ hMR]
    push_cast at hlt' ⊢
    nlinarith [hlt']
  have hc := (Nat.cast_le (α := ℝ)).mpr hnat
  push_cast at hc
  linarith

theorem block_sum (a : ℕ) (ha : 1 ≤ a) :
    ((2 : ℝ) ^ a / (mu a) - 3) * (1 / ((2 : ℝ) ^ (a + 1) * ((a + 1) * Real.log 2)))
      ≤ ∑ k ∈ (Finset.Ico (2 ^ a) (2 ^ (a + 1))).filter Keep, harm k := by
  set M := mu a with hM
  have hMpos : 0 < M := mu_pos a
  set A := 2 ^ a / M + 1 with hA
  set B := 2 ^ (a + 1) / M with hB
  have hdm := Nat.div_add_mod (2 ^ a) M
  have hmod := Nat.mod_lt (2 ^ a) hMpos
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set w : ℝ := 1 / ((2 : ℝ) ^ (a + 1) * ((a + 1) * Real.log 2)) with hw
  have hwpos : 0 < w := by rw [hw]; positivity
  -- membership
  have hmem : ∀ j ∈ Finset.Ico A B, M * j ∈ (Finset.Ico (2 ^ a) (2 ^ (a + 1))).filter Keep := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hlow : 2 ^ a ≤ M * j := by
      have : M * A ≤ M * j := Nat.mul_le_mul_left M hj.1
      have hMA : 2 ^ a < M * A := by
        rw [hA]; nlinarith [hdm, hmod]
      omega
    have hhigh : M * j < 2 ^ (a + 1) := by
      have hMB : M * B ≤ 2 ^ (a + 1) := Nat.mul_div_le _ _ |>.trans_eq rfl
      have : M * j ≤ M * (B - 1) := Nat.mul_le_mul_left M (by omega)
      have hB1 : M * (B - 1) + M = M * B := by
        have h1B : 1 ≤ B := by omega
        have hle : M ≤ M * B := Nat.le_mul_of_pos_right M (by omega)
        rw [Nat.mul_sub, Nat.mul_one]; omega
      omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hlow, hhigh⟩, ?_⟩
    have : modulus (M * j) = M := modulus_eq_of_mem a _ hlow hhigh
    rw [Keep, this]
    exact Dvd.intro j rfl
  have hinj : Set.InjOn (fun j => M * j) (Finset.Ico A B : Set ℕ) := by
    intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_left hMpos hxy
  have hsub : ((Finset.Ico A B).image (fun j => M * j)) ⊆
      (Finset.Ico (2 ^ a) (2 ^ (a + 1))).filter Keep := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨j, hj, rfl⟩ := hk
    exact hmem j hj
  have h1 : ∑ k ∈ (Finset.Ico A B).image (fun j => M * j), harm k
      ≤ ∑ k ∈ (Finset.Ico (2 ^ a) (2 ^ (a + 1))).filter Keep, harm k :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => harm_nonneg i)
  have h2 : ∑ k ∈ (Finset.Ico A B).image (fun j => M * j), harm k
      = ∑ j ∈ Finset.Ico A B, harm (M * j) := Finset.sum_image (by
        intro x hx y hy hxy; exact hinj hx hy hxy)
  have h3 : ∀ j ∈ Finset.Ico A B, w ≤ harm (M * j) := by
    intro j hj
    have hk := hmem j hj
    rw [Finset.mem_filter, Finset.mem_Ico] at hk
    obtain ⟨⟨hlow, hhigh⟩, hkeep⟩ := hk
    have h2a : (2:ℕ) ≤ M * j := le_trans (by
      calc (2:ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha) hlow
    have hkR : (2:ℝ) ≤ (M * j : ℕ) := by exact_mod_cast h2a
    have hkR2 : ((M * j : ℕ) : ℝ) ≤ (2:ℝ) ^ (a + 1) := by
      have := hhigh.le
      have : ((M * j : ℕ) : ℝ) ≤ ((2 ^ (a+1) : ℕ) : ℝ) := by exact_mod_cast hhigh.le
      simpa using this
    have hlogle : Real.log (M * j : ℕ) ≤ (a + 1) * Real.log 2 := by
      have hx := Real.log_le_log (by linarith) hkR2
      rw [Real.log_pow] at hx; push_cast at hx ⊢; exact hx
    have hlogpos : 0 < Real.log (M * j : ℕ) := Real.log_pos (by linarith)
    rw [harm, if_pos hkeep, hw]
    apply one_div_le_one_div_of_le (by positivity)
    have : (0:ℝ) < ((M*j : ℕ) : ℝ) := by linarith
    nlinarith [hlogle, hkR2, hlogpos]
  calc ((2 : ℝ) ^ a / M - 3) * w
      ≤ ((Finset.Ico A B).card : ℝ) * w := by
        have := card_block a
        nlinarith [hwpos, this]
    _ = ∑ _j ∈ Finset.Ico A B, w := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ Finset.Ico A B, harm (M * j) := Finset.sum_le_sum h3
    _ = _ := h2.symm
    _ ≤ _ := h1

noncomputable def F (a : ℕ) : ℝ := ∑ k ∈ (Finset.Ico (2 ^ a) (2 ^ (a + 1))).filter Keep, harm k

theorem F_nonneg (a : ℕ) : 0 ≤ F a := Finset.sum_nonneg (fun i _ => harm_nonneg i)

theorem two_mul_le_two_pow (t : ℕ) : 2 * t ≤ 2 ^ t := by
  induction t with
  | zero => norm_num
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · norm_num
      · have : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
        omega

/-- Super-block bound: over the `a`-range `[2^t, 2^{t+1})` the modulus is `t+1`. -/
theorem superblock (t : ℕ) :
    1 / (4 * ((t : ℝ) + 1) * Real.log 2) - (3 / Real.log 2) * (1 / 2 ^ (t + 1))
      ≤ ∑ a ∈ Finset.Ico (2 ^ t) (2 ^ (t + 1)), F a := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set N := 2 ^ t with hN
  have hNpos : 0 < N := Nat.two_pow_pos t
  have hmu : ∀ a ∈ Finset.Ico N (2 ^ (t+1)), mu a = t + 1 := by
    intro a ha
    rw [Finset.mem_Ico] at ha
    have : Nat.log 2 a = t := by
      rw [Nat.log_eq_iff (by omega)]
      exact ⟨ha.1, ha.2⟩
    rw [mu, this]
  have hlow : ∀ a ∈ Finset.Ico N (2 ^ (t+1)),
      1 / (2 * ((t:ℝ)+1) * ((a:ℝ)+1) * Real.log 2) - 3 / ((2:ℝ) ^ (a+1) * (((a:ℝ)+1) * Real.log 2))
        ≤ F a := by
    intro a ha
    have ha1 : 1 ≤ a := by
      rw [Finset.mem_Ico] at ha; omega
    have hb := block_sum a ha1
    rw [hmu a ha] at hb
    refine le_trans (le_of_eq ?_) hb
    have h1 : ((t:ℕ) + 1 : ℕ) = ((t:ℝ) + 1) := by push_cast; ring
    push_cast
    field_simp
    ring
  refine le_trans ?_ (Finset.sum_le_sum hlow)
  rw [Finset.sum_sub_distrib]
  have hA : 1 / (4 * ((t : ℝ) + 1) * Real.log 2)
      ≤ ∑ a ∈ Finset.Ico N (2 ^ (t+1)), 1 / (2 * ((t:ℝ)+1) * ((a:ℝ)+1) * Real.log 2) := by
    have hterm : ∀ a ∈ Finset.Ico N (2 ^ (t+1)),
        1 / (2 * ((t:ℝ)+1) * (2 * (N:ℝ)) * Real.log 2)
          ≤ 1 / (2 * ((t:ℝ)+1) * ((a:ℝ)+1) * Real.log 2) := by
      intro a ha
      rw [Finset.mem_Ico] at ha
      have haR : ((a:ℝ) + 1) ≤ 2 * (N:ℝ) := by
        have : a + 1 ≤ 2 ^ (t+1) := by omega
        have := (Nat.cast_le (α := ℝ)).mpr this
        rw [hN]
        have hps : (2:ℝ) ^ (t+1) = 2 * 2 ^ t := by ring
        push_cast at this ⊢
        linarith [this, hps]
      have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
      have haR0 : (0:ℝ) < (a:ℝ) + 1 := by positivity
      apply one_div_le_one_div_of_le (by positivity)
      have hc : (0:ℝ) ≤ 2 * ((t:ℝ)+1) * Real.log 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left haR hc]
    have hcard : (Finset.Ico N (2 ^ (t+1))).card = N := by
      rw [Nat.card_Ico, hN]
      have : (2:ℕ) ^ (t+1) = 2 * 2 ^ t := by ring
      omega
    have := Finset.card_nsmul_le_sum (Finset.Ico N (2 ^ (t+1)))
      (fun a => 1 / (2 * ((t:ℝ)+1) * ((a:ℝ)+1) * Real.log 2))
      (1 / (2 * ((t:ℝ)+1) * (2 * (N:ℝ)) * Real.log 2)) hterm
    rw [hcard, nsmul_eq_mul] at this
    refine le_trans (le_of_eq ?_) this
    have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
    field_simp
    ring
  have hB : ∑ a ∈ Finset.Ico N (2 ^ (t+1)),
      3 / ((2:ℝ) ^ (a+1) * (((a:ℝ)+1) * Real.log 2)) ≤ (3 / Real.log 2) * (1 / 2 ^ (t + 1)) := by
    have hterm : ∀ a ∈ Finset.Ico N (2 ^ (t+1)),
        3 / ((2:ℝ) ^ (a+1) * (((a:ℝ)+1) * Real.log 2)) ≤ 3 / ((2:ℝ) ^ (N+1) * Real.log 2) := by
      intro a ha
      rw [Finset.mem_Ico] at ha
      have hpow : ((2:ℝ) ^ (N+1)) ≤ (2:ℝ) ^ (a+1) := by
        apply pow_le_pow_right₀ (by norm_num); omega
      have ha0 : (1:ℝ) ≤ (a:ℝ) + 1 := by
        have : (0:ℝ) ≤ (a:ℝ) := Nat.cast_nonneg a
        linarith
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have h1 : (2:ℝ) ^ (N+1) * 1 ≤ 2 ^ (a+1) * ((a:ℝ)+1) :=
        mul_le_mul hpow ha0 (by norm_num) (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right h1 hlog2.le]
    have hcard : (Finset.Ico N (2 ^ (t+1))).card = N := by
      rw [Nat.card_Ico, hN]
      have : (2:ℕ) ^ (t+1) = 2 * 2 ^ t := by ring
      omega
    have hsum := Finset.sum_le_card_nsmul (Finset.Ico N (2 ^ (t+1)))
      (fun a => 3 / ((2:ℝ) ^ (a+1) * (((a:ℝ)+1) * Real.log 2)))
      (3 / ((2:ℝ) ^ (N+1) * Real.log 2)) hterm
    rw [hcard, nsmul_eq_mul] at hsum
    refine le_trans hsum ?_
    -- `N * 2^{t+1} ≤ 2^{N+1}`
    have hkey : (N:ℝ) * 2 ^ (t+1) ≤ (2:ℝ) ^ (N+1) := by
      have hnat : N * 2 ^ (t+1) ≤ 2 ^ (N+1) := by
        rw [hN]
        have h1 : 2 ^ t * 2 ^ (t+1) = 2 ^ (2*t+1) := by
          rw [← pow_add]; ring_nf
        rw [h1]
        exact Nat.pow_le_pow_right (by norm_num) (by have := two_mul_le_two_pow t; omega)
      have := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast at this
      exact this
    have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
    have h2p : (0:ℝ) < (2:ℝ) ^ (N+1) := by positivity
    have h2q : (0:ℝ) < (2:ℝ) ^ (t+1) := by positivity
    have hL : (N:ℝ) * (3 / ((2:ℝ) ^ (N+1) * Real.log 2))
        = ((N:ℝ) * 3) / ((2:ℝ) ^ (N+1) * Real.log 2) := by ring
    have hR : 3 / Real.log 2 * (1 / (2:ℝ) ^ (t+1))
        = 3 / ((2:ℝ) ^ (t+1) * Real.log 2) := by field_simp
    rw [hL, hR, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hkey, hlog2, h2p, h2q]
  linarith

/-- Blocks are pairwise disjoint. -/
theorem blocks_disjoint : ∀ (n : ℕ), ((Finset.Ico 1 (2 ^ n) : Finset ℕ) : Set ℕ).PairwiseDisjoint
    (fun a => (Finset.Ico (2 ^ a) (2 ^ (a + 1))).filter Keep) := by
  intro n a _ b _ hab
  simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter, Finset.mem_Ico]
  rintro k ⟨⟨hk1, hk2⟩, -⟩ ⟨⟨hk3, hk4⟩, -⟩
  rcases lt_or_gt_of_ne hab with h | h
  · have : (2:ℕ) ^ (a + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have : (2:ℕ) ^ (b + 1) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- **(c)** `∑_{k ∈ A} 1/(k log k) = ∞`. -/
theorem not_summable_keep_harmonic : ¬ Summable harm := by
  intro hsum
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set C := ∑' k, harm k with hC
  -- every finite union of blocks has sum ≤ C
  have hbound : ∀ n : ℕ, ∑ a ∈ Finset.Ico 1 (2 ^ n), F a ≤ C := by
    intro n
    have hdis := blocks_disjoint n
    have heq : ∑ a ∈ Finset.Ico 1 (2 ^ n), F a
        = ∑ k ∈ (Finset.Ico 1 (2 ^ n)).biUnion
            (fun a => (Finset.Ico (2 ^ a) (2 ^ (a + 1))).filter Keep), harm k :=
      (Finset.sum_biUnion hdis).symm
    rw [heq, hC]
    exact hsum.sum_le_tsum _ (fun i _ => harm_nonneg i)
  -- the super-block lower bounds telescope
  have hlower : ∀ n : ℕ, ∑ t ∈ Finset.range n,
      (1 / (4 * ((t : ℝ) + 1) * Real.log 2) - (3 / Real.log 2) * (1 / 2 ^ (t + 1)))
        ≤ ∑ a ∈ Finset.Ico 1 (2 ^ n), F a := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        have hsplit : ∑ a ∈ Finset.Ico 1 (2 ^ (m + 1)), F a
            = (∑ a ∈ Finset.Ico 1 (2 ^ m), F a) + ∑ a ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), F a := by
          rw [Finset.sum_Ico_consecutive _ (Nat.one_le_two_pow)
            (Nat.pow_le_pow_right (by norm_num) (by omega))]
        rw [Finset.sum_range_succ, hsplit]
        exact add_le_add ih (superblock m)
  -- harmonic divergence
  have hgeom : ∀ n : ℕ, ∑ t ∈ Finset.range n, (3 / Real.log 2) * (1 / (2:ℝ) ^ (t + 1))
      ≤ 3 / Real.log 2 := by
    intro n
    have h1 : ∑ t ∈ Finset.range n, (1 / (2:ℝ) ^ (t + 1)) ≤ 1 := by
      have := sum_geometric_two_le n
      have heq : ∑ t ∈ Finset.range n, (1 / (2:ℝ) ^ (t + 1))
          = (1/2) * ∑ t ∈ Finset.range n, (1 / (2:ℝ)) ^ t := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [div_pow, one_pow, pow_succ]
        field_simp
      rw [heq]
      linarith
    rw [← Finset.mul_sum]
    have hpos : (0:ℝ) < 3 / Real.log 2 := by positivity
    nlinarith [h1, hpos]
  have hharm : ∀ n : ℕ, (1 / (4 * Real.log 2)) * ∑ t ∈ Finset.range n, (1 / ((t:ℝ) + 1))
      ≤ C + 3 / Real.log 2 := by
    intro n
    have h1 := (hlower n).trans (hbound n)
    rw [Finset.sum_sub_distrib] at h1
    have h2 := hgeom n
    have heq : ∑ t ∈ Finset.range n, 1 / (4 * ((t : ℝ) + 1) * Real.log 2)
        = (1 / (4 * Real.log 2)) * ∑ t ∈ Finset.range n, (1 / ((t:ℝ) + 1)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      have : (0:ℝ) < (t:ℝ) + 1 := by positivity
      field_simp
    rw [heq] at h1
    linarith
  have hdiv := Real.tendsto_sum_range_one_div_nat_succ_atTop
  have hbdd : ∀ n : ℕ, ∑ t ∈ Finset.range n, (1 / ((t:ℝ) + 1)) ≤ (C + 3 / Real.log 2) * (4 * Real.log 2) := by
    intro n
    have := hharm n
    have h4 : (0:ℝ) < 4 * Real.log 2 := by positivity
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ h4] at this
    nlinarith [this, h4]
  have := (hdiv.eventually_ge_atTop ((C + 3 / Real.log 2) * (4 * Real.log 2) + 1)).exists
  obtain ⟨n, hn⟩ := this
  linarith [hbdd n, hn]

/-! #### (d) assembly -/

/-- `π` is a bijection from the primes `< x` in `S` onto `{k < π'(x) : m k ∣ k}`. -/
theorem card_filter_PSet (x : ℕ) :
    ((x.primesBelow.filter PSet).card)
      = ((Finset.range (Nat.count Nat.Prime x)).filter Keep).card := by
  apply Finset.card_bij (fun p _ => Nat.count Nat.Prime p)
  · intro p hp
    rw [Finset.mem_filter, Nat.mem_primesBelow] at hp
    obtain ⟨⟨hpx, hprime⟩, hps⟩ := hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hps.2⟩
    have h1 : Nat.count Nat.Prime (p + 1) = Nat.count Nat.Prime p + 1 := by
      rw [Nat.count_succ, if_pos hprime]
    have h2 : Nat.count Nat.Prime (p + 1) ≤ Nat.count Nat.Prime x :=
      Nat.count_monotone Nat.Prime (by omega)
    omega
  · intro a ha b hb hab
    rw [Finset.mem_filter, Nat.mem_primesBelow] at ha hb
    have := Nat.nth_count ha.1.2
    have hb' := Nat.nth_count hb.1.2
    rw [← this, ← hb', hab]
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    refine ⟨Nat.nth Nat.Prime k, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨Nat.nth_lt_of_lt_count hk.1,
        Nat.prime_nth_prime k⟩, ⟨Nat.prime_nth_prime k, ?_⟩⟩
      have hc : Nat.count Nat.Prime (Nat.nth Nat.Prime k) = k := Nat.primeCounting'_nth_eq k
      rw [hc]
      exact hk.2
    · exact Nat.primeCounting'_nth_eq k

/-- **(d)** the prime set `PSet` has relative density `0`. -/
theorem relDensityZero_PSet : RelDensityZero PSet := by
  rw [RelDensityZero]
  have hcard : ∀ x : ℕ, ((x.primesBelow.filter PSet).card : ℝ) / (x.primesBelow.card : ℝ)
      = ((((Finset.range (Nat.count Nat.Prime x)).filter Keep).card : ℝ))
        / (Nat.count Nat.Prime x : ℝ) := by
    intro x
    rw [card_filter_PSet x]
    congr 1
    rw [Nat.primesBelow_eq_filter_range, ← Nat.count_eq_card_filter_range]
  rw [funext hcard]
  exact tendsto_keepCount_div.comp Nat.tendsto_primeCounting'

/-- `1/p_k` along `A`, `0` off it (a named function: `ite` on `Keep` must not be unfolded
during unification, or `Nat.log`'s well-founded recursion makes `whnf` diverge). -/
noncomputable def recipNth (k : ℕ) : ℝ := if Keep k then 1 / (Nat.nth Nat.Prime k : ℝ) else 0

/-- Reindexing the prime sum by `k = π'(p)`. -/
theorem summable_recipNth_of (h : Summable (fun p : ℕ => if p.Prime ∧ PSet p then (1 : ℝ) / p
    else 0)) : Summable recipNth := by
  have hinj : Function.Injective (Nat.nth Nat.Prime) :=
    Nat.nth_injective Nat.infinite_setOfPred_prime
  have hzero : ∀ x ∉ Set.range (Nat.nth Nat.Prime),
      (if x.Prime ∧ PSet x then (1 : ℝ) / x else 0) = 0 := by
    intro x hx
    rw [if_neg]
    rintro ⟨hp, -⟩
    exact hx ⟨Nat.count Nat.Prime x, Nat.nth_count hp⟩
  have hcomp := (Function.Injective.summable_iff hinj hzero).mpr h
  have hfun : (fun k : ℕ => if (Nat.nth Nat.Prime k).Prime ∧ PSet (Nat.nth Nat.Prime k)
      then (1 : ℝ) / (Nat.nth Nat.Prime k) else 0) = recipNth := by
    funext k
    have hp : (Nat.nth Nat.Prime k).Prime := Nat.prime_nth_prime k
    have hc : Nat.count Nat.Prime (Nat.nth Nat.Prime k) = k := Nat.primeCounting'_nth_eq k
    rw [recipNth]
    by_cases hk : Keep k
    · have hkeep' : Keep (Nat.count Nat.Prime (Nat.nth Nat.Prime k)) := by rw [hc]; exact hk
      rw [if_pos ⟨hp, hp, hkeep'⟩, if_pos hk]
    · rw [if_neg, if_neg hk]
      rintro ⟨-, -, hkeep⟩
      rw [hc] at hkeep
      exact hk hkeep
  exact hfun ▸ hcomp

/-- **(d)** the prime set `PSet` has divergent reciprocal sum. -/
theorem divergentRecip_PSet : DivergentRecip PSet := by
  rw [DivergentRecip]
  intro hsum
  have hcomp := summable_recipNth_of hsum
  have htail : Summable (fun k : ℕ => recipNth (k + 16)) := (summable_nat_add_iff 16).mpr hcomp
  have hcmp : Summable (fun k : ℕ => (1 / 20 : ℝ) * harm (k + 16)) := by
    refine Summable.of_nonneg_of_le
      (fun k => by have := harm_nonneg (k + 16); linarith) (fun k => ?_) htail
    set K := k + 16 with hK
    by_cases hk : Keep K
    · rw [harm, recipNth, if_pos hk, if_pos hk]
      have hple := nth_prime_le_mul_log K (by omega)
      have hKR : (16 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : 16 ≤ K)
      have hlogK : 0 < Real.log K := Real.log_pos (by linarith)
      have hppos : (0 : ℝ) < (Nat.nth Nat.Prime K : ℝ) := by
        have : (2 : ℝ) ≤ (Nat.nth Nat.Prime K : ℝ) := by
          exact_mod_cast (Nat.prime_nth_prime K).two_le
        linarith
      have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
      have hKlog : (0 : ℝ) < (K : ℝ) * Real.log K := mul_pos hKpos hlogK
      rw [mul_one_div, div_le_div_iff₀ (by positivity) hppos]
      nlinarith [hple, hlogK, hKR]
    · rw [harm, recipNth, if_neg hk, if_neg hk]; simp
  have hs : Summable (fun k : ℕ => harm (k + 16)) := by
    have h20 := hcmp.mul_left 20
    have hid : ∀ k : ℕ, (20 : ℝ) * ((1 / 20 : ℝ) * harm (k + 16)) = harm (k + 16) := by
      intro k; ring
    simpa [hid] using h20
  exact not_summable_keep_harmonic ((summable_nat_add_iff 16).mp hs)

end SparseExists

/-- A sparse divergent set of primes exists.

**Construction that needs no prime counting for the density and only Chebyshev for the sum**
(operator, 2026-09-19 22:15, after the lap's "PNT wall" claim below): index the primes by `π`.
Let `m k := Nat.log 2 (Nat.log 2 k) + 1` (slowly growing, `→ ∞`) and

  `S p :↔ p.Prime ∧ m (π p) ∣ π p`,   i.e. keep the `k`-th prime iff `m k ∣ k`.

* *Density.*  `π` is a bijection from the primes `≤ x` onto `[1, π x]`, so
  `#{p ≤ x : S p} = #{k ≤ π x : m k ∣ k}`.  On the block `I_m = {k : m k = m}` (an interval, since
  `m` is monotone) there are at most `|I_m|/m + 1` multiples of `m`; splitting at any `m₀`,
  `#{k ≤ K : m k ∣ k} ≤ C(m₀) + K/m₀ + m(K)`, and `m(K) = o(K)`, so the ratio to `K = π x` is
  `≤ 1/m₀ + o(1)` for every `m₀`.  **No estimate for `π` is used** - only that `π x → ∞`.
* *Divergence.*  `∑_{p∈S} 1/p = ∑_{k : m k ∣ k} 1/p_k` with `p_k = Nat.nth Nat.Prime (k-1)`.
  Chebyshev's lower bound (`Chebyshev.pi_ge : (n log 2 − log(n+1))/log n ≤ π n`, in Mathlib) gives
  `p_k ≤ C k log k` for large `k` (from `k = π(p_k) ≥ c p_k/log p_k`, then `log p_k ≤ 2 log k`).
  So it suffices that `∑_{k : m k ∣ k} 1/(k log k) = ∞`.  On `I_m = [2^{2^{m-1}}, 2^{2^m})` the
  multiples of `m` are `k = m j`, `j ∈ [A, B)` with `A = 2^{2^{m-1}}/m`, `B = 2^{2^m}/m`, and
  `∑_{j∈[A,B)} 1/(mj log(mj)) ≥ (1/(2m)) ∑_{j∈[A,B)} 1/(j log j) ≥ (1/(2m)) (log(B/A) − 1)/log B
  ≥ (1/(2m)) · (1/4)` for large `m` (`log(B/A) = 2^{m-1} log 2 + log 1 ≈ ½ log B`), using only
  `log_le_sum_range_inv`-type harmonic bounds.  Then `∑_m 1/(8m) = ∞`.

Sub-leaves for a lap: (a) `nth_prime_le_mul_log : ∀ᶠ k, Nat.nth Nat.Prime k ≤ C * k * log k`
from `Chebyshev.pi_ge`; (b) the block-count bound for multiples of a slowly varying modulus;
(c) the harmonic lower bound on `[A, B)`; (d) assembly.  Elementary throughout.

**The lap's claim of 2026-09-20 ("needs PNT with error term") is withdrawn**: its obstruction
argument assumed the count of `S` is bounded by "a fraction of the integers"; indexing by `π p`
makes the density statement combinatorial and moves all analytic input into the one-sided
Chebyshev bound, which Mathlib has.  It remains off the main line: `exists_sparse_normal_of_KMT_quant'`
consumes only `DivergentRecip`. -/
theorem exists_relDensityZero_divergent :
    ∃ (S : ℕ → Prop) (_ : DecidablePred S), RelDensityZero S ∧ DivergentRecip S :=
  ⟨SparseExists.PSet, inferInstance, SparseExists.relDensityZero_PSet,
    SparseExists.divergentRecip_PSet⟩

/-- **Existence**, conditional on the diagonal reading of Prop. 4.3 for every sparse divergent `S`
(the "∀ sufficiently sparse" form; the `k`-uniformity of the implied constant is the open step):
some `c_𝒫(4)` with `∑_{p∈𝒫} 1/p = ∞` is normal to base `4`. -/
theorem exists_sparse_normal
    (hKMT : ∀ (S : ℕ → Prop) [DecidablePred S], RelDensityZero S → DivergentRecip S →
      KMT_along S windowJ) :
    ∃ (S : ℕ → Prop) (_ : DecidablePred S), RelDensityZero S ∧ DivergentRecip S ∧
      IsNormal 4 (subsetLambert S 4) := by
  obtain ⟨S, hdec, hden, hdiv⟩ := exists_relDensityZero_divergent
  exact ⟨S, hdec, hden, hdiv, isNormal_subsetLambert_of_KMT_windowJ S (hKMT S hden hdiv)⟩

/-! ### The quantitative node: Prop. 4.3 specialised, with its `k`-dependent constant exposed

For `f_j(n) = e(h 4^{-j} ω_S(n))` the pretentious distances in Prop. 4.3 are explicit:
`𝔻(f_j, 1; y, x)² = (1 − cos(2πh/4^j)) ∑_{y<p≤x, p∈S} 1/p ≤ 2 ∑_{y<p≤x, p∈S} 1/p`, and at the first
site `j` with `h/4^j ∉ ℤ` the fractional part is `1/4, 1/2` or `3/4`, so `1 − cos ≥ 1` and
`max_j 𝔻(f_j, 1; y)² ≥ ∑_{p≤y, p∈S} 1/p`.  So the proposition, at shifts `1, …, J`, reads as the
elementary inequality `KMT_quant C` below with some constant `C J` depending only on `J`.

Reading the proof (KMT §4.1–4.2) the constant collects: the sum over `e_j ∣ A^∞` with
`A ⊇ ∏_{p<J} p` (`≍ (log J)^J`), the fundamental lemma of sieve theory in dimension `J`, dimension-`J`
Mertens products, and the smooth-number truncation `d_j ≤ x^{1/(4J)}` (which needs only `Jε → 0`,
although the paper's fixed form `exp(−1/(2ε))` silently costs `ε ≤ e^{−4J}/(4J)`).  The small-prime
tuple sum dominates, giving `C J = exp(O(J²))` once (4.20) is re-run with the natural Dickman bound
(as printed the constant absorbs `ε > e^{−4J}/(4J)` and is too large); the existence theorem below
needs only `log C J = o(4^J)`.
-/

/-- `∑_{p ≤ x, p ∈ S} 1/p`. -/
noncomputable def recipSumLe (x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Iic x).filter (fun p => p.Prime ∧ S p), (1 : ℝ) / p

/-- `∑_{y < p ≤ x, p ∈ S} 1/p`. -/
noncomputable def recipSumIoc (y x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc y x).filter (fun p => p.Prime ∧ S p), (1 : ℝ) / p

/-- **Frozen input**, quantitative form of KMT 2023 Prop. 4.3 at shifts `1, …, J`, `χ = 1`, `t = 0`,
for the phases `e(h 4^{-j} ω_S)`, with the implied constant `C J` exposed.  The `n < x` versus
`n ≤ x` discrepancy is `≤ 1/x ≤ exp(−1/(8J²ε))` on the stated `ε`-range, absorbed by `C`. -/
def KMT_quant (C : ℕ → ℝ) : Prop :=
  ∀ (S : ℕ → Prop) [DecidablePred S] (J : ℕ) (h : ℤ), h ≠ 0 → NontrivialWindow J h →
    ∀ x : ℕ, 3 ≤ x → ∀ ε : ℝ, 1 / Real.log (Real.log x) < ε → ε < 1 / 2 →
      ‖windowMeanS S J h x‖ ≤ C J *
        (Real.sqrt (Real.log (1 / ε)) * Real.sqrt (2 * recipSumIoc S ⌊(x : ℝ) ^ ε⌋₊ x)
          + Real.exp (- recipSumLe S ⌊(x : ℝ) ^ ε⌋₊)
          + Real.exp (- 1 / (8 * (J : ℝ) ^ 2 * ε)))

/-! ### The block construction

**Existence from the fixed-`k` proposition alone** (no uniformity in `k` beyond a growth bound
on its constant).  Block construction: `S = ⋃ᵢ Bᵢ`, `Bᵢ ⊆ (xᵢ, xᵢ₊₁]` with `∑_{p∈Bᵢ} 1/p = δᵢ`,
`xᵢ₊₁ ≥ xᵢ^{1/εᵢ₊₁}` so that `[x^ε, x]` meets at most two blocks; schedule `J_N = Jᵢ` on
`(xᵢ, xᵢ₊₁]` with `εᵢ = 1/(8 Jᵢ² log i)`.  The three terms give `C(Jᵢ) √δᵢ √log(Jᵢ² log i)`,
`C(Jᵢ) exp(−∑_{i'<i−1} δᵢ')`, `C(Jᵢ)/i`; the L¹ tail (`tail_error_L1`) needs
`∑_{i'≤i} δᵢ' = o(4^{Jᵢ})`.  With `δᵢ = 1/i` the sandwich `log C(Jᵢ) + ω(1) ≤ log i ≤ o(4^{Jᵢ})`
is solvable iff `log C k = o(4^k)`, and `∑ δᵢ = ∞` gives `DivergentRecip`.  Proved at the end of
the file as `exists_sparse_normal_of_KMT_quant`, from `exists_good` + the block leaves. 
-/

/-- The tail difference as a convergent nonnegative series (the leaf-2 decomposition, factored
out for the L¹ bound). -/
theorem summable_tail_diff (J n : ℕ) :
    Summable (fun t : ℕ => omegaS S (n + (t + J) + 1) / (4 : ℝ) ^ (t + J + 1)) := by
  have hsum : Summable (fun i : ℕ => omegaS S (n + i + 1) / (4 : ℝ) ^ (i + 1)) := by
    have h := TWeight.summable_tailB (W := TWeight.subset S) (b := 4) (by norm_num) n
    exact h.congr (fun i => by rw [TWeight.subset_wN]; norm_num)
  exact (summable_nat_add_iff J).mpr hsum

theorem tail_diff_tsum (J n : ℕ) :
    (TWeight.subset S).tailB 4 n - truncTailS S J n
      = ∑' t : ℕ, omegaS S (n + (t + J) + 1) / (4 : ℝ) ^ (t + J + 1) := by
  have hsum : Summable (fun i : ℕ => omegaS S (n + i + 1) / (4 : ℝ) ^ (i + 1)) := by
    have h := TWeight.summable_tailB (W := TWeight.subset S) (b := 4) (by norm_num) n
    exact h.congr (fun i => by rw [TWeight.subset_wN]; norm_num)
  have hsplit := hsum.sum_add_tsum_nat_add J
  have htB : (TWeight.subset S).tailB 4 n
      = ∑' i : ℕ, omegaS S (n + i + 1) / (4 : ℝ) ^ (i + 1) := by
    rw [TWeight.tailB]; exact tsum_congr fun i => by rw [TWeight.subset_wN]; norm_num
  rw [htB, truncTailS, ← hsplit]
  ring

/-- Multiples of `p` in a shifted window: at most `N/p + 2`. -/
theorem card_filter_dvd_shift_le (p N j : ℕ) (hp : 0 < p) :
    ((((Finset.range N).filter (fun n => p ∣ n + j)).card : ℝ)) ≤ (N : ℝ) / p + 2 := by
  have hnat : ((Finset.range N).filter (fun n => p ∣ n + j)).card ≤ N / p + 2 := by
    have hsub : ∀ n ∈ (Finset.range N).filter (fun n => p ∣ n + j),
        (n + j) / p ∈ Finset.Icc (j / p) ((N + j) / p) := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_range] at hn
      exact Finset.mem_Icc.mpr
        ⟨Nat.div_le_div_right (by omega), Nat.div_le_div_right (by omega)⟩
    have hinj : Set.InjOn (fun n => (n + j) / p)
        ((Finset.range N).filter (fun n => p ∣ n + j) : Finset ℕ) := by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at ha hb
      have ha' : p * ((a + j) / p) = a + j := Nat.mul_div_cancel' ha.2
      have hb' : p * ((b + j) / p) = b + j := Nat.mul_div_cancel' hb.2
      simp only at hab
      have h1 : a + j = b + j := by
        calc a + j = p * ((a + j) / p) := ha'.symm
          _ = p * ((b + j) / p) := by rw [hab]
          _ = b + j := hb'
      omega
    have hcard := Finset.card_le_card_of_injOn _ hsub hinj
    rw [Nat.card_Icc] at hcard
    have hadd := Nat.add_div (a := N) (b := j) hp
    generalize hA : N / p = A at *
    generalize hBb : j / p = Bb at *
    generalize hC : (N + j) / p = Cc at *
    split_ifs at hadd <;> omega
  have hcast : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
  calc ((((Finset.range N).filter (fun n => p ∣ n + j)).card : ℝ))
      ≤ ((N / p + 2 : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = ((N / p : ℕ) : ℝ) + 2 := by push_cast; ring
    _ ≤ (N : ℝ) / p + 2 := by linarith

/-- Double counting: `∑_{n<N} ω_S(n+j) ≤ N · S_S(2N) + 2N + 5j`. -/
theorem sum_omegaS_shift_le (N j : ℕ) (hN : 1 ≤ N) (hj : 1 ≤ j) :
    ∑ n ∈ Finset.range N, omegaS S (n + j)
      ≤ (N : ℝ) * (recipSumLe S (2 * N) + 2) + 5 * j := by
  classical
  set P : Finset ℕ := (Finset.Iic (N + j)).filter (fun p => p.Prime ∧ S p) with hP
  have hrec : recipSumLe S (N + j) = ∑ p ∈ P, (1 : ℝ) / p := by rw [hP, recipSumLe]
  -- pointwise: `ω_S(n+j)` counts the primes of `P` dividing `n+j`
  have hpoint : ∀ n ∈ Finset.range N,
      omegaS S (n + j) = ∑ p ∈ P, (if p ∣ n + j then (1 : ℝ) else 0) := by
    intro n hn
    rw [Finset.mem_range] at hn
    have hset : (n + j).primeFactors.filter S = P.filter (fun p => p ∣ n + j) := by
      ext q
      simp only [hP, Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_Iic]
      constructor
      · rintro ⟨⟨hpp, hdvd, _⟩, hs⟩
        exact ⟨⟨le_trans (Nat.le_of_dvd (by omega) hdvd) (by omega), hpp, hs⟩, hdvd⟩
      · rintro ⟨⟨_, hpp, hs⟩, hdvd⟩
        exact ⟨⟨hpp, hdvd, by omega⟩, hs⟩
    rw [omegaS, omegaSN, hset, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- double counting
  have hswap : ∑ n ∈ Finset.range N, omegaS S (n + j)
      = ∑ p ∈ P, ((((Finset.range N).filter (fun n => p ∣ n + j)).card : ℝ)) := by
    rw [Finset.sum_congr rfl hpoint, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hbd : ∑ p ∈ P, ((((Finset.range N).filter (fun n => p ∣ n + j)).card : ℝ))
      ≤ ∑ p ∈ P, ((N : ℝ) / p + 2) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hpp : p.Prime := (((Finset.mem_filter.mp (hP ▸ hp)).2).1)
    exact card_filter_dvd_shift_le p N j hpp.pos
  have hsplit : ∑ p ∈ P, ((N : ℝ) / p + 2)
      = (N : ℝ) * recipSumLe S (N + j) + (P.card : ℝ) * 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hrec, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun p _ => by rw [mul_one_div])
  -- primes above `2N` contribute little
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hQ : recipSumLe S (N + j) ≤ recipSumLe S (2 * N)
      + ∑ p ∈ (Finset.Ioc (2 * N) (N + j)).filter (fun p => p.Prime ∧ S p), (1 : ℝ) / p := by
    have hsub : (Finset.Iic (N + j)).filter (fun p => p.Prime ∧ S p)
        ⊆ ((Finset.Iic (2 * N)).filter (fun p => p.Prime ∧ S p))
          ∪ ((Finset.Ioc (2 * N) (N + j)).filter (fun p => p.Prime ∧ S p)) := by
      intro q hq
      rw [Finset.mem_filter, Finset.mem_Iic] at hq
      by_cases h : q ≤ 2 * N
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr h, hq.2⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hq.1⟩, hq.2⟩)
    have hdisj : Disjoint ((Finset.Iic (2 * N)).filter (fun p => p.Prime ∧ S p))
        ((Finset.Ioc (2 * N) (N + j)).filter (fun p => p.Prime ∧ S p)) := by
      refine Finset.disjoint_left.mpr (fun q hq1 hq2 => ?_)
      rw [Finset.mem_filter, Finset.mem_Iic] at hq1
      rw [Finset.mem_filter, Finset.mem_Ioc] at hq2
      omega
    calc recipSumLe S (N + j)
        ≤ ∑ p ∈ ((Finset.Iic (2 * N)).filter (fun p => p.Prime ∧ S p))
            ∪ ((Finset.Ioc (2 * N) (N + j)).filter (fun p => p.Prime ∧ S p)), (1 : ℝ) / p := by
          rw [recipSumLe]
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
      _ = _ := by rw [Finset.sum_union hdisj, recipSumLe]
  have hQsmall : ∑ p ∈ (Finset.Ioc (2 * N) (N + j)).filter (fun p => p.Prime ∧ S p), (1 : ℝ) / p
      ≤ (j : ℝ) / (2 * N) := by
    have hterm : ∀ q ∈ (Finset.Ioc (2 * N) (N + j)).filter (fun p => p.Prime ∧ S p),
        (1 : ℝ) / q ≤ 1 / (2 * N) := by
      intro q hq
      rw [Finset.mem_filter, Finset.mem_Ioc] at hq
      have : (2 * (N : ℝ)) ≤ q := by exact_mod_cast hq.1.1.le
      exact one_div_le_one_div_of_le (by linarith) this
    have hcard : (((Finset.Ioc (2 * N) (N + j)).filter (fun p => p.Prime ∧ S p)).card : ℝ)
        ≤ (j : ℝ) := by
      have h1 := Finset.card_filter_le (Finset.Ioc (2 * N) (N + j)) (fun p => p.Prime ∧ S p)
      rw [Nat.card_Ioc] at h1
      have : ((Finset.Ioc (2 * N) (N + j)).filter (fun p => p.Prime ∧ S p)).card ≤ j := by omega
      exact_mod_cast this
    calc ∑ p ∈ (Finset.Ioc (2 * N) (N + j)).filter (fun p => p.Prime ∧ S p), (1 : ℝ) / p
        ≤ ∑ _p ∈ (Finset.Ioc (2 * N) (N + j)).filter (fun p => p.Prime ∧ S p),
            (1 : ℝ) / (2 * N) := Finset.sum_le_sum hterm
      _ = (((Finset.Ioc (2 * N) (N + j)).filter (fun p => p.Prime ∧ S p)).card : ℝ)
            * (1 / (2 * N)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (j : ℝ) * (1 / (2 * N)) := by
          have : (0 : ℝ) ≤ 1 / (2 * N) := by positivity
          exact mul_le_mul_of_nonneg_right hcard this
      _ = (j : ℝ) / (2 * N) := by ring
  have hPcard : (P.card : ℝ) ≤ (N : ℝ) + j + 1 := by
    have h1 : P.card ≤ (Finset.Iic (N + j)).card := by
      rw [hP]; exact Finset.card_filter_le _ _
    rw [Nat.card_Iic] at h1
    have : (P.card : ℝ) ≤ ((N + j + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this; linarith
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hextra : (N : ℝ) * ((j : ℝ) / (2 * N)) = (j : ℝ) / 2 := by
    field_simp
  have hchain : (N : ℝ) * recipSumLe S (N + j)
      ≤ (N : ℝ) * recipSumLe S (2 * N) + (j : ℝ) / 2 := by
    calc (N : ℝ) * recipSumLe S (N + j)
        ≤ (N : ℝ) * (recipSumLe S (2 * N) + (j : ℝ) / (2 * N)) := by
          refine mul_le_mul_of_nonneg_left ?_ hNR.le
          linarith [hQ, hQsmall]
      _ = (N : ℝ) * recipSumLe S (2 * N) + (j : ℝ) / 2 := by rw [mul_add, hextra]
  calc ∑ n ∈ Finset.range N, omegaS S (n + j)
      = ∑ p ∈ P, ((((Finset.range N).filter (fun n => p ∣ n + j)).card : ℝ)) := hswap
    _ ≤ ∑ p ∈ P, ((N : ℝ) / p + 2) := hbd
    _ = (N : ℝ) * recipSumLe S (N + j) + (P.card : ℝ) * 2 := hsplit
    _ ≤ (N : ℝ) * recipSumLe S (2 * N) + (j : ℝ) / 2 + ((N : ℝ) + j + 1) * 2 := by
        linarith [hchain, hPcard]
    _ ≤ (N : ℝ) * (recipSumLe S (2 * N) + 2) + 5 * j := by
        rw [mul_add]; linarith

/-- `∑'_t (B + c t)/2^{t+1} = B + c`. -/
theorem tsum_lin_geom (B c : ℝ) : ∑' t : ℕ, (B + c * t) / 2 ^ (t + 1) = B + c := by
  have hcongr : ∀ t : ℕ, (B + c * t) / 2 ^ (t + 1)
      = B * ((1 : ℝ) / 2 ^ (t + 1)) + c * ((t : ℝ) / 2 ^ (t + 1)) := by
    intro t; ring
  rw [tsum_congr hcongr,
    Summable.tsum_add (summable_geom_shift.mul_left B) (summable_i_geom.mul_left c),
    tsum_mul_left, tsum_mul_left, tsum_geom_shift, tsum_i_geom, mul_one, mul_one]

/-- The site `j = |h| + 1` always carries a nontrivial phase (as in `G₄`). -/
theorem nontrivial_site {h : ℤ} (hh : h ≠ 0) :
    ¬ ∃ m : ℤ, (h : ℝ) / (4 : ℝ) ^ (h.natAbs + 1) = m := by
  set j₀ : ℕ := h.natAbs + 1 with hj₀def
  rintro ⟨m, hm⟩
  have h4 : ((4 : ℝ) ^ j₀) ≠ 0 := by positivity
  have hR : (h : ℝ) = (m : ℝ) * (4 : ℝ) ^ j₀ := by field_simp at hm; linarith [hm]
  have hZ : h = m * 4 ^ j₀ := by exact_mod_cast hR
  have hm0 : m ≠ 0 := by rintro rfl; simp at hZ; exact hh hZ
  have hlb : (4 : ℤ) ^ j₀ ≤ |h| := by
    rw [hZ, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 4 ^ j₀)]
    have : 1 ≤ |m| := Int.one_le_abs (by omega)
    nlinarith [abs_nonneg m, (by positivity : (0 : ℤ) < 4 ^ j₀)]
  have hub : h.natAbs < 4 ^ j₀ := by
    calc h.natAbs < 2 ^ h.natAbs := Nat.lt_two_pow_self
      _ ≤ 4 ^ (h.natAbs + 1) := by
          calc 2 ^ h.natAbs ≤ 4 ^ h.natAbs := Nat.pow_le_pow_left (by norm_num) _
            _ ≤ 4 ^ (h.natAbs + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have habs : |h| = (h.natAbs : ℤ) := Int.abs_eq_natAbs h
  have hge : ((4 : ℤ) ^ j₀) ≤ (h.natAbs : ℤ) := by rw [habs] at hlb; exact hlb
  have hub' : ((h.natAbs : ℤ)) < 4 ^ j₀ := by exact_mod_cast hub
  omega

/-- `(5k + 11)/4^k → 0`. -/
theorem tendsto_lin_div_pow : Tendsto (fun k : ℕ => (5 * (k : ℝ) + 11) / 4 ^ k) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => (k : ℝ) * (1 / 4 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_abs_lt_one (by norm_num)
  have h2 : Tendsto (fun k : ℕ => ((1 : ℝ) / 4) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h3 := (h1.const_mul 5).add (h2.const_mul 11)
  rw [mul_zero, mul_zero, add_zero] at h3
  refine h3.congr (fun k => ?_)
  rw [div_pow, one_pow]
  field_simp

/-- L¹ tail for a slow schedule.  For `J < j`, `∑_{n<N} ω_S(n+j) ≤ N·(S_S(2N) + 2) + 5j`
(double counting over the primes of `S`, `#{n<N : p ∣ n+j} ≤ N/p + 2`), so the geometric sum gives
`≪ 4^{-J}(S_S(2N) + J)` — no `log N`, which is what lets `J_N` grow as slowly as `log₄ S_S(N)`.
(The constant deviates from the kickoff's `+1`/`log₂ N` shape: the honest elementary count costs
`+2` per `n` and `+5j` for the primes above `2N`, and the fringe `j > N` is absorbed into the same
geometric series rather than a separate `4^{-N}` term.  The shape `≪ 4^{-J}(S_S(2N) + o(4^J))` is
what the block construction consumes.) -/
theorem tail_error_L1 (J N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.range N, |(TWeight.subset S).tailB 4 n - truncTailS S J n|) / N
      ≤ (recipSumLe S (2 * N) + 5 * J + 12) / (4 : ℝ) ^ J := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set R : ℝ := recipSumLe S (2 * N) with hRdef
  have hR0 : 0 ≤ R := by
    rw [hRdef, recipSumLe]
    exact Finset.sum_nonneg (fun p _ => by positivity)
  -- each term is a nonnegative tsum
  have habs : ∀ n : ℕ, |(TWeight.subset S).tailB 4 n - truncTailS S J n|
      = ∑' t : ℕ, omegaS S (n + (t + J) + 1) / (4 : ℝ) ^ (t + J + 1) := by
    intro n
    rw [tail_diff_tsum S J n, abs_of_nonneg]
    exact tsum_nonneg (fun t => by have := omegaS_nonneg (S := S) (n + (t + J) + 1); positivity)
  -- swap the finite and infinite sums
  have hswap : ∑ n ∈ Finset.range N, |(TWeight.subset S).tailB 4 n - truncTailS S J n|
      = ∑' t : ℕ, ∑ n ∈ Finset.range N,
          omegaS S (n + (t + J) + 1) / (4 : ℝ) ^ (t + J + 1) := by
    rw [Finset.sum_congr rfl (fun n _ => habs n)]
    exact (Summable.tsum_finsetSum (fun n _ => summable_tail_diff S J n)).symm
  -- the majorant
  set B : ℝ := (N : ℝ) * (R + 2) + 5 * J + 5 with hB
  have hmajterm : ∀ t : ℕ, ∑ n ∈ Finset.range N,
      omegaS S (n + (t + J) + 1) / (4 : ℝ) ^ (t + J + 1)
        ≤ (1 / (4 : ℝ) ^ J) * ((B + 5 * t) / 2 ^ (t + 1)) := by
    intro t
    have hcount := sum_omegaS_shift_le S N (t + J + 1) hN (by omega)
    have hre : ∑ n ∈ Finset.range N, omegaS S (n + (t + J) + 1) / (4 : ℝ) ^ (t + J + 1)
        = (∑ n ∈ Finset.range N, omegaS S (n + (t + J + 1))) / (4 : ℝ) ^ (t + J + 1) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun n _ => by rw [show n + (t + J) + 1 = n + (t + J + 1) by ring])
    rw [hre]
    have hnum : (∑ n ∈ Finset.range N, omegaS S (n + (t + J + 1)))
        ≤ B + 5 * t := by
      have : ((t : ℝ) + J + 1) = ((t + J + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hB]
      push_cast at hcount ⊢
      linarith
    have hden : (2 : ℝ) ^ (t + 1) * 4 ^ J ≤ 4 ^ (t + J + 1) := by
      have h2 : (2 : ℝ) ^ (t + 1) ≤ 4 ^ (t + 1) := by gcongr <;> norm_num
      calc (2 : ℝ) ^ (t + 1) * 4 ^ J ≤ 4 ^ (t + 1) * 4 ^ J := by gcongr
        _ = 4 ^ (t + J + 1) := by rw [← pow_add]; ring_nf
    have hB0 : 0 ≤ B + 5 * t := by
      rw [hB]
      have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
      have hJ : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
      nlinarith
    have hs0 : (0 : ℝ) ≤ ∑ n ∈ Finset.range N, omegaS S (n + (t + J + 1)) :=
      Finset.sum_nonneg (fun n _ => omegaS_nonneg (S := S) _)
    have hpos1 : (0:ℝ) < 4 ^ (t + J + 1) := by positivity
    have hpos2 : (0:ℝ) < 2 ^ (t + 1) * (4:ℝ) ^ J := by positivity
    rw [one_div, inv_mul_eq_div, div_div, div_le_div_iff₀ hpos1 hpos2]
    nlinarith [hnum, hden, hB0, hs0, hpos1.le, hpos2.le]
  have hmajsum : Summable (fun t : ℕ => (1 / (4 : ℝ) ^ J) * ((B + 5 * t) / 2 ^ (t + 1))) := by
    have h1 : Summable (fun t : ℕ => (B + 5 * (t : ℝ)) / 2 ^ (t + 1)) := by
      have := (summable_geom_shift.mul_left B).add (summable_i_geom.mul_left 5)
      refine this.congr (fun i => ?_); ring
    exact h1.mul_left _
  have hLsum : Summable (fun t : ℕ => ∑ n ∈ Finset.range N,
      omegaS S (n + (t + J) + 1) / (4 : ℝ) ^ (t + J + 1)) :=
    summable_sum (fun n _ => summable_tail_diff S J n)
  have hkey : ∑ n ∈ Finset.range N, |(TWeight.subset S).tailB 4 n - truncTailS S J n|
      ≤ (1 / (4 : ℝ) ^ J) * (B + 5) := by
    rw [hswap]
    calc ∑' t : ℕ, ∑ n ∈ Finset.range N,
            omegaS S (n + (t + J) + 1) / (4 : ℝ) ^ (t + J + 1)
        ≤ ∑' t : ℕ, (1 / (4 : ℝ) ^ J) * ((B + 5 * t) / 2 ^ (t + 1)) :=
          Summable.tsum_le_tsum hmajterm hLsum hmajsum
      _ = (1 / (4 : ℝ) ^ J) * (B + 5) := by rw [tsum_mul_left, tsum_lin_geom]
  have h4 : (0 : ℝ) < (4 : ℝ) ^ J := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
  rw [div_le_div_iff₀ hNR h4]
  have hkey' : (∑ n ∈ Finset.range N, |(TWeight.subset S).tailB 4 n - truncTailS S J n|)
      * (4 : ℝ) ^ J ≤ B + 5 := by
    rw [← le_div_iff₀ h4]
    calc (∑ n ∈ Finset.range N, |(TWeight.subset S).tailB 4 n - truncTailS S J n|)
        ≤ (1 / (4 : ℝ) ^ J) * (B + 5) := hkey
      _ = (B + 5) / (4 : ℝ) ^ J := by rw [one_div, inv_mul_eq_div]
  have : B + 5 ≤ (R + 5 * J + 12) * N := by
    rw [hB]
    nlinarith [hR0, hN1, hJ0]
  linarith

/-! ### The block construction, decomposed

`S = ⋃ᵢ Bᵢ` with `Bᵢ` a finite set of primes in `(xᵢ, xᵢ₊₁]`, `δᵢ = ∑_{Bᵢ} 1/p`.  At a scale `N`
in block `i` (`xᵢ < N ≤ xᵢ₊₁`) the schedule is `Jᵢ` and the KMT parameter `εᵢ`.  `Good C` lists
the sandwich inequalities that make the three KMT terms and the L¹ tail vanish; `exists_good`
solves the sandwich from `log C k = o(4^k)`; the rest is bookkeeping. -/

/-- Block data: cut points `x`, blocks `B`, schedule `J`, KMT parameter `ε`. -/
structure BlockData where
  x : ℕ → ℕ
  B : ℕ → Finset ℕ
  J : ℕ → ℕ
  ε : ℕ → ℝ
  x_mono : StrictMono x
  B_prime : ∀ i, ∀ p ∈ B i, p.Prime ∧ x i < p ∧ p ≤ x (i + 1)

namespace BlockData

variable (D : BlockData)

/-- The union of the blocks. -/
def set (p : ℕ) : Prop := ∃ i, p ∈ D.B i

noncomputable instance : DecidablePred D.set := Classical.decPred _

/-- `δᵢ = ∑_{p ∈ Bᵢ} 1/p`. -/
noncomputable def δ (i : ℕ) : ℝ := ∑ p ∈ D.B i, (1 : ℝ) / p

/-- The block containing `N`: the greatest `i` with `xᵢ < N` (so `xᵢ < N ≤ xᵢ₊₁`). -/
noncomputable def blockIndex (N : ℕ) : ℕ := Nat.findGreatest (fun i => D.x i < N) N

/-- The schedule `J_N = J_{blockIndex N}`. -/
noncomputable def sched (N : ℕ) : ℕ := D.J (D.blockIndex N)

/-- The sandwich: everything the diagonal needs, as inequalities in `i`. -/
structure Good (C : ℕ → ℝ) : Prop where
  /-- `Jᵢ → ∞` (so every `h ≠ 0` eventually has a nontrivial site). -/
  J_tendsto : Tendsto D.J atTop atTop
  /-- `∑ δᵢ = ∞`. -/
  δ_div : ¬ Summable D.δ
  /-- The KMT `ε`-range holds at every scale of block `i`. -/
  ε_range : ∀ i N, D.x i < N → 1 / Real.log (Real.log N) < D.ε i ∧ D.ε i < 1 / 2
  /-- `[N^{εᵢ}, N]` meets at most blocks `i−1, i`: `N^{εᵢ} ≥ xᵢ₋₁` on block `i`.
  ⚠️ The hypothesis `1 ≤ i` is **necessary**: at `i = 0` this field and `ε_range` are jointly
  contradictory (`sep_eps_incompatible` below, machine-checked).  `kmt_along` only ever uses it
  at `blockIndex N ≥ 1`, which holds for all large `N`. -/
  sep : ∀ i N, 1 ≤ i → D.x i < N → D.x (i - 1) ≤ ⌊(N : ℝ) ^ D.ε i⌋₊
  /-- `2N` stays inside block `i+1`. -/
  x_double : ∀ i, 2 * D.x (i + 1) ≤ D.x (i + 2)
  /-- The three KMT terms, with the constant, vanish along the blocks. -/
  terms : Tendsto (fun i => C (D.J i) *
      (Real.sqrt (Real.log (1 / D.ε i)) * Real.sqrt (2 * (D.δ (i - 1) + D.δ i))
        + Real.exp (- ∑ i' ∈ Finset.range (i - 1), D.δ i')
        + Real.exp (- 1 / (8 * (D.J i : ℝ) ^ 2 * D.ε i)))) atTop (𝓝 0)
  /-- The L¹ tail vanishes: `∑_{i' ≤ i+1} δᵢ' = o(4^{Jᵢ})`. -/
  tail : Tendsto (fun i => (∑ i' ∈ Finset.range (i + 2), D.δ i' + 1) / (4 : ℝ) ^ D.J i)
    atTop (𝓝 0)

/-- Distinct blocks are disjoint: `B i ⊆ (x i, x (i+1)]`. -/
theorem B_disjoint {i i' : ℕ} (h : i ≠ i') : Disjoint (D.B i) (D.B i') := by
  refine Finset.disjoint_left.mpr (fun p hp hp' => ?_)
  obtain ⟨-, h1, h2⟩ := D.B_prime i p hp
  obtain ⟨-, h1', h2'⟩ := D.B_prime i' p hp'
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have := D.x_mono.monotone (show i + 1 ≤ i' by omega)
    omega
  · have := D.x_mono.monotone (show i' + 1 ≤ i by omega)
    omega

theorem B_pairwiseDisjoint (s : Finset ℕ) : (s : Set ℕ).PairwiseDisjoint D.B :=
  fun _ _ _ _ h => D.B_disjoint h

/-- Every prime of `D.set` below `y` lies in one of the first blocks. -/
theorem biUnion_subset_filter (i y : ℕ) (hy : D.x (i - 1) ≤ y) :
    (Finset.range (i - 1)).biUnion D.B ⊆ (Finset.Iic y).filter (fun p => p.Prime ∧ D.set p) := by
  intro p hp
  rw [Finset.mem_biUnion] at hp
  obtain ⟨i', hi', hpB⟩ := hp
  rw [Finset.mem_range] at hi'
  obtain ⟨hprime, -, h2⟩ := D.B_prime i' p hpB
  have hx : D.x (i' + 1) ≤ D.x (i - 1) := D.x_mono.monotone (by omega)
  exact Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr (by omega), hprime, ⟨i', hpB⟩⟩

/-- On block `i`, `∑_{y<p≤N, p∈S} 1/p ≤ δᵢ₋₁ + δᵢ` once `y ≥ xᵢ₋₁`. -/
theorem recipSumIoc_le (i N y : ℕ) (hN : D.x i < N) (hN' : N ≤ D.x (i + 1))
    (hy : D.x (i - 1) ≤ y) : recipSumIoc D.set y N ≤ D.δ (i - 1) + D.δ i := by
  have hsub : (Finset.Ioc y N).filter (fun p => p.Prime ∧ D.set p) ⊆ D.B (i - 1) ∪ D.B i := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨k, hk⟩ := hp.2.2
    obtain ⟨-, hkl, hkr⟩ := D.B_prime k p hk
    have h1 : p ≤ D.x (i + 1) := le_trans hp.1.2 hN'
    have h2 : D.x (i - 1) < p := lt_of_le_of_lt hy hp.1.1
    have hkle : k ≤ i := by
      by_contra hc
      have := D.x_mono.monotone (show i + 1 ≤ k by omega)
      omega
    have hkge : i - 1 ≤ k := by
      by_contra hc
      have := D.x_mono.monotone (show k + 1 ≤ i - 1 by omega)
      omega
    rcases (by omega : k = i - 1 ∨ k = i) with rfl | rfl
    · exact Finset.mem_union_left _ hk
    · exact Finset.mem_union_right _ hk
  calc recipSumIoc D.set y N ≤ ∑ p ∈ D.B (i - 1) ∪ D.B i, (1 : ℝ) / p := by
        rw [recipSumIoc]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
    _ ≤ D.δ (i - 1) + D.δ i := by
        rw [δ, δ, ← Finset.sum_union_inter]
        have : (0 : ℝ) ≤ ∑ p ∈ D.B (i - 1) ∩ D.B i, (1 : ℝ) / p :=
          Finset.sum_nonneg (fun q _ => by positivity)
        linarith

/-- `∑_{p≤y, p∈S} 1/p ≥ ∑_{i'<i−1} δᵢ'` once `y ≥ xᵢ₋₁`. -/
theorem recipSumLe_ge (i y : ℕ) (hy : D.x (i - 1) ≤ y) :
    ∑ i' ∈ Finset.range (i - 1), D.δ i' ≤ recipSumLe D.set y := by
  have heq : ∑ i' ∈ Finset.range (i - 1), D.δ i'
      = ∑ p ∈ (Finset.range (i - 1)).biUnion D.B, (1 : ℝ) / p := by
    rw [Finset.sum_biUnion (D.B_pairwiseDisjoint _)]
    rfl
  rw [heq, recipSumLe]
  exact Finset.sum_le_sum_of_subset_of_nonneg (D.biUnion_subset_filter i y hy)
    (fun q _ _ => by positivity)

/-- `∑_{p≤y, p∈S} 1/p ≤ ∑_{i'≤i+1} δᵢ'` once `y ≤ xᵢ₊₂`. -/
theorem recipSumLe_le (i y : ℕ) (hy : y ≤ D.x (i + 2)) :
    recipSumLe D.set y ≤ ∑ i' ∈ Finset.range (i + 2), D.δ i' := by
  have heq : ∑ i' ∈ Finset.range (i + 2), D.δ i'
      = ∑ p ∈ (Finset.range (i + 2)).biUnion D.B, (1 : ℝ) / p := by
    rw [Finset.sum_biUnion (D.B_pairwiseDisjoint _)]
    rfl
  have hsub : (Finset.Iic y).filter (fun p => p.Prime ∧ D.set p)
      ⊆ (Finset.range (i + 2)).biUnion D.B := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Iic] at hp
    obtain ⟨k, hk⟩ := hp.2.2
    obtain ⟨-, hkl, -⟩ := D.B_prime k p hk
    have hklt : k < i + 2 := by
      by_contra hc
      have := D.x_mono.monotone (show i + 2 ≤ k by omega)
      omega
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hklt, hk⟩
  rw [heq, recipSumLe]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)

/-- `blockIndex N → ∞`. -/
theorem blockIndex_tendsto : Tendsto D.blockIndex atTop atTop := by
  refine tendsto_atTop_atTop.mpr (fun b => ⟨D.x b + 1, fun N hN => ?_⟩)
  have hxb : b ≤ D.x b := D.x_mono.le_apply
  exact Nat.le_findGreatest (by omega) (by omega)

/-- `x (blockIndex N) < N ≤ x (blockIndex N + 1)` for `N > x 0`. -/
theorem blockIndex_spec (N : ℕ) (hN : D.x 0 < N) :
    D.x (D.blockIndex N) < N ∧ N ≤ D.x (D.blockIndex N + 1) := by
  have hspec : D.x (D.blockIndex N) < N :=
    Nat.findGreatest_spec (P := fun i => D.x i < N) (Nat.zero_le N) hN
  refine ⟨hspec, ?_⟩
  have hle : D.blockIndex N ≤ N := Nat.findGreatest_le N
  have hlt : D.blockIndex N < N := by
    rcases eq_or_lt_of_le hle with heq | h
    · exfalso
      have : N ≤ D.x N := D.x_mono.le_apply
      rw [heq] at hspec
      omega
    · exact h
  have := Nat.findGreatest_is_greatest (P := fun i => D.x i < N)
    (show D.blockIndex N < D.blockIndex N + 1 by omega) (by omega)
  omega

/-- Divergence of `∑ δᵢ` gives divergence of `∑_{p∈S} 1/p`. -/
theorem divergentRecip (hδ : ¬ Summable D.δ) : DivergentRecip D.set := by
  rw [DivergentRecip]
  intro hsum
  refine hδ ?_
  set f : ℕ → ℝ := fun p => if p.Prime ∧ D.set p then (1 : ℝ) / p else 0 with hf
  have hf0 : ∀ p, 0 ≤ f p := by intro p; rw [hf]; dsimp only; split_ifs <;> positivity
  have hδ0 : ∀ i, 0 ≤ D.δ i := fun i => Finset.sum_nonneg (fun p _ => by positivity)
  refine summable_of_sum_range_le (c := ∑' p, f p) hδ0 (fun n => ?_)
  have heq : ∑ i ∈ Finset.range n, D.δ i = ∑ p ∈ (Finset.range n).biUnion D.B, f p := by
    rw [Finset.sum_biUnion (D.B_pairwiseDisjoint _)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [δ]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    obtain ⟨hprime, -, -⟩ := D.B_prime i p hp
    have hmem : Nat.Prime p ∧ D.set p := ⟨hprime, ⟨i, hp⟩⟩
    rw [hf]
    simp only [if_pos hmem]
  rw [heq]
  exact hsum.sum_le_tsum _ (fun p _ => hf0 p)

/-- The KMT means vanish along the block schedule: `KMT_quant` at scale `N` in block `i` with
`ε = εᵢ`, `J = Jᵢ`, the three bounds above, and `Good.terms`. -/
theorem kmt_along {C : ℕ → ℝ} (hKMT : KMT_quant C) (hG : D.Good C) :
    KMT_along D.set D.sched := by
  intro h hh
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  have hterms := hG.terms.comp D.blockIndex_tendsto
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hterms
  filter_upwards [eventually_gt_atTop (D.x 0), eventually_ge_atTop 3,
    (hG.J_tendsto.comp D.blockIndex_tendsto).eventually_ge_atTop (h.natAbs + 1),
    D.blockIndex_tendsto.eventually_ge_atTop 1]
    with N hN hN3 hJ hbi1
  obtain ⟨hspec1, hspec2⟩ := D.blockIndex_spec N hN
  have hntw : NontrivialWindow (D.J (D.blockIndex N)) h :=
    ⟨h.natAbs + 1, by omega, hJ, nontrivial_site hh⟩
  obtain ⟨hε1, hε2⟩ := hG.ε_range (D.blockIndex N) N hspec1
  have hb := hKMT D.set (D.J (D.blockIndex N)) h hh hntw N hN3 (D.ε (D.blockIndex N)) hε1 hε2
  have hy : D.x (D.blockIndex N - 1) ≤ ⌊(N : ℝ) ^ D.ε (D.blockIndex N)⌋₊ :=
    hG.sep (D.blockIndex N) N hbi1 hspec1
  have hIoc := D.recipSumIoc_le (D.blockIndex N) N ⌊(N : ℝ) ^ D.ε (D.blockIndex N)⌋₊
    hspec1 hspec2 hy
  have hLe := D.recipSumLe_ge (D.blockIndex N) ⌊(N : ℝ) ^ D.ε (D.blockIndex N)⌋₊ hy
  set A : ℝ := Real.sqrt (Real.log (1 / D.ε (D.blockIndex N)))
      * Real.sqrt (2 * recipSumIoc D.set ⌊(N : ℝ) ^ D.ε (D.blockIndex N)⌋₊ N)
    + Real.exp (- recipSumLe D.set ⌊(N : ℝ) ^ D.ε (D.blockIndex N)⌋₊)
    + Real.exp (- 1 / (8 * (D.J (D.blockIndex N) : ℝ) ^ 2 * D.ε (D.blockIndex N))) with hA
  set B : ℝ := Real.sqrt (Real.log (1 / D.ε (D.blockIndex N)))
      * Real.sqrt (2 * (D.δ (D.blockIndex N - 1) + D.δ (D.blockIndex N)))
    + Real.exp (- ∑ i' ∈ Finset.range (D.blockIndex N - 1), D.δ i')
    + Real.exp (- 1 / (8 * (D.J (D.blockIndex N) : ℝ) ^ 2 * D.ε (D.blockIndex N))) with hB
  have hApos : 0 < A := by
    rw [hA]
    have h1 : 0 ≤ Real.sqrt (Real.log (1 / D.ε (D.blockIndex N)))
        * Real.sqrt (2 * recipSumIoc D.set ⌊(N : ℝ) ^ D.ε (D.blockIndex N)⌋₊ N) := by positivity
    have h2 : 0 < Real.exp (- recipSumLe D.set ⌊(N : ℝ) ^ D.ε (D.blockIndex N)⌋₊) :=
      Real.exp_pos _
    have h3 : 0 < Real.exp (- 1 / (8 * (D.J (D.blockIndex N) : ℝ) ^ 2
      * D.ε (D.blockIndex N))) := Real.exp_pos _
    linarith
  have hC : 0 ≤ C (D.J (D.blockIndex N)) := by
    by_contra hc
    push_neg at hc
    nlinarith [norm_nonneg (windowMeanS D.set (D.J (D.blockIndex N)) h N), hb,
      mul_neg_of_neg_of_pos hc hApos]
  have hAB : A ≤ B := by
    rw [hA, hB]
    have hsq : Real.sqrt (2 * recipSumIoc D.set ⌊(N : ℝ) ^ D.ε (D.blockIndex N)⌋₊ N)
        ≤ Real.sqrt (2 * (D.δ (D.blockIndex N - 1) + D.δ (D.blockIndex N))) :=
      Real.sqrt_le_sqrt (by linarith)
    have hmul : Real.sqrt (Real.log (1 / D.ε (D.blockIndex N)))
        * Real.sqrt (2 * recipSumIoc D.set ⌊(N : ℝ) ^ D.ε (D.blockIndex N)⌋₊ N)
        ≤ Real.sqrt (Real.log (1 / D.ε (D.blockIndex N)))
        * Real.sqrt (2 * (D.δ (D.blockIndex N - 1) + D.δ (D.blockIndex N))) :=
      mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
    have hexp : Real.exp (- recipSumLe D.set ⌊(N : ℝ) ^ D.ε (D.blockIndex N)⌋₊)
        ≤ Real.exp (- ∑ i' ∈ Finset.range (D.blockIndex N - 1), D.δ i') :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have hsched : D.sched N = D.J (D.blockIndex N) := rfl
  calc ‖windowMeanS D.set (D.sched N) h N‖
      = ‖windowMeanS D.set (D.J (D.blockIndex N)) h N‖ := by rw [hsched]
    _ ≤ C (D.J (D.blockIndex N)) * A := hb
    _ ≤ C (D.J (D.blockIndex N)) * B := mul_le_mul_of_nonneg_left hAB hC
    _ = ((fun i => C (D.J i) *
          (Real.sqrt (Real.log (1 / D.ε i)) * Real.sqrt (2 * (D.δ (i - 1) + D.δ i))
            + Real.exp (- ∑ i' ∈ Finset.range (i - 1), D.δ i')
            + Real.exp (- 1 / (8 * (D.J i : ℝ) ^ 2 * D.ε i)))) ∘ D.blockIndex) N := by
        simp only [Function.comp_apply]
        rw [hB]

/-- The L¹ tail vanishes along the block schedule: `tail_error_L1` + `recipSumLe_le` +
`Good.tail`. -/
theorem tailOK {C : ℕ → ℝ} (hG : D.Good C) : TailOK D.set D.sched := by
  rw [TailOK]
  have h2 : Tendsto (fun i => (5 * (D.J i : ℝ) + 11) / (4 : ℝ) ^ D.J i) atTop (𝓝 0) :=
    tendsto_lin_div_pow.comp hG.J_tendsto
  have hGto : Tendsto (fun i => (∑ i' ∈ Finset.range (i + 2), D.δ i' + 1) / (4 : ℝ) ^ D.J i
      + (5 * (D.J i : ℝ) + 11) / (4 : ℝ) ^ D.J i) atTop (𝓝 0) := by
    simpa using hG.tail.add h2
  have hcomp := hGto.comp D.blockIndex_tendsto
  refine squeeze_zero' (Eventually.of_forall (fun N =>
    div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Nat.cast_nonneg N))) ?_ hcomp
  filter_upwards [eventually_gt_atTop (D.x 0), eventually_ge_atTop 1] with N hN hN1
  obtain ⟨hspec1, hspec2⟩ := D.blockIndex_spec N hN
  have h2N : 2 * N ≤ D.x (D.blockIndex N + 2) :=
    le_trans (by have := hG.x_double (D.blockIndex N); omega) (le_refl _)
  have hrec := D.recipSumLe_le (D.blockIndex N) (2 * N) h2N
  have hsched : D.sched N = D.J (D.blockIndex N) := rfl
  calc (∑ n ∈ Finset.range N,
        |(TWeight.subset D.set).tailB 4 n - truncTailS D.set (D.sched N) n|) / N
      ≤ (recipSumLe D.set (2 * N) + 5 * (D.sched N) + 12) / (4 : ℝ) ^ (D.sched N) :=
        tail_error_L1 D.set (D.sched N) N hN1
    _ = (recipSumLe D.set (2 * N) + 5 * (D.J (D.blockIndex N) : ℝ) + 12)
          / (4 : ℝ) ^ (D.J (D.blockIndex N)) := by rw [hsched]
    _ ≤ (∑ i' ∈ Finset.range (D.blockIndex N + 2), D.δ i' + 5 * (D.J (D.blockIndex N) : ℝ) + 12)
          / (4 : ℝ) ^ (D.J (D.blockIndex N)) := by gcongr
    _ = (∑ i' ∈ Finset.range (D.blockIndex N + 2), D.δ i' + 1)
            / (4 : ℝ) ^ (D.J (D.blockIndex N))
          + (5 * (D.J (D.blockIndex N) : ℝ) + 11) / (4 : ℝ) ^ (D.J (D.blockIndex N)) := by
        rw [← add_div]
        ring_nf
    _ = ((fun i => (∑ i' ∈ Finset.range (i + 2), D.δ i' + 1) / (4 : ℝ) ^ D.J i
          + (5 * (D.J i : ℝ) + 11) / (4 : ℝ) ^ D.J i) ∘ D.blockIndex) N := rfl

end BlockData

/-- Greedy block: a finite set of primes above `y` with reciprocal sum in `[δ, δ + 1/y]`
(take primes `> y` in order until the sum exceeds `δ`; `∑_{p>y} 1/p = ∞` from
`log_log_le_sum_inv_primesBelow`). -/
theorem exists_block (y : ℕ) (hy : 1 ≤ y) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : Finset ℕ, (∀ p ∈ B, p.Prime ∧ y < p) ∧
      δ ≤ ∑ p ∈ B, (1 : ℝ) / p ∧ ∑ p ∈ B, (1 : ℝ) / p ≤ δ + 1 / y := by
  classical
  set T : ℕ → ℝ := fun n => ∑ p ∈ (Finset.Ioc y n).filter Nat.Prime, (1 : ℝ) / p with hT
  set K : ℝ := ∑ p ∈ (y + 1).primesBelow, (p : ℝ)⁻¹ with hK
  have hsplit : ∀ n : ℕ, y ≤ n → ∑ p ∈ (n + 1).primesBelow, (p : ℝ)⁻¹ = K + T n := by
    intro n hn
    have hset : (n + 1).primesBelow
        = ((y + 1).primesBelow) ∪ ((Finset.Ioc y n).filter Nat.Prime) := by
      ext q
      simp only [Nat.mem_primesBelow, Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨hq, hp⟩
        by_cases hc : q ≤ y
        · exact Or.inl ⟨by omega, hp⟩
        · exact Or.inr ⟨⟨by omega, by omega⟩, hp⟩
      · rintro (⟨hq, hp⟩ | ⟨⟨h1, h2⟩, hp⟩)
        · exact ⟨by omega, hp⟩
        · exact ⟨by omega, hp⟩
    have hdisj : Disjoint ((y + 1).primesBelow) ((Finset.Ioc y n).filter Nat.Prime) := by
      refine Finset.disjoint_left.mpr (fun q hq1 hq2 => ?_)
      rw [Nat.mem_primesBelow] at hq1
      rw [Finset.mem_filter, Finset.mem_Ioc] at hq2
      omega
    rw [hset, Finset.sum_union hdisj, hK, hT]
    congr 1
    exact Finset.sum_congr rfl (fun q _ => by rw [one_div])
  -- divergence gives some `n` with `δ ≤ T n`
  have htend : Tendsto (fun n : ℕ => Real.log (Real.log ((n : ℝ) + 1))) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp h1)
  obtain ⟨n, hn2, hn1⟩ :=
    ((htend.eventually_ge_atTop (δ + K + 1)).and (eventually_ge_atTop y)).exists
  have hex : ∃ n, δ ≤ T n := by
    refine ⟨n, ?_⟩
    have hM := log_log_le_sum_inv_primesBelow (n + 1) (by omega)
    rw [hsplit n hn1] at hM
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hM
    linarith
  set n₀ := Nat.find hex with hn₀
  have hspec : δ ≤ T n₀ := Nat.find_spec hex
  have hgt : y < n₀ := by
    by_contra hc
    have hempty : Finset.Ioc y n₀ = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hT] at hspec
    simp only [hempty, Finset.filter_empty, Finset.sum_empty] at hspec
    linarith
  have hmin : ¬ (δ ≤ T (n₀ - 1)) := Nat.find_min hex (by omega)
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hstep : T n₀ ≤ T (n₀ - 1) + 1 / (y : ℝ) := by
    have hIoc : Finset.Ioc y n₀ = insert n₀ (Finset.Ioc y (n₀ - 1)) := by
      ext q
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    have hnotmem : n₀ ∉ (Finset.Ioc y (n₀ - 1)).filter Nat.Prime := by
      rw [Finset.mem_filter, Finset.mem_Ioc]
      rintro ⟨⟨-, h2⟩, -⟩
      omega
    rw [hT]
    simp only
    rw [hIoc, Finset.filter_insert]
    by_cases hp : Nat.Prime n₀
    · rw [if_pos hp, Finset.sum_insert hnotmem]
      have hle : (1 : ℝ) / n₀ ≤ 1 / y := by
        refine one_div_le_one_div_of_le hyR ?_
        exact_mod_cast le_of_lt hgt
      linarith
    · rw [if_neg hp]
      have : (0 : ℝ) < 1 / y := by positivity
      linarith
  refine ⟨(Finset.Ioc y n₀).filter Nat.Prime, ?_, hspec, ?_⟩
  · intro q hq
    rw [Finset.mem_filter, Finset.mem_Ioc] at hq
    exact ⟨hq.2, hq.1.1⟩
  · push_neg at hmin
    have : T n₀ = ∑ p ∈ (Finset.Ioc y n₀).filter Nat.Prime, (1 : ℝ) / p := rfl
    linarith [hstep, hmin.le]

/-! ### The explicit schedule for `exists_good`

`Jᵢ := max{J ≤ i : ∀ J' ≤ J, |C J'| ≤ ⁴√i}` (so `|C Jᵢ| ≤ ⁴√i`, and by maximality
`log i ≤ 4 log|C(Jᵢ+1)| = o(4^{Jᵢ})`); `εᵢ := 1/Kᵢ` with `Kᵢ := 8(i+3)³` (so `εᵢ < 1/2` and
`1/(8Jᵢ²εᵢ) = (i+3)³/Jᵢ² ≥ i`); `Bᵢ := ` a greedy block above `xᵢ` of mass `≈ 1/(i+1)`;
`x₀ := ⌈exp exp K₀⌉`, `xᵢ₊₁ := max(2xᵢ+1, ⌈exp exp Kᵢ₊₁⌉, xᵢ^{Kᵢ₊₁}, max Bᵢ)`. -/

namespace GoodExists

/-- `Kᵢ = 8(i+3)³ = 1/εᵢ`. -/
def Kn (i : ℕ) : ℕ := 8 * (i + 3) ^ 3

/-- `εᵢ = 1/Kᵢ`. -/
noncomputable def epsF (i : ℕ) : ℝ := 1 / (Kn i : ℝ)

/-- `⌈exp exp Kᵢ⌉`: the cut point must exceed this for `ε_range`. -/
noncomputable def EF (i : ℕ) : ℕ := ⌈Real.exp (Real.exp (Kn i))⌉₊

open Classical in
/-- `Jᵢ`: the greatest `J ≤ i` with `|C J'| ≤ ⁴√i` for all `J' ≤ J`. -/
noncomputable def JF (C : ℕ → ℝ) (i : ℕ) : ℕ :=
  Nat.findGreatest (fun J => ∀ J' ≤ J, |C J'| ≤ Real.sqrt (Real.sqrt i)) i

/-- The greedy block above `y` of mass `≈ 1/(i+1)`. -/
noncomputable def blkAux (y i : ℕ) (hy : 1 ≤ y) : Finset ℕ :=
  (exists_block y hy ((1 : ℝ) / ((i : ℝ) + 1)) (by positivity)).choose

theorem blkAux_spec (y i : ℕ) (hy : 1 ≤ y) :
    (∀ p ∈ blkAux y i hy, p.Prime ∧ y < p) ∧
      (1 : ℝ) / ((i : ℝ) + 1) ≤ ∑ p ∈ blkAux y i hy, (1 : ℝ) / p ∧
      ∑ p ∈ blkAux y i hy, (1 : ℝ) / p ≤ (1 : ℝ) / ((i : ℝ) + 1) + 1 / y :=
  (exists_block y hy ((1 : ℝ) / ((i : ℝ) + 1)) (by positivity)).choose_spec

noncomputable def blk (y i : ℕ) : Finset ℕ := if h : 1 ≤ y then blkAux y i h else ∅

/-- The cut points. -/
noncomputable def XF : ℕ → ℕ
  | 0 => EF 0
  | i + 1 => max (max (2 * XF i + 1) (EF (i + 1)))
      (max ((XF i) ^ Kn (i + 1)) ((blk (XF i) i).sup id))

theorem Kn_pos (i : ℕ) : 0 < Kn i := by unfold Kn; positivity

theorem Kn_ge (i : ℕ) : 216 ≤ Kn i := by
  have h : 3 ^ 3 ≤ (i + 3) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  simp only [Kn]
  omega

theorem epsF_pos (i : ℕ) : 0 < epsF i := by
  unfold epsF
  have : (0 : ℝ) < (Kn i : ℝ) := by exact_mod_cast Kn_pos i
  positivity

theorem epsF_lt (i : ℕ) : epsF i < 1 / 2 := by
  unfold epsF
  have h : (216 : ℝ) ≤ (Kn i : ℝ) := by exact_mod_cast Kn_ge i
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
  linarith

theorem one_le_EF (i : ℕ) : 1 ≤ EF i := by
  have h1 : (1 : ℝ) ≤ Real.exp (Real.exp (Kn i)) := Real.one_le_exp (Real.exp_pos _).le
  simp only [EF]
  exact Nat.one_le_ceil_iff.mpr (by linarith)

theorem EF_le (i : ℕ) : Real.exp (Real.exp (Kn i)) ≤ (EF i : ℝ) := Nat.le_ceil _

theorem XF_succ_eq (i : ℕ) : XF (i + 1) = max (max (2 * XF i + 1) (EF (i + 1)))
    (max ((XF i) ^ Kn (i + 1)) ((blk (XF i) i).sup id)) := rfl

theorem XF_ge_EF (i : ℕ) : EF i ≤ XF i := by
  cases i with
  | zero => exact le_refl _
  | succ n => rw [XF_succ_eq]; omega

theorem XF_succ_ge (i : ℕ) : 2 * XF i + 1 ≤ XF (i + 1) := by rw [XF_succ_eq]; omega

theorem XF_ge_pow (i : ℕ) : (XF i) ^ Kn (i + 1) ≤ XF (i + 1) := by rw [XF_succ_eq]; omega

theorem XF_ge_sup (i : ℕ) : (blk (XF i) i).sup id ≤ XF (i + 1) := by rw [XF_succ_eq]; omega

theorem XF_ge (i : ℕ) : i + 1 ≤ XF i := by
  induction i with
  | zero => exact le_trans (one_le_EF 0) (XF_ge_EF 0)
  | succ n ih => have := XF_succ_ge n; omega

theorem one_le_XF (i : ℕ) : 1 ≤ XF i := by have := XF_ge i; omega

theorem XF_strictMono : StrictMono XF := by
  refine strictMono_nat_of_lt_succ (fun n => ?_)
  have := XF_succ_ge n
  have := one_le_XF n
  omega

/-- The block data of the explicit schedule. -/
noncomputable def DD (C : ℕ → ℝ) : BlockData where
  x := XF
  B := fun i => blk (XF i) i
  J := JF C
  ε := epsF
  x_mono := XF_strictMono
  B_prime := by
    intro i p hp
    have hy : 1 ≤ XF i := one_le_XF i
    have hmem : p ∈ blkAux (XF i) i hy := by
      rw [show blk (XF i) i = blkAux (XF i) i hy from dif_pos hy] at hp; exact hp
    obtain ⟨hprime, hgt⟩ := (blkAux_spec (XF i) i hy).1 p hmem
    refine ⟨hprime, hgt, ?_⟩
    refine le_trans ?_ (XF_ge_sup i)
    exact Finset.le_sup (f := id) hp

theorem DD_delta (C : ℕ → ℝ) (i : ℕ) :
    (DD C).δ i = ∑ p ∈ blk (XF i) i, (1 : ℝ) / p := rfl

/-! #### Leaves -/

/-- Leaf 3a: `δᵢ ≥ 1/(i+1)`. -/
theorem delta_ge (C : ℕ → ℝ) (i : ℕ) : (1 : ℝ) / ((i : ℝ) + 1) ≤ (DD C).δ i := by
  have hy : 1 ≤ XF i := one_le_XF i
  rw [DD_delta, show blk (XF i) i = blkAux (XF i) i hy from dif_pos hy]
  exact (blkAux_spec (XF i) i hy).2.1

/-- Leaf 3b: `δᵢ ≤ 2/(i+1)`. -/
theorem delta_le (C : ℕ → ℝ) (i : ℕ) : (DD C).δ i ≤ 2 / ((i : ℝ) + 1) := by
  have hy : 1 ≤ XF i := one_le_XF i
  rw [DD_delta, show blk (XF i) i = blkAux (XF i) i hy from dif_pos hy]
  have h := (blkAux_spec (XF i) i hy).2.2
  have hx : ((i : ℝ) + 1) ≤ (XF i : ℝ) := by
    have := XF_ge i
    have : ((i + 1 : ℕ) : ℝ) ≤ (XF i : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have hpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have : (1 : ℝ) / (XF i : ℝ) ≤ 1 / ((i : ℝ) + 1) := by
    apply one_div_le_one_div_of_le hpos hx
  have h2 : (2 : ℝ) / ((i : ℝ) + 1) = 1 / ((i : ℝ) + 1) + 1 / ((i : ℝ) + 1) := by ring
  rw [h2]
  linarith

/-- Harmonic lower bound. -/
theorem harm_lower (m : ℕ) :
    Real.log ((m : ℝ) + 1) ≤ ∑ k ∈ Finset.range m, (1 : ℝ) / ((k : ℝ) + 1) := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hstep : Real.log (((n : ℝ) + 1) + 1) - Real.log ((n : ℝ) + 1)
        ≤ 1 / ((n : ℝ) + 1) := by
      have hdiv : Real.log ((((n : ℝ) + 1) + 1) / ((n : ℝ) + 1))
          ≤ (((n : ℝ) + 1) + 1) / ((n : ℝ) + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at hdiv
      have : (((n : ℝ) + 1) + 1) / ((n : ℝ) + 1) - 1 = 1 / ((n : ℝ) + 1) := by
        field_simp; ring
      linarith
    have hcast : ((n : ℕ) + 1 : ℕ) = (n : ℕ) + 1 := rfl
    push_cast
    push_cast at ih
    linarith

/-- Harmonic upper bound. -/
theorem harm_upper (m : ℕ) :
    ∑ k ∈ Finset.range m, (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 + Real.log m := by
  induction m with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Finset.sum_range_succ]
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hstep : 1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
        have hdiv : Real.log ((n : ℝ) / ((n : ℝ) + 1)) ≤ (n : ℝ) / ((n : ℝ) + 1) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        rw [Real.log_div (by positivity) (by positivity)] at hdiv
        have : (n : ℝ) / ((n : ℝ) + 1) - 1 = - (1 / ((n : ℝ) + 1)) := by field_simp; ring
        rw [this] at hdiv
        linarith
      push_cast
      linarith

/-- Leaf 3: `∑ δᵢ = ∞`. -/
theorem delta_div (C : ℕ → ℝ) : ¬ Summable (DD C).δ := by
  intro hsum
  have hcomp : Summable (fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 1)) := by
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => delta_ge C i) hsum
  refine Real.not_summable_one_div_natCast ?_
  rw [← summable_nat_add_iff 1]
  simpa using hcomp

/-- Leaf 4a: the `ε`-range. -/
theorem eps_range (_C : ℕ → ℝ) (i N : ℕ) (hN : XF i < N) :
    1 / Real.log (Real.log N) < epsF i ∧ epsF i < 1 / 2 := by
  refine ⟨?_, epsF_lt i⟩
  have hK : (0 : ℝ) < (Kn i : ℝ) := by exact_mod_cast Kn_pos i
  have h1 : Real.exp (Real.exp (Kn i)) < (N : ℝ) := by
    have hE : Real.exp (Real.exp (Kn i)) ≤ (EF i : ℝ) := EF_le i
    have hX : (EF i : ℝ) ≤ (XF i : ℝ) := by exact_mod_cast XF_ge_EF i
    have hNN : (XF i : ℝ) < (N : ℝ) := by exact_mod_cast hN
    linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_trans (Real.exp_pos _) h1
  have hlogN : Real.exp (Kn i) < Real.log N :=
    (Real.lt_log_iff_exp_lt hNpos).mpr h1
  have hlogpos : (0 : ℝ) < Real.log N := lt_trans (Real.exp_pos _) hlogN
  have h2 : (Kn i : ℝ) < Real.log (Real.log N) :=
    (Real.lt_log_iff_exp_lt hlogpos).mpr hlogN
  rw [epsF]
  exact one_div_lt_one_div_of_lt hK h2

/-- Leaf 4b: separation. -/
theorem sep_holds (C : ℕ → ℝ) (i N : ℕ) (hi : 1 ≤ i) (hN : XF i < N) :
    XF (i - 1) ≤ ⌊(N : ℝ) ^ epsF i⌋₊ := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  refine Nat.le_floor ?_
  set K : ℕ := Kn (j + 1) with hKdef
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast Kn_pos (j + 1)
  have ha : (1 : ℝ) ≤ (XF j : ℝ) := by exact_mod_cast one_le_XF j
  have hpow : ((XF j : ℝ)) ^ (K : ℕ) ≤ (N : ℝ) := by
    have h1 : (XF j) ^ K ≤ XF (j + 1) := XF_ge_pow j
    have h2 : (XF j) ^ K ≤ N := by omega
    exact_mod_cast h2
  have hmono : ((XF j : ℝ) ^ (K : ℕ)) ^ epsF (j + 1) ≤ (N : ℝ) ^ epsF (j + 1) :=
    Real.rpow_le_rpow (by positivity) hpow (epsF_pos _).le
  have hid : ((XF j : ℝ) ^ (K : ℕ)) ^ epsF (j + 1) = (XF j : ℝ) := by
    rw [← Real.rpow_natCast (XF j : ℝ) K, ← Real.rpow_mul (by linarith), epsF, ← hKdef]
    rw [mul_one_div, div_self (ne_of_gt hK0), Real.rpow_one]
  linarith [hid ▸ hmono]

/-- `⁴√i → ∞`. -/
theorem tendsto_qsqrt : Tendsto (fun i : ℕ => Real.sqrt (Real.sqrt i)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

/-- Every `J' ≤ Jᵢ` satisfies the defining bound (given that `J' = 0` does). -/
theorem JF_spec (C : ℕ → ℝ) (i : ℕ) (h0 : |C 0| ≤ Real.sqrt (Real.sqrt i)) :
    ∀ J' ≤ JF C i, |C J'| ≤ Real.sqrt (Real.sqrt i) := by
  classical
  refine Nat.findGreatest_spec (P := fun J => ∀ J' ≤ J, |C J'| ≤ Real.sqrt (Real.sqrt i))
    (Nat.zero_le i) ?_
  intro J' hJ'
  rw [Nat.le_zero.mp hJ']
  exact h0

theorem JF_le (C : ℕ → ℝ) (i : ℕ) : JF C i ≤ i := Nat.findGreatest_le i

/-- Maximality: if `Jᵢ < i` then `|C (Jᵢ+1)| > ⁴√i`. -/
theorem JF_max (C : ℕ → ℝ) (i : ℕ) (h0 : |C 0| ≤ Real.sqrt (Real.sqrt i)) (hlt : JF C i < i) :
    Real.sqrt (Real.sqrt i) < |C (JF C i + 1)| := by
  classical
  have hng : ¬ (∀ J' ≤ JF C i + 1, |C J'| ≤ Real.sqrt (Real.sqrt i)) :=
    Nat.findGreatest_is_greatest (P := fun J => ∀ J' ≤ J, |C J'| ≤ Real.sqrt (Real.sqrt i))
      (k := JF C i + 1) (Nat.lt_succ_self _) (by omega)
  push_neg at hng
  obtain ⟨J', hJ', hgt⟩ := hng
  rcases Nat.lt_or_ge J' (JF C i + 1) with hc | hc
  · exact absurd (JF_spec C i h0 J' (by omega)) (not_le.mpr hgt)
  · have : J' = JF C i + 1 := by omega
    rw [this] at hgt; exact hgt

/-- Leaf 1a: `Jᵢ → ∞`. -/
theorem JF_tendsto (C : ℕ → ℝ) : Tendsto (JF C) atTop atTop := by
  refine tendsto_atTop.mpr (fun m => ?_)
  have hb : ∀ J' ≤ m, |C J'| ≤ ∑ J'' ∈ Finset.range (m + 1), |C J''| := by
    intro J' hJ'
    refine Finset.single_le_sum (f := fun J'' => |C J''|) (fun _ _ => abs_nonneg _) ?_
    exact Finset.mem_range.mpr (by omega)
  filter_upwards [eventually_ge_atTop m,
    tendsto_qsqrt.eventually_ge_atTop (∑ J'' ∈ Finset.range (m + 1), |C J''|)]
    with i him hbig
  exact Nat.le_findGreatest him (fun J' hJ' => le_trans (hb J' hJ') hbig)

/-- Leaf 1b: `|C Jᵢ| ≤ ⁴√i` eventually. -/
theorem JF_C_le (C : ℕ → ℝ) : ∀ᶠ i : ℕ in atTop, |C (JF C i)| ≤ Real.sqrt (Real.sqrt i) := by
  filter_upwards [tendsto_qsqrt.eventually_ge_atTop |C 0|] with i hi
  exact JF_spec C i hi _ (le_refl _)

/-- Leaf 1c: `log i = o(4^{Jᵢ})`. -/
theorem log_div_self_tendsto : Tendsto (fun i : ℕ => Real.log i / (i : ℝ)) atTop (𝓝 0) :=
  (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop

/-- `log i / 4^i → 0`, crudely from `i ≤ 4^i`. -/
theorem log_div_four_pow : Tendsto (fun i : ℕ => Real.log i / (4 : ℝ) ^ i) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ log_div_self_tendsto
  · filter_upwards [eventually_ge_atTop 1] with i hi
    have : (0 : ℝ) ≤ Real.log i := Real.log_natCast_nonneg i
    positivity
  · filter_upwards [eventually_ge_atTop 1] with i hi
    have hlog : (0 : ℝ) ≤ Real.log i := Real.log_natCast_nonneg i
    have hip : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
    have h4 : (i : ℝ) ≤ (4 : ℝ) ^ i := by
      have : i < 4 ^ i := Nat.lt_pow_self (by norm_num)
      calc (i : ℝ) ≤ ((4 ^ i : ℕ) : ℝ) := by exact_mod_cast this.le
        _ = (4 : ℝ) ^ i := by push_cast; ring
    exact div_le_div_of_nonneg_left hlog hip h4

theorem log_o_pow (C : ℕ → ℝ)
    (hgrow : Tendsto (fun k : ℕ => Real.log (C k) / 4 ^ k) atTop (𝓝 0)) :
    Tendsto (fun i : ℕ => Real.log i / (4 : ℝ) ^ JF C i) atTop (𝓝 0) := by
  have hJ1 : Tendsto (fun i => JF C i + 1) atTop atTop :=
    tendsto_atTop_mono (fun i => Nat.le_succ _) (JF_tendsto C)
  have hg : Tendsto (fun i : ℕ => |Real.log (C (JF C i + 1)) / 4 ^ (JF C i + 1)|)
      atTop (𝓝 0) := by
    have := (hgrow.comp hJ1).abs
    simpa using this
  have hbd : Tendsto (fun i : ℕ => 16 * |Real.log (C (JF C i + 1)) / 4 ^ (JF C i + 1)|
      + Real.log i / (4 : ℝ) ^ i) atTop (𝓝 0) := by
    simpa using (hg.const_mul 16).add log_div_four_pow
  refine squeeze_zero' ?_ ?_ hbd
  · filter_upwards [eventually_ge_atTop 1] with i hi
    have : (0 : ℝ) ≤ Real.log i := Real.log_natCast_nonneg i
    positivity
  · filter_upwards [eventually_ge_atTop 1, tendsto_qsqrt.eventually_ge_atTop |C 0|] with i hi h0
    have hlog : (0 : ℝ) ≤ Real.log i := Real.log_natCast_nonneg i
    have hpow : (0 : ℝ) < (4 : ℝ) ^ JF C i := by positivity
    have habs : (0 : ℝ) ≤ |Real.log (C (JF C i + 1)) / 4 ^ (JF C i + 1)| := abs_nonneg _
    rcases eq_or_lt_of_le (JF_le C i) with heq | hlt
    · have hrw : Real.log i / (4 : ℝ) ^ JF C i = Real.log i / (4 : ℝ) ^ i := by rw [heq]
      rw [hrw]
      have : (0 : ℝ) ≤ 16 * |Real.log (C (JF C i + 1)) / 4 ^ (JF C i + 1)| := by positivity
      linarith
    · have hmax := JF_max C i h0 hlt
      have hq : (0 : ℝ) < Real.sqrt (Real.sqrt i) := by
        have : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
        have h1 : (0 : ℝ) < Real.sqrt i := Real.sqrt_pos.mpr (by linarith)
        exact Real.sqrt_pos.mpr h1
      have hlogle : Real.log (Real.sqrt (Real.sqrt i)) ≤ Real.log |C (JF C i + 1)| :=
        Real.log_le_log hq hmax.le
      have hq4 : Real.log (Real.sqrt (Real.sqrt i)) = Real.log i / 4 := by
        rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt (by positivity)]
        ring
      rw [hq4, Real.log_abs] at hlogle
      have hnum : Real.log i ≤ 4 * Real.log (C (JF C i + 1)) := by linarith
      have hkey : Real.log i / (4 : ℝ) ^ JF C i
          ≤ 4 * (Real.log (C (JF C i + 1)) / (4 : ℝ) ^ JF C i) := by
        rw [mul_div_assoc']
        exact div_le_div_of_nonneg_right hnum hpow.le
      have hrw : 4 * (Real.log (C (JF C i + 1)) / (4 : ℝ) ^ JF C i)
          = 16 * (Real.log (C (JF C i + 1)) / (4 : ℝ) ^ (JF C i + 1)) := by
        rw [pow_succ]
        field_simp
        ring
      have hle2 : Real.log (C (JF C i + 1)) / (4 : ℝ) ^ (JF C i + 1)
          ≤ |Real.log (C (JF C i + 1)) / 4 ^ (JF C i + 1)| := le_abs_self _
      rw [hrw] at hkey
      have hlog4 : (0 : ℝ) ≤ Real.log i / (4 : ℝ) ^ i := by
        have : (0 : ℝ) < (4 : ℝ) ^ i := by positivity
        positivity
      linarith

/-- `1/√i → 0`. -/
theorem one_div_sqrt_tendsto : Tendsto (fun i : ℕ => 1 / Real.sqrt i) atTop (𝓝 0) := by
  have h : Tendsto (fun i : ℕ => Real.sqrt i) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  exact (h.inv_tendsto_atTop).congr (fun i => by simp [one_div])

/-- `log i/√i → 0`. -/
theorem log_div_sqrt_tendsto : Tendsto (fun i : ℕ => Real.log i / Real.sqrt i) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Tendsto (fun i : ℕ => 2 * (Real.log (Real.sqrt i) / Real.sqrt i)) atTop (𝓝 0) := by
    have := (h.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).const_mul 2
    simpa using this
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with i hi
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  rw [Real.log_sqrt hi0]
  ring

/-- `log Kᵢ/√i → 0`. -/
theorem log_Kn_div_sqrt : Tendsto (fun i : ℕ => Real.log (Kn i) / Real.sqrt i) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun i : ℕ => Real.log 512 * (1 / Real.sqrt i)
      + 3 * (Real.log i / Real.sqrt i)) atTop (𝓝 0) := by
    simpa using (one_div_sqrt_tendsto.const_mul (Real.log 512)).add
      (log_div_sqrt_tendsto.const_mul 3)
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop 1] with i hi
    have h1 : (1 : ℝ) ≤ (Kn i : ℝ) := by
      have := Kn_ge i
      have : (216 : ℝ) ≤ (Kn i : ℝ) := by exact_mod_cast this
      linarith
    have := Real.log_nonneg h1
    positivity
  · filter_upwards [eventually_ge_atTop 1] with i hi
    have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    have hsq : (0 : ℝ) < Real.sqrt i := Real.sqrt_pos.mpr (by linarith)
    have hKle : (Kn i : ℝ) ≤ 512 * (i : ℝ) ^ 3 := by
      have h4 : (i + 3 : ℕ) ≤ 4 * i := by omega
      have : ((i + 3 : ℕ) : ℝ) ≤ 4 * (i : ℝ) := by exact_mod_cast h4
      have hb : (0 : ℝ) ≤ ((i : ℝ) + 3) := by linarith
      have hc : ((i : ℝ) + 3) ≤ 4 * (i : ℝ) := by push_cast at this ⊢; linarith
      have : ((i : ℝ) + 3) ^ 3 ≤ (4 * (i : ℝ)) ^ 3 := pow_le_pow_left₀ hb hc 3
      simp only [Kn]
      push_cast
      nlinarith
    have hlogle : Real.log (Kn i) ≤ Real.log 512 + 3 * Real.log i := by
      have h1 : Real.log (Kn i) ≤ Real.log (512 * (i : ℝ) ^ 3) :=
        Real.log_le_log (by
          have : (216 : ℝ) ≤ (Kn i : ℝ) := by exact_mod_cast Kn_ge i
          linarith) hKle
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
      push_cast at h1
      linarith
    have hstep : Real.log (Kn i) / Real.sqrt i
        ≤ (Real.log 512 + 3 * Real.log i) / Real.sqrt i :=
      div_le_div_of_nonneg_right hlogle hsq.le
    have hsplit : (Real.log 512 + 3 * Real.log i) / Real.sqrt i
        = Real.log 512 * (1 / Real.sqrt i) + 3 * (Real.log i / Real.sqrt i) := by
      field_simp
    linarith [hstep, hsplit.le, hsplit.ge]

theorem DD_J (C : ℕ → ℝ) (i : ℕ) : (DD C).J i = JF C i := rfl
theorem DD_eps (C : ℕ → ℝ) (i : ℕ) : (DD C).ε i = epsF i := rfl

/-- Leaf 5: the three KMT terms. -/
theorem terms_tendsto (C : ℕ → ℝ) : Tendsto (fun i => C ((DD C).J i) *
      (Real.sqrt (Real.log (1 / (DD C).ε i)) * Real.sqrt (2 * ((DD C).δ (i - 1) + (DD C).δ i))
        + Real.exp (- ∑ i' ∈ Finset.range (i - 1), (DD C).δ i')
        + Real.exp (- 1 / (8 * ((DD C).J i : ℝ) ^ 2 * (DD C).ε i)))) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun i : ℕ => Real.sqrt (8 * (Real.log (Kn i) / Real.sqrt i))
      + 2 * (1 / Real.sqrt i)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun i : ℕ => Real.sqrt (8 * (Real.log (Kn i) / Real.sqrt i)))
        atTop (𝓝 0) := by
      have := (log_Kn_div_sqrt.const_mul (8 : ℝ)).sqrt
      simpa using this
    simpa using h1.add (one_div_sqrt_tendsto.const_mul 2)
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop 2, JF_C_le C, (JF_tendsto C).eventually_ge_atTop 1]
    with i hi hCle hJ1
  have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (by omega : 1 ≤ i)
  have hipos : (0 : ℝ) < (i : ℝ) := by linarith
  have hsq : (0 : ℝ) < Real.sqrt i := Real.sqrt_pos.mpr hipos
  -- the three terms
  set T1 : ℝ := Real.sqrt (Real.log (1 / (DD C).ε i))
      * Real.sqrt (2 * ((DD C).δ (i - 1) + (DD C).δ i)) with hT1
  set T2 : ℝ := Real.exp (- ∑ i' ∈ Finset.range (i - 1), (DD C).δ i') with hT2
  set T3 : ℝ := Real.exp (- 1 / (8 * ((DD C).J i : ℝ) ^ 2 * (DD C).ε i)) with hT3
  have hT1nn : 0 ≤ T1 := by rw [hT1]; positivity
  have hT2nn : 0 < T2 := Real.exp_pos _
  have hT3nn : 0 < T3 := Real.exp_pos _
  -- bound on T1
  have hlogeps : Real.log (1 / (DD C).ε i) = Real.log (Kn i) := by
    rw [DD_eps, epsF, one_div_one_div]
  have hdeltasum : (DD C).δ (i - 1) + (DD C).δ i ≤ 4 / (i : ℝ) := by
    have h1 := delta_le C (i - 1)
    have h2 := delta_le C i
    have hcast : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by
      have : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
        have : (1 : ℕ) ≤ i := by omega
        push_cast [Nat.cast_sub this]
        ring
      rw [this]; ring
    rw [hcast] at h1
    have h3 : (2 : ℝ) / ((i : ℝ) + 1) ≤ 2 / (i : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hipos (by linarith)
    have : (4 : ℝ) / (i : ℝ) = 2 / (i : ℝ) + 2 / (i : ℝ) := by ring
    linarith
  have hT1le : T1 ≤ Real.sqrt (Real.log (Kn i)) * Real.sqrt (8 / (i : ℝ)) := by
    rw [hT1, hlogeps]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    refine Real.sqrt_le_sqrt ?_
    have h8 : (8 : ℝ) / (i : ℝ) = 2 * (4 / (i : ℝ)) := by ring
    linarith
  -- bound on T2
  have hT2le : T2 ≤ 1 / (i : ℝ) := by
    have hsumge : Real.log ((((i - 1 : ℕ)) : ℝ) + 1)
        ≤ ∑ i' ∈ Finset.range (i - 1), (DD C).δ i' := by
      refine le_trans (harm_lower (i - 1)) ?_
      exact Finset.sum_le_sum (fun k _ => delta_ge C k)
    have hcast : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by
      have h1 : (1 : ℕ) ≤ i := by omega
      have : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
        push_cast [Nat.cast_sub h1]; ring
      rw [this]; ring
    rw [hcast] at hsumge
    rw [hT2]
    calc Real.exp (- ∑ i' ∈ Finset.range (i - 1), (DD C).δ i')
        ≤ Real.exp (- Real.log i) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / (i : ℝ) := by rw [Real.exp_neg, Real.exp_log hipos, one_div]
  -- bound on T3
  have hT3le : T3 ≤ 1 / (i : ℝ) := by
    have hJle : (JF C i : ℝ) ≤ (i : ℝ) := by exact_mod_cast JF_le C i
    have hJ1' : (1 : ℝ) ≤ (JF C i : ℝ) := by exact_mod_cast hJ1
    have hKeq : (8 : ℝ) * ((DD C).J i : ℝ) ^ 2 * (DD C).ε i
        = 8 * (JF C i : ℝ) ^ 2 / (Kn i : ℝ) := by
      rw [DD_J, DD_eps, epsF]
      field_simp
    have hKn : (Kn i : ℝ) = 8 * ((i : ℝ) + 3) ^ 3 := by
      simp only [Kn]; push_cast; ring
    have hpos : (0 : ℝ) < 8 * (JF C i : ℝ) ^ 2 / (Kn i : ℝ) := by
      rw [hKn]; positivity
    have hge : (i : ℝ) ≤ 1 / (8 * (JF C i : ℝ) ^ 2 / (Kn i : ℝ)) := by
      rw [one_div_div, hKn, le_div_iff₀ (by positivity)]
      have hJ2 : (JF C i : ℝ) ^ 2 ≤ (i : ℝ) ^ 2 := by nlinarith
      have hc1 : (i : ℝ) * (8 * (JF C i : ℝ) ^ 2) ≤ 8 * (i : ℝ) ^ 3 := by nlinarith
      have hc2 : (8 : ℝ) * (i : ℝ) ^ 3 ≤ 8 * ((i : ℝ) + 3) ^ 3 := by nlinarith [sq_nonneg (i:ℝ)]
      linarith
    rw [hT3, hKeq]
    calc Real.exp (-1 / (8 * (JF C i : ℝ) ^ 2 / (Kn i : ℝ)))
        ≤ Real.exp (- (i : ℝ)) := by
          refine Real.exp_le_exp.mpr ?_
          have hone : (-1 : ℝ) / (8 * (JF C i : ℝ) ^ 2 / (Kn i : ℝ))
              = - (1 / (8 * (JF C i : ℝ) ^ 2 / (Kn i : ℝ))) := by ring
          rw [hone]
          linarith [hge]
      _ ≤ 1 / (i : ℝ) := by
          rw [Real.exp_neg, ← one_div]
          refine one_div_le_one_div_of_le hipos ?_
          linarith [Real.add_one_le_exp (i : ℝ)]
  -- assemble
  have habs : ‖C ((DD C).J i) * (T1 + T2 + T3)‖ ≤ Real.sqrt (Real.sqrt i) * (T1 + T2 + T3) := by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ T1 + T2 + T3)]
    exact mul_le_mul_of_nonneg_right (by rw [DD_J]; exact hCle) (by linarith)
  refine le_trans habs ?_
  have hstep : Real.sqrt (Real.sqrt i) * (T1 + T2 + T3)
      ≤ Real.sqrt (Real.sqrt i) * (Real.sqrt (Real.log (Kn i)) * Real.sqrt (8 / (i : ℝ))
        + 2 * (1 / (i : ℝ))) := by
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    have : (2 : ℝ) * (1 / (i : ℝ)) = 1 / (i : ℝ) + 1 / (i : ℝ) := by ring
    linarith
  refine le_trans hstep ?_
  have hA : Real.sqrt (Real.sqrt i) * (Real.sqrt (Real.log (Kn i)) * Real.sqrt (8 / (i : ℝ)))
      = Real.sqrt (8 * (Real.log (Kn i) / Real.sqrt i)) := by
    have hlogKn : (0 : ℝ) ≤ Real.log (Kn i) := by
      have : (216 : ℝ) ≤ (Kn i : ℝ) := by exact_mod_cast Kn_ge i
      exact Real.log_nonneg (by linarith)
    rw [← Real.sqrt_mul hlogKn, ← Real.sqrt_mul (Real.sqrt_nonneg _)]
    congr 1
    have hs : Real.sqrt i * Real.sqrt i = (i : ℝ) := Real.mul_self_sqrt hipos.le
    field_simp
    nlinarith [hs, hsq]
  have hB : Real.sqrt (Real.sqrt i) * (2 * (1 / (i : ℝ))) ≤ 2 * (1 / Real.sqrt i) := by
    have h1 : Real.sqrt (Real.sqrt i) ≤ Real.sqrt i :=
      Real.sqrt_le_self_iff.mpr (Or.inr (Real.one_le_sqrt.mpr hi1))
    have h2 : Real.sqrt i * (2 * (1 / (i : ℝ))) = 2 * (1 / Real.sqrt i) := by
      have hs : Real.sqrt i * Real.sqrt i = (i : ℝ) := Real.mul_self_sqrt hipos.le
      field_simp
      nlinarith [hs]
    calc Real.sqrt (Real.sqrt i) * (2 * (1 / (i : ℝ)))
        ≤ Real.sqrt i * (2 * (1 / (i : ℝ))) := by
          refine mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 2 * (1 / Real.sqrt i) := h2
  rw [mul_add, hA]
  linarith

/-- Leaf 6: the L¹ tail. -/
theorem tail_tendsto (C : ℕ → ℝ)
    (hgrow : Tendsto (fun k : ℕ => Real.log (C k) / 4 ^ k) atTop (𝓝 0)) :
    Tendsto (fun i => (∑ i' ∈ Finset.range (i + 2), (DD C).δ i' + 1) / (4 : ℝ) ^ (DD C).J i)
      atTop (𝓝 0) := by
  sorry

end GoodExists

/-- **The sandwich is solvable** when `log C k = o(4^k)`.  Explicit choices (design doc §5,
"`exists_good`, explicit"): `φ(J) := max(1, max_{J'≤J} log C J')`, `Jᵢ := max{J : 4φ(J) + 4J ≤ log i}`
(so `C(Jᵢ) ≤ i^{1/4}` and, by maximality, `log i = o(4^{Jᵢ})`), `εᵢ := 1/(8Jᵢ² log i)`,
`Bᵢ` from `exists_block (y := xᵢ) (δ := 1/(i+1))`, and `xᵢ₊₁ := max(max Bᵢ, 2xᵢ, (xᵢ+1)^{⌈1/εᵢ₊₁⌉},
⌈exp exp(8Jᵢ₊₁² log(i+1))⌉)`.  Then the three terms are `≤ i^{1/4}√(log(8(log i)³))√(8/i)`,
`≤ e·i^{−3/4}`, `≤ i^{−3/4}`, and the tail is `≤ (log(i+2) + 3)/4^{Jᵢ} → 0`. -/
theorem exists_good (C : ℕ → ℝ)
    (hgrow : Tendsto (fun k : ℕ => Real.log (C k) / 4 ^ k) atTop (𝓝 0)) :
    ∃ D : BlockData, D.Good C := by
  refine ⟨GoodExists.DD C, ?_, GoodExists.delta_div C, ?_, ?_, ?_,
    GoodExists.terms_tendsto C, GoodExists.tail_tendsto C hgrow⟩
  · exact GoodExists.JF_tendsto C
  · exact fun i N hN => GoodExists.eps_range C i N hN
  · exact fun i N hi hN => GoodExists.sep_holds C i N hi hN
  · intro i
    show 2 * GoodExists.XF (i + 1) ≤ GoodExists.XF (i + 1 + 1)
    have := GoodExists.XF_succ_ge (i + 1)
    omega

/-- **Existence from the fixed-`k` proposition alone**, assembled from the leaves above. -/
theorem exists_sparse_normal_of_KMT_quant' (C : ℕ → ℝ)
    (hgrow : Tendsto (fun k : ℕ => Real.log (C k) / 4 ^ k) atTop (𝓝 0))
    (hKMT : KMT_quant C) :
    ∃ (S : ℕ → Prop) (_ : DecidablePred S), DivergentRecip S ∧ IsNormal 4 (subsetLambert S 4) := by
  obtain ⟨D, hG⟩ := exists_good C hgrow
  exact ⟨D.set, inferInstance, D.divergentRecip hG.δ_div,
    isNormal_subsetLambert_of_KMT_along D.set D.sched (D.tailOK hG) (D.kmt_along hKMT hG)⟩

/-- **Existence from the fixed-`k` proposition alone** (the block construction; identical to
`exists_sparse_normal_of_KMT_quant'`). -/
theorem exists_sparse_normal_of_KMT_quant (C : ℕ → ℝ)
    (hgrow : Tendsto (fun k : ℕ => Real.log (C k) / 4 ^ k) atTop (𝓝 0))
    (hKMT : KMT_quant C) :
    ∃ (S : ℕ → Prop) (_ : DecidablePred S), DivergentRecip S ∧ IsNormal 4 (subsetLambert S 4) :=
  exists_sparse_normal_of_KMT_quant' C hgrow hKMT

end NormalNumbers.G4Sparse

section Refutation

/-- **The `i = 0` obstruction.**  `Good.ε_range` and `Good.sep` are jointly unsatisfiable at
`i = 0`: `ε_range` forces `x 0` to be huge (`N = 16` already needs `ε > 1/2` when `x 0 < 16`),
while `sep` at `N = x 0 + 1` forces `x 0 ≤ (x 0 + 1)^ε < (x 0 + 1)^{1/2}`, i.e. `x 0 ≤ 1`. -/
theorem sep_eps_incompatible (x0 : ℕ) (ε : ℝ) (hε2 : ε < 1 / 2)
    (hrange : ∀ N : ℕ, x0 < N → 1 / Real.log (Real.log N) < ε)
    (hsep : ∀ N : ℕ, x0 < N → x0 ≤ ⌊(N : ℝ) ^ ε⌋₊) : False := by
  by_cases hsmall : x0 < 16
  · have h16 : ((16 : ℕ) : ℝ) = 16 := by norm_num
    have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hl2' : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
    have hlog16 : Real.log ((16 : ℕ) : ℝ) = 4 * Real.log 2 := by
      rw [h16]
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    have h1 : 1 < Real.log ((16 : ℕ) : ℝ) := by rw [hlog16]; linarith
    have h2 : Real.log ((16 : ℕ) : ℝ) ≤ 7 := by rw [hlog16]; linarith
    have hpos : 0 < Real.log (Real.log ((16 : ℕ) : ℝ)) := Real.log_pos h1
    have hle : Real.log (Real.log ((16 : ℕ) : ℝ)) ≤ 2 := by
      have : Real.log (Real.log ((16 : ℕ) : ℝ)) ≤ Real.log 7 :=
        Real.log_le_log (by linarith) h2
      have hexp2 : (7 : ℝ) ≤ Real.exp 2 := by
        have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
      have h7 : Real.log 7 ≤ 2 := by
        have : Real.log 7 ≤ Real.log (Real.exp 2) :=
          Real.log_le_log (by norm_num) hexp2
        simpa using this
      linarith
    have := hrange 16 (by omega)
    have hge : (1 : ℝ) / 2 ≤ 1 / Real.log (Real.log ((16 : ℕ) : ℝ)) := by
      apply one_div_le_one_div_of_le hpos hle
    linarith
  · push_neg at hsmall
    have hN : x0 < x0 + 1 := by omega
    have := hsep (x0 + 1) hN
    have hcast : ((x0 + 1 : ℕ) : ℝ) = (x0 : ℝ) + 1 := by push_cast; ring
    have hb1 : (1 : ℝ) ≤ (x0 : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (x0 : ℝ) := Nat.cast_nonneg x0
      linarith
    have hfl : ((x0 : ℕ) : ℝ) ≤ ((x0 + 1 : ℕ) : ℝ) ^ ε := by
      refine le_trans ?_ (Nat.floor_le (by positivity))
      exact_mod_cast this
    have hmono : ((x0 + 1 : ℕ) : ℝ) ^ ε ≤ ((x0 + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [hcast]
      exact Real.rpow_le_rpow_of_exponent_le hb1 (le_of_lt hε2)
    have hsq : ((x0 + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt ((x0 : ℝ) + 1) := by
      rw [hcast, Real.sqrt_eq_rpow]
    have hx16 : (16 : ℝ) ≤ (x0 : ℝ) := by exact_mod_cast hsmall
    have hfin : (x0 : ℝ) ≤ Real.sqrt ((x0 : ℝ) + 1) := by
      rw [← hsq]; linarith [hfl, hmono]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (x0 : ℝ) + 1 by positivity),
      Real.sqrt_nonneg ((x0 : ℝ) + 1)]

end Refutation
