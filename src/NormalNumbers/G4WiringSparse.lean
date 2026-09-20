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

/-! #### (b) the density count -/

/-- **(b)** `#{k < K : m k ∣ k} / K → 0`. -/
theorem tendsto_keepCount_div : Filter.Tendsto
    (fun K : ℕ => (((Finset.range K).filter Keep).card : ℝ) / K) Filter.atTop (𝓝 0) := by
  sorry

/-! #### (c) the divergent harmonic sum along `A` -/

/-- **(c)** `∑_{k ∈ A} 1/(k log k) = ∞`. -/
theorem not_summable_keep_harmonic :
    ¬ Summable (fun k : ℕ => if Keep k then 1 / ((k : ℝ) * Real.log k) else 0) := by
  sorry

/-! #### (d) assembly -/

/-- **(d)** the prime set `PSet` has relative density `0`. -/
theorem relDensityZero_PSet : RelDensityZero PSet := by
  sorry

/-- **(d)** the prime set `PSet` has divergent reciprocal sum. -/
theorem divergentRecip_PSet : DivergentRecip PSet := by
  sorry

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
  /-- `[N^{εᵢ}, N]` meets at most blocks `i−1, i`: `N^{εᵢ} ≥ xᵢ₋₁` on block `i`. -/
  sep : ∀ i N, D.x i < N → D.x (i - 1) ≤ ⌊(N : ℝ) ^ D.ε i⌋₊
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
    (hG.J_tendsto.comp D.blockIndex_tendsto).eventually_ge_atTop (h.natAbs + 1)]
    with N hN hN3 hJ
  obtain ⟨hspec1, hspec2⟩ := D.blockIndex_spec N hN
  have hntw : NontrivialWindow (D.J (D.blockIndex N)) h :=
    ⟨h.natAbs + 1, by omega, hJ, nontrivial_site hh⟩
  obtain ⟨hε1, hε2⟩ := hG.ε_range (D.blockIndex N) N hspec1
  have hb := hKMT D.set (D.J (D.blockIndex N)) h hh hntw N hN3 (D.ε (D.blockIndex N)) hε1 hε2
  have hy : D.x (D.blockIndex N - 1) ≤ ⌊(N : ℝ) ^ D.ε (D.blockIndex N)⌋₊ :=
    hG.sep (D.blockIndex N) N hspec1
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

/-- **The sandwich is solvable** when `log C k = o(4^k)`.  Explicit choices (design doc §5,
"`exists_good`, explicit"): `φ(J) := max(1, max_{J'≤J} log C J')`, `Jᵢ := max{J : 4φ(J) + 4J ≤ log i}`
(so `C(Jᵢ) ≤ i^{1/4}` and, by maximality, `log i = o(4^{Jᵢ})`), `εᵢ := 1/(8Jᵢ² log i)`,
`Bᵢ` from `exists_block (y := xᵢ) (δ := 1/(i+1))`, and `xᵢ₊₁ := max(max Bᵢ, 2xᵢ, (xᵢ+1)^{⌈1/εᵢ₊₁⌉},
⌈exp exp(8Jᵢ₊₁² log(i+1))⌉)`.  Then the three terms are `≤ i^{1/4}√(log(8(log i)³))√(8/i)`,
`≤ e·i^{−3/4}`, `≤ i^{−3/4}`, and the tail is `≤ (log(i+2) + 3)/4^{Jᵢ} → 0`. -/
theorem exists_good (C : ℕ → ℝ)
    (hgrow : Tendsto (fun k : ℕ => Real.log (C k) / 4 ^ k) atTop (𝓝 0)) :
    ∃ D : BlockData, D.Good C := by
  sorry

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
