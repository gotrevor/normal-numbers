import NormalNumbers.G4WiringCRT

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

/-- A sparse divergent set of primes exists (e.g. `π_S(x) ≍ π(x) / log log x`, whose reciprocal
sum grows like `log log log x`). -/
theorem exists_relDensityZero_divergent :
    ∃ (S : ℕ → Prop) (_ : DecidablePred S), RelDensityZero S ∧ DivergentRecip S := by
  sorry

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

/-- **Existence from the fixed-`k` proposition alone** (no uniformity in `k` beyond a growth bound
on its constant).  Block construction: `S = ⋃ᵢ Bᵢ`, `Bᵢ ⊆ (xᵢ, xᵢ₊₁]` with `∑_{p∈Bᵢ} 1/p = δᵢ`,
`xᵢ₊₁ ≥ xᵢ^{1/εᵢ₊₁}` so that `[x^ε, x]` meets at most two blocks; schedule `J_N = Jᵢ` on
`(xᵢ, xᵢ₊₁]` with `εᵢ = 1/(8 Jᵢ² log i)`.  The three terms give `C(Jᵢ) √δᵢ √log(Jᵢ² log i)`,
`C(Jᵢ) exp(−∑_{i'<i−1} δᵢ')`, `C(Jᵢ)/i`; the L¹ tail (`tail_error_L1`) needs
`∑_{i'≤i} δᵢ' = o(4^{Jᵢ})`.  With `δᵢ = 1/i` the sandwich `log C(Jᵢ) + ω(1) ≤ log i ≤ o(4^{Jᵢ})`
is solvable iff `log C k = o(4^k)`, and `∑ δᵢ = ∞` gives `DivergentRecip`. -/
theorem exists_sparse_normal_of_KMT_quant (C : ℕ → ℝ)
    (hgrow : Tendsto (fun k : ℕ => Real.log (C k) / 4 ^ k) atTop (𝓝 0))
    (hKMT : KMT_quant C) :
    ∃ (S : ℕ → Prop) (_ : DecidablePred S), DivergentRecip S ∧ IsNormal 4 (subsetLambert S 4) := by
  sorry

/-- L¹ tail for a slow schedule.  For `J < j ≤ N`, `∑_{n<N} ω_S(n+j) ≤ ∑_{p∈S, p≤2N} (N/p + 1)
≤ N (S_S(2N) + 1)` (`π(2N) ≤ N`); for `j > N` use `ω_S ≤ log₂`.  Hence
`(1/N) ∑_{n<N} |tailB n − truncTailS J n| ≤ (S_S(2N) + 1)/4^J + (log₂ N + 3)/4^N`,
which lets `J_N` grow as slowly as `log₄ S_S(N)` instead of `log₂ log₂ N`. -/
theorem tail_error_L1 (J N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.range N, |(TWeight.subset S).tailB 4 n - truncTailS S J n|) / N
      ≤ (recipSumLe S (2 * N) + 1) / (4 : ℝ) ^ J + ((Nat.log 2 N : ℝ) + 3) / (4 : ℝ) ^ N := by
  sorry

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

/-- On block `i`, `∑_{y<p≤N, p∈S} 1/p ≤ δᵢ₋₁ + δᵢ` once `y ≥ xᵢ₋₁`. -/
theorem recipSumIoc_le (i N y : ℕ) (hN : D.x i < N) (hN' : N ≤ D.x (i + 1))
    (hy : D.x (i - 1) ≤ y) : recipSumIoc D.set y N ≤ D.δ (i - 1) + D.δ i := by
  sorry

/-- `∑_{p≤y, p∈S} 1/p ≥ ∑_{i'<i−1} δᵢ'` once `y ≥ xᵢ₋₁`. -/
theorem recipSumLe_ge (i y : ℕ) (hy : D.x (i - 1) ≤ y) :
    ∑ i' ∈ Finset.range (i - 1), D.δ i' ≤ recipSumLe D.set y := by
  sorry

/-- `∑_{p≤y, p∈S} 1/p ≤ ∑_{i'≤i+1} δᵢ'` once `y ≤ xᵢ₊₂`. -/
theorem recipSumLe_le (i y : ℕ) (hy : y ≤ D.x (i + 2)) :
    recipSumLe D.set y ≤ ∑ i' ∈ Finset.range (i + 2), D.δ i' := by
  sorry

/-- `blockIndex N → ∞`. -/
theorem blockIndex_tendsto : Tendsto D.blockIndex atTop atTop := by
  sorry

/-- `x (blockIndex N) < N ≤ x (blockIndex N + 1)` for `N > x 0`. -/
theorem blockIndex_spec (N : ℕ) (hN : D.x 0 < N) :
    D.x (D.blockIndex N) < N ∧ N ≤ D.x (D.blockIndex N + 1) := by
  sorry

/-- Divergence of `∑ δᵢ` gives divergence of `∑_{p∈S} 1/p`. -/
theorem divergentRecip (hδ : ¬ Summable D.δ) : DivergentRecip D.set := by
  sorry

/-- The KMT means vanish along the block schedule: `KMT_quant` at scale `N` in block `i` with
`ε = εᵢ`, `J = Jᵢ`, the three bounds above, and `Good.terms`. -/
theorem kmt_along {C : ℕ → ℝ} (hKMT : KMT_quant C) (hG : D.Good C) :
    KMT_along D.set D.sched := by
  sorry

/-- The L¹ tail vanishes along the block schedule: `tail_error_L1` + `recipSumLe_le` +
`Good.tail`. -/
theorem tailOK {C : ℕ → ℝ} (hG : D.Good C) : TailOK D.set D.sched := by
  sorry

end BlockData

/-- Greedy block: a finite set of primes above `y` with reciprocal sum in `[δ, δ + 1/y]`
(take primes `> y` in order until the sum exceeds `δ`; `∑_{p>y} 1/p = ∞` from
`G4Mertens.log_log_le_sum_inv_primesBelow`). -/
theorem exists_block (y : ℕ) (hy : 1 ≤ y) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : Finset ℕ, (∀ p ∈ B, p.Prime ∧ y < p) ∧
      δ ≤ ∑ p ∈ B, (1 : ℝ) / p ∧ ∑ p ∈ B, (1 : ℝ) / p ≤ δ + 1 / y := by
  sorry

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

end NormalNumbers.G4Sparse
