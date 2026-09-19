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
  sorry

/-- The crude schedule works for every `S`: `TailOK S windowJ`. -/
theorem tailOK_windowJ : TailOK S windowJ := by
  sorry

/-! ### Assembly (W1 + W3 directly on prefix means; no W4) -/

/-- The orbit of `c_S(4)` is the subset tail mod one (`coe_tailB` + `lambert_subset`). -/
theorem orbit_eq_fract_tailB_subset (n : ℕ) :
    orbit 4 (subsetLambert S 4) n = Int.fract ((TWeight.subset S).tailB 4 n) := by
  sorry

/-- Prefix Fourier means of the orbit vanish: `TailOK` + `KMT_along`. -/
theorem prefix_fourier_tendsto_zero (Jsched : ℕ → ℕ) (hTail : TailOK S Jsched)
    (hKMT : KMT_along S Jsched) (h : ℤ) (hh : h ≠ 0) :
    Tendsto (prefixMean (fun n => ePhase (h * orbit 4 (subsetLambert S 4) n))) atTop (𝓝 0) := by
  sorry

/-- **Wiring theorem**: normality of `c_S(4)` from the diagonal KMT input along any schedule with a
negligible tail. -/
theorem isNormal_subsetLambert_of_KMT_along (Jsched : ℕ → ℕ) (hTail : TailOK S Jsched)
    (hKMT : KMT_along S Jsched) : IsNormal 4 (subsetLambert S 4) := by
  rw [isNormal_iff_equidistributed_orbit 4 (by norm_num)]
  refine equidistributed_of_weyl _ (orbit_mem_Ico 4 _) ?_
  intro h hh
  have := prefix_fourier_tendsto_zero S Jsched hTail hKMT h hh
  -- `fourierMean u h = prefixMean (fun n => ePhase (h * u n))`
  sorry

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
although the paper's fixed form `exp(−1/(2ε))` silently costs `ε ≤ e^{−4J}/(4J)`).  Everything is
`exp(O(J log J))`; the existence theorem below needs only `log C J = o(4^J)`.
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

/-- L¹ tail for a slow schedule: `(1/N) ∑_{n<N} |tailB n − truncTailS J n|` is at most
`(∑_{j>J} 4^{-j}) (recipSumLe S (2N) + 2)` up to the `n + j > 2N` fringe, i.e. `≪ 4^{-J} S_S(2N)`.
This is what lets `J_N` grow as slowly as `log₄ S_S(N)` instead of `log₂ log₂ N`. -/
theorem tail_error_L1 (J N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.range N, |(TWeight.subset S).tailB 4 n - truncTailS S J n|) / N
      ≤ (recipSumLe S (2 * N) + (Nat.log 2 (2 * N) : ℝ) + 3) / (4 : ℝ) ^ J := by
  sorry

end NormalNumbers.G4Sparse
