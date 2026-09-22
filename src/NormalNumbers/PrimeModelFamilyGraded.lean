import NormalNumbers.PrimeModelWindowSchedule
import NormalNumbers.PrimeModelSqrtFresh
import NormalNumbers.PrimeModelFamilyIterMass

/-!
# Theorem C′: the square-root fresh-mass criterion, on the graded schedule

Leaf **G5c** of the graded-state regrade — lap 7 of `KICKOFF-2026-09-22-multicutoff-lean.md`.
`KMT.window_bound_schedule` (G5b) is Theorem A with every model and sieve hypothesis discharged;
what is left is to *choose the schedule* (Astra §8/§11) and drive its five terms to zero.

## The schedule

    Z-free bottom cutoff   yBot N = ⌊N^{(1/L₃N) 2^{−J₁N}}⌋        (`aMinG`, `yBotG`)
    fresh-mass surrogate   ε_N    = sup_{q ≥ yBot N} r_P(q)        (`epsG`)
    band count             u_N    = ⌊min(√(L₃N), ε_N^{−1/2})⌋      (`uG`)
    top exponent           a_N    = u_N^{−2}                       (`aG`)
    site cutoffs           y_j    = ⌊N^{a_N 2^{−j}}⌋               (`yG`)
    number of sites        J_N    = min(⌊L₃N⌋, ⌊S_P(yBot N)/8⌋)    (`JG`)
    Markov thresholds      T_j    = N^{2^{−j/2}/16}                (`TG`)
    tier weights           u_b    = u_N + b                        (`uuG`)
    level count            L_N    = max 2 ⌊log₂(log yBot N / log 2)⌋ (`LG`)

Two choices differ from a naive reading of the paper and are what make the five terms close:

* the tier weights are **graded**, `u_b = u_N + b`, so `∑_b e^{−u_b} ≤ 1.6 e^{−u_N}` with **no
  `J` factor** — a constant `u_b = u` would leave `J e^{−u}`, and `J ≍ L₃N` is pinned by
  `TailOK`, so that term could not be driven to zero by `ρ_N → 0` alone;
* the bottom cutoff `yBot` is defined from `J₁` and the *minimal* admissible `a` (`1/L₃N`), not
  from `J_N` or `a_N`, which breaks the circularity `J_N ← S_P(y_{J_N−1})`.  Every actual cutoff
  dominates it, so it serves as the uniform `Z` of the root chain and as the uniform lower end
  of the E5 contraction.

With `a_N = u_N^{−2}` the graded support level is
`log R ≤ a_N(540 + 8u_N) log N = (540 + 8u_N)/u_N² · log N = o(log N)`, so `R²/N → 0`: the wall
that killed the constant class count (`log R ≥ 128 k log y_0` with `k = J`) is gone.

## Status

The assembly below is complete: `windowMean_le_terms` is the pointwise bound off
`window_bound_schedule`, and `kmt_along_graded` / `isNormal_subsetLambert_of_sqrtFreshMassZero`
follow from the five term limits by a squeeze.  The five limits and the schedule's pointwise
admissibility are the open leaves, listed in `PENDING_WORK.md`.
-/

set_option linter.unusedSectionVars false

open Finset Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeModel.FamilyGraded

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel.Params NormalNumbers.PrimeModel.KMT
open NormalNumbers.PrimeModel.Family NormalNumbers.PrimeModel.FamilyIter
open NormalNumbers.PrimeModel.SqrtFresh NormalNumbers.PrimeModel.BlockSieve
open NormalNumbers.PrimeModel.PhaseFactor

variable (P : ℕ → Prop) [DecidablePred P]

/-! ## The schedule -/

/-- The minimal admissible top exponent times the last halving: `a ≥ 1/L₃N` always. -/
noncomputable def aMinG (N : ℕ) : ℝ := (1 / L3 N) * (1 / 2) ^ (J1 N)

/-- The bottom cutoff: below every actual site cutoff, and independent of `J_N`. -/
noncomputable def yBotG (N : ℕ) : ℕ := ⌊(N : ℝ) ^ aMinG N⌋₊

/-- The square-root fresh mass above the bottom cutoff (Astra 11.2). -/
noncomputable def epsG (N : ℕ) : ℝ :=
  ⨆ q : {q : ℕ // yBotG N ≤ q}, recipSumIoc P (Nat.sqrt (q : ℕ)) (q : ℕ)

/-- `ε_N^{−1/2}`, with the degenerate value `ε_N = 0` sent to the other branch of the `min`. -/
noncomputable def invEpsG (N : ℕ) : ℝ :=
  if epsG P N ≤ 0 then Real.sqrt (L3 N) else 1 / Real.sqrt (epsG P N)

/-- The band parameter `u_N → ∞`. -/
noncomputable def uG (N : ℕ) : ℕ := ⌊min (Real.sqrt (L3 N)) (invEpsG P N)⌋₊

/-- The top cutoff exponent `a_N = u_N^{−2}`. -/
noncomputable def aG (N : ℕ) : ℝ := 1 / ((uG P N : ℝ)) ^ 2

/-- The site cutoffs `y_j = ⌊N^{a_N 2^{−j}}⌋`. -/
noncomputable def yG (N j : ℕ) : ℕ := ⌊(N : ℝ) ^ (aG P N * (1 / 2) ^ j)⌋₊

/-- The number of sites, `J_N = min(⌊L₃N⌋, ⌊S_P(yBot)/8⌋)`. -/
noncomputable def JG (N : ℕ) : ℕ := min (J1 N) ⌊recipSumLe P (yBotG N) / 8⌋₊

/-- The Markov thresholds `T_j = N^{2^{−j/2}/16}`. -/
noncomputable def TG (N j : ℕ) : ℝ := (N : ℝ) ^ ((1 / 16) * Real.sqrt ((1 / 2) ^ j))

/-- The level count of the dyadic block family. -/
noncomputable def LG (N : ℕ) : ℕ :=
  max 2 ⌊Real.log (Real.log (yBotG N) / Real.log 2) / Real.log 2⌋₊

/-- The band floors: `lo b = y_{b+1}`, and `2J` on the bottom band. -/
noncomputable def loG (N : ℕ) : Fin (JG P N) → ℕ :=
  fun b => if (b : ℕ) + 1 < JG P N then yG P N ((b : ℕ) + 1) else 2 * JG P N

/-- The graded tier weights `u_b = u_N + b`: this is what removes the factor `J` from E4b. -/
noncomputable def uuG (N : ℕ) : Fin (JG P N) → ℕ := fun b => uG P N + (b : ℕ)

/-! ## The five terms -/

/-- E1, the per-site transfer error. -/
noncomputable def termE1 (h : ℤ) (N : ℕ) : ℝ :=
  ∑ j : Fin (JG P N), siteBudget h j.val
    * (2 * recipSumIoc P (yG P N j) N + ((JG P N : ℕ) : ℝ) / N)

/-- E4a, the discarded radical mass, at the sharp per-site exponent. -/
noncomputable def termE4a (N : ℕ) : ℝ :=
  2 * ∑ j : Fin (JG P N),
    Real.exp 20 / (TG N j) ^ (1 / (2 * Real.log (yG P N j)))

/-- E4b, the sieve defect. -/
noncomputable def termE4b (N : ℕ) : ℝ :=
  2 * (0.3 * ∑ b : Fin (JG P N), Real.exp (-(uuG P N b : ℝ)))

/-- E4c, the CRT remainder. -/
noncomputable def termE4c (N : ℕ) : ℝ :=
  2 * ((primorial (2 * JG P N) : ℕ) : ℝ) * (∏ j : Fin (JG P N), (Nat.floor (TG N j) : ℝ))
    * (gradedLevel Finset.univ (fun b : Fin (JG P N) => (b : ℕ) + 1) (uuG P N)
        (fun b : Fin (JG P N) => ((yG P N b : ℕ) : ℝ))) ^ 2 / N

/-- E5, the phase contraction, at the uniform bottom cutoff. -/
noncomputable def termE5 (N : ℕ) : ℝ :=
  Real.exp (2 * JG P N)
    * Real.exp (- ∑ p ∈ (midPrimes P (2 * JG P N) (yG P N 0)).filter
        (fun p => p ≤ yBotG N), (1 : ℝ) / (p : ℝ))

/-! ## Admissibility of the schedule (open leaf) -/

/-- **Open leaf G5c-1.**  The schedule is pointwise admissible for `window_bound_schedule`.
Every clause is an inequality between the explicit schedule functions above; none involves the
model or the sieve.  See `PENDING_WORK.md` for the sub-leaves. -/
theorem schedule_admissible : ∀ᶠ N : ℕ in atTop,
    1 ≤ JG P N
    ∧ (∀ i j : Fin (JG P N), i ≤ j → yG P N j ≤ yG P N i)
    ∧ (∀ j : Fin (JG P N), 2 * JG P N ≤ yG P N j)
    ∧ (∀ j : Fin (JG P N), 2 ≤ Real.log (yG P N j))
    ∧ (∀ (b : Fin (JG P N)) (hb : (b : ℕ) + 1 < JG P N),
        loG P N b = yG P N ((b : ℕ) + 1))
    ∧ (∀ b : Fin (JG P N), (b : ℕ) + 1 = JG P N → loG P N b = 2 * JG P N)
    ∧ (∀ b : Fin (JG P N),
        cut (fun b : Fin (JG P N) => ((yG P N b : ℕ) : ℝ)) b (LG N) ≤ (loG P N b : ℝ))
    ∧ (∀ b : Fin (JG P N),
        2 ≤ cut (fun b : Fin (JG P N) => ((yG P N b : ℕ) : ℝ)) b (LG N))
    ∧ (∑ b : Fin (JG P N), Real.exp (-(uuG P N b : ℝ)) ≤ 1)
    ∧ (∀ j : Fin (JG P N), 1 ≤ TG N j)
    ∧ (∀ j : Fin (JG P N), yBotG N ≤ yG P N j) := by
  sorry

/-! ## The pointwise window bound on the schedule -/

/-- The graded window bound, with the `j₀`-dependence of E5 removed by monotonicity: every site
cutoff dominates `yBot N`, so the contraction collected below `y_{j₀}` is at least the one
collected below `yBot N`. -/
theorem windowMean_le_terms (h : ℤ) : ∀ᶠ N : ℕ in atTop,
    (∀ hh : NontrivialWindow (JG P N) h, 0 < N →
      ‖windowMeanS P (JG P N) h N‖
        ≤ termE1 P h N + (termE4a P N + termE4b P N + termE4c P N) + termE5 P N) := by
  filter_upwards [schedule_admissible P] with N hadm
  obtain ⟨hk, hmono, hmy, hylog, hloin, hlotop, hcutlo, hcut2, hT1, hT, hybot⟩ := hadm
  intro hntw hN
  obtain ⟨j₀, hbound⟩ := window_bound_schedule P (k := JG P N) (L := LG N) hk
    (fun j => yG P N j) hmono hmy hylog (loG P N) hloin hlotop hcutlo hcut2
    (uuG P N) hT1 hT h hntw N hN

  rw [termE1, termE4a, termE4b, termE4c, termE5]
  refine hbound.trans (add_le_add (le_refl _) ?_)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg ?_)) (by positivity)
  have hsub : ((midPrimes P (2 * JG P N) (yG P N 0)).filter (fun p => p ≤ yBotG N))
      ⊆ ((midPrimes P (2 * JG P N) (yG P N 0)).filter
        (fun p => p ≤ yG P N (j₀ : ℕ))) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, le_trans hp.2 (hybot j₀)⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)

/-! ## The five limits (open leaves) -/

/-- **Open leaf G5c-2 (E1).**  `∑_j a_j (2 S_P(y_j, N) + J/N) → 0`: the root chain
(`SqrtFresh.recipSumIoc_le_rootChain`) gives `S_P(y_j, N) ≤ ε_N (j + 2 log₂ u_N + 1)`, and
`u_N ≤ ε_N^{−1/2}` makes `ε_N log u_N → 0`. -/
theorem termE1_tendsto (hS : SqrtFreshMassZero P) (hP : DivergentRecip P) (h : ℤ) :
    Tendsto (termE1 P h) atTop (𝓝 0) := by
  sorry

/-- **Open leaf G5c-3 (E4a).**  `log T_j / (2 log y_j) = 2^{j/2} u_N²/32`, so the sum is
`2 e^{20} ∑_j exp(−2^{j/2} u_N²/32) → 0`.  This is the term the ungraded Markov range made
diverge like `J e^{20}`. -/
theorem termE4a_tendsto (hP : DivergentRecip P) : Tendsto (termE4a P) atTop (𝓝 0) := by
  sorry

/-- **Open leaf G5c-4 (E4b).**  `∑_b e^{−(u_N + b)} ≤ 1.6 e^{−u_N} → 0` — no `J` factor,
because the tier weights are graded. -/
theorem termE4b_tendsto (hP : DivergentRecip P) : Tendsto (termE4b P) atTop (𝓝 0) := by
  sorry

/-- **Open leaf G5c-5 (E4c).**  `log R ≤ (540 + 8u_N)/u_N² · log N`, so
`R² ≤ N^{2(540+8u_N)/u_N²} = N^{o(1)}`; with `(2J)# ≤ 4^{2J} = N^{o(1)}` and
`∏_j ⌊T_j⌋ ≤ N^{0.22}` the whole term is `N^{−1+o(1)} → 0`. -/
theorem termE4c_tendsto (hP : DivergentRecip P) : Tendsto (termE4c P) atTop (𝓝 0) := by
  sorry

/-- **Open leaf G5c-6 (E5).**  `J_N ≤ S_P(yBot N)/8` and `S_P(2J) = O(log log J)` give
`∑_{p ∈ P ∩ (2J, yBot]} 1/p ≥ 8J − O(log log J) ≥ 2J + 5J`, so the term is `≤ e^{−5J} → 0`. -/
theorem termE5_tendsto (hP : DivergentRecip P) : Tendsto (termE5 P) atTop (𝓝 0) := by
  sorry

/-! ## Theorem C′ -/

/-- **Open leaf G5c-7.**  The tail along the graded schedule: the `min` in `JG` is the same
device as `JI`, so `tail_fresh`'s two-branch argument applies with `yBotG` in place of `yI`. -/
theorem tailOK_graded (hS : SqrtFreshMassZero P) (hP : DivergentRecip P) :
    TailOK P (JG P) := by
  sorry

theorem JG_tendsto (hS : SqrtFreshMassZero P) (hP : DivergentRecip P) :
    Tendsto (JG P) atTop atTop := by
  sorry

theorem kmt_along_graded (hS : SqrtFreshMassZero P) (hP : DivergentRecip P) :
    KMT_along P (JG P) := by
  intro h hh
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  have hsum : Tendsto (fun N : ℕ =>
      termE1 P h N + (termE4a P N + termE4b P N + termE4c P N) + termE5 P N)
      atTop (𝓝 0) := by
    have := ((termE1_tendsto P hS hP h).add
      (((termE4a_tendsto P hP).add (termE4b_tendsto P hP)).add (termE4c_tendsto P hP))).add
      (termE5_tendsto P hP)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hsum
  filter_upwards [windowMean_le_terms P h, eventually_gt_atTop 0,
    (JG_tendsto P hS hP).eventually_ge_atTop (h.natAbs + 1)] with N hb hN hJ
  exact hb ⟨h.natAbs + 1, by omega, hJ, nontrivial_site hh⟩ hN

/-- **Theorem C′** (Astra §11 / Fable §9): vanishing square-root fresh reciprocal mass plus a
divergent reciprocal sum give a normal base-4 Lambert constant. -/
theorem isNormal_subsetLambert_of_sqrtFreshMassZero
    (hS : SqrtFreshMassZero P) (hP : DivergentRecip P) : IsNormal 4 (subsetLambert P 4) :=
  isNormal_subsetLambert_of_KMT_along P (JG P) (tailOK_graded P hS hP)
    (kmt_along_graded P hS hP)

end NormalNumbers.PrimeModel.FamilyGraded
