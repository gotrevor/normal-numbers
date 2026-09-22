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
open NormalNumbers.PrimeModel.PhaseFactor NormalNumbers.PrimeModel.DensityMass

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

/-! ## The bottom cutoff diverges -/

/-- `2 log t ≤ t^{3/10}` eventually. -/
private theorem two_log_le_rpow : ∀ᶠ t : ℝ in atTop, 2 * Real.log t ≤ t ^ (3 / 10 : ℝ) := by
  have h := tendsto_log_div_rpow (r := (3 / 10 : ℝ)) (by norm_num)
  filter_upwards [h.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
    eventually_gt_atTop (0 : ℝ)] with t ht htp
  have hp : (0 : ℝ) < t ^ (3 / 10 : ℝ) := Real.rpow_pos_of_pos htp _
  rw [div_lt_iff₀ hp] at ht
  linarith

/-- `ε_N ≤ a_min(N)`: the bottom cutoff of the graded schedule is **above** the classical
`y_N = N^{2/L₂N}`.  Indeed `a_min = (L₃N)^{-1} 2^{-J₁N} ≥ (L₃N)^{-1}(L₂N)^{-log 2}`, and
`(L₂N)^{1-log 2}` beats `2 L₃N = 2 log L₂N` because `1 - log 2 > 3/10`. -/
theorem epsN_le_aMinG : ∀ᶠ N : ℕ in atTop, epsN N ≤ aMinG N := by
  filter_upwards [L2_tendsto.eventually two_log_le_rpow,
    L2_tendsto.eventually_ge_atTop (1 : ℝ),
    L3_tendsto.eventually_ge_atTop (1 : ℝ)] with N hlog hL2 hL3
  set t : ℝ := L2 N with htdef
  have hL3eq : L3 N = Real.log t := rfl
  have ht0 : (0 : ℝ) < t := by linarith
  have hlt0 : (0 : ℝ) < Real.log t := by rw [← hL3eq]; linarith
  -- `2 log t ≤ t^{1 - log 2}`
  have hlog2 : Real.log 2 ≤ 7 / 10 := le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num))
  have hstep : (t : ℝ) ^ (3 / 10 : ℝ) ≤ t ^ ((1 : ℝ) - Real.log 2) :=
    Real.rpow_le_rpow_of_exponent_le hL2 (by linarith)
  have key : 2 * Real.log t ≤ t ^ ((1 : ℝ) - Real.log 2) := le_trans hlog hstep
  -- `t^{1 - log 2} = t * t^{-log 2}`
  have hsplit : t ^ ((1 : ℝ) - Real.log 2) = t * t ^ (-Real.log 2) := by
    rw [sub_eq_add_neg, Real.rpow_add ht0, Real.rpow_one]
  have key' : 2 * Real.log t ≤ t * t ^ (-Real.log 2) := by rw [← hsplit]; exact key
  -- `(1/2)^{J₁N} ≥ (1/2)^{L₃N} = t^{-log 2}`
  have hJ1 : ((J1 N : ℕ) : ℝ) ≤ Real.log t := by
    rw [← hL3eq]; exact Nat.floor_le (by linarith)
  have hpow : t ^ (-Real.log 2) ≤ (1 / 2 : ℝ) ^ (J1 N) := by
    have h1 : ((1 : ℝ) / 2) ^ (Real.log t) ≤ ((1 : ℝ) / 2) ^ ((J1 N : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hJ1
    have h2 : ((1 : ℝ) / 2) ^ (Real.log t) = t ^ (-Real.log 2) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 1/2),
        Real.rpow_def_of_pos ht0, Real.log_div one_ne_zero two_ne_zero, Real.log_one]
      ring_nf
    rw [← h2, ← Real.rpow_natCast ((1:ℝ)/2) (J1 N)]
    exact h1
  -- assemble
  have hA : (0 : ℝ) < t ^ (-Real.log 2) := Real.rpow_pos_of_pos ht0 _
  have hmain : epsN N ≤ (1 / L3 N) * t ^ (-Real.log 2) := by
    rw [epsN, ← htdef, hL3eq, div_le_iff₀ ht0]
    have hrw : (1 / Real.log t * t ^ (-Real.log 2)) * t
        = (t ^ (-Real.log 2) * t) / Real.log t := by field_simp
    rw [hrw, le_div_iff₀ hlt0]
    nlinarith [key']
  refine hmain.trans ?_
  rw [aMinG]
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- The bottom cutoff diverges. -/
theorem yBotG_tendsto : Tendsto yBotG atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ yN_tendsto
  filter_upwards [epsN_le_aMinG, eventually_ge_atTop 1] with N hle hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hN1 hle)

/-! ## The fresh-mass surrogate -/

/-- The square-root fresh mass is uniformly bounded: `r_P(q) ≤ 8 + 12 log 3` for `q ≥ 4`.
(`q ≤ ⌊√q⌋³`, so the Mertens ratio on `(⌊√q⌋, q]` is at most `3`.) -/
theorem recipSumIoc_sqrt_le {q : ℕ} (hq : 4 ≤ q) :
    recipSumIoc P (Nat.sqrt q) q ≤ 8 + 12 * Real.log 3 := by
  classical
  set s : ℕ := Nat.sqrt q with hsdef
  have hs2 : 2 ≤ s := by
    have h1 : Nat.sqrt 4 ≤ Nat.sqrt q := Nat.sqrt_le_sqrt hq
    have h2 : Nat.sqrt 4 = 2 := by norm_num
    omega
  have hsq : s ≤ q := Nat.sqrt_le_self q
  have hset : (Finset.Iic q).filter (fun p => Nat.Prime p ∧ ((s : ℝ)) < (p : ℝ))
      = (Finset.Ioc s q).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc, Nat.cast_lt]
    tauto
  have h1 : recipSumIoc P s q ≤ ∑ p ∈ (Finset.Ioc s q).filter Nat.Prime, (1 : ℝ) / p := by
    rw [recipSumIoc]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by positivity)
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  have key := NormalNumbers.PrimeModel.PrimeDensity.primeRecipSum_le (s : ℝ)
    (by exact_mod_cast hs2) q (by exact_mod_cast hsq)
  rw [hset] at key
  -- the ratio `log q / log s ≤ 3`
  have hcube : q ≤ s ^ 3 := by
    have hlt : q < (s + 1) ^ 2 := Nat.lt_succ_sqrt' q
    nlinarith [hs2, hlt]
  have hsr : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs2
  have hslog : 0 < Real.log s := Real.log_pos (by linarith)
  have hqr : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqlog : 0 < Real.log q := Real.log_pos (by linarith)
  have hcube' : (q : ℝ) ≤ (s : ℝ) ^ 3 := by exact_mod_cast hcube
  have hlogq : Real.log q ≤ 3 * Real.log s := by
    have h2 : Real.log q ≤ Real.log ((s : ℝ) ^ 3) := Real.log_le_log (by linarith) hcube'
    rwa [Real.log_pow] at h2
  have hratio : Real.log q / Real.log s ≤ 3 := by rw [div_le_iff₀ hslog]; linarith
  have hratiopos : 0 < Real.log q / Real.log s := by positivity
  have hlogratio : Real.log (Real.log q / Real.log s) ≤ Real.log 3 :=
    Real.log_le_log hratiopos hratio
  linarith

theorem epsG_nonneg (N : ℕ) : 0 ≤ epsG P N := by
  rw [epsG]
  exact Real.iSup_nonneg (fun q => recipSumIoc_nonneg P _ _)

theorem bddAbove_sqrtFresh (N : ℕ) (h4 : 4 ≤ yBotG N) :
    BddAbove (Set.range fun q : {q : ℕ // yBotG N ≤ q} =>
      recipSumIoc P (Nat.sqrt (q : ℕ)) (q : ℕ)) := by
  refine ⟨8 + 12 * Real.log 3, ?_⟩
  rintro x ⟨q, rfl⟩
  exact recipSumIoc_sqrt_le P (le_trans h4 q.2)

/-- `ε_N` dominates every square-root fresh mass above the bottom cutoff. -/
theorem recipSumIoc_le_epsG (N : ℕ) (h4 : 4 ≤ yBotG N) {q : ℕ} (hq : yBotG N ≤ q) :
    recipSumIoc P (Nat.sqrt q) q ≤ epsG P N := by
  rw [epsG]
  exact le_ciSup (bddAbove_sqrtFresh P N h4) (⟨q, hq⟩ : {q : ℕ // yBotG N ≤ q})

theorem epsG_le {N : ℕ} {ε : ℝ}
    (hε : ∀ q, yBotG N ≤ q → recipSumIoc P (Nat.sqrt q) q ≤ ε) : epsG P N ≤ ε := by
  rw [epsG]
  haveI : Nonempty {q : ℕ // yBotG N ≤ q} := ⟨⟨yBotG N, le_rfl⟩⟩
  exact ciSup_le (fun q => hε (q : ℕ) q.2)

theorem epsG_tendsto (hS : SqrtFreshMassZero P) (hy : Tendsto yBotG atTop atTop) :
    Tendsto (epsG P) atTop (𝓝 0) := by
  refine NormedAddGroup.tendsto_nhds_zero.mpr fun ε hε => ?_
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((tendsto_order.1 hS).2 (ε / 2) (by linarith))
  filter_upwards [hy.eventually_ge_atTop T] with N hN
  have hle : epsG P N ≤ ε / 2 := epsG_le P (fun q hq => (hT q (le_trans hN hq)).le)
  rw [Real.norm_eq_abs, abs_of_nonneg (epsG_nonneg P N)]
  linarith

/-- **`u_N → ∞`.**  Both branches of the `min` diverge: `√(L₃N) → ∞`, and `ε_N → 0` makes
`ε_N^{−1/2} → ∞` (with the degenerate `ε_N = 0` routed to the first branch). -/
theorem uG_tendsto (hS : SqrtFreshMassZero P) (hy : Tendsto yBotG atTop atTop) :
    Tendsto (uG P) atTop atTop := by
  rw [tendsto_atTop]
  intro M
  have hεpos : (0 : ℝ) < 1 / ((M : ℝ) + 1) ^ 2 := by positivity
  filter_upwards [L3_tendsto.eventually_ge_atTop (((M : ℝ) + 1) ^ 2),
    (epsG_tendsto P hS hy).eventually (gt_mem_nhds hεpos)] with N h1' h2
  have h1 : (M : ℝ) + 1 ≤ Real.sqrt (L3 N) := by
    rw [show ((M : ℝ) + 1) = Real.sqrt (((M : ℝ) + 1) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt h1'
  have hkey : ((M : ℝ) + 1) ≤ min (Real.sqrt (L3 N)) (invEpsG P N) := by
    refine le_min h1 ?_
    rw [invEpsG]
    split
    · exact h1
    · rename_i hpos
      have hp : 0 < epsG P N := lt_of_le_of_ne (epsG_nonneg P N) (by
        intro hc; exact hpos (le_of_eq hc.symm))
      rw [le_div_iff₀ (Real.sqrt_pos.mpr hp)]
      have hsq : Real.sqrt (epsG P N) ≤ 1 / ((M : ℝ) + 1) := by
        have hb : epsG P N ≤ (1 / ((M : ℝ) + 1)) ^ 2 := by
          rw [div_pow, one_pow]
          exact h2.le
        calc Real.sqrt (epsG P N) ≤ Real.sqrt ((1 / ((M : ℝ) + 1)) ^ 2) :=
              Real.sqrt_le_sqrt hb
          _ = 1 / ((M : ℝ) + 1) := Real.sqrt_sq (by positivity)
      have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
      calc ((M : ℝ) + 1) * Real.sqrt (epsG P N) ≤ ((M : ℝ) + 1) * (1 / ((M : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hsq hM1.le
        _ = 1 := by field_simp
  rw [uG]
  exact Nat.le_floor (by linarith)

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
theorem sum_uuG_le (N : ℕ) :
    ∑ b : Fin (JG P N), Real.exp (-(uuG P N b : ℝ))
      ≤ 1.6 * Real.exp (-(uG P N : ℝ)) := by
  have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hr0 : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
  have hrval : Real.exp (-1) < 3 / 8 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have hr1 : Real.exp (-1) < 1 := by linarith
  have hsplit : ∑ b : Fin (JG P N), Real.exp (-(uuG P N b : ℝ))
      = Real.exp (-(uG P N : ℝ)) * ∑ b ∈ Finset.range (JG P N), (Real.exp (-1)) ^ b := by
    rw [Finset.mul_sum]
    rw [show (∑ b : Fin (JG P N), Real.exp (-(uuG P N b : ℝ)))
        = ∑ b : Fin (JG P N), Real.exp (-((uG P N + (b : ℕ) : ℕ) : ℝ)) from rfl,
      Fin.sum_univ_eq_sum_range (fun i => Real.exp (-((uG P N + i : ℕ) : ℝ))) (JG P N)]
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
  calc Real.exp (-(uG P N : ℝ)) * ∑ b ∈ Finset.range (JG P N), (Real.exp (-1)) ^ b
      ≤ Real.exp (-(uG P N : ℝ)) * 1.6 :=
        mul_le_mul_of_nonneg_left hgeom (Real.exp_pos _).le
    _ = 1.6 * Real.exp (-(uG P N : ℝ)) := by ring

theorem termE4b_tendsto (hS : SqrtFreshMassZero P) (_hP : DivergentRecip P) :
    Tendsto (termE4b P) atTop (𝓝 0) := by
  have hu : Tendsto (fun N : ℕ => Real.exp (-(uG P N : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => -((uG P N : ℕ) : ℝ)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp
        (tendsto_natCast_atTop_atTop.comp (uG_tendsto P hS yBotG_tendsto))
    exact Real.tendsto_exp_atBot.comp h1
  refine squeeze_zero (fun N => ?_) (fun N => ?_)
    (by simpa using hu.const_mul (0.96 : ℝ))
  · rw [termE4b]
    have : (0 : ℝ) ≤ ∑ b : Fin (JG P N), Real.exp (-(uuG P N b : ℝ)) :=
      Finset.sum_nonneg fun b _ => (Real.exp_pos _).le
    linarith
  · rw [termE4b]
    have := sum_uuG_le P N
    nlinarith [(Real.exp_pos (-(uG P N : ℝ))).le]

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
      (((termE4a_tendsto P hP).add (termE4b_tendsto P hS hP)).add (termE4c_tendsto P hP))).add
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
