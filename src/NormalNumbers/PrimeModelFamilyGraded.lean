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

/-- The number of sites, `J_N = min(⌊L₃N⌋, ⌊S_N/8⌋)` with `S_N = S_P(N)` the **full** mass up
to `N` (Astra §8: `S_N = S_P(0,N)`).  Tying `J` to the full mass — rather than to the mass below
the bottom cutoff — is what the bounded contracting site index (`exists_site_re_nonpos_le`)
buys: leg E5 collects its contraction at the *near-top* cutoff `y_{c(h)}`, and the mass above
that cutoff is `O(ε_N log u_N) = o(1)` by a **short** root chain. -/
noncomputable def JG (N : ℕ) : ℕ := min (J1 N) ⌊recipSumLe P N / 8⌋₊

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

/-! ## Schedule facts used by the term estimates -/

theorem JG_le_J1 (N : ℕ) : JG P N ≤ J1 N := min_le_left _ _

theorem invEpsG_nonneg (N : ℕ) : 0 ≤ invEpsG P N := by
  rw [invEpsG]; split
  · exact Real.sqrt_nonneg _
  · positivity

theorem uG_sq_le_L3 {N : ℕ} (hL3 : 0 ≤ L3 N) : ((uG P N : ℕ) : ℝ) ^ 2 ≤ L3 N := by
  have h1 : ((uG P N : ℕ) : ℝ) ≤ Real.sqrt (L3 N) := by
    rw [uG]
    exact le_trans (Nat.floor_le (le_min (Real.sqrt_nonneg _) (invEpsG_nonneg P N)))
      (min_le_left _ _)
  have h0 : (0 : ℝ) ≤ ((uG P N : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith [Real.sq_sqrt hL3, Real.sqrt_nonneg (L3 N)]

theorem aG_pos {N : ℕ} (hu : 1 ≤ uG P N) : 0 < aG P N := by
  have : (1 : ℝ) ≤ ((uG P N : ℕ) : ℝ) := by exact_mod_cast hu
  rw [aG]; positivity

theorem aG_ge_invL3 {N : ℕ} (hL3 : 0 < L3 N) (hu : 1 ≤ uG P N) : 1 / L3 N ≤ aG P N := by
  have hu1 : (1 : ℝ) ≤ ((uG P N : ℕ) : ℝ) := by exact_mod_cast hu
  rw [aG]
  exact one_div_le_one_div_of_le (by nlinarith) (uG_sq_le_L3 P hL3.le)

/-- Every site cutoff dominates the bottom cutoff — the uniform lower end of the schedule. -/
theorem yBotG_le_yG_nat (hS : SqrtFreshMassZero P) : ∀ᶠ N : ℕ in atTop,
    ∀ j : ℕ, j ≤ J1 N → yBotG N ≤ yG P N j := by
  filter_upwards [L3_tendsto.eventually_gt_atTop (0 : ℝ),
    (uG_tendsto P hS yBotG_tendsto).eventually_ge_atTop 1,
    eventually_ge_atTop 1] with N hL3 hu hN j hj
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hexp : aMinG N ≤ aG P N * (1 / 2) ^ (j : ℕ) := by
    rw [aMinG]
    have h1 : (1 / L3 N) * (1 / 2 : ℝ) ^ (J1 N) ≤ aG P N * (1 / 2 : ℝ) ^ (J1 N) :=
      mul_le_mul_of_nonneg_right (aG_ge_invL3 P hL3 hu) (by positivity)
    have h2 : (aG P N) * (1 / 2 : ℝ) ^ (J1 N) ≤ aG P N * (1 / 2 : ℝ) ^ (j : ℕ) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj) (aG_pos P hu).le
    linarith
  exact Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hN1 hexp)

theorem yBotG_le_yG (hS : SqrtFreshMassZero P) : ∀ᶠ N : ℕ in atTop,
    ∀ j : Fin (JG P N), yBotG N ≤ yG P N (j : ℕ) := by
  filter_upwards [yBotG_le_yG_nat P hS] with N h j
  exact h (j : ℕ) (le_trans (le_of_lt j.2) (JG_le_J1 P N))

/-- `ε_N u_N² ≤ 1`: this is what the `ε_N^{−1/2}` branch of `u_N` is for. -/
theorem epsG_mul_uG_sq_le (N : ℕ) : epsG P N * ((uG P N : ℕ) : ℝ) ^ 2 ≤ 1 := by
  rcases eq_or_lt_of_le (epsG_nonneg P N) with heq | hpos
  · rw [← heq]; simp
  · have hu : ((uG P N : ℕ) : ℝ) ≤ invEpsG P N := by
      rw [uG]
      exact le_trans (Nat.floor_le (le_min (Real.sqrt_nonneg _) (invEpsG_nonneg P N)))
        (min_le_right _ _)
    rw [invEpsG, if_neg (not_le.mpr hpos)] at hu
    have hsp : 0 < Real.sqrt (epsG P N) := Real.sqrt_pos.mpr hpos
    have hsq : Real.sqrt (epsG P N) * Real.sqrt (epsG P N) = epsG P N :=
      Real.mul_self_sqrt (le_of_lt hpos)
    have h1 : ((uG P N : ℕ) : ℝ) * Real.sqrt (epsG P N) ≤ 1 := by
      rw [le_div_iff₀ hsp] at hu
      linarith
    have h0 : (0 : ℝ) ≤ ((uG P N : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : (((uG P N : ℕ) : ℝ) * Real.sqrt (epsG P N)) ^ 2 ≤ 1 :=
      pow_le_one₀ (by positivity) h1
    calc epsG P N * ((uG P N : ℕ) : ℝ) ^ 2
        = (((uG P N : ℕ) : ℝ) * Real.sqrt (epsG P N)) ^ 2 := by
          rw [mul_pow, pow_two (Real.sqrt (epsG P N)), hsq]; ring
      _ ≤ 1 := h2

/-! ### Two elementary numeric lemmas -/

private theorem one_add_div_four_sq_le (j : ℕ) : (1 + (j : ℝ) / 4) ^ 2 ≤ 2 ^ j := by
  induction j with
  | zero => norm_num
  | succ n ih =>
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    push_cast
    rw [show ((2 : ℝ)) ^ (n + 1) = 2 * 2 ^ n from by ring]
    nlinarith [ih, hn, sq_nonneg ((n : ℝ) / 4)]

private theorem one_add_div_four_le_sqrt (j : ℕ) : 1 + (j : ℝ) / 4 ≤ Real.sqrt (2 ^ j) := by
  have h := Real.sqrt_le_sqrt (one_add_div_four_sq_le j)
  rwa [Real.sqrt_sq (by positivity)] at h

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

/-- The index of the contracting site, clipped to the site range: `c(h) = log₄|h|`, and
`min` with `J − 1` because the schedule only has `J` sites.  `exists_site_re_nonpos_le` says the
site that Theorem A's leg E5 contracts at has index `≤ c(h)`, hence `≤ cIdx`, hence its cutoff
**dominates** `y_{cIdx}`. -/
noncomputable def cIdx (h : ℤ) (N : ℕ) : ℕ := min (Nat.log 4 h.natAbs) (JG P N - 1)

/-- E5, the phase contraction, at the **near-top** cutoff `y_{c(h)}`. -/
noncomputable def termE5 (h : ℤ) (N : ℕ) : ℝ :=
  Real.exp (2 * JG P N)
    * Real.exp (- ∑ p ∈ (midPrimes P (2 * JG P N) (yG P N 0)).filter
        (fun p => p ≤ yG P N (cIdx P h N)), (1 : ℝ) / (p : ℝ))

/-- The site cutoffs decrease with the index. -/
theorem yG_antitone {N : ℕ} (hN : 1 ≤ N) {i j : ℕ} (hij : i ≤ j) :
    yG P N j ≤ yG P N i := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  refine Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hN1 ?_)
  have hpow : ((1 : ℝ) / 2) ^ j ≤ ((1 : ℝ) / 2) ^ i :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
  have ha : (0 : ℝ) ≤ aG P N := by rw [aG]; positivity
  exact mul_le_mul_of_nonneg_left hpow ha

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
        ≤ termE1 P h N + (termE4a P N + termE4b P N + termE4c P N) + termE5 P h N) := by
  filter_upwards [schedule_admissible P, eventually_ge_atTop 1] with N hadm hN1
  obtain ⟨hk, hmono, hmy, hylog, hloin, hlotop, hcutlo, hcut2, hT1, hT, hybot⟩ := hadm
  intro hntw hN
  obtain ⟨j₀, hjb, hbound⟩ := window_bound_schedule P (k := JG P N) (L := LG N) hk
    (fun j => yG P N j) hmono hmy hylog (loG P N) hloin hlotop hcutlo hcut2
    (uuG P N) hT1 hT h hntw N hN

  rw [termE1, termE4a, termE4b, termE4c, termE5]
  refine hbound.trans (add_le_add (le_refl _) ?_)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg ?_)) (by positivity)
  have hjc : (j₀ : ℕ) ≤ cIdx P h N := by
    rw [cIdx]
    exact le_min hjb (by omega)
  have hyc : yG P N (cIdx P h N) ≤ yG P N (j₀ : ℕ) := yG_antitone P hN1 hjc
  have hsub : ((midPrimes P (2 * JG P N) (yG P N 0)).filter (fun p => p ≤ yG P N (cIdx P h N)))
      ⊆ ((midPrimes P (2 * JG P N) (yG P N 0)).filter
        (fun p => p ≤ yG P N (j₀ : ℕ))) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, le_trans hp.2 hyc⟩
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
theorem termE4a_le (hS : SqrtFreshMassZero P) : ∀ᶠ N : ℕ in atTop,
    termE4a P N ≤ 4 * Real.exp 20 * Real.exp (-(((uG P N : ℕ) : ℝ) ^ 2 / 32)) := by
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    have h1 : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
    have h2 := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at h2
  filter_upwards [yBotG_le_yG P hS, yBotG_tendsto.eventually_ge_atTop 3,
    (uG_tendsto P hS yBotG_tendsto).eventually_ge_atTop 10,
    L3_tendsto.eventually_gt_atTop (0 : ℝ), eventually_ge_atTop 3] with N hyb hyb3 hu hL3 hN3
  have hNr : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hlogN : (1 : ℝ) ≤ Real.log N := le_trans hlog3 (Real.log_le_log (by norm_num) hNr)
  have hu1 : 1 ≤ uG P N := by omega
  have hu10' : (10 : ℝ) ≤ ((uG P N : ℕ) : ℝ) := by exact_mod_cast hu
  set u : ℝ := ((uG P N : ℕ) : ℝ) with hudef
  have hu10 : (10 : ℝ) ≤ u := hu10'
  have hapos : 0 < aG P N := aG_pos P hu1
  have haGval : aG P N = 1 / u ^ 2 := rfl
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
      Real.exp 20 / (TG N (j : ℕ)) ^ (1 / (2 * Real.log (yG P N (j : ℕ))))
        ≤ Real.exp 20 * Real.exp (-(u ^ 2 / 32)) * r ^ (j : ℕ) := by
    intro j
    have hy3 : 3 ≤ yG P N (j : ℕ) := le_trans hyb3 (hyb j)
    have hy3r : (3 : ℝ) ≤ ((yG P N (j : ℕ) : ℕ) : ℝ) := by exact_mod_cast hy3
    have hylog : (1 : ℝ) ≤ Real.log (yG P N (j : ℕ)) :=
      le_trans hlog3 (Real.log_le_log (by norm_num) hy3r)
    -- upper bound on `log y_j`
    set A : ℝ := aG P N * (1 / 2) ^ (j : ℕ) * Real.log N with hAdef
    have hyub : Real.log (yG P N (j : ℕ)) ≤ A := by
      have hfl : ((yG P N (j : ℕ) : ℕ) : ℝ) ≤ (N : ℝ) ^ (aG P N * (1 / 2) ^ (j : ℕ)) :=
        Nat.floor_le (Real.rpow_nonneg hN0.le _)
      have := Real.log_le_log (by linarith) hfl
      rwa [Real.log_rpow hN0, ← hAdef] at this
    have hA1 : (1 : ℝ) ≤ A := le_trans hylog hyub
    -- the Markov threshold is ≥ 1 and the exponent comparison
    have hTexp : (0 : ℝ) ≤ (1 / 16) * Real.sqrt ((1 / 2) ^ (j : ℕ)) := by positivity
    have hT1 : (1 : ℝ) ≤ TG N (j : ℕ) := Real.one_le_rpow hN1 hTexp
    have hexpo : 1 / (2 * A) ≤ 1 / (2 * Real.log (yG P N (j : ℕ))) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    have hTmono : (TG N (j : ℕ)) ^ (1 / (2 * A))
        ≤ (TG N (j : ℕ)) ^ (1 / (2 * Real.log (yG P N (j : ℕ)))) :=
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
        ≤ (TG N (j : ℕ)) ^ (1 / (2 * Real.log (yG P N (j : ℕ)))) := by
      refine le_trans ?_ hTmono
      rw [hval]
      refine Real.exp_le_exp.mpr ?_
      have := one_add_div_four_le_sqrt (j : ℕ)
      nlinarith [sq_nonneg u]
    have hpos : (0 : ℝ) < Real.exp (u ^ 2 * (1 + (j : ℕ) / 4) / 32) := Real.exp_pos _
    have hstep : Real.exp 20 / (TG N (j : ℕ)) ^ (1 / (2 * Real.log (yG P N (j : ℕ))))
        ≤ Real.exp 20 / Real.exp (u ^ 2 * (1 + (j : ℕ) / 4) / 32) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le hpos hlow
    refine hstep.trans (le_of_eq ?_)
    rw [hrdef, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_sub]
    ring_nf
    rw [Real.exp_add]
  -- sum up
  rw [termE4a]
  have hsum : ∑ j : Fin (JG P N),
      Real.exp 20 / (TG N (j : ℕ)) ^ (1 / (2 * Real.log (yG P N (j : ℕ))))
      ≤ ∑ j : Fin (JG P N), (Real.exp 20 * Real.exp (-(u ^ 2 / 32))) * r ^ (j : ℕ) :=
    Finset.sum_le_sum fun j _ => by simpa [mul_assoc] using hterm j
  have hgeo : ∑ j : Fin (JG P N), (Real.exp 20 * Real.exp (-(u ^ 2 / 32))) * r ^ (j : ℕ)
      ≤ (Real.exp 20 * Real.exp (-(u ^ 2 / 32))) * 2 := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Fin.sum_univ_eq_sum_range (fun i => r ^ i) (JG P N)]
    exact geom_sum_le_two hr0 hrhalf _
  nlinarith [hsum, hgeo, Real.exp_pos (20 : ℝ), Real.exp_pos (-(u ^ 2 / 32))]

theorem termE4a_tendsto (hS : SqrtFreshMassZero P) (_hP : DivergentRecip P) :
    Tendsto (termE4a P) atTop (𝓝 0) := by
  have hu : Tendsto (fun N : ℕ => Real.exp (-(((uG P N : ℕ) : ℝ) ^ 2 / 32))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun N : ℕ => ((uG P N : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (uG_tendsto P hS yBotG_tendsto)
    have hsq : Tendsto (fun N : ℕ => ((uG P N : ℕ) : ℝ) ^ 2) atTop atTop :=
      tendsto_atTop_mono' atTop
        (by filter_upwards [h0.eventually_ge_atTop 1] with N hN; nlinarith) h0
    have h1 : Tendsto (fun N : ℕ => -(((uG P N : ℕ) : ℝ) ^ 2 / 32)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (hsq.atTop_div_const (by norm_num))
    exact Real.tendsto_exp_atBot.comp h1
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) (termE4a_le P hS)
    (by simpa using hu.const_mul (4 * Real.exp 20))
  rw [termE4a]
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => ?_)
  have hT : (0 : ℝ) ≤ (TG N (j : ℕ)) ^ (1 / (2 * Real.log (yG P N (j : ℕ)))) := by
    rw [TG]; positivity
  exact div_nonneg (Real.exp_pos _).le hT

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
theorem termE5_tendsto (hS : SqrtFreshMassZero P) (hP : DivergentRecip P) (h : ℤ) :
    Tendsto (termE5 P h) atTop (𝓝 0) := by
  sorry

/-! ## Theorem C′ -/

/-- **Open leaf G5c-7.**  The tail along the graded schedule: the `min` in `JG` is the same
device as `JI`, so `tail_fresh`'s two-branch argument applies with `yBotG` in place of `yI`. -/
theorem JG_le_L3 : ∀ᶠ N : ℕ in atTop, (JG P N : ℝ) ≤ L3 N := by
  filter_upwards [L3_tendsto.eventually_ge_atTop 0] with N hL
  have h2 : ((J1 N : ℕ) : ℝ) ≤ L3 N := Nat.floor_le (by linarith)
  have h3 : (JG P N : ℝ) ≤ ((J1 N : ℕ) : ℝ) := by exact_mod_cast JG_le_J1 P N
  linarith

theorem JG_le_mass (N : ℕ) : 8 * (JG P N : ℝ) ≤ recipSumLe P N := by
  have hS := recipSumLe_nonneg P N
  have h1 : JG P N ≤ ⌊recipSumLe P N / 8⌋₊ := min_le_right _ _
  have h2 : ((⌊recipSumLe P N / 8⌋₊ : ℕ) : ℝ) ≤ recipSumLe P N / 8 :=
    Nat.floor_le (by positivity)
  have h3 : (JG P N : ℝ) ≤ ((⌊recipSumLe P N / 8⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
  linarith

/-- In the first branch of the `min`, `J_N ≥ L₃N − 1`. -/
theorem JG_lower {N : ℕ} (hcase : J1 N ≤ ⌊recipSumLe P N / 8⌋₊) (hL : 0 ≤ L3 N) :
    L3 N - 1 ≤ (JG P N : ℝ) := by
  have h : JG P N = J1 N := min_eq_left hcase
  rw [h]
  have h2 : L3 N < ((J1 N : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one (L3 N)
  linarith

/-- The bottom cutoff is below `N`: `a_min ≤ 1`. -/
theorem yBotG_le_self : ∀ᶠ N : ℕ in atTop, yBotG N ≤ N := by
  filter_upwards [L3_tendsto.eventually_ge_atTop (1 : ℝ), eventually_ge_atTop 1]
    with N hL3 hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have ha1 : aMinG N ≤ 1 := by
    rw [aMinG]
    have h1 : (1 / L3 N) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have h2 : ((1 : ℝ) / 2) ^ (J1 N) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 1/2 by norm_num) (J1 N)]
  have : ((N : ℝ)) ^ aMinG N ≤ (N : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 ha1
  rw [Real.rpow_one] at this
  have hfl : ⌊((N : ℝ)) ^ aMinG N⌋₊ ≤ ⌊(N : ℝ)⌋₊ := Nat.floor_le_floor this
  simpa [yBotG] using hfl

theorem JG_tendsto (hP : DivergentRecip P) : Tendsto (JG P) atTop atTop := by
  have hA : Tendsto J1 atTop atTop := J1_tendsto
  have hB : Tendsto (fun N : ℕ => ⌊recipSumLe P N / 8⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp
      ((recipSumLe_tendsto_atTop P hP).atTop_div_const (by norm_num))
  refine tendsto_atTop.mpr fun b => ?_
  filter_upwards [hA.eventually_ge_atTop b, hB.eventually_ge_atTop b] with N h1 h2
  exact le_min h1 h2

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
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500, JG_le_L3 P,
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

/-- **PROVED** (was the residual tail crux).  The mass of `P` on `(N, 2N]` is eventually `≤ 1`.
This is a **one-step** root chain: `(N, 2N] ⊆ (⌊√(2N)⌋, 2N]`, so the mass is at most
`r_P(2N) ≤ ε_N → 0`.  The earlier version of this lemma asked for the mass on `(yBot N, 2N]`,
which needs `≍ L₃N` halvings and is NOT implied by `ε_N → 0`; retying `JG` to the full mass
`S_P(N)` — legitimate because leg E5's contracting site index is bounded
(`exists_site_re_nonpos_le`) — replaces it by this. -/
theorem freshMassTwo_graded (hS : SqrtFreshMassZero P) :
    ∀ᶠ N : ℕ in atTop, recipSumIoc P N (2 * N) ≤ 1 := by
  filter_upwards [(epsG_tendsto P hS yBotG_tendsto).eventually
      (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    yBotG_tendsto.eventually_ge_atTop 4, yBotG_le_self, eventually_ge_atTop 2] with N h1 h4 hyN hN2
  have hsq : Nat.sqrt (2 * N) ≤ N := by
    by_contra hc
    have h1 : N + 1 ≤ Nat.sqrt (2 * N) := by omega
    have h2 : (N + 1) ^ 2 ≤ Nat.sqrt (2 * N) ^ 2 := Nat.pow_le_pow_left h1 2
    have h3 := Nat.sqrt_le' (2 * N)
    nlinarith
  have hmono : recipSumIoc P N (2 * N) ≤ recipSumIoc P (Nat.sqrt (2 * N)) (2 * N) := by
    unfold recipSumIoc
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_left hsq)) ?_
    exact fun p _ _ => by positivity
  have hyb : yBotG N ≤ 2 * N := le_trans hyN (by omega)
  have := recipSumIoc_le_epsG P N h4 hyb
  linarith

theorem tailOK_graded (hS : SqrtFreshMassZero P) (hP : DivergentRecip P) :
    TailOK P (JG P) := by
  rw [TailOK]
  refine squeeze_zero' (Eventually.of_forall (fun N => ?_)) ?_
    (tail_graded P (freshMassTwo_graded P hS) hP)
  · exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Nat.cast_nonneg N)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact tail_error_L1 P (JG P N) N hN

theorem kmt_along_graded (hS : SqrtFreshMassZero P) (hP : DivergentRecip P) :
    KMT_along P (JG P) := by
  intro h hh
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  have hsum : Tendsto (fun N : ℕ =>
      termE1 P h N + (termE4a P N + termE4b P N + termE4c P N) + termE5 P h N)
      atTop (𝓝 0) := by
    have := ((termE1_tendsto P hS hP h).add
      (((termE4a_tendsto P hS hP).add (termE4b_tendsto P hS hP)).add (termE4c_tendsto P hP))).add
      (termE5_tendsto P hS hP h)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hsum
  filter_upwards [windowMean_le_terms P h, eventually_gt_atTop 0,
    (JG_tendsto P hP).eventually_ge_atTop (h.natAbs + 1)] with N hb hN hJ
  exact hb ⟨h.natAbs + 1, by omega, hJ, nontrivial_site hh⟩ hN

/-- **Theorem C′** (Astra §11 / Fable §9): vanishing square-root fresh reciprocal mass plus a
divergent reciprocal sum give a normal base-4 Lambert constant. -/
theorem isNormal_subsetLambert_of_sqrtFreshMassZero
    (hS : SqrtFreshMassZero P) (hP : DivergentRecip P) : IsNormal 4 (subsetLambert P 4) :=
  isNormal_subsetLambert_of_KMT_along P (JG P) (tailOK_graded P hS hP)
    (kmt_along_graded P hS hP)

end NormalNumbers.PrimeModel.FamilyGraded
