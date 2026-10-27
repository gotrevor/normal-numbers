/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import NormalNumbers.CoefmassErdosBorweinMultiShift
import NormalNumbers.CoefmassErdosBorweinPairShiftAux

/-!
# Normal above the sub-power weight for every `c < 1`, given only the pair Kubilius model
(personal-c5, 2026-10-26)

All definitions and the headline are verbatim from the KB packet `NNErdosBorweinRandom.lean`; never
edit them.  `PairShiftKubiliusTV` is a named hypothesis: never prove, weaken or axiomatize it.  Do not
use `MultiShiftKubiliusTV` (the point of this file is to avoid it).  The paper argument is in
`nn-erdos-borwein-random-2026-10-12.md`, section "Normal for c < 1 from a pair model only"; the plan
is in `EB-PAIRSHIFT-NEXT.md`.
-/

namespace NormalNumbers.ErdosBorweinPairShift

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open NormalNumbers.ErdosBorweinPositive NormalNumbers.ErdosBorweinEndpoint NormalNumbers.ErdosBorweinShift
open NormalNumbers.ErdosBorweinMultiShift

/-- The primes in `(P, y]` that divide `m`. -/
def primePatternIoc (P y m : ℕ) : Finset ℕ := m.primeFactors.filter (fun p => P < p ∧ p ≤ y)

open Classical in
/-- Mass of `A` under the pair Kubilius model.  Each prime `p ∈ (P, y]` independently divides the
first shift (`some false`) with probability `1/p`, the second (`some true`) with probability `1/p`,
or neither with probability `1 − 2/p`. -/
noncomputable def pairShiftMass (P y : ℕ) (A : Set (Finset ℕ × Finset ℕ)) : ℝ :=
  ∑ σ : (primesIoc P y) → Option Bool,
    if ((Finset.univ.filter (fun p : primesIoc P y => σ p = some false)).map
          (Function.Embedding.subtype _),
        (Finset.univ.filter (fun p : primesIoc P y => σ p = some true)).map
          (Function.Embedding.subtype _)) ∈ A then
      ∏ p : primesIoc P y, (match σ p with
        | none => 1 - 2 / ((p : ℕ) : ℝ)
        | some _ => 1 / ((p : ℕ) : ℝ))
    else 0

open Classical in
/-- **Hypothesis (sieve, dimension 2): the pair Kubilius model.**  For two shifts `a < b ≤ N` with
`b − a ≤ P`, every prime `p > P` divides at most one of `n + a`, `n + b`.  The joint pattern of the
primes in `(P, y]` dividing them, for `n ≤ N` uniform, is within `C(e^{−u/C} + (log N)²/√N)` of the
pair model, `u = log N / log y`.  Expected from the fundamental lemma in fixed dimension `2` with
Rankin truncation.  A named hypothesis, not an axiom.  Confidence 92%. -/
def PairShiftKubiliusTV : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N y P a b : ℕ, 2 ≤ P → a < b → b - a ≤ P → b ≤ N → 2 ≤ y → y ≤ N →
    ∀ A : Set (Finset ℕ × Finset ℕ),
      |(((Finset.Icc 1 N).filter (fun n =>
          (primePatternIoc P y (n + a), primePatternIoc P y (n + b)) ∈ A)).card : ℝ) / N -
          pairShiftMass P y A| ≤
        C * (Real.exp (-(Real.log N / Real.log y) / C) + Real.log N ^ 2 / Real.sqrt N)

set_option maxHeartbeats 800000 in
/-- **Target: normal above the sub-power weight for every `c < 1`, given only the pair model.**  The
same conclusion as `ebRandom_ae_normal_subpower_of_multiShift`.  Count the heavy shifts
`Z = Σ_j 1[H_j]` and apply Chebyshev: in the pair model the heavy events are independent up to
`2/P₀`, so `Var Z/(E Z)² ≤ 1/Σ q_j + 2J²/(P₀ (Σ q_j)²) → 0`, using only the lower bound on `q_j`
and `Σ q_j → ∞`.  Draft: "Normal for c < 1 from a pair model only".  Confidence 85%. -/
theorem ebRandom_ae_normal_subpower_of_pairShift (hP : PairShiftKubiliusTV)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (c c₀ : ℝ) (hc : c < 1) (hc₀ : 0 < c₀)
    (hdelta : ∀ m : ℕ, 2 ≤ m → c₀ * subpowerWeight c m ≤ delta m * (1 - delta m)) :
    ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → NormalNumbers.IsNormal b (ebLambert b X w) := by
  classical
  have pairShiftMass_count_eq (P y t₀ t₁ : ℕ) :
      pairShiftMass P y
          {Q | t₀ ≤ Q.1.card ∧ t₁ ≤ Q.2.card} =
        pairBoolCountMass
          (fun i : Fin (Fintype.card (primesIoc P y)) ↦
            1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)) t₀ t₁ := by
    let A : Set ((primesIoc P y) → Option Bool) :=
      {σ | t₀ ≤ (Finset.univ.filter fun p ↦ σ p = some false).card ∧
        t₁ ≤ (Finset.univ.filter fun p ↦ σ p = some true).card}
    have hreindex := finiteProductMass_reindex (primeIndexEquiv P y)
      (fun p : primesIoc P y ↦ pairBoolWeight (1 / ((p : ℕ) : ℝ))) A
    have hcardReindex
        (σ : Fin (Fintype.card (primesIoc P y)) → Option Bool) (b : Bool) :
        (Finset.univ.filter fun i ↦ σ i = some b).card =
          (Finset.univ.filter fun p : primesIoc P y ↦
            σ ((primeIndexEquiv P y).symm p) = some b).card := by
      apply Finset.card_bij'
        (fun i _ ↦ (primeIndexEquiv P y) i)
        (fun p _ ↦ (primeIndexEquiv P y).symm p)
      · intro i hi
        simpa using hi
      · intro p hp
        simpa using hp
      · intro i hi
        simp
      · intro p hp
        simp
    have hpreimage :
        {σ : Fin (Fintype.card (primesIoc P y)) → Option Bool |
          t₀ ≤ (Finset.univ.filter fun i ↦ σ i = some false).card ∧
          t₁ ≤ (Finset.univ.filter fun i ↦ σ i = some true).card} =
        {σ | (fun p ↦ σ ((primeIndexEquiv P y).symm p)) ∈ A} := by
      ext σ
      simp only [Set.mem_ofPred_eq, A]
      rw [← hcardReindex σ false, ← hcardReindex σ true]
    rw [← hpreimage] at hreindex
    unfold pairShiftMass pairBoolCountMass
    rw [hreindex]
    apply Fintype.sum_congr
    intro σ
    by_cases hσ : σ ∈ A
    · rw [if_pos hσ]
      have hcardFalse :
          (((Finset.univ.filter (fun p : primesIoc P y ↦ σ p = some false)).map
            (Function.Embedding.subtype _)).card) =
            (Finset.univ.filter fun p : primesIoc P y ↦ σ p = some false).card :=
        Finset.card_map _
      have hcardTrue :
          (((Finset.univ.filter (fun p : primesIoc P y ↦ σ p = some true)).map
            (Function.Embedding.subtype _)).card) =
            (Finset.univ.filter fun p : primesIoc P y ↦ σ p = some true).card :=
        Finset.card_map _
      rw [if_pos (by simpa only [A, Set.mem_ofPred_eq, hcardFalse, hcardTrue] using hσ)]
      apply Finset.prod_congr rfl
      intro p hp
      cases σ p <;> simp [pairBoolWeight, div_eq_mul_inv]
    · rw [if_neg hσ]
      rw [if_neg]
      intro hcounts
      apply hσ
      simpa only [A, Set.mem_ofPred_eq, Finset.card_map] using hcounts
  apply ebRandom_ae_normal_of_shiftedVariance_diverges μ delta X hX
    multiShiftScheduleJ eventually_multiShiftScheduleJ_le_log_log
  intro b hb j₀ T
  obtain ⟨C, hC, hTV⟩ := hP
  obtain ⟨eps, eta, A, alpha, heps, heta0, heta1, hetaEps, hA,
      hlargeA, habsorbA, halpha, halphaHalf⟩ :=
    exists_multiShiftModerateParameters c hc
  let v : ℕ → ℝ := fun m ↦ delta m * (1 - delta m)
  let Q : ℕ → ℝ := fun N ↦
    ∑ j : Fin (multiShiftScheduleJ N) with j₀ ≤ j.val + 1,
      pairScheduledColumnMass c A b N j
  let R : ℕ → ℝ := pairShiftSecondError C
  have hQ : Tendsto Q atTop atTop := by
    simpa only [Q] using tendsto_pairActiveColumnMassSum
      c A eps eta alpha hc hA heps heta0 heta1 hetaEps hlargeA habsorbA
        halpha halphaHalf b hb j₀
  have hR : Tendsto R atTop (nhds 0) := by
    simpa only [R] using tendsto_pairShiftSecondError C hC
  have hupper : Tendsto
      (fun N ↦ (Q N + R N + 2 * Q N * R N) / Q N ^ 2) atTop (nhds 0) :=
    tendsto_pairChebyshevBound Q R R hQ hR hR
  refine squeeze_zero' (Eventually.of_forall fun N ↦ by positivity) ?_ hupper
  · have hLTop : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
      Real.tendsto_log_atTop.comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    filter_upwards [eventually_multiShiftSieveGeometry,
        eventually_multiShiftCutoffY_bounds,
        eventually_multiShiftLogBlock_bounds,
        eventually_multiShiftThreshold_scalar c A c₀ T hA hc₀ b hb,
        eventually_multiShiftPrimeMean_bounds,
        hLTop.eventually_ge_atTop 3,
        hQ.eventually_gt_atTop 0,
        tendsto_multiShiftScheduleJ.eventually_ge_atTop 1] with
        N hgeom hy hblock hscalar hmean hL hQpos hJpos
    let P : ℕ := collisionCutoff N
    let y : ℕ := multiShiftCutoffY N
    let J : ℕ := multiShiftScheduleJ N
    let threshold : Fin J → ℕ := fun j ↦ multiShiftThreshold c A b N j.val
    let active : Finset (Fin J) := Finset.univ.filter (fun j ↦ j₀ ≤ j.val + 1)
    let H : Fin J → ℕ → Prop := fun j n ↦
      threshold j ≤ (multiShiftPattern P y J n j).card
    let count : ℕ → ℝ := finiteEventCount active H
    let colMass : ℕ → Fin 2 → ℝ := fun t k ↦
      NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass
        (Finset.univ : Finset (Fin (Fintype.card (primesIoc P y)) × Fin 2))
        (fun z ↦ 1 / (((primeIndexEquiv P y) z.1 : ℕ) : ℝ))
        {S | t ≤ (S ∩ shiftArrayColumn (Fintype.card (primesIoc P y)) 2 k).card}
    let q : Fin J → ℝ := fun j ↦ colMass (threshold j) 1
    let E : ℝ := pairShiftSieveError C N + 4 * (P : ℝ)⁻¹
    have hJ1 : 1 ≤ J := by simpa only [J] using hgeom.1
    have hJP : J ≤ P := by simpa only [J, P] using hgeom.2.1
    have hP2 : 2 ≤ P := by simpa only [P] using hblock.1
    have hy2 : 2 ≤ y := by simpa only [y] using hgeom.2.2.1
    have hyN : y ≤ N := by simpa only [y] using hgeom.2.2.2.1
    have hPy : P ≤ y := by simpa only [P, y] using hy.1
    have hN0 : 0 < N := lt_of_lt_of_le (by omega) hyN
    have hPlog : 1 ≤ Real.log (Real.log (P + 1)) := by
      let L : ℝ := Real.log (Real.log N)
      have hL3 : 3 ≤ L := by simpa only [L] using hL
      have hfloor := natFloor_exp_log_bounds
        (x := L ^ 2) (show 2 * Real.log 2 ≤ L ^ 2 by
          have hlog2lt : Real.log (2 : ℝ) < 1 := Real.log_two_lt_d9.trans (by norm_num)
          nlinarith)
      change 2 ≤ P ∧ L ^ 2 / 2 ≤ Real.log P ∧
        Real.log P ≤ L ^ 2 ∧
        Real.log (L ^ 2) - Real.log 2 ≤ Real.log (Real.log P) ∧
        Real.log (Real.log P) ≤ Real.log (L ^ 2) at hfloor
      have hlogP3 : 3 ≤ Real.log P := by nlinarith [hfloor.2.1]
      have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
      have hlogMono : Real.log P ≤ Real.log (P + 1) := by
        apply Real.log_le_log hPpos
        exact_mod_cast (Nat.le_add_right P 1)
      calc
        (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log (Real.log (P + 1)) := Real.log_le_log (Real.exp_pos 1)
          (Real.exp_one_lt_three.le.trans (hlogP3.trans hlogMono))
    have hthreshold : ∀ j : Fin J, j₀ ≤ j.val + 1 → 1 ≤ threshold j := by
      intro j hj
      let L : ℝ := Real.log (Real.log N)
      have hL3 : 3 ≤ L := by simpa only [L] using hL
      have hmean0 : 0 < multiShiftPrimeMean N := by
        have hlower := hmean.1
        change L / 2 ≤ multiShiftPrimeMean N at hlower
        exact lt_of_lt_of_le (by nlinarith) hlower
      apply Nat.one_le_ceil_iff.mpr
      have hlogL0 : 0 < Real.log L := Real.log_pos (by linarith)
      have hpenalty : 0 ≤ multiShiftSubpowerPenalty c N := by
        simp only [multiShiftSubpowerPenalty]
        positivity
      have hshift : 0 ≤
          (((2 * (j.val + 1) : ℕ) : ℝ) * Real.log b / Real.log 2) := by
        have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
        have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
        positivity
      positivity
    have hcolRelabel (t : ℕ) : colMass t 0 = colMass t 1 := by
      simpa only [colMass] using pairIndependentColumnMass_zero_eq_one
        (fun i : Fin (Fintype.card (primesIoc P y)) ↦
          1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)) t
    have hcolZero : colMass 0 1 = 1 := by
      rw [← hcolRelabel 0]
      dsimp only [colMass]
      rw [show {S : Finset (Fin (Fintype.card (primesIoc P y)) × Fin 2) |
          0 ≤ (S ∩ shiftArrayColumn (Fintype.card (primesIoc P y)) 2 0).card} =
          Set.univ by ext S; simp]
      exact NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass_univ _ _
    have hmodelApprox (t₀ t₁ : ℕ) :
        |pairShiftMass P y {U | t₀ ≤ U.1.card ∧ t₁ ≤ U.2.card} -
            colMass t₀ 1 * colMass t₁ 1| ≤ 4 * (P : ℝ)⁻¹ := by
      have hc := abs_pairBoolCountMass_sub_independent_le_inv hP2 hPy t₀ t₁
      rw [← pairShiftMass_count_eq P y t₀ t₁] at hc
      change |pairShiftMass P y {U | t₀ ≤ U.1.card ∧ t₁ ≤ U.2.card} -
        colMass t₀ 0 * colMass t₁ 1| ≤ 4 * (P : ℝ)⁻¹ at hc
      rwa [hcolRelabel t₀] at hc
    have hmarginal (j : Fin J) :
        q j - E ≤
            (((Finset.Icc 1 N).filter (fun n ↦ H j n)).card : ℝ) / N ∧
          (((Finset.Icc 1 N).filter (fun n ↦ H j n)).card : ℝ) / N ≤ q j + E := by
      let event : Set (Finset ℕ × Finset ℕ) :=
        {U | 0 ≤ U.1.card ∧ threshold j ≤ U.2.card}
      have hshiftLe : j.val + 1 ≤ P := (show j.val + 1 ≤ J by omega).trans hJP
      have hshiftN : j.val + 1 ≤ N := hshiftLe.trans (hPy.trans hyN)
      have htv := hTV N y P 0 (j.val + 1) hP2 (by omega) (by simpa using hshiftLe)
        hshiftN hy2 hyN event
      have htv' :
          |(((Finset.Icc 1 N).filter (fun n ↦ H j n)).card : ℝ) / N -
              pairShiftMass P y event| ≤ pairShiftSieveError C N := by
        simpa only [event, H, threshold, multiShiftPattern, primePatternIoc,
          Set.mem_ofPred_eq, Nat.zero_add, zero_le, true_and, pairShiftSieveError,
          P, y, J, Nat.add_assoc, neg_div] using htv
      have hmodel := hmodelApprox 0 (threshold j)
      have hmodel' : |pairShiftMass P y event - q j| ≤ 4 * (P : ℝ)⁻¹ := by
        simpa only [event, q, hcolZero, one_mul] using hmodel
      have htvBounds := abs_le.mp htv'
      have hmodelBounds := abs_le.mp hmodel'
      constructor <;> dsimp only [E] <;> linarith
    have hoff (i : Fin J) (_hi : i ∈ active) (j : Fin J) (_hj : j ∈ active)
        (hij : i ≠ j) :
        (((Finset.Icc 1 N).filter (fun n ↦ H i n ∧ H j n)).card : ℝ) / N ≤
          q i * q j + E := by
      have hval : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
      rcases lt_or_gt_of_ne hval with hijlt | hjilt
      · let event : Set (Finset ℕ × Finset ℕ) :=
          {U | threshold i ≤ U.1.card ∧ threshold j ≤ U.2.card}
        have hdiff : (j.val + 1) - (i.val + 1) ≤ P := by
          have : j.val + 1 ≤ J := by omega
          omega
        have hbN : j.val + 1 ≤ N :=
          (show j.val + 1 ≤ J by omega).trans (hJP.trans (hPy.trans hyN))
        have htv := hTV N y P (i.val + 1) (j.val + 1) hP2 (by omega)
          hdiff hbN hy2 hyN event
        have htv' :
            |(((Finset.Icc 1 N).filter (fun n ↦ H i n ∧ H j n)).card : ℝ) / N -
                pairShiftMass P y event| ≤ pairShiftSieveError C N := by
          simpa only [event, H, threshold, multiShiftPattern, primePatternIoc,
            Set.mem_ofPred_eq, pairShiftSieveError, P, y, J, Nat.add_assoc,
            neg_div] using htv
        have hmodel := hmodelApprox (threshold i) (threshold j)
        have hmodel' : |pairShiftMass P y event - q i * q j| ≤ 4 * (P : ℝ)⁻¹ := by
          simpa only [event, q] using hmodel
        have htvUpper := (abs_le.mp htv').2
        have hmodelUpper := (abs_le.mp hmodel').2
        dsimp only [E]
        linarith
      · let event : Set (Finset ℕ × Finset ℕ) :=
          {U | threshold j ≤ U.1.card ∧ threshold i ≤ U.2.card}
        have hdiff : (i.val + 1) - (j.val + 1) ≤ P := by
          have : i.val + 1 ≤ J := by omega
          omega
        have hbN : i.val + 1 ≤ N :=
          (show i.val + 1 ≤ J by omega).trans (hJP.trans (hPy.trans hyN))
        have htv := hTV N y P (j.val + 1) (i.val + 1) hP2 (by omega)
          hdiff hbN hy2 hyN event
        have htv' :
            |(((Finset.Icc 1 N).filter (fun n ↦ H i n ∧ H j n)).card : ℝ) / N -
                pairShiftMass P y event| ≤ pairShiftSieveError C N := by
          simpa only [event, H, threshold, multiShiftPattern, primePatternIoc,
            Set.mem_ofPred_eq, and_comm, pairShiftSieveError, P, y, J,
            Nat.add_assoc, neg_div] using htv
        have hmodel := hmodelApprox (threshold j) (threshold i)
        have hmodel' : |pairShiftMass P y event - q i * q j| ≤ 4 * (P : ℝ)⁻¹ := by
          have hm : |pairShiftMass P y event - q j * q i| ≤ 4 * (P : ℝ)⁻¹ := by
            simpa only [event, q] using hmodel
          calc
            |pairShiftMass P y event - q i * q j| =
                |pairShiftMass P y event - q j * q i| := by
              rw [mul_comm (q i) (q j)]
            _ ≤ 4 * (P : ℝ)⁻¹ := hm
        have htvUpper := (abs_le.mp htv').2
        have hmodelUpper := (abs_le.mp hmodel').2
        dsimp only [E]
        linarith
    have hq0 : ∀ j ∈ active, 0 ≤ q j := by
      intro j hj
      change 0 ≤ pairScheduledColumnMass c A b N j
      exact pairScheduledColumnMass_nonneg c A b N j
    have hScard : (Finset.Icc 1 N).card = N := by simp [Nat.card_Icc]
    have hSnonempty : (Finset.Icc 1 N).Nonempty := by
      exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN0⟩⟩
    have hactiveCard : active.card ≤ J := by
      simpa only [active, Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.filter_subset (fun j : Fin J ↦ j₀ ≤ j.val + 1) Finset.univ)
    have hE0 : 0 ≤ E := by
      dsimp only [E, pairShiftSieveError]
      positivity
    have hRform : R N = (J : ℝ) ^ 2 * E := by
      dsimp only [R, pairShiftSecondError, E, pairShiftSieveError, P, J]
      ring
    have hactiveSq : ((active.card : ℕ) : ℝ) ^ 2 ≤ (J : ℝ) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hactiveCard) 2
    have hactiveOne : (active.card : ℝ) ≤ (J : ℝ) ^ 2 := by
      have hcardJ : (active.card : ℝ) ≤ J := by exact_mod_cast hactiveCard
      have hJone : (1 : ℝ) ≤ J := by simpa only [J] using hJpos
      have hJsq : (J : ℝ) ≤ (J : ℝ) ^ 2 := by
        calc
          (J : ℝ) = J * 1 := by ring
          _ ≤ J * J := mul_le_mul_of_nonneg_left hJone (by positivity)
          _ = J ^ 2 := by ring
      exact hcardJ.trans hJsq
    have hfirstRaw :
        (∑ j ∈ active, q j) - (active.card : ℝ) * E ≤
          (∑ n ∈ Finset.Icc 1 N, count n) / ((Finset.Icc 1 N).card : ℝ) := by
      rw [sum_finiteEventCount, hScard]
      calc
        (∑ j ∈ active, q j) - (active.card : ℝ) * E =
            ∑ j ∈ active, (q j - E) := by
          simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ j ∈ active,
            (((Finset.Icc 1 N).filter (fun n ↦ H j n)).card : ℝ) / N := by
          apply Finset.sum_le_sum
          intro j hj
          exact (hmarginal j).1
        _ ≤ (∑ j ∈ active,
            (((Finset.Icc 1 N).filter (fun n ↦ H j n)).card : ℝ)) / N := by
          exact le_of_eq ((Finset.sum_div active
            (fun j ↦ (((Finset.Icc 1 N).filter (fun n ↦ H j n)).card : ℝ)) N).symm)
        _ ≤ _ := by
          apply le_of_eq
          apply congrArg (fun z : ℝ ↦ z / N)
          apply Finset.sum_congr rfl
          intro j hj
          apply congrArg (fun k : ℕ ↦ (k : ℝ))
          apply congrArg Finset.card
          apply Finset.ext
          intro n
          simp only [Finset.mem_filter]
    have hfirst :
        (∑ j ∈ active, q j) - R N ≤
          (∑ n ∈ Finset.Icc 1 N, count n) / ((Finset.Icc 1 N).card : ℝ) := by
      have herrLe : (active.card : ℝ) * E ≤ R N := by
        rw [hRform]
        exact mul_le_mul_of_nonneg_right hactiveOne hE0
      linarith
    let p : Fin J → Fin J → ℝ := fun i j ↦
      (((@Finset.filter ℕ (fun n ↦ H i n ∧ H j n)
        (fun n ↦ @instDecidableAnd (H i n) (H j n)
          (Classical.propDecidable (H i n)) (Classical.propDecidable (H j n)))
        (Finset.Icc 1 N)).card : ℕ) : ℝ) / N
    have hdiag : ∀ i ∈ active, p i i ≤ q i + E := by
      intro i hi
      have hm := (hmarginal i).2
      simpa only [p, and_self] using hm
    have hpairs := sum_pair_le_sq_add active q p E E hq0 hdiag
      (fun i hi j hj hij ↦ by
        dsimp only [p]
        rw [Finset.filter_congr_decidable]
        exact hoff i hi j hj hij)
    have hsecondRaw :
        (∑ n ∈ Finset.Icc 1 N, (count n) ^ 2) /
            ((Finset.Icc 1 N).card : ℝ) ≤
          (∑ j ∈ active, q j) ^ 2 + (∑ j ∈ active, q j) +
            (active.card : ℝ) * E +
              (active.card : ℝ) * (active.card - 1 : ℕ) * E := by
      rw [sum_finiteEventCount_sq, hScard]
      calc
        (∑ i ∈ active, ∑ j ∈ active,
            (((@Finset.filter ℕ (fun n ↦ H i n ∧ H j n)
              (fun n ↦ @instDecidableAnd (H i n) (H j n)
                (Classical.propDecidable (H i n)) (Classical.propDecidable (H j n)))
              (Finset.Icc 1 N)).card : ℕ) : ℝ)) / N =
            ∑ i ∈ active, ∑ j ∈ active, p i j := by
          let d : Fin J → Fin J → ℝ := fun i j ↦
            (((@Finset.filter ℕ (fun n ↦ H i n ∧ H j n)
              (fun n ↦ @instDecidableAnd (H i n) (H j n)
                (Classical.propDecidable (H i n)) (Classical.propDecidable (H j n)))
              (Finset.Icc 1 N)).card : ℕ) : ℝ)
          have hinner (i : Fin J) :
              (∑ j ∈ active, d i j) / N = ∑ j ∈ active, p i j := by
            calc
              (∑ j ∈ active, d i j) / N = ∑ j ∈ active, d i j / N :=
                Finset.sum_div active (fun j ↦ d i j) N
              _ = ∑ j ∈ active, p i j := by
                apply Finset.sum_congr rfl
                intro j hj
                rfl
          calc
            (∑ i ∈ active, ∑ j ∈ active, d i j) / N =
                ∑ i ∈ active, (∑ j ∈ active, d i j) / N :=
              Finset.sum_div active (fun i ↦ ∑ j ∈ active, d i j) N
            _ = ∑ i ∈ active, ∑ j ∈ active, p i j := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hinner i
        _ ≤ _ := hpairs
    have hagg :
        (active.card : ℝ) * E +
            (active.card : ℝ) * (active.card - 1 : ℕ) * E =
          (active.card : ℝ) ^ 2 * E := by
      by_cases hzero : active.card = 0
      · simp [hzero]
      · have hone : 1 ≤ active.card := Nat.one_le_iff_ne_zero.mpr hzero
        rw [Nat.cast_sub hone]
        push_cast
        ring
    have hsecond :
        (∑ n ∈ Finset.Icc 1 N, (count n) ^ 2) /
            ((Finset.Icc 1 N).card : ℝ) ≤
          (∑ j ∈ active, q j) ^ 2 + (∑ j ∈ active, q j) + R N := by
      have herrLe : (active.card : ℝ) ^ 2 * E ≤ R N := by
        rw [hRform]
        exact mul_le_mul_of_nonneg_right hactiveSq hE0
      calc
        (∑ n ∈ Finset.Icc 1 N, (count n) ^ 2) /
              ((Finset.Icc 1 N).card : ℝ) ≤
            ((∑ j ∈ active, q j) ^ 2 + (∑ j ∈ active, q j)) +
              ((active.card : ℝ) * E +
                (active.card : ℝ) * (active.card - 1 : ℕ) * E) := by
          simpa only [add_assoc] using hsecondRaw
        _ = ((∑ j ∈ active, q j) ^ 2 + (∑ j ∈ active, q j)) +
              (active.card : ℝ) ^ 2 * E := by rw [hagg]
        _ ≤ ((∑ j ∈ active, q j) ^ 2 + (∑ j ∈ active, q j)) + R N :=
          add_le_add_right herrLe _
    have hqsum : (∑ j ∈ active, q j) = Q N := by
      simp only [Q, active, q, colMass, threshold, P, y, J,
        pairScheduledColumnMass]
    have hcheb := card_filter_eq_zero_div_le_of_moments
      (Finset.Icc 1 N) count (Q N) (R N) (R N) hSnonempty hQpos
      (by rw [hRform]; positivity)
      (by simpa only [hqsum] using hfirst)
      (by simpa only [hqsum] using hsecond)
    have hdet : ∀ n ∈ Finset.Icc 1 N,
        shiftedVarianceMass v b j₀ J P n ≤ T → count n = 0 := by
      intro n hn hmass
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      have hnM : ∀ j : Fin J, n + j.val + 1 ≤ 2 * N := by
        intro j
        have hjN : j.val + 1 ≤ N := by
          have hjJ : j.val + 1 ≤ J := by omega
          exact hjJ.trans (hJP.trans (hPy.trans hyN))
        omega
      have hpattern := low_shiftedVarianceMass_pattern_noHeavy
        (P := P) (y := y) (n := n) (M := 2 * N) (b := b) (j₀ := j₀)
        (J := J) (T := T) v
        (fun d ↦ mul_nonneg (hX.1 d).1 (sub_nonneg.mpr (hX.1 d).2)) c c₀
        threshold (by omega) hnM (by omega) hPlog hc₀.le hdelta hthreshold
        (fun j hj ↦ by simpa only [threshold] using hscalar j.val) hmass
      apply finiteEventCount_eq_zero_of_forall_not
      intro j hj
      have hjactive : j₀ ≤ j.val + 1 := (Finset.mem_filter.mp hj).2
      have hjlt := hpattern j
      simp only [H]
      simpa only [if_pos hjactive] using (not_le.mpr hjlt)
    have hsubset :
        (Finset.Icc 1 N).filter (fun n ↦ shiftedVarianceMass v b j₀ J P n ≤ T) ⊆
          (Finset.Icc 1 N).filter (fun n ↦ count n = 0) := by
      intro n hn
      simp only [Finset.mem_filter] at hn ⊢
      exact ⟨hn.1, hdet n hn.1 hn.2⟩
    have hcard :
        (((Finset.Icc 1 N).filter
          (fun n ↦ shiftedVarianceMass v b j₀ J P n ≤ T)).card : ℝ) ≤
        (((Finset.Icc 1 N).filter (fun n ↦ count n = 0)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    have hdensity := div_le_div_of_nonneg_right hcard (by positivity : (0 : ℝ) ≤ N)
    change (((Finset.Icc 1 N).filter (fun n ↦
      shiftedVarianceMass (fun m ↦ delta m * (1 - delta m)) b j₀
        (multiShiftScheduleJ N) (collisionCutoff N) n ≤ T)).card : ℝ) / N ≤ _
    exact hdensity.trans (by
      rw [hScard] at hcheb
      simpa only [Q, R, P, y, J, v, count] using hcheb)

end NormalNumbers.ErdosBorweinPairShift
