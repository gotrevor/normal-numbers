/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import NormalNumbers.CoefmassErdosBorweinMultiShiftAux
import NormalNumbers.CoefmassErdosBorweinShift

/-!
# Normal above the sub-power weight for every `c < 1`, given the `J`-shift Kubilius model
(personal-c5, 2026-10-26)

All definitions and the headline are verbatim from the KB packet `NNErdosBorweinRandom.lean`; never
edit them.  `MultiShiftKubiliusTV` is a named hypothesis: never prove, weaken or axiomatize it.
The paper argument is in `nn-erdos-borwein-random-2026-10-12.md`, section "Normal for c < 1 given
the J-shift Kubilius model"; the plan is in `EB-MULTISHIFT-NEXT.md`.
-/

namespace NormalNumbers.ErdosBorweinMultiShift

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open NormalNumbers.ErdosBorweinPositive NormalNumbers.ErdosBorweinEndpoint NormalNumbers.ErdosBorweinShift

/-- The sub-power weight `(log m)^{−ln 2} · exp(−ln 2 · √(c·u·log u))`, with `u = log log m`.  Where
`c·u·log u < 0` (small `m`), `Real.sqrt` returns `0` and the weight is `(log m)^{−ln 2}`. -/
noncomputable def subpowerWeight (c : ℝ) (m : ℕ) : ℝ :=
  Real.rpow (Real.log m) (-Real.log 2) *
    Real.exp (-(Real.log 2) * Real.sqrt (c * Real.log (Real.log m) * Real.log (Real.log (Real.log m))))

theorem subpowerWeight_nonneg (c : ℝ) (m : ℕ) : 0 ≤ subpowerWeight c m := by
  by_cases hm : m = 0
  · subst m
    have hlog2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    simp [subpowerWeight, Real.zero_rpow (neg_ne_zero.mpr hlog2)]
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm1)
  unfold subpowerWeight
  exact mul_nonneg (Real.rpow_nonneg hlog _) (Real.exp_pos _).le

/-- Once `log log m ≥ 1`, the sub-power weight is antitone.  The split at `c = 0` is
essential: for `c ≤ 0` the square-root factor vanishes throughout this eventual range. -/
theorem subpowerWeight_antitone_of_log_log_one_le (c : ℝ) {m M : ℕ}
    (hm1 : 1 < m) (hmlog : 1 ≤ Real.log (Real.log m)) (hmM : m ≤ M) :
    subpowerWeight c M ≤ subpowerWeight c m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm1)
  have hM0 : (0 : ℝ) < M := hm0.trans_le (by exact_mod_cast hmM)
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm1)
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by
    exact_mod_cast hm1.trans_le hmM)
  have hlog : Real.log (m : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log hm0 (by exact_mod_cast hmM)
  have hloglog : Real.log (Real.log m) ≤ Real.log (Real.log M) :=
    Real.log_le_log hlogm hlog
  have hloglogm : 0 < Real.log (Real.log m) := zero_lt_one.trans_le hmlog
  have hloglogM : 0 < Real.log (Real.log M) := hloglogm.trans_le hloglog
  have hlogloglog : Real.log (Real.log (Real.log m)) ≤
      Real.log (Real.log (Real.log M)) :=
    Real.log_le_log hloglogm hloglog
  have hlogloglogm0 : 0 ≤ Real.log (Real.log (Real.log m)) :=
    Real.log_nonneg hmlog
  have hMlog : 1 ≤ Real.log (Real.log M) := hmlog.trans hloglog
  have hlogloglogM0 : 0 ≤ Real.log (Real.log (Real.log M)) :=
    Real.log_nonneg hMlog
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hendpoint :
      Real.rpow (Real.log M) (-Real.log 2) ≤
        Real.rpow (Real.log m) (-Real.log 2) :=
    Real.rpow_le_rpow_of_nonpos hlogm hlog (by linarith)
  by_cases hc : 0 ≤ c
  · have hradicand :
        c * Real.log (Real.log m) * Real.log (Real.log (Real.log m)) ≤
          c * Real.log (Real.log M) * Real.log (Real.log (Real.log M)) := by
      gcongr
    have hsqrt := Real.sqrt_le_sqrt hradicand
    have hpenalty :
        Real.exp (-(Real.log 2) * Real.sqrt
            (c * Real.log (Real.log M) * Real.log (Real.log (Real.log M)))) ≤
          Real.exp (-(Real.log 2) * Real.sqrt
            (c * Real.log (Real.log m) * Real.log (Real.log (Real.log m)))) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left hsqrt (by linarith)
    unfold subpowerWeight
    exact mul_le_mul hendpoint hpenalty (Real.exp_pos _).le
      (Real.rpow_nonneg hlogm.le _)
  · have hc' : c ≤ 0 := le_of_not_ge hc
    have hradm :
        c * Real.log (Real.log m) * Real.log (Real.log (Real.log m)) ≤ 0 := by
      rw [mul_assoc]
      exact mul_nonpos_of_nonpos_of_nonneg hc'
        (mul_nonneg hloglogm.le hlogloglogm0)
    have hradM :
        c * Real.log (Real.log M) * Real.log (Real.log (Real.log M)) ≤ 0 := by
      rw [mul_assoc]
      exact mul_nonpos_of_nonpos_of_nonneg hc'
        (mul_nonneg hloglogM.le hlogloglogM0)
    unfold subpowerWeight
    rw [Real.sqrt_eq_zero_of_nonpos hradM, Real.sqrt_eq_zero_of_nonpos hradm]
    simpa using hendpoint

/-- A large set of prime divisors above `P` forces large divisor-variance mass at the sub-power
weight.  Unlike the earlier finite-cutoff walk argument, this global-cutoff form needs no bound on
the total number of prime factors of `n`: every chain divisor is at most `n ≤ M`. -/
theorem divisorVarianceMass_ge_primeDivisorSet_subpower
    (v : ℕ → ℝ) (hv0 : ∀ d, 0 ≤ v d) (c c₀ : ℝ) {P n M : ℕ} (Q : Finset ℕ)
    (hQ : Q.Nonempty) (hprime : ∀ q ∈ Q, q.Prime) (hdvd : ∀ q ∈ Q, q ∣ n)
    (hlarge : ∀ q ∈ Q, P < q) (hn : n ≠ 0) (hnM : n ≤ M) (hP : 1 ≤ P)
    (hPlog : 1 ≤ Real.log (Real.log (P + 1))) (hc₀ : 0 ≤ c₀)
    (hv : ∀ d : ℕ, 2 ≤ d → c₀ * subpowerWeight c d ≤ v d) :
    (((2 ^ (Q.card - 1) : ℕ) : ℝ) * (c₀ * subpowerWeight c M)) ≤
      divisorVarianceMass v P n := by
  apply divisorVarianceMass_ge_primeDivisorSet v hv0 Q hQ hprime hdvd hlarge hn hnM
    (mul_nonneg hc₀ (subpowerWeight_nonneg c M))
  intro d hPd hdM
  have hP1d : P + 1 ≤ d := by omega
  have hP1 : 1 < P + 1 := by omega
  have hd1 : 1 < d := hP1.trans_le hP1d
  have hlogP : 0 < Real.log ((P : ℝ) + 1) := Real.log_pos (by exact_mod_cast hP1)
  have hlogd : 0 < Real.log (d : ℝ) := Real.log_pos (by exact_mod_cast hd1)
  have hlog : Real.log ((P : ℝ) + 1) ≤ Real.log (d : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hP1d
  have hloglog : Real.log (Real.log (P + 1)) ≤ Real.log (Real.log d) :=
    Real.log_le_log hlogP hlog
  have hdlog : 1 ≤ Real.log (Real.log d) := hPlog.trans hloglog
  calc
    c₀ * subpowerWeight c M ≤ c₀ * subpowerWeight c d :=
      mul_le_mul_of_nonneg_left
        (subpowerWeight_antitone_of_log_log_one_le c hd1 hdlog hdM) hc₀
    _ ≤ v d := hv d (by omega)

/-- The primes in `(P, y]`. -/
def primesIoc (P y : ℕ) : Finset ℕ := (Finset.Ioc P y).filter Nat.Prime

/-- The `J`-shift prime pattern of `n`: for each shift `j < J`, the primes in `(P, y]` that divide
`n + j + 1`. -/
def multiShiftPattern (P y J n : ℕ) : Fin J → Finset ℕ :=
  fun j => (n + j + 1).primeFactors.filter (fun p => P < p ∧ p ≤ y)

/-- Concrete deterministic Step 1: one heavy multishift column makes the corresponding summand
of `shiftedVarianceMass` exceed `T`.  The scalar hypothesis is deliberately separated from the
prime-chain argument; later asymptotics only have to show that the displayed explicit lower bound
beats `T b^(2j)`. -/
theorem shiftedVarianceMass_gt_of_heavyColumn
    (v : ℕ → ℝ) (hv0 : ∀ d, 0 ≤ v d) (c c₀ : ℝ)
    {P y n M b j₀ J : ℕ} {T : ℝ} (j : Fin J) (hb : 1 ≤ b)
    (hj₀ : j₀ ≤ j.val + 1) (hnM : n + j.val + 1 ≤ M) (hP : 1 ≤ P)
    (hPlog : 1 ≤ Real.log (Real.log (P + 1))) (hc₀ : 0 ≤ c₀)
    (hv : ∀ d : ℕ, 2 ≤ d → c₀ * subpowerWeight c d ≤ v d)
    (hQ : 1 ≤ (multiShiftPattern P y J n j).card)
    (hscalar : T * (b : ℝ) ^ (2 * (j.val + 1)) <
      (((2 ^ ((multiShiftPattern P y J n j).card - 1) : ℕ) : ℝ) *
        (c₀ * subpowerWeight c M))) :
    T < shiftedVarianceMass v b j₀ J P n := by
  let Q := multiShiftPattern P y J n j
  have hQcard : 1 ≤ Q.card := by simpa only [Q] using hQ
  have hQne : Q.Nonempty := Finset.card_pos.mp (Nat.zero_lt_one.trans_le hQcard)
  have hprime : ∀ q ∈ Q, q.Prime := by
    intro q hq
    exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hq).1).1
  have hdvd : ∀ q ∈ Q, q ∣ n + j.val + 1 := by
    intro q hq
    exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hq).1).2.1
  have hlarge : ∀ q ∈ Q, P < q := by
    intro q hq
    exact (Finset.mem_filter.mp hq).2.1
  have hn0 : n + j.val + 1 ≠ 0 := by omega
  have hchain := divisorVarianceMass_ge_primeDivisorSet_subpower v hv0 c c₀ Q
    hQne hprime hdvd hlarge hn0 hnM hP hPlog hc₀ hv
  have hmass : T * (b : ℝ) ^ (2 * (j.val + 1)) <
      divisorVarianceMass v P (n + j.val + 1) := by
    exact hscalar.trans_le hchain
  have hbpos : (0 : ℝ) < (b : ℝ) ^ (2 * (j.val + 1)) := by
    positivity
  have hterm : T < ((b : ℝ) ^ (2 * (j.val + 1)))⁻¹ *
      divisorVarianceMass v P (n + j.val + 1) := by
    rw [mul_comm]
    exact (lt_mul_inv_iff₀ hbpos).2 hmass
  have hjmem : j.val + 1 ∈ Finset.Icc j₀ J := by
    exact Finset.mem_Icc.mpr ⟨hj₀, by omega⟩
  have hterm_le : ((b : ℝ) ^ (2 * (j.val + 1)))⁻¹ *
      divisorVarianceMass v P (n + j.val + 1) ≤ shiftedVarianceMass v b j₀ J P n := by
    unfold shiftedVarianceMass
    have hnonneg : ∀ k ∈ Finset.Icc j₀ J,
        0 ≤ ((b : ℝ) ^ (2 * k))⁻¹ * divisorVarianceMass v P (n + k) := by
      intro k hk
      exact mul_nonneg (by positivity) (divisorVarianceMass_nonneg v hv0 P (n + k))
    simpa only [Nat.add_assoc] using (Finset.single_le_sum (s := Finset.Icc j₀ J)
      (f := fun k ↦ ((b : ℝ) ^ (2 * k))⁻¹ * divisorVarianceMass v P (n + k))
      hnonneg hjmem)
  exact hterm.trans_le hterm_le

open Classical in
/-- Mass of `A` under the `J`-shift Kubilius model.  Each prime `p ∈ (P, y]` independently picks the
shift `j` with probability `1/p` (for each `j < J`), or no shift with probability `1 − J/p`. -/
noncomputable def multiShiftMass (P y J : ℕ) (A : Set (Fin J → Finset ℕ)) : ℝ :=
  ∑ σ : (primesIoc P y) → Option (Fin J),
    if (fun j => ((Finset.univ.filter (fun p : primesIoc P y => σ p = some j)).map
        (Function.Embedding.subtype _))) ∈ A then
      ∏ p : primesIoc P y, (match σ p with
        | none => 1 - (J : ℝ) / (p : ℕ)
        | some _ => 1 / ((p : ℕ) : ℝ))
    else 0

/-! ### Enumerating the concrete prime model -/

/-- An arbitrary enumeration of the primes in `(P, y]`.  All product masses below are invariant
under this choice. -/
noncomputable def primeIndexEquiv (P y : ℕ) :
    Fin (Fintype.card (primesIoc P y)) ≃ primesIoc P y :=
  (Fintype.equivFin (primesIoc P y)).symm

/-- Reconstruct the prime finset in every shift column from an indexed categorical configuration. -/
noncomputable def indexedMultiShiftPattern (P y J : ℕ)
    (τ : Fin (Fintype.card (primesIoc P y)) → Option (Fin J)) : Fin J → Finset ℕ :=
  fun j => (Finset.univ.filter (fun i => τ i = some j)).map
    ((primeIndexEquiv P y).toEmbedding.trans (Function.Embedding.subtype _))

theorem indexedMultiShiftPattern_eq_subtype (P y J : ℕ)
    (τ : Fin (Fintype.card (primesIoc P y)) → Option (Fin J)) :
    indexedMultiShiftPattern P y J τ =
      fun j => ((Finset.univ.filter
        (fun p : primesIoc P y => τ ((primeIndexEquiv P y).symm p) = some j)).map
          (Function.Embedding.subtype _)) := by
  classical
  funext j
  unfold indexedMultiShiftPattern
  rw [← Finset.map_map]
  congr 1
  ext p
  simp

/-- Enumeration does not change the number of selected primes in a shift column. -/
theorem card_indexedMultiShiftPattern (P y J : ℕ)
    (τ : Fin (Fintype.card (primesIoc P y)) → Option (Fin J)) (j : Fin J) :
    (indexedMultiShiftPattern P y J τ j).card =
      (Finset.univ.filter (fun i => τ i = some j)).card := by
  simp [indexedMultiShiftPattern]

/-- The packet's concrete multishift model is exactly the abstract categorical finite product,
after enumerating `primesIoc`. -/
theorem multiShiftMass_eq_finiteProductMass (P y J : ℕ)
    (A : Set (Fin J → Finset ℕ)) :
    multiShiftMass P y J A =
      finiteProductMass
        (fun i => categoricalShiftWeight J
          (1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)))
        {τ | indexedMultiShiftPattern P y J τ ∈ A} := by
  classical
  symm
  have hevent :
      {τ | indexedMultiShiftPattern P y J τ ∈ A} =
        {τ | (fun j => ((Finset.univ.filter
          (fun p : primesIoc P y =>
            τ ((primeIndexEquiv P y).symm p) = some j)).map
              (Function.Embedding.subtype _))) ∈ A} := by
    ext τ
    simp only [Set.mem_ofPred_eq]
    rw [indexedMultiShiftPattern_eq_subtype]
  rw [hevent]
  have hreindex := finiteProductMass_reindex (primeIndexEquiv P y)
    (fun p : primesIoc P y =>
      categoricalShiftWeight J (1 / ((p : ℕ) : ℝ)))
    {σ | (fun j => ((Finset.univ.filter
      (fun p : primesIoc P y => σ p = some j)).map
        (Function.Embedding.subtype _))) ∈ A}
  simp only [Set.mem_ofPred_eq] at hreindex
  rw [hreindex]
  unfold multiShiftMass
  apply Fintype.sum_congr
  intro σ
  split <;> rename_i hσ
  · apply Finset.prod_congr rfl
    intro p hp
    cases hval : σ p <;> simp [categoricalShiftWeight, div_eq_mul_inv]
  · rfl

/-- Concrete Step 4 comparison for the packet's prime model.  Its only error is the two copies of
the summed per-prime collision cost; the independent term factors over shifts by
`independentShiftProduct_card_lt_eq_prod_one_sub`. -/
theorem multiShiftMass_noHeavy_le_independent {P y J : ℕ} (hJP : J ≤ P)
    (threshold : Fin J → ℕ) :
    multiShiftMass P y J
        {Q | ∀ j, (Q j).card < threshold j} ≤
      finiteProductMass
          (fun i => independentShiftSubsetWeight J
            (1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)))
          {σ | ∀ j, (Finset.univ.filter (fun i => j ∈ σ i)).card < threshold j} +
        2 * ∑ i, (J : ℝ) * (J - 1 : ℕ) *
          (1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)) ^ 2 := by
  classical
  rw [multiShiftMass_eq_finiteProductMass]
  have hprime : ∀ i : Fin (Fintype.card (primesIoc P y)),
      Nat.Prime ((primeIndexEquiv P y) i : ℕ) := by
    intro i
    exact (Finset.mem_filter.mp ((primeIndexEquiv P y) i).property).2
  have hP : ∀ i : Fin (Fintype.card (primesIoc P y)),
      P < ((primeIndexEquiv P y) i : ℕ) := by
    intro i
    exact Finset.mem_Ioc.mp
      (Finset.mem_filter.mp ((primeIndexEquiv P y) i).property).1 |>.1
  have hq0 : ∀ i : Fin (Fintype.card (primesIoc P y)),
      0 ≤ (1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)) := by
    intro i
    positivity
  have hq1 : ∀ i : Fin (Fintype.card (primesIoc P y)),
      (1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)) ≤ 1 := by
    intro i
    have hpR : (0 : ℝ) < (((primeIndexEquiv P y) i : ℕ) : ℝ) := by
      exact_mod_cast (hprime i).pos
    apply (div_le_one hpR).2
    exact_mod_cast (hprime i).one_le
  have hJq : ∀ i : Fin (Fintype.card (primesIoc P y)),
      (J : ℝ) * (1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)) ≤ 1 := by
    intro i
    rw [mul_one_div]
    have hpR : (0 : ℝ) < (((primeIndexEquiv P y) i : ℕ) : ℝ) := by
      exact_mod_cast (hprime i).pos
    apply (div_le_one hpR).2
    exact_mod_cast hJP.trans (hP i).le
  simpa only [Set.mem_ofPred_eq, card_indexedMultiShiftPattern] using
    (categoricalShiftProduct_noHeavy_le_independent
      (fun i => 1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)) hq0 hq1 hJq threshold)

/-- The collision sum over the enumerated primes in `(P,y]` is bounded by the elementary
reciprocal-square tail `1/P`. -/
theorem sum_primeIndex_inv_sq_le {P y : ℕ} (hP0 : P ≠ 0) (hPy : P ≤ y) :
    (∑ i : Fin (Fintype.card (primesIoc P y)),
        (1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)) ^ 2) ≤
      ((P : ℝ) : ℝ)⁻¹ := by
  classical
  calc
    (∑ i : Fin (Fintype.card (primesIoc P y)),
        (1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)) ^ 2) =
        ∑ p : primesIoc P y, (1 / ((p : ℕ) : ℝ)) ^ 2 :=
      (primeIndexEquiv P y).sum_comp
        (fun p : primesIoc P y => (1 / ((p : ℕ) : ℝ)) ^ 2)
    _ = ∑ p ∈ primesIoc P y, (1 / (p : ℝ)) ^ 2 := by
      rw [← (primesIoc P y).attach_eq_univ]
      exact Finset.sum_attach (primesIoc P y)
        (fun p : ℕ => (1 / (p : ℝ)) ^ 2)
    _ = ∑ p ∈ primesIoc P y, (((p : ℝ) ^ 2)⁻¹) := by
      simp only [one_div, inv_pow]
    _ ≤ ∑ p ∈ Finset.Ioc P y, (((p : ℝ) ^ 2)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro p hpIoc hpnot
        positivity
    _ ≤ (P : ℝ)⁻¹ - (y : ℝ)⁻¹ :=
      sum_Ioc_inv_sq_le_sub hP0 hPy
    _ ≤ (P : ℝ)⁻¹ := sub_le_self _ (by positivity)

/-- Step 4 in its concrete factored form: the no-heavy model mass is bounded by a product of
independent one-column lower tails plus an explicit `O(J²/P)` collision error. -/
theorem multiShiftMass_noHeavy_le_prod_one_sub {P y J : ℕ} (hJP : J ≤ P)
    (hP0 : P ≠ 0) (hPy : P ≤ y) (threshold : Fin J → ℕ) :
    multiShiftMass P y J
        {Q | ∀ j, (Q j).card < threshold j} ≤
      ∏ j, (1 - NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass
        (Finset.univ : Finset
          (Fin (Fintype.card (primesIoc P y)) × Fin J))
        (fun z => 1 / (((primeIndexEquiv P y) z.1 : ℕ) : ℝ))
        {S | threshold j ≤
          (S ∩ shiftArrayColumn (Fintype.card (primesIoc P y)) J j).card}) +
        2 * (J : ℝ) * (J - 1 : ℕ) * (P : ℝ)⁻¹ := by
  calc
    multiShiftMass P y J {Q | ∀ j, (Q j).card < threshold j} ≤
        finiteProductMass
            (fun i => independentShiftSubsetWeight J
              (1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)))
            {σ | ∀ j, (Finset.univ.filter (fun i => j ∈ σ i)).card < threshold j} +
          2 * ∑ i, (J : ℝ) * (J - 1 : ℕ) *
            (1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)) ^ 2 :=
      multiShiftMass_noHeavy_le_independent hJP threshold
    _ ≤ finiteProductMass
            (fun i => independentShiftSubsetWeight J
              (1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)))
            {σ | ∀ j, (Finset.univ.filter (fun i => j ∈ σ i)).card < threshold j} +
          2 * (J : ℝ) * (J - 1 : ℕ) * (P : ℝ)⁻¹ := by
      have herr :
          2 * ∑ i, (J : ℝ) * (J - 1 : ℕ) *
              (1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)) ^ 2 ≤
            2 * (J : ℝ) * (J - 1 : ℕ) * (P : ℝ)⁻¹ := by
        calc
        2 * ∑ i, (J : ℝ) * (J - 1 : ℕ) *
            (1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)) ^ 2 =
            (2 * (J : ℝ) * (J - 1 : ℕ)) *
              ∑ i, (1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)) ^ 2 := by
          have hfactor :
              (∑ i, (J : ℝ) * (J - 1 : ℕ) *
                (1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)) ^ 2) =
                ((J : ℝ) * (J - 1 : ℕ)) *
                  ∑ i, (1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)) ^ 2 := by
            rw [Finset.mul_sum]
          rw [hfactor]
          ring
        _ ≤ (2 * (J : ℝ) * (J - 1 : ℕ)) * (P : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left (sum_primeIndex_inv_sq_le hP0 hPy) (by positivity)
        _ = 2 * (J : ℝ) * (J - 1 : ℕ) * (P : ℝ)⁻¹ := by ring
      simpa only [add_comm] using add_le_add_left herr
        (finiteProductMass
          (fun i => independentShiftSubsetWeight J
            (1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)))
          {σ | ∀ j, (Finset.univ.filter (fun i => j ∈ σ i)).card < threshold j})
    _ = _ := by
      rw [independentShiftProduct_card_lt_eq_prod_one_sub]

open Classical in
/-- **Hypothesis (sieve, dimension `J`): the `J`-shift Kubilius model.**  This is the natural
`J`-dimensional extension of `KubiliusTV`.  It is expected from the fundamental lemma of sieve theory
in dimension `J` at level `N^{1/2}`.  The large-pattern mass is `e^{−u/2 + 2J}` by Rankin, and the
remainder is `≤ N^{−1/2}(log N)^J`.  Searched for (2026-10-26) and not found in print: Tenenbaum
1999, Ford 2025 (IMRN rnaf079) and Gorodetsky (arXiv 2608.14190, Thm 2.3 and Cor 2.5) treat a single
sequence.  A named hypothesis, not an axiom.  Confidence 85% in this form. -/
def MultiShiftKubiliusTV : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N y J P : ℕ, 1 ≤ J → J ≤ P → 2 ≤ y → y ≤ N →
    C * J * Real.log (J + 2) ≤ Real.log N / Real.log y →
    ∀ A : Set (Fin J → Finset ℕ),
      |(((Finset.Icc 1 N).filter (fun n => multiShiftPattern P y J n ∈ A)).card : ℝ) / N -
          multiShiftMass P y J A| ≤
        C * (Real.exp (-(Real.log N / Real.log y) / C) + Real.log N ^ J / Real.sqrt N)

/-- **Target (positive side): normal above the sub-power weight for every `c < 1`, given the
`J`-shift Kubilius model.**  This is `EBLogWindow`'s normal half at its conjectured threshold.
Step 1′ (`ebRandom_ae_normal_of_shiftedVariance_diverges`) is fed by heavy-neighbour coverage.
Take `J ≍ √L` and `y₀ = N^{1/u}` with `u = J (log L)³`.  The heavy event for shift `j` is
`#{p ∈ (P₀, y₀] : p ∣ n+j} ≥ mean + ψ(L₀) + 2j log₂ b + B log L`, giving
`W(n+j) ≥ T b^{2j}` by the chain bound.  In the model, couple to independent shifts (cost
`J²/P₀`) and use a tilted-Chebyshev moderate-deviation lower bound.  Then
`P(no heavy) ≤ exp(−Σ_j p_j)` with `Σ_j p_j ≳ L^{−c(1+ε)/2}√(L/log L) → ∞`.  One TV application
transfers the event.  Draft: "Normal for c < 1 given the J-shift Kubilius model".  Confidence 70%. -/
theorem ebRandom_ae_normal_subpower_of_multiShift (hM : MultiShiftKubiliusTV)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (c c₀ : ℝ) (hc : c < 1) (hc₀ : 0 < c₀)
    (hdelta : ∀ m : ℕ, 2 ≤ m → c₀ * subpowerWeight c m ≤ delta m * (1 - delta m)) :
    ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → NormalNumbers.IsNormal b (ebLambert b X w) := by
  sorry

end NormalNumbers.ErdosBorweinMultiShift
