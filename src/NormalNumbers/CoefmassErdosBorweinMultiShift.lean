/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import NormalNumbers.CoefmassErdosBorweinEndpointKub
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

/-- The packet's prime block is the natural-cutoff block used by the existing Mertens theorem. -/
theorem primesIoc_eq_primesUpTo_filter (P y : ℕ) :
    primesIoc P y =
      (NormalNumbers.ErdosBorweinEndpointKub.primesUpTo y).filter (P < ·) := by
  ext p
  simp [primesIoc, NormalNumbers.ErdosBorweinEndpointKub.primesUpTo_eq_filter_Iic,
    and_comm, and_left_comm, and_assoc]

/-- Mertens' second theorem, specialized to the packet's prime block `(P,y]`. -/
theorem mertens_primesIoc_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P y : ℕ, 2 ≤ P → P ≤ y →
      |∑ p ∈ primesIoc P y, (1 / p : ℝ) -
          (Real.log (Real.log y) - Real.log (Real.log P))| ≤ 2 * C := by
  obtain ⟨C, hC⟩ :=
    NormalNumbers.ErdosBorweinEndpointKub.mertens_primeReciprocalSum_bound
  have hC0 : 0 ≤ C :=
    (abs_nonneg (∑ p ∈ NormalNumbers.ErdosBorweinEndpointKub.primesUpTo 2,
      (1 / p : ℝ) - Real.log (Real.log 2))).trans (hC 2 (by norm_num))
  refine ⟨C, hC0, ?_⟩
  intro P y hP hPy
  rw [primesIoc_eq_primesUpTo_filter,
    NormalNumbers.ErdosBorweinEndpointKub.primeReciprocalSum_block_eq_sub P y hPy]
  have hCP := hC P hP
  have hCy := hC y (hP.trans hPy)
  have htriangle :
      |((∑ p ∈ NormalNumbers.ErdosBorweinEndpointKub.primesUpTo y, (1 / p : ℝ)) -
          Real.log (Real.log y)) -
        ((∑ p ∈ NormalNumbers.ErdosBorweinEndpointKub.primesUpTo P, (1 / p : ℝ)) -
          Real.log (Real.log P))| ≤ C + C :=
    (abs_sub _ _).trans (add_le_add hCy hCP)
  convert htriangle using 1 <;> ring

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

/-- Enumerating the packet's prime block preserves its reciprocal-prime mean. -/
theorem sum_primeIndex_inv_eq_primesIoc (P y : ℕ) :
    (∑ i : Fin (Fintype.card (primesIoc P y)),
        1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)) =
      ∑ p ∈ primesIoc P y, (1 / p : ℝ) := by
  classical
  calc
    (∑ i : Fin (Fintype.card (primesIoc P y)),
        1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)) =
        ∑ p : primesIoc P y, 1 / ((p : ℕ) : ℝ) :=
      (primeIndexEquiv P y).sum_comp
        (fun p : primesIoc P y ↦ 1 / ((p : ℕ) : ℝ))
    _ = ∑ p ∈ primesIoc P y, (1 / p : ℝ) := by
      rw [← (primesIoc P y).attach_eq_univ]
      exact Finset.sum_attach (primesIoc P y) (fun p : ℕ ↦ (1 / p : ℝ))

/-- Every independent shift column has exactly the packet's reciprocal-prime mean. -/
theorem sum_shiftArrayColumn_inv_eq_primesIoc {P y J : ℕ} (j : Fin J) :
    (∑ z ∈ shiftArrayColumn (Fintype.card (primesIoc P y)) J j,
        1 / (((primeIndexEquiv P y) z.1 : ℕ) : ℝ)) =
      ∑ p ∈ primesIoc P y, (1 / p : ℝ) := by
  calc
    (∑ z ∈ shiftArrayColumn (Fintype.card (primesIoc P y)) J j,
        1 / (((primeIndexEquiv P y) z.1 : ℕ) : ℝ)) =
        ∑ i, 1 / (((primeIndexEquiv P y) i : ℕ) : ℝ) :=
      sum_shiftArrayColumn_fst j
        (fun i ↦ 1 / (((primeIndexEquiv P y) i : ℕ) : ℝ))
    _ = ∑ p ∈ primesIoc P y, (1 / p : ℝ) :=
      sum_primeIndex_inv_eq_primesIoc P y

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

/-- The square-mass of one independent shift column is controlled by the reciprocal-square
tail above the packet's lower cutoff. -/
theorem sum_shiftArrayColumn_inv_sq_le {P y J : ℕ} (j : Fin J)
    (hP0 : P ≠ 0) (hPy : P ≤ y) :
    (∑ z ∈ shiftArrayColumn (Fintype.card (primesIoc P y)) J j,
        (1 / (((primeIndexEquiv P y) z.1 : ℕ) : ℝ)) ^ 2) ≤ (P : ℝ)⁻¹ := by
  calc
    (∑ z ∈ shiftArrayColumn (Fintype.card (primesIoc P y)) J j,
        (1 / (((primeIndexEquiv P y) z.1 : ℕ) : ℝ)) ^ 2) =
        ∑ i, (1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)) ^ 2 :=
      sum_shiftArrayColumn_fst j
        (fun i ↦ (1 / (((primeIndexEquiv P y) i : ℕ) : ℝ)) ^ 2)
    _ ≤ (P : ℝ)⁻¹ := sum_primeIndex_inv_sq_le hP0 hPy

/-- Concrete Step 5 adapter for one shift column.  The abstract moderate-deviation theorem is
applied on the column support; the cylinder identity then restores the full prime-by-shift
universe used by `multiShiftMass_noHeavy_le_prod_one_sub`. -/
theorem multiShiftColumnMass_ge_moderate
    {P y J : ℕ} (j : Fin J) (hP : 2 ≤ P) (hPy : P ≤ y)
    {eps eta x : ℝ} (heps : 0 < eps) (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 100)
    (hetaEps : 80 * eta ≤ eps)
    (hmean : 0 < ∑ p ∈ primesIoc P y, (1 / p : ℝ)) (hx : 0 < x)
    (hsquareMass : (P : ℝ)⁻¹ ≤ eta * ∑ p ∈ primesIoc P y, (1 / p : ℝ))
    (hsmallTilt : (1 + 4 * eta) * x / (∑ p ∈ primesIoc P y, (1 / p : ℝ)) ≤ eta)
    (hlargeDeviation : 6 * (∑ p ∈ primesIoc P y, (1 / p : ℝ)) ≤ eta ^ 2 * x ^ 2)
    (habsorb : 4 * Real.log 2 * (∑ p ∈ primesIoc P y, (1 / p : ℝ)) ≤
      eps * x ^ 2) :
    Real.exp (-((1 + eps) * x ^ 2 /
        (2 * ∑ p ∈ primesIoc P y, (1 / p : ℝ)))) ≤
      NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass
        (Finset.univ : Finset
          (Fin (Fintype.card (primesIoc P y)) × Fin J))
        (fun z ↦ 1 / (((primeIndexEquiv P y) z.1 : ℕ) : ℝ))
        {S | (∑ p ∈ primesIoc P y, (1 / p : ℝ)) + x ≤
          ((S ∩ shiftArrayColumn (Fintype.card (primesIoc P y)) J j).card : ℝ)} := by
  classical
  let n := Fintype.card (primesIoc P y)
  let U : Finset (Fin n × Fin J) := Finset.univ
  let B : Finset (Fin n × Fin J) := shiftArrayColumn n J j
  let q : Fin n × Fin J → ℝ :=
    fun z ↦ 1 / (((primeIndexEquiv P y) z.1 : ℕ) : ℝ)
  let mean : ℝ := ∑ p ∈ primesIoc P y, (1 / p : ℝ)
  have hprime : ∀ z ∈ B, Nat.Prime ((primeIndexEquiv P y) z.1 : ℕ) := by
    intro z hz
    exact (Finset.mem_filter.mp ((primeIndexEquiv P y) z.1).property).2
  have hq0 : ∀ z ∈ B, 0 ≤ q z := by
    intro z hz
    dsimp [q]
    positivity
  have hq1 : ∀ z ∈ B, q z ≤ 1 := by
    intro z hz
    have hpR : (0 : ℝ) < (((primeIndexEquiv P y) z.1 : ℕ) : ℝ) := by
      exact_mod_cast (hprime z hz).pos
    dsimp [q]
    apply (div_le_one hpR).2
    exact_mod_cast (hprime z hz).one_le
  have hmeanEq : ∑ z ∈ B, q z = mean := by
    simpa only [n, B, q, mean] using
      (sum_shiftArrayColumn_inv_eq_primesIoc (P := P) (y := y) j)
  have hsquare : (∑ z ∈ B, (q z) ^ 2) ≤ eta * ∑ z ∈ B, q z := by
    rw [hmeanEq]
    calc
      (∑ z ∈ B, (q z) ^ 2) ≤ (P : ℝ)⁻¹ := by
        simpa only [n, B, q] using
          (sum_shiftArrayColumn_inv_sq_le (P := P) (y := y) j (by omega) hPy)
      _ ≤ eta * mean := by simpa only [mean] using hsquareMass
  have hmoderate := bernoulliSubsetMass_card_ge_moderate_lower B q hq0 hq1
    heps heta0 heta1 hetaEps (hmeanEq.symm ▸ hmean) hx hsquare
    (hmeanEq.symm ▸ hsmallTilt) (hmeanEq.symm ▸ hlargeDeviation)
    (hmeanEq.symm ▸ habsorb)
  have hcylinder :=
    NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass_inter U B
      (Finset.subset_univ B) q {S | mean + x ≤ (S.card : ℝ)}
  calc
    Real.exp (-((1 + eps) * x ^ 2 / (2 * mean))) ≤
        NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass B q
          {S | mean + x ≤ (S.card : ℝ)} := by
      simpa only [hmeanEq] using hmoderate
    _ = NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass U q
          {S | mean + x ≤ ((S ∩ B).card : ℝ)} := by
      exact hcylinder.symm

/-- A square-root-scale buffer is enough to discharge the two lower-size hypotheses in the
moderate-deviation estimate.  This is useful also when `c ≤ 0`: adding a fixed sufficiently
large multiple of `sqrt mean` to the heavy threshold gives a fixed positive column probability,
so no separate central-tail theorem is needed. -/
theorem multiShiftColumnMass_ge_moderate_of_baseline
    {P y J : ℕ} (j : Fin J) (hP : 2 ≤ P) (hPy : P ≤ y)
    {eps eta x A : ℝ} (heps : 0 < eps) (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 100)
    (hetaEps : 80 * eta ≤ eps)
    (hmean : 0 < ∑ p ∈ primesIoc P y, (1 / p : ℝ)) (hx : 0 < x)
    (hsquareMass : (P : ℝ)⁻¹ ≤ eta * ∑ p ∈ primesIoc P y, (1 / p : ℝ))
    (hsmallTilt : (1 + 4 * eta) * x / (∑ p ∈ primesIoc P y, (1 / p : ℝ)) ≤ eta)
    (hbaseline : A ^ 2 * (∑ p ∈ primesIoc P y, (1 / p : ℝ)) ≤ x ^ 2)
    (hlargeA : 6 ≤ eta ^ 2 * A ^ 2)
    (habsorbA : 4 * Real.log 2 ≤ eps * A ^ 2) :
    Real.exp (-((1 + eps) * x ^ 2 /
        (2 * ∑ p ∈ primesIoc P y, (1 / p : ℝ)))) ≤
      NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass
        (Finset.univ : Finset
          (Fin (Fintype.card (primesIoc P y)) × Fin J))
        (fun z ↦ 1 / (((primeIndexEquiv P y) z.1 : ℕ) : ℝ))
        {S | (∑ p ∈ primesIoc P y, (1 / p : ℝ)) + x ≤
          ((S ∩ shiftArrayColumn (Fintype.card (primesIoc P y)) J j).card : ℝ)} := by
  apply multiShiftColumnMass_ge_moderate j hP hPy heps heta0 heta1 hetaEps hmean hx
    hsquareMass hsmallTilt
  · have hprod : 0 ≤ (eta ^ 2 * A ^ 2 - 6) *
        (∑ p ∈ primesIoc P y, (1 / p : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hlargeA) hmean.le
    nlinarith
  · have hprod : 0 ≤ (eps * A ^ 2 - 4 * Real.log 2) *
        (∑ p ∈ primesIoc P y, (1 / p : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr habsorbA) hmean.le
    nlinarith

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

/-- The deterministic inclusion used in Step 3.  On active columns, a threshold-sized prime set
beats `T` by the prime-chain bound.  Inactive columns receive the impossible threshold
`card (primesIoc P y) + 1`, allowing the factored all-column model theorem to be used unchanged. -/
theorem low_shiftedVarianceMass_pattern_noHeavy
    (v : ℕ → ℝ) (hv0 : ∀ d, 0 ≤ v d) (c c₀ : ℝ)
    {P y n M b j₀ J : ℕ} {T : ℝ} (threshold : Fin J → ℕ)
    (hb : 1 ≤ b) (hnM : ∀ j : Fin J, n + j.val + 1 ≤ M) (hP : 1 ≤ P)
    (hPlog : 1 ≤ Real.log (Real.log (P + 1))) (hc₀ : 0 ≤ c₀)
    (hv : ∀ d : ℕ, 2 ≤ d → c₀ * subpowerWeight c d ≤ v d)
    (hthreshold : ∀ j : Fin J, j₀ ≤ j.val + 1 → 1 ≤ threshold j)
    (hscalar : ∀ j : Fin J, j₀ ≤ j.val + 1 →
      T * (b : ℝ) ^ (2 * (j.val + 1)) <
        (((2 ^ (threshold j - 1) : ℕ) : ℝ) * (c₀ * subpowerWeight c M)))
    (hmass : shiftedVarianceMass v b j₀ J P n ≤ T) :
    ∀ j : Fin J, (multiShiftPattern P y J n j).card <
      if j₀ ≤ j.val + 1 then threshold j else (primesIoc P y).card + 1 := by
  intro j
  split_ifs with hj
  · by_contra hnot
    have hcard : threshold j ≤ (multiShiftPattern P y J n j).card := by omega
    have hQ : 1 ≤ (multiShiftPattern P y J n j).card :=
      (hthreshold j hj).trans hcard
    have hpowNat : 2 ^ (threshold j - 1) ≤
        2 ^ ((multiShiftPattern P y J n j).card - 1) := by
      exact Nat.pow_le_pow_right (by omega) (Nat.sub_le_sub_right hcard 1)
    have hpow : ((2 ^ (threshold j - 1) : ℕ) : ℝ) ≤
        ((2 ^ ((multiShiftPattern P y J n j).card - 1) : ℕ) : ℝ) := by
      exact_mod_cast hpowNat
    have hweight : 0 ≤ c₀ * subpowerWeight c M :=
      mul_nonneg hc₀ (subpowerWeight_nonneg c M)
    have hscalar' : T * (b : ℝ) ^ (2 * (j.val + 1)) <
        (((2 ^ ((multiShiftPattern P y J n j).card - 1) : ℕ) : ℝ) *
          (c₀ * subpowerWeight c M)) :=
      (hscalar j hj).trans_le (mul_le_mul_of_nonneg_right hpow hweight)
    have hgt := shiftedVarianceMass_gt_of_heavyColumn v hv0 c c₀ j hb hj
      (hnM j) hP hPlog hc₀ hv hQ hscalar'
    linarith
  · have hsubset : multiShiftPattern P y J n j ⊆ primesIoc P y := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr hp'.2, (Nat.mem_primeFactors.mp hp'.1).1⟩
    have hcard := Finset.card_le_card hsubset
    omega

open Classical in
/-- A generic finite total-variation transfer.  Once the deterministic bad set is contained in a
model event, the absolute TV estimate bounds its density by the model mass plus the TV error. -/
theorem low_shiftedVarianceMass_density_le_model
    (v : ℕ → ℝ) {P y J N b j₀ : ℕ} {T E : ℝ}
    (A : Set (Fin J → Finset ℕ)) (hN : 0 < N)
    (hdet : ∀ n ∈ Finset.Icc 1 N, shiftedVarianceMass v b j₀ J P n ≤ T →
      multiShiftPattern P y J n ∈ A)
    (hTV : |(((Finset.Icc 1 N).filter (fun n ↦ multiShiftPattern P y J n ∈ A)).card : ℝ) /
          N - multiShiftMass P y J A| ≤ E) :
    (((Finset.Icc 1 N).filter (fun n ↦
        shiftedVarianceMass v b j₀ J P n ≤ T)).card : ℝ) / N ≤
      multiShiftMass P y J A + E := by
  classical
  have hsubset :
      (Finset.Icc 1 N).filter (fun n ↦ shiftedVarianceMass v b j₀ J P n ≤ T) ⊆
        (Finset.Icc 1 N).filter (fun n ↦ multiShiftPattern P y J n ∈ A) := by
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hdet n hn.1 hn.2⟩
  have hcard :
      (((Finset.Icc 1 N).filter (fun n ↦
        shiftedVarianceMass v b j₀ J P n ≤ T)).card : ℝ) ≤
      (((Finset.Icc 1 N).filter (fun n ↦ multiShiftPattern P y J n ∈ A)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hratio := div_le_div_of_nonneg_right hcard hNreal.le
  have hupper :
      (((Finset.Icc 1 N).filter (fun n ↦ multiShiftPattern P y J n ∈ A)).card : ℝ) /
          N ≤ multiShiftMass P y J A + E := by
    have := (le_abs_self ((((Finset.Icc 1 N).filter
      (fun n ↦ multiShiftPattern P y J n ∈ A)).card : ℝ) / N -
        multiShiftMass P y J A)).trans hTV
    linarith
  exact hratio.trans hupper

/-! ### The multishift schedule -/

/-- If `x` is large enough, flooring `exp x` loses at most a factor of two.  This
variable-exponent version of the fixed-power cutoff estimate in
`CoefmassErdosBorweinEndpointKub` is the basic adapter for the multishift cutoff. -/
theorem natFloor_exp_log_bounds {x : ℝ} (hx : 2 * Real.log 2 ≤ x) :
    let z := ⌊Real.exp x⌋₊
    2 ≤ z ∧
      x / 2 ≤ Real.log z ∧ Real.log z ≤ x ∧
      Real.log x - Real.log 2 ≤ Real.log (Real.log z) ∧
      Real.log (Real.log z) ≤ Real.log x := by
  let z : ℕ := ⌊Real.exp x⌋₊
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hexpOne : 1 ≤ Real.exp x := Real.one_le_exp hx0.le
  have hhalf : Real.exp x / 2 ≤ (z : ℝ) :=
    NormalNumbers.ErdosBorweinEndpointKub.half_le_natFloor hexpOne
  have hzTwoReal : (2 : ℝ) ≤ z := by
    calc
      (2 : ℝ) ≤ Real.exp x / 2 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
        calc
          (2 : ℝ) * 2 = 4 := by norm_num
          _ = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
          _ = Real.exp (2 * Real.log 2) := by
            congr 1
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
            norm_num
          _ ≤ Real.exp x := Real.exp_le_exp.mpr hx
      _ ≤ z := hhalf
  have hzTwo : 2 ≤ z := by exact_mod_cast hzTwoReal
  have hz0 : (0 : ℝ) < z := by positivity
  have hlogLower : x / 2 ≤ Real.log z := by
    calc
      x / 2 ≤ x - Real.log 2 := by linarith
      _ = Real.log (Real.exp x / 2) := by
        rw [Real.log_div (Real.exp_ne_zero x) (by norm_num), Real.log_exp]
      _ ≤ Real.log z := Real.log_le_log (by positivity) hhalf
  have hfloorUpper : (z : ℝ) ≤ Real.exp x := Nat.floor_le (Real.exp_pos x).le
  have hlogUpper : Real.log z ≤ x := by
    simpa only [Real.log_exp] using Real.log_le_log hz0 hfloorUpper
  have hxhalf0 : 0 < x / 2 := by positivity
  have hlogz0 : 0 < Real.log z := hxhalf0.trans_le hlogLower
  refine ⟨hzTwo, hlogLower, hlogUpper, ?_, ?_⟩
  · calc
      Real.log x - Real.log 2 = Real.log (x / 2) := by
        rw [Real.log_div hx0.ne' (by norm_num)]
      _ ≤ Real.log (Real.log z) := Real.log_le_log hxhalf0 hlogLower
  · exact Real.log_le_log hlogz0 hlogUpper

/-- The number of shifts used in the final application of Step 1'. -/
noncomputable def multiShiftScheduleJ (N : ℕ) : ℕ :=
  ⌈Real.sqrt (Real.log (Real.log N))⌉₊

/-- The real sieve depth `u = J (log log log N)^3`. -/
noncomputable def multiShiftScheduleU (N : ℕ) : ℝ :=
  (multiShiftScheduleJ N : ℝ) * (Real.log (Real.log (Real.log N))) ^ 3

/-- The variable prime cutoff `y = ⌊exp(log N / u)⌋`. -/
noncomputable def multiShiftCutoffY (N : ℕ) : ℕ :=
  ⌊Real.exp (Real.log N / multiShiftScheduleU N)⌋₊

/-- The reciprocal-prime mean on the scheduled block. -/
noncomputable def multiShiftPrimeMean (N : ℕ) : ℝ :=
  ∑ p ∈ primesIoc (collisionCutoff N) (multiShiftCutoffY N), (1 / p : ℝ)

/-- The exact square-root penalty occurring in `subpowerWeight c (2 * N)`.  Keeping the
`2 * N` expression exact makes the deterministic heavy-column calculation algebraic; its
asymptotic replacement by `sqrt (c * L * log L)` is postponed to the probability estimate. -/
noncomputable def multiShiftSubpowerPenalty (c : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt (c * Real.log (Real.log ((2 * N : ℕ) : ℝ)) *
    Real.log (Real.log (Real.log ((2 * N : ℕ) : ℝ))))

/-- The heavy-column threshold.  Besides the exact subpower penalty it contains a fixed
square-root baseline for the tilted-Chebyshev estimate, the exact cost of the shifted factor
`b ^ (2 * (j + 1))`, and an `8 * log L` buffer for the cutoff and Mertens losses. -/
noncomputable def multiShiftThreshold (c A : ℝ) (b N j : ℕ) : ℕ :=
  ⌈multiShiftPrimeMean N + multiShiftSubpowerPenalty c N +
      A * Real.sqrt (multiShiftPrimeMean N) +
      (((2 * (j + 1) : ℕ) : ℝ) * Real.log b / Real.log 2) +
      8 * Real.log (Real.log (Real.log N))⌉₊

/-- The real displacement used to compare the integer heavy-column threshold with the
moderate-deviation event.  The final `+ 1` absorbs the ceiling in `multiShiftThreshold`. -/
noncomputable def multiShiftDeviation (c A : ℝ) (b N j : ℕ) : ℝ :=
  multiShiftSubpowerPenalty c N +
    A * Real.sqrt (multiShiftPrimeMean N) +
    (((2 * (j + 1) : ℕ) : ℝ) * Real.log b / Real.log 2) +
    8 * Real.log (Real.log (Real.log N)) + 1

/-- The square-root schedule satisfies the upper bound required by Step 1'. -/
theorem eventually_multiShiftScheduleJ_le_log_log :
    ∀ᶠ N : ℕ in atTop,
      (multiShiftScheduleJ N : ℝ) ≤ Real.log (Real.log N) := by
  have hLtop : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hLtop.eventually_ge_atTop 4] with N hL
  have hceil : (multiShiftScheduleJ N : ℝ) <
      Real.sqrt (Real.log (Real.log N)) + 1 := by
    exact Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  have hsqrtSq : Real.sqrt (Real.log (Real.log N)) ^ 2 =
      Real.log (Real.log N) := Real.sq_sqrt (by linarith)
  nlinarith [Real.sqrt_nonneg (Real.log (Real.log N))]

/-- In particular, the number of available shifts tends to infinity. -/
theorem tendsto_multiShiftScheduleJ :
    Tendsto (fun N : ℕ ↦ (multiShiftScheduleJ N : ℝ)) atTop atTop := by
  have hLtop : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hsqrtTop := Real.tendsto_sqrt_atTop.comp hLtop
  refine tendsto_atTop.2 fun R ↦ ?_
  filter_upwards [hsqrtTop.eventually_ge_atTop R] with N hR
  exact hR.trans (Nat.le_ceil _)

/-- The sieve depth is positive and negligible compared with `sqrt (log N)`.  The deliberately
coarse proof bounds it by `(log log N)^4` and uses `(log x)^8 = o(x)`. -/
theorem eventually_multiShiftScheduleU_bounds :
    ∀ᶠ N : ℕ in atTop,
      0 < multiShiftScheduleU N ∧
        multiShiftScheduleU N ≤ Real.sqrt (Real.log N) := by
  have htTop : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLTop : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp htTop
  have hsmallReal := (Real.isLittleO_pow_log_id_atTop (n := 8)).bound one_pos
  have hsmall := htTop.eventually hsmallReal
  filter_upwards [eventually_multiShiftScheduleJ_le_log_log,
      htTop.eventually_ge_atTop 2, hLTop.eventually_ge_atTop 2, hsmall] with
      N hJL ht hL hsmall
  let L : ℝ := Real.log (Real.log N)
  have ht0 : 0 < Real.log (N : ℝ) := by linarith
  have hL0 : 0 < L := by simpa only [L] using (show 0 < Real.log (Real.log N) by linarith)
  have hlogL0 : 0 < Real.log L := Real.log_pos (by linarith)
  have hJ1 : 1 ≤ multiShiftScheduleJ N := by
    apply Nat.one_le_ceil_iff.mpr
    exact Real.sqrt_pos.2 hL0
  have hJ0 : (0 : ℝ) < multiShiftScheduleJ N := by exact_mod_cast hJ1
  have hlogL_le : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
  have hU0 : 0 < multiShiftScheduleU N := by
    rw [multiShiftScheduleU]
    change 0 < (multiShiftScheduleJ N : ℝ) * (Real.log L) ^ 3
    positivity
  have hUle : multiShiftScheduleU N ≤ L ^ 4 := by
    rw [multiShiftScheduleU]
    change (multiShiftScheduleJ N : ℝ) * (Real.log L) ^ 3 ≤ L ^ 4
    calc
      (multiShiftScheduleJ N : ℝ) * (Real.log L) ^ 3 ≤
          L * L ^ 3 := by gcongr
      _ = L ^ 4 := by ring
  have hL8 : L ^ 8 ≤ Real.log N := by
    have hsmall' : |Real.log (Real.log N) ^ 8| ≤ |Real.log N| := by
      simpa only [Real.norm_eq_abs, one_mul, id] using hsmall
    rw [abs_of_nonneg (pow_nonneg hL0.le _), abs_of_pos ht0] at hsmall'
    simpa only [L] using hsmall'
  have hUsq : (multiShiftScheduleU N) ^ 2 ≤ Real.log N := by
    calc
      (multiShiftScheduleU N) ^ 2 ≤ (L ^ 4) ^ 2 :=
        (sq_le_sq₀ hU0.le (pow_nonneg hL0.le 4)).2 hUle
      _ = L ^ 8 := by ring
      _ ≤ Real.log N := hL8
  have hsqrtSq : Real.sqrt (Real.log N) ^ 2 = Real.log N :=
    Real.sq_sqrt ht0.le
  refine ⟨hU0, ?_⟩
  nlinarith [Real.sqrt_nonneg (Real.log N)]

/-- The variable cutoff lies between the collision cutoff and `N`, and its two logarithms are
controlled explicitly by `x = log N / u`.  These are exactly the geometric side conditions needed
by the sieve hypothesis and by Mertens. -/
theorem eventually_multiShiftCutoffY_bounds :
    ∀ᶠ N : ℕ in atTop,
      let x := Real.log N / multiShiftScheduleU N
      collisionCutoff N ≤ multiShiftCutoffY N ∧
        multiShiftCutoffY N ≤ N ∧ 2 ≤ multiShiftCutoffY N ∧
        x / 2 ≤ Real.log (multiShiftCutoffY N) ∧
        Real.log (multiShiftCutoffY N) ≤ x ∧
        Real.log x - Real.log 2 ≤ Real.log (Real.log (multiShiftCutoffY N)) ∧
        Real.log (Real.log (multiShiftCutoffY N)) ≤ Real.log x := by
  have htTop : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLTop : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp htTop
  have hcollision :=
    NormalNumbers.ErdosBorweinEndpointKub.eventually_collisionCutoff_le_natFloor_exp_log_rpow_add
      0 (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [eventually_multiShiftScheduleU_bounds,
      eventually_multiShiftScheduleJ_le_log_log, htTop.eventually_ge_atTop 16,
      hLTop.eventually_ge_atTop 3, hcollision] with N hU hJL ht hL hcollision
  let L : ℝ := Real.log (Real.log N)
  let U : ℝ := multiShiftScheduleU N
  let x : ℝ := Real.log N / U
  have ht0 : 0 < Real.log (N : ℝ) := by linarith
  have hsqrt0 : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.2 ht0
  have hsqrtSq : Real.sqrt (Real.log N) ^ 2 = Real.log N :=
    Real.sq_sqrt ht0.le
  have hL0 : 0 < L := by simpa only [L] using (show 0 < Real.log (Real.log N) by linarith)
  have hlogL1 : 1 ≤ Real.log L := by
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) Real.exp_one_lt_three.le
      _ ≤ Real.log L := Real.log_le_log (by norm_num) (by simpa only [L] using hL)
  have hJ1 : 1 ≤ multiShiftScheduleJ N := by
    apply Nat.one_le_ceil_iff.mpr
    exact Real.sqrt_pos.2 hL0
  have hU1 : 1 ≤ U := by
    dsimp [U]
    rw [multiShiftScheduleU]
    change (1 : ℝ) ≤ (multiShiftScheduleJ N : ℝ) * (Real.log L) ^ 3
    have hJ1real : (1 : ℝ) ≤ multiShiftScheduleJ N := by exact_mod_cast hJ1
    have hlogpow : (1 : ℝ) ≤ (Real.log L) ^ 3 := one_le_pow₀ hlogL1
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (multiShiftScheduleJ N : ℝ) * (Real.log L) ^ 3 :=
        mul_le_mul hJ1real hlogpow zero_le_one (zero_le_one.trans hJ1real)
  have hxLower : Real.sqrt (Real.log N) ≤ x := by
    dsimp [x, U]
    rw [le_div_iff₀ hU.1]
    have hmul : Real.sqrt (Real.log N) * multiShiftScheduleU N ≤
        Real.sqrt (Real.log N) * Real.sqrt (Real.log N) :=
      mul_le_mul_of_nonneg_left hU.2 (Real.sqrt_nonneg _)
    nlinarith
  have hxUpper : x ≤ Real.log N := by
    dsimp [x, U]
    exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hU1)).2
      (by nlinarith [ht0.le])
  have hxLarge : 2 * Real.log 2 ≤ x := by
    have hlog2lt : Real.log (2 : ℝ) < 1 := Real.log_two_lt_d9.trans (by norm_num)
    nlinarith [Real.sqrt_nonneg (Real.log N)]
  have hfloor := natFloor_exp_log_bounds hxLarge
  change 2 ≤ multiShiftCutoffY N ∧
      x / 2 ≤ Real.log (multiShiftCutoffY N) ∧
      Real.log (multiShiftCutoffY N) ≤ x ∧
      Real.log x - Real.log 2 ≤ Real.log (Real.log (multiShiftCutoffY N)) ∧
      Real.log (Real.log (multiShiftCutoffY N)) ≤ Real.log x at hfloor
  have hfixedDynamic :
      ⌊Real.exp (Real.rpow (Real.log N) (1 / 2 : ℝ))⌋₊ ≤ multiShiftCutoffY N := by
    apply Nat.floor_le_floor
    apply Real.exp_le_exp.mpr
    calc
      Real.rpow (Real.log N) (1 / 2 : ℝ) = Real.sqrt (Real.log N) :=
        (Real.sqrt_eq_rpow _).symm
      _ ≤ x := hxLower
  have hcollisionY : collisionCutoff N ≤ multiShiftCutoffY N := by
    have hcollision' : collisionCutoff N ≤
        ⌊Real.exp (Real.rpow (Real.log N) (1 / 2 : ℝ))⌋₊ := by
      simpa using hcollision
    exact hcollision'.trans hfixedDynamic
  have hyN : multiShiftCutoffY N ≤ N := by
    have hNnat : 0 < N := by
      by_contra hnot
      have : N = 0 := Nat.eq_zero_of_not_pos hnot
      subst N
      norm_num at ht
    have hyReal : (multiShiftCutoffY N : ℝ) ≤ N := by
      calc
        (multiShiftCutoffY N : ℝ) ≤ Real.exp x :=
          Nat.floor_le (Real.exp_pos x).le
        _ ≤ Real.exp (Real.log N) := Real.exp_le_exp.mpr hxUpper
        _ = N := Real.exp_log (by exact_mod_cast hNnat)
    exact_mod_cast hyReal
  exact ⟨hcollisionY, hyN, hfloor⟩

/-- The logarithm of the sieve depth costs at most four logarithms of `L = log log N`. -/
theorem eventually_log_multiShiftScheduleU_le :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ multiShiftScheduleU N ∧
        Real.log (multiShiftScheduleU N) ≤
          4 * Real.log (Real.log (Real.log N)) := by
  have hLTop : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_multiShiftScheduleJ_le_log_log,
      hLTop.eventually_ge_atTop 3] with N hJL hL
  let L : ℝ := Real.log (Real.log N)
  have hL0 : 0 < L := by simpa only [L] using (show 0 < Real.log (Real.log N) by linarith)
  have hlogL1 : 1 ≤ Real.log L := by
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) Real.exp_one_lt_three.le
      _ ≤ Real.log L := Real.log_le_log (by norm_num) (by simpa only [L] using hL)
  have hJ1 : 1 ≤ multiShiftScheduleJ N := by
    apply Nat.one_le_ceil_iff.mpr
    exact Real.sqrt_pos.2 hL0
  have hU1 : 1 ≤ multiShiftScheduleU N := by
    rw [multiShiftScheduleU]
    change (1 : ℝ) ≤ (multiShiftScheduleJ N : ℝ) * (Real.log L) ^ 3
    have hJ1real : (1 : ℝ) ≤ multiShiftScheduleJ N := by exact_mod_cast hJ1
    have hlogpow : (1 : ℝ) ≤ (Real.log L) ^ 3 := one_le_pow₀ hlogL1
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (multiShiftScheduleJ N : ℝ) * (Real.log L) ^ 3 :=
        mul_le_mul hJ1real hlogpow zero_le_one (zero_le_one.trans hJ1real)
  have hlogL_le : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
  have hUle : multiShiftScheduleU N ≤ L ^ 4 := by
    rw [multiShiftScheduleU]
    change (multiShiftScheduleJ N : ℝ) * (Real.log L) ^ 3 ≤ L ^ 4
    calc
      (multiShiftScheduleJ N : ℝ) * (Real.log L) ^ 3 ≤ L * L ^ 3 := by gcongr
      _ = L ^ 4 := by ring
  refine ⟨hU1, ?_⟩
  calc
    Real.log (multiShiftScheduleU N) ≤ Real.log (L ^ 4) :=
      Real.log_le_log (lt_of_lt_of_le zero_lt_one hU1) hUle
    _ = 4 * Real.log L := by rw [Real.log_pow]; norm_num

/-- Before the bounded Mertens error is inserted, the reciprocal-prime block has logarithmic
length `L - O(log L)`. -/
theorem eventually_multiShiftLogBlock_bounds :
    ∀ᶠ N : ℕ in atTop,
      let L := Real.log (Real.log N)
      2 ≤ collisionCutoff N ∧
        L - 6 * Real.log L - Real.log 2 ≤
          Real.log (Real.log (multiShiftCutoffY N)) -
            Real.log (Real.log (collisionCutoff N)) ∧
        Real.log (Real.log (multiShiftCutoffY N)) -
            Real.log (Real.log (collisionCutoff N)) ≤ L + Real.log 2 := by
  have htTop : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLTop : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp htTop
  filter_upwards [eventually_multiShiftCutoffY_bounds,
      eventually_log_multiShiftScheduleU_le, htTop.eventually_ge_atTop 2,
      hLTop.eventually_ge_atTop 3] with N hy hU ht hL
  let L : ℝ := Real.log (Real.log N)
  let U : ℝ := multiShiftScheduleU N
  let x : ℝ := Real.log N / U
  have ht0 : 0 < Real.log (N : ℝ) := by linarith
  have hL0 : 0 < L := by simpa only [L] using (show 0 < Real.log (Real.log N) by linarith)
  have hlogL0 : 0 < Real.log L := Real.log_pos (by linarith)
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU.1
  have hx0 : 0 < x := div_pos ht0 hU0
  have hlogx : Real.log x = L - Real.log U := by
    dsimp [x]
    rw [Real.log_div ht0.ne' hU0.ne']
  have hcollisionFloor := natFloor_exp_log_bounds
    (x := L ^ 2) (show 2 * Real.log 2 ≤ L ^ 2 by
      have hlog2lt : Real.log (2 : ℝ) < 1 := Real.log_two_lt_d9.trans (by norm_num)
      nlinarith)
  change 2 ≤ collisionCutoff N ∧
      L ^ 2 / 2 ≤ Real.log (collisionCutoff N) ∧
      Real.log (collisionCutoff N) ≤ L ^ 2 ∧
      Real.log (L ^ 2) - Real.log 2 ≤ Real.log (Real.log (collisionCutoff N)) ∧
      Real.log (Real.log (collisionCutoff N)) ≤ Real.log (L ^ 2) at hcollisionFloor
  have hlogLsq : Real.log (L ^ 2) = 2 * Real.log L := by
    rw [Real.log_pow]
    norm_num
  have hyLower := hy.2.2.2.2.2.1
  have hyUpper := hy.2.2.2.2.2.2
  change Real.log x - Real.log 2 ≤ Real.log (Real.log (multiShiftCutoffY N)) at hyLower
  change Real.log (Real.log (multiShiftCutoffY N)) ≤ Real.log x at hyUpper
  have hlogU : Real.log U ≤ 4 * Real.log L := by
    simpa only [U, L] using hU.2
  refine ⟨hcollisionFloor.1, ?_, ?_⟩
  · rw [hlogx] at hyLower
    rw [hlogLsq] at hcollisionFloor
    linarith [hcollisionFloor.2.2.2.2]
  · rw [hlogx] at hyUpper
    rw [hlogLsq] at hcollisionFloor
    have hlogU0 : 0 ≤ Real.log U := Real.log_nonneg hU.1
    linarith [hcollisionFloor.2.2.2.1]

/-- The reciprocal-prime mean on the variable block is comparable with `L = log log N`.
This is the coarse estimate needed by all moderate-deviation side conditions. -/
theorem eventually_multiShiftPrimeMean_bounds :
    ∀ᶠ N : ℕ in atTop,
      let L := Real.log (Real.log N)
      L / 2 ≤ ∑ p ∈ primesIoc (collisionCutoff N) (multiShiftCutoffY N), (1 / p : ℝ) ∧
        ∑ p ∈ primesIoc (collisionCutoff N) (multiShiftCutoffY N), (1 / p : ℝ) ≤ 2 * L := by
  obtain ⟨C, hC0, hMertens⟩ := mertens_primesIoc_bound
  have hLTop : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlogSmallReal := (Real.isLittleO_log_id_atTop.bound
    (show (0 : ℝ) < 1 / 24 by norm_num))
  have hlogSmall := hLTop.eventually hlogSmallReal
  filter_upwards [eventually_multiShiftCutoffY_bounds,
      eventually_multiShiftLogBlock_bounds, hlogSmall,
      hLTop.eventually_ge_atTop (4 * (Real.log 2 + 2 * C + 1))] with
      N hy hblock hlogSmall hLlarge
  let L : ℝ := Real.log (Real.log N)
  let mean : ℝ := ∑ p ∈ primesIoc (collisionCutoff N) (multiShiftCutoffY N), (1 / p : ℝ)
  have hL0 : 0 < L := by
    have hconst0 : 0 < 4 * (Real.log 2 + 2 * C + 1) := by positivity
    exact hconst0.trans_le (by simpa only [L] using hLlarge)
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by
    have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have : 4 ≤ 4 * (Real.log 2 + 2 * C + 1) := by nlinarith
    linarith)
  have hlogSmall' : Real.log L ≤ (1 / 24 : ℝ) * L := by
    have := hlogSmall
    simpa only [L, Real.norm_eq_abs, abs_of_nonneg hlogL0, abs_of_pos hL0, id] using this
  have hconst : Real.log 2 + 2 * C ≤ L / 4 := by
    change 4 * (Real.log 2 + 2 * C + 1) ≤ L at hLlarge
    nlinarith
  have hP2 : 2 ≤ collisionCutoff N := hblock.1
  have hPy : collisionCutoff N ≤ multiShiftCutoffY N := hy.1
  have hM := hMertens (collisionCutoff N) (multiShiftCutoffY N) hP2 hPy
  change |mean - (Real.log (Real.log (multiShiftCutoffY N)) -
      Real.log (Real.log (collisionCutoff N)))| ≤ 2 * C at hM
  have hmainLower := hblock.2.1
  have hmainUpper := hblock.2.2
  change L - 6 * Real.log L - Real.log 2 ≤
      Real.log (Real.log (multiShiftCutoffY N)) -
        Real.log (Real.log (collisionCutoff N)) at hmainLower
  change Real.log (Real.log (multiShiftCutoffY N)) -
      Real.log (Real.log (collisionCutoff N)) ≤ L + Real.log 2 at hmainUpper
  have hMlo := (abs_le.mp hM).1
  have hMhi := (abs_le.mp hM).2
  refine ⟨?_, ?_⟩
  · nlinarith
  · nlinarith

/-- The sharp lower estimate retained from Mertens.  The coarse comparison
`multiShiftPrimeMean N ≥ L / 2` is enough for side conditions, but the final exponent needs the
full `L - O(log L)` main term. -/
theorem eventually_multiShiftPrimeMean_lower :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      let L := Real.log (Real.log N)
      L - 6 * Real.log L - C ≤ multiShiftPrimeMean N := by
  obtain ⟨C, hC0, hMertens⟩ := mertens_primesIoc_bound
  refine ⟨Real.log 2 + 2 * C, by positivity, ?_⟩
  filter_upwards [eventually_multiShiftCutoffY_bounds,
      eventually_multiShiftLogBlock_bounds] with N hy hblock
  let L : ℝ := Real.log (Real.log N)
  have hM := hMertens (collisionCutoff N) (multiShiftCutoffY N)
    hblock.1 hy.1
  change |multiShiftPrimeMean N -
      (Real.log (Real.log (multiShiftCutoffY N)) -
        Real.log (Real.log (collisionCutoff N)))| ≤ 2 * C at hM
  have hmain := hblock.2.1
  change L - 6 * Real.log L - Real.log 2 ≤
      Real.log (Real.log (multiShiftCutoffY N)) -
        Real.log (Real.log (collisionCutoff N)) at hmain
  linarith [abs_le.mp hM |>.1]

/-- Replacing `N` by `2 * N` changes `log log N` by at most `log 2`, eventually. -/
theorem eventually_log_log_two_mul_le :
    ∀ᶠ N : ℕ in atTop,
      Real.log (Real.log ((2 * N : ℕ) : ℝ)) ≤
        Real.log (Real.log N) + Real.log 2 := by
  have htTop : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [htTop.eventually_ge_atTop (Real.log 2)] with N hlogN
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogN0 : 0 < Real.log (N : ℝ) := hlog2.trans_le hlogN
  have hNnat : 0 < N := by
    by_contra hnot
    have : N = 0 := Nat.eq_zero_of_not_pos hnot
    subst N
    norm_num at hlogN0
  have hN0 : (0 : ℝ) < N := by
    exact_mod_cast hNnat
  have hlogTwoN0 : 0 < Real.log (((2 * N : ℕ) : ℝ)) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hN0.ne']
    linarith
  have hinner : Real.log (((2 * N : ℕ) : ℝ)) ≤ 2 * Real.log N := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hN0.ne']
    linarith
  calc
    Real.log (Real.log ((2 * N : ℕ) : ℝ)) ≤ Real.log (2 * Real.log N) :=
      Real.log_le_log hlogTwoN0 hinner
    _ = Real.log (Real.log N) + Real.log 2 := by
      rw [Real.log_mul (by norm_num) hlogN0.ne']
      ring_nf

/-- After the `8 * log L` threshold buffer, the Mertens loss and the exact global-cutoff
weight loss leave a quantity tending to infinity.  This is the analytic core of the
deterministic heavy-column inequality. -/
theorem tendsto_multiShiftBufferedMean :
    Tendsto (fun N : ℕ ↦ multiShiftPrimeMean N +
      8 * Real.log (Real.log (Real.log N)) -
        Real.log (Real.log ((2 * N : ℕ) : ℝ))) atTop atTop := by
  obtain ⟨C, hC0, hmean⟩ := eventually_multiShiftPrimeMean_lower
  have hLTop : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlogLTop : Tendsto
      (fun N : ℕ ↦ Real.log (Real.log (Real.log (N : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLTop
  have hmajor : Tendsto (fun N : ℕ ↦
      2 * Real.log (Real.log (Real.log N)) - C - Real.log 2) atTop atTop := by
    have hmul := hlogLTop.const_mul_atTop (show (0 : ℝ) < 2 by norm_num)
    simpa only [sub_eq_add_neg, add_assoc] using
      tendsto_atTop_add_const_right atTop (-C - Real.log 2) hmul
  refine Filter.tendsto_atTop_mono' atTop ?_ hmajor
  filter_upwards [hmean, eventually_log_log_two_mul_le] with N hmeanN htwo
  let L : ℝ := Real.log (Real.log N)
  change L - 6 * Real.log L - C ≤ multiShiftPrimeMean N at hmeanN
  change Real.log (Real.log ((2 * N : ℕ) : ℝ)) ≤ L + Real.log 2 at htwo
  change 2 * Real.log L - C - Real.log 2 ≤
    multiShiftPrimeMean N + 8 * Real.log L -
      Real.log (Real.log ((2 * N : ℕ) : ℝ))
  linarith

/-- Uniform deterministic threshold calculation.  A column reaching `multiShiftThreshold`
beats the scalar premise of `shiftedVarianceMass_gt_of_heavyColumn`, with the global cutoff
`M = 2 * N`.  The proof is uniform in the shift index: the threshold contains exactly the
logarithm of the factor `b ^ (2 * (j + 1))`. -/
theorem eventually_multiShiftThreshold_scalar
    (c A c₀ T : ℝ) (hA : 0 ≤ A) (hc₀ : 0 < c₀) (b : ℕ) (hb : 2 ≤ b) :
    ∀ᶠ N : ℕ in atTop, ∀ j : ℕ,
      T * (b : ℝ) ^ (2 * (j + 1)) <
        (((2 ^ (multiShiftThreshold c A b N j - 1) : ℕ) : ℝ) *
          (c₀ * subpowerWeight c (2 * N))) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hbuffer := tendsto_multiShiftBufferedMean
  have hscaled : Tendsto (fun N : ℕ ↦ Real.log 2 *
      (multiShiftPrimeMean N + 8 * Real.log (Real.log (Real.log N)) -
        Real.log (Real.log ((2 * N : ℕ) : ℝ)) - 1)) atTop atTop := by
    have hmul := hbuffer.const_mul_atTop hlog2
    have hadd := tendsto_atTop_add_const_right atTop (-Real.log 2) hmul
    convert hadd using 1
    ext N
    ring
  have hfactorTop : Tendsto (fun N : ℕ ↦ c₀ * Real.exp (Real.log 2 *
      (multiShiftPrimeMean N + 8 * Real.log (Real.log (Real.log N)) -
        Real.log (Real.log ((2 * N : ℕ) : ℝ)) - 1))) atTop atTop :=
    (Real.tendsto_exp_atTop.comp hscaled).const_mul_atTop hc₀
  have htTop : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLTop : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp htTop
  filter_upwards [hfactorTop.eventually_gt_atTop T,
      eventually_multiShiftPrimeMean_bounds,
      htTop.eventually_ge_atTop (Real.log 2), hLTop.eventually_ge_atTop 2] with
      N hfactor hmean hlogN hL
  intro j
  let L : ℝ := Real.log (Real.log N)
  let mean : ℝ := multiShiftPrimeMean N
  let psi : ℝ := multiShiftSubpowerPenalty c N
  let shift : ℝ := (((2 * (j + 1) : ℕ) : ℝ) * Real.log b / Real.log 2)
  let threshold : ℕ := multiShiftThreshold c A b N j
  have hL2 : 2 ≤ L := by simpa only [L] using hL
  have hL0 : 0 < L := by linarith
  have hlogL0 : 0 < Real.log L := Real.log_pos (by linarith)
  have hmeanLower : L / 2 ≤ mean := by
    simpa only [L, mean, multiShiftPrimeMean] using hmean.1
  have hmean0 : 0 < mean := lt_of_lt_of_le (by positivity) hmeanLower
  have hpsi0 : 0 ≤ psi := by simp only [psi, multiShiftSubpowerPenalty]; positivity
  have hbR : (0 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hb)
  have hlogb0 : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
  have hshift0 : 0 ≤ shift := by dsimp only [shift]; positivity
  have harg0 : 0 < mean + psi + A * Real.sqrt mean + shift + 8 * Real.log L := by
    have hsqrt0 : 0 ≤ Real.sqrt mean := Real.sqrt_nonneg _
    positivity
  have hceil : mean + psi + A * Real.sqrt mean + shift + 8 * Real.log L ≤
      (threshold : ℝ) := by
    simpa only [threshold, multiShiftThreshold, mean, psi, shift, L] using
      (Nat.le_ceil (mean + psi + A * Real.sqrt mean + shift + 8 * Real.log L))
  have hthreshold1 : 1 ≤ threshold := by
    exact Nat.one_le_ceil_iff.mpr harg0
  have hcastSub : ((threshold - 1 : ℕ) : ℝ) = (threshold : ℝ) - 1 := by
    rw [Nat.cast_sub hthreshold1]
    norm_num
  have hpowExponent : Real.log 2 *
      (mean + psi + A * Real.sqrt mean + shift + 8 * Real.log L - 1) ≤
        ((threshold - 1 : ℕ) : ℝ) * Real.log 2 := by
    rw [hcastSub]
    nlinarith
  have htwoPow : (((2 ^ (threshold - 1) : ℕ) : ℝ)) =
      Real.exp (((threshold - 1 : ℕ) : ℝ) * Real.log 2) := by
    calc
      (((2 ^ (threshold - 1) : ℕ) : ℝ)) = (2 : ℝ) ^ (threshold - 1) := by norm_num
      _ = Real.exp (Real.log 2) ^ (threshold - 1) := by rw [Real.exp_log (by norm_num)]
      _ = Real.exp (((threshold - 1 : ℕ) : ℝ) * Real.log 2) := by
        rw [← Real.exp_nat_mul]
  have hpowLower : Real.exp (Real.log 2 *
      (mean + psi + A * Real.sqrt mean + shift + 8 * Real.log L - 1)) ≤
        (((2 ^ (threshold - 1) : ℕ) : ℝ)) := by
    rw [htwoPow]
    exact Real.exp_le_exp.mpr hpowExponent
  have hNnat : 0 < N := by
    by_contra hnot
    have : N = 0 := Nat.eq_zero_of_not_pos hnot
    subst N
    norm_num at hlogN
    linarith
  have hMone : 1 < 2 * N := by omega
  have hlogM0 : 0 < Real.log (((2 * N : ℕ) : ℝ)) :=
    Real.log_pos (by exact_mod_cast hMone)
  have hrpow : Real.rpow (Real.log (((2 * N : ℕ) : ℝ))) (-Real.log 2) =
      Real.exp (Real.log (Real.log ((2 * N : ℕ) : ℝ)) * (-Real.log 2)) := by
    exact Real.rpow_def_of_pos hlogM0 (-Real.log 2)
  have hweight : subpowerWeight c (2 * N) =
      Real.exp (-(Real.log 2) *
        (Real.log (Real.log ((2 * N : ℕ) : ℝ)) + psi)) := by
    rw [subpowerWeight, hrpow]
    simp only [psi, multiShiftSubpowerPenalty]
    rw [← Real.exp_add]
    congr 1
    ring
  have hbpow : (b : ℝ) ^ (2 * (j + 1)) =
      Real.exp (((2 * (j + 1) : ℕ) : ℝ) * Real.log b) := by
    calc
      (b : ℝ) ^ (2 * (j + 1)) = Real.exp (Real.log b) ^ (2 * (j + 1)) := by
        rw [Real.exp_log hbR]
      _ = Real.exp (((2 * (j + 1) : ℕ) : ℝ) * Real.log b) := by
        rw [← Real.exp_nat_mul]
  have hexponent : Real.log 2 *
        (mean + psi + A * Real.sqrt mean + shift + 8 * Real.log L - 1) +
      (-(Real.log 2) *
        (Real.log (Real.log ((2 * N : ℕ) : ℝ)) + psi)) =
      (((2 * (j + 1) : ℕ) : ℝ) * Real.log b) +
        Real.log 2 * (mean + A * Real.sqrt mean + 8 * Real.log L -
          Real.log (Real.log ((2 * N : ℕ) : ℝ)) - 1) := by
    dsimp only [shift]
    field_simp [hlog2.ne']
    ring
  have hlower : (b : ℝ) ^ (2 * (j + 1)) *
        (c₀ * Real.exp (Real.log 2 *
          (mean + A * Real.sqrt mean + 8 * Real.log L -
            Real.log (Real.log ((2 * N : ℕ) : ℝ)) - 1))) ≤
      (((2 ^ (threshold - 1) : ℕ) : ℝ) *
        (c₀ * subpowerWeight c (2 * N))) := by
    calc
      (b : ℝ) ^ (2 * (j + 1)) *
          (c₀ * Real.exp (Real.log 2 *
            (mean + A * Real.sqrt mean + 8 * Real.log L -
              Real.log (Real.log ((2 * N : ℕ) : ℝ)) - 1))) =
        Real.exp (Real.log 2 *
            (mean + psi + A * Real.sqrt mean + shift + 8 * Real.log L - 1)) *
          (c₀ * subpowerWeight c (2 * N)) := by
            rw [hbpow, hweight]
            calc
              Real.exp (((2 * (j + 1) : ℕ) : ℝ) * Real.log b) *
                  (c₀ * Real.exp (Real.log 2 *
                    (mean + A * Real.sqrt mean + 8 * Real.log L -
                      Real.log (Real.log ((2 * N : ℕ) : ℝ)) - 1))) =
                c₀ * Real.exp
                  ((((2 * (j + 1) : ℕ) : ℝ) * Real.log b) +
                    Real.log 2 *
                      (mean + A * Real.sqrt mean + 8 * Real.log L -
                        Real.log (Real.log ((2 * N : ℕ) : ℝ)) - 1)) := by
                    rw [Real.exp_add]
                    ring
              _ = c₀ * Real.exp
                  (Real.log 2 *
                      (mean + psi + A * Real.sqrt mean + shift + 8 * Real.log L - 1) +
                    (-(Real.log 2) *
                      (Real.log (Real.log ((2 * N : ℕ) : ℝ)) + psi))) := by
                    rw [hexponent]
              _ = Real.exp (Real.log 2 *
                    (mean + psi + A * Real.sqrt mean + shift + 8 * Real.log L - 1)) *
                  (c₀ * Real.exp (-(Real.log 2) *
                    (Real.log (Real.log ((2 * N : ℕ) : ℝ)) + psi))) := by
                    rw [Real.exp_add]
                    ring
      _ ≤ (((2 ^ (threshold - 1) : ℕ) : ℝ) *
          (c₀ * subpowerWeight c (2 * N))) := by
        exact mul_le_mul_of_nonneg_right hpowLower
          (mul_nonneg hc₀.le (subpowerWeight_nonneg c (2 * N)))
  have hbaseline : c₀ * Real.exp (Real.log 2 *
      (mean + 8 * Real.log L - Real.log (Real.log ((2 * N : ℕ) : ℝ)) - 1)) ≤
      c₀ * Real.exp (Real.log 2 *
        (mean + A * Real.sqrt mean + 8 * Real.log L -
          Real.log (Real.log ((2 * N : ℕ) : ℝ)) - 1)) := by
    apply mul_le_mul_of_nonneg_left _ hc₀.le
    apply Real.exp_le_exp.mpr
    have hsqrt0 : 0 ≤ Real.sqrt mean := Real.sqrt_nonneg _
    apply mul_le_mul_of_nonneg_left _ hlog2.le
    nlinarith [mul_nonneg hA hsqrt0]
  have hfactor' : T < c₀ * Real.exp (Real.log 2 *
      (mean + 8 * Real.log L - Real.log (Real.log ((2 * N : ℕ) : ℝ)) - 1)) := by
    simpa only [mean, L] using hfactor
  have hfactorA := hfactor'.trans_le hbaseline
  have hbpow0 : 0 < (b : ℝ) ^ (2 * (j + 1)) := by positivity
  calc
    T * (b : ℝ) ^ (2 * (j + 1)) <
        (c₀ * Real.exp (Real.log 2 *
          (mean + A * Real.sqrt mean + 8 * Real.log L -
            Real.log (Real.log ((2 * N : ℕ) : ℝ)) - 1))) *
          (b : ℝ) ^ (2 * (j + 1)) :=
      mul_lt_mul_of_pos_right hfactorA hbpow0
    _ = (b : ℝ) ^ (2 * (j + 1)) *
        (c₀ * Real.exp (Real.log 2 *
          (mean + A * Real.sqrt mean + 8 * Real.log L -
            Real.log (Real.log ((2 * N : ℕ) : ℝ)) - 1))) := by ring
    _ ≤ (((2 ^ (threshold - 1) : ℕ) : ℝ) *
        (c₀ * subpowerWeight c (2 * N))) := hlower
    _ = (((2 ^ (multiShiftThreshold c A b N j - 1) : ℕ) : ℝ) *
        (c₀ * subpowerWeight c (2 * N))) := by rfl

/-- All geometric side conditions for the multishift sieve, apart from its constant-dependent
depth inequality.  Moreover `log N / log y` is trapped between `u` and `2u`. -/
theorem eventually_multiShiftSieveGeometry :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ multiShiftScheduleJ N ∧
        multiShiftScheduleJ N ≤ collisionCutoff N ∧
        2 ≤ multiShiftCutoffY N ∧ multiShiftCutoffY N ≤ N ∧
        multiShiftScheduleU N ≤ Real.log N / Real.log (multiShiftCutoffY N) ∧
        Real.log N / Real.log (multiShiftCutoffY N) ≤
          2 * multiShiftScheduleU N := by
  have htTop : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLTop : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp htTop
  filter_upwards [eventually_multiShiftCutoffY_bounds,
      eventually_multiShiftScheduleJ_le_log_log, eventually_log_multiShiftScheduleU_le,
      htTop.eventually_ge_atTop 2, hLTop.eventually_ge_atTop 3] with N hy hJL hU ht hL
  let L : ℝ := Real.log (Real.log N)
  let U : ℝ := multiShiftScheduleU N
  let x : ℝ := Real.log N / U
  have hL0 : 0 < L := by simpa only [L] using (show 0 < Real.log (Real.log N) by linarith)
  have ht0 : 0 < Real.log (N : ℝ) := by linarith
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU.1
  have hJ1 : 1 ≤ multiShiftScheduleJ N := by
    apply Nat.one_le_ceil_iff.mpr
    exact Real.sqrt_pos.2 hL0
  have hcollisionFloor := natFloor_exp_log_bounds
    (x := L ^ 2) (show 2 * Real.log 2 ≤ L ^ 2 by
      have hlog2lt : Real.log (2 : ℝ) < 1 := Real.log_two_lt_d9.trans (by norm_num)
      nlinarith)
  change 2 ≤ collisionCutoff N ∧
      L ^ 2 / 2 ≤ Real.log (collisionCutoff N) ∧
      Real.log (collisionCutoff N) ≤ L ^ 2 ∧
      Real.log (L ^ 2) - Real.log 2 ≤ Real.log (Real.log (collisionCutoff N)) ∧
      Real.log (Real.log (collisionCutoff N)) ≤ Real.log (L ^ 2) at hcollisionFloor
  have hLlogP : L ≤ Real.log (collisionCutoff N) := by
    nlinarith [hcollisionFloor.2.1]
  have hlogPP : Real.log (collisionCutoff N) ≤ (collisionCutoff N : ℝ) := by
    have hP0 : (0 : ℝ) < collisionCutoff N := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hcollisionFloor.1)
    exact (Real.log_le_sub_one_of_pos hP0).trans (by linarith)
  have hJP : multiShiftScheduleJ N ≤ collisionCutoff N := by
    have hJPreal : (multiShiftScheduleJ N : ℝ) ≤ collisionCutoff N :=
      hJL.trans (hLlogP.trans hlogPP)
    exact_mod_cast hJPreal
  have hy2 : 2 ≤ multiShiftCutoffY N := hy.2.2.1
  have hlogy0 : 0 < Real.log (multiShiftCutoffY N) :=
    Real.log_pos (by exact_mod_cast (show 1 < multiShiftCutoffY N by omega))
  have hyLower := hy.2.2.2.1
  have hyUpper := hy.2.2.2.2.1
  change x / 2 ≤ Real.log (multiShiftCutoffY N) at hyLower
  change Real.log (multiShiftCutoffY N) ≤ x at hyUpper
  have hratioLower : U ≤ Real.log N / Real.log (multiShiftCutoffY N) := by
    rw [le_div_iff₀ hlogy0]
    have hmul := mul_le_mul_of_nonneg_right hyUpper hU0.le
    dsimp [x] at hmul
    rw [div_mul_cancel₀ (Real.log N) hU0.ne'] at hmul
    nlinarith
  have hratioUpper : Real.log N / Real.log (multiShiftCutoffY N) ≤ 2 * U := by
    rw [div_le_iff₀ hlogy0]
    have hmul := mul_le_mul_of_nonneg_left hyLower (show 0 ≤ 2 * U by positivity)
    have heq : (2 * U) * (x / 2) = Real.log N := by
      dsimp [x]
      field_simp
    nlinarith
  exact ⟨hJ1, hJP, hy2, hy.2.1, hratioLower, hratioUpper⟩

/-- The packet's constant-dependent sieve-depth condition holds on the chosen schedule. -/
theorem eventually_multiShiftSieveDepth (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      C * multiShiftScheduleJ N * Real.log (multiShiftScheduleJ N + 2) ≤
        Real.log N / Real.log (multiShiftCutoffY N) := by
  have hLTop : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlogLTop : Tendsto
      (fun N : ℕ ↦ Real.log (Real.log (Real.log (N : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLTop
  filter_upwards [eventually_multiShiftSieveGeometry,
      eventually_multiShiftScheduleJ_le_log_log,
      hLTop.eventually_ge_atTop 2,
      hlogLTop.eventually_ge_atTop (max 1 (2 * C))] with N hgeom hJL hL hlogL
  let L : ℝ := Real.log (Real.log N)
  have hL0 : 0 < L := by simpa only [L] using (show 0 < Real.log (Real.log N) by linarith)
  have hlogL1 : 1 ≤ Real.log L := by
    simpa only [L] using (le_max_left (1 : ℝ) (2 * C)).trans hlogL
  have hlogLC : 2 * C ≤ Real.log L := by
    simpa only [L] using (le_max_right (1 : ℝ) (2 * C)).trans hlogL
  have hJplus : (multiShiftScheduleJ N : ℝ) + 2 ≤ 2 * L := by
    nlinarith
  have hlogJ : Real.log (multiShiftScheduleJ N + 2) ≤ 2 * Real.log L := by
    calc
      Real.log (multiShiftScheduleJ N + 2) ≤ Real.log (2 * L) :=
        Real.log_le_log (by positivity) hJplus
      _ = Real.log 2 + Real.log L := Real.log_mul (by norm_num) hL0.ne'
      _ ≤ 2 * Real.log L := by
        have hlog2le : Real.log (2 : ℝ) ≤ Real.log L :=
          Real.log_le_log (by norm_num) (by linarith)
        linarith
  have hCLog : C * Real.log (multiShiftScheduleJ N + 2) ≤ (Real.log L) ^ 3 := by
    have hClogL : 2 * C * Real.log L ≤ (Real.log L) ^ 3 := by
      calc
        2 * C * Real.log L ≤ Real.log L * Real.log L :=
          mul_le_mul_of_nonneg_right hlogLC (zero_le_one.trans hlogL1)
        _ ≤ (Real.log L) ^ 3 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hlogL1) (sq_nonneg (Real.log L))]
    exact (mul_le_mul_of_nonneg_left hlogJ hC.le).trans (by nlinarith)
  have hdepth :
      C * multiShiftScheduleJ N * Real.log (multiShiftScheduleJ N + 2) ≤
        multiShiftScheduleU N := by
    rw [multiShiftScheduleU]
    change C * (multiShiftScheduleJ N : ℝ) *
        Real.log (multiShiftScheduleJ N + 2) ≤
      (multiShiftScheduleJ N : ℝ) * (Real.log L) ^ 3
    nlinarith [show (0 : ℝ) ≤ multiShiftScheduleJ N by positivity]
  exact hdepth.trans hgeom.2.2.2.2.1

/-- The exponential Rankin part of the multishift total-variation error vanishes. -/
theorem tendsto_multiShiftSieveExpError (C : ℝ) (hC : 0 < C) :
    Tendsto (fun N : ℕ ↦ Real.exp
      (-(Real.log N / Real.log (multiShiftCutoffY N) / C))) atTop (𝓝 0) := by
  have hLTop : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlogLTop : Tendsto
      (fun N : ℕ ↦ Real.log (Real.log (Real.log (N : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLTop
  have hmajorTop : Tendsto
      (fun N : ℕ ↦ C⁻¹ * Real.log (Real.log (Real.log (N : ℝ)))) atTop atTop :=
    hlogLTop.const_mul_atTop (inv_pos.mpr hC)
  have hratioTop : Tendsto
      (fun N : ℕ ↦ Real.log N / Real.log (multiShiftCutoffY N) / C) atTop atTop := by
    refine Filter.tendsto_atTop_mono' atTop ?_ hmajorTop
    filter_upwards [eventually_multiShiftSieveGeometry,
        hlogLTop.eventually_ge_atTop 1] with N hgeom hlogL
    let L : ℝ := Real.log (Real.log N)
    have hlogL1 : 1 ≤ Real.log L := by simpa only [L] using hlogL
    have hJ1 : 1 ≤ (multiShiftScheduleJ N : ℝ) := by exact_mod_cast hgeom.1
    have hUlower : Real.log L ≤ multiShiftScheduleU N := by
      rw [multiShiftScheduleU]
      change Real.log L ≤ (multiShiftScheduleJ N : ℝ) * (Real.log L) ^ 3
      calc
        Real.log L = Real.log L * 1 := by ring
        _ ≤ Real.log L * (Real.log L) ^ 2 := by
          gcongr
          exact one_le_pow₀ hlogL1
        _ = (Real.log L) ^ 3 := by ring
        _ ≤ (multiShiftScheduleJ N : ℝ) * (Real.log L) ^ 3 := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hJ1
            (pow_nonneg (zero_le_one.trans hlogL1) 3)
    have hratio := hUlower.trans hgeom.2.2.2.2.1
    change C⁻¹ * Real.log L ≤
      (Real.log N / Real.log (multiShiftCutoffY N)) / C
    rw [div_eq_mul_inv]
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_left hratio (inv_nonneg.mpr hC.le))
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hratioTop)

/-- The sieve remainder `(log N)^J / sqrt N` vanishes for `J = ceil(sqrt(log log N))`. -/
theorem tendsto_multiShiftSievePowerError :
    Tendsto (fun N : ℕ ↦ Real.log N ^ multiShiftScheduleJ N / Real.sqrt N)
      atTop (𝓝 0) := by
  have htTop : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLTop : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp htTop
  have hsmall := htTop.eventually
    ((Real.isLittleO_pow_log_id_atTop (n := 2)).bound
      (show (0 : ℝ) < 1 / 4 by norm_num))
  have hmajor : Tendsto (fun N : ℕ ↦ Real.exp (-(Real.log N / 4))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hquarter : Tendsto (fun N : ℕ ↦ (1 / 4 : ℝ) * Real.log N) atTop atTop :=
      htTop.const_mul_atTop (by norm_num)
    convert tendsto_neg_atTop_atBot.comp hquarter using 1
    ext N
    simp only [Function.comp_apply]
    ring
  refine squeeze_zero' (Eventually.of_forall (fun N => by positivity)) ?_ hmajor
  filter_upwards [eventually_multiShiftScheduleJ_le_log_log,
      htTop.eventually_ge_atTop 1, hLTop.eventually_ge_atTop 1, hsmall] with
      N hJL ht hL hsmall
  let t : ℝ := Real.log N
  let L : ℝ := Real.log (Real.log N)
  have ht0 : 0 < t := by simpa only [t] using (show 0 < Real.log (N : ℝ) by linarith)
  have hL0 : 0 < L := by simpa only [L] using (show 0 < Real.log (Real.log N) by linarith)
  have hsmall' : L ^ 2 ≤ t / 4 := by
    have hs := hsmall
    simpa only [t, L, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hL0.le 2),
      abs_of_pos ht0, one_mul, id, div_eq_mul_inv, mul_comm] using hs
  have hJL' : (multiShiftScheduleJ N : ℝ) ≤ L := by simpa only [L] using hJL
  have hexponent : (multiShiftScheduleJ N : ℝ) * L - t / 2 ≤ -(t / 4) := by
    have hmul : (multiShiftScheduleJ N : ℝ) * L ≤ L ^ 2 := by nlinarith
    linarith
  have hpow : Real.log N ^ multiShiftScheduleJ N =
      Real.exp ((multiShiftScheduleJ N : ℝ) * L) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos ht0]
    congr 1
    simp only [t, L]
    ring
  have hsqrt : Real.sqrt N = Real.exp (t / 2) := by
    have hN0 : (0 : ℝ) < N := by
      exact_mod_cast (show 0 < N by
        by_contra hnot
        have : N = 0 := Nat.eq_zero_of_not_pos hnot
        subst N
        norm_num at ht)
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hN0]
    congr 1
    simp only [t]
    ring
  rw [hpow, hsqrt, ← Real.exp_sub]
  exact Real.exp_le_exp.mpr hexponent

/-- The prime-collision comparison cost vanishes on the multishift schedule. -/
theorem tendsto_multiShiftCollisionError :
    Tendsto (fun N : ℕ ↦
      2 * (multiShiftScheduleJ N : ℝ) * (multiShiftScheduleJ N - 1 : ℕ) *
        (collisionCutoff N : ℝ)⁻¹) atTop (𝓝 0) := by
  have hLTop : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hLsqTop : Tendsto (fun N : ℕ ↦ (Real.log (Real.log N)) ^ 2) atTop atTop := by
    refine Filter.tendsto_atTop_mono' atTop ?_ hLTop
    filter_upwards [hLTop.eventually_ge_atTop 1] with N hL
    nlinarith
  have hmajor : Tendsto (fun N : ℕ ↦ 16 / (Real.log (Real.log N)) ^ 2)
      atTop (𝓝 0) := hLsqTop.const_div_atTop 16
  refine squeeze_zero' (Eventually.of_forall (fun N => by positivity)) ?_ hmajor
  filter_upwards [eventually_multiShiftLogBlock_bounds,
      eventually_multiShiftScheduleJ_le_log_log,
      hLTop.eventually_ge_atTop 2] with N hblock hJL hL
  let L : ℝ := Real.log (Real.log N)
  let P : ℕ := collisionCutoff N
  have hL0 : 0 < L := by simpa only [L] using (show 0 < Real.log (Real.log N) by linarith)
  have hP2 : 2 ≤ P := by simpa only [P] using hblock.1
  have hlogP : L ^ 2 / 2 ≤ Real.log P := by
    have hfloor := natFloor_exp_log_bounds
      (x := L ^ 2) (show 2 * Real.log 2 ≤ L ^ 2 by
        have hlog2lt : Real.log (2 : ℝ) < 1 := Real.log_two_lt_d9.trans (by norm_num)
        nlinarith)
    change 2 ≤ P ∧ L ^ 2 / 2 ≤ Real.log P ∧
      Real.log P ≤ L ^ 2 ∧
      Real.log (L ^ 2) - Real.log 2 ≤ Real.log (Real.log P) ∧
      Real.log (Real.log P) ≤ Real.log (L ^ 2) at hfloor
    exact hfloor.2.1
  have hexpP : Real.exp (L ^ 2 / 2) ≤ (P : ℝ) := by
    calc
      Real.exp (L ^ 2 / 2) ≤ Real.exp (Real.log P) := Real.exp_le_exp.mpr hlogP
      _ = P := Real.exp_log (by exact_mod_cast (show 0 < P by omega))
  have hquartic : L ^ 4 / 8 ≤ (P : ℝ) := by
    have hseries := Real.pow_div_factorial_le_exp (L ^ 2 / 2)
      (by positivity) 2
    norm_num at hseries
    nlinarith
  have hPinv : (P : ℝ)⁻¹ ≤ 8 / L ^ 4 := by
    have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
    have hL4 : 0 < L ^ 4 := pow_pos hL0 4
    rw [inv_eq_one_div, div_le_div_iff₀ hP0 hL4]
    nlinarith
  have hJ : (multiShiftScheduleJ N : ℝ) ≤ L := by simpa only [L] using hJL
  have hJpred : ((multiShiftScheduleJ N - 1 : ℕ) : ℝ) ≤ L := by
    have hsub : ((multiShiftScheduleJ N - 1 : ℕ) : ℝ) ≤
        (multiShiftScheduleJ N : ℝ) := by exact_mod_cast Nat.sub_le (multiShiftScheduleJ N) 1
    exact hsub.trans hJ
  calc
    2 * (multiShiftScheduleJ N : ℝ) * (multiShiftScheduleJ N - 1 : ℕ) *
        (collisionCutoff N : ℝ)⁻¹ ≤ 2 * L * L * (8 / L ^ 4) := by
      change 2 * (multiShiftScheduleJ N : ℝ) *
        ((multiShiftScheduleJ N - 1 : ℕ) : ℝ) * (P : ℝ)⁻¹ ≤ _
      gcongr
    _ = 16 / L ^ 2 := by field_simp; ring
    _ = 16 / (Real.log (Real.log N)) ^ 2 := by rfl

/-- The exact total-variation and collision loss used in the final transfer tends to zero. -/
theorem tendsto_multiShiftTransferError (C : ℝ) (hC : 0 < C) :
    Tendsto (fun N : ℕ ↦
      C * (Real.exp (-(Real.log N / Real.log (multiShiftCutoffY N) / C)) +
        Real.log N ^ multiShiftScheduleJ N / Real.sqrt N) +
      2 * (multiShiftScheduleJ N : ℝ) * (multiShiftScheduleJ N - 1 : ℕ) *
        (collisionCutoff N : ℝ)⁻¹) atTop (𝓝 0) := by
  simpa using
    ((tendsto_multiShiftSieveExpError C hC).add tendsto_multiShiftSievePowerError).const_mul C
      |>.add tendsto_multiShiftCollisionError

/-- On every scheduled shift column, the exact threshold displacement is small compared with
the prime mean.  This is the uniform small-tilt estimate needed by the moderate-deviation
theorem; in particular no shorter active prefix than the full `sqrt (log log N)` schedule is
needed. -/
theorem eventually_multiShiftDeviation_smallTilt
    (c A : ℝ) (hc : c < 1) (b : ℕ) (hb : 2 ≤ b)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ j : Fin (multiShiftScheduleJ N),
      (1 + 4 * eta) * multiShiftDeviation c A b N j.val /
          multiShiftPrimeMean N ≤ eta := by
  let q : ℝ := eta / (8 * (1 + 4 * eta))
  have honeEta : 0 < 1 + 4 * eta := by positivity
  have hq : 0 < q := div_pos heta (by positivity)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos hbR
  let k : ℝ := 2 * Real.log b / Real.log 2
  have hk : 0 < k := by dsimp [k]; positivity
  have hLTop : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlogSmallPenalty := hLTop.eventually
    (Real.isLittleO_log_id_atTop.bound (show 0 < q ^ 2 / 4 by positivity))
  have hlogSmallBuffer := hLTop.eventually
    (Real.isLittleO_log_id_atTop.bound (show 0 < q / 16 by positivity))
  filter_upwards [eventually_multiShiftPrimeMean_bounds,
      eventually_log_log_two_mul_le, hlogSmallPenalty, hlogSmallBuffer,
      hLTop.eventually_ge_atTop
        (max (max (max (max (Real.log 2) 2)
          (2 * A ^ 2 / q ^ 2)) ((2 * k / q) ^ 2))
          (max (2 * k / q) (2 / q)))] with
      N hmean htwo hlogPenalty hlogBuffer hlarge
  intro j
  let L : ℝ := Real.log (Real.log N)
  let mean : ℝ := multiShiftPrimeMean N
  let L₂ : ℝ := Real.log (Real.log ((2 * N : ℕ) : ℝ))
  have hLlog2 : Real.log (2 : ℝ) ≤ L := by
    exact (le_max_left _ _).trans (le_max_left _ _) |>.trans
      (le_max_left _ _) |>.trans (le_max_left _ _) |>.trans (by simpa only [L] using hlarge)
  have hL2 : 2 ≤ L := by
    exact (le_max_right (Real.log 2) 2).trans (le_max_left _ _) |>.trans
      (le_max_left _ _) |>.trans (le_max_left _ _) |>.trans (by simpa only [L] using hlarge)
  have hL0 : 0 < L := by linarith
  have hlogL0 : 0 < Real.log L := Real.log_pos (by linarith)
  have hmeanLower : L / 2 ≤ mean := by
    simpa only [L, mean, multiShiftPrimeMean] using hmean.1
  have hmeanUpper : mean ≤ 2 * L := by
    simpa only [L, mean, multiShiftPrimeMean] using hmean.2
  have hmean0 : 0 < mean := lt_of_lt_of_le (by positivity) hmeanLower
  have hlogPenalty' : Real.log L ≤ q ^ 2 / 4 * L := by
    simpa only [L, Real.norm_eq_abs, abs_of_pos hlogL0, abs_of_pos hL0,
      one_mul, id] using hlogPenalty
  have hlogBuffer' : Real.log L ≤ q / 16 * L := by
    simpa only [L, Real.norm_eq_abs, abs_of_pos hlogL0, abs_of_pos hL0,
      one_mul, id] using hlogBuffer
  have hL₂Upper : L₂ ≤ 2 * L := by
    have := htwo
    change L₂ ≤ L + Real.log 2 at this
    linarith
  have hNpos : 0 < N := by
    by_contra hnot
    have : N = 0 := Nat.eq_zero_of_not_pos hnot
    subst N
    norm_num [L] at hL2
  have hlogN0 : 0 < Real.log (N : ℝ) := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hNpos.ne')
    have hlogNnonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
    have : 1 < Real.log (N : ℝ) :=
      (Real.log_pos_iff hlogNnonneg).mp (by simpa only [L] using hL0)
    linarith
  have hL₂Lower : L ≤ L₂ := by
    dsimp only [L, L₂]
    apply Real.log_le_log hlogN0
    apply Real.log_le_log (by exact_mod_cast hNpos)
    exact_mod_cast (show N ≤ 2 * N by omega)
  have hL₂One : 1 < L₂ := lt_of_lt_of_le (by linarith : 1 < L) hL₂Lower
  have hlogL₂Upper : Real.log L₂ ≤ 2 * Real.log L := by
    calc
      Real.log L₂ ≤ Real.log (2 * L) :=
        Real.log_le_log (by linarith) hL₂Upper
      _ = Real.log 2 + Real.log L := Real.log_mul (by norm_num) hL0.ne'
      _ ≤ 2 * Real.log L := by
        have : Real.log (2 : ℝ) ≤ Real.log L :=
          Real.log_le_log (by norm_num) hL2
        linarith
  have hpenalty : multiShiftSubpowerPenalty c N ≤ q * L := by
    have hrad : c * L₂ * Real.log L₂ ≤ 4 * L * Real.log L := by
      by_cases hc0 : 0 ≤ c
      · have hc1 : c ≤ 1 := le_of_lt hc
        have hlogL₂0 : 0 ≤ Real.log L₂ := Real.log_nonneg hL₂One.le
        calc
          c * L₂ * Real.log L₂ ≤ 1 * (2 * L) * (2 * Real.log L) := by
            gcongr
          _ = 4 * L * Real.log L := by ring
      · have hc' : c ≤ 0 := le_of_not_ge hc0
        have hnonneg : 0 ≤ L₂ * Real.log L₂ :=
          mul_nonneg (by linarith) (Real.log_nonneg hL₂One.le)
        have : c * L₂ * Real.log L₂ ≤ 0 := by
          rw [mul_assoc]
          exact mul_nonpos_of_nonpos_of_nonneg hc' hnonneg
        exact this.trans (by positivity)
    have hradq : 4 * L * Real.log L ≤ (q * L) ^ 2 := by
      nlinarith [mul_nonneg hL0.le hlogL0.le]
    calc
      multiShiftSubpowerPenalty c N = Real.sqrt (c * L₂ * Real.log L₂) := by
        rfl
      _ ≤ Real.sqrt ((q * L) ^ 2) := Real.sqrt_le_sqrt (hrad.trans hradq)
      _ = q * L := by rw [Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos hq hL0)]
  have hbaseline : A * Real.sqrt mean ≤ q * L := by
    have hALarge : 2 * A ^ 2 / q ^ 2 ≤ L := by
      exact (le_max_right (max (Real.log 2) 2) (2 * A ^ 2 / q ^ 2)).trans
        (le_max_left _ _) |>.trans (le_max_left _ _) |>.trans (by simpa only [L] using hlarge)
    have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq
    have hAsq : A ^ 2 * mean ≤ q ^ 2 * L ^ 2 := by
      have : 2 * A ^ 2 ≤ q ^ 2 * L := by
        simpa only [mul_comm] using (div_le_iff₀ hq2).mp hALarge
      nlinarith [mul_nonneg (sq_nonneg A) hL0.le]
    have hsqrtSq : (Real.sqrt mean) ^ 2 = mean := Real.sq_sqrt hmean0.le
    nlinarith [sq_nonneg (A * Real.sqrt mean - q * L)]
  have hshift : (((2 * (j.val + 1) : ℕ) : ℝ) * Real.log b / Real.log 2) ≤
      q * L := by
    have hJceil : (multiShiftScheduleJ N : ℝ) < Real.sqrt L + 1 := by
      simpa only [multiShiftScheduleJ, L] using Nat.ceil_lt_add_one (Real.sqrt_nonneg L)
    have hjJ : ((j.val + 1 : ℕ) : ℝ) ≤ multiShiftScheduleJ N := by
      exact_mod_cast j.isLt
    have hj : ((j.val + 1 : ℕ) : ℝ) ≤ Real.sqrt L + 1 :=
      hjJ.trans hJceil.le
    have hkSqLarge : (2 * k / q) ^ 2 ≤ L := by
      exact (le_max_right (max (max (Real.log 2) 2) (2 * A ^ 2 / q ^ 2))
        ((2 * k / q) ^ 2)).trans (le_max_left _ _) |>.trans
          (by simpa only [L] using hlarge)
    have hkLarge : 2 * k / q ≤ L := by
      exact (le_max_left (2 * k / q) (2 / q)).trans (le_max_right _ _) |>.trans
        (by simpa only [L] using hlarge)
    have hsqrtSq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
    have hsqrtBound : k * Real.sqrt L ≤ q * L / 2 := by
      have hr0 : 0 < 2 * k / q := by positivity
      have hr : (2 * k / q) * Real.sqrt L ≤ L := by
        apply (sq_le_sq₀ (mul_nonneg hr0.le (Real.sqrt_nonneg L)) hL0.le).mp
        calc
          ((2 * k / q) * Real.sqrt L) ^ 2 =
              (2 * k / q) ^ 2 * L := by rw [mul_pow, hsqrtSq]
          _ ≤ L * L := mul_le_mul_of_nonneg_right hkSqLarge hL0.le
          _ = L ^ 2 := by ring
      calc
        k * Real.sqrt L = (q / 2) * ((2 * k / q) * Real.sqrt L) := by
          field_simp
        _ ≤ (q / 2) * L := mul_le_mul_of_nonneg_left hr (by positivity)
        _ = q * L / 2 := by ring
    have hkBound : k ≤ q * L / 2 := by
      calc
        k = (q / 2) * (2 * k / q) := by
          field_simp
        _ ≤ (q / 2) * L := mul_le_mul_of_nonneg_left hkLarge (by positivity)
        _ = q * L / 2 := by ring
    calc
      (((2 * (j.val + 1) : ℕ) : ℝ) * Real.log b / Real.log 2) =
          k * ((j.val + 1 : ℕ) : ℝ) := by
        dsimp [k]
        push_cast
        ring
      _ ≤ k * (Real.sqrt L + 1) :=
        mul_le_mul_of_nonneg_left hj hk.le
      _ ≤ q * L := by nlinarith
  have hbuffer : 8 * Real.log L + 1 ≤ q * L := by
    have hOne : 2 / q ≤ L := by
      exact (le_max_right (2 * k / q) (2 / q)).trans (le_max_right _ _) |>.trans
        (by simpa only [L] using hlarge)
    have : 1 ≤ q * L / 2 := by
      calc
        (1 : ℝ) = (q / 2) * (2 / q) := by
          field_simp
        _ ≤ (q / 2) * L := mul_le_mul_of_nonneg_left hOne (by positivity)
        _ = q * L / 2 := by ring
    have hlogPart : 8 * Real.log L ≤ q * L / 2 := by
      nlinarith only [hlogBuffer']
    nlinarith only [hlogPart, this]
  have hxUpper : multiShiftDeviation c A b N j.val ≤ 4 * q * L := by
    rw [multiShiftDeviation]
    change multiShiftSubpowerPenalty c N + A * Real.sqrt mean +
      (((2 * (j.val + 1) : ℕ) : ℝ) * Real.log b / Real.log 2) +
      8 * Real.log L + 1 ≤ 4 * q * L
    linarith
  rw [div_le_iff₀ hmean0]
  have hqIdentity : (1 + 4 * eta) * (4 * q) = eta / 2 := by
    dsimp [q]
    field_simp
    ring
  calc
    (1 + 4 * eta) * multiShiftDeviation c A b N j.val ≤
        (1 + 4 * eta) * (4 * q * L) :=
      mul_le_mul_of_nonneg_left hxUpper honeEta.le
    _ = (eta / 2) * L := by rw [← hqIdentity]; ring
    _ = eta * (L / 2) := by ring
    _ ≤ eta * mean := mul_le_mul_of_nonneg_left hmeanLower heta.le

/-- The remaining hypotheses of `multiShiftColumnMass_ge_moderate_of_baseline`, bundled
uniformly over all scheduled columns.  The square-root baseline itself supplies the two
large-deviation lower-size conditions; this lemma supplies positivity, reciprocal-square
control, small tilt, and baseline domination. -/
theorem eventually_multiShiftModerateSideConditions
    (c A : ℝ) (hc : c < 1) (hA : 0 ≤ A) (b : ℕ) (hb : 2 ≤ b)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ j : Fin (multiShiftScheduleJ N),
      let x := multiShiftDeviation c A b N j.val
      0 < multiShiftPrimeMean N ∧ 0 < x ∧
        (collisionCutoff N : ℝ)⁻¹ ≤ eta * multiShiftPrimeMean N ∧
        (1 + 4 * eta) * x / multiShiftPrimeMean N ≤ eta ∧
        A ^ 2 * multiShiftPrimeMean N ≤ x ^ 2 := by
  have hLTop : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_multiShiftDeviation_smallTilt c A hc b hb eta heta,
      eventually_multiShiftPrimeMean_bounds, eventually_multiShiftLogBlock_bounds,
      hLTop.eventually_ge_atTop (max 2 (1 / eta))] with
      N hsmall hmean hblock hlarge
  intro j
  let L : ℝ := Real.log (Real.log N)
  let mean : ℝ := multiShiftPrimeMean N
  let x : ℝ := multiShiftDeviation c A b N j.val
  have hL2 : 2 ≤ L :=
    (le_max_left (2 : ℝ) (1 / eta)).trans (by simpa only [L] using hlarge)
  have hLeta : 1 / eta ≤ L :=
    (le_max_right (2 : ℝ) (1 / eta)).trans (by simpa only [L] using hlarge)
  have hL0 : 0 < L := by linarith
  have hlogL0 : 0 < Real.log L := Real.log_pos (by linarith)
  have hmeanLower : L / 2 ≤ mean := by
    simpa only [L, mean, multiShiftPrimeMean] using hmean.1
  have hmean0 : 0 < mean := lt_of_lt_of_le (by positivity) hmeanLower
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have hshift0 : 0 ≤
      (((2 * (j.val + 1) : ℕ) : ℝ) * Real.log b / Real.log 2) := by
    have : 0 < Real.log (b : ℝ) := Real.log_pos hbR
    positivity
  have hx0 : 0 < x := by
    dsimp only [x, multiShiftDeviation]
    have hpenalty0 : 0 ≤ multiShiftSubpowerPenalty c N := by
      simp only [multiShiftSubpowerPenalty]
      positivity
    have hbaseline0 : 0 ≤ A * Real.sqrt mean :=
      mul_nonneg hA (Real.sqrt_nonneg _)
    positivity
  have hP2 : 2 ≤ collisionCutoff N := by
    simpa only [L] using hblock.1
  have hPinv : (collisionCutoff N : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hP2)
  have hetaL : 1 ≤ eta * L := by
    have := (div_le_iff₀ heta).mp hLeta
    nlinarith
  have hsquareMass : (collisionCutoff N : ℝ)⁻¹ ≤ eta * mean := by
    calc
      (collisionCutoff N : ℝ)⁻¹ ≤ 1 / 2 := hPinv
      _ ≤ eta * (L / 2) := by nlinarith
      _ ≤ eta * mean := mul_le_mul_of_nonneg_left hmeanLower heta.le
  have hbaselineLe : A * Real.sqrt mean ≤ x := by
    dsimp only [x, multiShiftDeviation]
    have hpenalty0 : 0 ≤ multiShiftSubpowerPenalty c N := by
      simp only [multiShiftSubpowerPenalty]
      positivity
    nlinarith
  have hbaselineSq : A ^ 2 * mean ≤ x ^ 2 := by
    have hsqrtSq : (Real.sqrt mean) ^ 2 = mean := Real.sq_sqrt hmean0.le
    have hsq := (sq_le_sq₀ (mul_nonneg hA (Real.sqrt_nonneg _)) hx0.le).2 hbaselineLe
    calc
      A ^ 2 * mean = (A * Real.sqrt mean) ^ 2 := by rw [mul_pow, hsqrtSq]
      _ ≤ x ^ 2 := hsq
  exact ⟨hmean0, hx0, hsquareMass, by simpa only [x, mean] using hsmall j,
    hbaselineSq⟩

/-- The one-column moderate-deviation bound in the exact event shape consumed by
`multiShiftMass_noHeavy_le_prod_one_sub`.  The real displacement has a final `+ 1`, so the
moderate event implies the packet's natural-valued ceiling threshold. -/
theorem eventually_multiShiftColumnMass_ge_deviation
    (c A eps eta : ℝ) (hc : c < 1) (hA : 0 ≤ A) (b : ℕ) (hb : 2 ≤ b)
    (heps : 0 < eps) (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 100)
    (hetaEps : 80 * eta ≤ eps) (hlargeA : 6 ≤ eta ^ 2 * A ^ 2)
    (habsorbA : 4 * Real.log 2 ≤ eps * A ^ 2) :
    ∀ᶠ N : ℕ in atTop, ∀ j : Fin (multiShiftScheduleJ N),
      Real.exp (-((1 + eps) * multiShiftDeviation c A b N j.val ^ 2 /
          (2 * multiShiftPrimeMean N))) ≤
        NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass
          (Finset.univ : Finset
            (Fin (Fintype.card (primesIoc (collisionCutoff N) (multiShiftCutoffY N))) ×
              Fin (multiShiftScheduleJ N)))
          (fun z ↦ 1 / (((primeIndexEquiv (collisionCutoff N)
            (multiShiftCutoffY N)) z.1 : ℕ) : ℝ))
          {S | multiShiftThreshold c A b N j.val ≤
            (S ∩ shiftArrayColumn
              (Fintype.card (primesIoc (collisionCutoff N) (multiShiftCutoffY N)))
              (multiShiftScheduleJ N) j).card} := by
  classical
  have hLTop : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_multiShiftModerateSideConditions c A hc hA b hb eta heta0,
      eventually_multiShiftCutoffY_bounds, eventually_multiShiftLogBlock_bounds,
      hLTop.eventually_ge_atTop 2] with N hsides hcut hblock hL
  intro j
  let P : ℕ := collisionCutoff N
  let y : ℕ := multiShiftCutoffY N
  let J : ℕ := multiShiftScheduleJ N
  let mean : ℝ := multiShiftPrimeMean N
  let x : ℝ := multiShiftDeviation c A b N j.val
  have hside := hsides j
  change 0 < mean ∧ 0 < x ∧ (P : ℝ)⁻¹ ≤ eta * mean ∧
    (1 + 4 * eta) * x / mean ≤ eta ∧ A ^ 2 * mean ≤ x ^ 2 at hside
  have hP2 : 2 ≤ P := by simpa only [P] using hblock.1
  have hPy : P ≤ y := by
    simpa only [P, y] using hcut.1
  have hmoderate := multiShiftColumnMass_ge_moderate_of_baseline
    (P := P) (y := y) (J := J) j hP2 hPy
    heps heta0 heta1 hetaEps hside.1 hside.2.1 hside.2.2.1 hside.2.2.2.1
    hside.2.2.2.2 hlargeA habsorbA
  calc
    Real.exp (-((1 + eps) * multiShiftDeviation c A b N j.val ^ 2 /
        (2 * multiShiftPrimeMean N))) ≤
      NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass
        (Finset.univ : Finset (Fin (Fintype.card (primesIoc P y)) × Fin J))
        (fun z ↦ 1 / (((primeIndexEquiv P y) z.1 : ℕ) : ℝ))
        {S | mean + x ≤
          ((S ∩ shiftArrayColumn (Fintype.card (primesIoc P y)) J j).card : ℝ)} := by
      simpa only [P, y, J, mean, x, multiShiftPrimeMean] using hmoderate
    _ ≤ NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass
        (Finset.univ : Finset (Fin (Fintype.card (primesIoc P y)) × Fin J))
        (fun z ↦ 1 / (((primeIndexEquiv P y) z.1 : ℕ) : ℝ))
        {S | multiShiftThreshold c A b N j.val ≤
          (S ∩ shiftArrayColumn (Fintype.card (primesIoc P y)) J j).card} := by
      apply NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubsetMass_mono
      · intro S hS
        have hL0 : 0 < Real.log (Real.log (N : ℝ)) := by linarith
        have hlogL0 : 0 ≤ Real.log (Real.log (Real.log (N : ℝ))) :=
          Real.log_nonneg (by linarith)
        have hshift0 : 0 ≤
            (((2 * (j.val + 1) : ℕ) : ℝ) * Real.log b / Real.log 2) := by
          have : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
          positivity
        have harg0 : 0 ≤ multiShiftPrimeMean N + multiShiftSubpowerPenalty c N +
            A * Real.sqrt (multiShiftPrimeMean N) +
            (((2 * (j.val + 1) : ℕ) : ℝ) * Real.log b / Real.log 2) +
            8 * Real.log (Real.log (Real.log N)) := by
          have hpenalty0 : 0 ≤ multiShiftSubpowerPenalty c N := by
            simp only [multiShiftSubpowerPenalty]
            positivity
          have hbaseline0 : 0 ≤ A * Real.sqrt (multiShiftPrimeMean N) :=
            mul_nonneg hA (Real.sqrt_nonneg _)
          have hmeanN : 0 < multiShiftPrimeMean N := by
            simpa only [mean] using hside.1
          nlinarith
        have hceil := Nat.ceil_lt_add_one harg0
        have hthreshold : (multiShiftThreshold c A b N j.val : ℝ) < mean + x := by
          dsimp only [mean, x, multiShiftDeviation]
          rw [multiShiftThreshold]
          exact hceil.trans_eq (by ring)
        change multiShiftThreshold c A b N j.val ≤
          (S ∩ shiftArrayColumn (Fintype.card (primesIoc P y)) J j).card
        have hreal : (multiShiftThreshold c A b N j.val : ℝ) ≤
            ((S ∩ shiftArrayColumn (Fintype.card (primesIoc P y)) J j).card : ℝ) :=
          hthreshold.le.trans hS
        exact_mod_cast hreal
      · intro z hz
        positivity
      · intro z hz
        have hp : Nat.Prime ((primeIndexEquiv P y) z.1 : ℕ) :=
          (Finset.mem_filter.mp ((primeIndexEquiv P y) z.1).property).2
        exact (div_le_one (by exact_mod_cast hp.pos)).2 (by exact_mod_cast hp.one_le)
    _ = _ := by rfl

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
