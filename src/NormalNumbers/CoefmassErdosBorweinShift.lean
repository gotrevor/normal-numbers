/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import NormalNumbers.CoefmassErdosBorweinShiftAux

/-!
# Step 1′: the shifted growing-moment criterion (personal-c5, 2026-10-25)

Statements are verbatim from the KB packet `NNErdosBorweinRandom.lean`; never edit them.  The
paper argument is in `nn-erdos-borwein-random-2026-10-12.md`, section "Heavy neighbours", and the
plan is in `EB-SHIFT-NEXT.md`.
-/

namespace NormalNumbers.ErdosBorweinShift

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open NormalNumbers.ErdosBorweinPositive NormalNumbers.ErdosBorweinEndpoint
open NormalNumbers.RandomLambertMoment

/-- The shifted divisor variance mass `Σ_{j₀ ≤ j ≤ J} b^{−2j} W(n + j)` (Step 1′). -/
noncomputable def shiftedVarianceMass (v : ℕ → ℝ) (b j₀ J P n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc j₀ J, ((b : ℝ) ^ (2 * j))⁻¹ * divisorVarianceMass v P (n + j)

/-- Reindex a natural interval by the successor map. -/
theorem sum_Icc_succ_shift (f : ℕ → ℝ) (a z : ℕ) :
    (∑ j ∈ Finset.Icc (a + 1) (z + 1), f j) =
      ∑ j ∈ Finset.Icc a z, f (j + 1) := by
  have hmap : Finset.map (addLeftEmbedding 1) (Finset.Icc a z) =
      Finset.Icc (a + 1) (z + 1) := by
    simpa [Nat.add_comm] using Finset.map_add_left_Icc a z 1
  rw [← hmap, Finset.sum_map]
  simp only [addLeftEmbedding_apply, Nat.add_comm]

/-- The shifted anchor sum on tuple exponents `0,…,N-1` is the packet's variance mass on
`1,…,N`, with the fixed extra factor `b⁻²`. -/
theorem shifted_anchor_sum_eq (v : ℕ → ℝ) (b j₀ J P x : ℕ) :
    (∑ a ∈ Finset.Icc (j₀ + 1) (J + 1),
        ((b : ℝ) ^ (2 * a))⁻¹ * divisorVarianceMass v P (x + a)) =
      ((b : ℝ) ^ 2)⁻¹ * shiftedVarianceMass v b j₀ J P (x + 1) := by
  rw [sum_Icc_succ_shift]
  unfold shiftedVarianceMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show x + (j + 1) = x + 1 + j by omega]
  rw [show (b : ℝ) ^ (2 * (j + 1)) = (b : ℝ) ^ 2 * (b : ℝ) ^ (2 * j) by
    rw [show 2 * (j + 1) = 2 + 2 * j by ring, pow_add]]
  by_cases hb0 : b = 0
  · subst b
    norm_num [zero_pow (by omega : 2 * (j + 1) ≠ 0)]
  · have hb0R : (b : ℝ) ≠ 0 := by exact_mod_cast hb0
    field_simp [hb0R]

/-- Split the tuple sum into shifted-collision tuples and collision-free tuples. -/
theorem tupleBernMod_sum_le_shiftCollision_add_pow
    (delta : ℕ → ℝ) (hdelta : ∀ p : ℕ, 0 ≤ delta p ∧ delta p ≤ 1)
    (b H j₀ J K P k N : ℕ) (h : ℤ)
    (hb : 2 ≤ b) (hk : 1 ≤ k) (hh : h ≠ 0) (hH : h.natAbs = H)
    (hj₀ : 1 ≤ j₀) (hfreq : 4 * H ≤ b ^ (j₀ + 1)) (hJK : J + 1 ≤ K)
    (hlarge : 16 * (2 * k) * b ^ (J + 1) ≤ b ^ K) (hP : 1 ≤ P) (hKP : 2 * K ≤ P) :
    (∑ n : Fin (2 * k) → Fin N,
        ∏ r ∈ Finset.range (N + K),
          bernMod (delta (r + 1))
            (tuplePhase b h k (r + 1) (fun i => (n i).val))) ≤
      ((shiftTupleCollisionSet (j₀ + 1) (J + 1) K P N k).card : ℝ) +
        (∑ x : Fin N, Real.exp (-(1 / 2 : ℝ) * ((b : ℝ) ^ 2)⁻¹ *
          shiftedVarianceMass (fun p => delta p * (1 - delta p))
            b j₀ J P (x.val + 1))) ^ (2 * k) := by
  classical
  let S := shiftTupleCollisionSet (j₀ + 1) (J + 1) K P N k
  let W : Fin N → ℝ := fun x =>
    shiftedVarianceMass (fun p => delta p * (1 - delta p)) b j₀ J P (x.val + 1)
  let c : ℝ := (1 / 2 : ℝ) * ((b : ℝ) ^ 2)⁻¹
  let g : Fin N → ℝ := fun x => Real.exp (-c * W x)
  let f : (Fin (2 * k) → Fin N) → ℝ := fun n =>
    ∏ r ∈ Finset.range (N + K),
      bernMod (delta (r + 1))
        (tuplePhase b h k (r + 1) (fun i => (n i).val))
  have hf_one (n : Fin (2 * k) → Fin N) : f n ≤ 1 := by
    dsimp only [f]
    apply Finset.prod_le_one
    · intro r hr
      exact bernMod_nonneg _ _
    · intro r hr
      exact bernMod_le_one (hdelta (r + 1)).1 (hdelta (r + 1)).2 _
  have hg_nonneg (x : Fin N) : 0 ≤ g x := (Real.exp_pos _).le
  have hout (n : Fin (2 * k) → Fin N) (hn : n ∉ S) :
      f n ≤ ∏ i, g (n i) := by
    have hfree : ShiftTupleCollisionFree (j₀ + 1) (J + 1) K P k
        (fun i => (n i).val) := by
      by_contra hnot
      exact hn ((mem_shiftTupleCollisionSet_iff_not_collisionFree
        (j₀ := j₀ + 1) (J := J + 1) (K := K) (P := P) (N := N)
        (k := k) (n := n)).2 hnot)
    have hcontract := global_bernMod_product_le_shiftedMass_of_collisionFree
      delta hdelta b H (j₀ + 1) (J + 1) K P k N h n hb hk hh hH
      (by omega) hfreq hJK hP hlarge hKP hfree
    calc
      f n ≤ Real.exp (-(1 / 2 : ℝ) *
          ∑ i : Fin (2 * k), ∑ a ∈ Finset.Icc (j₀ + 1) (J + 1),
            ((b : ℝ) ^ (2 * a))⁻¹ *
              divisorVarianceMass (fun p => delta p * (1 - delta p))
                P ((n i).val + a)) := by
        simpa only [f] using hcontract
      _ = ∏ i : Fin (2 * k), g (n i) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [shifted_anchor_sum_eq]
        dsimp only [g, c, W]
        ring
  have hfilterS : (Finset.univ : Finset (Fin (2 * k) → Fin N)).filter
      (fun n => n ∈ S) = S := by
    ext n
    simp
  have hinside : (∑ n ∈ (Finset.univ : Finset (Fin (2 * k) → Fin N)) with n ∈ S,
      f n) ≤ (S.card : ℝ) := by
    rw [hfilterS]
    simpa only [nsmul_eq_mul, Nat.cast_ofNat, mul_one] using
      (Finset.sum_le_card_nsmul S f 1 (fun n _ => hf_one n))
  have houtside :
      (∑ n ∈ (Finset.univ : Finset (Fin (2 * k) → Fin N)) with n ∉ S, f n) ≤
        ∑ n : Fin (2 * k) → Fin N, ∏ i, g (n i) := by
    calc
      (∑ n ∈ (Finset.univ : Finset (Fin (2 * k) → Fin N)) with n ∉ S, f n) ≤
          ∑ n ∈ (Finset.univ : Finset (Fin (2 * k) → Fin N)) with n ∉ S,
            ∏ i, g (n i) := by
        exact Finset.sum_le_sum fun n hn => hout n (Finset.mem_filter.mp hn).2
      _ ≤ ∑ n : Fin (2 * k) → Fin N, ∏ i, g (n i) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun n _ _ => Finset.prod_nonneg fun i _ => hg_nonneg (n i))
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (Fin (2 * k) → Fin N))) (p := fun n => n ∈ S) f
  calc
    (∑ n : Fin (2 * k) → Fin N, f n) =
        (∑ n ∈ (Finset.univ : Finset (Fin (2 * k) → Fin N)) with n ∈ S, f n) +
          ∑ n ∈ (Finset.univ : Finset (Fin (2 * k) → Fin N)) with n ∉ S, f n :=
      hsplit.symm
    _ ≤ (S.card : ℝ) + ∑ n : Fin (2 * k) → Fin N, ∏ i, g (n i) :=
      add_le_add hinside houtside
    _ = (S.card : ℝ) + (∑ x : Fin N, g x) ^ (2 * k) := by
      rw [← Fintype.prod_sum, Fin.prod_const]
    _ = ((shiftTupleCollisionSet (j₀ + 1) (J + 1) K P N k).card : ℝ) +
        (∑ x : Fin N, Real.exp (-(1 / 2 : ℝ) * ((b : ℝ) ^ 2)⁻¹ *
          shiftedVarianceMass (fun p => delta p * (1 - delta p))
            b j₀ J P (x.val + 1))) ^ (2 * k) := by
      dsimp only [S, g, c, W]
      congr 2
      apply Finset.sum_congr rfl
      intro x hx
      congr 1
      ring

/-- Normalized shifted moment bound: a power of the one-coordinate weighted-mass average plus
the explicit shifted-collision density. -/
theorem ebMoment_le_shiftedMassAvg_pow_add_collision
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (b H j₀ J K P k N : ℕ) (h : ℤ)
    (hb : 2 ≤ b) (hk : 1 ≤ k) (hh : h ≠ 0) (hH : h.natAbs = H)
    (hN : 1 ≤ N) (hP : 1 ≤ P) (hKN : K ≤ N)
    (hj₀ : 1 ≤ j₀) (hfreq : 4 * H ≤ b ^ (j₀ + 1)) (hJK : J + 1 ≤ K)
    (hlarge : 16 * (2 * k) * b ^ (J + 1) ≤ b ^ K) (hKP : 2 * K ≤ P) :
    (∫ w, ‖ErdosBorweinPositive.weylMean b h (ebLambert b X w) N‖ ^ (2 * k) ∂μ) ≤
      ((∑ x : Fin N, Real.exp (-(1 / 2 : ℝ) * ((b : ℝ) ^ 2)⁻¹ *
        shiftedVarianceMass (fun p => delta p * (1 - delta p))
          b j₀ J P (x.val + 1))) / (N : ℝ)) ^ (2 * k) +
        4 * (k : ℝ) ^ 2 * (J + 1) * K *
          (3 / (P : ℝ) + 4 / (N : ℝ)) := by
  let f : (Fin (2 * k) → Fin N) → ℝ := fun n =>
    ∏ r ∈ Finset.range (N + K),
      bernMod (delta (r + 1))
        (tuplePhase b h k (r + 1) (fun i => (n i).val))
  let A : ℝ := ∑ x : Fin N, Real.exp (-(1 / 2 : ℝ) * ((b : ℝ) ^ 2)⁻¹ *
    shiftedVarianceMass (fun p => delta p * (1 - delta p)) b j₀ J P (x.val + 1))
  have hmoment := ebMoment_le_tupleAvg b hb h μ delta X hX
    (Finset.range (N + K)) k N hN 0 1 (Or.inl rfl)
  have hmoment' :
      (∫ w, ‖ErdosBorweinPositive.weylMean b h (ebLambert b X w) N‖ ^ (2 * k) ∂μ) ≤
        (∑ n, f n) / (N : ℝ) ^ (2 * k) := by
    simpa only [f, zero_add, Int.cast_one, one_mul] using hmoment
  have hsum : (∑ n, f n) ≤
      ((shiftTupleCollisionSet (j₀ + 1) (J + 1) K P N k).card : ℝ) + A ^ (2 * k) := by
    simpa only [f, A] using tupleBernMod_sum_le_shiftCollision_add_pow delta hX.1
      b H j₀ J K P k N h hb hk hh hH hj₀ hfreq hJK hlarge hP hKP
  have hNpow : 0 < (N : ℝ) ^ (2 * k) := by positivity
  have hcollision := shiftCollisionDensity_le_four
    (j₀ + 1) (J + 1) K P N k (by omega) hP hN hKN hk
  have hcollision' :
      ((shiftTupleCollisionSet (j₀ + 1) (J + 1) K P N k).card : ℝ) /
          (N : ℝ) ^ (2 * k) ≤
        4 * (k : ℝ) ^ 2 * ((J : ℝ) + 1) * K *
          (3 / (P : ℝ) + 4 / (N : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hcollision
  calc
    (∫ w, ‖ErdosBorweinPositive.weylMean b h (ebLambert b X w) N‖ ^ (2 * k) ∂μ) ≤
        (∑ n, f n) / (N : ℝ) ^ (2 * k) := hmoment'
    _ ≤ (((shiftTupleCollisionSet (j₀ + 1) (J + 1) K P N k).card : ℝ) +
        A ^ (2 * k)) / (N : ℝ) ^ (2 * k) :=
      div_le_div_of_nonneg_right hsum hNpow.le
    _ = ((shiftTupleCollisionSet (j₀ + 1) (J + 1) K P N k).card : ℝ) /
          (N : ℝ) ^ (2 * k) + (A / (N : ℝ)) ^ (2 * k) := by
      rw [add_div, div_pow]
    _ ≤ 4 * (k : ℝ) ^ 2 * (J + 1) * K *
          (3 / (P : ℝ) + 4 / (N : ℝ)) + (A / (N : ℝ)) ^ (2 * k) :=
      add_le_add hcollision' le_rfl
    _ = (A / (N : ℝ)) ^ (2 * k) +
        4 * (k : ℝ) ^ 2 * (J + 1) * K *
          (3 / (P : ℝ) + 4 / (N : ℝ)) := by ring
    _ = ((∑ x : Fin N, Real.exp (-(1 / 2 : ℝ) * ((b : ℝ) ^ 2)⁻¹ *
        shiftedVarianceMass (fun p => delta p * (1 - delta p))
          b j₀ J P (x.val + 1))) / (N : ℝ)) ^ (2 * k) +
        4 * (k : ℝ) ^ 2 * (J + 1) * K *
          (3 / (P : ℝ) + 4 / (N : ℝ)) := by rfl

/-- Shifted variance mass is nonnegative for nonnegative weights. -/
theorem shiftedVarianceMass_nonneg (v : ℕ → ℝ) (hv : ∀ p, 0 ≤ v p)
    (b j₀ J P n : ℕ) : 0 ≤ shiftedVarianceMass v b j₀ J P n := by
  unfold shiftedVarianceMass
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (by positivity) (divisorVarianceMass_nonneg v hv P (n + j))

/-- The finite average is bounded by the density of low shifted mass plus its uniform
exponential cost above the threshold. -/
theorem shiftedMassExpAvg_le_density_add
    (v : ℕ → ℝ) (hv : ∀ p, 0 ≤ v p) (b j₀ J N : ℕ)
    (c : ℝ) (hc : 0 < c) (T : ℝ) (hN : 1 ≤ N) :
    (∑ x : Fin N, Real.exp (-c *
        shiftedVarianceMass v b j₀ J (collisionCutoff N) (x.val + 1))) / (N : ℝ) ≤
      ((((Finset.Icc 1 N).filter (fun n =>
        shiftedVarianceMass v b j₀ J (collisionCutoff N) n ≤ T)).card : ℝ) / (N : ℝ)) +
        Real.exp (-c * T) := by
  classical
  let W : Fin N → ℝ := fun x =>
    shiftedVarianceMass v b j₀ J (collisionCutoff N) (x.val + 1)
  let low : Finset (Fin N) := Finset.univ.filter fun x => W x ≤ T
  let f : Fin N → ℝ := fun x => Real.exp (-c * W x)
  let E : ℝ := Real.exp (-c * T)
  have hf_one (x : Fin N) : f x ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hW0 : 0 ≤ W x := shiftedVarianceMass_nonneg v hv _ _ _ _ _
    nlinarith
  have hout (x : Fin N) (hx : x ∉ low) : f x ≤ E := by
    have hxT : T < W x := by
      simpa only [low, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hx
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsum : (∑ x : Fin N, f x) ≤ (low.card : ℝ) + (N : ℝ) * E := by
    simpa only [Fintype.card_fin] using
      (sum_le_card_exceptional_add_uniform low f E (Real.exp_pos _).le
        (fun x _ => hf_one x) hout)
  have hlowcard : low.card =
      ((Finset.Icc 1 N).filter (fun n =>
        shiftedVarianceMass v b j₀ J (collisionCutoff N) n ≤ T)).card := by
    apply Finset.card_bij (fun x _ => x.val + 1)
    · intro x hx
      have hx' : W x ≤ T := (Finset.mem_filter.mp hx).2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by have := x.isLt; omega⟩, hx'⟩
    · intro x hx y hy hxy
      apply Fin.ext
      omega
    · intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hnIcc, hnT⟩
      rcases Finset.mem_Icc.mp hnIcc with ⟨hn1, hnN⟩
      let x : Fin N := ⟨n - 1, by omega⟩
      refine ⟨x, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ x, ?_⟩
        change shiftedVarianceMass v b j₀ J (collisionCutoff N) ((n - 1) + 1) ≤ T
        rwa [Nat.sub_add_cancel hn1]
      · dsimp only [x]
        omega
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    (∑ x : Fin N, Real.exp (-c *
        shiftedVarianceMass v b j₀ J (collisionCutoff N) (x.val + 1))) / (N : ℝ) =
        (∑ x : Fin N, f x) / (N : ℝ) := by rfl
    _ ≤ ((low.card : ℝ) + (N : ℝ) * E) / (N : ℝ) :=
      div_le_div_of_nonneg_right hsum hNreal.le
    _ = (low.card : ℝ) / (N : ℝ) + E := by
      rw [add_div]
      field_simp [ne_of_gt hNreal]
    _ = ((((Finset.Icc 1 N).filter (fun n =>
        shiftedVarianceMass v b j₀ J (collisionCutoff N) n ≤ T)).card : ℝ) / (N : ℝ)) +
        Real.exp (-c * T) := by rw [hlowcard]

/-- Density divergence of the shifted mass forces its exponential average to vanish. -/
theorem tendsto_shiftedMassExpAvg
    (v : ℕ → ℝ) (hv : ∀ p, 0 ≤ v p) (b j₀ : ℕ) (J : ℕ → ℕ)
    (c : ℝ) (hc : 0 < c)
    (hdiv : ∀ T : ℝ, Tendsto (fun N : ℕ =>
      ((((Finset.Icc 1 N).filter (fun n =>
        shiftedVarianceMass v b j₀ (J N) (collisionCutoff N) n ≤ T)).card : ℝ) / (N : ℝ)))
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (∑ x : Fin N, Real.exp (-c *
        shiftedVarianceMass v b j₀ (J N) (collisionCutoff N) (x.val + 1))) / (N : ℝ))
      atTop (𝓝 0) := by
  have hexp : Tendsto (fun T : ℕ => Real.exp (-c * (T : ℝ))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by linarith)
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨T, hT⟩ := Metric.tendsto_atTop.1 hexp (ε / 2) (by positivity)
  have hET : Real.exp (-c * (T : ℝ)) < ε / 2 := by
    have h := hT T le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_pos (Real.exp_pos _)] at h
    exact h
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 (hdiv (T : ℝ)) (ε / 2) (by positivity)
  refine ⟨max 1 N₀, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hNN₀ : N₀ ≤ N := le_trans (le_max_right _ _) hN
  have hdensity := hN₀ N hNN₀
  have hdensity0 : 0 ≤
      ((((Finset.Icc 1 N).filter (fun n =>
        shiftedVarianceMass v b j₀ (J N) (collisionCutoff N) n ≤ (T : ℝ))).card : ℝ) /
          (N : ℝ)) := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hdensity0] at hdensity
  have havg := shiftedMassExpAvg_le_density_add v hv b j₀ (J N) N c hc (T : ℝ) hN1
  have havg0 : 0 ≤
      (∑ x : Fin N, Real.exp (-c *
        shiftedVarianceMass v b j₀ (J N) (collisionCutoff N) (x.val + 1))) / (N : ℝ) := by
    positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg havg0]
  exact havg.trans_lt (by linarith)

/-! ## Slow-schedule assembly -/

/-- The protected phase window is the varying shift window plus Step 1's fixed-frequency tail. -/
def shiftedPhaseCutoff (Jv H t : ℕ) : ℕ :=
  Jv + 1 + endpointPhaseCutoff 0 H t

/-- The slow interpolation schedule has the standard elementary upper bound. -/
theorem shift_sched_le_three_exp (s : ℕ) :
    (NormalNumbers.CantorLiouville.sched s : ℝ) ≤ 3 * Real.exp (Real.sqrt s) := by
  unfold NormalNumbers.CantorLiouville.sched
  push_cast
  have h1 := Nat.floor_le (Real.exp_pos (Real.sqrt s)).le
  have h2 : (s : ℝ) ≤ 2 * Real.exp (Real.sqrt s) := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
    have he := Real.quadratic_le_exp_of_nonneg (Real.sqrt_nonneg (s : ℝ))
    nlinarith [Real.sqrt_nonneg (s : ℝ)]
  linarith

/-- On the slow schedule, `log log N` is bounded by twice the schedule index. -/
theorem log_log_sched_le_two_mul (s : ℕ) (hs : 2 ≤ s) :
    Real.log (Real.log (NormalNumbers.CantorLiouville.sched s)) ≤ 2 * s := by
  let N := NormalNumbers.CantorLiouville.sched s
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
  have hspos : (0 : ℝ) < s := by positivity
  have hsqrtle : Real.sqrt (s : ℝ) ≤ s := by
    have hsq := Real.sq_sqrt (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
    nlinarith [Real.sqrt_nonneg (s : ℝ)]
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast NormalNumbers.CantorLiouville.one_le_sched s
  have hexppos : (0 : ℝ) < 3 * Real.exp (Real.sqrt s) := by positivity
  have hlogN : Real.log (N : ℝ) ≤ Real.log (3 * Real.exp (Real.sqrt s)) :=
    Real.log_le_log hNpos (shift_sched_le_three_exp s)
  have hlog3raw := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
  have hlog3 : Real.log 3 ≤ 2 := by
    norm_num at hlog3raw ⊢
    exact hlog3raw
  have hlogNle : Real.log (N : ℝ) ≤ (s : ℝ) + 2 := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hlogN
    linarith
  have hlogspos : 0 < Real.log (N : ℝ) := by
    have hlow : Real.exp (Real.sqrt s) ≤ (N : ℝ) :=
      NormalNumbers.CantorLiouville.exp_sqrt_le_sched s (by omega)
    have := Real.log_le_log (Real.exp_pos _) hlow
    rw [Real.log_exp] at this
    exact lt_of_lt_of_le (Real.sqrt_pos.2 hspos) this
  have hloglog := Real.log_le_sub_one_of_pos hlogspos
  calc
    Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) - 1 := hloglog
    _ ≤ (s : ℝ) + 1 := by linarith
    _ ≤ 2 * (s : ℝ) := by linarith

/-- The varying shift window is still linear in the slow-schedule index. -/
theorem eventually_shiftWindow_sched_le (J : ℕ → ℕ)
    (hJ : ∀ᶠ N : ℕ in atTop, (J N : ℝ) ≤ Real.log (Real.log N)) :
    ∀ᶠ t : ℕ in atTop,
      J (NormalNumbers.CantorLiouville.sched (t + 3)) ≤ 2 * (t + 3) := by
  let n : ℕ → ℕ := fun t => NormalNumbers.CantorLiouville.sched (t + 3)
  have hn : StrictMono n := by
    intro a z haz
    exact NormalNumbers.CantorLiouville.sched_strictMono (by omega)
  have hcomp := hn.tendsto_atTop.eventually hJ
  filter_upwards [hcomp] with t ht
  have hlog := log_log_sched_le_two_mul (t + 3) (by omega)
  have hreal : (J (n t) : ℝ) ≤ ((2 * (t + 3) : ℕ) : ℝ) := by
    simpa only [n, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using ht.trans hlog
  exact_mod_cast hreal

/-- Linear bound for the full protected phase cutoff. -/
theorem shiftedPhaseCutoff_le (H t Jv : ℕ) (hJv : Jv ≤ 2 * (t + 3)) :
    shiftedPhaseCutoff Jv H t ≤ (4 + 64 * H) * (t + 3) := by
  have hphase := endpointPhaseCutoff_le 0 H t
  unfold shiftedPhaseCutoff
  have ht : 1 ≤ t + 3 := by omega
  nlinarith

/-- The full shifted phase cutoff supplies the relative tail separation required above. -/
theorem shifted_phase_large {b H t Jv : ℕ} (hb : 2 ≤ b) (hH : 1 ≤ H) :
    16 * (2 * endpointMomentOrder t) * b ^ (Jv + 1) ≤
      b ^ shiftedPhaseCutoff Jv H t := by
  have hbase := endpoint_phase_large (b := b) (e := 0) (H := H) (j := t) hb
  have hsmall : 16 * (2 * endpointMomentOrder t) ≤
      b ^ endpointPhaseCutoff 0 H t := by
    calc
      16 * (2 * endpointMomentOrder t) ≤ 16 * H * (2 * endpointMomentOrder t) := by
        exact Nat.mul_le_mul_right (2 * endpointMomentOrder t)
          (Nat.mul_le_mul_left 16 hH)
      _ ≤ b ^ endpointPhaseCutoff 0 H t := hbase
  unfold shiftedPhaseCutoff
  calc
    16 * (2 * endpointMomentOrder t) * b ^ (Jv + 1) ≤
        b ^ endpointPhaseCutoff 0 H t * b ^ (Jv + 1) :=
      Nat.mul_le_mul_right (b ^ (Jv + 1)) hsmall
    _ = b ^ (Jv + 1) * b ^ endpointPhaseCutoff 0 H t := by ring
    _ = b ^ (Jv + 1 + endpointPhaseCutoff 0 H t) := by
      simp only [pow_add]

/-- Eventually the collision cutoff and sample length dominate the varying protected window. -/
theorem eventually_shifted_cutoff_conditions (J : ℕ → ℕ)
    (hJ : ∀ᶠ N : ℕ in atTop, (J N : ℝ) ≤ Real.log (Real.log N)) (H : ℕ) :
    ∀ᶠ t : ℕ in atTop,
      let N := NormalNumbers.CantorLiouville.sched (t + 3)
      let K := shiftedPhaseCutoff (J N) H t
      2 * K ≤ collisionCutoff N ∧ K ≤ N ∧ J N ≤ 2 * (t + 3) := by
  let C := 2 * (4 + 64 * H)
  filter_upwards [eventually_shiftWindow_sched_le J hJ,
    eventually_pow_le_collisionCutoff_sched 1, eventually_pow_le_sched 1,
    eventually_ge_atTop C] with t hJt hP hN ht
  let N := NormalNumbers.CantorLiouville.sched (t + 3)
  let K := shiftedPhaseCutoff (J N) H t
  have hK : K ≤ (4 + 64 * H) * (t + 3) := shiftedPhaseCutoff_le H t (J N) hJt
  have hs : 1 ≤ t + 3 := by omega
  have hpoly : C * (t + 3) ≤ (t + 3) ^ 4 := by
    calc
      C * (t + 3) ≤ (t + 3) * (t + 3) := Nat.mul_le_mul_right _ (by omega)
      _ = (t + 3) ^ 2 := by ring
      _ ≤ (t + 3) ^ 4 := pow_le_pow_right' hs (by omega)
  refine ⟨?_, ?_, hJt⟩
  · calc
      2 * K ≤ C * (t + 3) := by
        exact (Nat.mul_le_mul_left 2 hK).trans_eq (by simp only [C]; ring)
      _ ≤ (t + 3) ^ 4 := hpoly
      _ ≤ collisionCutoff N := by simpa only [N] using hP
  · calc
      K ≤ (4 + 64 * H) * (t + 3) := hK
      _ ≤ C * (t + 3) := by gcongr; simp only [C]; omega
      _ ≤ (t + 3) ^ 4 := hpoly
      _ ≤ N := by simpa only [N] using hN

/-- The extra moving-shift factor in the collision density costs only one additional
polynomial degree beyond the shifted phase window. -/
theorem shifted_collision_prefactor_le (H q t Jv : ℕ)
    (hJv : Jv ≤ 2 * (t + 3)) :
    (q + 1) ^ (2 * endpointMomentOrder t) *
        (4 * endpointMomentOrder t ^ 2 * (Jv + 1) * shiftedPhaseCutoff Jv H t) ≤
      (48 * (4 + 64 * H) * 2 ^ (2 * (q + 1))) *
        (t + 3) ^ (2 * (q + 1) + 4) := by
  let k := endpointMomentOrder t
  let K := shiftedPhaseCutoff Jv H t
  let S := t + 3
  let D := 2 * (q + 1)
  have hth := endpoint_threshold_factor_le q t
  have hk := endpointMomentOrder_le t
  have hK := shiftedPhaseCutoff_le H t Jv hJv
  have hS : 1 ≤ S := by dsimp only [S]; omega
  have hJone : Jv + 1 ≤ 3 * S := by
    dsimp only [S]
    nlinarith
  calc
    (q + 1) ^ (2 * k) * (4 * k ^ 2 * (Jv + 1) * K) ≤
        (2 ^ D * S ^ D) *
          (4 * (2 * S) ^ 2 * (3 * S) * ((4 + 64 * H) * S)) := by
      gcongr
    _ = (48 * (4 + 64 * H) * 2 ^ D) * S ^ (D + 4) := by ring
    _ = (48 * (4 + 64 * H) * 2 ^ (2 * (q + 1))) *
        (t + 3) ^ (2 * (q + 1) + 4) := by rfl

/-- The shifted moment estimate is summable after normalization by every fixed rational
threshold.  This is Step 1's slow-schedule argument with the proved moving-window collision
and phase bounds substituted verbatim. -/
theorem summable_shifted_normalized_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (J : ℕ → ℕ) (hJ : ∀ᶠ N : ℕ in atTop, (J N : ℝ) ≤ Real.log (Real.log N))
    (hdiv : ∀ b : ℕ, 2 ≤ b → ∀ j₀ : ℕ, ∀ T : ℝ, Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N).filter (fun n =>
        shiftedVarianceMass (fun m => delta m * (1 - delta m)) b j₀ (J N)
          (collisionCutoff N) n ≤ T)).card : ℝ) / N) atTop (𝓝 0))
    (b : ℕ) (hb : 2 ≤ b) (h : ℤ) (hh : h ≠ 0) (q : ℕ) :
    Summable (fun t : ℕ =>
      (∫ w, ‖ErdosBorweinPositive.weylMean b h (ebLambert b X w)
        (NormalNumbers.CantorLiouville.sched (t + 3))‖ ^
          (2 * endpointMomentOrder t) ∂μ) /
        ((1 : ℝ) / (q + 1)) ^ (2 * endpointMomentOrder t)) := by
  let v : ℕ → ℝ := fun m => delta m * (1 - delta m)
  have hv (m : ℕ) : 0 ≤ v m := by
    dsimp only [v]
    exact mul_nonneg (hX.1 m).1 (sub_nonneg.mpr (hX.1 m).2)
  let H := h.natAbs
  have hH : 1 ≤ H := by
    dsimp only [H]
    exact (Int.natAbs_pos.mpr hh)
  let j₀ := 4 * H
  have hj₀ : 1 ≤ j₀ := by dsimp only [j₀]; omega
  have hfreq : 4 * H ≤ b ^ (j₀ + 1) := by
    calc
      4 * H ≤ 2 ^ (4 * H) := (Nat.lt_two_pow_self).le
      _ ≤ b ^ (4 * H) := Nat.pow_le_pow_left hb _
      _ ≤ b ^ (4 * H + 1) := pow_le_pow_right' (by omega) (by omega)
      _ = b ^ (j₀ + 1) := by rfl
  let n : ℕ → ℕ := fun t => NormalNumbers.CantorLiouville.sched (t + 3)
  let k : ℕ → ℕ := endpointMomentOrder
  let K : ℕ → ℕ := fun t => shiftedPhaseCutoff (J (n t)) H t
  let P : ℕ → ℕ := fun t => collisionCutoff (n t)
  let c : ℝ := (1 / 2 : ℝ) * ((b : ℝ) ^ 2)⁻¹
  have hc : 0 < c := by dsimp only [c]; positivity
  let φ : ℕ → ℝ := fun t =>
    (∑ x : Fin (n t), Real.exp (-c *
      shiftedVarianceMass v b j₀ (J (n t)) (P t) (x.val + 1))) / (n t : ℝ)
  have hn : StrictMono n := by
    intro i t hit
    exact NormalNumbers.CantorLiouville.sched_strictMono (by omega)
  have hφ : Tendsto φ atTop (𝓝 0) := by
    exact (tendsto_shiftedMassExpAvg v hv b j₀ J c hc (hdiv b hb j₀)).comp
      hn.tendsto_atTop
  let ε : ℝ := 1 / (q + 1)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hφsmall : ∀ᶠ t : ℕ in atTop, φ t < ε / 2 :=
    (tendsto_order.1 hφ).2 (ε / 2) (by positivity)
  have hcut := eventually_shifted_cutoff_conditions J hJ H
  let d : ℕ := 2 * (q + 1) + 4
  let C : ℕ := 48 * (4 + 64 * H) * 2 ^ (2 * (q + 1))
  have hsS : Summable (fun t : ℕ => 1 / (((t + 3 : ℕ) : ℝ) ^ 2)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (summable_nat_add_iff 3).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num))
  have hsP : Summable (fun t : ℕ =>
      (C : ℝ) * 3 * (((t + 3 : ℕ) : ℝ) ^ d /
        collisionCutoff (NormalNumbers.CantorLiouville.sched (t + 3)))) := by
    exact (summable_pow_div_collisionCutoff_sched d).mul_left ((C : ℝ) * 3)
  have hsN : Summable (fun t : ℕ =>
      (C : ℝ) * 4 * (((t + 3 : ℕ) : ℝ) ^ d /
        NormalNumbers.CantorLiouville.sched (t + 3))) := by
    exact (summable_pow_div_sched d).mul_left ((C : ℝ) * 4)
  have href : Summable (fun t : ℕ =>
      1 / (((t + 3 : ℕ) : ℝ) ^ 2) +
        (C : ℝ) * 3 * (((t + 3 : ℕ) : ℝ) ^ d / P t) +
        (C : ℝ) * 4 * (((t + 3 : ℕ) : ℝ) ^ d / n t)) := by
    simpa only [P, n] using (hsS.add hsP).add hsN
  refine Summable.of_norm_bounded_eventually href ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hφsmall, hcut] with t hsmall hconditions
  have hk : 1 ≤ k t := endpointMomentOrder_pos t
  have hN : 1 ≤ n t := NormalNumbers.CantorLiouville.one_le_sched (t + 3)
  have hJK : J (n t) + 1 ≤ K t := by simp [K, shiftedPhaseCutoff]
  have hKN : K t ≤ n t := by simpa only [K, n] using hconditions.2.1
  have hKP : 2 * K t ≤ P t := by simpa only [K, P, n] using hconditions.1
  have hP : 1 ≤ P t := by omega
  have hlarge : 16 * (2 * k t) * b ^ (J (n t) + 1) ≤ b ^ (K t) := by
    simpa only [k, K] using shifted_phase_large (b := b) (H := H)
      (t := t) (Jv := J (n t)) hb hH
  have hmoment := ebMoment_le_shiftedMassAvg_pow_add_collision μ delta X hX
    b H j₀ (J (n t)) (K t) (P t) (k t) (n t) h hb hk hh rfl hN hP hKN
      hj₀ hfreq hJK hlarge hKP
  have hφ0 : 0 ≤ φ t := by dsimp only [φ]; positivity
  have hfirst : (φ t) ^ (2 * k t) / ε ^ (2 * k t) ≤
      1 / (((t + 3 : ℕ) : ℝ) ^ 2) := by
    have hbase : φ t / ε ≤ (1 / 2 : ℝ) := by
      rw [div_le_iff₀ hε]
      linarith
    calc
      (φ t) ^ (2 * k t) / ε ^ (2 * k t) = (φ t / ε) ^ (2 * k t) :=
        (div_pow _ _ _).symm
      _ ≤ (1 / 2 : ℝ) ^ (2 * k t) :=
        pow_le_pow_left₀ (div_nonneg hφ0 hε.le) hbase _
      _ ≤ 1 / (((t + 3 : ℕ) : ℝ) ^ 2) := endpoint_half_pow_le t
  have hprefactor :
      (((q + 1 : ℕ) : ℝ) ^ (2 * k t)) *
          (4 * (k t : ℝ) ^ 2 * (J (n t) + 1) * (K t : ℝ)) ≤
        (C : ℝ) * (((t + 3 : ℕ) : ℝ) ^ d) := by
    exact_mod_cast shifted_collision_prefactor_le H q t (J (n t)) hconditions.2.2
  have hcollision :
      (4 * (k t : ℝ) ^ 2 * (J (n t) + 1) * (K t : ℝ) *
          (3 / (P t : ℝ) + 4 / (n t : ℝ))) / ε ^ (2 * k t) ≤
        (C : ℝ) * 3 * (((t + 3 : ℕ) : ℝ) ^ d / (P t : ℝ)) +
          (C : ℝ) * 4 * (((t + 3 : ℕ) : ℝ) ^ d / (n t : ℝ)) := by
    calc
      (4 * (k t : ℝ) ^ 2 * (J (n t) + 1) * (K t : ℝ) *
          (3 / (P t : ℝ) + 4 / (n t : ℝ))) / ε ^ (2 * k t) =
          ((((q + 1 : ℕ) : ℝ) ^ (2 * k t)) *
            (4 * (k t : ℝ) ^ 2 * (J (n t) + 1) * (K t : ℝ))) *
              (3 / (P t : ℝ) + 4 / (n t : ℝ)) := by
        dsimp only [ε]
        rw [one_div_pow, one_div, div_inv_eq_mul]
        push_cast
        ring
      _ ≤ ((C : ℝ) * (((t + 3 : ℕ) : ℝ) ^ d)) *
          (3 / (P t : ℝ) + 4 / (n t : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hprefactor (by positivity)
      _ = (C : ℝ) * 3 * (((t + 3 : ℕ) : ℝ) ^ d / (P t : ℝ)) +
          (C : ℝ) * 4 * (((t + 3 : ℕ) : ℝ) ^ d / (n t : ℝ)) := by ring
  have hI0 : 0 ≤ ∫ w, ‖ErdosBorweinPositive.weylMean b h (ebLambert b X w)
      (n t)‖ ^ (2 * k t) ∂μ := integral_nonneg fun _ => by positivity
  rw [Real.norm_of_nonneg (div_nonneg hI0 (pow_nonneg hε.le _))]
  calc
    (∫ w, ‖ErdosBorweinPositive.weylMean b h (ebLambert b X w)
        (n t)‖ ^ (2 * k t) ∂μ) / ε ^ (2 * k t) ≤
        ((φ t) ^ (2 * k t) +
          4 * (k t : ℝ) ^ 2 * (J (n t) + 1) * (K t : ℝ) *
            (3 / (P t : ℝ) + 4 / (n t : ℝ))) / ε ^ (2 * k t) :=
      div_le_div_of_nonneg_right
        (by simpa only [φ, v, c, P, n, k, K, neg_mul] using hmoment)
        (pow_nonneg hε.le _)
    _ = (φ t) ^ (2 * k t) / ε ^ (2 * k t) +
        (4 * (k t : ℝ) ^ 2 * (J (n t) + 1) * (K t : ℝ) *
          (3 / (P t : ℝ) + 4 / (n t : ℝ))) / ε ^ (2 * k t) := by rw [add_div]
    _ ≤ 1 / (((t + 3 : ℕ) : ℝ) ^ 2) +
        ((C : ℝ) * 3 * (((t + 3 : ℕ) : ℝ) ^ d / (P t : ℝ)) +
          (C : ℝ) * 4 * (((t + 3 : ℕ) : ℝ) ^ d / (n t : ℝ))) :=
      add_le_add hfirst hcollision
    _ = 1 / (((t + 3 : ℕ) : ℝ) ^ 2) +
        (C : ℝ) * 3 * (((t + 3 : ℕ) : ℝ) ^ d / P t) +
        (C : ℝ) * 4 * (((t + 3 : ℕ) : ℝ) ^ d / n t) := by ring

/-- **Target (positive side, no arithmetic input): Step 1′, the shifted growing-moment criterion.**
A divisor `d > P₀` of `n_i + j` contributes `1 − 4v_d sin²(π h b^{−j})` to the `2k`-th moment.  So
Step 1's proof runs with the collision window `K` replaced by `2J + K`; collisions cost
`O(k²J²/P₀)`.  The binder `j₀` is needed: for `b^j ∣ h` the angle is an integer and nothing
contracts.  The proof uses `b^{j₀} ≥ 2|h|`.  Confidence 85%. -/
theorem ebRandom_ae_normal_of_shiftedVariance_diverges
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (J : ℕ → ℕ) (hJ : ∀ᶠ N : ℕ in atTop, (J N : ℝ) ≤ Real.log (Real.log N))
    (hdiv : ∀ b : ℕ, 2 ≤ b → ∀ j₀ : ℕ, ∀ T : ℝ, Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N).filter (fun n =>
        shiftedVarianceMass (fun m => delta m * (1 - delta m)) b j₀ (J N)
          (collisionCutoff N) n ≤ T)).card : ℝ) / N) atTop (𝓝 0)) :
    ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → NormalNumbers.IsNormal b (ebLambert b X w) := by
  rw [ae_all_iff]
  intro b
  by_cases hb : 2 ≤ b
  · have hall : ∀ᵐ w ∂μ, ∀ h : ℤ, h ≠ 0 →
        Tendsto (fun N : ℕ => ErdosBorweinPositive.weylMean b h (ebLambert b X w) N)
          atTop (𝓝 0) := by
      rw [ae_all_iff]
      intro h
      by_cases hh : h = 0
      · exact Eventually.of_forall fun _ hne => absurd hh hne
      · have hsum : ∀ q : ℕ, Summable (fun t : ℕ =>
            (∫ w, ‖ErdosBorweinPositive.weylMean b h (ebLambert b X w)
              (NormalNumbers.CantorLiouville.sched (t + 3))‖ ^
                (2 * endpointMomentOrder t) ∂μ) /
              ((1 : ℝ) / (q + 1)) ^ (2 * endpointMomentOrder t)) :=
          fun q => summable_shifted_normalized_moments μ delta X hX J hJ hdiv b hb h hh q
        filter_upwards [ae_tendsto_weylMean_of_growing_moment_sums μ (ebLambert b X)
          (measurable_ebLambert b X hX.2.1) b h endpointMomentOrder
          endpointMomentOrder_pos hsum] with w hw _
        exact hw
    filter_upwards [hall] with w hw _
    apply NormalNumbers.QSpanCriterion.isNormal_of_weylAvg b hb
    intro h hh
    exact (hw h hh).congr fun N => weylMean_eq_weylAvg b h (ebLambert b X w) N
  · exact Eventually.of_forall fun _ hb' => absurd hb' hb

end NormalNumbers.ErdosBorweinShift
