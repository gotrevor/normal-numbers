/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyTwoPoint
import NormalNumbers.VandeheyTransfer

/-!
# The orbit transfer: from the measure bound to `ClassEquidistribution`

`VandeheyTwoPoint.sum_gaussMeasure_windowBound_le` bounds the `γ`-weighted total of
`VandeheyCocycle.windowBound` over any finite family of genuine length-`(K+|q|)` words by
`|S|·√(varConst/K)`.  What `ClassEquidistribution` asks for is the *orbit* average of the same
quantity along a single CF-normal point.  CF-normality supplies exactly the bridge: the frequency
of each fixed window converges to its `γ`-mass, and the windows that are *not* digit-bounded are
charged to the digit tail, whose frequency is `O(1/Z)` uniformly
(`VandeheyAut.card_unbounded_window_le`, `tendsto_digitTail_freq`, `digitTail_le`).

Order of choice: `ε ↦ K` (from the variance bound), then `K ↦ Z` (the digit bound, which must
beat `(1+|L|)·(K+|q|)·τ(Z)`).  The threshold in `n` may depend on `x`; `K` may not.
-/

namespace NormalNumbers

open MeasureTheory Filter VandeheyAut VandeheyState VandeheyMix

namespace VandeheyTwo

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Bad digit positions in `[0, n+m)` are bad positions in `[0,n)` plus at most `m` more. -/
lemma card_bad_shift_le (x : ℝ) (Z n m : ℕ) :
    (((Finset.range (n + m)).filter
        (fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ Z))).card : ℕ)
      ≤ ((Finset.range n).filter
          (fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ Z))).card + m := by
  classical
  have hsub : (Finset.range (n + m)).filter
      (fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ Z))
      ⊆ ((Finset.range n).filter (fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ Z)))
        ∪ Finset.Ico n (n + m) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    by_cases hin : i < n
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hin, hi.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, hi.1⟩)
  calc ((Finset.range (n + m)).filter
        (fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ Z))).card
      ≤ (((Finset.range n).filter (fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ Z)))
          ∪ Finset.Ico n (n + m)).card := Finset.card_le_card hsub
    _ ≤ ((Finset.range n).filter (fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ Z))).card
          + (Finset.Ico n (n + m)).card := Finset.card_union_le _ _
    _ = ((Finset.range n).filter (fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ Z))).card + m := by
        rw [Nat.card_Ico]; omega

/-- **The orbit split.**  The orbit sum of `windowBound` splits into a finite weighted count over
digit-bounded windows plus a residue charged to the digit tail. -/
theorem sum_windowBound_le_split [Nonempty S] (δ : S → ℕ → S) (t : S) (q : List ℕ) (L : ℝ)
    {K : ℕ} (hK : 0 < K) (Z : ℕ) (x : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, VandeheyCocycle.windowBound δ t q L K (cfWindow x i (K + q.length))
      ≤ (∑ W ∈ VandeheyAut.boundedWords Z (K + q.length),
            VandeheyCocycle.windowBound δ t q L K W
              * (((Finset.range n).filter (fun i => W = cfWindow x i (K + q.length))).card : ℝ))
        + (1 + |L|) * ((K + q.length : ℕ) : ℝ)
            * ((((Finset.range n).filter
                (fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ Z))).card : ℝ)
              + ((K + q.length : ℕ) : ℝ)) := by
  classical
  set m : ℕ := K + q.length with hm
  set b : List ℕ → ℝ := VandeheyCocycle.windowBound δ t q L K with hb
  set F : Finset (List ℕ) := VandeheyAut.boundedWords Z m with hF
  set B : ℝ := 1 + |L| with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hbB : ∀ W : List ℕ, b W ≤ B := fun W => VandeheyCocycle.windowBound_le δ t q L hK W
  have hb0 : ∀ W : List ℕ, 0 ≤ b W := by
    intro W
    rw [hb, VandeheyCocycle.windowBound]
    have h := Finset.le_sup' (fun d : S => |VandeheyCocycle.localAvg δ t q L K d W|)
      (Finset.mem_univ (Classical.arbitrary S))
    exact le_trans (abs_nonneg _) h
  set G : Finset ℕ := (Finset.range n).filter (fun i => cfWindow x i m ∈ F) with hG
  set Bad : Finset ℕ := (Finset.range n).filter (fun i => cfWindow x i m ∉ F) with hBad
  have hsplit : ∑ i ∈ Finset.range n, b (cfWindow x i m)
      = (∑ i ∈ G, b (cfWindow x i m)) + ∑ i ∈ Bad, b (cfWindow x i m) :=
    (Finset.sum_filter_add_sum_filter_not (Finset.range n) _ _).symm
  -- the good part is a finite weighted count
  have hgood : ∑ i ∈ G, b (cfWindow x i m)
      = ∑ W ∈ F, b W * (((Finset.range n).filter (fun i => W = cfWindow x i m)).card : ℝ) := by
    have hmaps : ∀ i ∈ G, cfWindow x i m ∈ F := fun i hi => (Finset.mem_filter.mp hi).2
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun i => b (cfWindow x i m))]
    refine Finset.sum_congr rfl fun W hW => ?_
    have hfil : G.filter (fun i => cfWindow x i m = W)
        = (Finset.range n).filter (fun i => W = cfWindow x i m) := by
      ext i
      simp only [hG, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨⟨hin, -⟩, hWi⟩; exact ⟨hin, hWi.symm⟩
      · rintro ⟨hin, hWi⟩; exact ⟨⟨hin, hWi ▸ hW⟩, hWi.symm⟩
    rw [hfil]
    have hconst : ∀ i ∈ (Finset.range n).filter (fun i => W = cfWindow x i m),
        b (cfWindow x i m) = b W := by
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- the bad part is charged to the digit tail
  have hbadcard : (Bad.card : ℝ) ≤ (m : ℝ)
      * ((((Finset.range n).filter
          (fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ Z))).card : ℝ) + (m : ℝ)) := by
    have h1 : Bad.card ≤ m * ((Finset.range (n + m)).filter
        (fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ Z))).card := by
      simpa [hBad, hF] using card_unbounded_window_le x Z m n
    have h2 := card_bad_shift_le x Z n m
    have h3 : Bad.card ≤ m * (((Finset.range n).filter
        (fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ Z))).card + m) :=
      le_trans h1 (Nat.mul_le_mul_left m h2)
    exact_mod_cast h3
  have hbad : ∑ i ∈ Bad, b (cfWindow x i m) ≤ B * (Bad.card : ℝ) := by
    calc ∑ i ∈ Bad, b (cfWindow x i m) ≤ ∑ _i ∈ Bad, B :=
          Finset.sum_le_sum fun i _ => hbB _
      _ = (Bad.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = B * (Bad.card : ℝ) := by ring
  rw [hsplit, hgood]
  have hfinal : B * (Bad.card : ℝ)
      ≤ B * (m : ℝ) * ((((Finset.range n).filter
          (fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ Z))).card : ℝ) + (m : ℝ)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hbadcard hB0
  linarith [hbad, hfinal]

/-! ## The weighted window frequency -/

omit [Fintype S] [DecidableEq S] in
/-- The `b`-weighted window frequency of a finite family converges to its `b`-weighted
`γ`-mass. -/
theorem tendsto_weighted_window_freq {x : ℝ} (hx : IsCFNormal x) (F : Finset (List ℕ)) {m : ℕ}
    (hm : 1 ≤ m) (hFlen : ∀ W ∈ F, W.length = m) (hFpos : ∀ W ∈ F, ∀ a ∈ W, 1 ≤ a)
    (b : List ℕ → ℝ) :
    Tendsto (fun n => ∑ W ∈ F, b W * ((((Finset.range n).filter
        (fun i => W = cfWindow x i m)).card : ℝ) / n)) atTop
      (nhds (∑ W ∈ F, b W * (gaussMeasure (cfCylinder W)).toReal)) := by
  refine tendsto_finsetSum _ fun W hW => ?_
  have hlen := hFlen W hW
  have hne : W ≠ [] := by
    intro h
    rw [h] at hlen
    simp only [List.length_nil] at hlen
    omega
  have h := tendsto_windowFreq hx W hne (hFpos W hW)
  rw [hlen] at h
  exact h.const_mul (b W)

/-! ## The main theorem -/

/-- **`ClassEquidistribution` holds for every automaton the pin covers.**

This is the bridge from the transfer-operator pin `VandeheyState.stateHorizonIntegral_pin` to
the hypothesis that `VandeheyCocycle.tendsto_jointCount_of_classEquidistribution` consumes.  The
reference weight is the pin's constant `c`, so it mentions neither `x` nor the initial state —
exactly the `VandeheyUniformFreq` contract. -/
theorem classEquidistribution_of_pin [Nonempty S] (δ : S → ℕ → S) (t : S) (q : List ℕ)
    {c C θ : ℝ} (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hpin : ∀ (n : ℕ) (e : S) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      |stateHorizonIntegral δ (cfCylinder q) n e t τ
          - c * (gaussMeasure (cfCylinder q)).toReal|
        ≤ C * θ ^ n * (gaussMeasure (cfCylinder q)).toReal) :
    VandeheyCocycle.ClassEquidistribution δ t q := by
  classical
  refine ⟨c, fun ε hε => ?_⟩
  set N : ℝ := (Fintype.card S : ℝ) with hN
  set V : ℝ := varConst C θ q.length with hV
  have hV0 : 0 ≤ V := varConst_nonneg hC hθ0 hθ1 _
  -- Step 1: choose `K` from the variance bound
  have htK : Tendsto (fun K : ℕ => N * Real.sqrt (V / K)) atTop (nhds 0) := by
    have h0 : Tendsto (fun K : ℕ => V / (K : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat V
    have h1 : Tendsto (fun K : ℕ => Real.sqrt (V / K)) atTop (nhds 0) := by
      have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h0
      simpa [Function.comp_def, Real.sqrt_zero] using h
    simpa using h1.const_mul N
  obtain ⟨K, hK1, hKε⟩ : ∃ K : ℕ, 1 ≤ K ∧ N * Real.sqrt (V / K) < ε / 3 := by
    have h := (htK.eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε / 3))).and
      (eventually_ge_atTop 1)
    obtain ⟨K, hK⟩ := h.exists
    exact ⟨K, hK.2, hK.1⟩
  have hK : 0 < K := hK1
  set m : ℕ := K + q.length with hm
  set B : ℝ := 1 + |c| with hB
  have hB0 : 0 < B := by rw [hB]; positivity
  have hm0 : 0 < m := by omega
  -- Step 2: choose the digit bound `Z`
  have htZ : Tendsto (fun Z : ℕ =>
      B * (m : ℝ) * (Real.log (1 + 1 / ((Z : ℝ) + 1)) / Real.log 2)) atTop (nhds 0) := by
    simpa using tendsto_digitTail_bound.const_mul (B * (m : ℝ))
  obtain ⟨Z, hZε⟩ : ∃ Z : ℕ,
      B * (m : ℝ) * (Real.log (1 + 1 / ((Z : ℝ) + 1)) / Real.log 2) < ε / 3 :=
    ((htZ.eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε / 3))).exists).imp
      fun Z hZ => hZ
  refine ⟨K, hK, fun x hx => ?_⟩
  set F : Finset (List ℕ) := VandeheyAut.boundedWords Z m with hF
  set bfun : List ℕ → ℝ := VandeheyCocycle.windowBound δ t q c K with hbfun
  have hFlen : ∀ W ∈ F, W.length = m := fun W hW => (VandeheyAut.mem_boundedWords m W |>.mp hW).1
  have hFpos : ∀ W ∈ F, ∀ a ∈ W, 1 ≤ a :=
    fun W hW a ha => ((VandeheyAut.mem_boundedWords m W |>.mp hW).2 a ha).1
  -- the measure-side bound on the finite family
  have hmeas : ∑ W ∈ F, bfun W * (gaussMeasure (cfCylinder W)).toReal < ε / 3 := by
    have h := sum_gaussMeasure_windowBound_le δ t q hC hθ0 hθ1 hc0 hc1 hpin hK F
      (by intro W hW; rw [hFlen W hW])
    have hcomm : ∑ W ∈ F, (gaussMeasure (cfCylinder W)).toReal * bfun W
        = ∑ W ∈ F, bfun W * (gaussMeasure (cfCylinder W)).toReal :=
      Finset.sum_congr rfl fun W _ => mul_comm _ _
    rw [hcomm] at h
    exact lt_of_le_of_lt h hKε
  -- the digit-tail side
  set τZ : ℝ := 1 - ∑ k ∈ Finset.Icc 1 Z, (gaussMeasure (cfCylinder [k])).toReal with hτZ
  have htail : B * (m : ℝ) * τZ < ε / 3 := by
    have h1 : τZ ≤ Real.log (1 + 1 / ((Z : ℝ) + 1)) / Real.log 2 := digitTail_le Z
    have h2 : B * (m : ℝ) * τZ
        ≤ B * (m : ℝ) * (Real.log (1 + 1 / ((Z : ℝ) + 1)) / Real.log 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  -- the three convergent pieces
  set f₁ : ℕ → ℝ := fun n => ∑ W ∈ F, bfun W * ((((Finset.range n).filter
    (fun i => W = cfWindow x i m)).card : ℝ) / n) with hf₁
  set f₂ : ℕ → ℝ := fun n => B * (m : ℝ) * ((((Finset.range n).filter
    (fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ Z))).card : ℝ) / n) with hf₂
  set f₃ : ℕ → ℝ := fun n => B * (m : ℝ) * (m : ℝ) / n with hf₃
  have ht₁ : Tendsto f₁ atTop (nhds (∑ W ∈ F, bfun W * (gaussMeasure (cfCylinder W)).toReal)) :=
    tendsto_weighted_window_freq hx F (by omega) hFlen hFpos bfun
  have ht₂ : Tendsto f₂ atTop (nhds (B * (m : ℝ) * τZ)) :=
    (tendsto_digitTail_freq hx Z).const_mul (B * (m : ℝ))
  have ht₃ : Tendsto f₃ atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (B * (m : ℝ) * (m : ℝ))
  have htot : Tendsto (fun n => f₁ n + f₂ n + f₃ n) atTop
      (nhds ((∑ W ∈ F, bfun W * (gaussMeasure (cfCylinder W)).toReal)
        + B * (m : ℝ) * τZ + 0)) := (ht₁.add ht₂).add ht₃
  have hΛ : (∑ W ∈ F, bfun W * (gaussMeasure (cfCylinder W)).toReal)
      + B * (m : ℝ) * τZ + 0 < ε := by linarith
  have hev := htot.eventually (gt_mem_nhds hΛ)
  filter_upwards [hev, eventually_gt_atTop 0] with n hfn hn
  -- assemble
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsplit := sum_windowBound_le_split δ t q c hK Z x n
  have hsum_mul : (∑ W ∈ F, bfun W * ((((Finset.range n).filter
        (fun i => W = cfWindow x i m)).card : ℝ) / n)) * n
      = ∑ W ∈ F, bfun W * (((Finset.range n).filter
        (fun i => W = cfWindow x i m)).card : ℝ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun W _ => ?_
    field_simp
  have halg : ((f₁ n + f₂ n + f₃ n) * n)
      = (∑ W ∈ F, bfun W * (((Finset.range n).filter
            (fun i => W = cfWindow x i m)).card : ℝ))
        + B * (m : ℝ) * ((((Finset.range n).filter
            (fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ Z))).card : ℝ) + (m : ℝ)) := by
    simp only [hf₁, hf₂, hf₃]
    rw [add_mul, add_mul, hsum_mul]
    field_simp
    ring
  have hlt : (f₁ n + f₂ n + f₃ n) * n < ε * n :=
    mul_lt_mul_of_pos_right hfn hnR
  rw [halg] at hlt
  calc ∑ i ∈ Finset.range n,
        VandeheyCocycle.windowBound δ t q c K (cfWindow x i (K + q.length))
      ≤ (∑ W ∈ F, bfun W * (((Finset.range n).filter
            (fun i => W = cfWindow x i m)).card : ℝ))
        + B * (m : ℝ) * ((((Finset.range n).filter
            (fun i => ¬ (1 ≤ cfDigit x i ∧ cfDigit x i ≤ Z))).card : ℝ) + (m : ℝ)) := hsplit
    _ ≤ ε * n := le_of_lt hlt

/-! ## The payoff: the class automaton, unconditionally -/

/-- **Vandehey §3, repaired.**  For a prime `D`, the class cocycle — the Gauss map read modulo
`D`, i.e. the `Γ₀(D)`-coset of the CF matrix product — equidistributes jointly with digit windows
along **every** CF-normal orbit, with reference weight `1/|ℙ¹(ℤ/D)|`.

This is the statement Vandehey buys from the Airey–Mance-refuted Moshchevitin–Shkredov theorem.
Here it is unconditional: the hot-spot criterion is never used, and no tightness hypothesis is
needed, because the transfer-operator pin `stateHorizonIntegral_pin` supplies a *quantitative*
equidistribution with geometric rate, and `ClassEquidistribution` is its Cesàro consequence. -/
theorem classEquidistribution_classStep (D : ℕ) [Fact (Nat.Prime D)]
    (t : VandeheyClass.ClassSpace D) (q : List ℕ) :
    VandeheyCocycle.ClassEquidistribution (VandeheyClass.classStep D) t q := by
  have hreach : ∀ d s : VandeheyClass.ClassSpace D, ∃ w : List ℕ, w.length = 3 ∧
      (∀ a ∈ w, 1 ≤ a) ∧ runState (VandeheyClass.classStep D) d w = s := by
    intro d s
    obtain ⟨w, hlen, hpos, hrun⟩ := VandeheyRenyi.Doeblin.exists_classWord_three d s
    exact ⟨w, hlen, hpos, hrun⟩
  obtain ⟨C, θ, hC, hθ0, hθ1, hpin⟩ :=
    stateHorizonIntegral_pin (VandeheyClass.classStep D) (measurableSet_cfCylinder q)
      (cfCylinder_subset_Ioo q) 3 (by norm_num) hreach
      (fun a => VandeheyRenewal.classStep_bijective a)
  have hcard : 0 < Fintype.card (VandeheyClass.ClassSpace D) := Fintype.card_pos
  have hc0 : (0 : ℝ) ≤ (Fintype.card (VandeheyClass.ClassSpace D) : ℝ)⁻¹ := by positivity
  have hc1 : (Fintype.card (VandeheyClass.ClassSpace D) : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    exact_mod_cast hcard
  exact classEquidistribution_of_pin (VandeheyClass.classStep D) t q hC hθ0 hθ1 hc0 hc1
    (fun n e τ hτ => hpin n e t τ hτ)

/-- **The joint (window, class) frequency converges, to an `x`-independent value.**  Combining
`classEquidistribution_classStep` with the already-proved transfer principle: along every
CF-normal `x` and from every initial class, the frequency of positions where the digit window
spells `q` *and* the class equals `t` converges to `γ(I_q)/|ℙ¹(ℤ/D)|`. -/
theorem tendsto_jointCount_classStep (D : ℕ) [Fact (Nat.Prime D)]
    (t : VandeheyClass.ClassSpace D) {q : List ℕ} (hq : q ≠ []) (hqpos : ∀ a ∈ q, 1 ≤ a) :
    ∃ L : ℝ, ∀ (s₀ : VandeheyClass.ClassSpace D) (x : ℝ), IsCFNormal x →
      Tendsto (fun n => (jointCount (VandeheyClass.classStep D) s₀ t q x n : ℝ) / n) atTop
        (nhds (L * (gaussMeasure (cfCylinder q)).toReal)) :=
  VandeheyCocycle.tendsto_jointCount_of_classEquidistribution
    (classEquidistribution_classStep D t q) hq hqpos


/-! ## The general engine: equidistribution from transitivity alone

With `VandeheyState.stateHorizonIntegral_pin_of_reach` in hand, `ClassEquidistribution` needs
**only** that the automaton is transitive with a uniform word length.  No bijectivity, hence no
uniform invariant law, hence no computation of the limiting constant — `classEquidistribution_of_pin`
was always willing to take an unnamed `c ∈ [0,1]`.

This is the form the Raney transducer of `VandeheyRaney.lean` will be fed to: its digit steps
are demonstrably *not* injective (`Mat2.vandeheyStep_not_terminating`'s companion probe), so
the `classStep` route through `VandeheyRenewal.classStep_bijective` is unavailable to it.
-/

/-- **`ClassEquidistribution` from transitivity alone.**  A finite automaton reading CF digits,
in which every ordered pair of states is joined by a genuine word of one fixed length `M ≥ 2`,
equidistributes jointly with digit windows along every CF-normal orbit. -/
theorem classEquidistribution_of_reach [Nonempty S] (δ : S → ℕ → S) (t : S) (q : List ℕ)
    (M : ℕ) (hM : 2 ≤ M)
    (hreach : ∀ d s : S, ∃ w : List ℕ, w.length = M ∧ (∀ a ∈ w, 1 ≤ a) ∧
      runState δ d w = s) :
    VandeheyCocycle.ClassEquidistribution δ t q := by
  obtain ⟨c, C, θ, hc0, hc1, hC, hθ0, hθ1, hpin⟩ :=
    VandeheyState.stateHorizonIntegral_pin_of_reach δ (measurableSet_cfCylinder q)
      (cfCylinder_subset_Ioo q) M hM hreach t
  exact classEquidistribution_of_pin δ t q hC hθ0 hθ1 hc0 hc1 hpin

/-- **The joint (window, state) frequency converges, for any transitive finite automaton.**
The limit mentions neither the CF-normal point `x` nor the initial state.  This is exactly the
`VandeheyUniformFreq` contract, one automaton at a time. -/
theorem tendsto_jointCount_of_reach [Nonempty S] (δ : S → ℕ → S) (t : S)
    (M : ℕ) (hM : 2 ≤ M)
    (hreach : ∀ d s : S, ∃ w : List ℕ, w.length = M ∧ (∀ a ∈ w, 1 ≤ a) ∧
      runState δ d w = s)
    {q : List ℕ} (hq : q ≠ []) (hqpos : ∀ a ∈ q, 1 ≤ a) :
    ∃ L : ℝ, ∀ (s₀ : S) (x : ℝ), IsCFNormal x →
      Tendsto (fun n => (jointCount δ s₀ t q x n : ℝ) / n) atTop
        (nhds (L * (gaussMeasure (cfCylinder q)).toReal)) :=
  VandeheyCocycle.tendsto_jointCount_of_classEquidistribution
    (classEquidistribution_of_reach δ t q M hM hreach) hq hqpos

#print axioms classEquidistribution_of_reach
#print axioms tendsto_jointCount_of_reach

end VandeheyTwo

end NormalNumbers
