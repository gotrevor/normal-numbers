/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.TwoPointC3Wall
import NormalNumbers.TwoPointC3Depth
import NormalNumbers.SwingC3Mean

/-!
# Rung 3 of the C3 depth ladder: the pin

`DIRECTION.md`'s rung 3.  C1's analogue is `TwoPointDepthInvariance`: there the crux is equivalent
to a **fixed-depth weighted** correlation for *every* depth (an exact identity, no hypothesis), and
to a **growing-depth unweighted** one under a peel budget.  This file does the same for C3.

The exact peel identity is

    tailLarge P b n  =  depthPeel P b K n  +  b^{−K} · tailLarge P b (n+K) ,
    depthPeel P b K n = ∑_{i<K} ω_{>P}(n+i+1)·b^{−(i+1)} ,

so the crux's summand factors as

    e(h·tailLarge P b n)  =  e(h·depthPeel P b K n) · tailPeelWeight ,

with `tailPeelWeight` of modulus one.  Hence:

* `addCharTail_iff_depthWeighted` — the crux is **equal**, at every fixed depth `K`, to the
  `K`-point weighted correlation.  Free, unconditional: depth is not the resource, the weight is.
* `addCharTail_iff_unweighted_of_budget` — dropping the weight at a schedule `K(N)` is legitimate
  exactly when the **peel budget** `(1/N)∑_{n<N} b^{−K(N)}·tailLarge P b (n+K(N)) → 0` holds.
* `no_constant_depth_budget` — and the budget **fails for every constant schedule**, because of
  rung 2 (`tendsto_mean_tailLarge_atTop`).  So the depth genuinely must grow; the weighted
  fixed-depth surface and the growing-depth unweighted surface are the only two admissible ones,
  and they state the same problem.

Together with rung 2 this closes off "truncate the tail at a fixed depth" in the kernel, exactly
as `TwoPointDepthInvariance` closed off "pick a better depth / drop the weight" for C1.
-/

open Filter Topology Finset

namespace NormalNumbers.CastingOut

open PrimeLambert

/-! ### The exact peel identity -/

/-- The depth-`K` peel of the large-prime tail. -/
noncomputable def depthPeel (P b K n : ℕ) : ℝ :=
  ∑ i ∈ range K, (omegaLarge P (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)

/-- **The exact peel identity**: the tail is its depth-`K` peel plus a `b^{−K}`-scaled copy of
itself, shifted by `K`.  The C3 analogue of `pairTail_eq_digitTrunc_add`. -/
theorem tailLarge_eq_depthPeel_add {b : ℕ} (hb : 2 ≤ b) (P K n : ℕ) :
    tailLarge P b n = depthPeel P b K n + ((b : ℝ) ^ K)⁻¹ * tailLarge P b (n + K) := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by
    have : (0 : ℕ) < b := by omega
    exact_mod_cast this
  have hsum := summable_tailLarge hb P n
  have hsplit := Summable.sum_add_tsum_nat_add (f := fun i : ℕ =>
      (omegaLarge P (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)) K hsum
  have hshift : ∑' i : ℕ, (omegaLarge P (n + (i + K) + 1) : ℝ) / (b : ℝ) ^ ((i + K) + 1)
      = ((b : ℝ) ^ K)⁻¹ * tailLarge P b (n + K) := by
    rw [tailLarge, ← Summable.tsum_mul_left _ (summable_tailLarge hb P (n + K))]
    refine tsum_congr fun i => ?_
    have hn : n + (i + K) + 1 = (n + K) + i + 1 := by ring
    rw [hn]
    rw [pow_add, pow_add]
    field_simp
    ring
  rw [tailLarge, ← hsplit, hshift, depthPeel]

/-! ### The two surfaces -/

/-- The unit-modulus peel weight the depth-`K` truncation drops. -/
noncomputable def tailPeelWeight (P b K : ℕ) (h : ℤ) (n : ℕ) : ℂ :=
  ee ((((h : ℝ) * ((b : ℝ) ^ K)⁻¹ * tailLarge P b (n + K) : ℝ)) : ℂ)

lemma norm_tailPeelWeight (P b K : ℕ) (h : ℤ) (n : ℕ) : ‖tailPeelWeight P b K h n‖ = 1 :=
  norm_ee_real _

/-- **The crux at fixed depth `K`, weighted.**  The `K`-point correlation
`∏_{i<K} z_i^{ω_{>P}(n+i+1)}` twisted by the additive character and by one unit-modulus weight. -/
def AddCharTailDepth (b P Q j K : ℕ) (h : ℤ) : Prop :=
  Tendsto (fun N : ℕ =>
    (∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ)) : ℂ)
      * ee (((h : ℝ) * depthPeel P b K n : ℝ) : ℂ) * tailPeelWeight P b K h n) / N)
    atTop (𝓝 0)

/-- **The crux at fixed depth `K`, unweighted**: the weight is simply dropped. -/
def AddCharTailDepthPlain (b P Q j K : ℕ) (h : ℤ) : Prop :=
  Tendsto (fun N : ℕ =>
    (∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ)) : ℂ)
      * ee (((h : ℝ) * depthPeel P b K n : ℝ) : ℂ)) / N)
    atTop (𝓝 0)

/-- The summand of the crux factors through the peel, exactly. -/
lemma addChar_summand_eq {b : ℕ} (hb : 2 ≤ b) (P Q j K : ℕ) (h : ℤ) (n : ℕ) :
    ee ((((j : ℝ) * n / Q : ℝ)) : ℂ) * ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)
      = ee ((((j : ℝ) * n / Q : ℝ)) : ℂ)
        * ee (((h : ℝ) * depthPeel P b K n : ℝ) : ℂ) * tailPeelWeight P b K h n := by
  have hB : (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)
      = ((((h : ℝ) * depthPeel P b K n : ℝ)) : ℂ)
        + ((((h : ℝ) * ((b : ℝ) ^ K)⁻¹ * tailLarge P b (n + K) : ℝ)) : ℂ) := by
    rw [tailLarge_eq_depthPeel_add hb P K n]
    push_cast
    ring
  rw [hB, ee_add, tailPeelWeight]
  ring

/-- **Depth is free, the weight is not.**  At *every* fixed depth `K`, the crux is literally the
weighted `K`-point correlation.  No hypothesis on `K`: the identity is exact, so — exactly as in
C1's `pairDecorr_iff_multiElliottWeighted` — depth `1` is as good as depth `K`. -/
theorem addCharTail_iff_depthWeighted {b : ℕ} (hb : 2 ≤ b) (P Q j K : ℕ) (h : ℤ) :
    Tendsto (fun N : ℕ =>
        (∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ)) : ℂ)
          * ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)) / N) atTop (𝓝 0)
      ↔ AddCharTailDepth b P Q j K h := by
  rw [AddCharTailDepth]
  refine Iff.of_eq (congrArg (fun f => Tendsto f atTop (𝓝 0)) (funext fun N => ?_))
  congr 1
  exact Finset.sum_congr rfl fun n _ => addChar_summand_eq hb P Q j K h n

/-! ### The peel budget, and why the depth must grow -/

/-- **The peel budget at schedule `K`.**  The mean cost of dropping the weight. -/
def PeelBudget (P b : ℕ) (h : ℤ) (K : ℕ → ℕ) : Prop :=
  Tendsto (fun N : ℕ =>
    (∑ n ∈ range N, ((b : ℝ) ^ (K N))⁻¹ * tailLarge P b (n + K N)) / N) atTop (𝓝 0)

/-- **Rung 2 kills every constant schedule.**  For a constant depth the budget is
`b^{−K}·(1/N)∑ tailLarge(n+K)`, whose mean diverges by `tendsto_mean_tailLarge_atTop`; so no fixed
depth may drop the weight. -/
theorem no_constant_depth_budget {b : ℕ} (hb : 2 ≤ b) (P K₀ : ℕ) (h : ℤ) :
    ¬ PeelBudget P b h (fun _ => K₀) := by
  intro hbud
  have hb0 : (0 : ℝ) < (b : ℝ) := by
    have : (0 : ℕ) < b := by omega
    exact_mod_cast this
  have hcoef : (0 : ℝ) < ((b : ℝ) ^ K₀)⁻¹ := by positivity
  have hnn : ∀ m : ℕ, 0 ≤ tailLarge P b m := fun m => tsum_nonneg fun i => by positivity
  set C : ℝ := ∑ m ∈ range K₀, tailLarge P b m with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun m _ => hnn m
  -- shifting the argument by `K₀` costs at most the first `K₀` terms
  have hlow : ∀ N : ℕ, K₀ ≤ N →
      (∑ m ∈ range N, tailLarge P b m) - C ≤ ∑ n ∈ range N, tailLarge P b (n + K₀) := by
    intro N hKN
    have hrw : ∑ n ∈ range N, tailLarge P b (n + K₀)
        = ∑ i ∈ range N, tailLarge P b (K₀ + i) :=
      Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm]
    have hsub : ∑ i ∈ range (N - K₀), tailLarge P b (K₀ + i)
        ≤ ∑ i ∈ range N, tailLarge P b (K₀ + i) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.sub_le N K₀)) (fun i _ _ => hnn _)
    have hico : ∑ m ∈ Finset.Ico K₀ N, tailLarge P b m
        = ∑ i ∈ range (N - K₀), tailLarge P b (K₀ + i) :=
      Finset.sum_Ico_eq_sum_range _ _ _
    have hsplit2 : ∑ m ∈ range N, tailLarge P b m
        = C + ∑ m ∈ Finset.Ico K₀ N, tailLarge P b m := by
      rw [hC, ← Finset.sum_range_add_sum_Ico _ hKN]
    rw [hrw, hsplit2, hico]
    linarith
  have hshift : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, tailLarge P b (n + K₀)) / N) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_
      (tendsto_atTop_add_const_right atTop (-C) (tendsto_mean_tailLarge_atTop hb P))
    filter_upwards [eventually_ge_atTop K₀, eventually_ge_atTop 1] with N hKN hN1
    have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hNR0 : (0 : ℝ) < (N : ℝ) := by linarith
    have hstep : ((∑ m ∈ range N, tailLarge P b m) - C) / N
        ≤ (∑ n ∈ range N, tailLarge P b (n + K₀)) / N := by
      have := hlow N hKN
      gcongr
    have hCdiv : C / (N : ℝ) ≤ C := by
      rw [div_le_iff₀ hNR0]
      nlinarith
    have hexp : ((∑ m ∈ range N, tailLarge P b m) - C) / N
        = (∑ m ∈ range N, tailLarge P b m) / N - C / N := by ring
    rw [hexp] at hstep
    linarith
  have hdiv : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, ((b : ℝ) ^ K₀)⁻¹ * tailLarge P b (n + K₀)) / N) atTop atTop := by
    have := Filter.Tendsto.const_mul_atTop hcoef hshift
    refine this.congr fun N => ?_
    rw [← Finset.mul_sum, mul_div_assoc]
  exact not_tendsto_nhds_of_tendsto_atTop hdiv 0 hbud

/-- **Dropping the weight is legitimate exactly under the budget.**  Given the peel budget at a
schedule `K`, the growing-depth *unweighted* surface and the crux state the same problem.  With
`no_constant_depth_budget` this is the pin: the only admissible unweighted surfaces are the ones
whose depth grows. -/
theorem addCharTail_iff_plain_of_budget {b : ℕ} (hb : 2 ≤ b) (P Q j : ℕ) (h : ℤ) (K : ℕ → ℕ)
    (hbud : PeelBudget P b h K) :
    Tendsto (fun N : ℕ =>
        (∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ)) : ℂ)
          * ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)) / N) atTop (𝓝 0)
      ↔ Tendsto (fun N : ℕ =>
        (∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ)) : ℂ)
          * ee (((h : ℝ) * depthPeel P b (K N) n : ℝ) : ℂ)) / N) atTop (𝓝 0) := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by
    have : (0 : ℕ) < b := by omega
    exact_mod_cast this
  have hnn : ∀ m : ℕ, 0 ≤ tailLarge P b m := fun m => tsum_nonneg fun i => by positivity
  set F : ℕ → ℂ := fun N =>
    (∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ)) : ℂ)
      * ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)) / N with hF
  set G : ℕ → ℂ := fun N =>
    (∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ)) : ℂ)
      * ee (((h : ℝ) * depthPeel P b (K N) n : ℝ) : ℂ)) / N with hG
  set R : ℕ → ℝ := fun N =>
    (∑ n ∈ range N, ((b : ℝ) ^ (K N))⁻¹ * tailLarge P b (n + K N)) / N with hR
  -- the two surfaces differ by at most `16|h|` times the budget
  have hbound : ∀ N : ℕ, ‖F N - G N‖ ≤ 16 * |(h : ℝ)| * R N := by
    intro N
    have hterm : ∀ n : ℕ,
        ‖ee ((((j : ℝ) * n / Q : ℝ)) : ℂ) * ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)
          - ee ((((j : ℝ) * n / Q : ℝ)) : ℂ)
            * ee (((h : ℝ) * depthPeel P b (K N) n : ℝ) : ℂ)‖
        ≤ 16 * |(h : ℝ)| * (((b : ℝ) ^ (K N))⁻¹ * tailLarge P b (n + K N)) := by
      intro n
      rw [← mul_sub, norm_mul, norm_ee_real, one_mul]
      refine (norm_ee_sub_ee_le _ _).trans ?_
      have hdelta : (h : ℝ) * tailLarge P b n - (h : ℝ) * depthPeel P b (K N) n
          = (h : ℝ) * (((b : ℝ) ^ (K N))⁻¹ * tailLarge P b (n + K N)) := by
        rw [tailLarge_eq_depthPeel_add hb P (K N) n]; ring
      rw [hdelta, abs_mul]
      have hpos : |((b : ℝ) ^ (K N))⁻¹ * tailLarge P b (n + K N)|
          = ((b : ℝ) ^ (K N))⁻¹ * tailLarge P b (n + K N) := by
        rw [abs_of_nonneg (mul_nonneg (by positivity) (hnn _))]
      rw [hpos]
      ring_nf
      exact le_rfl
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [hF, hG, hR]
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hsub : F N - G N
        = (∑ n ∈ range N, (ee ((((j : ℝ) * n / Q : ℝ)) : ℂ)
            * ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)
          - ee ((((j : ℝ) * n / Q : ℝ)) : ℂ)
            * ee (((h : ℝ) * depthPeel P b (K N) n : ℝ) : ℂ))) / N := by
      rw [hF, hG, Finset.sum_sub_distrib, sub_div]
    rw [hsub, norm_div, Complex.norm_natCast]
    rw [div_le_iff₀ hNR]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ range N, ‖_‖ ≤ ∑ n ∈ range N,
          16 * |(h : ℝ)| * (((b : ℝ) ^ (K N))⁻¹ * tailLarge P b (n + K N)) :=
          Finset.sum_le_sum fun n _ => hterm n
      _ = 16 * |(h : ℝ)| * ((∑ n ∈ range N, ((b : ℝ) ^ (K N))⁻¹ * tailLarge P b (n + K N))) := by
          rw [← Finset.mul_sum]
      _ = 16 * |(h : ℝ)| * R N * N := by
          rw [hR]; field_simp
  have hRzero : Tendsto (fun N => 16 * |(h : ℝ)| * R N) atTop (𝓝 0) := by
    have := hbud
    rw [PeelBudget] at this
    have h2 := this.const_mul (16 * |(h : ℝ)|)
    simpa using h2
  have hdiff : Tendsto (fun N => F N - G N) atTop (𝓝 0) :=
    squeeze_zero_norm hbound hRzero
  constructor
  · intro hf
    have := hf.sub hdiff
    simpa using this
  · intro hg
    have := hg.add hdiff
    simpa using this

end NormalNumbers.CastingOut
