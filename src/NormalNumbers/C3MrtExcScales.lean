/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtTTThm31

/-!
# The exceptional set of scales is a genuine obstruction — machine-checked

Lap 62 stated Tao–Teräväinen Theorem 3.1(ii) faithfully (`TwoPointNaturalCorrelation`): the
`L^{-c}` saving holds for all scales `N ∈ [√X, X]` **outside** an exceptional set `E` of
logarithmic density `≪ L^{-c}`.  `LogToNaturalCorrelation K`, by contrast, demands
`Tendsto … atTop (𝓝 0)` — a bound at *every* scale.

It would be easy, and wrong, to record "density `o(1)`, so morally every scale".  This file
proves the gap is real, as a theorem rather than a remark.

`exceptional_scales_not_tendsto`: there is a set `E ⊆ ℕ` of scale-indices of **density zero**
which nevertheless contains **arbitrarily long runs**, so the sequence `1_E` tends to `0`
along the complement of `E` (trivially: it is `0` there) and does not tend to `0` at all.

The witness is `E = ⋃_{j ≥ 1} [j⁴, j⁴ + j)`: the `j`-th block has length `j → ∞`, while
`|E ∩ [0,K)| ≤ 4√K`.  In the multiplicative scale variable of Theorem 3.1 a run of length `j`
in the exponent is a block `[A, 2^j A]` of unbounded ratio — precisely the configuration that
defeats every "fill in between two good scales" rescue.

**Verdict for the ledger.**  The `D = 2` row splits into a *scale-exceptional* natural-density
rung, which is a published theorem (`TwoPointNaturalCorrelation`), and the every-scale version
`LogToNaturalCorrelation 2`, which this file shows cannot be recovered from it by any purely
measure-theoretic argument about the scale set.  Tao–Teräväinen say the same in print
(`papers/tao-teravainen-2025-quantitative-correlations.txt:2997`).

**Refuted this lap (do not re-chase).**  The Fubini rescue: for a *fixed* scale `N`, vary `X`
over `[N, N²]` and hope `N ∉ E(X)` for some admissible `X`.  Swapping the order of integration
in `∫_N^{N²} ∫_{E(X)} dt/t · dX/X` bounds the `X`-measure of bad `X` only *for most `t`*, not
for a given `t`; the exceptional set reappears one level up.  Theorem 3.1 is a black box in
`X`, so nothing stronger is available from the statement alone.
-/

open Filter Finset Topology

namespace NormalNumbers

namespace CastingOut

/-- The witness set: the union of the blocks `[j⁴, j⁴ + j)` for `j ≥ 1`. -/
def excScales : Set ℕ := {k | ∃ j : ℕ, 0 < j ∧ j ^ 4 ≤ k ∧ k < j ^ 4 + j}

lemma excScales_pow_mem {j : ℕ} (hj : 0 < j) : j ^ 4 ∈ excScales := ⟨j, hj, le_rfl, by omega⟩

noncomputable instance : DecidablePred (· ∈ excScales) := Classical.decPred _

/-- **Arbitrarily long runs.**  The block starting at `(L+1)⁴` has length `L+1`. -/
theorem excScales_long_runs (L : ℕ) : ∃ k : ℕ, ∀ i ≤ L, k + i ∈ excScales :=
  ⟨(L + 1) ^ 4, fun i hi => ⟨L + 1, Nat.succ_pos L, by omega, by omega⟩⟩

/-- The block index of `k ∈ E` is `⌊k^{1/4}⌋ = √(√k)` — so the block a point belongs to is
determined by the point, which is what makes the counting map injective. -/
lemma excScales_index {k j : ℕ} (hj : 0 < j) (h1 : j ^ 4 ≤ k) (h2 : k < j ^ 4 + j) :
    Nat.sqrt (Nat.sqrt k) = j := by
  have hup : j ^ 4 + j ≤ (j + 1) ^ 4 := by nlinarith [sq_nonneg j, hj]
  have hle : j ≤ Nat.sqrt (Nat.sqrt k) := by
    rw [Nat.le_sqrt, Nat.le_sqrt]
    calc j * j * (j * j) = j ^ 4 := by ring
      _ ≤ k := h1
  have hlt : Nat.sqrt (Nat.sqrt k) < j + 1 := by
    rw [Nat.sqrt_lt, Nat.sqrt_lt]
    calc k < j ^ 4 + j := h2
      _ ≤ (j + 1) ^ 4 := hup
      _ = (j + 1) * (j + 1) * ((j + 1) * (j + 1)) := by ring
  omega

/-- **Density zero — the counting bound.**  `|E ∩ [0,K)| ≤ (s+1)²` with `s = √(√K)`. -/
theorem excScales_card_le (K : ℕ) :
    ((Finset.range K).filter (fun k => k ∈ excScales)).card
      ≤ (Nat.sqrt (Nat.sqrt K) + 1) ^ 2 := by
  classical
  set s : ℕ := Nat.sqrt (Nat.sqrt K) with hs
  set T : Finset (ℕ × ℕ) := (Finset.range (s + 1)) ×ˢ (Finset.range (s + 1)) with hT
  have hTcard : T.card = (s + 1) ^ 2 := by
    rw [hT, Finset.card_product, Finset.card_range]; ring
  rw [← hTcard]
  refine Finset.card_le_card_of_injOn
    (fun k => (Nat.sqrt (Nat.sqrt k), k - (Nat.sqrt (Nat.sqrt k)) ^ 4)) ?_ ?_
  · intro k hk
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk
    simp only []
    obtain ⟨j, hj, h1, h2⟩ := hk.2
    have hjk : Nat.sqrt (Nat.sqrt k) = j := excScales_index hj h1 h2
    have hjs : j ≤ s := by
      rw [hs, Nat.le_sqrt, Nat.le_sqrt]
      calc j * j * (j * j) = j ^ 4 := by ring
        _ ≤ k := h1
        _ ≤ K := le_of_lt hk.1
    rw [Finset.mem_coe, hT, Finset.mem_product, Finset.mem_range, Finset.mem_range, hjk]
    exact ⟨by omega, by omega⟩
  · intro k hk k' hk' hEq
    rw [Finset.coe_filter, Set.mem_setOf_eq] at hk hk'
    obtain ⟨j, hj, h1, h2⟩ := hk.2
    obtain ⟨j', hj', h1', h2'⟩ := hk'.2
    have hjk : Nat.sqrt (Nat.sqrt k) = j := excScales_index hj h1 h2
    have hjk' : Nat.sqrt (Nat.sqrt k') = j' := excScales_index hj' h1' h2'
    simp only [Prod.ext_iff] at hEq
    rw [hjk, hjk'] at hEq
    obtain ⟨hje, hde⟩ := hEq
    subst hje
    omega

/-- `s⁴ ≤ K`, i.e. `s = √(√K)` really is a fourth root. -/
lemma excScales_sq_le (K : ℕ) : (Nat.sqrt (Nat.sqrt K)) ^ 2 ≤ Nat.sqrt K := by
  exact Nat.sqrt_le' (Nat.sqrt K)

open scoped Classical in
/-- **Density zero.** -/
theorem excScales_density_zero :
    Filter.Tendsto
      (fun K : ℕ => (((Finset.range K).filter (fun k => k ∈ excScales)).card : ℝ) / (K : ℝ))
      atTop (𝓝 0) := by
  classical
  have hmain : ∀ K : ℕ, 1 ≤ K →
      (((Finset.range K).filter (fun k => k ∈ excScales)).card : ℝ) / (K : ℝ)
        ≤ 4 / Real.sqrt K := by
    intro K hK
    set s : ℕ := Nat.sqrt (Nat.sqrt K) with hs
    have hs1 : 1 ≤ s := by
      rw [hs, Nat.le_sqrt, Nat.le_sqrt]; simpa using hK
    have hcard : ((Finset.range K).filter (fun k => k ∈ excScales)).card ≤ 4 * s ^ 2 := by
      have := excScales_card_le K
      rw [← hs] at this
      nlinarith [this, hs1]
    have hsK : (s : ℝ) ^ 2 ≤ Real.sqrt K := by
      have h1 : (s ^ 2 : ℕ) ≤ Nat.sqrt K := excScales_sq_le K
      have h2 : (Nat.sqrt K : ℝ) ≤ Real.sqrt K := Real.nat_sqrt_le_real_sqrt
      exact le_trans (by exact_mod_cast h1) h2
    have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
    have hsqrt : Real.sqrt K * Real.sqrt K = (K : ℝ) := Real.mul_self_sqrt hKR.le
    have hsqrtpos : (0 : ℝ) < Real.sqrt K := Real.sqrt_pos.2 hKR
    rw [div_le_div_iff₀ hKR hsqrtpos]
    have hc : (((Finset.range K).filter (fun k => k ∈ excScales)).card : ℝ) ≤ 4 * (s : ℝ) ^ 2 := by
      exact_mod_cast hcard
    nlinarith [hc, hsK, hsqrtpos.le, hsqrt]
  refine squeeze_zero' (Filter.Eventually.of_forall fun K => by positivity)
    (Filter.eventually_atTop.2 ⟨1, hmain⟩) ?_
  have hten : Filter.Tendsto (fun K : ℕ => Real.sqrt K) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have := hten.inv_tendsto_atTop.const_mul (4 : ℝ)
  simpa [div_eq_mul_inv] using this

open scoped Classical in
/-- **THE OBSTRUCTION, machine-checked.**  A density-zero set of scale-indices, containing
arbitrarily long runs, on which a `1`-bounded sequence can sit: the sequence vanishes off the
exceptional set, yet does not tend to `0`.  Hence no bound valid only off a density-zero set of
scales can yield `Tendsto … atTop (𝓝 0)`, which is what `LogToNaturalCorrelation K` demands. -/
theorem exceptional_scales_not_tendsto :
    ∃ (E : Set ℕ) (a : ℕ → ℝ),
      (∀ k, 0 ≤ a k ∧ a k ≤ 1) ∧
      (∀ k, k ∉ E → a k = 0) ∧
      (∀ L : ℕ, ∃ k : ℕ, ∀ i ≤ L, k + i ∈ E) ∧
      Filter.Tendsto
        (fun K : ℕ => (((Finset.range K).filter (fun k => k ∈ E)).card : ℝ) / (K : ℝ))
        atTop (𝓝 0) ∧
      ¬ Filter.Tendsto a atTop (𝓝 0) := by
  classical
  refine ⟨excScales, fun k => if k ∈ excScales then 1 else 0, ?_, ?_,
    excScales_long_runs, excScales_density_zero, ?_⟩
  · intro k; by_cases h : k ∈ excScales <;> simp [h]
  · intro k hk; simp [hk]
  · intro hten
    have h1 : ∀ᶠ K : ℕ in atTop, |(if K ∈ excScales then (1 : ℝ) else 0) - 0| < 1 / 2 := by
      have := Metric.tendsto_atTop.1 hten (1 / 2) (by norm_num)
      obtain ⟨M, hM⟩ := this
      exact Filter.eventually_atTop.2 ⟨M, fun K hK => by
        have h := hM K hK
        rwa [Real.dist_eq] at h⟩
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 h1
    have hbig : (M + 1) ^ 4 ∈ excScales := excScales_pow_mem (Nat.succ_pos M)
    have hMle : M ≤ (M + 1) ^ 4 := by
      have h := Nat.le_self_pow (n := 4) (by norm_num) (M + 1)
      omega
    have := hM _ hMle
    rw [if_pos hbig] at this
    norm_num at this

#print axioms excScales_long_runs
#print axioms excScales_density_zero
#print axioms exceptional_scales_not_tendsto

end CastingOut

end NormalNumbers
