/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyOffset

/-!
# Every position of every sampled window, at the implemented schedule

`G4EntropyOffset.abs_posAvg_sub_le` proved, for an abstract `FinLaw`, that a per-coordinate
entropy deficit of `δ` bits controls the frequency of an `ℓ`-block word over **all** `m − ℓ + 1`
positions of the window — not just the `⌊m/ℓ⌋` aligned ones of `G4EntropyTiling`.  That bound was
never connected to `G₄`.  This module renders it at the base-four schedule, mirroring
`G4EntropyTiling`'s last three theorems:

* `posAt_blockVal` — the digit dictionary for `posAt`: the `ℓ`-block at position `p` of the
  `m`-bit window of `y` at `q` is the `ℓ`-bit window of `y` at `q + p` (for `p + ℓ ≤ m`).  This is
  `blkAt_blockVal` with `jℓ` replaced by an arbitrary `p`, and it is the general-`p` form the
  lap-36 handoff asked for.
* `Sched.posFreq` and `abs_posFreq_sub_le_of_deficit` — the capacity bound at the schedule, with
  the deficit hypothesis *verbatim* `abs_blockFreqT_sub_le_of_deficit`'s.
* `abs_posFreq_sub_le_primeLambertFour` — `entropy_E1`'s `δ = 50√K` at `m_K = K/4`, giving
  `2√(400 log 2 · ℓ/√K)` whenever `2ℓ ≤ m_K`; the aligned bound's constant was `200`.
* `tendsto_occursCountP_primeLambertFour` — **the endpoint**: for every finite binary word `v`,

    `#{(n,α,p) : OccursAt 2 G₄ v (2·kIdx(n,α) + p)} / (|P_K|·|Atom_K|·(m_K−|v|+1))  →  2^{−|v|}`

  — every word occurs with its correct frequency among **all** positions of `G₄`'s sampled
  windows, over the very predicate `isDisjunctive_two` is built from.  Strictly stronger than the
  aligned `tendsto_occursCountT_primeLambertFour`, which sees only a `1/ℓ` fraction of them.

**This is not a normality claim.**  The sampled positions have density `≤ ½(3/K⁴)^K`
(`G4EntropyPositions`, `G4EntropyScales`); see `REFLECTION-2026-09-14-entropy.md`.
-/

open Finset Filter

namespace NormalNumbers.G4Entropy

/-! ### The digit dictionary at an arbitrary position -/

/-- **`posAt` on digits.**  For `p + ℓ ≤ m` the `ℓ`-block at position `p` of the `m`-bit window
of `y` beginning at `q` is the `ℓ`-bit window of `y` beginning at `q + p`. -/
theorem posAt_blockVal (y : ℝ) (q m ℓ p : ℕ) (h : p + ℓ ≤ m) :
    posAt m ℓ p ⟨blockVal y q m, blockVal_lt y q m⟩
      = ⟨blockVal y (q + p) ℓ, blockVal_lt y (q + p) ℓ⟩ := by
  refine Fin.ext ?_
  rw [posAt_val]
  set t := m - p - ℓ with ht
  have hm : m = p + ℓ + t := by omega
  show blockVal y q m / 2 ^ t % 2 ^ ℓ = blockVal y (q + p) ℓ
  rw [show blockVal y q m = blockVal y q (p + ℓ + t) by rw [← hm], blockVal_div_mod]

end NormalNumbers.G4Entropy

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The all-positions sampled frequency of a word -/

/-- **The frequency of `w` among the `m_K − ℓ + 1` positions of the scale-`i` sampled windows.**
Every position that admits a full `ℓ`-block is counted, once. -/
noncomputable def posFreq (i ℓ : ℕ) (x : ℝ) (w : Fin (2 ^ ℓ)) : ℝ :=
  posAvg (kk i) ℓ (jointLawAt i x) w

/-- Atoms exist. -/
instance instNonemptyAtomAt (i : ℕ) : Nonempty (gridAt i).Atom := ⟨fun _ => 0⟩

/-- **The all-positions capacity inequality.**  A per-window deficit of `δ` bits controls every
word of length `ℓ ≤ m_K` at **every** window position to within `2√(log 2·ℓδ/(m_K−ℓ+1))`. -/
theorem abs_posFreq_sub_le_of_deficit (i ℓ : ℕ) (hℓ : 0 < ℓ) (hℓm : ℓ ≤ kk i) (x : ℝ)
    (w : Fin (2 ^ ℓ)) {δ : ℝ} (hδ : 0 < δ)
    (hdef : ((kk i : ℝ) - δ) * (Fintype.card (gridAt i).Atom : ℝ) ≤ (jointLawAt i x).H₂) :
    |posFreq i ℓ x w - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * δ / ((kk i : ℝ) - ℓ + 1)) :=
  abs_posAvg_sub_le hℓ hℓm (jointLawAt i x) w hδ hdef

/-! ### `G₄`: the same ceiling as the aligned tiling, twice the constant -/

/-- **The all-positions capacity bound at the implemented schedule.**  `entropy_E1` supplies
`δ = 50√K` and `m_K = K/4`, so for every `ℓ` with `2ℓ ≤ m_K`

    `|posFreq i ℓ G₄ w − 2^{−ℓ}| ≤ 2√(400 log 2 · ℓ/√K)`.

The aligned bound `abs_blockFreqT_sub_le_primeLambertFour` has constant `200`; halving the
denominator `m_K − ℓ + 1 ≥ m_K/2` is the entire difference. -/
theorem abs_posFreq_sub_le_primeLambertFour (i ℓ : ℕ) (hℓ : 0 < ℓ) (hℓm : 2 * ℓ ≤ kk i)
    (w : Fin (2 ^ ℓ)) :
    |posFreq i ℓ (primeLambertAtBase 4) w - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (400 * Real.log 2 * (ℓ : ℝ) / Real.sqrt (KK i)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : (0 : ℝ) < (KK i : ℝ) := by
    have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
    linarith
  have hS0 : 0 < Real.sqrt ((KK i : ℕ) : ℝ) := Real.sqrt_pos.2 hKpos
  have hδ : (0 : ℝ) < 50 * Real.sqrt (KK i) := by positivity
  have hE1 := entropy_E1 (K := KK i) (k₄ := kk i) rfl (KK_ge i)
  have hcard : (Fintype.card (gridAt i).Atom : ℝ) = (((KK i ^ 2 + 1) ^ KK i : ℕ) : ℝ) := by
    rw [card_Atom_gridAt i]
  have hdef : ((kk i : ℝ) - 50 * Real.sqrt (KK i)) * (Fintype.card (gridAt i).Atom : ℝ)
      ≤ (jointLawAt i (primeLambertAtBase 4)).H₂ := by
    rw [hcard, sub_mul]
    exact hE1.le
  have hmain := abs_posFreq_sub_le_of_deficit i ℓ hℓ (by omega) _ w hδ hdef
  refine hmain.trans ?_
  -- `m_K − ℓ + 1 ≥ m_K/2`, so the argument at most doubles
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hkR : (0 : ℝ) < (kk i : ℝ) := by
    have : 0 < kk i := by unfold kk; omega
    exact_mod_cast this
  have hhalf : (kk i : ℝ) / 2 ≤ (kk i : ℝ) - ℓ + 1 := by
    have : (2 : ℝ) * ℓ ≤ (kk i : ℝ) := by exact_mod_cast hℓm
    linarith
  have hden : (0 : ℝ) < (kk i : ℝ) - ℓ + 1 := by linarith
  have hstep : Real.log 2 * (ℓ : ℝ) * (50 * Real.sqrt (KK i)) / ((kk i : ℝ) - ℓ + 1)
      ≤ 400 * Real.log 2 * (ℓ : ℝ) / Real.sqrt (KK i) := by
    have hkk4 : (KK i : ℝ) = 4 * (kk i : ℝ) := by unfold KK; push_cast; ring
    have hsq : Real.sqrt ((KK i : ℕ) : ℝ) * Real.sqrt ((KK i : ℕ) : ℝ) = 4 * (kk i : ℝ) := by
      rw [Real.mul_self_sqrt hKpos.le, hkk4]
    rw [div_le_div_iff₀ hden hS0]
    have hkey : Real.log 2 * (ℓ : ℝ) * (50 * Real.sqrt (KK i)) * Real.sqrt ((KK i : ℕ) : ℝ)
        = 200 * Real.log 2 * (ℓ : ℝ) * (kk i : ℝ) := by
      linear_combination (50 * Real.log 2 * (ℓ : ℝ)) * hsq
    rw [hkey]
    nlinarith [mul_le_mul_of_nonneg_left hhalf
      (by positivity : (0:ℝ) ≤ 400 * Real.log 2 * (ℓ : ℝ))]
  have hpos1 : (0 : ℝ) ≤ Real.log 2 * (ℓ : ℝ) * (50 * Real.sqrt (KK i))
      / ((kk i : ℝ) - ℓ + 1) := by positivity
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hstep) (by norm_num)

/-- **The all-positions frequency theorem with a growing word length.**  Same ceiling as the
aligned version: every `ℓ(K) = o(√K)` is controlled, words free to vary with the scale. -/
theorem tendsto_posFreq_growing (ℓ : ℕ → ℕ) (hpos : ∀ᶠ i in atTop, 0 < ℓ i)
    (hle : ∀ᶠ i in atTop, 2 * ℓ i ≤ kk i)
    (hgrow : Tendsto (fun i => (ℓ i : ℝ) / Real.sqrt (KK i)) atTop (nhds 0))
    (w : ∀ i, Fin (2 ^ ℓ i)) :
    Tendsto (fun i => posFreq i (ℓ i) (primeLambertAtBase 4) (w i) - 1 / (2 : ℝ) ^ (ℓ i))
      atTop (nhds 0) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hinner : Tendsto (fun i => 400 * Real.log 2 * (ℓ i : ℝ) / Real.sqrt (KK i))
      atTop (nhds 0) := by
    have h := hgrow.const_mul (400 * Real.log 2)
    simp only [mul_zero] at h
    refine h.congr fun i => ?_
    rw [mul_div_assoc]
  have hsq : Tendsto (fun i => 2 * Real.sqrt (400 * Real.log 2 * (ℓ i : ℝ)
      / Real.sqrt (KK i))) atTop (nhds 0) := by
    have := hinner.sqrt
    simpa using this.const_mul (2 : ℝ)
  refine squeeze_zero_norm' ?_ hsq
  filter_upwards [hpos, hle] with i hp hl
  simpa [Real.norm_eq_abs] using abs_posFreq_sub_le_primeLambertFour i (ℓ i) hp hl (w i)

/-! ### The faithfulness rendering -/

open Classical in
/-- **The count rendering.**  `posFreq` is the density, among the `|P_K|·|Atom_K|·(m_K−ℓ+1)`
triples `(n, α, p)`, of those whose `ℓ`-block at window position `p` is `w`. -/
theorem posFreq_eq_count (i ℓ : ℕ) (x : ℝ) (w : Fin (2 ^ ℓ)) :
    posFreq i ℓ x w
      = (∑ c : (gridAt i).Atom × Fin (kk i - ℓ + 1),
            (((PK i).filter fun n =>
              posAt (kk i) ℓ (c.2 : ℕ) (ZVec (gridAt i) (kk i) x n c.1) = w).card : ℝ))
        / (((PK i).card : ℝ)
            * ((Fintype.card (gridAt i).Atom : ℝ) * ((kk i - ℓ + 1 : ℕ) : ℝ))) := by
  classical
  have hp : ∀ c : (gridAt i).Atom × Fin (kk i - ℓ + 1),
      ((jointLawAt i x).map (fun z => posAt (kk i) ℓ (c.2 : ℕ) (z c.1))).prob {w}
        = (((PK i).filter fun n =>
              posAt (kk i) ℓ (c.2 : ℕ) (ZVec (gridAt i) (kk i) x n c.1) = w).card : ℝ)
          / ((PK i).card : ℝ) := by
    intro c
    rw [FinLaw.prob, Finset.sum_singleton]
    exact map_empirical_p (apSample_nonempty (gridAt i) (b₀_lt_X_at i)) _ _ w
  have hsum : (∑ c : (gridAt i).Atom × Fin (kk i - ℓ + 1),
        ((jointLawAt i x).map (fun z => posAt (kk i) ℓ (c.2 : ℕ) (z c.1))).prob {w})
      = (∑ c : (gridAt i).Atom × Fin (kk i - ℓ + 1),
          (((PK i).filter fun n =>
            posAt (kk i) ℓ (c.2 : ℕ) (ZVec (gridAt i) (kk i) x n c.1) = w).card : ℝ))
        / ((PK i).card : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun c _ => hp c
  rw [posFreq, posAvg, hsum, div_div]

open Classical in
/-- **The digit rendering.**  The event is: the `ℓ` binary digits of `x` beginning at position
`2·kIdx(n,α) + p` spell `w`, for every window position `p ≤ m_K − ℓ`. -/
theorem posFreq_eq_digits (i ℓ : ℕ) (_hℓ : 0 < ℓ) (hℓm : ℓ ≤ kk i) (x : ℝ) (w : Fin (2 ^ ℓ)) :
    posFreq i ℓ x w
      = (∑ c : (gridAt i).Atom × Fin (kk i - ℓ + 1),
            (((PK i).filter fun n =>
              blockVal (Int.fract x) (2 * kIdx (gridAt i) n c.1 + (c.2 : ℕ)) ℓ
                = (w : ℕ)).card : ℝ))
        / (((PK i).card : ℝ)
            * ((Fintype.card (gridAt i).Atom : ℝ) * ((kk i - ℓ + 1 : ℕ) : ℝ))) := by
  classical
  rw [posFreq_eq_count i ℓ x w]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 2
  have hZ : ∀ n : ℕ, ZVec (gridAt i) (kk i) x n c.1
      = ⟨blockVal (Int.fract x) (2 * kIdx (gridAt i) n c.1) (kk i), blockVal_lt _ _ _⟩ :=
    fun n => Fin.ext (ZSample_eq_blockVal (gridAt i) (kk i) x n c.1)
  have hfit : (c.2 : ℕ) + ℓ ≤ kk i := by
    have := c.2.isLt
    omega
  refine Finset.filter_congr fun n _ => ?_
  rw [hZ n, posAt_blockVal _ _ _ _ _ hfit]
  exact ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩

open Classical in
/-- **The endpoint: every finite binary word, at EVERY position of the sampled windows.**
For every finite binary word `v`, the proportion of triples `(n, α, p)` at which `v` occurs in
the binary expansion of `G₄` at position `2·kIdx(n,α) + p` tends to `2^{−|v|}`.

`tendsto_occursCountT_primeLambertFour` is the aligned sub-count `p ∈ {0, ℓ, 2ℓ, …}`; this reads
every position, which is the predicate `NormalNumbers.IsNormal`/`isDisjunctive_two` is built from.
It is still a statement about the *sampled* positions only. -/
theorem tendsto_occursCountP_primeLambertFour (v : List ℕ) (hlen : 0 < v.length)
    (hv : ∀ i, ∀ h : i < v.length, v[i] < 2) :
    Tendsto (fun i =>
      (∑ c : (gridAt i).Atom × Fin (kk i - v.length + 1),
          (((PK i).filter fun n =>
            OccursAt 2 (primeLambertAtBase 4) v
              (2 * kIdx (gridAt i) n c.1 + (c.2 : ℕ))).card : ℝ))
        / (((PK i).card : ℝ)
            * ((Fintype.card (gridAt i).Atom : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ))))
      atTop (nhds (1 / (2 : ℝ) ^ v.length)) := by
  classical
  have hmain : Tendsto (fun i => posFreq i v.length (primeLambertAtBase 4)
      ⟨wordVal v, wordVal_lt hv⟩) atTop (nhds (1 / (2 : ℝ) ^ v.length)) := by
    have hgrow : Tendsto (fun i => (v.length : ℝ) / Real.sqrt (KK i)) atTop (nhds 0) := by
      have hsqrt : Tendsto (fun i => Real.sqrt (KK i)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_KK_atTop
      exact hsqrt.const_div_atTop _
    have hle : ∀ᶠ i in atTop, 2 * v.length ≤ kk i := by
      filter_upwards [eventually_ge_atTop (2 * v.length)] with i hi
      unfold kk
      omega
    have := tendsto_posFreq_growing (fun _ => v.length)
      (Filter.Eventually.of_forall fun _ => hlen) hle hgrow
      (fun _ => ⟨wordVal v, wordVal_lt hv⟩)
    have hlim : Tendsto (fun _ : ℕ => (1 : ℝ) / (2 : ℝ) ^ v.length) atTop
        (nhds (1 / (2 : ℝ) ^ v.length)) := tendsto_const_nhds
    simpa using this.add hlim
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop v.length] with i hi
  have hle : v.length ≤ kk i := by unfold kk; omega
  rw [posFreq_eq_digits i v.length hlen hle]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 2
  refine Finset.filter_congr fun n _ => ?_
  exact blockVal_eq_wordVal_iff (y := primeLambertAtBase 4) hv

end NormalNumbers.G4.Sched
