/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyShift

/-!
# Every quantized sampler at once

The expedition's sample is one instance of a general shape: pick times `r` and quantization
levels `m`, and record `⌊2^m {2^r x}⌋`.  The schedule's `Z^x_{K,α}(n)` is exactly this with
`r = 2·kIdx` and `m = m_K` (`ZSample_eq_blockVal`, `floor_fract_eq_blockVal`).

This module settles *all* such samplers in one theorem, for an arbitrary index set of
`(time, level)` pairs — any schedule, any set of times, any growth rate of the levels:

> **`qForces_normal_iff_density_one`**: a satisfiable hypothesis about the quantized sample
> values implies binary normality **iff** the union of the sampled windows
> `⋃ᵢ [rᵢ, rᵢ + mᵢ)` has density one.

Both directions use that a window value is *equivalent* to the digits inside it: `blockVal_congr`
one way, and `digitOf_congr_of_blockVal` (this module, by the recursion
`blockVal_succ`) the other.  The density-one side then comes from `G4EntropyStable`, the
density-`< 1` side from `G4EntropyDensityOne`.

Applied to the schedule, whose windows cover at most a quarter of every prefix
(`Sched.card_isSampled_le_real`), this is again a refutation — but now it forecloses every
variant at once, including levels `m_K → ∞`, which is the only freedom the brief's §6 positive
branch had left.
-/

open Finset Filter

namespace NormalNumbers.G4Entropy

open NormalNumbers NormalNumbers.G4

/-! ### A window value is equivalent to the digits inside it -/

/-- The window recursion: one more digit doubles the window value. -/
lemma blockVal_succ (y : ℝ) (j m : ℕ) :
    blockVal y j (m + 1) = 2 * blockVal y j m + digitOf 2 y (j + m) := by
  unfold blockVal
  simp only [Nat.add_sub_cancel, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < m := Finset.mem_range.1 hi
  have he : m - i = (m - 1 - i) + 1 := by omega
  rw [he, pow_succ]
  ring

/-- **A window value determines its digits.**  The converse of `blockVal_congr`. -/
lemma digitOf_congr_of_blockVal {x y : ℝ} {j : ℕ} :
    ∀ {m : ℕ}, blockVal x j m = blockVal y j m → ∀ i < m,
      digitOf 2 x (j + i) = digitOf 2 y (j + i) := by
  intro m
  induction m with
  | zero => intro _ i hi; omega
  | succ m ih =>
    intro h i hi
    rw [blockVal_succ, blockVal_succ] at h
    have hdx : digitOf 2 x (j + m) < 2 := Nat.mod_lt _ (by omega)
    have hdy : digitOf 2 y (j + m) < 2 := Nat.mod_lt _ (by omega)
    have hb : blockVal x j m = blockVal y j m := by omega
    have hd : digitOf 2 x (j + m) = digitOf 2 y (j + m) := by omega
    rcases Nat.lt_or_ge i m with hlt | hge
    · exact ih hb i hlt
    · have : i = m := by omega
      subst this
      exact hd

/-! ### Quantized samplers -/

variable {ι : Type*}

/-- The digit positions a quantized sampler reads: each index `i` contributes the window
`[rᵢ, rᵢ + mᵢ)`. -/
def qRead (W : ι → ℕ × ℕ) (j : ℕ) : Prop := ∃ i, (W i).1 ≤ j ∧ j < (W i).1 + (W i).2

noncomputable instance (W : ι → ℕ × ℕ) : DecidablePred (qRead W) := Classical.decPred _

/-- The quantized sample value at index `i`: `⌊2^{mᵢ} {2^{rᵢ} x}⌋`. -/
noncomputable def qVal (W : ι → ℕ × ℕ) (x : ℝ) (i : ι) : ℕ :=
  ⌊(2 : ℝ) ^ (W i).2 * Int.fract ((2 : ℝ) ^ (W i).1 * Int.fract x)⌋₊

lemma qVal_eq_blockVal (W : ι → ℕ × ℕ) (x : ℝ) (i : ι) :
    qVal W x i = blockVal (Int.fract x) (W i).1 (W i).2 :=
  floor_fract_eq_blockVal (Int.fract_nonneg x) _ _

/-- The sample values are a function of the digits at the positions read. -/
lemma qVal_congr {W : ι → ℕ × ℕ} {x y : ℝ}
    (hd : ∀ j, qRead W j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j) :
    qVal W x = qVal W y := by
  funext i
  rw [qVal_eq_blockVal, qVal_eq_blockVal]
  refine blockVal_congr fun k hk => hd ((W i).1 + k) ⟨i, Nat.le_add_right _ _, by omega⟩

/-- …and conversely the digits at the positions read are a function of the sample values. -/
lemma digits_congr_of_qVal {W : ι → ℕ × ℕ} {x y : ℝ} (h : qVal W x = qVal W y) :
    ∀ j, qRead W j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j := by
  rintro j ⟨i, h1, h2⟩
  have hi := congrFun h i
  rw [qVal_eq_blockVal, qVal_eq_blockVal] at hi
  have := digitOf_congr_of_blockVal hi (j - (W i).1) (by omega)
  rwa [show (W i).1 + (j - (W i).1) = j by omega] at this

/-! ### The theorem for every quantized sampler -/

/-- **Every quantized sampler at once.**  For an arbitrary family of times and quantization
levels, a satisfiable hypothesis about the sample values `⌊2^{mᵢ} {2^{rᵢ} x}⌋` implies binary
normality **iff** the sampled windows `⋃ᵢ [rᵢ, rᵢ + mᵢ)` have density one.

No assumption is made on the index set, on how the times are distributed, or on how fast the
quantization levels grow: the levels enter only through the length of the windows. -/
theorem qForces_normal_iff_density_one (W : ι → ℕ × ℕ) :
    (∃ P : ℝ → Prop,
        (∀ x y : ℝ, qVal W x = qVal W y → P x → P y)
        ∧ (∃ x : ℝ, P x)
        ∧ (∀ y : ℝ, 0 ≤ y → y < 1 → P y → IsNormal 2 y))
      ↔ Tendsto (fun L => ((((Finset.range L).filter (qRead W)).card : ℝ)) / L)
          atTop (nhds 1) := by
  constructor
  · rintro ⟨P, hloc, ⟨x, hx⟩, hforce⟩
    exact tendsto_density_one_of_forces_normal
      (fun x y hd => hloc x y (qVal_congr hd)) hx hforce
  · intro hdens
    refine ⟨fun x => IsNormal 2 x, ?_, ⟨stoneham23, isNormal_two_stoneham23⟩,
      fun y _ _ h => h⟩
    intro x y hq hx
    exact isNormal_local_of_density_one (tendsto_compl_zero_of_density_one hdens)
      x y (digits_congr_of_qVal hq) hx

/-- **The negative half, in the form the expedition needs**: if the sampled windows miss a
positive fraction of some arbitrarily long prefixes — upper density `< 1` suffices — then every
satisfiable hypothesis about the quantized sample values has a nonnormal model. -/
theorem exists_nonnormal_of_qLocal (W : ι → ℕ × ℕ) {c : ℝ} (hc : c < 1) {L₀ : ℕ}
    (hdens : ∀ L : ℕ, L₀ ≤ L → ((((Finset.range L).filter (qRead W)).card : ℝ)) ≤ c * L)
    {P : ℝ → Prop} (hloc : ∀ x y : ℝ, qVal W x = qVal W y → P x → P y)
    {x : ℝ} (hx : P x) :
    ∃ y : ℝ, 0 ≤ y ∧ y < 1 ∧ P y ∧ ¬ IsNormal 2 y :=
  exists_nonnormal_of_digitLocal_of_lt_one hc hdens
    (fun x y hd => hloc x y (qVal_congr hd)) hx

end NormalNumbers.G4Entropy

/-! ## The implemented schedule is one of these samplers -/

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy Filter

/-- The index set of the implemented sampler: a scale, a sample point of that scale's
arithmetic progression, and an atom. -/
def SchedIdx : Type :=
  (i : ℕ) × {n : ℕ // n ∈ apSample (X (KK i)) (gridAt i).P₀ (gridAt i).b₀} × (gridAt i).Atom

/-- Its `(time, level)` family: the window `[2·kIdx, 2·kIdx + m_K)`. -/
noncomputable def schedW : SchedIdx → ℕ × ℕ :=
  fun z => (2 * kIdx (gridAt z.1) z.2.1.1 z.2.2, kk z.1)

/-- The windows of the implemented sampler are exactly the sampled positions. -/
lemma qRead_schedW_iff (j : ℕ) : qRead schedW j ↔ IsSampled j := by
  constructor
  · rintro ⟨⟨i, n, α⟩, h1, h2⟩
    exact ⟨i, (mem_sampledPos (gridAt i)).2
      ⟨n.1, n.2, α, j - 2 * kIdx (gridAt i) n.1 α, by
        simp only [schedW] at h1 h2; omega, by
        simp only [schedW] at h1 h2; omega⟩⟩
  · rintro ⟨i, hj⟩
    obtain ⟨n, hn, α, h, hh, rfl⟩ := (mem_sampledPos (gridAt i)).1 hj
    exact ⟨⟨i, ⟨n, hn⟩, α⟩, by simp only [schedW]; omega, by simp only [schedW]; omega⟩

/-- **The implemented schedule fails the criterion.**  Its windows cover at most a quarter of
every prefix, so by `qForces_normal_iff_density_one` no hypothesis about its quantized sample
values — at any quantization level, over any set of scales — can imply binary normality. -/
theorem not_qForces_normal :
    ¬ ∃ P : ℝ → Prop,
        (∀ x y : ℝ, qVal schedW x = qVal schedW y → P x → P y)
        ∧ (∃ x : ℝ, P x)
        ∧ (∀ y : ℝ, 0 ≤ y → y < 1 → P y → IsNormal 2 y) := by
  intro h
  have hdens := (qForces_normal_iff_density_one schedW).1 h
  have hq : ∀ L : ℕ, ((((Finset.range L).filter (qRead schedW)).card : ℝ)) ≤ (1 / 4 : ℝ) * L := by
    intro L
    have hset : (Finset.range L).filter (qRead schedW) = (Finset.range L).filter IsSampled := by
      apply Finset.filter_congr
      intro j _
      simpa using qRead_schedW_iff j
    rw [hset]
    exact card_isSampled_le_real L
  have hev : ∀ᶠ L : ℕ in atTop,
      ((((Finset.range L).filter (qRead schedW)).card : ℝ)) / L ≤ 1 / 4 := by
    filter_upwards [Filter.eventually_gt_atTop 0] with L hL
    have hLR : (0 : ℝ) < L := by exact_mod_cast hL
    rw [div_le_iff₀ hLR]
    exact hq L
  have := le_of_tendsto hdens hev
  linarith

end NormalNumbers.G4.Sched
