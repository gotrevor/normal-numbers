/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorExactExponent

/-!
# The middle-fifth set `K₅`: a computable point with exact irrationality exponent `μ₀`

`K₅ = {Σ dᵢ 5^{−i−1} : dᵢ ∈ {0, 1, 3, 4}}` (`cantorFive`), dimension `log 4 / log 5 ≈ 0.861`.
Base-5 analogue of `CantorExactExponent.exists_computable_mem_cantorSet_irrExponent_normal`:
for rational `μ₀ > T₅ = 2 + log₄ 5 ≈ 3.161`, a computable `x ∈ K₅` with irrationality exponent
exactly `μ₀`, normal to every base `b ≥ 2` with `5 ∤ b`, not normal to base 5
(`exists_computable_mem_cantorFive_irrExponent_normal`).

He–Liao (arXiv 2602.01307, Thm 1.5) covers this set (one missing digit, base 5) for the
exponent question alone; the joint normality/computability statement is the point here.  The
stretch range `2 < μ₀ ≤ T₅` is the open node `StretchFive`.

## Threshold

The trivial count: at scale `q ≈ 5ᵐ` there are `≲ 4^{F(m)}` numerators near the support, each
ball `B(p/q, q^{−τ})` has coin mass `≲ 4^{−F(τm)}`, and at the entry of a run the window
`(m, τm]` holds only `≈ (τ−2)m` free places.  The block cost `5ᵐ 4^{−(μ₀−2)m}` is summable iff
`μ₀ > 2 + log₄ 5` (`summable_bc_five`).  Kernel controls on the real schedule bracket it:
`μ₀ = 31/10 < T₅` is red (`bcTerm_red_five`), `μ₀ = 7/2 > T₅` green (`bcTerm_green_five`).

## Design (lap 1)

**Copy, not generalize.**  The base-3 infrastructure (`CantorLiouville`, `CantorLiouvilleAll`,
`CantorExpGeneric`, ~5500 lines) hard-codes base 3 and digits `{0,2}` throughout (`tdig`,
`changes`, the `cos` bounds of the second moment, `3 ∣ b² − 1` orbit counting).  A generic
rewrite is several laps before it pays.  The coin space is kept: each free base-5 digit is
`3·ω(2i) + ω(2i+1) ∈ {0,1,3,4}` (`ptDigitF`), so the coin measure, `pre`, and the derandomizer
`CantorLiouvilleAll.exists_computable_normal_sched_family` (stated for any `G` over Boolean
coins) are reused verbatim, and the run schedule `expRunStart`/`expRunEnd`/`expFree` of the
base-3 file is reused unchanged.  The per-digit characteristic function factors as
`((1 + e(3t))/2)·((1 + e(t))/2)`, which is the route for the base-5 second moment.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.CantorExactExponentFive

open CantorLiouville Derandomize CantorExactExponent

/-! ## Vocabulary -/

/-- The middle-fifth Cantor set: base-5 expansions with digits in `{0, 1, 3, 4}`. -/
def cantorFive : Set ℝ :=
  {x | ∃ d : ℕ → ℕ, (∀ i, d i < 5 ∧ d i ≠ 2) ∧ x = realOfDigits 5 d}

/-- The threshold `2 + log₄ 5 ≈ 3.161` of the trivial rational count in `K₅`. -/
noncomputable def thresholdFive : ℝ := 2 + Real.logb 4 5

theorem one_lt_thresholdFive : 1 < thresholdFive := by
  have : 0 < Real.logb 4 5 := Real.logb_pos (by norm_num) (by norm_num)
  unfold thresholdFive; linarith

/-- Free position `i` carries the base-5 digit `3·ω(2i) + ω(2i+1) ∈ {0,1,3,4}`; forced ones `0`. -/
def ptDigitF (free : ℕ → Bool) (ω : ℕ → Bool) (i : ℕ) : ℕ :=
  if free i then 3 * (ω (2 * i)).toNat + (ω (2 * i + 1)).toNat else 0

/-- The point coded by coins `ω`. -/
noncomputable def ptF (free : ℕ → Bool) (ω : ℕ → Bool) : ℝ := realOfDigits 5 (ptDigitF free ω)

/-- The base-5 exponent point: forced zero runs `[a k, ⌈μ₀ a k⌉)` of the base-3 schedule. -/
noncomputable def cantorFiveExpReal (μ₀ : ℚ) (ω : ℕ → Bool) : ℝ := ptF (expFree μ₀) ω

theorem ptDigitF_lt (free : ℕ → Bool) (ω : ℕ → Bool) (i : ℕ) :
    ptDigitF free ω i < 5 ∧ ptDigitF free ω i ≠ 2 := by
  unfold ptDigitF; split_ifs <;> cases ω (2 * i) <;> cases ω (2 * i + 1) <;> simp

theorem ptF_mem_cantorFive (free : ℕ → Bool) (ω : ℕ → Bool) : ptF free ω ∈ cantorFive :=
  ⟨_, ptDigitF_lt free ω, rfl⟩

theorem mem_cantorFive (μ₀ : ℚ) (ω : ℕ → Bool) : cantorFiveExpReal μ₀ ω ∈ cantorFive :=
  ptF_mem_cantorFive _ _

/-! ## Where the threshold enters -/

theorem rho_five_lt_one (μ₀ : ℝ) (hμ : thresholdFive < μ₀) : 5 * (4 : ℝ) ^ (-(μ₀ - 2)) < 1 := by
  have h1 : (5 : ℝ) = 4 ^ Real.logb 4 5 :=
    (Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)).symm
  rw [h1, ← Real.rpow_add (by norm_num)]
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
  unfold thresholdFive at hμ; linarith

/-- **The trivial-count block costs** `5ᵐ 4^{−(μ₀−2)m}` are summable exactly above `T₅`. -/
theorem summable_bc_five (μ₀ : ℝ) (hμ : thresholdFive < μ₀) :
    Summable fun m : ℕ => (5 : ℝ) ^ m * (4 : ℝ) ^ (-((μ₀ - 2) * m)) := by
  have hρ := rho_five_lt_one μ₀ hμ
  refine (summable_geometric_of_lt_one (by positivity) hρ).congr fun m => ?_
  rw [mul_pow, ← Real.rpow_natCast ((4 : ℝ) ^ (-(μ₀ - 2))), ← Real.rpow_mul (by norm_num)]
  ring_nf

/-- **Red control (below `T₅`).**  `μ₀ = τ = 31/10 < 2 + log₄ 5`: run `2` starts at `a₂ = 243`,
and at `m = 116 ≈ a₂/(τ−1)` the window `[116, 360)` holds `127` free places, so the trivial block
cost `5^{116} · 4^{−127}` exceeds `1`.  (Kernel.) -/
theorem bcTerm_red_five :
    expRunStart (31 / 10) 2 = 243 ∧
      freeCount (expFree (31 / 10)) 360 - freeCount (expFree (31 / 10)) 116 = 127 ∧
      4 ^ (freeCount (expFree (31 / 10)) 360 - freeCount (expFree (31 / 10)) 116) < 5 ^ 116 := by
  decide +kernel

/-- **Green control (above `T₅`).**  `μ₀ = τ = 7/2`: `a₂ = 294`, at `m = 118` the window
`[118, 413)` holds `176` free places and `4^{176} > 5^{118}`.  (Kernel.) -/
theorem bcTerm_green_five :
    expRunStart (7 / 2) 2 = 294 ∧
      freeCount (expFree (7 / 2)) 413 - freeCount (expFree (7 / 2)) 118 = 176 ∧
      5 ^ 118 < 4 ^ (freeCount (expFree (7 / 2)) 413 - freeCount (expFree (7 / 2)) 118) := by
  decide +kernel

/-! ## Leaves -/

theorem ptDigitF_proper (free : ℕ → Bool) (ω : ℕ → Bool)
    (hforced : ∀ N, ∃ i, N ≤ i ∧ free i = false) : ProperDigits 5 (ptDigitF free ω) := by
  intro N
  obtain ⟨i, hi, hf⟩ := hforced N
  exact ⟨i, hi, by simp [ptDigitF, hf]⟩

/-- **Base 5 fails, for every `ω`.**  Forced places recur, so the base-5 expansion is
`ptDigitF`, which never shows the digit `2`. -/
theorem not_isNormal_five_ptF (free : ℕ → Bool) (ω : ℕ → Bool)
    (hforced : ∀ N, ∃ i, N ≤ i ∧ free i = false) : ¬ IsNormal 5 (ptF free ω) := by
  intro h
  have hp := ptDigitF_proper free ω hforced
  have hlt : ∀ i, ptDigitF free ω i < 5 := fun i => (ptDigitF_lt free ω i).1
  have hmem := realOfDigits_mem_Ico 5 (by norm_num) _ hlt hp
  rw [Set.mem_Ico] at hmem
  unfold IsNormal at h
  rw [ptF, Int.fract_eq_self.mpr hmem, digitOf_realOfDigits 5 (by norm_num) _ hlt hp] at h
  have ht := h [2] (by simp) (by intro d hd; simp at hd; omega)
  have h0 : ∀ n, countOccurrences [2] ((List.range n).map (ptDigitF free ω)) = 0 := by
    intro n
    rw [countOccurrences_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro i - ⟨-, hi⟩
    simp at hi
    exact (ptDigitF_lt free ω i).2 hi.symm
  simp only [h0, Nat.cast_zero, zero_div] at ht
  have := tendsto_nhds_unique tendsto_const_nhds ht
  norm_num at this

theorem not_isNormal_five_cantorFiveExpReal (μ₀ : ℚ) (hμ : 1 < μ₀) (ω : ℕ → Bool) :
    ¬ IsNormal 5 (cantorFiveExpReal μ₀ ω) :=
  not_isNormal_five_ptF _ ω (expForced_recur μ₀ hμ)

/-- **The exponent tests** (base-5 `exists_exponent_tests`).  Confidence 75%.

English proof.  As in base 3 with `3 → 5`, `2 → 4`: the lower bound from truncation before each
run (`|x − P/5^{a}| ≤ 5^{−⌈μ₀ a⌉}`), the upper bound by Borel–Cantelli on prefix tests whose
block mass is `≲ 5ᵐ 4^{−(μ₀−2)m}` (`summable_bc_five`), the triangle range by the
separation `|x − p/q| ≥ 1/(2q5^a)`. -/
theorem exists_exponent_tests_five (μ₀ : ℚ) (hμ : thresholdFive < μ₀) :
    ∃ (bad' : ℕ → List Bool → Bool) (d' : ℕ → ℕ), Primrec₂ bad' ∧ Primrec d' ∧
      (∀ j, coins.real {ω | bad' j (pre ω (d' j)) = true} ≤ 1 / ((j : ℝ) + 1) ^ 2) ∧
      ∀ e : ℕ → Bool, (∃ j₁, ∀ j, j₁ ≤ j → bad' j (pre e (d' j)) = false) →
        HasIrrExponent (cantorFiveExpReal μ₀ e) μ₀ := by
  sorry

/-- **Family derandomization, base 5.**  Confidence 75%.

English proof.  `CantorLiouvilleAll.exists_computable_normal_sched_family` with the base-5
prefix approximants (prefix of `D` coins fixes `⌊D/2⌋` digits; tail `≤ 2·5^{−⌈D/2⌉} ≤ 2^{−D}`),
`S b = ¬ 5 ∣ b`, and the base-5 second moment: per digit `|φ(t)| = |cos 3πt|·|cos πt|`, and the
`5`-adic orbit of `bᵏ h` (`5 ∤ b`) moves the digit pattern as the base-3 orbit argument does. -/
theorem exists_computable_normal_avoid_five (μ₀ : ℚ) (hμ : 1 < μ₀)
    (bad' : ℕ → List Bool → Bool) (hbad' : Primrec₂ bad') (d' : ℕ → ℕ) (hd' : Primrec d')
    (hmass : ∀ j, coins.real {ω | bad' j (pre ω (d' j)) = true} ≤ 1 / ((j : ℝ) + 1) ^ 2) :
    ∃ e : ℕ → Bool, Computable e ∧
      (∀ b : ℕ, 2 ≤ b → ¬ 5 ∣ b → IsNormal b (cantorFiveExpReal μ₀ e)) ∧
      ∃ j₁, ∀ j, j₁ ≤ j → bad' j (pre e (d' j)) = false := by
  sorry

/-! ## Headlines -/

/-- **Headline.**  For every rational `μ₀ > 2 + log₄ 5 ≈ 3.161` there is a computable coin
sequence `e` such that `x = cantorFiveExpReal μ₀ e` lies in the middle-fifth set `K₅`, has
irrationality exponent exactly `μ₀`, is normal to every base `b ≥ 2` with `5 ∤ b`, and is not
normal to base 5. -/
theorem exists_computable_mem_cantorFive_irrExponent_normal (μ₀ : ℚ) (hμ : thresholdFive < μ₀) :
    ∃ e : ℕ → Bool, Computable e ∧ cantorFiveExpReal μ₀ e ∈ cantorFive ∧
      HasIrrExponent (cantorFiveExpReal μ₀ e) μ₀ ∧
      (∀ b : ℕ, 2 ≤ b → ¬ 5 ∣ b → IsNormal b (cantorFiveExpReal μ₀ e)) ∧
      ¬ IsNormal 5 (cantorFiveExpReal μ₀ e) := by
  have h1 : (1 : ℚ) < μ₀ := by
    have := one_lt_thresholdFive
    exact_mod_cast this.trans hμ
  obtain ⟨bad', d', hbad', hd', hmass, hexp⟩ := exists_exponent_tests_five μ₀ hμ
  obtain ⟨e, hce, hn, j₁, hj⟩ := exists_computable_normal_avoid_five μ₀ h1 bad' hbad' d' hd' hmass
  exact ⟨e, hce, mem_cantorFive μ₀ e, hexp e ⟨j₁, hj⟩, hn,
    not_isNormal_five_cantorFiveExpReal μ₀ h1 e⟩

/-- **Existence form.** -/
theorem exists_mem_cantorFive_irrExponent_normal (μ₀ : ℚ) (hμ : thresholdFive < μ₀) :
    ∃ x : ℝ, x ∈ cantorFive ∧ HasIrrExponent x μ₀ ∧
      (∀ b : ℕ, 2 ≤ b → ¬ 5 ∣ b → IsNormal b x) ∧ ¬ IsNormal 5 x := by
  obtain ⟨e, -, h⟩ := exists_computable_mem_cantorFive_irrExponent_normal μ₀ hμ
  exact ⟨_, h⟩

/-- **Open node: the base-5 stretch range** `2 < μ₀ ≤ T₅`.  Measure counts cap at `μ₀ > 3`
(`thickening_cost_ge_one` is set-independent); below `T₅` a better count of rationals near `K₅`
is needed (He–Liao 2602.01307 Thm 1.5 gives the exponent alone). -/
def StretchFive : Prop :=
  ∀ μ₀ : ℚ, 2 < (μ₀ : ℝ) → (μ₀ : ℝ) ≤ thresholdFive →
    ∃ x : ℝ, x ∈ cantorFive ∧ HasIrrExponent x μ₀ ∧
      (∀ b : ℕ, 2 ≤ b → ¬ 5 ∣ b → IsNormal b x) ∧ ¬ IsNormal 5 x

end NormalNumbers.CantorExactExponentFive
