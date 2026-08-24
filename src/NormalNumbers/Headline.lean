/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.RealDefs
import NormalNumbers.CFDigitLaw
import NormalNumbers.DaryCorrect
import NormalNumbers.Pillai
import NormalNumbers.KhinchinDefs
import NormalNumbers.Khinchin

/-!
# B5′ headline statement surface (judge-frozen)

The exported destination of expedition B5′ (`KHINCHIN.md`), frozen by the
judge (`JUDGE.md`, 2026-08-23) so the campaign proves toward a statement it
does not own.  Two tiers, both stated in **witness-existence form** — the
construction (`xstar`, its schedule, and any future digit-cap re-plumbing
for the Khinchin graft) is deliberately NOT named here, so W6's capped
rebuild discharges the same frozen statements:

* `exists_absolutely_normal_cf_normal` — **Tier 1 = the Becher–Yuhjtman
  theorem** (IMRN 2019, arXiv:1704.03622, minus the efficiency claim):
  a real that is absolutely normal AND CF-normal.  Apparently the first
  formalization of this theorem in any prover (landscape survey
  2026-08-23, `KHINCHIN.md`).
* `exists_absolutely_normal_cf_normal_khinchin` — **Tier 2 = the
  expedition headline**: additionally Khinchin-typical.  The conjunction
  is apparently new even on paper (`KHINCHIN.md` "Apparent literature
  gap").

Definitions frozen with them: `IsAbsolutelyNormal` (Track A's full
`IsNormal` in every base `b ≥ 2` — NOT mere simple normality; the Pillai
powers-equivalence, or direct block frequencies, is part of the Tier-1
obligation), `IsCFNormal` (every genuine CF pattern occurs with
window-frequency `γ(I_v)`, the B–Y §2.2 form), `khinchinK₀` (Khinchin's
constant as the tprod), `KhinchinTypical` (geometric mean of the CF digits
→ `K₀`).

Hand-checked anchors (frozen with the statements): overlapping window
counting (`countOccurrences [1,1] [1,1,1] = 2`); the `K₀` factor at digit
`a = 1` is `(4/3)^{log₂ 1} = 1` and at `a = 2` is `(9/8)^{log₂ 2} = 9/8` —
these pin the tprod's index alignment (index `k` ↦ digit `k+1`).
-/

namespace NormalNumbers

open MeasureTheory

/-! ## Anchors (kernel-checked) -/

example : countOccurrences [1] [1, 2, 1] = 2 := by decide
example : countOccurrences [1, 1] [1, 1, 1] = 2 := by decide
example : (1 + 1 / (1 * 3) : ℝ) ^ Real.logb 2 1 = 1 := by
  rw [Real.logb_one, Real.rpow_zero]
example : (1 + 1 / (2 * 4) : ℝ) ^ Real.logb 2 2 = 9 / 8 := by
  rw [Real.logb_self_eq_one (by norm_num), Real.rpow_one]
  norm_num

/-! ## The frozen definitions -/

/-- Absolutely normal: (fully) normal in every integer base `b ≥ 2`
(Track A's `IsNormal` — all blocks, correct frequencies; NOT merely
simple normality). -/
def IsAbsolutelyNormal (x : ℝ) : Prop := ∀ b : ℕ, 2 ≤ b → IsNormal b x

/-- CF-normal (B–Y §2.2 window-frequency form): every genuine finite CF
pattern `v` occurs among the windows of the length-`p` CF-digit prefix of
`x` with frequency tending to `γ(I_v)`. -/
def IsCFNormal (x : ℝ) : Prop :=
  ∀ v : List ℕ, v ≠ [] → (∀ a ∈ v, 1 ≤ a) →
    Filter.Tendsto
      (fun p => (countOccurrences v ((List.range p).map (cfDigit x)) : ℝ) / p)
      Filter.atTop (nhds ((gaussMeasure (cfCylinder v)).toReal))

/-! `khinchinK₀` and `KhinchinTypical` are the JUDGE-frozen Khinchin definitions;
they now live BYTE-IDENTICAL in `KhinchinDefs.lean` (upstream) so `Khinchin.lean`
can prove `xstar_khinchinTypical` and this file can invoke it (route-D′ layering).
The anchors above pin the `tprod` alignment (`k ↦ k+1`) that `khinchinK₀` uses. -/

/-! ## The frozen headline statements -/

/-- Bridge: the `List.count` of a value among the mapped-range digit prefix
equals the `Finset.filter`-card of matching indices (the two count idioms
used by `xstar_dary_freq_tendsto` and `pillai` respectively). -/
private theorem count_map_range_eq_card_filter (f : ℕ → ℕ) (c p : ℕ) :
    ((List.range p).map f).count c = ((Finset.range p).filter (fun q => f q = c)).card := by
  induction p with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.count_append, Finset.range_add_one]
    simp only [List.map_cons, List.map_nil, List.count_cons, List.count_nil, zero_add]
    by_cases h : f n = c
    · rw [Finset.filter_insert, if_pos h, Finset.card_insert_of_notMem (by simp), ih]
      simp [h]
    · rw [Finset.filter_insert, if_neg h, ih]
      simp [h]

/-- `xstar` is absolutely normal (Track A's full `IsNormal` in every base
`b ≥ 2`): Pillai's powers-equivalence fed by the d-ary simple normality of
`xstar` at every `b^r` (`xstar_dary_freq_tendsto`). -/
theorem xstar_isAbsolutelyNormal : IsAbsolutelyNormal xstar := by
  intro b hb
  have hxfrac : Int.fract xstar = xstar :=
    Int.fract_eq_self.mpr ⟨xstar_mem_Ioo.1.le, xstar_mem_Ioo.2⟩
  have hy : xstar ∈ Set.Ico (0 : ℝ) 1 := ⟨xstar_mem_Ioo.1.le, xstar_mem_Ioo.2⟩
  show IsNormalSequence b (digitOf b (Int.fract xstar))
  rw [hxfrac]
  apply pillai b hb xstar hy
  intro r hr1 c hc
  have hd2 : 2 ≤ b ^ r := by
    calc 2 ≤ b := hb
      _ = b ^ 1 := (pow_one b).symm
      _ ≤ b ^ r := Nat.pow_le_pow_right (by omega) hr1
  have h := xstar_dary_freq_tendsto (b ^ r) hd2 c hc
  have h2 := h.congr (fun p => by rw [count_map_range_eq_card_filter])
  have hcast : ((b : ℝ) ^ r)⁻¹ = ((b ^ r : ℕ) : ℝ)⁻¹ := by push_cast; ring
  rwa [hcast]

/-- `xstar` is CF-normal (B–Y §2.2 window-frequency form),
`xstar_cf_freq_tendsto`. -/
theorem xstar_isCFNormal : IsCFNormal xstar :=
  fun v hne hpos => xstar_cf_freq_tendsto v hne hpos

/-- **Tier 1 — the Becher–Yuhjtman theorem** (IMRN 2019, minus
efficiency): there is a real number that is absolutely normal and
CF-normal.  Witness: `xstar` (its machinery lives in the `CF*`/`TBrick*`
modules; this statement deliberately does not name it). -/
theorem exists_absolutely_normal_cf_normal :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ IsCFNormal x :=
  ⟨xstar, xstar_isAbsolutelyNormal, xstar_isCFNormal⟩

/-- **Tier 2 — the expedition headline** (the conjunction apparently new
even on paper): there is a real number that is absolutely normal,
CF-normal, and Khinchin-typical.  Witness: `xstar`; the Khinchin leg is
`xstar_khinchinTypical` (`Khinchin.lean`, delivered by the route-C′ summable
log-tail family grafted into the schedule). -/
theorem exists_absolutely_normal_cf_normal_khinchin :
    ∃ x : ℝ, IsAbsolutelyNormal x ∧ IsCFNormal x ∧ KhinchinTypical x :=
  ⟨xstar, xstar_isAbsolutelyNormal, xstar_isCFNormal, xstar_khinchinTypical⟩

end NormalNumbers
