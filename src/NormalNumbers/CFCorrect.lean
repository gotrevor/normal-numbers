/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFSchedule
import NormalNumbers.CFConcat
import NormalNumbers.BaryConcat

/-!
# W5 — correctness of the schedule, CF side (B–Y §2.2)

`xstar`'s CF digit word is the increasing union of the scheduled words
`wSched s`; each appended block `uSched s` carries the Lemma-13 CF count
payload.  Chaining the payloads through B–Y Lemma 7 (`CFDiscLt.append`,
`cfDiscLt_short_append`, `cfDiscLt_append_take`) yields **CF normality of
`xstar`**: for every genuine pattern `v`, the fitting-window frequency of `v`
in the length-`p` digit prefix of `xstar` tends to `γ(I_v)`.
-/

namespace NormalNumbers

open MeasureTheory Filter

/-! ## Schedule accessors -/

/-- The scheduled CF word at stage `s`. -/
noncomputable def wSched (s : ℕ) : List ℕ := (sched s).B.w

/-- The scheduled level at stage `s`. -/
noncomputable def tSched (s : ℕ) : ℕ := (sched s).t

/-- The CF block appended at step `s` (so `wSched (s+1) = wSched s ++ uSched s`). -/
noncomputable def uSched (s : ℕ) : List ℕ :=
  (wSched (s + 1)).drop (wSched s).length

theorem wSched_ne (s : ℕ) : wSched s ≠ [] := (sched s).B.hw_ne

theorem wSched_pos (s : ℕ) : ∀ a ∈ wSched s, 1 ≤ a := (sched s).B.hw_pos

theorem wSched_succ (s : ℕ) : wSched (s + 1) = wSched s ++ uSched s := by
  obtain ⟨u, -, -, -, -, hw, -⟩ := sched_step s
  rw [uSched, wSched, wSched, hw, List.drop_left]

/-- The CF-side payload of the block appended at step `s` (level, length,
genuineness, continuant bound, pattern counts). -/
theorem uSched_spec (s : ℕ) :
    (uSched s).length = nFn (tSched (s + 1)) ∧
    (∀ a ∈ uSched s, 1 ≤ a) ∧
    (cfK (uSched s) : ℝ) ≤ Real.exp (goodC * nFn (tSched (s + 1))) ∧
    (∀ v ∈ wordFamily (tSched (s + 1)), |(countOccurrences v (uSched s) : ℝ)
      - (gaussMeasure (cfCylinder v)).toReal * nFn (tSched (s + 1))|
        < schedEps (tSched (s + 1)) * nFn (tSched (s + 1)) + v.length) := by
  obtain ⟨u, m₁, j₁, r₁, ht, hw, hlen, hpos, -, -, hK, hCF, -⟩ := sched_step s
  have hu : uSched s = u := by
    rw [uSched, wSched, wSched, hw, List.drop_left]
  rw [hu]
  exact ⟨hlen, hpos, hK, hCF⟩

theorem uSched_length (s : ℕ) : (uSched s).length = nFn (tSched (s + 1)) :=
  (uSched_spec s).1

theorem uSched_ne (s : ℕ) : uSched s ≠ [] := by
  intro h
  have := uSched_length s
  rw [h] at this
  simp at this
  exact absurd this.symm (nFn_pos _).ne'

/-- Word length at stage `s`. -/
theorem wSched_length_succ (s : ℕ) :
    (wSched (s + 1)).length = (wSched s).length + nFn (tSched (s + 1)) := by
  rw [wSched_succ, List.length_append, uSched_length]

/-- The dominance condition in accessor form: the appended block has length
at most `|wSched s| / tSched (s+1)`. -/
theorem uSched_dominance (s : ℕ) :
    tSched (s + 1) * (uSched s).length ≤ (wSched s).length := by
  rw [uSched_length]
  exact sched_dominance s

/-! ## Digit identification -/

/-- The length-`p` CF digit prefix of `xstar`. -/
noncomputable def cfPrefix (p : ℕ) : List ℕ :=
  (List.range p).map (cfDigit xstar)

theorem cfPrefix_length (p : ℕ) : (cfPrefix p).length = p := by
  simp [cfPrefix]

/-- Digit identification at stage boundaries: the digit prefix of `xstar`
of length `|wSched s|` IS `wSched s`. -/
theorem cfPrefix_eq_wSched (s : ℕ) :
    cfPrefix (wSched s).length = wSched s := by
  have hx : xstar ∈ cfCylinder (([] : List ℕ) ++ wSched s) := xstar_mem s
  have h := range_map_cfDigit_eq hx
  simpa [cfPrefix] using h

/-- Prefixes restrict: `cfPrefix p = (cfPrefix q).take p` for `p ≤ q`. -/
theorem cfPrefix_take {p q : ℕ} (h : p ≤ q) :
    cfPrefix p = (cfPrefix q).take p := by
  rw [cfPrefix, cfPrefix, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-! ## Monotonicity helpers -/

/-- `CFDiscLt` is monotone in the accuracy. -/
theorem CFDiscLt.mono {w a : List ℕ} {m ε ε' : ℝ} (h : CFDiscLt w a m ε)
    (hε : ε ≤ ε') : CFDiscLt w a m ε' :=
  lt_of_lt_of_le h (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _))

/-- `γ(I_v) ∈ [0, 1]`. -/
theorem gaussMeasure_toReal_mem_Icc (S : Set ℝ) :
    (gaussMeasure S).toReal ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have h := prob_le_one (μ := gaussMeasure) (s := S)
  calc (gaussMeasure S).toReal ≤ (1 : ENNReal).toReal :=
        ENNReal.toReal_mono ENNReal.one_ne_top h
    _ = 1 := by simp

end NormalNumbers
