/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFCorrect
import NormalNumbers.DaryDigits

/-!
# W5 — correctness of the schedule, d-ary side (B–Y §2.2)

Per base `d` and stage `s` (with `d` active, `d ≤ tSched s`), the Lemma-13
payload puts `xstar` in a definite order-`mSched s d` cell and reads off a
GOOD block of new base-`d` digits up to order `mSched (s+1) d`
(`xstar_dary_step` + `digit_window_eq`).  This file sets up the accessors
and the `badBlocks ↔ HasDiscLt` bridge; the chain (Lemma 9), the `m`-growth
estimates, and the final simple-normality limits build on it.
-/

namespace NormalNumbers

open MeasureTheory

/-! ## Accessors -/

/-- The d-ary cell order of stage `s` at base `d`. -/
noncomputable def mSched (s d : ℕ) : ℕ := (sched s).B.m d

/-- The d-ary cell index of stage `s` at base `d`. -/
noncomputable def jSched (s d : ℕ) : ℤ := (sched s).B.j d

theorem xstar_mem_Ioo : xstar ∈ Set.Ioo (0 : ℝ) 1 := (xstar_mem 0).1

/-- **The d-ary payload at `xstar`** (SchedStep payloads 5, 9, 10 combined):
for an active base, `xstar` lies in a definite cell of stage `s`'s block and
its refined sub-cell carries a good digit block, gaining at least
`kminFn (tSched (s+1))` digits. -/
theorem xstar_dary_step (s d : ℕ) (hd2 : 2 ≤ d) (hdt : d ≤ tSched s) :
    ∃ k : ℕ, mSched (s + 1) d = mSched s d + k ∧
      kminFn (tSched (s + 1)) ≤ k ∧
      ∃ i : ℕ, i < 2 ∧ xstar ∈ daryCell d (mSched s d) (jSched s d + i) 1 ∧
        ∃ β : Fin k → Fin d,
          β ∉ badBlocks d k (schedEps (tSched (s + 1))) ∧
          xstar ∈ daryCell d (mSched s d + k)
            ((jSched s d + i) * d ^ k
              + blockNatVal d (List.ofFn fun l => (β l : ℕ))) 1 := by
  obtain ⟨u, m₁, j₁, r₁, ht, hw, hlen, hpos, hold, hstart, hK, hCF, hgrow,
    hgood⟩ := sched_step s
  have hdt' : d ≤ tSched (s + 1) := le_trans hdt (sched_t_mono (Nat.le_succ s))
  obtain ⟨hm₁, hj₁⟩ := hold d hd2 hdt
  have hx : xstar ∈ cfCylinder ((sched (s + 1)).B.w) := xstar_mem (s + 1)
  have hgrow' := hgrow d hd2 hdt'
  obtain ⟨i, hi2, hcell, hβex⟩ := hgood d hd2 hdt' xstar hx
  -- make the digit gain `k` opaque BEFORE destructuring `∃ β` (the `set`
  -- rewrite is only type-correct while `β` is still bound)
  set k : ℕ := (sched (s + 1)).B.m d - m₁ d with hk
  clear_value k
  obtain ⟨β, hβ, hsub⟩ := hβex
  rw [hm₁, hj₁] at hcell hsub
  refine ⟨k, ?_, ?_, i, hi2, hcell, β, hβ, hsub⟩
  · have hms : mSched s d = m₁ d := hm₁.symm
    show (sched (s + 1)).B.m d = mSched s d + k
    omega
  · show kminFn ((sched (s + 1)).t) ≤ k
    omega

/-- The cell index of `xstar`'s cell is nonnegative (it is the floor of a
positive number below `d^m`). -/
theorem jSched_add_nonneg {s d : ℕ} (hd : 1 ≤ d) {i : ℕ}
    (hcell : xstar ∈ daryCell d (mSched s d) (jSched s d + i) 1) :
    0 ≤ jSched s d + i := by
  have hfloor := floor_eq_of_mem_daryCell_one hd hcell
  rw [← hfloor]
  have hx0 : 0 ≤ xstar := xstar_mem_Ioo.1.le
  positivity

/-! ## The `badBlocks ↔ HasDiscLt` bridge -/

/-- Avoiding the bad-block set is exactly the deviation-form discrepancy
bound of B–Y Lemma 9. -/
theorem hasDiscLt_ofFn_of_notMem_badBlocks {d k : ℕ} {ε : ℝ}
    {β : Fin k → Fin d} (hβ : β ∉ badBlocks d k ε) :
    HasDiscLt (List.ofFn β) ε := by
  intro c
  rw [badBlocks, Finset.mem_filter] at hβ
  push Not at hβ
  have h := hβ (Finset.mem_univ β) c
  rw [← digitCount_eq_count_ofFn, List.length_ofFn]
  exact h

/-- `HasDiscLt` is monotone in the accuracy. -/
theorem HasDiscLt.mono {b : ℕ} {u : List (Fin b)} {ε ε' : ℝ}
    (h : HasDiscLt u ε) (hε : ε ≤ ε') : HasDiscLt u ε' := fun c =>
  lt_of_lt_of_le (h c) (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _))

/-- **The per-stage digit window of `xstar`** (a, b combined): at each stage
with base `d` active, `xstar` gains `k ≥ kminFn` new base-`d` digits, and
that digit window is a `schedEps (tSched (s+1))`-good block. -/
theorem xstar_dary_window (s d : ℕ) (hd2 : 2 ≤ d) (hdt : d ≤ tSched s) :
    ∃ k : ℕ, mSched (s + 1) d = mSched s d + k ∧
      kminFn (tSched (s + 1)) ≤ k ∧
      ∃ β : Fin k → Fin d,
        HasDiscLt (List.ofFn β) (schedEps (tSched (s + 1))) ∧
        (List.range k).map (fun l => digitOf d xstar (mSched s d + l))
          = List.ofFn fun i => (β i : ℕ) := by
  obtain ⟨k, hm, hkmin, i, hi2, hcell, β, hβ, hsub⟩ :=
    xstar_dary_step s d hd2 hdt
  have hd1 : 1 ≤ d := by omega
  have hJ : 0 ≤ jSched s d + i := jSched_add_nonneg hd1 hcell
  exact ⟨k, hm, hkmin, β, hasDiscLt_ofFn_of_notMem_badBlocks hβ,
    digit_window_eq hd1 hJ hsub⟩

/-! ## Continuant growth (for the `m`-growth estimates) -/

/-- Fibonacci doubling: `2^j ≤ fib (2j + 1)`. -/
theorem two_pow_le_fib (j : ℕ) : 2 ^ j ≤ Nat.fib (2 * j + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by omega
    rw [h1, Nat.fib_add_two, pow_succ]
    have h2 : Nat.fib (2 * j + 1) ≤ Nat.fib (2 * j + 1 + 1) :=
      Nat.fib_mono (Nat.le_succ _)
    omega

/-- Exponential continuant growth: a genuine word of length `n` has
`cfK ≥ 2^(n/2)` (integer division). -/
theorem two_pow_le_cfK (u : List ℕ) (hpos : ∀ a ∈ u, 1 ≤ a) :
    2 ^ (u.length / 2) ≤ cfK u := by
  have h1 := fib_le_cfK u hpos
  have h2 : 2 * (u.length / 2) + 1 ≤ u.length + 1 := by omega
  calc 2 ^ (u.length / 2) ≤ Nat.fib (2 * (u.length / 2) + 1) :=
        two_pow_le_fib _
    _ ≤ Nat.fib (u.length + 1) := Nat.fib_mono h2
    _ ≤ cfK u := h1

end NormalNumbers
