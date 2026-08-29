/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LnTwoRuns

/-!
# Kick dynamics: gates, the sliver-escape node, and its run edge

Unconditional structure of the Bailey–Crandall surrogate
`x_{n+1} = fract(2·x_n + κ_n)`, `κ_n = 1/(n+1)` — the phase-space geometry
behind `docs/lnTwo-kick-blueprint.md` §1, proved sorry-free:

* **Gate theorems** (`kick_floor`, `top_gate`): the only ways the surrogate
  can be kick-small (`x_{n+1} < κ_n`) or enter the top sliver
  (`x_{n+1} ≥ 1 − θ`) are through explicit windows of width `O(θ + 1/n)`
  around `1/2` or from within the top region itself.  The dangerous sets
  are *gated*: reachable only through measure-`1/n` doors.

* **The frozen node `SliverEscape`**: the surrogate cannot ride the top
  sliver `x_{n+j} ≥ 1 − 1/(n+j+1)` for more than `C·log₂ n` consecutive
  steps.  A statement about the explicit rational sequence
  `x_n = (A_n mod lcm(1..n))/lcm(1..n)` only — no `ln 2`, no orbit.
  Probe (`experiments/lntwo_runs.py`): observed rides in 4000 steps have
  length ≤ 5.  Odds it is true: high (the in-sliver dynamics
  `δ' = 2δ − κ` is neutral-unstable, so rides need `2⁻ᵏ`-tuned initial
  data); odds it is provable without Diophantine input: open.  The costume
  check passed: it is not a tier in disguise (see the node docstring).

* **The edge** (`zeroRun_le_of_sliverEscape`): `SliverEscape C` caps every
  zero-run of binary `ln 2` at `C·log₂(n+2) + log₂(n+k+1) + 2` — because a
  super-logarithmic run *forces* a sliver ride via the dichotomy of
  `LnTwoRuns.lean` applied at each offset.
-/

namespace NormalNumbers

open Filter Set

/-! ### Gate theorems (unconditional) -/

/-- The surrogate recursion, restated. -/
theorem lnTwoOrbit_succ (n : ℕ) :
    lnTwoOrbit (n + 1) = Int.fract (2 * lnTwoOrbit n + 1 / ((n : ℝ) + 1)) := rfl

private theorem fract_sub_one_eq {y : ℝ} (h1 : 1 ≤ y) (h2 : y < 2) :
    Int.fract y = y - 1 := by
  have hy : y - 1 + ((1 : ℤ) : ℝ) = y := by push_cast; ring
  rw [← hy, Int.fract_add_intCast,
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  push_cast
  ring

private theorem fract_sub_two_eq {y : ℝ} (h1 : 2 ≤ y) (h2 : y < 3) :
    Int.fract y = y - 2 := by
  have hy : y - 2 + ((2 : ℤ) : ℝ) = y := by push_cast; ring
  rw [← hy, Int.fract_add_intCast,
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  push_cast
  ring

/-- **The kick floor is gated.**  The surrogate can fall below the kick
scale (`x_{n+1} < 1/(n+1)`) only from the width-`1/(2(n+1))` window just
below `1/2` (a mid-wrap) or from the width-`1/(2(n+1))` top sliver (a
double-wrap).  In particular, from generic position the kick forces
`x_{n+1} ≥ 1/(n+1)`. -/
theorem kick_floor {n : ℕ}
    (h : lnTwoOrbit (n + 1) < 1 / ((n : ℝ) + 1)) :
    (1 / 2 - 1 / (2 * ((n : ℝ) + 1)) ≤ lnTwoOrbit n ∧ lnTwoOrbit n < 1 / 2) ∨
      1 - 1 / (2 * ((n : ℝ) + 1)) ≤ lnTwoOrbit n := by
  set x := lnTwoOrbit n with hx_def
  set κ : ℝ := 1 / ((n : ℝ) + 1) with hκ_def
  have hκ0 : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 := by
    rw [hκ_def]
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hx01 := lnTwoOrbit_mem_Ico n
  have hκ2 : κ / 2 = 1 / (2 * ((n : ℝ) + 1)) := by
    rw [hκ_def, div_div]
    ring_nf
  rw [lnTwoOrbit_succ] at h
  rcases lt_or_ge (2 * x + κ) 1 with h1 | h1
  · exfalso
    rw [Int.fract_eq_self.mpr ⟨by nlinarith [hx01.1], h1⟩] at h
    nlinarith [hx01.1]
  · rcases lt_or_ge (2 * x + κ) 2 with h2 | h2
    · rw [fract_sub_one_eq h1 h2] at h
      left
      constructor
      · nlinarith
      · nlinarith
    · right
      nlinarith [hx01.2]

/-- **The top sliver is gated.**  For `θ + 1/(n+1) ≤ 1`: the surrogate can
land in the top sliver (`x_{n+1} ≥ 1 − θ`) only from the width-
`(θ + κ)/2` window just below `1/2`, or from the width-`(θ + κ)/2` top
region itself (a ride step).  So the sliver is reachable only through a
measure-`O(θ + 1/n)` gate, or by already riding. -/
theorem top_gate {n : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ + 1 / ((n : ℝ) + 1) ≤ 1)
    (h : 1 - θ ≤ lnTwoOrbit (n + 1)) :
    (1 / 2 - (θ + 1 / ((n : ℝ) + 1)) / 2 ≤ lnTwoOrbit n ∧ lnTwoOrbit n < 1 / 2) ∨
      1 - (θ + 1 / ((n : ℝ) + 1)) / 2 ≤ lnTwoOrbit n := by
  set x := lnTwoOrbit n with hx_def
  set κ : ℝ := 1 / ((n : ℝ) + 1) with hκ_def
  have hκ0 : 0 < κ := by positivity
  have hx01 := lnTwoOrbit_mem_Ico n
  rw [lnTwoOrbit_succ] at h
  rcases lt_or_ge (2 * x + κ) 1 with h1 | h1
  · rw [Int.fract_eq_self.mpr ⟨by nlinarith [hx01.1], h1⟩] at h
    left
    constructor
    · nlinarith
    · nlinarith
  · rcases lt_or_ge (2 * x + κ) 2 with h2 | h2
    · rw [fract_sub_one_eq h1 h2] at h
      right
      nlinarith
    · exfalso
      have h3 : 2 * x + κ < 3 := by nlinarith [hx01.2]
      rw [fract_sub_two_eq h2 h3] at h
      nlinarith [hx01.2]

/-! ### The frozen node and its run edge -/

/-- **Node (frozen, OPEN): sliver escape.**  The surrogate cannot ride the
top sliver `x_{n+j} ≥ 1 − 1/(n+j+1)` for more than `C·log₂(n+2)`
consecutive steps.  A statement about the explicit rational sequence
`x_n` alone — no `ln 2`, no orbit, decidable per `(n, k)`.

Status 2026-08-29: probe-supported (rides ≤ 5 in 4000 steps); the
in-sliver dynamics `δ' = 2δ − κ` is neutral-unstable around the profile
`δ = 1/n`, so long rides need exponentially tuned initial data.  Costume
check PASSED (analytic, see `docs/diophantine-wall.md`): a ride certifies
only `‖2^(n+j)·ln 2‖ ≤ 1/(n+j+1)` — log-precision, far above
`LnTwoPolySep`'s floor — so this node constrains *duration* of coarse
closeness where the tiers constrain *depth*; neither implies the other. -/
def SliverEscape (C : ℝ) (N₀ : ℕ) : Prop :=
  ∀ n, N₀ ≤ n → ∀ k : ℕ,
    (∀ j, j < k → 1 - 1 / ((n : ℝ) + j + 1) ≤ lnTwoOrbit (n + j)) →
    (k : ℝ) ≤ C * Real.logb 2 ((n : ℝ) + 2)

/-- Truncating a run keeps it a run (shifted). -/
theorem occursAt_replicate_shift {x : ℝ} {k d n : ℕ} (j : ℕ) (hj : j ≤ k)
    (h : OccursAt 2 x (List.replicate k d) n) :
    OccursAt 2 x (List.replicate (k - j) d) (n + j) := by
  intro i hi
  rw [List.length_replicate] at hi
  have h2 := h (j + i) (by rw [List.length_replicate]; omega)
  rw [List.getElem_replicate] at h2 ⊢
  rwa [← Nat.add_assoc] at h2

private theorem natLog_le_logb (m : ℕ) (hm : m ≠ 0) :
    (Nat.log 2 m : ℝ) ≤ Real.logb 2 m := by
  have hpow : (2 : ℕ) ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hm
  have hpowR : ((2 : ℝ)) ^ Nat.log 2 m ≤ (m : ℝ) := by exact_mod_cast hpow
  calc (Nat.log 2 m : ℝ) = Real.logb 2 ((2 : ℝ) ^ Nat.log 2 m) := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
        ring
    _ ≤ Real.logb 2 m :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hpowR

/-- **Edge**: `SliverEscape` caps zero-runs.  A run of `k` zeros at
position `n` forces the surrogate into the sliver at every offset `j` with
`2^(k−j) > 2(n+k+1)` (the dichotomy, shifted), i.e. a ride of length
`k − log₂(n+k+1) − 2`; the node then bounds `k` logarithmically. -/
theorem zeroRun_le_of_sliverEscape {C : ℝ} {N₀ : ℕ} (hC : 0 ≤ C)
    (hesc : SliverEscape C N₀) {n k : ℕ} (hn : N₀ ≤ n)
    (h : OccursAt 2 (Real.log 2) (List.replicate k 0) n) :
    (k : ℝ) ≤ C * Real.logb 2 ((n : ℝ) + 2)
      + Real.logb 2 ((n : ℝ) + k + 1) + 2 := by
  set c₀ : ℕ := Nat.log 2 (n + k + 1) + 2 with hc₀_def
  have hcast : ((n + k + 1 : ℕ) : ℝ) = (n : ℝ) + k + 1 := by push_cast; ring
  have hc₀R : (c₀ : ℝ) ≤ Real.logb 2 ((n : ℝ) + k + 1) + 2 := by
    rw [hc₀_def]
    push_cast
    have := natLog_le_logb (n + k + 1) (by omega)
    rw [hcast] at this
    linarith
  have hlogb0 : 0 ≤ Real.logb 2 ((n : ℝ) + 2) :=
    Real.logb_nonneg (by norm_num) (by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith)
  have hc₀pow : 2 * (n + k + 1) < 2 ^ c₀ := by
    have h1 : n + k + 1 < 2 ^ (Nat.log 2 (n + k + 1) + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) _
    have h2 : (2 : ℕ) ^ c₀ = 2 * 2 ^ (Nat.log 2 (n + k + 1) + 1) := by
      rw [hc₀_def]
      ring
    omega
  by_cases hk : k ≤ c₀
  · have : (k : ℝ) ≤ (c₀ : ℝ) := by exact_mod_cast hk
    nlinarith
  · push Not at hk
    have hride : ∀ j, j < k - c₀ →
        1 - 1 / ((n : ℝ) + j + 1) ≤ lnTwoOrbit (n + j) := by
      intro j hj
      have hjk : j ≤ k := by omega
      have hshift := occursAt_replicate_shift j hjk h
      have hkj : 2 * ((n + j : ℕ) + 1) < 2 ^ (k - j) := by
        have hle : 2 * (n + j + 1) ≤ 2 * (n + k + 1) := by omega
        have hexp : (2 : ℕ) ^ c₀ ≤ 2 ^ (k - j) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hkjR : 2 * (((n + j : ℕ) : ℝ) + 1) < 2 ^ (k - j) := by
        exact_mod_cast hkj
      have hsliver := lnTwoOrbit_top_sliver_of_zeroRun hkjR hshift
      have hcast2 : ((n + j : ℕ) : ℝ) = (n : ℝ) + j := by push_cast; ring
      rw [hcast2] at hsliver
      linarith [hsliver]
  -- note: `hsliver : 1 - 1/((n:ℝ)+j+1) ≤ lnTwoOrbit (n+j)` matches the goal
    have hescape := hesc n hn (k - c₀) hride
    have hsub : ((k - c₀ : ℕ) : ℝ) = (k : ℝ) - c₀ := by
      have : c₀ ≤ k := le_of_lt hk
      push_cast [this]
      ring
    rw [hsub] at hescape
    linarith

end NormalNumbers
