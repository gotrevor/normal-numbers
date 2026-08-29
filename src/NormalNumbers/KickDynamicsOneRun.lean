/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.KickDynamics

/-!
# The twin edge: sliver escape caps one-runs

Lane-2 target 2 (2026-08-29 operator brief; alien review move 2 — "completes
D7 symmetry").  Mirror of `zeroRun_le_of_sliverEscape` for runs of ones,
via `lnTwoOrbit_top_sliver_of_oneRun`.

## The width mismatch, resolved honestly

The one-run dichotomy (`lnTwoOrbit_top_sliver_of_oneRun`) lands the
surrogate only in the WIDE sliver `1 − 2/(n+1)`: in the no-wraparound
branch it yields `x ≥ 1 − 1/2ᵏ − τ` and the tail bound is only
`τ ≤ 1/(n+1)`, so the narrow sliver `1 − 1/(n+1)` of the frozen node
`SliverEscape` is genuinely out of reach (the tail can really sit near
its upper bound).  Per the draft docstring's mandate we therefore freeze
the wide-sliver variant node `SliverEscapeWide` here (provenance below),
prove the twin edge from it, and note `SliverEscapeWide → SliverEscape`
(a narrow ride is a wide ride), so the wide node is the stronger — and
for the one-run edge the necessary — hypothesis.  The frozen
`SliverEscape` in `KickDynamics.lean` is untouched (ADDITIVE ONLY).
-/

namespace NormalNumbers

open Filter Set

/-- **Node (frozen, OPEN): wide sliver escape.**  The surrogate cannot
ride the wide top sliver `x_{n+j} ≥ 1 − 2/(n+j+1)` for more than
`C·log₂(n+2)` consecutive steps.  Same shape as the frozen narrow node
`SliverEscape`, with sliver width doubled.

Provenance (2026-08-29, width-mismatch resolution): the one-run
dichotomy only certifies the WIDE sliver — its no-wraparound branch
gives `x ≥ 1 − 1/2ᵏ − τ` with tail bound `τ ≤ 1/(n+1)` — so the twin
edge `oneRun_le_of_sliverEscape` needs this variant; the narrow node
cannot serve.  Heuristically as plausible as the narrow node: the
in-sliver dynamics is the same neutral-unstable `δ' = 2δ − κ`, only the
admissible profile is `δ ≤ 2/n` instead of `δ ≤ 1/n`. -/
def SliverEscapeWide (C : ℝ) (N₀ : ℕ) : Prop :=
  ∀ n, N₀ ≤ n → ∀ k : ℕ,
    (∀ j, j < k → 1 - 2 / ((n : ℝ) + j + 1) ≤ lnTwoOrbit (n + j)) →
    (k : ℝ) ≤ C * Real.logb 2 ((n : ℝ) + 2)

/-- The wide node is the stronger hypothesis: a narrow ride is a wide
ride, so wide escape implies narrow escape. -/
theorem sliverEscape_of_wide {C : ℝ} {N₀ : ℕ}
    (h : SliverEscapeWide C N₀) : SliverEscape C N₀ := by
  intro n hn k hride
  refine h n hn k fun j hj => ?_
  have hdiff : 2 / ((n : ℝ) + j + 1) - 1 / ((n : ℝ) + j + 1)
      = 1 / ((n : ℝ) + j + 1) := by ring
  have hp : 0 ≤ 1 / ((n : ℝ) + j + 1) := by positivity
  linarith [hride j hj]

private theorem natLog_le_logb (m : ℕ) (hm : m ≠ 0) :
    (Nat.log 2 m : ℝ) ≤ Real.logb 2 m := by
  have hpow : (2 : ℕ) ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hm
  have hpowR : ((2 : ℝ)) ^ Nat.log 2 m ≤ (m : ℝ) := by exact_mod_cast hpow
  calc (Nat.log 2 m : ℝ) = Real.logb 2 ((2 : ℝ) ^ Nat.log 2 m) := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
        ring
    _ ≤ Real.logb 2 m :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hpowR

/-- **Twin edge**: wide sliver escape caps one-runs of binary `ln 2`,
mirroring `zeroRun_le_of_sliverEscape`.  A run of `k` ones at position
`n ≥ 1` forces the surrogate into the wide sliver at every offset `j`
with `2^(k−j) > 2(n+k+1)` (the one-run dichotomy, shifted), i.e. a wide
ride of length `k − log₂(n+k+1) − 2`; the wide node then bounds `k`
logarithmically.  Restated from the draft (2026-08-29): hypothesis is
the wide node (width mismatch, see module docstring), constant tightened
from the draft's `+3` to the `+2` the mirror proof actually yields. -/
theorem oneRun_le_of_sliverEscape {C : ℝ} {N₀ : ℕ} (hC : 0 ≤ C)
    (hesc : SliverEscapeWide C N₀) {n k : ℕ} (hn : N₀ ≤ n) (hn1 : 1 ≤ n)
    (h : OccursAt 2 (Real.log 2) (List.replicate k 1) n) :
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
        1 - 2 / ((n : ℝ) + j + 1) ≤ lnTwoOrbit (n + j) := by
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
      have hsliver := lnTwoOrbit_top_sliver_of_oneRun
        (show 1 ≤ n + j by omega) hkjR hshift
      have hcast2 : ((n + j : ℕ) : ℝ) = (n : ℝ) + j := by push_cast; ring
      rw [hcast2] at hsliver
      linarith [hsliver]
    have hescape := hesc n hn (k - c₀) hride
    have hsub : ((k - c₀ : ℕ) : ℝ) = (k : ℝ) - c₀ := by
      have : c₀ ≤ k := le_of_lt hk
      push_cast [this]
      ring
    rw [hsub] at hescape
    linarith

end NormalNumbers
