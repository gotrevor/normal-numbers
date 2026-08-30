/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderEngineCore

/-!
# Range-split checking for the parametric engine

The `AdderCertSplit` chunking machinery, abstracted over the predecessor
map: `edgeOkP` is the per-state body of `checkEdgesP`, `checkEdgesOnP`
sweeps `[lo, lo+n)`, and `checkEdgesP_of_edgeOkP` reassembles the full
check — so signed-family certificates can be kernel-checked in
heartbeat-sized chunks exactly like the unsigned main certificate.
-/

namespace NormalNumbers.Adder

/-- Per-state edge check — definitionally the body of `checkEdgesP`. -/
def edgeOkP (fpred : ℕ → ℕ → ℕ → Option ℕ) (live : ℕ → Bool)
    (rho omega : ℕ → ℕ) (forced : ℕ → Option (ℕ × ℕ)) (s' : ℕ) : Bool :=
  (List.range 4).all fun σ =>
    match fpred (σ % 2) (σ / 2) s' with
    | none => true
    | some s =>
      if live s then
        !live s' || (decide (rho s' < rho s)
          || (decide (forced s = some (σ, s')) && decide (rho s' = rho s)))
      else
        !live s' && decide (omega s' < omega s)

/-- Chunked sweep over `[lo, lo + n)`. -/
def checkEdgesOnP (fpred : ℕ → ℕ → ℕ → Option ℕ) (live : ℕ → Bool)
    (rho omega : ℕ → ℕ) (forced : ℕ → Option (ℕ × ℕ)) (lo n : ℕ) : Bool :=
  (List.range n).all fun i => edgeOkP fpred live rho omega forced (lo + i)

theorem checkEdgesOnP_spec {fpred : ℕ → ℕ → ℕ → Option ℕ} {live : ℕ → Bool}
    {rho omega : ℕ → ℕ} {forced : ℕ → Option (ℕ × ℕ)} {lo n : ℕ}
    (h : checkEdgesOnP fpred live rho omega forced lo n = true) :
    ∀ i, i < n → edgeOkP fpred live rho omega forced (lo + i) = true := by
  unfold checkEdgesOnP at h
  rw [List.all_eq_true] at h
  exact fun i hi => h i (List.mem_range.2 hi)

theorem checkEdgesP_of_edgeOkP {fpred : ℕ → ℕ → ℕ → Option ℕ} {S : ℕ}
    {live : ℕ → Bool} {rho omega : ℕ → ℕ} {forced : ℕ → Option (ℕ × ℕ)}
    (h : ∀ s', s' < S → edgeOkP fpred live rho omega forced s' = true) :
    checkEdgesP fpred S live rho omega forced = true := by
  unfold checkEdgesP
  rw [List.all_eq_true]
  intro s' hs'
  exact h s' (List.mem_range.1 hs')

theorem checkCertP_of_parts {fpred : ℕ → ℕ → ℕ → Option ℕ} {S : ℕ}
    {live : ℕ → Bool} {rho omega : ℕ → ℕ} {forced : ℕ → Option (ℕ × ℕ)}
    (h₁ : checkEdgesP fpred S live rho omega forced = true)
    (h₂ : checkForcedP fpred S live forced = true) :
    checkCertP fpred S live rho omega forced = true := by
  unfold checkCertP
  rw [h₁, h₂]
  rfl

end NormalNumbers.Adder
