/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderAutomaton

/-!
# The certificate checker (module 3 of the adder wing)

Brief: `BRIEF-adder-disjunction-formalization.md` §"The certificate".

A certificate for a channel family consists of four tables over the ambient
state space `[0, S)`: `live` (the set `L`), `rho` (rank), `omega`
(dead-depth), and `forced` (the unique intra-cycle successor edge).  The
checker sweeps every `(σ, s')` — the automaton is backward-deterministic, so
each pair carries at most one edge `HStep s σ s'` with `s = famPred σ s'` —
and verifies the three local conditions:

* **(C1)** live `s`, live `s'`: `rho s' < rho s`, or
  `forced s = some (σ, s')` with `rho s' = rho s`;
* **(C3')** dead `s`: `s'` is dead and `omega s' < omega s`;
* **(C1')** `forced s = some (σ, s')` implies the edge is legal, in-range,
  and `s'` is live.

`checkEdges_c1`, `checkEdges_c3'`, `checkForced_spec` extract the semantic
content from a `check… = true` fact (proved by `decide` for the toy family,
`native_decide` for the main family).
-/

namespace NormalNumbers.Adder

/-- Sweep every `(σ, s')` with `σ < 4`, `s' < S`; on each legal edge
`HStep s σ s'` check (C1) (live case) or (C3') (dead case). -/
def checkEdges (chs : List Channel) (S : ℕ) (live : ℕ → Bool)
    (rho omega : ℕ → ℕ) (forced : ℕ → Option (ℕ × ℕ)) : Bool :=
  (List.range S).all fun s' =>
    (List.range 4).all fun σ =>
      match famPred chs (σ % 2) (σ / 2) s' with
      | none => true
      | some s =>
        if live s then
          !live s' || (decide (rho s' < rho s)
            || (decide (forced s = some (σ, s')) && decide (rho s' = rho s)))
        else
          !live s' && decide (omega s' < omega s)

/-- (C1'): every `forced` edge is legal, in-range, and lands live. -/
def checkForced (chs : List Channel) (S : ℕ) (live : ℕ → Bool)
    (forced : ℕ → Option (ℕ × ℕ)) : Bool :=
  (List.range S).all fun s =>
    match forced s with
    | none => true
    | some (σ, s') =>
      decide (σ < 4) && decide (s' < S) && live s'
        && decide (famPred chs (σ % 2) (σ / 2) s' = some s)

/-- The full certificate check. -/
def checkCert (chs : List Channel) (S : ℕ) (live : ℕ → Bool)
    (rho omega : ℕ → ℕ) (forced : ℕ → Option (ℕ × ℕ)) : Bool :=
  checkEdges chs S live rho omega forced && checkForced chs S live forced

/-! ## Semantic extraction -/

theorem checkEdges_c1 {chs : List Channel} {S : ℕ} {live : ℕ → Bool}
    {rho omega : ℕ → ℕ} {forced : ℕ → Option (ℕ × ℕ)}
    (h : checkEdges chs S live rho omega forced = true)
    {s σ s' : ℕ} (hσ : σ < 4) (hs' : s' < S)
    (hstep : HStep chs s σ s') (hl : live s = true) (hl' : live s' = true) :
    rho s' < rho s ∨ (forced s = some (σ, s') ∧ rho s' = rho s) := by
  unfold checkEdges at h
  rw [List.all_eq_true] at h
  have h₁ := h s' (List.mem_range.2 hs')
  rw [List.all_eq_true] at h₁
  have h₂ := h₁ σ (List.mem_range.2 hσ)
  unfold HStep at hstep
  rw [hstep] at h₂
  simp only [hl, hl', if_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq] at h₂
  tauto

theorem checkEdges_c3' {chs : List Channel} {S : ℕ} {live : ℕ → Bool}
    {rho omega : ℕ → ℕ} {forced : ℕ → Option (ℕ × ℕ)}
    (h : checkEdges chs S live rho omega forced = true)
    {s σ s' : ℕ} (hσ : σ < 4) (hs' : s' < S)
    (hstep : HStep chs s σ s') (hl : live s = false) :
    live s' = false ∧ omega s' < omega s := by
  unfold checkEdges at h
  rw [List.all_eq_true] at h
  have h₁ := h s' (List.mem_range.2 hs')
  rw [List.all_eq_true] at h₁
  have h₂ := h₁ σ (List.mem_range.2 hσ)
  unfold HStep at hstep
  rw [hstep] at h₂
  simp [hl] at h₂
  exact h₂

theorem checkForced_spec {chs : List Channel} {S : ℕ} {live : ℕ → Bool}
    {forced : ℕ → Option (ℕ × ℕ)}
    (h : checkForced chs S live forced = true)
    {s σ s' : ℕ} (hs : s < S) (hf : forced s = some (σ, s')) :
    σ < 4 ∧ s' < S ∧ live s' = true ∧ HStep chs s σ s' := by
  unfold checkForced at h
  rw [List.all_eq_true] at h
  have h₁ := h s (List.mem_range.2 hs)
  rw [hf] at h₁
  simp only [Bool.and_eq_true, decide_eq_true_eq, HStep] at h₁ ⊢
  tauto

theorem checkCert_edges {chs : List Channel} {S : ℕ} {live : ℕ → Bool}
    {rho omega : ℕ → ℕ} {forced : ℕ → Option (ℕ × ℕ)}
    (h : checkCert chs S live rho omega forced = true) :
    checkEdges chs S live rho omega forced = true := by
  simp only [checkCert, Bool.and_eq_true] at h
  exact h.1

theorem checkCert_forced {chs : List Channel} {S : ℕ} {live : ℕ → Bool}
    {rho omega : ℕ → ℕ} {forced : ℕ → Option (ℕ × ℕ)}
    (h : checkCert chs S live rho omega forced = true) :
    checkForced chs S live forced = true := by
  simp only [checkCert, Bool.and_eq_true] at h
  exact h.2

end NormalNumbers.Adder
