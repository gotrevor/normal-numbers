/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderCert

/-!
# Range-split certificate checking (kernel-tier chunking support)

`decide +kernel` on the full 73728-state sweep is a single long kernel
evaluation; splitting it into ranges lets each chunk stay within the
heartbeat budget and parallelize across olean jobs.  `edgeOk` is the
per-state body of `checkEdges`; `checkEdgesOn lo n` sweeps `[lo, lo+n)`;
`checkEdges_of_edgeOk` reassembles the full check.
-/

namespace NormalNumbers.Adder

/-- Per-state edge check — definitionally the body of `checkEdges`. -/
def edgeOk (chs : List Channel) (live : ℕ → Bool) (rho omega : ℕ → ℕ)
    (forced : ℕ → Option (ℕ × ℕ)) (s' : ℕ) : Bool :=
  (List.range 4).all fun σ =>
    match famPred chs (σ % 2) (σ / 2) s' with
    | none => true
    | some s =>
      if live s then
        !live s' || (decide (rho s' < rho s)
          || (decide (forced s = some (σ, s')) && decide (rho s' = rho s)))
      else
        !live s' && decide (omega s' < omega s)

/-- Chunked sweep over `[lo, lo + n)`. -/
def checkEdgesOn (chs : List Channel) (live : ℕ → Bool) (rho omega : ℕ → ℕ)
    (forced : ℕ → Option (ℕ × ℕ)) (lo n : ℕ) : Bool :=
  (List.range n).all fun i => edgeOk chs live rho omega forced (lo + i)

theorem checkEdgesOn_spec {chs : List Channel} {live : ℕ → Bool}
    {rho omega : ℕ → ℕ} {forced : ℕ → Option (ℕ × ℕ)} {lo n : ℕ}
    (h : checkEdgesOn chs live rho omega forced lo n = true) :
    ∀ i, i < n → edgeOk chs live rho omega forced (lo + i) = true := by
  unfold checkEdgesOn at h
  rw [List.all_eq_true] at h
  exact fun i hi => h i (List.mem_range.2 hi)

theorem checkEdges_of_edgeOk {chs : List Channel} {S : ℕ} {live : ℕ → Bool}
    {rho omega : ℕ → ℕ} {forced : ℕ → Option (ℕ × ℕ)}
    (h : ∀ s', s' < S → edgeOk chs live rho omega forced s' = true) :
    checkEdges chs S live rho omega forced = true := by
  unfold checkEdges
  rw [List.all_eq_true]
  intro s' hs'
  exact h s' (List.mem_range.1 hs')

theorem checkCert_of_parts {chs : List Channel} {S : ℕ} {live : ℕ → Bool}
    {rho omega : ℕ → ℕ} {forced : ℕ → Option (ℕ × ℕ)}
    (h₁ : checkEdges chs S live rho omega forced = true)
    (h₂ : checkForced chs S live forced = true) :
    checkCert chs S live rho omega forced = true := by
  unfold checkCert
  rw [h₁, h₂]
  rfl

end NormalNumbers.Adder
