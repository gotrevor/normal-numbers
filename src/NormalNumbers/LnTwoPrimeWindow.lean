/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.NumberTheory.Bertrand
import NormalNumbers.LnTwoLattice

/-!
# The prime-window door (R3): sparse separation suffices

Companion to `docs/lit-sweep-2026-08-29.md` (the Fermat-quotient bridge)
and `LnTwoLattice.lean` (the certificate surface).  Two observations make
prime-adjacent positions special:

1. **Arithmetic handle.**  At `n = p − 1` the surrogate numerator carries
   Fermat-quotient arithmetic: `A_{p−1} ≡ L_{p−1} · q_p(2) (mod p)` where
   `q_p(2) = (2^{p−1} − 1)/p mod p` — the Glaisher / Z.-H. Sun congruence.
   Probe (`experiments/lntwo_fermat_bridge.py`, 2026-08-29): verified
   exactly for ALL 2261 primes `3 ≤ p < 20000`, zero failures, with the
   unit pinned as `L_{p−1} mod p`; the degenerate case `q_p(2) ≡ 0` is
   precisely the Wieferich condition, and the probe recovers exactly the
   two known Wieferich primes 1093, 3511.  So a super-threshold run at
   `p − 1` forces (through the unique-candidate certificate,
   `zeroRun_res_eq_ceil`) a *specific* value of the Fermat quotient — a
   Wieferich-type coincidence.
2. **Sparse positions suffice.**  A long run crosses many positions, so a
   run cap enforced only on a sparse set covers every position at the cost
   of the gap to that set (`occursAt_replicate_suffix`).  With Bertrand
   the gap is `< n`; any prime-gap improvement (e.g. Baker–Harman–Pintz
   `n^{0.525}`, under nothing) sharpens the edge for free.

This file freezes the door as ONE node and wires the covering edge:

* `occursAt_replicate_suffix` (unconditional): a suffix of a run is a run;
* `LnTwoPrimeRunBound g P₀` (frozen node): runs *at prime-adjacent
  positions* `p − 1` are capped by `g (p−1)`.  🎭 Costume-honest: this is
  `LnTwoDyadicSep`-strength information RESTRICTED to `n = p − 1` — not a
  new wall, but the restriction to positions carrying the arithmetic
  handle above, which is exactly what the congruence door could someday
  discharge;
* `run_le_of_primeRunBound` (the covering edge, unconditional wiring):
  the sparse node caps runs at EVERY position `n ≥ max(P₀,1)` by
  `(p − 1 − n) + g (p−1)` for a Bertrand prime `p ∈ (n, 2n]`.

Lagarias guardrail: the node is Diophantine input, named as such; nothing
here claims a density or growth conclusion unconditionally.
-/

namespace NormalNumbers

/-- **Run propagation** (unconditional): a suffix of a digit run is a
digit run — a run of `k` copies of `d` at position `n` yields a run of
`k − j` copies at position `n + j`. -/
theorem occursAt_replicate_suffix {b : ℕ} {x : ℝ} {d n k j : ℕ} (hj : j ≤ k)
    (h : OccursAt b x (List.replicate k d) n) :
    OccursAt b x (List.replicate (k - j) d) (n + j) := by
  intro i hi
  rw [List.length_replicate] at hi
  have h2 := h (j + i) (by rw [List.length_replicate]; omega)
  simp only [List.getElem_replicate] at h2 ⊢
  rw [show n + j + i = n + (j + i) by omega]
  exact h2

/-- **Frozen node (R3, the prime-window door).**  Runs of binary `ln 2`
at prime-adjacent positions `p − 1` (`p ≥ P₀` prime) are capped by
`g (p − 1)`.

Provenance: through the unique-candidate certificate
(`zeroRun_res_eq_ceil` / `oneRun_res_eq_ceil_sub_one`), a super-threshold
run at `p − 1` forces the integer identity
`lnTwoRes (p−1) = ⌈latticeCenter (p−1)⌉`, and
`lnTwoNum (p−1) ≡ lcmRange (p−1) · q_p(2) (mod p)` (Fermat-quotient
bridge, probe-verified for all primes below 20000) — so the run forces a
specific Fermat-quotient value, a Wieferich-type coincidence.  Heuristic
odds: `q_p(2)` is empirically uniform mod `p`, so each coincidence has
probability `~1/p`; discharging the node needs number theory beyond
current reach (non-Wieferich infinitude is open, known under abc).
🎭 Costume-honest: restricted-to-`p−1` dyadic separation, frozen because
these are the positions with an arithmetic handle. -/
def LnTwoPrimeRunBound (g : ℕ → ℕ) (P₀ : ℕ) : Prop :=
  ∀ p k : ℕ, p.Prime → P₀ ≤ p →
    (OccursAt 2 (Real.log 2) (List.replicate k 0) (p - 1) ∨
      OccursAt 2 (Real.log 2) (List.replicate k 1) (p - 1)) →
    k ≤ g (p - 1)

/-- **The covering edge** (unconditional wiring): the sparse prime-window
node caps runs at EVERY position — any run at `n` crosses `p − 1` for a
Bertrand prime `p ∈ (n, 2n]`, so its tail there is capped and
`k ≤ (p − 1 − n) + g (p − 1)`.  Sparse separation suffices, at the cost
of one prime gap. -/
theorem run_le_of_primeRunBound {g : ℕ → ℕ} {P₀ : ℕ}
    (hnode : LnTwoPrimeRunBound g P₀) {n k d : ℕ}
    (hn0 : 1 ≤ n) (hn : P₀ ≤ n) (hd : d = 0 ∨ d = 1)
    (h : OccursAt 2 (Real.log 2) (List.replicate k d) n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 2 * n ∧ k ≤ (p - 1 - n) + g (p - 1) := by
  obtain ⟨p, hp, hnp, hp2n⟩ := Nat.bertrand n (by omega)
  refine ⟨p, hp, hnp, hp2n, ?_⟩
  set j := p - 1 - n with hj
  rcases Nat.lt_or_ge j k with hjk | hkj
  · have hsuf := occursAt_replicate_suffix (le_of_lt hjk) h
    rw [show n + j = p - 1 by omega] at hsuf
    have hcap : k - j ≤ g (p - 1) := by
      apply hnode p (k - j) hp (by omega)
      rcases hd with rfl | rfl
      · exact Or.inl hsuf
      · exact Or.inr hsuf
    omega
  · omega

end NormalNumbers
