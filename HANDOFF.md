# HANDOFF — Stoneham campaign: prove the 7 sorries in `src/NormalNumbers/Stoneham.lean`

**Objective**: `isNormal_two_stoneham23` — Stoneham (1973): `α₂,₃ = Σ 1/(3ᵐ·2^(3ᵐ))` is
normal in base 2.  All 7 `src/` sorries live in `Stoneham.lean`; `src/` sorry-free = done.

**Route**: hot-spot, per the module docstring in `Stoneham.lean`.  Everything is exact
counting in `(ℤ/3^M)ˣ` except `isNormal_of_visit_upper_bound`, whose statement is
**PINNED** (2026-08-23) against `papers/bailey-misiurewicz-2006-hot-spot.md` — do not
weaken or reshape that statement; the proof route is free (the paper's ergodic argument
or elementary block counting; the pin note lists mathlib candidates to grep).
💎 The pin note's "Section 4 cross-check" table maps the paper's own proof of our exact
theorem onto our decomposition — read it before the counting lemmas, and cross-check
against it in review laps.  Expect a single-digit uniform constant (theirs is `C = 8`)
out of the window counting.
⚠️ Do NOT revive the mod-3^M′ cascade plan — known-flawed (it localizes the *low*
digits, not position).

**Suggested order** (counting first, analysis last):
`stonehamState_succ` → `stonehamState_unit` → `card_units_Ico` → `stonehamState_approx`
→ `segment_visit_upper` → `isNormal_of_visit_upper_bound` → `isNormal_two_stoneham23`.

**Existing assets — grep before re-proving**: `StonehamArith` (2 is a primitive root mod
`3^M`, order `2·3^(M-1)`), the DigitInterval toolkit (`digits_prefix_iff`, shift lemma),
the sequence↔real Bridge (`isNormal_realOfDigits`), counting/visit algebra, b-adic
sandwich.  `ROADMAP.md` has the programme map.

**Hygiene**: park exploratory/helper sorries under `wip/`, keep `src/` honest; commit
green builds; `#print axioms isNormal_two_stoneham23` at the end (target: standard 3).
