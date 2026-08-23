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

---

## Lap update 2026-08-23 (hot-spot campaign, lap A)

**HEAD**: `583c088` on `master`.  No uncommitted edits.

**⚠️ Toolchain blocker**: the box has no v4.33.1 Lean toolchain (elan mount is
read-only with only 4.29.1/4.31.0; no egress).  `lake build` is IMPOSSIBLE here
until the host answers `ON-LINE-REQUEST.md`.  All new work is compiler-verified
against the built v4.31.0 mathlib in `~/src/goodstein-ab-med` via the harness
`<scratchpad>/check.sh` (direct `lean` + LEAN_PATH; repo imports → Mathlib.Tactic
+ `stub.lean` axiom-stubs of Sandwich/Wall interfaces).  Re-verify in-repo
(`lake build`) the moment the toolchain lands, before trusting anything here.

**Done (new module `src/NormalNumbers/HotSpot.lean`, ~1050 lines, zero sorries)**:
elementary proof of the hot-spot crux — no Birkhoff/Vitali/ergodicity:
counting kit (`card_filter_div/mod/mod_div`, `card_filter_subword[_pair]`),
moments (`sum_occCount`, `sum_occCount_sq_le`), Chebyshev (`card_badSet_le`),
orbit layer (`mem_cell_iff_floor`, `orbit_add`, `cellAt`, `subword_cellAt`),
sliding double count (`sum_occCount_cellAt_{eq,le}`, `le_sum_occCount_cellAt`),
good/bad bounds (`cell_visits_{upper,lower}`, `card_cellAt_mem`), and the
squeeze `tendsto_cell_of_visit_upper` → `equidistributed_orbit_of_visit_upper`.

**Next steps** (in order):
1. In `Stoneham.lean`: `import NormalNumbers.HotSpot`, prove the pinned
   `isNormal_of_visit_upper_bound` ≈ 3 lines:
   `rw [isNormal_iff_equidistributed_orbit b hb x]`; apply
   `equidistributed_orbit_of_visit_upper` at `x' := Int.fract x` (hypothesis h
   is already stated for `orbit b (Int.fract x)`); transport with
   `funext (orbit_fract b x)`.
2. Then the six counting sorries (`stonehamState_succ` → `segment_visit_upper`
   → final assembly) per the original suggested order above.
3. To scratch-verify `Stoneham.lean` pieces, extend `stub.lean` or develop
   lemma bodies standalone; `check.sh <file> [stub]` is the loop.

**Gotchas hit (v4.31 mathlib)**: `Finset.card_nbij'` wants `Finset.mem_coe` in
simp sets; `Nat.mul_add_div/mod` need the modulus as FIRST factor (mul_comm
first); `pow_le_pow_left` absent → `mul_self_le_mul_self` + `sq`; iff form of
`mul_le_mul_right` absent → `le_of_mul_le_mul_right`; `set`-bound `K/N/T/An/Bn`
must be `clear_value`d or nlinarith/whnf times out; prefer `linarith [explicit
product hints]` over bare `nlinarith` in the squeeze.
