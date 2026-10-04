# Barrier library 🧱

The difficulty check says every crux names a known-false sibling its mechanism must fail on.
This library makes that a build check, as `MazeAudit.lean` did for Maze rows (proposal A1 in
`docs/ENGINE-PROPOSALS-2026-10-04.md`).

## Files

| File | Holds |
|---|---|
| `src/NormalNumbers/Barriers/Core.lean` | `Barrier`, `Evidence`, `Tier`, `CruxLink`, `Waiver`, and the `#barrier_audit` command |
| `src/NormalNumbers/Barriers/Siblings.lean` | New sibling statements the repo lacked (all proved) |
| `src/NormalNumbers/Barriers.lean` | The registry: one `def … : Barrier` per sibling, and `allBarriers` |
| `src/NormalNumbers/BarrierAudit.lean` | `cruxLinks` and `waivers`, and a local audit run |
| `src/NormalNumbers.lean` (last lines) | The authoritative audit run, over every module |
| `src/NormalNumbers/Barriers/AuditTest.lean` | Teeth test (not in the root): `lake build NormalNumbers.Barriers.AuditTest` |

## Design

* **A barrier carries its statement and evidence of it.**  `Barrier.proved s h decls guards`
  infers the statement from `h`, so the elaborator checks that the cited theorem proves exactly
  what the barrier claims.  `Barrier.cited s L h …` takes `h : L → P` from a `Literature` Prop
  `L`.  `Barrier.frozen` takes a `sorry` theorem.
* **The tier is checked.**  `collectAxioms` on each declaration: `proved` and `cited` must be
  `sorryAx`-free; a `frozen` barrier whose evidence has become sorry-free must be promoted.
  Each declaration in `decls` must occur in the barrier's value, so the name list cannot drift
  from the evidence.
* **The scan is the teeth.**  The audit lists every declaration in a `NormalNumbers` module whose
  own value mentions `sorryAx` (a direct `sorry`).  Each must be a crux with at least one
  registered barrier, a waiver with a reason, or a frozen barrier's declaration.  A new `sorry`
  anywhere in the build therefore fails `lake build` until someone decides which it is.  A crux or
  waiver whose `sorry` disappears also fails, so both lists track the open frontier.
* **Waivers are the honest "none exists".**  Leaf lemmas, literature-strength analytic inputs
  (Siegel zeros, Bombieri–Vinogradov), wiring steps and refutation bets carry a reason instead
  of a barrier.  Where a sibling is known but not yet in Lean, the waiver names the candidate.
  Converting a waiver to a crux means stating that sibling in `Barriers/Siblings.lean`.
* **Scope.**  `#barrier_audit` sees the environment it runs in.  The run at the end of the root
  file sees every module, and the root rebuilds whenever any module changes.  The run in
  `BarrierAudit.lean` is a fast local check over its own imports.

## Adding things

* **A new headline `sorry`:** state the sibling its mechanism must fail on (a theorem, a
  `Literature` derivation, or a frozen `sorry` with confidence and construction), register it in
  `Barriers.lean`, and add a `CruxLink` in `BarrierAudit.lean` (importing the crux's module).
  The `why` field says what the mechanism must use that the sibling lacks.
* **A leaf `sorry`:** add a `Waiver` with the reason.
* **A sibling gets proved:** change `.frozen` to `.proved`; the audit demands it.

## Open work for a treadmill

The four siblings first frozen in `Barriers/Siblings.lean` (`exists_rat_isNormalUpTo_not_isNormal`,
`exists_isLogNormal_not_isSimplyNormal`, `exists_normal_prefix_limit_not_normal`,
`tsum_two_pow_div_fermat`) are proved (2026-10-04) and registered as `proved`.  The waivers that name a candidate sibling
(`weylLambertTwist_holds`, the C′-quantitative chain at `ρ = log 2`) are the next barriers to
state.
