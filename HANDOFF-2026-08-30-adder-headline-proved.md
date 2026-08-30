# HANDOFF: adder six-fold disjunction PROVED (phase-1); kernel swap in flight 🧮

Lap of 2026-08-30, branch `wip/adder-disjunction`.  The operator addendum in
DIRECTION.md is essentially discharged: the brief's RESULT section is written
(see `BRIEF-adder-disjunction-formalization.md` top).

## State

- **`adder_sixfold_disjunction` (`AdderMain.lean`) is PROVED**, build green
  (8798 jobs).  Axioms: trust triple + the one disclosed per-site
  `main_cert_ok._native.native_decide.ax_1_1` (phase-1 tolerance).
- **`toy_disjunction` is kernel-tier end-to-end**, trust triple exactly —
  the pipeline validation the brief demanded.
- Modules: Carry → Automaton → Shadow → Cert(+Toy) → Descent → Endgame →
  CertMain → Main.  All committed green, one coherent checkpoint each.

## In flight (the ONE open item)

`src/NormalNumbers/AdderCertMainKernel.lean` (untracked until green):
kernel-tier re-encoding of the main certificate — omega/live packed 64
states per Nat chunk (base 8 / bits) in 36×32 two-level lists, rho/forced
assoc tables, `main_cert_ok_kernel` by `decide +kernel` with
`maxHeartbeats 8000000`.  Probe timing: 4096-state sweep ≈ 10 s kernel →
full ≈ 3–4 min; first full attempt hit the kernel deterministic timeout at
default heartbeats, retry with 8M is running.  If green: import it in
`AdderMain.lean`, swap `main_cert_ok` → `main_cert_ok_kernel` in the
`refine`, re-audit (should become trust triple), update RESULT.  If the
heartbeat budget still trips, fall back to range-splitting `checkEdges`
(add `checkEdgesOn lo n`, prove a `List.range` append-split lemma, 8
theorems of ~9216 states each, conjoin).

## Gotchas rediscovered this lap

- `Nat.add_mul_div_left/right` choose by which side the divisor multiplies;
  `omega` atomizes `m₀+(n+1)` vs `(m₀+n)+1` — bridge with defeq `show`.
- `rw [show ch.ell = (ch.ell-1)+1 …]` rewrites INSIDE `ch.ell - 1` too;
  use `conv_lhs` to target one occurrence.
- `Option.some.inj` on a pair gives a `Prod` equality — project with
  `Prod.mk.inj`.
- This pin: `Irrational.sub_intCast` (not `sub_int`); `push Not` (push_neg
  deprecated); native axioms are per-site (`…._native.native_decide.ax_1_1`).
- `ByteArray` has no `get?` field here — use `dite` on `size` with `get`.
