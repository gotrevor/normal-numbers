# BRIEF follow-on 2: signed channels + the engine meta-theorem 🎵🏗️

**Operator-authorized 2026-08-29 (Trevor, attended session).**  Execute AFTER
`BRIEF-adder-universal.md`.  Goal: make families **data**, then land the musical
disjunction as the first data-swap instance.

## Objective 1 — signed coefficients (borrow channels)

Generalize `Channel` to `a b : ℤ` (nonzero pair).  The mathematics:

- **Carry/borrow window**: for `z = aX + bY`,
  `T(n) = ⌊2ⁿz⌋ − a⌊2ⁿX⌋ − b⌊2ⁿY⌋ ∈ [−(a⁻+b⁻), a⁺+b⁺−1]`
  (positive/negative parts; window size `|a|+|b|`; strictness at the edges argued
  exactly like the current `carryT_le` case split).  Nat-encode carries with
  offset `+(a⁻+b⁻)`.
- **Column identity**: unchanged — it is a `ring` identity, already valid over ℤ.
- ⚠️ **Lean `Int` division is T-division.**  The automaton step needs the
  floor-consistent pair: use `v % 2 ∈ {0,1}` and `v / 2` such that
  `v = 2·(v/2) + v%2` for possibly-negative `v` — `Int.emod`/`Int.ediv` with
  positive modulus give exactly this; do NOT use `Int.div`.  Mirror the same
  convention in the Python emitter (Python `%`/`//` already floor — they match
  emod/ediv on positive modulus).
- Shadowing, descent, checker, endgame: descent and the certificate checker see
  only Nat states — untouched.  Shadowing needs the offset plumbed through.

## Objective 2 — the engine meta-theorem, stated once

> For any finite family of channels `(aᵢ, bᵢ) ∈ ℤ² ∖ {0}` with binary words
> `wᵢ`, if the family's automaton admits a valid `(live, ρ, forced, ω)`
> certificate (the C1/C1'/C3' conditions, checked), then for all `X Y : ℝ` not
> both rational, some `wᵢ` occurs infinitely often in the binary expansion of
> `aᵢX + bᵢY`.

Then restate the flagship (`adder_sixfold_disjunction_universal`) as an instance,
byte-identical conclusion — do not weaken or move the already-frozen statements.

## Objective 3 — the musical family as the first data swap

Family (exact-verified by probe, master commit `cf1ba1c`, 9 478 live states):
`(1,0)/00 · (0,1)/11 · (−1,1)/100 · (2,−1)/11 · (−3,2)/00 · (1,1)/010`
(instance constants: ln 2, ln 3, ln(3/2), ln(4/3), ln(9/8), ln 6).

1. Extend `experiments/adder_certificate_emit.py` to signed channels (same
   offset encoding bit-for-bit as Lean), emit + re-verify C1/C1'/C3' in Python
   (emitter refuses on failure, as now).
2. Extend `experiments/adder_cert_selftest.py`: shadowing anchor against the true
   bits of the six constants (mpmath), including a NEGATIVE-carry position check
   (a borrow actually exercised), before freezing the Lean data.
3. Land `adder_musical_disjunction` (universal form + ln-instance corollary via
   `Real.log_div`/`log_mul` rewrites).  All words (`00`, `11`, `100`, `010`) are
   open per the Adamczewski–Rampersad boundary — note it in the docstring.

Certificate route per two-lanes: `decide` kernel-tier if it fits (9 478 live
states is the smallest known), `native_decide` disclosed otherwise.

Out of scope: k-track (three reals) channels, other bases, word-sets per channel,
exhaustive variety mapping — later briefs; novelty sweep stays operator-owned.
