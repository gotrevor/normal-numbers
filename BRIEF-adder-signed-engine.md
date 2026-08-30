# BRIEF follow-on 2: signed channels + the engine meta-theorem 🎵🏗️

## RESULT (2026-08-30, autonomous lap)

**ALL THREE OBJECTIVES COMPLETE**, kernel tier, every named theorem audits
`[propext, Classical.choice, Quot.sound]` exactly.

* **Objective 1 (signed channels)** — `AdderSigned.lean`: `ZChannel`
  (`a b : ℤ`, needs one positive coefficient), borrow window
  `[−(a⁻+b⁻), a⁺+b⁺−1]` proved via `carryTZ_eq_floor_fract`
  (`T(n) = ⌊a·fract(X·2ⁿ) + b·fract(Y·2ⁿ)⌋` — cleaner than the unsigned
  case split), offset Nat encoding `c = T + (a⁻+b⁻)`, `Int.emod`/`ediv`
  step (`%`/`/` on ℤ ARE emod/ediv in this pin), signed shadowing.
* **Objective 2 (engine meta-theorem)** — `AdderEngineCore.lean` abstracts
  checker+descent over the predecessor map (`checkCertP`, `HStepP`,
  `inputP_eventually_periodic`; unsigned pipeline is definitionally the
  `famPred` instance).  `signed_engine` (`AdderSigned.lean`): certified
  signed family ⟹ for all X,Y not both rational some channel word occurs
  i.o.  Flagship restated byte-identically as a data instance
  (`AdderSignedInstance.lean`): `Channel.toZ` unsigned fibre, kernel
  certificate transferred with NO recheck
  (`adder_sixfold_disjunction_universal_via_engine`).
* **Objective 3 (musical family)** — pure-stdlib emitter
  `adder_signed_emit.py` (no egress: numpy/scipy/mpmath unavailable;
  crosscheck mode reproduces the frozen main JSON field-for-field) +
  `adder_signed_selftest.py` (integer-atanh true bits, 3492 positions,
  column identity over ℤ, shadowing, and REAL borrows exercised: min
  carries −1, −1, −3 on the signed channels).  Certificate: 15360 ambient
  states, **15 live**, 2 period-2 cycles, ω ≤ 9.
  `adder_musical_disjunction_universal` (any X,Y not both rational:
  00 in X ∨ 11 in Y ∨ 100 in Y−X ∨ 11 in 2X−Y ∨ 00 in 2Y−3X ∨ 010 in X+Y)
  + ln-instance `adder_musical_disjunction`
  (ln 2, ln 3, ln(3/2), ln(4/3), ln(9/8), ln 6) — `AdderMusical.lean`,
  single `decide +kernel` sweep (~2 min), no chunking needed.
* Out of scope (unchanged): k-track channels, other bases, word-sets,
  variety mapping; novelty sweep operator-owned.

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
