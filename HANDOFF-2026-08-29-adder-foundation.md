# HANDOFF: adder six-fold disjunction — foundation laid, execute the brief 🧮

**Read `BRIEF-adder-disjunction-formalization.md` first; it governs.**  This baton
records what the attended 2026-08-29 session already landed (do NOT re-derive), one
operator route-correction, and the module order.  Lane: novel candidate theorem,
occurrence currency; phase-1 tolerances allowed (`native_decide` disclosed), kernel
tier is the stretch.

## Done — build green (8715 jobs), committed, do not redo

- **Python certificate layer** (`experiments/adder_certificate_emit.py`,
  `experiments/adder_cert_selftest.py`, certs in `experiments/certs/*.json`).
  Emitter rebuilds the automaton on the LEAN conventions (independent of the
  probe's KMP encoding), computes `live/rho/omega/forced`, and re-verifies
  C1/C1'/C3' at emit time, refusing on failure.  **Main family: 73728 ambient, 75
  live states, 8 simple cycles (periods 1,2), rho ≤ 12, omega ≤ 7.  Toy: 16
  ambient, 7 live.**  Self-test anchors every convention against the true bits of
  ln 2 / ln 3 (3492 positions): carries in range, column identity exact, shadowing
  *biconditional* with word occurrence, survivor (10)^∞ live.  Rerun both scripts
  if in doubt; they are self-checking.
- **`src/NormalNumbers/AdderAutomaton.lean`** — `Channel`, `famSize`, `famPred`,
  `HStep`, `mainFamily`, `toyFamily`.  🧊 The conventions in its docstring are the
  frozen mirror of the emitter; change neither side alone.  Key structural fact:
  `HStep s σ s' ↔ famPred (σ%2) (σ/2) s' = some s` — the automaton is
  **backward-deterministic**, so every certificate condition is a sweep over
  `(σ, s')` with table lookups (≈ 300k checks, main).
- **`src/NormalNumbers/AdderCarry.lean`** — `rdigit`, `carryT`, bounds
  (`carryT_nonneg`, `carryT_le`, needs `1 ≤ a + b`), column identity
  (`carry_column`), digitOf bridge (`rdigit_eq_digitOf`).
- **`src/NormalNumbers/LnTwoIrrational.lean`** — `irrational_log_two`,
  axiom-clean `[propext, Classical.choice, Quot.sound]` (verified 2026-08-29).

## ⚠️ Operator route-correction (2026-08-29, overrides brief §Endgame)

The brief said to derive `Irrational (Real.log 2)` from `lnTwoExpSep_holds`.
**That implication is unsound** (separation is a lower bound; rationals with odd
denominator satisfy it) and mathlib has no substitute in this pin.  The correct
route is **already landed**: use `irrational_log_two` (Legendre route,
`legendre_log_two_small` + `lcmUpto_mul_geom_tendsto_zero`).  Everything else in
the brief's endgame stands.

## Module order (toy pipeline end-to-end BEFORE the main certificate)

1. **`AdderShadow.lean`** — the true state and the shadowing lemma.
   `winCode z m ℓ : ℕ` = `∑ j < ℓ-1, (rdigit z (m+j)).toNat * 2^j`;
   `chanCode ch X Y m = (carryT …  m).toNat * ch.winSize + winCode (a·X+b·Y) m ch.ell`;
   `famState` folds channels exactly as `famSize` (channel 0 least significant).
   Shadowing: if no channel word occurs at position `m` (`¬ OccursAt 2 (aX+bY)
   ch.word m` per channel), then
   `famPred chs (rdigit X m).toNat (rdigit Y m).toNat (famState … (m+1)) = some
   (famState … m)`.  Per-channel core: column identity turns
   `v = a·x + b·y + T(m+1)` into `digit + 2·T(m)` in ℕ; the formed ℓ-bit window
   `v%2 + 2·w'` equals the word-Nat iff the word occurs at `m` (needs a
   `foldr`-value injectivity lemma for equal-length bit lists — prove it once,
   by induction).  Needs `1 ≤ a+b` and `1 ≤ ℓ` side conditions (both families
   satisfy them; carry them as hypotheses `∀ ch ∈ chs, …`).
2. **`AdderCertToy.lean` + checker** — generate Lean data from
   `experiments/certs/adder_cert_toy.json` (16 states: inline arrays are fine).
   Checker over `(σ, s')`: for each, `famPred` + table lookups verifying C1, C1',
   C3' (semantics in the emitter docstring).  Prove `check… = true` by `decide`
   (toy is tiny) — this settles the module-3 route at toy scale.
3. **`AdderDescent.lean`** — from an infinite `HStep` path with all states
   `< famSize` and the checked conditions: (a) if some state ∉ L, C3' forces an
   infinite strictly-decreasing `omega` chain — impossible; (b) so the path stays
   in L, `rho` is non-increasing with finitely many drops; beyond the last drop
   every step equals `forced` (a function), so by pigeonhole the state sequence
   is eventually periodic AND the input labels `σ_m` (a function of the state via
   `forced`) are too.  No König, no compactness.
4. **`AdderEndgame.lean`** — eventually periodic `σ_m` ⟹ eventually periodic
   `rdigit X m` (x = σ%2) ⟹ `Int.fract (log 2)` has two orbit points
   (`orbit 2 x N`, `orbit 2 x (N+p)`) with identical digit streams ⟹ equal reals
   (nested cylinders via `digits_prefix_iff`; both in `[0,1)` by
   `orbit_mem_Ico`) ⟹ `2^N(2^p−1)·log 2 ∈ ℤ` ⟹ rational ⟹ contradicts
   `irrational_log_two`.  Only the X stream is needed.  Quantifier bookkeeping:
   negate the six-fold disjunction, take `N₀` = max of the six thresholds, apply
   shadowing + descent.  Constants: `log 6 = log 2 + log 3` etc. via
   `Real.log_mul`/`Real.log_pow` (6=2·3, 18=2·9, 12=4·3, 54=2·27).
5. **`AdderCertMain.lean`** — main-family data (75 live entries + assoc lists for
   rho/forced; omega for all 73728 states, values ≤ 7 — a digit-string decoded to
   an Array beats 74k literals, see KB frozen-table pattern).  Phase-1:
   `native_decide`, disclosed.  Kernel `decide` attempt is stretch, not gate.
6. **`AdderMain.lean`** — the frozen statement, exactly (brief §"The theorem to
   prove"; `OccursAt` from `Disjunctive.lean`; sanity anchor: `00` first occurs
   in ln 2 at position 4).

## Traps (beyond the brief's list)

- `famPred`/`Channel.pred` are written let-free so `unfold` + `split` work; keep
  new defs in that style.
- `omega` handles `/2` `%2` (literal divisors) but treats `x / ch.winSize` as an
  atom — feed it bounds as hypotheses first.
- `Nat.mul_le_mul_left` argument order in this pin: `Nat.mul_le_mul_left k h`.
- The `example : famSize mainFamily = 73728 := by decide` in AdderAutomaton
  confirms encodings agree with the emitter — if you touch either, re-check both.
- Commit each green module; `#print axioms` after endgame assembly (target: trust
  triple; `+ Lean.ofReduceBool` acceptable disclosed at the main-certificate
  checkpoint only).

Write `## RESULT` at the top of the BRIEF when done (statement location, axiom
audit, module-3 route, deviations — include the endgame route-correction above).
