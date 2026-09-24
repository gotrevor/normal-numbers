# HANDOFF 2026-09-24 (lap 4) — swing at C3, branch `wip/swing-c3`

**Checkpoint.**  HEAD `37f418c`, working tree CLEAN, nothing to push (host pushes).
`lake build` green, 9188 jobs.  `src/` holds **1** swing `sorry` (`tailLargeDecouple_holds`,
`SwingC3Rotation.lean` l. ~272) plus the 2 designated-open off-campaign ones
(`PrimeLambertOscillation`, `MahlerDriftOne`) — do not touch those.

Obey `DIRECTION.md` → CURRENT DIRECTIVE (swing-c3), then `KICKOFF-2026-09-24-swing-c3.md`.
Previous: `HANDOFF-2026-09-24-swing-c3-lap3.md`.

## Headline of this lap: the swing's MAIN TARGET is landed

The kickoff names as the swing's main target "a conditional theorem `conjC3_of_H` with `H` a
precise, literature-checkable arithmetic statement".  **That is now proved and axiom-clean.**

```
NormalNumbers.CastingOut.conjC3_of_addCharTail
  : (∀ b, 3 ≤ b → AddCharTail b) → ConjC3          -- [propext, Classical.choice, Quot.sound]

AddCharTail b : ∀ P Q j h, 0 < j → j < Q →
    (1/N) ∑_{n<N} e(jn/Q) · e(h · tailLarge P b n) → 0
```
(and the intermediate `conjC3_of_weylHypothesis`, also axiom-clean).

Everything on the route is machine-checked except `AddCharTail` itself.

## What landed, file by file (all new, all sorry-free)

| file | content |
|---|---|
| `SwingC3Cover.lean` | **Leaf A PROVED.**  `exists_rotationCover` is discharged.  Base-`b` digits (`sum_digits_eq/_reflect/_real`), growth `b·L+2 < len·b^L`, `exists_steered_class` (CRT steering with primes `≤ L+1` pinned by `a ≡ 0 [MOD R]`), assembly `exists_rotationCover_core`. |
| `SwingC3B5.lean` | **B5 REFUTED.**  `not_orbitDecouple_periodicWitness`: for `x = 1/(b^Q−1)` the orbit is `Q`-periodic (`orbit_periodicWitness : orbit b x n = x·b^{n mod Q}`), so `OrbitDecouple b Q x` is FALSE.  Dynamics give only `λ_r = T_*^r λ_0` (i.e. `T^Q`-invariance), never `T`-invariance. |
| `SwingC3Weyl.lean` | **Signed-weight Weyl criterion.**  `wMean`/`wFourierMean`/`wgood_span`/`wgood_all`/`wgood_real`; `classWeight r Q n = 1_{n≡r(Q)} − 1/Q` with `|·| ≤ 1`. |
| `SwingC3ContGlue.lean` | **The continuous-test-function glue + the conditional.**  `TailLargeDecoupleC`, `tailLargeDecoupleC_of_weyl`, `density_lower_of_decoupleR`, `isRich_of_rotationRouteC`, `WeylTailHypothesis`, `isRich_of_weylHypothesis`, `conjC3_of_weylHypothesis`. |
| `SwingC3AddChar.lean` | **`H` in additive-character form.**  `ee`, `sum_ee_div` (orthogonality mod `Q`), `classWeight_eq_addChar_sum`, `weylTailHypothesis_of_addChar`, `conjC3_of_addCharTail`. |
| `SwingC3Free.lean` | **The free/content boundary.**  `addCharTail_h_eq_zero` (the `h=0` case is a geometric sum, PROVED); `card_modEq_sub_div_le`, `card_modEq_crt_sub_div_le`, `coprime_prod_primes_gt`, `card_modEq_class_pattern_sub_div_le`. |
| `probes/swingc3_b4_class_dependence.py`, `probes/swingc3_b4_fourier.py` | **B4 probe.**  Data in `probes/data-2026-09-24-swingc3-b4-class-dependence.txt`. |

## The two ideas that made the lap work

**1. Move the GLUE, not the leaf.**  The *arc* form of Leaf B (`TailLargeDecouple`) cannot be
reached from a Fourier hypothesis: for a SIGNED weight the trapezoid squeeze costs
`(1/N)∑(trapUp − trapLo)(u_k)`, and controlling that is equidistribution of the `L_P` orbit —
i.e. normality, i.e. circular.  But `density_lower_of_decouple` only ever uses a LOWER bound on
the class counts, so the arc indicator may be replaced by a continuous bump `0 ≤ g ≤ 1`
supported in the arc; Leaf A supplies a net at ANY scale, so the covering runs on the middle
quarter where `g ≡ 1`.  No squeeze, no equidistribution, no limit law to identify.

**2. The signed criterion is easier than the unsigned one.**  `wgood_all` targets the limit `0`,
so nothing has to be *identified* — which is exactly the wall the Selberg–Delange pricing note
kept hitting.  The price is that `h = 0` is no longer excluded; for the class weight that case
is elementary.

## B4 probe: the route is CONFIRMED and PRICED (does not refute)

`b=4, P=3, Q=6` and `b=3, P=2, Q=2`, both with hand-computed known-answer checks
(`tailLarge 3 4 0` head `= 17/16384`).

* The class defect is REAL at finite `N` and decays far slower than the `N^{−1/2}` noise floor
  (worst/floor **grows** `3.4 → 7.9 → 13.3` over `N = 10^5 → 10^6 → 4·10^6`).  So any proof must
  be a `log`-power argument; sqrt-cancellation / sieve heuristics are ruled out.
* It DOES decay: `max_r |avg_{n≡r} e(h y_n) − avg_n e(h y_n)| ~ (log N)^{−a}`, `a ≈ 1.86`
  (`b=4,h=1`), `2.70` (`b=4,h=3`), `2.82` (`b=3,h=1`).
* **Decisive:** the GLOBAL mean `|avg_n e(h y_n)|` decays like `(log N)^{−0.84}`, i.e.
  `(log N)^{Re z − 1}` with `z = e(h/b)`, `Re e(1/4) = 0` — exactly Selberg–Delange.  The class
  defect carries `a ≈ a₀ + 1`: **the non-principal characters mod `Q` beat the principal one by
  precisely ONE power of `log`**, which the 2026-09-24 pricing note predicted and is now
  measured rather than conjectured.

## What the crux IS now

**`AddCharTail b`** — for `h ≠ 0` (the `h = 0` slice is proved) and `0 < j < Q`,
`(1/N)∑_{n<N} e(jn/Q)·e(h·tailLarge P b n) → 0`.

Also still in `src/`: the ratified `tailLargeDecouple_holds` (arc form), which `conjC3` in
`SwingC3.lean` routes through.  **It stays a `sorry` per the kickoff addendum** — and note this
lap's finding that the arc form is the *wrong* leaf (unreachable from Fourier); the live route
is the C-form.

### Next attacks
1. **Truncation with `N`-dependent depth.**  `e(h·tailLarge)` is not a function of boundedly
   many slots for fixed `J` (`E[ω] ≍ loglog N`), but `J = J(N) → ∞` slowly works:
   `b^{−J}·loglog N → 0`.  Formalising `AddCharTail ⟸ (truncated version + an L¹ tail bound)`
   needs `(1/N)∑_{n<N} ω(n) ≪ loglog N` — check whether this repo's Mertens/summatory modules
   (`HANDOFF-2026-09-16-mertensAP.md`, `-summatory-node`) already have it.
2. **The closed form** `tailLarge P b n = ∑_{p>P} b^{−(p − n mod p)}/(1−b^{−p})`: exhibits
   `tailLarge` as a sum of periodic functions with periods coprime to `Q`.  Flagged as worth
   formalising since lap 2; needs a nonneg double-`tsum` interchange.
3. **Smooth/rough split** toward the SD form: `n = s·t`, `t` coprime to `Q`, expand `e(jst/Q)` in
   Dirichlet characters mod `Q`.  Mathlib has `Nat.smoothNumbers`.  Mathlib has NO
   Selberg–Delange, so any route that identifies nothing is worth far more.

### Refuted, do not re-try
B5 (dynamics-only invariance — refuted IN `src/` this lap); effective disjunctivity; exact
prescription of `ω` on a window; `ω mod b` alone; sharpening the §5 schedule; truncate-and-CRT
at fixed depth (obstruction independently re-derived this lap: level `∏_{P<p≤K}p ≈ e^K` forces
`K ≲ log N`, where the discarded tail still weighs `≍ log(log N/log K) → ∞`).

## Pointers
`DIRECTION.md` (CURRENT DIRECTIVE — obey, do not edit) · `PENDING_WORK.md` (attack list, B4/B5/B6
verdicts, the "MAIN TARGET IS LANDED" block) · `KICKOFF-2026-09-24-swing-c3.md` ·
`src/NormalNumbers/Maze.lean`.
