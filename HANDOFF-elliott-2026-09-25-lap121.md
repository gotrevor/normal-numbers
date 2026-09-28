# HANDOFF — Elliott campaign, laps 113–121 (2026-09-25)

**Branch** `wip/elliott-port` · **HEAD** `8d2ba51` · **working tree clean, nothing uncommitted.**

**Green convention: TWO builds.**  `lake build` (9257 jobs) AND
`lake build NormalNumbers.ElliottAxiomAudit` (9697 jobs), zero `sorryAx`.
*(Lap 113 briefly introduced a third audit target; lap 114 removed the need for it.  Ignore any
"three builds" note.)*

---

## THE HEADLINE OF THIS SESSION

`NormalNumbers.ElliottLedger.twoPointElliottLog_of_zetaExponent` —
`ElliottTwoPointLog.TwoPointElliottLog b p q t` now follows from **one standard analytic fact**:

> `ZetaLogDerivExponent θ` for some `θ < 1`, i.e. `‖ζ'/ζ(s)‖ ≪ (log(|Im s|+16))^θ`
> on `1 ≤ Re s ≤ 3`, `|Im s| ≥ 1`.

Nothing else.  `PrimeDensityAP`, `CharacterClusterRigidity`, `ShiftedMertensSmall`,
`ArchCorrModerate` and `ArchCorrNearMaxHeight` are **all discharged inside that call**.
That meets — and then improves on — DIRECTION's stated objective, which asked for one *cited*
axiom (`ArchCorrNearMaxHeight`, a bespoke `Prop` about `archCorr`); the remaining hypothesis is now
a literature-standard statement about `ζ` instead.

Guarded by `ledger_nonvacuous` (lap 121): concrete `b=1, p=2, q=3, t=1/2` satisfies every side
condition, so the chain is not vacuously conditional.

---

## WHAT EACH LAP DID

* **113** `ElliottZetaModerate.exists_moderate_logDeriv_bound` — the moderate-band `ζ'/ζ` bound,
  from the in-repo `PNTPort.LogDerivZetaBndUnif99` + a compactness patch on `1 ≤ |Im s| ≤ 3`.
* **114 🔑 THE STRUCTURAL UNBLOCK.**  Two root-level namespace collisions made
  `PNTPort.ZetaBounds` unimportable alongside the Elliott chain — the real reason the campaign
  spent ~16 laps citing a dVP bound it already owned.  `CS.deriv` (`PNTPort.Sobolev` vs
  `PrimeNumberTheoremAnd.Sobolev`, reached via `ErdosProblems`): fixed by dropping
  `import PNTPort.Fourier` from `ZetaBounds`, which needed only `deriv ofReal = fun _ => 1` from
  it.  `B1` (`PNTPort.EulerMaclaurin` vs `Erdos49.PNT.EulerMaclaurin`): fixed by wrapping the
  79-line file in `namespace PNTPort`.  **Without this the route could not have completed.**
* **115** `exists_sliceCapModerate9` — the moderate cap clause, by a two-branch split on
  `(sliceT9)⁻¹ = min ((log(|v|+16))^9) (log X)`: dVP branch, or the *trivial* bound alone.
* **116** `exists_dampedSeriesBoundModerate9`.  Key lemma
  `integral_le_const_add_log_add_const`: the cap band tolerates a **multiplicative** constant for
  an **additive** price (band has length `T`, so `∫₀^T C·T⁻¹ = C`), leaving the `log(1/T)` main
  term with lap 106's sharp coefficient `1`.
* **117** `exists_archCorrModerate9` — (c′-II-a) discharged; ledger down to two.
* **118** `exists_primeDensityAP` (T3) — ledger down to one.  Route: four spelling bridges +
  `G4MertensAP.mertensRate_residueClass` + a reusable `Finset.induction` uniformiser applied twice.
* **119** `archCorrNearMaxHeight_antitone` — paid off an EA-1 debt lap 117 incurred: the widened
  band's hypothesis is *strictly stronger*, so it cannot later be bluffed from the narrow one.
* **120 🔑** The chain made **parametric in `θ`** (`ElliottZetaTheta.lean`).  The `9` entered in
  exactly one place (`log(1/T) = θ·log log`); everything else was exponent-blind.
  `archCorrNearMaxHeight_of_exponent` then *replaces the bespoke wall axiom outright* — and shows
  **the lower cut is irrelevant**: the saving comes entirely from `|v| ≤ A²X`.
* **121** Non-vacuity anchor + `zetaLogDerivExponent_gap`.

---

## THE REMAINING DEBT, EXACTLY

* **owned**: `θ ∈ [9, ∞)` (`zetaLogDerivExponent_of_nine_le`, from `PNTPort.ZetaZeroFree9`).
* **needed**: `θ ∈ [0, 1)`.
* monotone in between (`zetaLogDerivExponent_mono`), so nothing is free.

**Why `9`** (read off `src/PNTPort/ZetaBounds.lean`, don't re-derive):
`LogDerivZetaBnd = ZetaInvBnd × ZetaDerivUpperBnd`, i.e. **`9 = 7 + 2`** (`1/‖ζ‖` costs 7, `‖ζ'‖`
costs 2).  Meanwhile **`ZetaUpperBnd` gives `‖ζ(σ+it)‖ ≤ C·log|t|`, exponent exactly `1`** on the
wider region `σ ≥ 1 − A/log|t|`.  So the classical material sits *at* the threshold on the `ζ` side
and *above* it on the `ζ'/ζ` side — that is the wall, pinned to named lemmas.

---

## NEXT LAP — in priority order

1. **(a) The literature question, unsettled and the best target.**  The chain needs only `θ < 1`,
   which is **weaker than Vinogradov's `2/3`**: any sub-linear bound suffices.  Is
   `‖ζ'/ζ(1+it)‖ ≪ (log t)^{1−ε}` reachable by any route cheaper than Vinogradov's mean value
   theorem?  `WebSearch` works; `WebFetch` always times out (use `ON-LINE-REQUEST.md`).
   If the answer is no, record "Vinogradov or nothing" — don't soften it.
2. **(b) Numeric narrowing `9 → 7`**, by routing the near-max band through `log ζ`
   (`ZetaUpperBnd`, exponent 1) + `ZetaInvBnd` (exponent 7) instead of `ζ'/ζ`.  This does **not**
   reach `< 1`; do it only to keep the record sharp.  Prefer (a).
3. Do **not** file the gap as infeasible.  DIRECTION forbids attacking `ArchCorrNearMaxHeight`
   head-on and says it is never an excuse to stop.

## REFUTED THIS SESSION (record, do not retry)

* **Averaging over `v` instead of a pointwise bound.**  `ArchCorrLargeShift` is consumed
  *pointwise* — `twistAlmostRealPropDichotomy_of_inputs` applies it at the single shift `t` of the
  character the dichotomy produces, not under any integral.  So mean-value theorems for
  `|ζ(1+it)|` (fourth moment, Carlson) **cannot** be substituted for Vinogradov. ⛔

## MUST KEEP SAYING (DIRECTION requires it every lap)

* The remaining axiom is a **real wall**, not an artefact of the decomposition.
* `TwoPointElliottLog` is the **logarithmic** average.  `CastingOut.TwoPointElliott` — what the
  repo's normality route consumes — is the **natural** average, and the passage is a separate,
  known-open, Chowla-strength problem.  **This does not close the normality route**, and nothing in
  `src/` currently consumes `TwoPointElliottLog`.

## NOTE ON THE OPERATOR INSTRUCTION FOR THIS RUN

The run was scoped to "close `exists_caseA_thin_threshold` / `exists_caseB_threshold` in
`ElliottLeafTwo.lean`".  Both were **already proved** (lap 83) — re-verified in-kernel at the start
of this session: they and `ElliottGeneral.nonasymptoticLogElliott` all print
`[propext, Classical.choice, Quot.sound]`, and the audit build emits zero `sorryAx`.  The
instruction referenced lap 63.  The session therefore followed DIRECTION's CURRENT DIRECTIVE
(T1/T2/T3), which outranks a stale pointer.
