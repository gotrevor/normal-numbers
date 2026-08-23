# DIRECTION — normal-numbers 🧭

Altitude laps (review/reflection) are the ONLY writers of the CURRENT DIRECTIVE
section. Grind laps READ and OBEY it; it OUTRANKS the HANDOFF. Keep it short —
detail lives in PENDING_WORK.md.

## CURRENT DIRECTIVE (set 2026-08-23, review lap)

- **THE objective**: advance the B5′ expedition (Track B) toward its headline —
  one explicit real that is absolutely normal + CF-normal + Khinchin-typical.
  The current frontier is **W4: block-frequency variance/Chebyshev**, the
  concrete consumer of the proven γ-mixing engine
  (`gaussMeasure_cylinder_mixing`).
- **Mandated next move**: build `CFBlockFreq.lean` (lap-authored W4 groundwork,
  same pattern as `CFGammaMixing.lean`). Prove, in dependency order:
  (1) first moment `∫ S_n dγ = n·γ(A)` via `measurePreserving_gaussMap`;
  (2) pair-correlation invariance `γ(T^{-j}A ∩ T^{-j'}A) = γ(A ∩ T^{-|j-j'|}A)`;
  (3) second-moment expansion `∫ S_n² dγ = Σ_{j,j'} γ(T^{-j}A ∩ T^{-j'}A)`;
  (4) covariance-sum bound → `Var(S_n) ≤ K(v)·n·γ(I_v)` from γ-mixing;
  (5) Chebyshev ⇒ `γ{|S_n/n − γ(I_v)| ≥ δ} ≤ K(v)·γ(I_v)/(δ²n)`.
  Decompose freely into named sub-`sorry`s in src/ — that is progress.
- **Forbidden drift**: do NOT open Track A side-quests (it is COMPLETE and
  axiom-clean). Do NOT pivot to ergodicity/Birkhoff (B2/B3) — B5′ is
  deliberately Birkhoff-free. Do NOT weaken/reshape any JUDGE-frozen statement
  in CFCylinder/CFDigitLaw/CFMixing. Constants: distortion factor stays `2`,
  γ-mixing rate stays geometric `(9/10)`.
- **Why**: W3 (the expedition crux — correlation decay) is DONE and gives
  *geometric* covariance decay, so the efficiency-free "Markov + Chebyshev
  instead of CLT + KPW-LD" route is de-risked. W4 is now low-risk assembly on
  the critical path to W5 (construction) and W6 (Khinchin graft). Grinding W4
  turns the mixing engine into the per-stage bad-measure `< ¼` bound the whole
  Becher–Yuhjtman construction rests on.

### Directive history
- 2026-08-23 (review lap): Track A certified complete + axiom-clean; kept Track
  B / B5′ direction; sharpened next move to the W4 block-frequency Chebyshev
  assembly (`CFBlockFreq.lean`). No route trigger fired.

## Standing charter (destination)

Two classical harvests of one machine — Birkhoff-on-[0,1] applied to two
digit-reading dynamical systems:

- **Track A — base-b normality** (✅ COMPLETE, axiom-clean): Wall's theorem
  (`isNormal_iff_equidistributed_orbit`), the ln 2 reduction
  (`isNormal_log_two_of_equidistributed`), Stoneham's constant unconditional
  (`isNormal_two_stoneham23`).
- **Track B — CF metric theory / Khinchin** (🔨 active): the B5′ expedition
  (W1–W6, plan in `KHINCHIN.md`) building the combined
  absolutely-normal + CF-normal + Khinchin-typical witness. W1✅ W2✅ W3✅ +
  W4 γ-mixing engine ✅. Governance: statement freezing is JUDGE-owned
  (`JUDGE.md`); grind laps prove frozen statements and add intermediate lemmas.

Route-level abort/escalate triggers: (a) γ-mixing rate collapses below summable
→ escalate (would break W4/W5); NOT fired (geometric proven). (b) W5/W6 needs a
deep import the charter forbids (CLT/KPW/Birkhoff) → escalate; not yet reached.
