# DIRECTION — normal-numbers 🧭

Altitude laps (review/reflection) are the ONLY writers of the CURRENT DIRECTIVE
section. Grind laps READ and OBEY it; it OUTRANKS the HANDOFF. Keep it short —
detail lives in PENDING_WORK.md.

## CURRENT DIRECTIVE (set 2026-08-24, review lap)

- **THE objective**: advance the B5′ expedition (Track B) toward its headline —
  one explicit real that is absolutely normal + CF-normal + Khinchin-typical.
  W1–W4 are DONE; the frontier is now **W5: the main refinement lemma
  (B–Y Lemma 13)**. ALL of Lemma 13's inputs are proved (Lemmas 5-substitute,
  6-substitute = γ-Chebyshev brick, 7/8/9, Prop 12, d-ary bad zones, CF word
  bridge, digit semantics). Both deep ingredients are already discharged into
  elementary machinery. **The remaining crux is the ASSEMBLY, not more inputs.**
- **Mandated next move**: STOP gathering inputs; ATTACK the Lemma 13 assembly in
  `TBrick*.lean` (new file(s), lap-authored). In order:
  (1) t-brick structure + ε-refinement predicate (Defs 10–11): CF word `w` +
      per-base `d ≤ t` containment `cfCylinder w ⊆ daryCell d m_d j_d r_d`
      (r_d ∈ {1,2}), relative-length field ≥ `1/(2d)` (per-J m_d route, see
      PENDING_WORK KEY ROUTE DECISION — NOT B–Y's uniform 16e^{4c});
  (2) **the decisive core — the SELECTION/measure-balance lemma**: inside `I_w`,
      good-length mass (≥ ½|I_w| via `half_mass_long_extensions`) MINUS the CF
      discrepancy bad zone (`chebyshev_blockCount_brick` → `CFDiscLt` via
      `CFWordBridge`, O(1/n)|I_w|) MINUS Σ_{d≤t} wide d-ary bad zones
      (`volume_iUnion_daryBadZoneWide_le`, exp-small) is `> 0` for n ≥ n₀(t,ε).
      Convert Leb↔γ with `gaussMeasure_le_volume`/`volume_le_gaussMeasure`
      (factor-2 density window). **This inequality is the route-decisive test.**
  (3) Lemma 13 proper: a good J in the surviving set is an ε-refinement; the
      t→t+1 case via Prop 12 (new base ratio `1/(2(t+1))`).
  Decompose freely into named sub-`sorry`s in src/ — raising the src sorry count
  by decomposing the crux IS progress, not regression.
- **Forbidden drift**: do NOT prove yet-more Lemma-13 *inputs* as a substitute
  for attempting the assembly (input-gathering is now fixation — the balance
  inequality decides the whole route). Do NOT open Track A side-quests (COMPLETE,
  axiom-clean). Do NOT pivot to ergodicity/Birkhoff (B5′ is Birkhoff-free). Do
  NOT weaken/reshape any JUDGE-frozen statement. Constants: distortion `2`,
  γ-mixing `(9/10)`, brick ratio `1/(2d)`.
- **Why**: W1–W4 turned both of B–Y's deep imports into proved elementary facts,
  so Lemma 13 is now "long but elementary GIVEN the inputs" — and every input is
  in the repo. The one thing still genuinely UNCERTAIN is whether the measure
  balance closes with the repo's non-uniform-length Lemma-5 substitute (the
  per-J m_d route is the proposed fix, unverified). Settling that inequality
  de-risks all of W5/W6; everything downstream (schedule, limit x, correctness,
  Khinchin graft) is bookkeeping on top of it.

### Directive history
- 2026-08-23 (review lap): Track A certified complete + axiom-clean; kept Track
  B / B5′ direction; sharpened next move to the W4 block-frequency Chebyshev
  assembly (`CFBlockFreq.lean`). No route trigger fired.
- 2026-08-24 (review lap): W4 + ALL Lemma-13 inputs certified proved & axiom-
  clean (8 headlines trust-triple only, 8735 jobs green). Diagnosed input-
  gathering fixation: crux (Lemma 13 assembly) untouched for ~10 laps. Redirected
  from "prove inputs" to "ATTACK the measure-balance selection lemma" — the
  route-decisive test. No route trigger fired (both deep imports discharged).

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
