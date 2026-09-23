# HANDOFF — pointer only

This file is a **thin pointer**, never a second durable overview.

* **Durable overview + axiom ledger** → `STATUS.md`
* **Binding orders (altitude-lap owned, OUTRANKS every handoff)** → `DIRECTION.md` → CURRENT DIRECTIVE
* **Latest strategic synthesis** → `REFLECTION-2026-09-16-campaignB.md`
* **Newest dated baton** → `HANDOFF-2026-09-23-theoremC-audit-surface.md`
* **Open items / attack path** → `PENDING_WORK.md` (top section)
* **Frozen plan + estimates** → `ROADMAP.md`

Discover the newest dated baton by glob rather than trusting this line:
`ls HANDOFF-*.md | sort | tail -1`.

---

## ⛔ STUCK-BAIL IN FLIGHT — strike 1 of 2, filed 2026-09-23 (HEAD `b78b343`)

**Read this before doing anything else.**  Full rationale + the fast verification recipe:
`HANDOFF-2026-09-23-theoremC-audit-surface.md`, section "STUCK-BAIL (strike 1 of 2)".

**WHAT is blocked.**  Nothing mathematical is failing.  `lake build` is 🟢 9162 jobs and `src/`
holds exactly two `sorry`s:
`PrimeLambertOscillation.phaseOscillation` and `MahlerDriftOne.exists_prime_nonresidue`.

**WHY it is outside a lap's power.**  `DIRECTION.md` → CURRENT DIRECTIVE → *Forbidden drift*
names those two verbatim as "the two pre-existing off-campaign `sorry`s — **designated open**",
and forbids opening new campaigns.  The directive's own objective — Theorem C′
(`isNormal_subsetLambert_of_sqrtFreshMassZero`) sorry-free and trust-triple — is **MET**
(`3523f8d`), as is its audit surface (`dd540a4`, `#print axioms` clean), and the attended
2026-09-22 17:12 EDT multicutoff override says in terms "When lap 7 is green, write the HANDOFF
and STOP".  So no move this run is *permitted* to make can clear the repo-wide sorry gate.
Astra §10 (the abstract consumer) is not a leaf — `uG/aG/yG/JG/LG` are all defined through
`epsG`, so it is a multi-lap re-parametrisation, i.e. exactly the "new campaign" the directive bars.

**WHAT IS NEEDED FROM THE OPERATOR** — any one of:
1. authorise **Astra §10** (`F_N = ∑_{j≤J} 4^{−j} S_P(y_j, 2N) → 0`, `u_N` chosen freely) as a
   new campaign, with an updated CURRENT DIRECTIVE;
2. un-designate `phaseOscillation` and/or `exists_prime_nonresidue`;
3. relaunch bounded — `--done-when 'sorry-free:src/NormalNumbers/PrimeModelFamilyGraded.lean'`
   (already satisfied) — so the host stops on the campaign target, not the repo-wide count.

**For the confirming lap:** if you find authorised workable ground, work it and this claim
expires.  If you agree, file your own `box stuck` and the run halts for the operator.
