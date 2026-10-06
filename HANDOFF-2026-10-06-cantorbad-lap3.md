# HANDOFF 2026-10-06 cantorbad lap 3 (branch proof/cantor-bad-normal)

Target unchanged; one sorry: crux `fourierPairRate_descent`.

## Advance (route-decisive)
- `descent_eq_descentR`, `repC_ok` (proved): descentLaw = descentR repC, where repC is the
  `Classical.choose` replacement. A crux proof can use only `RepOK repC`, so in effect it must hold for every admissible rule.
- `AdversarialReplacement` (conjecture node, 50%): some admissible rule breaks 2-normality via steering on dead stages.
  If true, the frozen crux is unprovable from choose_spec. In that case the operator must sanction a canonical-replacement law
  (uniform resampling among alive blocks) for the headline.
- Numerics: `scripts/cantorbad_eta.py`. Dead-stage rate is ~1/3000 at stages 2–6. Deeper runs (10 stages, seeds 3–6) were started
  in /tmp scratch; rerun if lost.

## Next
1. Decide constant-η vs decay (deeper numerics; He–Liao 2602.01307 as a Literature Prop).
2. If η decays summably-fast, the obstruction dies. The adversary then has only finitely many steers, and the crux might
   be attacked via coupling to the pure Cantor coin point (the descent differs from `cpt ω` on finitely many blocks a.s.).
   Normality is invariant under finitely many digit changes? NO: changing ternary digits changes x by a ternary rational,
   which is a rational shift. Base-b normality IS invariant under rational shifts, and cpt ω is μ_K-a.e. normal (Cassels).
   So **if a.s. only finitely many stages are dead, the headline follows from Cassels plus a rational-shift invariance**,
   bypassing Fourier entirely. This is the most promising lead. Check Borel–Cantelli: Σ_s P(dead at s) < ∞?
