# HANDOFF — pi route 3 (disk residues), lap 3 (2026-10-26)

## Node graph
- `diskCount_sub_area` (proved): |diskCount R − πR²| ≤ 5R, R ≥ 1.
- `diskPhase_sub_le` / `diskPhase_shadow` (proved, C = 5).
- `pi_disjunctive_of_diskResidueCover` (proved; standard axioms only).
- `PiOrbitWindowCover` (new node, `DiskResidueCostume.lean`): quantitative window-cover of π's own
  binary orbit with middle-quarter targets.  Pure π-digit statement, ~85% heuristic, no mechanism.
- `diskResidueCover_of_piOrbitWindowCover` (proved): PiOrbitWindowCover → DiskResidueCover.
- `diskSmallPart_orbit` (proved): small-d part of the χ₄ identity, ×4/8^n, is within 4D/8^n of
  2^n·4·L_D (Leibniz partial sum, rational ⇒ periodic orbit).  The π-content lives in the tail d > D.
- `DiskResidueCover` (route premise, open).  `DiskDivisorIdentity` (hypothesis Prop, unused).

## Costume verdict
The disk premise is implied by a pure π-orbit statement; the lattice enters only through a
vanishing shadow error (probe `scripts/pi_route3_residue.py`: scaled error 0.002 at n = 11; square
control phases → 0).  The converse (DiskResidueCover → orbit cover with half-cylinder targets) is
the same argument and is not yet in Lean.  So route 3 has value only if the χ₄ divisor identity
gives a handle the digits lack.

## Next move
1. Prove the converse direction (makes "costume" an equivalence up to margins).
2. (done in Lean: `diskSmallPart_orbit`.)  Remaining: quantify the tail d > D — it equals
   2^n·4(π/4 − L_D) up to floor errors; probe whether any D-choice makes the tail floor errors
   structured (hyperbola-method middle).  Expect: no lever; then write the obstruction as a Maze-style
   node and self-stop per rule 9.
   Old: split diskCount(4^n) mod 8^n by d-range via the χ₄ identity; check whether the small-d part
   is explicit (Σ_{d ≤ D} χ₄(d)⌊16^n/d⌋ mod 8^n) and how much of the residue it carries.
