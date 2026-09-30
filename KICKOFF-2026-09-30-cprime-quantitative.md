# KICKOFF: quantitative C′ (prepared 2026-09-30, NOT launched)

**Target.**  Prove `CPrimeQuant` and then `CPrimeResidueRich`
(`src/NormalNumbers/CPrimeQuantStatement.lean`).  Both statements are frozen: byte-identical from
the commit that lands this kickoff (standing rule 4).

**Why.**  These would be the first frequency theorems for prime-Lambert constants of natural prime
sets.  Primes `≡ a (mod q)` give orbit discrepancy `O(log³φ(q)/φ(q))`.  Paper derivation:
`docs/CPRIME-QUANTITATIVE-2026-09-30.md`.  It was refereed once, with no false step and gaps in constants and infrastructure only; they are listed in the doc's "Referee findings and build gaps" section.  Those gaps come first; a lap that finds one
of them false records it in `Maze.lean` and stops.

**Route.**
1. **Fixed-`u` schedule.**  Rerun `PrimeModelFamilyGraded`'s schedule with a constant `u` in place
   of `uG`.  The Lean constants need `u ≥ 3000` as written, or about `u ≥ 176` after retuning
   `termE4c`.  Reuse `window_bound_schedule`.  The doc lists six build gaps; clear them in order.
2. **Limsup bounds.**  Re-prove `termE4*`/`termE5`/tail as limsup statements under
   `SqrtFreshMassLe P ρ`.
3. **Transfer.**  Bound `termE1` using the sharper `a_j ≤ min(2, 2π|h|4⁻ʲ)` together with the root
   chain (11.3).
4. **Discrepancy.**  Add a single-interval Erdős–Turán (a Fejér sandwich), which is not in the
   build; the result is `CPrimeQuant`.
5. **Corollary.**  Get Mertens in progressions for the window mass (check `G4MertensAP` and the
   PNT-in-AP modules first).  Add `DivergentRecip` from mathlib's
   `not_summable_residueClass_prime_div`, and the orbit-to-digit window translation (Wall).  The
   result is `CPrimeResidueRich`.

**Done when.**
- Both are proved.
- The axiom set is the trust base.
- They are in the root import.
- There are STATUS and OVERVIEW rows.

**Engine.**  Opus/low treadmill, with a review lap every 5.  Launch only on Trevor's word.
