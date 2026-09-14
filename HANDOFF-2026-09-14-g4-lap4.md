# HANDOFF 2026-09-14 — G4 disjunctivity, lap 4 (C3core eliminated: C3 is CRT counting only)

Branch `wip/g4-disjunctivity`.  Working tree clean apart from the host's untracked
`CHECK-g4-route-deviations.md` (not swept in, per lap 3).  Not pushed.  `DIRECTION.md` unchanged
(grind lap); `PENDING_WORK.md` §"GRIND 2026-09-14 (G4 lap 4)" carries the mathematics.

Build: `lake build NormalNumbers.G4TransferMoment` green (8713 jobs); every declaration below
prints `[propext, Classical.choice, Quot.sound]`.  No `sorry` in any G4 file.

## Advance on the crux (C3)

Lap 3 left C3 as two inputs: **C3a** (`ε`, CRT counting) and **C3core** (`B`, a Shiu-type
exponential moment of the active-prime count over the sample — a project-scale sieve theorem).
This lap shows **C3core is unnecessary**.  Expanding `∏_p g_p` around `1` instead of around the
independent means makes the `|T| > M` remainder supported on `{V(n) > M}` and bounded there by
`2(2eV(n)/M)^M`, a degree-`M` polynomial in the active count.  Its sample average transfers by CRT
(`M`-tuples of primes, modulus `≤ R^M`) to the independent model, where the needed exponential
moment is the exact product `∏_p(1 + e^λ π_p)`.

`src/NormalNumbers/G4TransferMoment.lean`:
* `norm_truncation_le` (pointwise polynomial truncation bound),
* `sampleAvg_card_pow_le` (moment transfer via CRT inputs on `D ⊆ s`, `|D| ≤ M`),
* `sum_card_pow_mul_prod_le` (independent-model moment `≤ (M/λ)^M ∏(1+e^λπ)`),
* **`norm_sampleAvg_prod_sub_prod_le'`** — the assembled skeleton whose only inputs are the two
  CRT averages `hsmall`, `hcrt`.  Paper budget in `PENDING_WORK.md`: the non-CRT error terms are
  `exp(−Θ(M))` with `M ≍ C·kL`, `C ≥ 10^4`, far below the main term `exp(−cL8^{−K})`.

The lap-3 skeleton (`G4Transfer.norm_sampleAvg_prod_sub_prod_le`) stays proved but is superseded.

## Open, in priority order

1. **`CRTInput`** — the single remaining C3 lemma: for pairwise-coprime `p ∈ T`, `h_p` periodic
   mod `p`, `‖h_p‖ ≤ 1`, sample `{n ≤ X : n ≡ a mod P₀}`, the sample average of `∏_T h_p` is within
   `2QP₀/X` of `∏_T(mean of h_p)`.  Elementary; `ZMod.chineseRemainder`.  Both `hsmall` and `hcrt`
   are instances.
2. **Instantiate `PropC`**: `g_p(n) = e(θ_p(n))`, `Act n` = good primes with `n` in an active
   class, `π_p = k/p`, `c_p = 2π_p`, contraction `‖μ_p‖ ≤ 1 − c'8^{−K}/p` from
   `G4LocalContraction`, and the harmonic sum over good primes.  Then **C4** (`Λδ₃ < 1`).
3. B assembly to `PropB` (labour), then A, D, and the §5 schedule module.

Nothing refuted this lap.  Route trigger G-T1 (C3 as a decomposed `Prop` stack within 5 laps) is
satisfied ahead of schedule: C3 is now one named elementary lemma.
