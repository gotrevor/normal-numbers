# HANDOFF: Mahler's Theorem M PROVED — new bound (g+3)·gᵏ 🧮

Branch `wip/adder-tower-c9` (continuing).  Full `lake build` green (8845 jobs).
Previous lap this session: C10 by reduction (`HANDOFF-2026-09-01-c10-reduction.md`).

## Landed this lap

**`NormalNumbers.Mahler.mahler_multiplier`** (`src/NormalNumbers/MahlerMultiplier.lean`,
~530 lines, imports only `Disjunctive`): for every irrational `α`, base `g ≥ 2`,
digit block `w` of length `k`, some multiplier `1 ≤ m ≤ (g+3)·gᵏ` has `w`
occurring i.o. in `m·α`.  `#print axioms` = `[propext, Classical.choice, Quot.sound]`
for it and every lemma (`near_rational_of_bad`, `orbit_escapes`, the two `_holds`).

This is the theorem the entire adder/tower wing descends from (Mahler 1973 Theorem M,
`m ≤ g^(2k+1)`; Berend–Boshernitzan 1994 `m ≤ 2g^(k+1)` per our tier-S sources).
The proof is NEW to the repo and elementary:

1. **Sweep lemma** (`sweep_pos`/`sweep_neg`): with `η = qx − p`, `gcd(p,q)=1`,
   `|η| < g⁻ᵏ`, the multiples `m = ℓq + r < Lq` form `q` arithmetic progressions
   of step `η`, one starting within `|η|` of each grid point `j/q` (modular inverse
   `rp ≡ j`); once `(L−1)|η| ≥ 1/q` they hit every cell `[W/gᵏ,(W+1)/gᵏ)`.
2. **Covering lemma** (`near_rational_of_bad`): Dirichlet + sweep ⇒ a bad point
   has `(M − 2gᵏ)·|qx − p| < 1` for some `q ≤ gᵏ`.
3. **Escape lemma** (`orbit_escapes`): if `x_n = {gⁿα}` stays within `1/(q_n D)`
   of rationals with `q_n ≤ Q`, `D ≥ (g+1)Q`, the integer
   `q_{n+1}(g p_n − q_n⌊g x_n⌋) − q_n p_{n+1}` has `|·| < 1`, so it is `0`, so the
   defect satisfies `ε_{n+1} = g·ε_n` EXACTLY and is unbounded — contradiction.
4. `M = (g+3)gᵏ` makes `M − 2gᵏ = (g+1)gᵏ` = the escape threshold.

**Ledger edges** (`src/NormalNumbers/LiteratureMahler.lean`): `mahler_theoremM_holds`
(all `g ≥ 2`, `k ≥ 1`; `(2,1)` via the Adamczewski–Rampersad boundary) and
`berendBoshernitzan_bound_holds_of_three_le` (`g ≥ 3`).  Ledger docstrings + the
literature brief's RESULT table marked WIRED.

## ⚠️ Claim hygiene for the operator

Our bound `(g+3)gᵏ` is strictly below the transcribed B–B bound `2g^(k+1)` for
`g ≥ 4`, equal at `g = 3`, worse at `g = 2`.  The B–B statement is tier-S (secondary
sources; PDF not held) — verify against Acta Arith. 66 before calling this an
improvement.  Their lower bound `gᵏ − 1` is untouched.

## Next attack

- **Close `g = 2`** (need `m ≤ 4·2ᵏ`): the slack is `q(L−1) > M − 2q` in the covering
  lemma (one `q` lost to `⌊M/q⌋`, one to `L−1`).  Options: use the `ℓ = L` point when
  `r ≤ M mod q`; a sharper start-point choice; or a base-2-specific escape bound.
  Pushing to `(g+2)gᵏ` in general would match B–B at `g = 2` and beat it for `g ≥ 3`.
- Other ledger nodes still cited-only: `furstenberg_dense_orbit` (Boshernitzan's
  elementary proof is a candidate), `philipp_psi_mixing` (constant-free `ρ < 0.8`
  form — real work), the two Vandehey open problems (open), Waldschmidt 1.1 (open).
