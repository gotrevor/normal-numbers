# Handoff 2026-09-13: Stoneham boundary campaign — endpoint proved

Scope: BRIEF-stoneham-boundary-2026-09-13.md + dated operator override in DIRECTION.md.

## Result

All six frozen declarations in `src/NormalNumbers/StonehamBoundary.lean` are proved.
`lake build` (whole repo) green.  `#print axioms` on all six:
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no custom axioms.
Frozen statements byte-identical to scaffold commit b007c35 (checked by extracting
every `theorem … := by` header from both versions and diffing).

## What was proved (mathematics, by lemma)

Helper module `src/NormalNumbers/StonehamBoundaryLemmas.lean` (imports only Mathlib):

* `sq_lift_two_adic`: x ≡ 1 + 2^m (mod 2^(m+1)), m ≥ 2 ⟹ x² ≡ 1 + 2^(m+1) (mod 2^(m+2)).
  Pure ring identity after writing 2^m = 4z.
* `three_pow_two_pow_modEq`: 3^(2^r) ≡ 1 + 2^(r+2) (mod 2^(r+3)), r ≥ 1 (induction, base 9 ≡ 9 mod 16).
* `three_pow_two_pow_modEq_one`: the weakening 3^(2^r) ≡ 1 (mod 2^(r+2)).
* `stoneham_f_add_two_pow`: f(k+2^r) ≡ f(k) − 2^r (mod 2^(r+2)), f(k) = 3^k − k in ℤ.
* `stoneham_f_periodic`: f(k + m·2^r) ≡ f(k) (mod 2^r), r ≥ 1.
* `exponent_residue_aux`: ∀ a : ℤ ∃ k < 2^r, f(k) ≡ a (mod 2^r).  Induction on r; r = 0→1 by
  parity; r ≥ 1 lifts via the two candidates k, k + 2^r.
* `three_pow_half_period`: 3^(2^(c−2)) ≡ 1 + 2^c (mod 2^(c+1)), c ≥ 3.
* `three_pow_grid_aux`: c ≥ 3, a ≡ 1 (mod 8) ⟹ ∃ e, 3^e ≡ a (mod 2^c).  Lift from 2^c to
  2^(c+1) with candidates e and e + 2^(c−2), using oddness of 3^e.

Frozen module:

* A `stoneham_exponent_residue_surjective` ← `exponent_residue_aux`.
* B `stoneham_three_pow_grid` ← `three_pow_grid_aux` + `Int.emod_eq_of_lt` cast bridge.
* C `stoneham_boundary_readout_recurrence`: k = k0 + (K+c+3)·2^(c−2) with k0 the residue
  solution of f(k0) ≡ e + c (mod 2^(c−2)).  `jstar (3^k − c) = k − 1` via `Nat.find_eq_iff`
  (needs c < 3^(k−1), k ≤ 3^(k−1)).  Then sC = c, sA = 3^k − c − k, and
  3^x mod 2^c depends only on x mod 2^(c−2) (`hred`), giving readout = 3^e mod 2^c = a.
* `stoneham_orbit_readout_cell`: public inequality of `stoneham_base6_readout` plus a copy
  of its internal `hT_lt` estimate (2·3^(a−1) < 4^(3^(J+1)) and 3^(J+2) − n = 2·3^(J+1) + c).
* D `stoneham_base6_interval_recurrence`: c = M + 3 with M > 16/(v−u) (so 2^c > c > M);
  a = 8⌊u·2^c/8⌋ + 9 satisfies u·2^c < a, a + 1 < v·2^c ≤ 2^c; apply C with K = N + c and the
  one-cell bound.
* `isDisjunctive_six_stoneham23`: supplied proof, now sorry-free transitively.

## What remains

Nothing in the brief's scope.  Claim limit (per brief): this is base-6 disjunctivity of
α_{2,3} via an elementary boundary readout; not normality (false in base 6 by Bailey–Borwein),
not a novelty claim (cf. Hertling 1995 Thm 8), nothing about log 2.

Not committed by this lap (host-owned / not mine): `ROADMAP.md` modification,
`experiments/theta_seed_precision.py`.

## Checkpoint (final, 2026-09-13)

* Branch: master.  HEAD: f1f9749 (`git log --oneline -1`).  Working tree: only host-owned
  `ROADMAP.md` edit and untracked `experiments/theta_seed_precision.py` remain uncommitted.
* Stop signalled twice via `box done` / `box done --green`; host verifies green and halts.
* Exact next steps: none in scope.  Host-side follow-ups only: fold the result into
  STATUS/ROADMAP (host-owned), and optionally decide whether to keep
  `StonehamBoundaryLemmas.lean` importing all of `Mathlib` or trim to the modules used
  (`Mathlib.Data.Int.ModEq`, `Mathlib.Tactic`) — cosmetic, no proof impact.
