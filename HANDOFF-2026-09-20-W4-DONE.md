# HANDOFF 2026-09-20 — W4 DONE (`DyadicToPrefix.lean` sorry-free)

Branch `wip/g5-prime-subset`, commit `179e24b`. Scope was `sorry-free:src/NormalNumbers/DyadicToPrefix.lean`; met.

## What landed
`NormalNumbers.prefixMean_tendsto_zero_of_dyadic` is a theorem.
`#print axioms` → `[propext, Classical.choice, Quot.sound]`.

**The advance (route change vs the kickoff).** The kickoff proposed head + `m` dyadic blocks with
per-block endpoint bookkeeping. What actually collapses the proof is the *halving chain*
`n_i = n / 2^i` and two lemmas, both new and now proved in the file:

* `halving_step`: for `N = n/2` with `N ≥ N₀`, `∑_{k<n} − ∑_{k<N} = ∑_{Ico N n}`, and since
  `n ∈ {2N, 2N+1}` (one `omega`), that is the dyadic block `Ico N (2N)` plus at most one term.
  Bound: `ε' N + C`. All rounding lives here, in one `rcases`.
* `halving_chain` (induction on `m`, generalized in `n`): peel the FIRST halving, apply the IH at
  `n/2`. The two `ε' (n/2)` pieces add to `≤ ε' n`, so the telescope is `ε' n + C m` — no geometric
  series, no `∑_i` reindexing, which is what the block route would have needed.

Assembly: `‖∑_{k<n}F‖ ≤ ε' n + C m + C·n/2^m`, choose `m` by `exists_pow_lt_of_lt_one`, then `n`.

## Notes for the next lap (leaves 2–7 of `KICKOFF-2026-09-19-closing-lap.md`, `G4WiringCRT.lean`)
Untouched and still open, in order: `orbit_eq_fract_tailB`, `tail_error_le`, `tail_error_uniform`,
`fullWindowMean_tendsto_zero`, `dyadic_fourier_tendsto_zero`, and the two in
`isNormal_G4_of_CRTConstant`. W4 is now available to that file as a finished input, so leaf 6→7 is
the only remaining wiring step once the L1 tail leaves land.

Gotchas paid for here (worth the corpus): `Nat.pos_pow_of_pos` is gone (use `pow_pos`);
`NormedAddCommGroup.tendsto_nhds_zero` is deprecated → `NormedAddGroup.tendsto_nhds_zero`;
`norm_add_le` needs the sum shaped by an explicit `calc _ = ‖(A−B)+B‖ := by rw [hsp]` step, a
`ring`-rewrite of the goal does not present it.
