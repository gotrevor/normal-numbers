# HANDOFF 2026-11-03/04: explicit sparse prime set, base-4-normal Lambert constant — COMPLETE

Branch `wip/explicit-cprime` (worktree `~/src/nn-explicit-cprime`).  Kickoff:
`KICKOFF-2026-11-03-explicit-sparse-normal.md`.

## Result

`NormalNumbers.PrimeModel.Explicit.isNormal_explicitSparseLambert`
(`src/NormalNumbers/ExplicitSparseNormal.lean`): for the decidable set
`P = {p : k(p) ≥ 1, ⌊log₂ p⌋·k(p) < 2^{k(p)}(k(p)+1)}`, `k(p) = ⌊log₂⌊log₂ p⌋⌋`, the constant
`Σ_{p prime, p ∈ P} 1/(4^p − 1)` is normal in base 4.  Both leaves
(`divergentRecip_explicitSparseSet`, `sqrtFreshMassZero_explicitSparseSet`) are proved; the three
frozen statements are byte-identical to the kickoff commit.

    #print axioms isNormal_explicitSparseLambert
    -- [propext, Classical.choice, Quot.sound]

(same for both leaves).  **No `Literature` Prop was planted**: the headline is unconditional.

## The mathematical simplification (vs. the kickoff plan)

The kickoff asked for Mertens' *second* theorem with vanishing error (step 0).  Not needed: the
repo's Mertens *first* theorem with an `O(1)` error (`CastingOut.mertens_lower`: `≥ log N − 9`,
`mertens_upper`: `≤ log N + log 4`) suffices, because each block `k` is a window `(x, y]` with
`log y / log x = T_k/2^k ∈ [1 + 1/k, 1 + 1/k + 2^{-k}]` and log-width `≍ 2^k/k → ∞`.  On such a
window `1/p` is sandwiched between `(log p/p)/log y` and `(log p/p)/log x`, so the `O(1)` error
costs only `O(2^{-k})`.  Declarations (`src/NormalNumbers/ExplicitSparseNormalAux.lean`,
namespace `NormalNumbers.PrimeModel.Explicit.Aux`):

* `mem_block_iff` — exact interval form: for `k ≥ 1`, `p` prime, `p ∈ P ∧ k(p) = k ↔
  2^{2^k} < p ≤ 2^{T_k}`, `T_k = blockTop k = ⌈2^k(k+1)/k⌉` (`mul_lt_iff_lt_blockTop`).
* `mertens_Ioc_le`, `mertens_Ioc_ge`, `recip_Ioc_le_div`, `div_le_recip_Ioc` — window Mertens.
* `blockMass_le : 1 ≤ k → blockMass k ≤ 18/k`; `blockMass_ge : 9 ≤ k → 1/(2(k+1)) ≤ blockMass k`.
* `divergentRecip_of_iff` — disjoint blocks (`blockSet_disjoint`, via the scale `k(p)`) plus
  harmonic divergence and `Summable.sum_le_tsum`.
* `scale_window` — a prime in `(√N, N]` has scale in `{m − 1, m}`, `m = ⌊log₂⌊log₂ N⌋⌋`.
* `recipSumIoc_sqrt_le` — fresh mass `≤ 36/(m − 1)`; `sqrtFreshMassZero_of_iff` — `→ 0`.

## Build

Root `src/NormalNumbers.lean` now imports `ExplicitSparseNormalAux` and `ExplicitSparseNormal`
(file is sorry-free, so the barrier audit passes).  Full `lake build` green (10891 jobs; barrier
audit: 104 open sorries scanned, unchanged elsewhere).

Environment note: the pre-commit full build twice failed spuriously with "Too many open files"
(reference corpus `lean-box-fd-exhaustion-is-mmap-not-nofile.md`); building the failing targets
(`BarrierAudit`, `MazeAudit`) individually and retrying converged.

## Next

Target met.  Possible follow-ups (not started): a `docs/notes/` note for the explicit normal
number; the same block trick with any `δ_k` window fraction gives a family of explicit sets.

## Final checkpoint (2026-11-04)

Branch `wip/explicit-cprime`, proof HEAD `fd8d3296`.  `box done --green` issued; scoped target
`sorry-free:src/NormalNumbers/ExplicitSparseNormal.lean` met (0 sorries in the file and its Aux).
Working tree clean apart from this checkpoint.  Next steps for a future session (optional, off the
scoped target): write `docs/notes/explicit-sparse-normal.md` (neutral note: the set, the theorem
at a pinned commit, the Mertens-I-only argument); host to review and merge `wip/explicit-cprime`.
