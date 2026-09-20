# KICKOFF 2026-09-19 — sparse-subset lap: elementary leaves of `G4WiringSparse` (PREPARED, not fired)

Branch `wip/g5-prime-subset`.  Engine Opus/low.  Design: `DESIGN-2026-09-19-bcr-wiring.md` §5.
Goal: `src/NormalNumbers/G4WiringSparse.lean` sorry-free **except** `exists_sparse_normal_of_KMT_quant`
(the block construction, a separate lap).  Then `isNormal_subsetLambert_of_KMT_along` is a theorem:
normality of `c_S(4)` from `KMT_along S Jsched` + `TailOK S Jsched`, and `exists_sparse_normal` from
the "∀ sufficiently sparse" hypothesis.  **Do not touch the statements of `KMT_sparse`, `KMT_along`,
`KMT_quant`, `TailOK`.**  Run the closing lap (`KICKOFF-2026-09-19-closing-lap.md`) first if it has
not run: leaves 2, 3, 6, 7 there are the `G₄` versions of leaves 1–4 here and the proofs transfer.

## Leaves, in order (each a named `sorry` already in the file; commit after each)

1. `orbit_eq_fract_tailB_subset`: as `orbit_eq_fract_tailB` with `TWeight.lambert_subset` in place
   of `lambert_omega` (`(subset S).lambert 4 = subsetLambert S 4`) and `TWeight.coe_tailB`.
2. `tail_error_le_subset`: as `tail_error_le`, with `omegaS_le_omegaR` then `omegaR_le_log`
   (`(subset S).wN m = omegaSN S m`, `subset_wN`).
3. `tailOK_windowJ`: average leaf 2 over `n < N`; the bound is monotone in `n`, so
   `(1/N) ∑_{n<N} |…| ≤ (log₂(N + windowJ N + 2) + windowJ N + 3)/4^{windowJ N}`, then the
   `tail_error_uniform` argument (or reuse it: the numerators differ by a constant shift).
4. `prefix_fourier_tendsto_zero`: `ePhase(h · orbit) = ePhase(h · tailB)` (leaf 1 + fract drops
   integers), `‖ePhase a − ePhase b‖ ≤ 2π|h||a − b|`, so
   `‖prefixMean(ePhase(h·orbit)) − windowMeanS S J h N‖ ≤ 2π|h| · (L¹ tail)`; `hTail` + `hKMT`.
5. Inline sorry in `isNormal_subsetLambert_of_KMT_along`: `fourierMean u h = prefixMean (fun n => ePhase (h * u n))`
   (unfold; the summands are syntactically equal).
6. `exists_relDensityZero_divergent`: any explicit `S`.  Suggested: `S p :↔ p.Prime ∧ ∃ k, p ∈ Icc (2^(2^k)) (2^(2^k) · k)`?
   Check the two conditions before committing to a witness; simplest is `S p :↔ p.Prime ∧ Nat.log 2 (Nat.log 2 p) ∣ … `
   — the lap picks; the requirement is `π_S(x)/π(x) → 0` (use `Nat.primesBelow` counting) and
   `∑ 1/p = ∞` (compare with `G4Mertens.log_log_le_sum_inv_primesBelow` on blocks).  This leaf is
   allowed to be hard; if it costs more than one lap, leave it and report.
7. `tail_error_L1`: `(1/N)∑_{n<N} ∑_{j>J} ω_S(n+j)/4^j`; swap sums; for each `j`,
   `∑_{n<N} ω_S(n+j) = ∑_{p∈S} #{n<N : p ∣ n+j} ≤ ∑_{p ∈ S, p ≤ N+j} (N/p + 1)`; for `j ≤ N` this is
   `≤ N·recipSumLe S (2N) + π(2N)`, for `j > N` use `ω_S ≤ log₂`; the `+ 3` and the `log₂(2N)` term
   absorb the fringe.  Weaken the constant if needed but keep the shape `≪ 4^{-J}(S_S(2N) + o(1))`.

8. Block-construction leaves (`BlockData` namespace), only after 1–7: `recipSumIoc_le`,
   `recipSumLe_ge`, `recipSumLe_le` (Finset bookkeeping over the blocks), `blockIndex_tendsto`,
   `blockIndex_spec` (`Nat.findGreatest_spec`/`Nat.le_findGreatest`), `divergentRecip`
   (comparison of nonneg series), `kmt_along` (apply `hKMT` at `N` in block `i` with `ε = εᵢ`,
   `J = Jᵢ`; squeeze with `Good.terms`), `tailOK` (`tail_error_L1` + `recipSumLe_le` + `Good.tail`),
   `exists_block` (greedy over primes `> y`, divergence from `G4Mertens.log_log_le_sum_inv_primesBelow`).
   `exists_good` (the sandwich) is the hardest and is a lap of its own; leave it if it resists.

## Rules
Report the advance, not the sorry count.  `box done --green` when every leaf but
`exists_sparse_normal_of_KMT_quant` is closed.  Nothing in `G4WiringCRT.lean`'s frozen Props changes.
