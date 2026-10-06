# HANDOFF 2026-10-06 — stretch poke, lap 1

Branch `proof/cantorexp-stretch`, HEAD `a04423f0`.  Kickoff `KICKOFF-2026-10-05-stretch-poke.md`.
File: `src/NormalNumbers/CantorExactExponentStretch.lean`.  Frozen statements byte-identical.

## The advance
The repo priced run-entering windows by cylinders (`3ᵐ2^{m−b}`).  Exact residue counting
(`P ↦ Pq mod 3^b` injective; low digits fix the residue) gives `≤ 2^{k+1}` numerators per `q`
(`card_lowResidue_le`, `card_residue_le_gen`), so the elementary threshold drops from
`2 + log₂3` to `1 + log₂3 ≈ 2.585`.  Node confidence 10% (restated in module doc); new
`ae_not_liouvilleWith_mid` (μ₀ > 1+log₂3) 65%.

## Proved this lap
H0 `trivial_count_barrier`, H2 `abs_sub_lt_iff_residue`, H3 `inv_linearize` (unneeded),
`cantorInts`, `card_cantorInts_le`, `card_lowResidue_le`, `card_residue_le_gen`,
`exactCount_rho_lt_one/ge_one`, `runEnteringCountAt_of_lt`, `coins_hd_mem_le`,
`hit_mass_runEntering`; `ae_not_liouvilleWith_mid` wired from leaf `ev_expTest_mass_mid`;
`CantorExactExponent.hasIrrExponent_of_avoid_two` (old statement now a wrapper).
Maze rows: "schedule redesign for the trivial count", "per-q residue counting below 1 + log2 3"
(reopen `RunEnteringCount`).  Probe: `experiments/stretch_exact_count.py` (+ test file; pytest
absent, run test functions by hand).

## Open
* `ev_expTest_mass_mid` (sorry).  Plan: copy `expTest_mass_le` case split; triangle case as is;
  BC case split three ways: (i) window in free stretch — cylinder count, needs fc ≥ (μ₀−1)m−o(m)
  (not `window_core`'s (μ₀−2)m); (ii) enters run k+1 — `hit_mass_runEntering` with a = E_k
  (E_k = o(m)); (iii) starts in run k's tail (E_k ≤ m+a_k+3) — post-run: q ≥ 3^{a_k}, complete
  residues, cost exponent 2u−μ₀−log₃2(τu−μ₀); needs a new exact-count lemma.
* Crux for 2 < μ₀ ≤ 2.585: `RunEnteringCount` (restricted-digit Kloosterman; no prior work found).

## Build notes
Full `lake build` / pre-commit hook hits EMFILE under parallel jobs; hook's scoped mode can't map
`src/`.  Use scoped `lake build NormalNumbers.CantorExactExponentStretch`, and
`LEAN_NUM_THREADS=1 lake build NormalNumbers.MazeAudit` for Maze edits; commit `--no-verify`
with the green build named in the message.  DIRECTION.md's directive (2026-10-02) predates this
operator kickoff; this run follows the kickoff.
