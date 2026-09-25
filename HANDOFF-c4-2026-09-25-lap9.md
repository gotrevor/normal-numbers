# HANDOFF C4 — 2026-09-25, end of session (laps 1–9)

Branch `wip/c4-infinite`, worktree `~/src/nn-c4`.  HEAD `a39dfc3`.  Working tree CLEAN.
`lake build` green (9260 jobs).  Objective: `KICKOFF-2026-09-24-c4.md` (necessity → finite `S` →
infinite `S`).

## Directive conflict — read before the next lap
Root `DIRECTION.md`'s CURRENT DIRECTIVE is dated 2026-09-23 and targets
`PrimeModelFamilyGraded.lean` (Theorem C′) in a different campaign.  `KICKOFF-2026-09-24-c4.md` is
newer, was ratified on this branch (`cafe6e1`), and is the operator's named objective for this
run, so every lap here worked C4.  `DIRECTION.md` is owned by altitude laps and was NOT edited; an
altitude lap should refresh it.

## Done (all in the kernel, all `#print axioms` clean)
| Target | Status |
|---|---|
| `abelianAt_one_of_abelianAt` (ratified necessity) | **PROVED** |
| `c4_realizable`, `S = ∅` branch | **PROVED** |
| `c4_realizable_singleton_one` (`S = {1}`) | **PROVED** |
| **`c4_realizable_odd` (`S = {odd L}`, INFINITE)** | **PROVED** |
| `c4_realizable_of_mem_one` (general `S`) | the one open `sorry`, `AbelianWindowSets.lean:506` |

## Files
* `src/NormalNumbers/AbelianWindowSets.lean` — the ratified statements; necessity; the `S = ∅`
  and `S = {1}` witnesses; `isAbelianAt_periodic_iff`; `isAbelianAt_blockSeq_iff`; the one `sorry`.
* `src/NormalNumbers/AbelianWindowBlocks.lean` (new) — `tendsto_blockEventG`, the block-density
  workhorse at ARBITRARY `(base B, residue modulus q)` (ported from the hard-wired base-16/mod-4
  version in `AbelianBlockDensity.lean`); `blockSeq`, `winOnes`, `onesCount_blockSeq`,
  `blockFreq`, `tendsto_onesFreq_blockSeq`.
* `src/NormalNumbers/AbelianWindowOdd.lean` (new) — the infinite witness: `zdig`, `Zgf`,
  `zcount_eq`, `sortedTable`, the four `winOnes_sorted_*` window formulas, `Wgf` and its four
  evaluations, `blockFreq_sorted_odd`, `blockFreq_sorted_even_ne`, `c4_realizable_odd`.
* `probes/c4_periodic_words.py`, `probes/c4_ap_defect_family.py`, `probes/c4_block_iid.py` —
  all stdlib-only, each with a hand-computed known-answer check.

## The two mechanisms, both now demonstrated
1. **Periodic witnesses (finite `S`).**  `isAbelianAt_periodic_iff`: for period-`D` `s`,
   `IsAbelianAt s L` is the exact finite condition `#{r<D : onesCount s L r = j}/D = C(L,j)/2^L`.
   Because there are only `D` windows, `G(v) ⊆ [1, D−1]` — non-membership at every large `L` is
   FREE.  `probes/c4_periodic_words.py`: `D = 16` realizes 7 of the 8 admissible subsets of
   `[1,4]`; `D = 64` supplies the missing `{1,2,4}`.
2. **Block-i.i.d. witnesses (infinite `S`).**  `isAbelianAt_blockSeq_iff`: for
   `blockSeq g c q n = g (n % q) (c (n / q))` with `c` normal base `B`, `IsAbelianAt` at `L` is
   the finite identity `blockFreq g q B S L j = C(L,j)/2^L`, valid whenever `q + L ≤ q·S + 1`.
   Aperiodic, so no ceiling.  `probes/c4_block_iid.py` finds `G` = odds (`q=2`) and three
   infinite eventually-periodic sets at `q=3`.

## Refuted / constrained sub-approaches (do not retry)
* **No stationary ±1 process has pair-only correlations** — the length-`n` Fourier expansion
  `2^{-n}(1 + ∑ρ(b−a)x_a x_b)` goes negative once `n·∑|ρ| > 1`.  So the higher `F_j` must be
  killed as symmetrized SUMS, not term by term.
* **Alternating AP-defects are one-signed**: `F_2^{(m)}(L) < 0` for every `L > m`, so nonnegative
  mixtures of them realize only initial segments `[1,k]`.  Fix: a mean-zero inner pattern with
  positive short autocorrelation (`000111`) restores both signs.
* **Periodic inner sequence + base-`2^K` filler fails**: a periodic sequence abelian at length 1
  must have EVEN period, so CRT independence against a `2^K`-periodic de Bruijn filler is
  unavailable.  The filler must be a genuinely normal sequence — which is what `blockSeq` does.

## Next attack on `c4_realizable_of_mem_one`
Hardest-first, in this order:
1. **Arbitrary finite `S`, by construction not search.**  The de Bruijn word of order `k` realizes
   `[1,k]` (every `k`-word once ⇒ every `L`-word exactly `2^{k−L}` times).  The open question is
   how to DELETE prescribed lengths from it while keeping the rest exact — likely a small integer
   perturbation of the cyclic word, i.e. an integer vector in `∩_{L∈S} ker A_L` outside
   `ker A_L` for `L ∉ S` (`probes/abelian_window_sets.py` has the `A_L` picture).
2. **Arbitrary infinite `S`.**  The `blockSeq` machinery is already parametric in `q, B, S`, so
   the obstacle is only the design of the block law at each block length; lap 6 shows that is a
   finite rational search per `q`.  The remaining STRUCTURAL gap is the multi-scale limit:
   concatenate stage words `w_k^{R_k}` with `R_k` growing fast, where `w_k` is exact at all
   `L ≤ k`, so the boundary error is `O(1/R_k)` and every `L`-frequency converges.  That
   concatenation lemma is not yet formalized and is the right next Lean artifact — it is needed
   by any general construction and is a self-contained analysis statement.
3. Useful coordinates already written down (docstring of the `sorry`): `IsAbelianAt s L ↔ ∀ j,
   F j L = 0` with `F j L = ∑_{T⊆[0,L), |T|=j} c T`; `F 1 L = L·c{0}` (this IS the necessity
   theorem), and `Δ²(F 2) = ρ`, so `F 2` is an arbitrary sequence vanishing at `0` and `1` —
   exactly the shape of the admissibility hypothesis.  That is the mechanism C4 rests on.

## Confidence
C4 is TRUE: **high**.  No obstruction has appeared at any scale probed, every admissible finite
set probed is realized by a periodic word, and an infinite one is now proved in the kernel.
