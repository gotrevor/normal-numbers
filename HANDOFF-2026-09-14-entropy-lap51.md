# HANDOFF — entropy lap 51 (review + rungs 1 and 3a), 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8981 jobs**.  New modules sorry-free.

## 0. The lap in one line

A fresh-mind review re-pointed the campaign (E-T7 had fired) at **an explicit normal number read
off `G₄`'s digits along the arithmetic sample**, and then proved rung 1 in full plus the
load-bearing counting lemma of rung 3.

## 1. The direction change (altitude work, `DIRECTION.md` CURRENT DIRECTIVE, lap 51)

The lap-37 objective was met at laps 38–47 and its boundary proved at 48; 49–50 opened the
richness line.  Every endpoint of laps 31–50 is a statistic *at scale `i`, with `i → ∞`* — a
sequence of finite statements, never one infinite object.  The repo already owns both pieces that
close that gap (`Bridge.isNormal_realOfDigits`, and the `countOccurrences` calculus of
`CFChainFreq`/`Counting`), and `tendsto_occursCountP_primeLambertFour` is exactly the input a
block-concatenation argument consumes.  So:

> 🎯 an `x`-independent `samplePos : ℕ → ℕ`, built from the schedule alone, with
> `IsNormalSequence 2 (fun j => digitOf 2 (Int.fract G₄) (samplePos j))`.

**Not a claim about `G₄`'s own normality**, which stays closed on this mechanism (lap 37).

## 2. What was proved

### `G4EntropyOcc.lean` (rung 1) — the window-counting layer

* `winCount s v n = #{p < n : v matches s at p}`, `winCount_split`.
* `isNormalSequence_of_tendsto_winCount` — window frequency `b^{−|v|}` for every nonempty
  base-`b` word ⟹ `IsNormalSequence b s`.  **The directive's decisive probe came back free**:
  `Counting.card_filter_matchesAt_le` already bounds the `countOccurrences`/`winCount` seam by
  `|v|`, so **trigger E-T9 does not fire**.
* `card_filter_periodic` — an `L`-periodic predicate has exactly `r ×` as many witnesses in
  `[0,rL)` as in `[0,L)`.

### `G4EntropyConcat.lean` (rung 3, abstract) — the `(scale, repetition)` assembly

* `per`/`cyc` (periodic extension of a block, and its **cyclic** window count);
  `winCount_per_mul : winCount (per i) v (r·L i) = r·cyc i` — **a repeated block costs no seam**.
* `Tacc`/`rep` with `lt_rep_mul : (m+2)·(Tacc m + L (m+1)) < rep m · L m`, hence
  `Tacc_le_div` (group `m` dominates the past) and `mul_L_succ_le` (it dominates the next block).
* `grp` (via `Nat.findGreatest`, hypothesis-free as a def), `seq`, `grp_eq`, and
  `matchesAt_seq_iff` — **localization**: a window inside group `m` is a window of the periodic
  block.
* `card_edge_le`, and the key lemma
  **`cntIco_group`**: for every `r ≤ rep m`,
  `|cntIco (Tacc m) (Tacc m + r·L m) − r·cyc m| ≤ |v|`.
  The only error in a whole group is its right edge, once.

## 3. The next bounded test (lap 52)

Finish rung 3, in this order — all in `G4EntropyConcat.lean`:

1. `cntIco_partial`: for `Tacc m ≤ N < Tacc (m+1)` and `q := (N − Tacc m)/L m`,
   `cntIco (Tacc m) N ≤ (q+1)·cyc m + |v|` and `q·cyc m ≤ cntIco (Tacc m) N + |v|`
   (monotonicity of `cntIco` plus `cntIco_group` at `q` and `q+1`; `q+1 ≤ rep m` because
   `N < Tacc (m+1)`).
2. The real-valued deviation `D N := winCount (seq) v N − c·N` with `c := (2^{|v|})⁻¹`:
   * group step `|D (Tacc (m+1))| ≤ |D (Tacc m)| + γ·(Tacc (m+1) − Tacc m)` whenever
     `|cyc j − c·L j| + |v| ≤ γ·L j` for `j ≥ M`;
   * induction ⟹ `|D (Tacc m)| ≤ Tacc M + γ·Tacc m` for `m ≥ M`;
   * prefix ⟹ `|D N| ≤ Tacc M + 3γ·N + N/(M+1) + |v|` for `N ≥ Tacc M`
     (using `L m ≤ Tacc m/(m+1)` from `mul_L_succ_le`).
3. `tendsto_winCount_seq` and `isNormalSequence_seq`.

Then rung 2 (`G4EntropyBlockWord.lean`): the `(n, α, p)` enumeration of the scale-`i` sample,
`L i = |P_i|·|Atom_i|·m_i`, and `cyc i / L i → 2^{−|v|}` out of
`tendsto_occursCountP_primeLambertFour`.

## Claim limits

Nothing here is a statement about the normality of `G₄`.
