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

### Rung 3 is COMPLETE (same lap)

```
cntIco_partial   a prefix of a group = q whole copies + a partial one
abs_dev_group    |dev(T(m+1)) − dev(T m)| ≤ γ·(T(m+1) − T m) for a γ-good block
abs_dev_Tacc     |dev(T m)| ≤ T M + γ·T m for every m ≥ M   (induction over groups)
abs_dev_prefix   |dev N| ≤ T M + γ·T m + (γ(N + L m) + c·L m + |v|)
tendsto_winCount_seq       cyc i/L i → c and L i → ∞  ⟹  winCount(seq) v N / N → c
isNormalSequence_seq       ⟹ IsNormalSequence b (seq L d)
isNormal_realOfDigits_seq  ⟹ IsNormal b (realOfDigits b (seq L d))
```
plus `properDigits_of_isNormalSequence` in `G4EntropyOcc.lean` (a normal sequence never sticks
at `b−1`, because the word `[0]` has positive frequency).  All three endpoints print
`[propext, Classical.choice, Quot.sound]`.

**So the abstract half of the objective is done**: any family of finite blocks whose window
frequencies converge, with lengths `→ ∞`, yields one normal real.  No hypothesis on how fast
`L` grows — repetition absorbs that.

## 3. The next bounded test (lap 52) — rung 2, the only remaining piece

`G4EntropyBlockWord.lean` must supply exactly the two hypotheses of `isNormal_realOfDigits_seq`
for `b = 2`:

* `L i := (PK i).card * Fintype.card (gridAt i).Atom * kk i` (all `x`-independent naturals;
  `0 < L i` needs `PK i ≠ ∅`, recorded in lap 1, and `0 < kk i`).  `L i → ∞` is immediate from
  `kk i = K i / 4 → ∞`.
* `d i j :=` the `j`-th digit of the scale-`i` block: decode `j` as `((a·|Atom| + α)·kk i + p)`,
  with `a` indexing `PK i` (via `Finset.orderIsoOfFin` or `.sort`) and `α` indexing the atom
  Fintype, and return `digitOf 2 (Int.fract G₄) (2·kIdx (gridAt i) n_a α + p)`.
* `cyc L d v i / L i → 2^{−|v|}`: `cyc` counts **cyclically** in one period, i.e. over all
  `(a, α, p)` including the `|v|−1` wrap positions per `(a,α)` window; the linear count over
  fitting `p` is exactly the numerator of `tendsto_occursCountP_primeLambertFour` (a Fubini
  re-index of its `∑_{c : Atom × Fin (kk i − ℓ + 1)}`), and the two differ by `≤ (|v|−1)` per
  window, i.e. a `(|v|−1)/kk i → 0` fraction.  Its denominator is `|P_i|·|Atom_i|·(kk i − ℓ + 1)`
  against `L i = |P_i|·|Atom_i|·kk i`, another `→ 1` factor.

Then the headline is `isNormal_realOfDigits_seq` applied to that `(L, d)`, plus a statement
naming `samplePos` explicitly.

## Claim limits

Nothing here is a statement about the normality of `G₄`.
