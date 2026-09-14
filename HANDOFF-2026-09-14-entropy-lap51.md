# HANDOFF — entropy lap 51 (review + rungs 1, 3 complete, rung 2 scaffolded), 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  **HEAD** `dd3c370`.  Working tree **clean**.
`lake build` 🟢 **8982 jobs**.  All new modules **sorry-free**; no `axiom` introduced.
No pre-expedition G4/G5 file edited.

## 0. The lap in one line

A fresh-mind review re-pointed the campaign (trigger E-T7 had fired) at **an explicit normal
number read off `G₄`'s digits along the arithmetic sample**, and then proved **rung 1 and all of
rung 3** — so the abstract half of the objective is done and only the schedule instantiation
(rung 2) remains.

## 1. The direction change (altitude work; `DIRECTION.md` CURRENT DIRECTIVE, lap 51)

The lap-37 objective was met at laps 38–47, its boundary proved at 48, and 49–50 opened the
richness line — leaving no live objective.  Every endpoint of laps 31–50 is a statistic *at scale
`i`, with `i → ∞`*: a sequence of finite statements, never one infinite object.  The repo already
owns both pieces that close that gap (`Bridge.isNormal_realOfDigits`, and the `countOccurrences`
calculus of `Counting`/`CFChainFreq`), and `tendsto_occursCountP_primeLambertFour` is exactly the
input a block-concatenation argument consumes.  So:

> 🎯 an `x`-independent `samplePos : ℕ → ℕ`, built from the schedule alone, with
> `IsNormalSequence 2 (fun j => digitOf 2 (Int.fract G₄) (samplePos j))`, hence a normal real.

**Not a claim about `G₄`'s own normality**, which stays closed on this mechanism (lap 37).

## 2. What was proved

### `G4EntropyOcc.lean` — rung 1, the window-counting layer

```
winCount s v n = #{p < n : v matches s at p}        winCount_split
isNormalSequence_of_tendsto_winCount                the criterion
card_filter_periodic        an L-periodic predicate: r× as many witnesses in [0,rL) as in [0,L)
properDigits_of_isNormalSequence                    normality ⟹ ProperDigits (via the word [0])
sum_range_mul / card_filter_range_mul               [0,P·A) = P blocks of length A
```
**The directive's decisive probe came back free**: `Counting.card_filter_matchesAt_le` already
bounds the `countOccurrences`/`winCount` seam by `|v|`, so **trigger E-T9 did not fire**.

### `G4EntropyConcat.lean` — rung 3, COMPLETE

```
per / cyc                     a block's periodic extension and its CYCLIC window count
winCount_per_mul              winCount (per i) v (r·L i) = r·cyc i   EXACTLY — no seam
Tacc / rep, lt_rep_mul        (m+2)(Tacc m + L (m+1)) < rep m · L m
grp / seq / matchesAt_seq_iff localization: a window inside group m is a window of the block
cntIco_group                  |cntIco (Tacc m) (Tacc m + r·L m) − r·cyc m| ≤ |v|,  r ≤ rep m
cntIco_partial                a prefix of a group = q whole copies + a partial one
abs_dev_group                 |dev(T(m+1)) − dev(T m)| ≤ γ·(T(m+1) − T m) for a γ-good block
abs_dev_Tacc                  |dev(T m)| ≤ Tacc M + γ·Tacc m  for every m ≥ M
abs_dev_prefix                |dev N| ≤ Tacc M + γ·T m + (γ(N + L m) + c·L m + |v|)
tendsto_winCount_seq          cyc i/L i → c and L i → ∞  ⟹  winCount (seq L d) v N / N → c
isNormalSequence_seq          ⟹ IsNormalSequence b (seq L d)
isNormal_realOfDigits_seq     ⟹ IsNormal b (realOfDigits b (seq L d))
```
All three endpoints print `[propext, Classical.choice, Quot.sound]`.

**Stronger than the plan asked for: there is NO growth hypothesis on `L`.**  The flagged doubt
was that `L(i+1) ≫ ∑_{j≤i} L j` makes prefixes of a fresh block non-negligible; repetition
absorbs it entirely, because `rep m` is chosen *inside* the construction from `L` alone.  Any
family of finite blocks with converging window frequencies and lengths `→ ∞` yields one normal
real.

### `G4EntropyBlockWord.lean` — rung 2, scaffolded

```
nthP / nthA + sum_range_nthP / sum_range_nthA   fixed enumerations of P_i and of the atoms
nwin i = |P_i|·|Atom_i|,  wpos i w,  wpos_mk    the w-th sampled window's opening position
blen i = nwin i · kk i,  samplePosIn i j,  bdig x i j,  bdig_lt
```

## 3. The next bounded test (lap 52) — the ONE remaining lemma

`cyc_bounds` in `G4EntropyBlockWord.lean`.  With `m := kk i`, `W := nwin i`, `ℓ := v.length ≤ m`,
and

```
goodCount i x v := ∑ c : (gridAt i).Atom × Fin (kk i − ℓ + 1),
    ((PK i).filter fun n => OccursAt 2 x v (2 * kIdx (gridAt i) n c.1 + (c.2 : ℕ))).card
```

(*literally* the numerator of `tendsto_occursCountP_primeLambertFour`), prove

```
goodCount i x v ≤ cyc blen (bdig x) v i ≤ goodCount i x v + nwin i * v.length.
```

Chain, each step already available:
1. `cyc = card ((range (W*m)).filter (MatchesAt (per blen (bdig x) i) v))`; apply
   **`card_filter_range_mul`** with `P := W`, `A := m` to get `∑_{w < W} #{p < m : …}`.
2. Split each inner count at `p + ℓ ≤ m`; the excess is `≤ ℓ − 1` per `w` (the same
   `card_edge_le` shape used in `cntIco_group`).  Note the cyclic wrap at the very end of the
   block is *inside* that excess, since `L` is a multiple of `m`.
3. For `p + ℓ ≤ m`: `MatchesAt (per …) v (w*m+p) ↔ OccursAt 2 x v (wpos i w + p)`, because
   `(w*m+p+q)/m = w` and `(w*m+p+q)%m = p+q` for `q < ℓ`.  (`OccursAt b x w n = ∀ j (hj), digitOf
   b (fract x) (n+j) = w[j]`; `MatchesAt s w i = ∀ j < |w|, s (i+j) = w.getD j 0`; bridge with
   `List.getD_eq_getElem`.)
4. `∑_{w < W}` → `∑_{a < |P_i|} ∑_{e < |Atom|}` by **`sum_range_mul`**, then `wpos_mk`, then
   **`sum_range_nthP`/`sum_range_nthA`** to reach `∑_{n ∈ P_i} ∑_α`.
5. Swap to `goodCount`'s order (`Fintype.sum_prod_type`, `Finset.sum_comm`,
   `Finset.card_filter`), and identify `(range m).filter (· + ℓ ≤ m) = range (m − ℓ + 1)`
   (`Finset.ext` + `omega`) with `Fin.sum_univ_eq_sum_range`.

Then the limit is pure arithmetic:
`cyc/blen = [goodCount/(W·(m−ℓ+1))]·[(m−ℓ+1)/m] ± ℓ/m → 2^{−ℓ}·1 ± 0`,
and `blen i → ∞` since `kk i = 40000 + i`.  Feed both into `isNormal_realOfDigits_seq` (b = 2,
`hd := bdig_lt`) for the headline, and state `samplePos` explicitly:
`samplePos j = samplePosIn (grp blen j) (…)` — i.e. every value is a sampled position of the
schedule and the map does not mention `x`.

## 4. Which bottleneck moved

The route-decisive doubt when the objective was set was whether the concatenation could work at
all given the explosive growth of `|P_i|`.  It is settled: rung 3 needs no growth hypothesis.
What is left is rendering, which is bookkeeping with every ingredient already named above.

## Claim limits

Nothing in this lap is a statement about the normality of `G₄`; the number rung 3 builds is made
*from* `G₄`'s digits and is not `G₄`.  All endpoints concern the *sampled* positions only.
