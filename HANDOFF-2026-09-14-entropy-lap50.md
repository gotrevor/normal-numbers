# HANDOFF — entropy lap 50 (joint richness on `G₄`'s digits), 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8979 jobs**.  `src/` sorry-free.  No `axiom`.

## 0. The lap in one line

The joint richness statement is rendered on `G₄`'s binary digits: **for at least half the
blocks, the `t` sampled windows take at least `2^{t·m_K − 200t√K}` distinct joint values** — a
per-block statement with *no averaging over positions at all*.

## 1. What was proved — `G4EntropyJointRich.lean`, schedule layer

```
suppOf_map_empirical         suppOf ((empirical S hS f).map g) = S.image (g ∘ f)
jointValues i t x b          the distinct t-tuples of m_K-bit blocks at block b's positions
suppOf_map_tupleOf           the support of the tuple law IS `jointValues`
jointValues_eq_digits        jointValues = (P_K).image (n ↦ (blockVal x (2·kIdx(n, blkSched b s)) m_K)_s)
joint_richness_primeLambertFour
tendsto_richness_shortfall   200√K / m_K = 800/√K → 0
```

**`joint_richness_primeLambertFour`**: for every `i` and `t ≥ 1` (with `2t ≤ |Atom|`) there is a
set `Poor` of blocks with `2|Poor| ≤ nblk_K` such that every block outside it satisfies

```
|jointValues i t G₄ b|  ≥  2^{t·m_K − 200t√K}.
```

Since `m_K = K/4`, the shortfall is a `800/√K` fraction of the exponent
(`tendsto_richness_shortfall`), so the **richness rate tends to 1**.

## 2. Which bottleneck moved

The campaign's endpoints had all been `ℓ¹` frequency statements — necessarily so, by lap 48.
This is the first endpoint of a *different type*: it is **pointwise in the block** (half the
blocks individually, not on average) and says nothing about frequencies.  The lap-48
obstruction does not apply, because it constrains only the control of pattern *frequencies*;
its own witness is rich.

Chain of the lap: `sum_tuple_deficit_le` (lap 49, zero slack) + `two_pow_H₂_le_card_support`
(entropy ⟹ support) + Markov over blocks + `suppOf_map_empirical` (support = image) +
`ZSample_eq_blockVal` (digit rendering).

## 3. The next bounded test

Per **E-T7** the next altitude lap owes a successor target.  What is now settled:

* frequencies, averaged over positions: laps 38–47, complete (lap 47 strongest);
* frequencies, pointwise: refuted, lap 48;
* richness, per block: laps 49–50.

Remaining candidates, in decreasing value:

1. **Richness in *every* block, not just half.**  The Markov step is lossy: `∑_b d_b ≤ Δ` gives
   a "most blocks" statement.  A per-block deficit bound would need the deficit to be spread,
   which the joint law need not do — and the lap-48 style witness (all the deficit in one
   block) probably **refutes** the every-block form.  A bounded probe: build that witness
   (uniform on {tuples of block 0 constant} × free elsewhere) and compute its per-block deficit.
   Either way the answer is an endpoint.
2. **Joint richness at `t → ∞` with `K`**: the current statement is for fixed `t`; the bound
   `2t ≤ |Atom|` and `200t√K ≤ t·m_K` allow `t` to grow with `K`.  State the largest `t = t(K)`
   for which the richness rate still tends to `1` (it is `t` free, since the rate is
   `1 − 800/√K` independent of `t` — worth recording as a corollary).
3. Close the campaign; brief §8 has been satisfied since lap 31.

Candidate 1 is the only genuinely open one.

## Claim limits (unchanged)

Nothing here is a statement about the normality of `G₄`; all endpoints concern the *sampled*
positions only.
