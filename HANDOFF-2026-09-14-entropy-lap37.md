# HANDOFF — entropy lap 37 (DEEP REFLECTION + rung 1), 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8971 jobs**.  New module sorry-free and
`#print axioms`-clean (trust triple).  No pre-expedition file edited.

## 1. What was proved / refuted / narrowed

**Proved** (`src/NormalNumbers/G4EntropyPosition.lean`, new) — rung 1 of the new objective, the
thread lap 36 left dangling:

```
posAt_blockVal                          the general-`p` digit dictionary (p + ℓ ≤ m)
Sched.posFreq                           posAvg at the schedule
Sched.abs_posFreq_sub_le_of_deficit     |posFreq − 2^{−ℓ}| ≤ 2√(log2·ℓδ/(m_K−ℓ+1))
Sched.abs_posFreq_sub_le_primeLambertFour   ≤ 2√(400 log2·ℓ/√K)   for 2ℓ ≤ m_K
Sched.tendsto_posFreq_growing           every ℓ(K) = o(√K)
Sched.posFreq_eq_count / posFreq_eq_digits
Sched.tendsto_occursCountP_primeLambertFour
    for every finite binary word v:
      #{(n,α,p) : OccursAt 2 G₄ v (2·kIdx(n,α) + p)} / (|P_K|·|Atom_K|·(m_K−|v|+1)) → 2^{−|v|}
```

That is **every** position of the sampled windows, not the `1/ℓ` aligned fraction lap 31 counted,
over the very `OccursAt 2 · v ·` predicate `isDisjunctive_two` is built from.  Constant `400`
vs the aligned `200` — the whole difference is `m_K − ℓ + 1 ≥ m_K/2`.

**Narrowed (the reflection's finding)**: normality of `G₄` is closed on this mechanism *and
measured* — sampled density `≤ ½(3/K⁴)^K`, window pinned at exactly `m_K = K/4` by
`entropy_cover_bound`, gap `≈ K^{4K}`; cause `GridParams.hQdvd ⟹ Q ≥ lcm(1,…,U)`, `U ≥ B^K`.
Three escapes re-costed and each closed by an existing theorem — **do not re-derive them**, see
`REFLECTION-2026-09-14-entropy.md` §1.

## 2. Which bottleneck moved

The objective moved.  `DIRECTION.md`'s CURRENT DIRECTIVE (reflection lap 37) now reads: the
**JOINT (`t`-wise) sampled-word frequency theorem** — `entropy_E1` bounds the law of the *whole*
vector and every result so far projects it to one coordinate; used jointly it says the sampled
windows of `G₄` **decorrelate**.  Rung 1 (this lap) is its `t = 1` case.

## 3. The next bounded test — rung 2

`G4EntropyJoint.lean`, and **probe the uncertain step first** (trigger E-T6): partition
`(gridAt i).Atom` into `t`-blocks; the per-block pattern coordinate is the product of the `t`
per-window `posAt`/`fullCoord` maps; is `∑_blocks (tℓ − H₂(pattern)) ≤ t·Δ` via
`FinLaw.H₂_le_sum_H₂_map`?  If yes, the averaged bound follows from the existing
Hellinger/Pinsker step on `tℓ` bits and rung 3 is the schedule instance + digit rendering
(`posAt_blockVal` is already general enough).  If no, record the exact degradation in
`PENDING_WORK.md`'s ACTIVE section and re-state with the true `t`-dependence — do **not** retreat
to `t = 1`, which is now proved twice over.

## 4. Lean notes from this lap

- `abs_posAvg_sub_le` needs `[Nonempty A]`; `instNonemptyAtomAt i : Nonempty (gridAt i).Atom :=
  ⟨fun _ => 0⟩` supplies it (`Atom = Fin K → Fin (s+1)`).
- `em` is ambiguous (`_root_.em` vs `Classical.em`) — and the branch was unnecessary: use
  `Tendsto.congr'` + `filter_upwards [eventually_ge_atTop v.length]` when the rendering lemma
  needs `ℓ ≤ kk i` (`kk i = 40000 + i`).
- `nlinarith` wanted the scaled hypothesis explicitly:
  `mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ 400 * Real.log 2 * ℓ)`.
