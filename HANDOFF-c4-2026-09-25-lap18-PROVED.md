# HANDOFF C4 — 2026-09-25, lap 18: **C4 IS PROVED**

Branch `wip/c4-infinite`, HEAD `ee38065`, tree CLEAN, `lake build` green (9267 jobs).

```
#print axioms NormalNumbers.Abelian.c4_realizable
  --> [propext, Classical.choice, Quot.sound]
```

**`c4_realizable`**: for every `S ⊆ {L ≥ 1}` with `S = ∅ ∨ 1 ∈ S` there is a binary sequence
abelian-normal at *exactly* the window lengths in `S`.  Necessity
(`abelianAt_one_of_abelianAt`) was already clean, so the C4 dichotomy is complete in both
directions.  No `sorry`, no `axiom`, in the whole C4 chain.

## What lap 18 added (all in `AbelianWindowLayers.lean` and the new `AbelianWindowBuild.lean`)

Item 4 of the `DIRECTION.md` route, start to finish.

1. **`stage_eq_of_ge` / `limSeq`** — `stage x n` = the width-`Q n` block engine driven by the
   digits of a binary normal `x`.  `stage_eq_absGad` says the perturbation at a covered position
   is the *absolute* gadget action at base `Q i * (m / Q i) + off i`, with no `n` in it; combined
   with `notMem_quad_of_lt` (layer `i` reaches no position below `Q i / 2 ≥ 32·2^i`) this gives
   `stage x n m = stage x m m` for `m ≤ n`.  So `limSeq x m := stage x m m`.
2. **`diffCount_stage_le`** — `diffCount (limSeq x) (stage x n) M ≤ (3/(16·2^n))·M`.  A differing
   position is covered by a layer `n < i ≤ m` (`diff_subset`); each layer covers `≤ 12M/Q i`
   positions below `M` uniformly (`card_cover_real_le`, the `Q i > 2M` case being VACUOUS by
   `hbig`); `Q i ≥ 64·2^i` sums the tail.  `c n = 0`, `η n → 0`.
3. **The exact law at an arm** — `segSet_unsep_gen`: a length-`L` window separates a gadget only
   from block `0`, at residue `p'+1`, and only when the arm is `L`.  **No arm-injectivity needed**,
   which is what lets a whole layer row share one arm.  `segGf_coeff_defect` pins the defective
   factor to exactly `3/4` (the dichotomy allows two values; the strict defect kills one).  Hence
   `winGf_coeff_plain_res` / `winGf_coeff_defect_res`, and summing over residues:
   `blockFreq_at_arm : blockFreq … (Q n + arm m) (arm m) 0 = (1 - 1/(4·Q m)) / 2^(arm m)` —
   **independent of `n`**, and `< 1/2^L`.  That single value is what the transfer needs.
4. **The verdicts** — `limSeq_isAbelianAt` (every non-arm length) and `limSeq_not_isAbelianAt`
   (every arm), both by `tendsto_onesFreq_of_linear_diff`.
5. **`AbelianWindowBuild.lean`** — the layer system exists.  The key simplification: the periods
   are *offset-independent* (`bQ 0 = 4(arm 0+64)`, `bQ (n+1) = 2·bQ n·(arm(n+1)+2)`), so
   `bQ_pos/_double/_dvd/_grow` need no offsets and the recursion is NOT mutual.  The offset at
   stage `n+1` is then chosen by `exists_avoiding_offset` inside `range (bQ n)` (`badRes`,
   `card ≤ 16`, `goodOff_of_notMem` via the `-δ'` translation mod `Q`) and translated by
   `bQ n · (arm(n+1)+2)` into the top half — translation by a multiple of `bQ n` preserves every
   residue mod `bQ m`, `m ≤ n`, so `hdisj` survives while `hbig` becomes automatic.
   `bLayerSys` then satisfies all nine `LayerSys` fields.
6. **Assembly** — `c4_realizable_of_arms` (any injective arm family with arms `≥ 2`), then
   `c4_realizable_of_mem_one` by splitting on whether `Sᶜ ∩ {L ≥ 2}` is finite
   (`c4_realizable_of_finite_compl`, lap 17) or infinite (`Nat.nth` enumeration).

## One structural note for a reader

`c4_realizable_of_mem_one` and `c4_realizable` **moved** from `AbelianWindowSets.lean` to the end
of `AbelianWindowBuild.lean`.  The statements are byte-identical; the move was forced, since the
construction imports `Sets`.  A pointer comment sits where they used to be.

## What is left in this repo

Nothing on C4.  The off-campaign designated-open leaves are untouched:
`PrimeLambertOscillation.phaseOscillation`, `MahlerDriftOne.exists_prime_nonresidue`,
the Swing/CF leaves, `PairDecoupleProve`.
