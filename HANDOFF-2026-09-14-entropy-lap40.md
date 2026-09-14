# HANDOFF — entropy lap 40 (independent per-window offsets, abstract + schedule), 2026-09-14

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8975 jobs**.  New module sorry-free.

## 0. The lap in one line

`DIRECTION.md`'s 🎯 asks for a position `p_s` **per window**; rung 3 gave only the common
aligned `jℓ`.  This lap closes that gap abstractly and at the schedule — at **zero** extra
entropy cost.

## 1. What was proved — `G4EntropyJointPos.lean`

The mechanism is a change of window, not new information theory.  Cut each window to a common
length `D` starting at *its own* offset:

```
cutCoord m D a z        the D-bit sub-window of z beginning at position a
cutTuple m D ρ          applied coordinatewise, each window at its own offset ρ α
outCoord / cut_out_injective / cutFam
H₂_cutTuple_ge          L.H₂ − |A|(m−D) ≤ H₂(L.map (cutTuple m D ρ))
blkAt_cutCoord          blkAt D ℓ j (cutCoord m D a z) = posAt m ℓ (a + jℓ) z
shiftOf / shiftOf_blk   the offset a blocking + offset vector attaches to an atom
patPos m ℓ t D pp blk   pack_s (posAt m ℓ (pp s + jℓ) (z (blk b s)))
abs_avg_patPos_prob_opt |avg_{b,j} Pr[pattern] − 2^{−ℓt}| ≤ 2√(log2·ℓΔ/(|B|·D))
Sched.ppMax / Sched.posPatFreq
Sched.abs_posPatFreq_sub_le_of_deficit   ≤ 2√(2 log2·ℓtδ/(m_K − max pp))
```

`H₂_cutTuple_ge` is `H₂_lowTuple_ge` generalized from one common truncation to a
**per-coordinate** one, and it is what makes the offsets free: an `m`-window deficit `Δ` becomes
a `D`-window deficit of the *same* `Δ`, so `abs_avg_patCoord_prob_opt` applies verbatim with
`m ↦ D`.  `pp = 0`, `D = m` recovers the aligned bound exactly.

## 2. Which bottleneck moved, and a narrowing recorded

Moved: the offsets.  Narrowed (recorded in `PENDING_WORK.md`, do not re-derive): the **uniform
average over all position vectors** `(p_1,…,p_t) ∈ [0,m−ℓ]^t` is *not* reachable by this ledger
— a jointly injective family of `(m/ℓ)^t` pattern coordinates per block would carry
`tℓ(m/ℓ)^t` bits against the `tm` its windows hold.  The reachable object is an arbitrary
offset vector plus one common aligned shift `j`, which is `patPos`.

## 3. Next bounded test (lap 41)

`abs_posPatFreq_sub_le_primeLambertFour` (`δ = 50√K`, `2(max pp + ℓ) ≤ m_K` ⟹
`≤ 2√(800 log2·ℓt/√K)`), the limit, the count/digit rendering, and the endpoint
`tendsto_occursCountJointPos_primeLambertFour`.

## 4. Lean notes harvested this lap

- `omega` needs `ℓ ≤ (j+1)*ℓ` spelled out (`Nat.le_mul_of_pos_left ℓ (by omega)`) before it can
  prove `D − (j+1)ℓ + ℓ ≤ D` from `(j+1)ℓ ≤ D`.
- `hex.choose = (b, s)` from injectivity: `hblk hex.choose_spec` types directly.
- `FinLaw.prob_singleton_map_map` plus a `funext`-proved function equality is the clean way to
  identify a two-step pushforward with a one-step one without unifying two `FinLaw.map`s.
