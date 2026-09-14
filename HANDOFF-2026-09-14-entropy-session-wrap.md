# HANDOFF — entropy expedition, session wrap (2026-09-14, Opus, laps 9–15)

**Branch** `wip/g4-entropy`.  **HEAD** `147967e` (this doc is committed on top of it).  Working
tree clean.  `lake build` green, **8955 jobs**.  Every module added this session is
**sorry-free** and `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).  No
pre-expedition file was edited.  Preserved declarations re-verified clean:
`G4.isDisjunctive_four`, `G4.isDisjunctive_two`, `G4.isDisjunctive_base`,
`PrimeLambert.primeSumAtBase_eq_primeLambertAtBase`.

Per-lap detail: `HANDOFF-2026-09-14-entropy-lap9.md` … `-lap15.md`.  This file is the summary
and the pointer for the next session.

## What this session did

The expedition arrived with `T_E` refuted by one witness (lap 8).  Laps 9–15 turned that into a
complete, structural answer to the brief's §5 and §6, in seven green commits.

**Lap 9 — `G4EntropyBarrier.lean`.**  The refutation became a theorem.
`exists_nonnormal_of_digitLocal`: a property depending on a real only through its binary digits
on a set of upper density `c < 1/2` holds at a *nonnormal* point of `[0,1)` whenever it holds
anywhere.  Corollaries `half_le_density_of_forces_normal` (any repair must read density `≥ 1/2`)
and `not_satisfiable_of_forces_normal` (refuted-or-vacuous).  At the implemented schedule
(`card_isSampled_le_real`, density `≤ 1/4`): `exists_nonnormal_jointLocal` — *no* property
determined by the joint sample laws implies normality; `not_T_E'` recovers lap 8 as an instance.
Brief §6's remaining column stated from the actual digit windows (`WinMatch`) and disposed of:
`S_freq`/`T_S`, `Mix_freq`/`T_mix`, `T_S_vacuous`, `T_mix_vacuous`.
**Lap 9b — `G4EntropyFamily.lean`.**  `ReadsHalf` names the repair property without mentioning
normality; `card_family_ge_two_pow` : it needs `≥ 2^(i+2)` members.

**Lap 10.**  `not_dense_of_common_multipliers`: a family sharing the implemented grid's
multipliers covers `< 1/2` of *every* prefix at *any* family size — `d_α ∣ kIdx` comes from the
CRT input, not from `b₀`, so every member reads only `2d_α ℕ + [0,m)`.  Translated grids are
refuted.  Also the barrier in eventual form (`upper_density_half_of_forces_normal`).

**Lap 11.**  `not_dense_of_scale`: `d α = 1 + Q(D₀ + gridU B α)` with `hU` an interface field, so
*every* grid at a scale has its multipliers in `multSet Q D₀ U` (`≤ U+1` values).  No family at
one scale, of any size, reads half the positions.  (Lap 10's proposed lemma `Q ∣ d_α` recorded
as **false**: `mult_mod_Q` gives `d ≡ 1 mod Q`.)

**Lap 12 — `G4EntropyScales.lean`.**  `not_dense_of_scales`: any set of distinct scales `K ≥ 2`,
via `scaleWeight_le` (`w(K) ≤ 4^{-K}`) and `sum_inv_four_pow_le` (`Σ ≤ 1/12`).

**Lap 13.**  `not_dense_of_scalePairs`: the same for arbitrary scale *pairs* `(K,N)`, removing
lap 12's one-layer-count-per-scale restriction.  New analysis: `sum_pow_Icc_le`
(`Σ_{K≥2} r^K ≤ 2r²`, uniform in `r`), `sum_inv_sq_le` (telescoping `Σ 1/M² ≤ 1`),
`sum_double_le` (`Σ (4M)^{-K} ≤ 1/8`), `pairWeight_le`.

**Lap 14.**  `not_readableScale`: for every `C` and every `K ≥ max(C,4)`, `2 d_min > C·H_K·m`.
`GridParams` forces `Q ≥ U`, `D₀ = K·U`, `U ≥ B^K ≥ K^{3K}`, so the period beats the alphabet by
`K^{3K}`.  **The sparsity is intrinsic to the freezing construction**, not to any choice in it.

**Lap 15 — `G4EntropyControl.lean`.**  Brief §5.  `H₂_uniformOn` (exact entropy of a uniform law
on a subset) and `entropy_rate_not_control_bit`: a law with entropy exactly `m−1` — rate
`(m−1)/m → 1`, precisely what `entropy_E0`/`entropy_E1` give — whose leading bit is `1` with
probability `0`.  So the sampled entropy controls **no** fixed-length frequency; what it
controls is richness (`prob_infoSet_ge`, `card_infoSet_le`).

## Status against the brief

| item | status |
|---|---|
| §2 sample frozen + dictionary | done (laps 1–3) |
| §3A/B/C capture, cover, transport | done (laps 4–6) |
| §4 E0/E1 vs the implemented schedule | `entropy_E0`, `entropy_E1` — unconditional, clean |
| §5 which frequencies entropy controls | answered (lap 15): none at fixed length; richness only |
| §6 `T_E` | **refuted**, exact-premise witness (lap 8), structurally (lap 9) |
| §6 `T_S`, `T_mix` | refuted-or-vacuous (lap 9) |
| §6 positive branch | closed negatively: laps 10, 11, 12, 13, and intrinsically 14 |

The brief's §8 outcome condition (E0/E1 settled AND `T_E` proved or refuted with a witness
meeting its exact premise) is **met**.

## What is NOT claimed

Nothing about the normality of `G₄` — it may well be normal.  Nothing about arithmetic
mechanisms outside the `GridParams` interface.  The output is a proof that *this* sample, however
strong the entropy statement about it, cannot bridge to ordinary normality, plus the exact
structural reason.

## Next session

1. **Altitude lap first.**  `DIRECTION.md`'s CURRENT DIRECTIVE and `STATUS.md` are owned by
   review laps and still describe `T_E` as the open objective; they should record the table
   above.  Grind laps must not edit them — this session did not.
2. **If more mathematics is wanted inside this campaign**: a sampler not built from a frozen CRT
   modulus.  `not_readableScale` states exactly what it must achieve (`2 d_min ≤ C·H·m`), and
   nothing here rules such a mechanism out — it is simply not this one.  That is a new
   construction, not a repair, and is arguably a new attended objective rather than a lap.
3. Unrelated open `sorry`s elsewhere in `src/` (Mahler / oscillation, 23 total) are **not** this
   campaign's and were untouched.
