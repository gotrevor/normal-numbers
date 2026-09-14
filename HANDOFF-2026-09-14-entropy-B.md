# HANDOFF — objective B, the residue probe: **VERDICT NO**, and the refutation is a theorem

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8997 jobs**.  New module
`src/NormalNumbers/G4EntropyResidueProbe.lean`, sorry-free, every endpoint
`[propext, Classical.choice, Quot.sound]`.

## The question

> The sample fixes ONE class `G.b₀ mod G.P₀`.  For every estimate in the E0 cone, does it hold
> for **every** class with frozen multiplier residues `c`, same constants?  All-YES means the
> union over classes reads density one and forces normality of `G₄` itself.

## Per-declaration audit — the estimates are class-uniform

| declaration | how `b₀` enters | every class, same constants? |
|---|---|---|
| `Sched.card_apSample_ge_half` | hypotheses are `a < P₀`, `2P₀ ≤ X` only | **YES**, verbatim |
| `GridParams.exists_mult_mul` / `EntropySample.kIdx_spec` | `b₀_modEq α : b₀ ≡ t_α (mod d_α²)` | **YES** *re-based*: `exists_kIdxOf_eq` (new) proves `d_α ∣ (n − b mod d_α²)/d_α` for every `b`, using only `d_α² ∣ P₀` |
| `GridParams.two_mul_card_le_of_not_dvd`, `goodPrime_of_not_dvd_P₀`, `prime_dvd_freezeQ_of_le`, `dist_dvd_freezeQ` | not at all — only `P₀`, `freezeQ`, `ρ` | **YES** |
| `gridFrame_propB_of_bound`, `entropy_cover_bound`, `entropy_cover_sum_le`, `log_det_one_add_tensorGram_le'` | not at all (the cover term is `X`- and `b₀`-free) | **YES** |
| `gridFrame_propC_four` / `G4Frame.smallPrimeBound` | only via `Psz = |apSample X P₀ b|` and `¬ p ∣ P₀` | **YES** |
| `ScheduleWitness.hbig` / `Sched.hbig_holds` | only via `|P|` and `Mx` | **YES** |
| `ScheduleWitness.hfar` / `G4FarTail.farC`, `sum_omegaR_shiftG_le` | only via `|P|` and `X + Dm` | **YES** |
| `gridFrame_propA` | calls `propA_of_progression … 0 …`, the `0` being the `t_α`-relative offset | **YES** *re-based*: the offset argument is already a parameter; class `b` feeds `c_α = b mod d_α²`, which shifts `Frame.θ` by an `n`-free, `X`-free constant.  `θ` enters the estimates only through `pieceCenter`, never a size bound, so no constant moves |
| `G4EntropyPositions.kIdx_pos` | argues `b₀ = t_α` is impossible | **NO** — but it is a non-vacuity statement, not an estimate.  Off `b₀`, `kIdxOf = 0` is possible (`n < d_α²`), which costs exactly the `+1` cell in `periodCol₀` below |

So the arithmetic audit is **all-YES on the estimates**, with two structural re-basings
(`kIdx → kIdxOf`, `θ`'s offset) and one non-vacuity lemma that needs a `+1`.

## But the payoff is unavailable: **verdict NO**

The all-YES conclusion the probe hoped for — "the union over classes reads density one" — is
**false**, and not for a quantitative reason.  The confinement of read positions is a property
of the **multipliers**, not of the class:

```
G4Entropy.exists_kIdxOf_eq      : ∀ b, n ∈ apSample X P₀ b → ∃ q, kIdxOf G b n α = d_α * q
G4Entropy.card_filter_le_of_classes : |{j < L : U j}| ≤ |D| * ((L/(2 dm) + 1) * m)   -- no |B|
Sched.not_dense_of_any_residue  : 2·dmin i ≤ L → ¬ (L ≤ 2 * |{j < L : U j}|)
```

`not_dense_of_any_residue` says: at scale `i`, for **any** finset `B` of residue classes mod
`P₀` — all of them, if you like, each with its own frozen multiplier residues — the positions
they read below `L` are less than half of `[0, L)`, at every prefix `L ≥ 2·dmin i`.  Density one
is therefore out of reach by a factor `≥ 2`, uniformly in `|B|`.

This is the class-side companion of `G4EntropyFamily.not_dense_of_scale`, which had closed only
the *grid* direction (every grid there samples its own `b₀`).  Between them the brief's §6
positive branch is now closed on both axes: **no family of samplers at a fixed scale, of any
size, over any grids and any residue classes, reads half of any prefix.**

## The surviving arithmetic gap, named

It is not an estimate.  It is `d_α ∣ kIdx`, i.e. `d_α² ∣ P₀` — the very fact that makes the
frame's transport exact (`exists_mult_mul` is what `PropA` consumes).  The sample must freeze
the multiplier residues to transport, and freezing them confines the read positions to
`⋃_α (2 d_α ℕ + [0, m_K))`, of density `≤ H·m_K/(2 dmin) ≤ 2^{−(i+3)}`.  Exactness and density
are in direct tension; moving the class trades neither.

## State of the 18:20 RE-TARGET override

* **A0** — verdict **NO**, obstruction proved: `ScheduleWitness.X_lt_X_step`
  (`HANDOFF-2026-09-14-entropy-A0.md`, `G4EntropyXCeiling.lean`).
* **A** — stopped per the override's instruction, obstruction named.
* **B** — verdict **NO**, refutation proved: `Sched.not_dense_of_any_residue`
  (this handoff, `G4EntropyResidueProbe.lean`).

Both objectives now have verdicts and A's obstruction is named, which is the override's stated
stopping condition.
