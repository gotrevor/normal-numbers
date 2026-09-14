# HANDOFF — entropy expedition, lap 11 (2026-09-14, Opus grind)

**Branch** `wip/g4-entropy`.  `lake build` green, 8953 jobs.  Sorry-free, axiom-clean, no
pre-expedition file edited.  Previous baton: `HANDOFF-2026-09-14-entropy-lap10.md`.

## Headline: the §6 positive branch's *averaging* direction is closed, **in full**

```
Sched.not_dense_of_scale (i) (F) (G) (U') (hL : 0 < L)
  (hT  : each member's offsets are nonconstant)
  (hQ  : (G ν).Q  = gridQ (KK i) (N (KK i)))
  (hD₀ : (G ν).D₀ = gridD₀ (KK i) (N (KK i)))
  (hU  : (G ν).U  = gridUmax (KK i) (N (KK i)))
  (hcov: the family's sampled positions cover U' below L) :
  ¬ (L ≤ 2 · |U' ∩ [0,L)|)
```

Lap 10 refuted *translates* of the implemented grid.  Lap 11 refutes **every** grid the
machinery admits at a scale, of any family size:

`GridParams.d α = mult B Q D₀ α = 1 + Q·(D₀ + gridU B α)` and `hU : gridU B α ≤ U` is a field of
the interface.  So every multiplier of every grid with the schedule's scale parameters lies in

```
multSet Q D₀ U = {1 + Q(D₀ + u) : u ≤ U}      (card ≤ U + 1, each ≥ 1 + Q D₀)
```

— the atoms, the digits of `B`, the frozen residue `b₀`, the translations: none of them can move
a multiplier off that progression.  Feeding `multSet` to lap 10's family-free counting bound
gives `|U' ∩ [0,L)| ≤ (U+1)·m·⌊L/(2(1+Q D₀))⌋`, and the parameter inequality
`4(U+1)m_K ≤ 1 + Q D₀` (from `Q ≥ U`, `D₀ = K·U`, `m_K = K/4`, so `Q D₀ ≥ K U²` against
`(U+1)K`) closes it at `L/8 < L/2`, for **every** `L > 0`.

### What this settles

The brief's §6 repair direction 1 — *average a proved family of admissible arithmetic samplers,
varying frozen residues or translated grids* — cannot produce the density-`≥ 1/2` input that
`G4EntropyBarrier.upper_density_half_of_forces_normal` shows any transfer needs.  Not because
the family would have to be large (lap 9's `2^(i+2)` bound), but because **the multipliers
themselves are pinned to an arithmetic progression by the interface**, and the read set is a
union of `2d·ℕ + [0,m)` over that progression.

A repair must therefore change the *scale parameters* `(Q, D₀, U)` — i.e. it is the brief's
direction 2 (synchronize construction scales), not direction 1, that remains open.

### The conjecture lap 10 proposed is FALSE (recorded)

Lap 10 named `Q ∣ d_α` as the decisive lemma.  It is false: `mult_mod_Q` gives `d_α ≡ 1 (mod Q)`.
The correct structural statement is the progression above, which is strictly stronger for this
purpose (it pins `d_α` to `U+1` values, not just to a residue class).

## Declaration map (lap 11)

`G4EntropyFamily.lean` (added): `multSet`, `card_multSet_le`, `d_mem_multSet`,
`le_of_mem_multSet`, `card_filter_le_of_scale`, `two_le_gridUmax`, `not_dense_of_scale`.

## Which bottleneck moved

Before: "can a big enough family of samplers read half the digits?"  After: **no family at a
fixed scale can, ever** — and the obstruction is identified as the multiplier progression
`1 + Q(D₀+u)`, a consequence of the CRT/freezing construction itself, not of any choice made
inside it.  The expedition's §6 output is now a complete negative answer for direction 1 plus a
precisely located demand on any repair.

## Next bounded test, hardest first

1. **Direction 2, made precise.**  Across scales the multipliers *do* move (`Q_K`, `D₀_K` grow
   with `K`), so the union over `K` of the sampled sets is not covered by one progression.  But
   `card_isSampled_le` already bounds that union by `L/4` — the growth is far too fast.  The
   bounded test that decides direction 2: for which sequences `K_j` of admissible scales is
   `Σ_j H_{K_j} m_{K_j}/(2 dmin(K_j))` bounded below by `1/2`?  State it as a hypothesis on an
   abstract admissible scale sequence and prove the implication; the implemented `X(K)` growth
   is what makes the series geometric, so the question is exactly *how slowly may admissible
   scales grow*.  If the arithmetic estimates force `dmin` to grow faster than `H·m` at every
   admissible scale — which `key_size` proves for the implemented sequence — then direction 2
   closes too and the expedition's §6 answer is complete and negative.
2. `G4EntropyBudget`/`G4EntropyTransport` are the modules that would have to certify any
   alternative scale sequence; the bounded test is to read off which inequalities there are
   *forced* (`key_size`'s inputs: `Q ≥ U ≥ B^K`, `D₀ = K U`, `B ≥ K³`) versus chosen.
3. Brief §5's (S) remains a defined leaf (`S_freq`), off the critical path.

## Lean gotchas from this lap

- `set x := e with hx` does NOT fold `e` inside hypotheses created *after* the `set`; `omega`
  then sees two atoms.  `rw [← hx] at hnew` after introducing them.
- `mult B Q D₀ α = 1 + Q * (D₀ + gridU B α)` holds by `rfl`, so membership in an image over
  `range (U+1)` closes with `rfl` as the third component.
