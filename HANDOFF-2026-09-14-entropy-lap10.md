# HANDOFF — entropy expedition, lap 10 (2026-09-14, Opus grind)

**Branch** `wip/g4-entropy`.  `lake build` green, 8953 jobs.  All work sorry-free, axiom-clean,
no pre-expedition file edited.  Previous baton: `HANDOFF-2026-09-14-entropy-lap9.md`.

## Headline: the brief's repair-direction 1 (translated grids) is **REFUTED**

```
Sched.not_dense_of_common_multipliers :
  0 < L → (every grid in F has its multipliers among `multipliers i`) →
  (F's sampled positions cover U below L) → ¬ (L ≤ 2 · |U ∩ [0,L)|)

Sched.not_readsHalf_of_common_multipliers :
  0 < L → (multipliers in `multipliers i`) → ¬ ReadsHalf i F G U L
```

Lap 9 showed a repair must read positions of upper density `≥ 1/2` and that a family of grids
doing so needs `≥ 2^(i+2)` members.  Lap 10 settles the route-decisive question it named: **a
larger family does not help at all, if the members share the implemented grid's multipliers.**

The reason is structural, not quantitative.  `kIdx_spec` gives `d_α ∣ kIdx G n α` for *every*
admissible sample point `n` of *every* grid — it is a property of the CRT input, not of the
frozen residue.  So each member reads only positions in `2 d_α ℕ + [0, m_K)`, a set that does
not depend on `b₀`, on `t_α`, or on `n`.  Varying the frozen residue (= translating the grid)
permutes nothing: the union of `|F|` copies of one periodic set is that set.  The bound
`|U ∩ [0,L)| ≤ Σ_{d ∈ D} m·⌊L/(2d)⌋` (`card_filter_le_of_multipliers`) **has no `|F|` in it**,
and `key_size` closes it at `L/8 < L/2` for every `L > 0`.

So the brief's item 1 — *average a proved family of admissible arithmetic samplers, varying
frozen residues or translated grids* — cannot produce the density-`1/2` input the barrier
requires.  Any repair must change the **multiplier set** `{d_α}` itself, i.e. supply a genuinely
different arithmetic input, not a translate of this one.

## Also this lap: the barrier in its sharp (eventual) form

`G4EntropyBarrier.lean` now proves the density hypothesis only needs to hold for large `L`
(finitely many positions cannot change a digit frequency):

```
G4Entropy.not_isNormal_maskReal_eventually
G4Entropy.exists_nonnormal_of_digitLocal_eventually
G4Entropy.upper_density_half_of_forces_normal :
  (P is S-local) → P x → (P forces normality) → c < 1/2 → 0 ≤ c → ∀ L₀,
    ∃ L ≥ L₀, c·L < |S ∩ [0,L)|
```

The last is the honest necessary condition: a repair must produce *upper* density `≥ 1/2`
(arbitrarily large prefixes), not one lucky prefix.  The plain-`∀L` versions of lap 9 are now
corollaries at `L₀ = 0`; helper lemmas were rebased on `hmiss : ∀ M, ∃ j ≥ M, ¬ S j`, which is
all the mask construction actually needs.

## Declaration map (lap 10)

`G4EntropyBarrier.lean` (added): `exists_not_mem_of_density_eventually`,
`not_isNormal_maskReal_eventually`, `exists_nonnormal_of_digitLocal_eventually`,
`nonneg_of_density`, `upper_density_half_of_forces_normal`.

`G4EntropyFamily.lean` (added): `periodCol`, `card_periodCol_le`, `mem_periodCol`,
`card_filter_le_of_multipliers`, `card_filter_le_of_multipliers'`, `multipliers`,
`card_multipliers_le`, `dmin_le_of_mem_multipliers`, `not_dense_of_common_multipliers`,
`not_readsHalf_of_common_multipliers`.

## Which bottleneck moved

The §6 positive branch had two named sub-directions.  Direction 1 is now closed **negatively**,
with a proof, not an estimate: no amount of averaging over translates changes the read set.
What survives is the demand that a repair change the multiplier set — and the multipliers are
where the grid's *transport* estimates live (`G4EntropyTransport`, `G4EntropyBudget`), so the
next question is whether a family of grids with genuinely different `{d_α}` can keep those
estimates uniform.  That is the brief's direction 2 (*synchronize construction scales*) in a
sharper form.

## Next bounded test, hardest first

1. **Can the multiplier set vary at all inside the proved machinery?**  `gridOf K N hK` fixes
   `d_α` through `gridD₀/gridUmax/gridQ`, which are dictated by `K` and the prime cutoff.  The
   bounded test: state `multipliers` for an arbitrary admissible grid at scale `K` and ask which
   `Finset ℕ` can occur.  If every admissible grid at scale `K` has `d_α ≡ 0 (mod Q_K)` — which
   `gridQ`'s divisibility (`hQdvd : ∀ m, 0 < m → m ≤ U → m ∣ Q`) strongly suggests — then **all**
   admissible multipliers share the factor `Q_K`, every sampled position of every admissible
   grid at scale `K` lies in `2 Q_K ℕ + [0,m)`, and the §6 positive branch closes *negatively in
   full*: no admissible sampler family whatsoever reads density `≥ 1/2`.  That is the decisive
   lemma to state next: `Q ∣ d_α` for every `GridParams` satisfying the interface.
2. If instead `Q_K ∤ d_α` in general, exhibit two admissible grids at one scale with coprime
   multipliers — that is the first real evidence the repair direction is alive.
3. Brief §5's (S) remains a defined leaf (`S_freq`), off the critical path.

## Lean gotchas from this lap

- `le_or_lt` is gone; use `Nat.le_or_lt` (or `le_or_gt`).
- `exact_mod_cast` through a nested `max` chain fails to unify the `set`-bound name: extract
  `have : N ≤ L := …` first, then cast that.
- Rebase mask-style constructions on the *consequence* they need (`∀ M, ∃ j ≥ M, ¬ S j`) rather
  than on the density bound, or every strengthening of the density hypothesis breaks every
  downstream helper's signature.
- `Finset.Icc 1 q` (not `range (q+1)`) for a column indexed by a positive multiplier: it drops
  the boundary `+1` and the resulting count needs no lower bound on `L`.
