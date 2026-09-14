# HANDOFF — entropy expedition, lap 9 (2026-09-14, Opus grind)

**Branch** `wip/g4-entropy`.  `lake build` green, 8953 jobs.  Two new modules, both
**sorry-free**, no new axioms, no pre-expedition file edited.

Previous baton: `HANDOFF-2026-09-14-entropy-lap8.md` (T_E refuted).  Binding orders: the
entropy CURRENT DIRECTIVE at the top of `DIRECTION.md`, route trigger **E-T2** (`not_T_E`
landed ⇒ next objective is the §6 positive branch).

## 1. What was proved

### (a) The refutation is a THEOREM, not a witness — `G4EntropyBarrier.lean`

Lap 8 killed `T_E` with one explicit number.  Lap 9 extracts the mechanism, with no reference
to `G₄`, to the schedule, or to entropy:

```
G4Entropy.exists_nonnormal_of_digitLocal :
  c < 1/2 → (∀ L, |S ∩ [0,L)| ≤ c·L) →
  (P is S-local) → P x → ∃ y ∈ [0,1), P y ∧ ¬ IsNormal 2 y
```

*`S`-local* means `P x` depends on `x` only through the binary digits of `x` at the positions
of `S`.  The proof is the masking construction `maskReal S x` (digits of `x` on `S`, `0` off
it), now stated for an arbitrary position set.  Two corollaries are the usable forms:

* `half_le_density_of_forces_normal` — **the contrapositive the positive branch needs**: a
  satisfiable `S`-local premise implies normality on `[0,1)` only if for every `c < 1/2` some
  prefix `[0,L)` holds more than `c·L` positions of `S`.  I.e. *any* repair must read a
  position set of upper density `≥ 1/2`.
* `not_satisfiable_of_forces_normal` — such a premise is **refuted or vacuous**.

Instantiated at the implemented schedule (`card_isSampled_le_real`: density `≤ 1/4`):

```
Sched.exists_nonnormal_jointLocal :
  (P determined by the joint laws `jointLawAt i ·`) → P x → ∃ y ∈ [0,1), P y ∧ ¬ IsNormal 2 y
```

**No property of the arithmetic sample whatsoever can imply ordinary normality.**  `not_T_E'`
recovers lap 8's headline as a one-line instance of this.

### (b) Brief §6's remaining column, stated and disposed of

`S_freq`/`T_S` (sampled block frequencies) and `Mix_freq`/`T_mix` (sampled *mixture*
frequencies, over every offset `h₀` with `h₀ + |w| ≤ m_K` inside the block) are now named
`Prop`s.  Both are defined from the digit windows the schedule genuinely reads (`WinMatch i x w
h₀ z : ∀ h < |w|, digitOf 2 (fract x) (2·kIdx + (h₀+h)) = w[h]`), so their locality is exact
rather than a modelling choice — `S_freq_local`, `Mix_freq_local` (via `eventually_fits`: a
fixed word eventually fits in the block, and `Tendsto` only sees the tail).

```
Sched.T_S_vacuous   : T_S   → ∀ x, ¬ S_freq x
Sched.T_mix_vacuous : T_mix → ∀ x, ¬ Mix_freq x
Sched.not_T_S_of_exists   : S_freq x   → ¬ T_S
Sched.not_T_mix_of_exists : Mix_freq x → ¬ T_mix
```

Unlike `T_E` (whose premise is *known* satisfiable, by `E0_primeLambertFour`), satisfiability
of (S) is open, so the honest disposal is the disjunction: each of `T_S`, `T_mix` is either
false or transfers nothing at all.

### (c) The positive branch, quantified — `G4EntropyFamily.lean`

The brief's item 1 is *average over a family of admissible samplers*.  Named as
`Sched.ReadsHalf i F G U L` (a finite family `F` of grids, each with the implemented grid's
multiplier lower bound `dmin i` and atom count, whose sampled positions cover a set `U` filling
at least half of `[0,L)`) — stated with **no reference to normality**.  The implication it
supplies:

```
G4Entropy.card_family_ge       : dm ≤ |F|·c             (pure counting, any position sets)
G4Entropy.card_grid_family_ge  : dm ≤ |F|·(|Atom|·m)    (families of GridParams)
Sched.card_family_ge_two_pow   : ReadsHalf i F G U L → 0 < L → 2^(i+2) ≤ |F|
```

**A bounded family of translated grids can never work.**  The number of admissible samplers
needed to see half the digit positions grows at least geometrically in the scale index, so a
repair must vary the frozen residue over a set that *grows with `K`* — averaging over any fixed
finite set of translations leaves the lap-8 witness alive (its digits are unconstrained off a
set of density `≤ |F|/4`).

## 2. Which bottleneck moved

Before lap 9 the refutation was a single counterexample; a reader could still hope that a
slightly different sampled statistic escapes it.  It does not: locality alone kills every
statistic, and the density `1/2` threshold is now a *named, proved* necessary condition on any
repair, with a proved geometric lower bound on the size of the averaging family that the
brief's first proposed repair would need.  The frontier is no longer "is T_E true" but
"**exhibit a family of admissible samplers of size ≥ 2^(i+2) at scale i, with uniform transport
estimates**" — or show no such family is admissible.

## 3. Next bounded test, hardest first

1. **Is a growing family admissible at all?**  `ReadsHalf` demands uniformity: the grid's
   transport/estimate machinery (`G4EntropyTransport`, `G4EntropyBudget`) must survive for each
   member.  The concrete test: fix `i`, and ask whether the frozen residue `b₀` can be varied
   over `≥ 2^(i+2)` values while `gridOf`'s side conditions (`b₀ < P₀`, prime cutoff, remainder)
   all hold.  `P₀` is astronomically larger than `2^(i+2)`, so the *count* is available; what is
   NOT yet known is whether `kIdx` then sweeps a positive fraction of residues mod `2 d_α` —
   that is the real content and the next lemma to state.
2. **The sharper obstruction**: `d_α ∣ kIdx` holds for *every* admissible grid with these
   parameters.  If the divisibility is forced by the CRT input rather than by the choice of
   `b₀`, then the union over the whole family still lies in `⋃_α (2 d_α)ℕ`, and `ReadsHalf` is
   *unsatisfiable*, which would close the positive branch negatively.  Deciding this is the
   route-decisive question now: state `kIdx_residue_range` (which residues mod `2 d_α` are hit
   as `b₀` varies) and prove or refute it.
3. Brief §5's (S) remains a leaf; `S_freq` is now defined, so proving `S_freq G₄` (or its
   failure) is a well-posed side question — not on the critical path.

## 4. Lean gotchas from this lap

- `variable {S}` after a `def` does not retroactively make `S` implicit in that `def`, but it
  *does* for later ones — keep mask-style definitions above the implicit-variable switch or
  the arguments silently shift.
- `Finset.Nonempty.product` (not `Finset.product_nonempty`) builds nonemptiness of `×ˢ`.
- `Tendsto.congr'` + `filter_upwards [eventually_ge_atTop n]` is the clean way to make an
  *eventually*-local statement local: a fixed word only fits in the block for large `i`, and
  that is enough for a limit hypothesis.
- `Nat.mul_lt_mul_of_lt_of_le h (le_refl q) hq` for `a*q < b*q` from `a < b`, `0 < q`.
- `omega` finishes a nonlinear Nat contradiction if you first hand it the ring identity
  relating the two atom shapes (`2*(A*(c*q)) = 2*(A*c*q)`).
