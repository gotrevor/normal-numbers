# Handoff: 2026-09-22 — radical state identification + retained count (KICKOFF discharged)

**Branch**: `wip/g5-prime-subset` · Build: `lake build` green (9117 jobs) · 0 `sorry` in the new module.

`KICKOFF-radical-state-count.md` is discharged.  New module
`src/NormalNumbers/PrimeModelRadicalState.lean` (namespace
`NormalNumbers.PrimeModel.RadicalState`), imported from `src/NormalNumbers.lean`.
No frozen module was edited; no new dependency, no analytic hypothesis.

`#print axioms` on all three targets: `[propext, Classical.choice, Quot.sound]`
(the audit lines live at the bottom of the module).

## Targets, with exact hypotheses

### 1. `retainedBox_card_le`

```
theorem retainedBox_card_le {ι} [Fintype ι] [DecidableEq ι] {p : ι → ℕ}
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) (k : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    ((Radical.retainedBox k p T).card : ℝ) ≤ (Nat.floor T : ℝ) ^ k
```

Uses the EXISTING `Radical.retainedBox` / `Radical.radSize`.  Route:

* `natRadSize p j s = ∏ i, (if s i = some j then p i else 1) : ℕ`, with
  `natRadSize_cast : (natRadSize p j s : ℝ) = radSize p j s`.
* `prime_dvd_natRadSize` : `p i ∣ natRadSize p j s ↔ s i = some j` — the unique-factorisation
  step (`Prime.dvd_finsetProd_iff` + `Nat.prime_dvd_prime_iff_eq` + injectivity of `p`).
* `natRadTuple_injective` : `s ↦ (j ↦ natRadSize p j s)` is injective.  Handles `none` states
  and `k = 0` uniformly (for `k = 0` the state type is a subsingleton and the bound reads `≤ 1`).
* Image lands in `Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 ⌊T⌋₊)`, of card `⌊T⌋₊ ^ k`.

The bound is independent of `#ι` — this is what the tail estimate needs; the trivial
`(k+1)^{#ι}` is useless.  `hT` is only carried for the intended use (`⌊T⌋₊ ≥ 1`).

### 2. `actual_state_sifted_iff`

```
theorem actual_state_sifted_iff {k} {P : Finset ℕ} {s : {q // q ∈ P} → Option (Fin k)}
    (hk : 0 < k) (hP : ∀ q ∈ P, k < q) (Q r n : ℕ) :
    (n % Q = r ∧ actualState k P n = s)
      ↔ Radical.SiftedCond k (stateA P s) (stateU P s) Q r (stateShift P s hk) n
```

* `hitShift k q n : Option (Fin k)` — `some t` for the (proved) unique `t < k` with
  `q ∣ n + t + 1`, else `none`.  Computable (`Fin.find`), so the `decide` anchors work.
* `hit_unique (hq : k < q)` — uniqueness is PROVED (difference of two hits is `< q` and
  divisible by `q`), not assumed.  This is the only place `hP` is used.
* `actualState k P n : {q // q ∈ P} → Option (Fin k) := fun i => hitShift k i n`.
* `stateA P s` = assigned primes, `stateU P s` = unassigned; helpers proved:
  `mem_stateA`, `mem_stateU`, `stateA_subset`, `stateU_subset`, `stateA_disjoint_stateU`,
  `stateU_eq_sdiff : stateU P s = P \ stateA P s`, `stateA_union_stateU`.
* `stateShift P s hk q` = the assigned shift at `q ∈ P`, default `⟨0, hk⟩` elsewhere.

Shift convention is `n + t + 1` throughout, matching `Radical.SiftedCond` and the CRT theorem.
Permanent `decide` anchors at the bottom of the module (`P = {3,5}`, `k = 2`):
`hitShift 2 3 0 = none`, `hitShift 2 5 0 = none`, `hitShift 2 3 1 = some 1`,
`hitShift 2 3 2 = some 0`, `hitShift 2 5 3 = some 1` — these catch an `n+t` vs `n+t+1` slip.

### 3. `state_model_density`

```
theorem state_model_density {k} {P : Finset ℕ} {s : {q // q ∈ P} → Option (Fin k)} :
    Radical.weight k (Radical.primeRecip (fun i : {q // q ∈ P} => (i : ℕ))) s
      = (1 / ∏ q ∈ stateA P s, (q : ℝ)) * ∏ q ∈ stateU P s, (1 - (k : ℝ) / q)
```

Same `A = stateA P s`, `U = stateU P s`, `s` as the predicate equivalence, so the model weight of
a state is exactly the main-term density of the sifted condition it is identified with.
Route: split `P.attach` by `(s i).isSome` (`Finset.prod_filter_mul_prod_filter_not`), then
`Finset.prod_image` along the injective `Subtype.val`.

## What this buys, and the remaining application work

Composing 2 + 3 with `Radical.radical_sieve_count` / `BrunCount.brun_sifted_count_lower` gives,
for each state `s`, a count of `n < X` realising `s` with main term `X · weight(s) / Q` — i.e.
the empirical joint law converges to `jointModel` state-by-state.  Not yet formalised:

1. **Per-state count**: instantiate the CRT/Brun counting theorems at `A = stateA P s`,
   `U = stateU P s`, `j = stateShift P s hk` and rewrite the main term with
   `state_model_density`.  Needs `Q` coprime to `∏ P`, `r < Q` — the hypotheses already carried
   by `radical_sieve_count`.
2. **Summation over states**: sum (1) over `s` in the retained box; `retainedBox_card_le`
   bounds the number of error terms by `⌊T⌋₊ ^ k`, which is what makes the accumulated
   remainder `⌊T⌋₊^k · (error per state)` usable.
3. **Optional task not done**: the normalised empirical joint law on `Fin Q × (P → Option (Fin k))`
   with mass 1.  It is a routine `Finset.card_eq_sum_ones` / partition argument on top of
   `actual_state_sifted_iff`; deliberately not substituted for any main target.

Nothing in flight; no Aristotle job open.
