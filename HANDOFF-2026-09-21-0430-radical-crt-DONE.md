# HANDOFF — exact assigned/sieve-prime CRT counting COMPLETE

Branch `proof/prime-model-complement`.  Full `lake build` GREEN (9108 jobs).
`KICKOFF-radical-crt.md` PRIMARY done, plus the optional scope note.

## Delivered

`src/NormalNumbers/PrimeModelRadicalCRT.lean` (new, imported from
`src/NormalNumbers.lean`), namespace `NormalNumbers.PrimeModel.Radical`.
No `sorry`, no `axiom`; `#print axioms` on every headline result is
`[propext, Classical.choice, Quot.sound]` (no `native_decide` — the numeric
anchors are kernel `decide`).

PRIMARY `radical_sieve_count`: for `A`, `E` disjoint sets of primes all `> k`,
`Q > 0` coprime to every prime of `A ∪ E`, `r < Q`, shift `j : ℕ → Fin k`,

    | #{n < X : SieveCond} − X·ρ / (Q·D·e) |  ≤  ρ,
    D = ∏_{p∈A} p,  e = ∏_{p∈E} p,  ρ = k^{#E}.

`SieveCond k A E Q r j n` = `n % Q = r` ∧ `∀ p ∈ A, p ∣ n+(j p)+1`
∧ `∀ p ∈ E, ∃ t : Fin k, p ∣ n+t+1`.  `X = 0`, `A = ∅`, `E = ∅` all allowed.

The class count is **discharged, not hypothesised**:
`radical_sieve_admissible_card` proves `#{c < Q·D·e : SieveCond c} = k^{#E}`.

## Supporting layer (independently reusable)

* `card_filter_shift` — for `m > 0`, `S ⊆ range m`: exactly `#S` residues
  `c < m` satisfy `∃ t ∈ S, m ∣ c+t+1`.  Bijection `c ↦ m−1−c`; the key step is
  that `m ∣ c+t+1` with `c,t < m` forces `c+t+1 = m` exactly.  Gives the
  assigned-prime count `1` (`card_assigned`) and the sieve-prime count `k`
  (`card_sieve`, needs `k < p` so the `k` negative shifts are distinct mod `p`).
* `sum_range_prod_eq_prod_sum` — multi-modulus CRT factorisation
  `∑_{b<∏p i} ∏ h i b = ∏ ∑_{b<p i} h i b`, by induction on the index set on
  top of `G4.sum_range_mul_eq_mul_sum` (the sum analogue of `G4.resMean_prod`,
  without the `p⁻¹` factors).
* `card_filter_range_prod` — CRT class count: `#{n < ∏ m i : ∀ i, B i (n % m i)}
  = ∏ #{c < m i : B i c}` for pairwise-coprime positive `m i`.  Proved by
  running the ℂ-valued indicator `if B i (n % m i) then 1 else 0` through
  `sum_range_prod_eq_prod_sum` and casting back (`Finset.prod_boole`).
* `abs_card_filter_periodic_sub_le` — generic transfer: for an `M`-periodic
  predicate, `| #{n<X : P n} − #classes·X/M | ≤ #classes`.  `biUnion` over
  classes + `G4.abs_card_filter_modEq_sub_le` per class.

Index bookkeeping: `T = insert 0 (A ∪ E)` with `locMod Q i = if i = 0 then Q
else i` and `locCond` the matching local predicate; `sieveCond_iff` is the
`SieveCond ↔ ∀ i ∈ T, locCond i (n % locMod i)` bridge (`dvd_mod_add_succ_iff`).

## Anchors in Lean (kernel `decide`)

`k=2,Q=2,r=0,A={3},j≡0,E={5}`: classes mod 30 are exactly `{8,14}`; `X=20`
count 2; `X=9` count 1.  `A={3},E=∅,X=20` count 3.  `A=∅,E={3,5},X=20` count 3.

## Remaining obligation (explicit)

This is a **one-sided local divisibility count**, not radical tuples.  The
two-sided fundamental lemma of the sieve — upper and lower bounds for the
sifted count with the error summed over all `E` in the sieve range — is NOT
proved.  The file's closing note records how `E` ranges over subsets of the
unassigned primes and why assigned primes need no exclusion.

## Lean gotchas worth keeping

* `rw` on a `locCond`-style `Prop`-valued function equality breaks the
  `Finset.filter` `DecidablePred` instance argument; use
  `Finset.filter_congr (q := …) (fun c _ => by simp [..])` instead.
* `rw [← h]` where `h`'s RHS is the bare variable `k` rewrites *every* `k` in
  the goal, including inside the filter.  Rewrite the predicate first, then the
  cardinality.
