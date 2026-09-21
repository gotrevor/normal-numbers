# HANDOFF 2026-09-21-0259 — radical CRT + Legendre sieve lap COMPLETE

Branch `proof/prime-model-complement`.  HEAD `ec781e1`.  Working tree clean apart
from this file.  Full `lake build` GREEN (9108 jobs, verified by the pre-commit
hook on both proof commits).  Treadmill stop requested by the host; this is the
checkpoint.

## Commits this lap

* `dd7e47e` — `PrimeModelRadicalCRT.lean`: exact assigned/sieve-prime CRT count,
  class count discharged.
* `719d036` — `PENDING_WORK.md`: the advance and the two-sided-sieve crux.
* `ec781e1` — `PrimeModelRadicalCRT.lean`: the Legendre sieve on top of it.

## What is proved

New file `src/NormalNumbers/PrimeModelRadicalCRT.lean` (imported from
`src/NormalNumbers.lean` line 389), namespace `NormalNumbers.PrimeModel.Radical`.
**No `sorry`, no `axiom`, no linter warnings.**  `#print axioms` on every headline
result is `[propext, Classical.choice, Quot.sound]` — in particular no
`native_decide`: the numeric anchors are kernel `decide`.

### Layer 1 — the kickoff target (`KICKOFF-radical-crt.md`, PRIMARY)

`SieveCond k A E Q r j n` := `n % Q = r` ∧ `∀ p ∈ A, p ∣ n+(j p)+1`
∧ `∀ p ∈ E, ∃ t : Fin k, p ∣ n+t+1`.

`radical_sieve_count` — for `A`, `E` disjoint sets of primes all `> k`, `Q > 0`
coprime to every prime of `A ∪ E`, `r < Q`, `j : ℕ → Fin k`, any `X`:

    | #{n < X : SieveCond} − X·ρ / (Q·D·e) |  ≤  ρ,
    D = ∏_{p∈A} p,   e = ∏_{p∈E} p,   ρ = k^{#E}.

`X = 0`, `A = ∅`, `E = ∅` all admitted.  The class count is **discharged, not
hypothesised**: `radical_sieve_admissible_card` proves
`#{c < Q·D·e : SieveCond c} = k^{#E}`.

Supporting, independently reusable:

* `card_filter_shift` — for `m > 0`, `S ⊆ range m`: exactly `#S` residues `c < m`
  satisfy `∃ t ∈ S, m ∣ c+t+1`.  Bijection `c ↦ m−1−c`; the exactness comes from
  `m ∣ c+t+1` with `c,t < m` forcing `c+t+1 = m` on the nose.  Specialises to
  `card_assigned` (count `1`) and `card_sieve` (count `k`, needs `k < p` so the
  `k` negative shifts are distinct mod `p`).
* `sum_range_prod_eq_prod_sum` — multi-modulus CRT sum factorisation
  `∑_{b<∏ p i} ∏ h i b = ∏ ∑_{b<p i} h i b`, by induction on the index set over
  the existing `G4.sum_range_mul_eq_mul_sum`.  (Sum analogue of
  `G4.resMean_prod`, without the `p⁻¹` factors.)
* `card_filter_range_prod` — CRT class count
  `#{n < ∏ m i : ∀ i, B i (n % m i)} = ∏ #{c < m i : B i c}` for pairwise-coprime
  positive `m i`; proved by running the ℂ-valued indicator
  `if B i (n % m i) then 1 else 0` through the above and casting back
  (`Finset.prod_boole`).
* `abs_card_filter_periodic_sub_le` — generic transfer: for an `M`-periodic
  predicate, `| #{n<X : P n} − #classes·X/M | ≤ #classes`; `biUnion` over classes
  plus `G4.abs_card_filter_modEq_sub_le`.

Index bookkeeping: `T = insert 0 (A ∪ E)`, `locMod Q i = if i = 0 then Q else i`,
`locCond` the matching local predicate, bridged by `sieveCond_iff`
(`dvd_mod_add_succ_iff`).

### Layer 2 — the Legendre sieve (beyond the kickoff)

`SiftedCond k A P Q r j n` := `n % Q = r` ∧ `∀ p ∈ A, p ∣ n+(j p)+1`
∧ `∀ p ∈ P, ∀ t : Fin k, ¬ p ∣ n+t+1` — **no** sieve prime divides any shift.

* `legendre_identity` — exact inclusion–exclusion, no error term:
  `∑_{E ⊆ P} (−1)^{#E} · #{n<X : SieveCond E} = #{n<X : SiftedCond}`.
  Structural move: swap the sums, and for fixed `n` collapse onto the hit set
  `hitSet k P n = P.filter (fun p => ∃ t, p ∣ n+t+1)` —
  `SieveCond E n ↔ base n ∧ E ⊆ hitSet n` and
  `SiftedCond n ↔ base n ∧ hitSet n = ∅` — so the inner sum is exactly
  `Finset.sum_powerset_neg_one_pow_card`.
* `legendre_sieve_count` —

      | #{n < X : SiftedCond} − X/(Q·D) · ∏_{p∈P} (1 − k/p) |  ≤  (1+k)^{#P}.

  Both halves fall out of the *same* mathlib identity `Finset.prod_one_add`:
  with `f p = −k/p` it telescopes the signed main terms into the Euler product
  (`legendre_main_term`), with `f p = k` it sums the per-subset errors `k^{#E}`
  to `(1+k)^{#P}` (`sum_powerset_pow_card`).

### Numeric anchors (kernel `decide`, in the file)

`k=2, Q=2, r=0, A={3}, j≡0, E={5}`: the admissible classes mod `30` are exactly
`{8,14}`; `X=20` count `2`; `X=9` count `1`.  `A={3}, E=∅, X=20` count `3`.
`A=∅, E={3,5}, X=20` count `3`.  Sifted: `A={3}, P={5}, X=20` count `1`
(main term `20/6 · 3/5 = 2`, bound `3`).

## THE CRUX, still open — exact next steps

`legendre_sieve_count` is the **untruncated** Legendre sieve: the error
`(1+k)^{#P}` is unconditional but swamps the main term as soon as `#P` is large.
That is the classical defect of Legendre's sieve, and the **two-sided
fundamental lemma** (usable upper *and* lower bounds for the sifted count) is
still OPEN.  This lap narrowed it to two separable, named pieces; every
per-subset term Brun's truncation consumes is already `radical_sieve_count`
verbatim.

**Next lap, step 1 (pure `Finset`/binomial combinatorics, no analysis):** the
**Bonferroni inequalities** — a truncated `Finset.sum_powerset_neg_one_pow_card`.
For `S : Finset ℕ` and a cut `h`,

    ∑_{E ⊆ S, #E ≤ 2h} (−1)^{#E}  ∈ [0, 1],    and it is  ≥  [S = ∅]
    ∑_{E ⊆ S, #E ≤ 2h+1} (−1)^{#E} ≤ [S = ∅],

with the sign of the truncation error fixed by the parity of the cut.  Route:
`Finset.sum_powerset_apply_card` reduces the inner sum to
`∑_{i ≤ 2h} (−1)^i C(#S, i)`, and the partial alternating binomial sums have the
closed form `(−1)^m C(#S − 1, m)` — see `Int.alternating_sum_range_choose` for
the full sum and prove the partial version by induction on the cut.  This is the
lemma that converts the exact identity into the one-sided bounds.

**Next lap, step 2:** the tail estimate
`∑_{E ⊆ P, #E = 2h+1} k^{#E} = C(#P, 2h+1) · k^{2h+1} ≤ (k log z)^{2h}/(2h)!`
for `P` the primes `≤ z`, replacing `(1+k)^{#P}`.  Needs a crude
`#{p ≤ z} ≤ ...` / `∑_{p ≤ z} log p` bound — note
`PrimeModelRadicalMoment.mertens_crude` (`∑_{p≤N} log p / p ≤ 4 log N`, proved
from the primorial bound) is already in the repo and `PrimeNumberTheoremAnd` is
**not** a dependency of this project.

**Then:** assemble `#{n<X : SiftedCond} ≥ X/(Q D) ∏_{p∈P}(1 − k/p) · (1 − o(1))`
and feed it to the radical-tuple layer.  The assigned primes `A` need no
exclusion (prescribed shift ⇒ single residue class ⇒ exact factor `1/p`), which
is why `A` enters as `1/D` and only `P` carries the `1 − k/p` Euler factors.

Also still open elsewhere (untouched, designated-open): `exists_good` (needs the
PNT error term — see `PENDING_WORK.md`, do **not** chase elementary Mertens),
`RoughIndependenceAt h 2` and `ParityDiscrepancy h` on the G₄ window law.

## Lean gotchas worth keeping

* `rw` on a `locCond`-style `Prop`-valued function equality breaks the
  `Finset.filter` `DecidablePred` instance argument.  Use
  `Finset.filter_congr (q := …) (fun c _ => by simp [..])` instead.
* `rw [← h]` where `h`'s RHS is a bare variable (`k`) rewrites *every* `k` in the
  goal, including inside the filter predicate.  Rewrite the predicate first, then
  the cardinality.
* `rw` of an `Iff` through an `if` whose `Decidable` instance mentions the
  rewritten proposition fails with "motive is not type correct".  `by_cases` on
  the condition first, then `if_pos` / `if_neg`.
* `Finset.subset_iff` and `Finset.filter_eq_empty_iff` bind the element
  *strict-implicitly*; `fun hp => …` silently binds the element, not the
  membership proof.  Use `intro p hp`.
