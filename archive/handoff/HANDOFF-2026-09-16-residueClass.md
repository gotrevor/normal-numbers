# HANDOFF 2026-09-16 — campaign A COMPLETE: `isDisjunctive_residueClass`, unconditional

Branch `wip/g5-prime-subset`, `lake build` green (9053 jobs), working tree clean.
**Every headline below prints `[propext, Classical.choice, Quot.sound]`.**

## The headline

```lean
theorem isDisjunctive_residueClass_primeSum {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    {b : ℕ} (hb : 3 ≤ b) :
    IsDisjunctive b (∑' p : ℕ, if p.Prime ∧ (p : ZMod q) = a then 1 / ((b : ℝ) ^ p - 1) else 0)
```

i.e. **`∑_{p ≡ a (mod q)} 1/(b^p − 1)` is disjunctive in every base `b ≥ 3`**, for every unit
`a` mod `q` — the exact instance named in the 2026-09-15 23:58 operator override.  Equivalent
weight form: `isDisjunctive_residueClass` on `c_S(b) = ∑_n ω_S(n)/bⁿ`.

General form (any prime set with a Mertens rate):

```lean
theorem isDisjunctive_subsetLambert (S : ℕ → Prop) [DecidablePred S] {c C : ℝ}
    (hmert : MertensAP.MertensRate S c C) {b : ℕ} (hb : 3 ≤ b) :
    IsDisjunctive b (subsetLambert S b)
```

Sanity instance: `isDisjunctive_subsetLambert_univ` re-derives `isDisjunctive_base`'s statement
from the `S`-route via `mertensRate_univ` (`MertensRate (fun _ => True) 1 1` from `G4Mertens`).

## How the two free parameters absorb the `S`-loss

The design finding stands: **bare divergence of `∑_{p∈S} 1/p` is not enough for this route; a
*rate* is, and any fixed `c > 0` suffices.**  Two parameters were freed this session:

1. **cutoff exponent `e`** (`SchedB.HypE b K e = Hyp b K + m₁ b K ≤ e + 10⁵·T K·e ≤ 2^{m₂ K}`).
   `G4SchedBE` re-proves the whole parameter layer and all six budget terms at a free `e`, and
   — the structural point — `hbudget_holdsE_gen` states the budget over an **arbitrary
   sub-family `sm` of the small primes**: terms (a),(d) need only `sm.card ≤ RE e + 1`, terms
   (b),(c) only `∑_{p∈sm} 1/p ≤ 3e+5`, and the gain term is the single place the family matters,
   taken as the hypothesis `hlow`.  No new analytic estimate is needed for `S`.
2. **outer dimension `K = 4k₄`** (`SchedB.hyp_KG`, `SchedB.KG_ge`, `SchedB.MG`): the witness no
   longer hard-codes `k₄ = k₄bℓ b ℓ`, only `k₄bℓ b ℓ ≤ k₄`.  This is what makes the moment cap
   reachable: the Mertens loss inflates the cutoff by a constant `Dc ≈ 1/(c log 2)`, and
   `Dc ≤ 2^K` is bought by taking `k₄ = max (k₄bℓ b ℓ) Dc`.

The one input that is NOT monotone in the cutoff is the far-tail size fact; it is
`SchedB.four_mul_le_two_pow_NE`, and the moment cap (`e ≤ 2^{8K²}` vs `N K = 100K²`) is exactly
what discharges it.

## Modules added this session

* `G4SchedBE.lean` (extended) — `term_b_leE`, `term_c_leE`, and `_gen` versions of all five
  `smallPrimeBound` terms; `hbudget_holdsE_gen` / `hbudget_holdsE`.
* `G4SchedBEAssembly.lean` (new) — `sample_ratio_leE`, `four_mul_le_two_pow_half`,
  `four_mul_le_two_pow_NE`, `hbig_holdsE`, `hfar_holdsE`; the `k₄`-free layer `MG`/`MG_lo`/
  `MG_hi`/`hM_holdsG`/`KG_ge`/`hyp_KG`; **`scheduleWitnessSE`**.
* `G4SubsetAssembly.lean` (new) — `smallPrimes_mono`, `exists_scheduleWitnessS`,
  **`isDisjunctive_subsetLambert`**, `mertensRate_univ`, `isDisjunctive_subsetLambert_univ`,
  **`isDisjunctive_residueClass`**, **`isDisjunctive_residueClass_primeSum`**.

## Open in `src/`

Exactly the two pre-expedition, forbidden-drift `sorry`s (`phaseOscillation`,
`exists_prime_nonresidue`).  Zero `axiom`s.

## Resume here

Campaign A items 0–3 of the override are done.  Item 4 is next: G5 steps 2–5 for `weightW c`
(`PENDING_WORK.md` §"Next actions", 2026-09-14) — transport for `w_c`, junk via `sum_junk_le`,
`isDisjunctive_Omega`.
