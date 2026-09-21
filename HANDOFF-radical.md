# HANDOFF — finite radical model (2026-09-21)

Branch: `proof/prime-model-complement`.  Full `lake build` GREEN (9105 jobs).
Scope: `KICKOFF-prime-model-radical.md` only.  Done; nothing left open in it.

## Landed

`src/NormalNumbers/PrimeModelRadical.lean` (imported from `src/NormalNumbers.lean`),
namespace `NormalNumbers.PrimeModel.Radical`.  No `sorry`, no `axiom`, no frozen
target touched.  `#print axioms` on all five headline results:
`propext, Classical.choice, Quot.sound`.

All five briefed results, stated for abstract reciprocals `q : ι → ℝ` over a
`Fintype` site index and re-exposed for `q p = 1/p` (`primeRecip`):

1. `localWeight_nonneg` (needs `0 ≤ q`, `k*q ≤ 1`), `localWeight_sum`.
2. `radical_weight_nonneg`, **`radical_mass_one`** (+ `radical_mass_one_prime`).
3. `localPhase_expectation` : `∑_a w a * φ a = 1 + q * ∑_j (z j - 1)`.
4. **`radical_phase_product`** (+ `radical_phase_product_prime`, the `/p` form).
5. **`radical_site_moment`** : fixed shift `j₀`, `∏_p (1 + q_p (t_p - 1))`
   (+ `radical_site_moment_prime` = `∏_p (1 + (t_p-1)/p)`), plus
   `radical_mult_product` (general per-shift multipliers) and
   `radical_site_moment_uniform` (`∏_p (1 + k q_p (t_p-1))`).

Design: one structural lemma `sum_pi_prod`
(`∑_{s : ι → Option (Fin k)} ∏_i g i (s i) = ∏_i ∑_a g i a`) via
`Finset.prod_univ_sum` + `Fintype.piFinset_univ`; every identity is that plus a
`Fintype.sum_option` three-term local computation.  Merging all higher valuations
into `some j` (mass `1/p`, not `1/p - 1/p²`) is what makes the site space finite —
it is a model change, not a squarefree truncation.

Numeric anchors in-file (independent expansion of the state space via
`Fin.consEquiv` / `Equiv.funUnique`, `k=2`, reciprocals `1/3, 1/5`): one-site
`4/3`, two-site `8/5`, two-site total mass `1`, each paired with a `norm_num`
evaluation of the closed form.  These guard the model statement itself.

`papers/prime-model-radical.md` documents the model change, the `d_j`/`D`/`μ(d)`
bridge with the `g=0` vs `g=k/p` exclusion count, the `α = 1/(2 log y)` moment
bound recovering `exp(4√e)` (hence the old `e^20`) with no geometric series, and
the residual obligation.

## Gotchas worth keeping

- `Fintype.sum_option` is the right splitter for `Option (Fin k)`; after it,
  `∑_{j : Fin k} c = k • c` needs `Finset.card_univ, Fintype.card_fin, nsmul_eq_mul`
  spelled out, then `ring` (a bare `simp [mul_comm]` leaves `k*t - k = k*(t-1)`).
- `Finset.sum_ite_eq'` does not fire on `(if j = j₀ then t else 1) - 1`; rewrite
  the summand to `if j = j₀ then t - 1 else 0` first.
- There is no `Equiv.piFinSucc` in this pin; use
  `Fin.consEquiv (fun _ => α) : α × (Fin n → α) ≃ (Fin (n+1) → α)` with
  `Fintype.sum_prod_type`, and peel the residual `Fin 1 → α` sum with
  `Equiv.funUnique` under a `Finset.sum_congr`.
- `set_option linter.unusedSectionVars false` at file top: `[DecidableEq ι]` is
  needed by `sum_pi_prod` but unused in several downstream lemmas.

## Residual analytic obligation (explicitly out of scope, per kickoff)

The two-sided sieve fundamental lemma is NOT proved.  Mathlib's `SelbergSieve`
has upper-bound machinery only; the Rosser–Iwaniec lower bound with
`1 + O(e^{-s})` error is absent.  Do not broaden into it without a new kickoff.
