# HANDOFF 2026-09-21 — finite radical model lap COMPLETE

Branch: `proof/prime-model-complement`
HEAD: `ed3248a` — PrimeModelRadical: moment identity in exponential form
Prior: `e7f4d40` — PrimeModelRadical: the finite radical model layer proved
Build: full `lake build` GREEN (pre-commit hook, 9105 jobs), both commits.

Scope: `KICKOFF-prime-model-radical.md` only. **Complete.** `box done --green`
signalled (sentinel written; host verifies green). DIRECTION.md says "No active
override"; its live crux `RoughIndependenceAt h 2` was deliberately NOT touched.

## Delivered

`src/NormalNumbers/PrimeModelRadical.lean`, namespace
`NormalNumbers.PrimeModel.Radical`, imported from `src/NormalNumbers.lean`.
No `sorry`, no `axiom`, no frozen statement touched (pure addition).
`#print axioms` on every headline result: `propext, Classical.choice, Quot.sound`.

Model: site index a `Fintype ι`; state space `Option (Fin k)` per site with
`some j ↦ q` (mass `1/p`; **all higher valuations merged into this state** — a
model change, NOT squarefree truncation) and `none ↦ 1 - k·q`; sites independent,
so `weight k q s = ∏ᵢ localWeight k (q i) (s i)`. Probability law exactly when
`k·q ≤ 1`, i.e. every prime `p > k` of the window.

All five briefed results, for abstract reciprocals `q : ι → ℝ` and re-exposed in
prime form via `primeRecip p = (p : ℝ)⁻¹`:

1. `localWeight_nonneg` (`0 ≤ q`, `k*q ≤ 1`), `localWeight_sum`.
2. `radical_weight_nonneg`, **`radical_mass_one`** (+ `_prime`,
   `radical_weight_nonneg_prime` with `0 < p`, `k ≤ p`).
3. `localPhase_expectation` : `∑_a w a · φ a = 1 + q ∑_j (z j - 1)`.
4. **`radical_phase_product`** (+ `radical_phase_product_prime`:
   `∏_p (1 + (∑_j (z_{p,j}-1))/p)`).
5. **`radical_site_moment`** (fixed shift `j₀`): `∏_p (1 + q_p (t_p - 1))`
   (+ `radical_site_moment_prime`: `∏_p (1 + (t_p-1)/p)`), plus
   `radical_mult_product` (arbitrary per-site/per-shift real multipliers) and
   `radical_site_moment_uniform` (`∏_p (1 + k q_p (t_p - 1))`).

Extra: `radical_site_moment_le_exp` — for `0 ≤ q_p`, `1 ≤ t_p`, the moment is
`≤ exp (∑_p q_p (t_p - 1))`; the first step of the `d_j^α` bridge.

Structure: one structural lemma `sum_pi_prod`
(`∑_{s : ι → Option (Fin k)} ∏_i g i (s i) = ∏_i ∑_a g i a`, via
`Finset.prod_univ_sum` + `Fintype.piFinset_univ`) plus a three-term
`Fintype.sum_option` local computation. Nothing else is needed.

Numeric anchors (in-file, **independent** of the identities — state space
expanded by hand through `Fin.consEquiv` / `Equiv.funUnique`), `k = 2`,
reciprocals `1/3, 1/5` (the instrument's primes 3, 5): one-site `4/3`, two-site
`8/5`, two-site total mass `1`, each paired with a `norm_num` evaluation of the
closed form. These guard the model *statement*, not just the algebra.

Docs: `papers/prime-model-radical.md` (model change; `d_j`/`D`/`μ(d)` bridge with
the assigned-`g=0` vs unassigned-`g=k/p` exclusion count giving
`main/(QD) = μ(d)/Q`; `α = 1/(2 log y)`, `y ≥ e²` recovering `exp(4√e)` and the
old `e^20` with no geometric series; residual obligation). `HANDOFF-radical.md`
carries the same plus the pin gotchas.

## Pin gotchas worth keeping (mathlib @ lean4 v4.33.1)

- `Fintype.sum_option` splits `Option (Fin k)` sums; afterwards `∑_{j:Fin k} c = k•c`
  needs `Finset.card_univ, Fintype.card_fin, nsmul_eq_mul` spelled out then `ring`
  (a bare `simp [mul_comm]` leaves `k*t - k = k*(t-1)` open).
- `Finset.sum_ite_eq'` will not fire on `(if j = j₀ then t else 1) - 1`; rewrite
  the summand to `if j = j₀ then t - 1 else 0` first.
- No `Equiv.piFinSucc` in this pin. Use
  `Fin.consEquiv (fun _ => α) : α × (Fin n → α) ≃ (Fin (n+1) → α)` with
  `Fintype.sum_prod_type`, then peel the residual `Fin 1 → α` sum with
  `Equiv.funUnique` *under* a `Finset.sum_congr` (a bare `rw` can't reach inside
  the outer binder).
- `Real.add_one_le_exp` is `x + 1 ≤ exp x`; `rw [add_comm]` first.
- `set_option linter.unusedSectionVars false` at file top: `[DecidableEq ι]` is
  required by `sum_pi_prod` but unused downstream.

## Exact next steps (for whoever picks this up)

1. **Nothing is open in this scope.** The module is sorry-free and axiom-clean;
   downstream consumers can use `radical_site_moment_prime` /
   `radical_site_moment_le_exp` directly.
2. If the `d_j^α ≤ exp(4√e)` bound is wanted *in Lean*, the two missing
   arithmetic inputs are: `p^α - 1 ≤ √e · α log p` for `α log p ≤ 1/2`
   (`Real.add_one_le_exp` + convexity on `[0,1/2]`), and Mertens
   `∑_{p≤y} log p / p ≤ 2 log y` (check `Nat.Prime`/Mertens API in this pin).
   Then compose with `radical_site_moment_le_exp` at `t p = p^α`.
3. **Do NOT broaden into the sieve fundamental lemma.** Mathlib's `SelbergSieve`
   is upper-bound machinery only; the Rosser–Iwaniec two-sided version with
   `1 + O(e^{-s})` error is absent and is a separate campaign needing its own
   kickoff. The radical model removes the *valuation-tail* obligation
   (`PrimeModelComplement.lean` covered the old one), not this one.
4. The inherited G4 work (`RoughIndependenceAt h 2`, `ParityDiscrepancy`) on other
   branches is untouched by this lap and remains the repo's real crux.
