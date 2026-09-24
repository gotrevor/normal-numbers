# HANDOFF — abelian normality in base two (KICKOFF-2026-09-23-abelian-normal.md)

**Status: DONE.**  `src/NormalNumbers/AbelianNormal.lean` is sorry-free; all four ratified
statements are axiom-clean (`propext, Classical.choice, Quot.sound` only — no `native_decide`).
Statements, definitions and binders are unchanged from the seed.

## What landed

New file `src/NormalNumbers/AbelianKrawtchouk.lean`:
* `kraw L j w := [X^j] ((1-X)^w (1+X)^(L-w))` in `ℝ[X]`.
* `sum_powersetCard_neg_one_pow`: for `W ⊆ range L`,
  `∑_{|S|=j, S ⊆ range L} (-1)^|S∩W| = kraw L j |W|`.
  **Route note:** the "symmetrized character sum depends on the window only through its weight"
  step needs *no* combinatorial bijection — `Finset.prod_add` applied to
  `∏_{i<L} (1 + ε_i X)` in `ℝ[X]`, then read off coefficient `j`.  This was the key
  simplification of the lap; the explicit Krawtchouk sum `∑_i (-1)^i C(w,i) C(L-w,j-i)`
  suggested by the kickoff is never needed.
* `sum_powerset_orth` (cube orthogonality via `symmDiff`, on top of Walsh's
  `sum_neg_one_pow_inter_eq_zero`), `sum_kraw_mul_choose` (mean zero for `j ≥ 1`),
  `sum_kraw_mul_sum` (inversion: `∑_j kraw L w j · (j-th symmetrized sum) = 2^L · 1[|W| = w]`).

In `AbelianNormal.lean`:
* `symParityMean_eq` (forward transform) and `onesFreq_eq` (inverse transform) — exact at
  every finite `N`, mirroring `Walsh.blockMean_eq`.  Both directions of the headline are then
  a finite linear combination of limits; the `j = 0` column is `symParityMean s L 0 N = 1`.
* `sum_fun_cons` / `sum_fun3` / `sum_fun4`: sums over `Fin n → Fin 2` split by first letter via
  `Fin.consEquiv`.  Needed because `decide` gets stuck on `Fintype.piFinset`
  (`Multiset.Pi.cons` does not kernel-reduce) — that is the reason `separation_four` is not a
  one-line `decide`.
* `separation_four` witness: `sepWord w = 1/16` if `w 1 = w 2`, else `2/16`/`0` by the parity of
  `w 0 + w 1 + w 3`.  (Equivalent to the kickoff's ±1 word list; the parity form is what makes
  `norm_num +decide` close all 15 abelian equations.)
* `rigid_three`: 10 abelian + 4 stationarity equations, `linarith`.  Watch `fin_cases`
  producing `⟨0, ⋯⟩` rather than `0` — `simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]`
  before `linarith` is what matches the atoms.

## Solution-space probe (independent of Lean, `experiments/`-style check re-run this lap)

Rank of (stationarity + abelian balance at all `k ≤ L`) on `2^L` unknowns: nullspace dimension
0 at `L = 3`, 1 at `L = 4`, 5 at `L = 5`.  Matches the seed comment.
