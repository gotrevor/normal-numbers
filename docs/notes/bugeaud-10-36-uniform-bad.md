# One ξ badly approximable to every base with a uniform exponent (Bugeaud, Problem 10.36)

[ Claude wrote this note at my direction.  The Lean files it links are the authority.  -Trevor ]

Write `‖t‖` for the distance from `t` to the nearest integer.  Bugeaud, *Distribution modulo one and Diophantine approximation* (Cambridge Tracts 193, 2012), p. 219:

> Problem 10.36.  There exist a real number `ξ` and a positive real number `c` such that `‖bⁿξ‖ > b^{−c}` for every base `b ≥ 2` and every integer `n ≥ 0` (resp., every integer `n` sufficiently large in terms of `b`).

The best result in the book is Theorem 7.8 (after Akhunzhanov), with the base-dependent bound `‖ξbⁿ‖ > b^{−1100 b log 3b}`.

This note records a proof with `c = 24`, checked in Lean at commit [`bdbe4fe`](https://github.com/gotrevor/normal-numbers/tree/bdbe4fe92ebd252073e177e7775459d841c6aed6).  It uses **no cited results**, and depends only on Lean's standard axioms.

## Statement

**Theorem.**  There is `ξ ∈ [1/4, 3/4]` with `‖bⁿξ‖ > b^{−24}` for every integer `b ≥ 2` and every `n ≥ 0`.

- [`exists_uniformBad_allBases_24`](https://github.com/gotrevor/normal-numbers/blob/bdbe4fe92ebd252073e177e7775459d841c6aed6/src/NormalNumbers/UniformBad.lean#L675), giving [`bugeaud_10_36`](https://github.com/gotrevor/normal-numbers/blob/bdbe4fe92ebd252073e177e7775459d841c6aed6/src/NormalNumbers/UniformBad.lean#L709) as posed, and the "resp." reading [`bugeaud_10_36_eventually`](https://github.com/gotrevor/normal-numbers/blob/bdbe4fe92ebd252073e177e7775459d841c6aed6/src/NormalNumbers/UniformBad.lean#L717).  Here `‖·‖` is [`dnear`](https://github.com/gotrevor/normal-numbers/blob/bdbe4fe92ebd252073e177e7775459d841c6aed6/src/NormalNumbers/UniformBad.lean#L101).

## How

A measure argument cannot work: for each base, the bad set at level `n` has measure about `2b^{−24}`, and there are infinitely many levels.  The proof is a nested-interval construction instead.

- **The engine.**  Consider a countable family of closed intervals ("obstacles"), each assigned to a stage.  Suppose a square-root potential of the obstacles in each stage is small enough.  Then some point avoids all of them ([`exists_avoid_of_stagePotential`](https://github.com/gotrevor/normal-numbers/blob/bdbe4fe92ebd252073e177e7775459d841c6aed6/src/NormalNumbers/UniformBad.lean#L342), one step: [`potential_step`](https://github.com/gotrevor/normal-numbers/blob/bdbe4fe92ebd252073e177e7775459d841c6aed6/src/NormalNumbers/UniformBad.lean#L192)).  At each step the construction keeps a sub-interval whose potential stays below a threshold, and the carried potential shrinks by a factor of 4 per step.
- **Early charging.**  The obstacle `{ξ : ‖bⁿξ‖ ≤ b^{−24}}` near `a/bⁿ` is charged at stage `k` where `64^{k−1} ≤ bⁿ < 64^k`.  At that stage each base contributes at most a few obstacles meeting any one window ([`encard_stage_meet_le`](https://github.com/gotrevor/normal-numbers/blob/bdbe4fe92ebd252073e177e7775459d841c6aed6/src/NormalNumbers/UniformBad.lean#L476)).  Each obstacle is still tiny compared with the window.  Summing over all bases converges, so the stage potential is at most `1/40` ([`newPotential_le`](https://github.com/gotrevor/normal-numbers/blob/bdbe4fe92ebd252073e177e7775459d841c6aed6/src/NormalNumbers/UniformBad.lean#L594)).

## Limits and controls

- **The exponent cannot be small.**  Base 2 alone rules out every `c ≤ log₂ 3`, since `‖ξ‖ ≤ 1/3` or `‖2ξ‖ ≤ 1/3` ([`not_uniformBad_of_third_le`](https://github.com/gotrevor/normal-numbers/blob/bdbe4fe92ebd252073e177e7775459d841c6aed6/src/NormalNumbers/UniformBad.lean#L760)).  So the best exponent lies in `[log₂ 3, 24]`.  Even after discarding finitely many bases, `c ≤ 1` fails, by Dirichlet ([`not_uniformBad_largeBases_of_le_one`](https://github.com/gotrevor/normal-numbers/blob/bdbe4fe92ebd252073e177e7775459d841c6aed6/src/NormalNumbers/UniformBad.lean#L846)).
- **Such ξ are far from normal.**  A witness is disjunctive to no base, and so normal to no base ([`not_isDisjunctive_of_uniformBad`](https://github.com/gotrevor/normal-numbers/blob/bdbe4fe92ebd252073e177e7775459d841c6aed6/src/NormalNumbers/UniformBad.lean#L862), [`not_isNormal_of_uniformBad`](https://github.com/gotrevor/normal-numbers/blob/bdbe4fe92ebd252073e177e7775459d841c6aed6/src/NormalNumbers/UniformBad.lean#L879)).
- The bound implies the book's (7.16) ([`bugeaud_7_16_of_uniformBad24`](https://github.com/gotrevor/normal-numbers/blob/bdbe4fe92ebd252073e177e7775459d841c6aed6/src/NormalNumbers/UniformBad.lean#L725)).

## How large is the set? (added 2026-10-04)

Let `E_C = {ξ : ‖bⁿξ‖ > b^{−C} for every b ≥ 2 and n ≥ 0}` ([`E`](https://github.com/gotrevor/normal-numbers/blob/bfca568d588bab19a168a46dfe65e50a0d4f5668/src/NormalNumbers/SchmidtGames.lean#L215)) and `U = ⋃_C E_C` ([`U`](https://github.com/gotrevor/normal-numbers/blob/bfca568d588bab19a168a46dfe65e50a0d4f5668/src/NormalNumbers/SchmidtGames.lean#L219)).  Using the potential games of Broderick–Fishman–Simmons ([arXiv:1703.09015](https://arxiv.org/abs/1703.09015), Acta Arith. 188 (2019)), stated as hypotheses, these results hold (links at commit [`bfca568`](https://github.com/gotrevor/normal-numbers/tree/bfca568d588bab19a168a46dfe65e50a0d4f5668)):

- `1 − dim_H E_C ≍ 2^{−C}`: all bases together cost, up to a constant factor, what base 2 alone costs ([`codim_E_asymp`](https://github.com/gotrevor/normal-numbers/blob/bfca568d588bab19a168a46dfe65e50a0d4f5668/src/NormalNumbers/SchmidtGames.lean#L1062)).  The lower bound comes from `E_C` being potential winning ([`potentialWinning_E`](https://github.com/gotrevor/normal-numbers/blob/bfca568d588bab19a168a46dfe65e50a0d4f5668/src/NormalNumbers/SchmidtGames.lean#L521)), with the nested-interval construction above as the strategy; the upper bound is a run-length count in base 2 ([`dimH_E₂_le`](https://github.com/gotrevor/normal-numbers/blob/bfca568d588bab19a168a46dfe65e50a0d4f5668/src/NormalNumbers/SchmidtGames.lean#L923)).
- `dim_H U = 1` ([`dimH_U_eq_one_of`](https://github.com/gotrevor/normal-numbers/blob/bfca568d588bab19a168a46dfe65e50a0d4f5668/src/NormalNumbers/SchmidtGames.lean#L1094)).
- In the middle-third Cantor set `K`: `dim_H(U ∩ K) ≥ log 2 / log 3` ([`le_dimH_U_inter_cantor_of`](https://github.com/gotrevor/normal-numbers/blob/bfca568d588bab19a168a46dfe65e50a0d4f5668/src/NormalNumbers/SchmidtGames.lean#L1105)), and the same with the badly approximable numbers intersected in ([`le_dimH_U_inter_Bad_inter_cantor_of`](https://github.com/gotrevor/normal-numbers/blob/bfca568d588bab19a168a46dfe65e50a0d4f5668/src/NormalNumbers/SchmidtGames.lean#L1145)).
- Guards: for a fixed `C` the set is not winning at small `α`, so the union over `C` is needed ([`not_potentialWinning_E_small`](https://github.com/gotrevor/normal-numbers/blob/bfca568d588bab19a168a46dfe65e50a0d4f5668/src/NormalNumbers/SchmidtGames.lean#L1167)); and the normal numbers are not potential winning ([`not_potentialWinning_isNormal`](https://github.com/gotrevor/normal-numbers/blob/bfca568d588bab19a168a46dfe65e50a0d4f5668/src/NormalNumbers/SchmidtGames.lean#L1197)).

The cited inputs are BFS Theorem 5.5 ([`Literature.BFSPotentialDim`](https://github.com/gotrevor/normal-numbers/blob/bfca568d588bab19a168a46dfe65e50a0d4f5668/src/NormalNumbers/SchmidtGames.lean#L260), restricted to starting scales `ρ ≤ 1` as in their §2; without that restriction the transcription is false, and that is proved in the same file) and BFS Lemma 3.11 (Lemma 3.10 on arXiv) with Remark 4.2 and Proposition 4.5 ([`Literature.BFSBadPotential`](https://github.com/gotrevor/normal-numbers/blob/bfca568d588bab19a168a46dfe65e50a0d4f5668/src/NormalNumbers/SchmidtGames.lean#L290)).

**Status.**  We did not find these dimension statements in print, but they follow closely from BFS: a per-base version of their Lemma 3.11, their Proposition 4.4 with `Σ_b b^{−C/2} < ∞`, then Theorem 5.5.  An expert may well regard them as an exercise.

## Prior work and what is not claimed

- The method is standard in spirit (Schmidt games, potential games).  We did not find a uniform `b^{−c}` bound for all bases stated anywhere.  Known bounds are base-dependent: Akhunzhanov `exp(−5000 b log² b)`, and Broderick–Bugeaud–Fishman–Kleinbock–Weiss (2010) `exp(−κ b log² b)`.  Peres–Schlag (2010) and Moshchevitin handle lacunary sequences, which `{bⁿ : b ≥ 2, n ≥ 0}` is not.
- Falconer–Yavicoli, *Intersections of thick compact sets in ℝᵈ*, Math. Z. 301 (2022) ([arXiv:2102.01186](https://arxiv.org/abs/2102.01186)), would give the result from a thickness bound `τ(E_b(C)) ≳ b^C` for the sets `E_b(C) = {ξ : ‖bⁿξ‖ ≥ b^{−C} ∀n}`.  We did not find that bound proved.  Experts may regard the statement as an exercise.  What is offered here is a complete written proof with an explicit exponent.
- No optimisation of `24`.  Priority beyond our search; corrections are welcome.

## Checking it

```sh
git clone https://github.com/gotrevor/normal-numbers && cd normal-numbers
git checkout bdbe4fe92ebd252073e177e7775459d841c6aed6
lake exe cache get
lake build NormalNumbers.UniformBad
```

Questions and corrections: please open an issue on this repository.
