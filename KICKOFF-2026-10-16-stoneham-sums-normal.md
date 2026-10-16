# Kickoff 2026-10-16: Stoneham sums are normal (Theorem A)

Branch `proof/stoneham-sums-normal`, worktree `~/src/nn-stoneham-sums`.  Target file
`src/NormalNumbers/StonehamSumsNormal.lean`: three ratified, sorried statements.  Prove them
**without changing any statement**.  The only allowed cited input is the existing
`Literature.VandeheyDiff.VandeheyThm51`, taken as a hypothesis exactly as the statements do.

## The proof

`papers/2026-10-16-stoneham-sums-normal.md` is the paper proof (refereed, repairs applied).  Follow
its structure:

1. **`vandeheyCor12_of_thm51`**: Vandehey §6.1.  For `N ≥ m` use the `k = 0` case of
   `VandeheyThm51` (`(m^{1/2} + M m^{-1/2} N)(1 + log m)`, so a power saving once `N ≥ m`).  For
   `m^ε ≤ N ≤ m` pick `k` with the exponent pair `expPair k` beating `ε`, as in Vandehey §6.1.
   The repo's `GrowingLocalizedLogExponent.lean` already extracts power savings from
   `VandeheyThm51`: read it first and reuse its lemmas about `expPair`, `alpha`, `constPair`.
2. **Reduction (paper §3)** to Proposition C: integer coefficients `pᵢ ≠ 0`, a denominator `L`
   coprime to `b`, frequency `h = 1`, via the Weyl criterion.  The repo has Weyl-criterion ⇒
   normality bridges (`isNormal_iff_equidistributed_orbit`, and whatever
   `GrowingLocalizedLogNormal.lean` uses): reuse, do not rebuild.
3. **Lemmas 1–3 (paper §4)**: tail approximation `|bⁿξ − Sₙ| ≤ C₀/n`; constancy `S_{s+j} = b^j S_s`
   between kicks; the denominator lemma (newest term survives: ℓ-adic valuation, pairwise
   coprimality used exactly once; `κ nʳ ≤ Dₙ ≤ L nʳ`).
4. **Paper §5**: cut `[√N, N)` at the `≤ r log₂ N` kicks; short pieces are `o(N)`; long pieces get
   `VandeheyCor12` at `ε = 1/(2r+1)`.
5. **Headline** `isNormal_two_stoneham_three_add_five` from Theorem A with `r = 2`.

`GrowingLocalizedLog*.lean` (`zetaY_isNormal`) is the closest existing proof in this repo, using the
same cited input and the same pieces-plus-Weyl shape.  Mine it hard.

## If a statement is false

Do not weaken it.  Prove the negation next to it, leave the original sorried with a docstring
note, and `box stuck` with the witness.  If the exact hypotheses of `VandeheyThm51` do not deliver
Cor 1.2 as stated (e.g. a `P`-dependence hidden in a constant), write that up in the handoff with
the precise gap, and add the minimal extra hypothesis to `VandeheyCor12`'s *proof path* only
through a new named Literature Prop, never by editing `VandeheyThm51`.

## After the target file is sorry-free

Maze: if the `register` has a row covering Stoneham sums as open (grep "Stoneham"), update it;
otherwise nothing.  Update `STATUS.md` with the headline.

## Done when

`StonehamSumsNormal.lean` is sorry-free (host-checked), `lake build` is green, and the three
theorems print only `[propext, Classical.choice, Quot.sound]` under `#print axioms` (the
`VandeheyThm51` hypothesis is a binder, not an axiom).
