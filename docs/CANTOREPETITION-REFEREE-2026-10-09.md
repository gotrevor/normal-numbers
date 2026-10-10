# Referee: a Liouville point of K normal to every base that is not a power of 3

Subject: `CantorRepetition.liouvilleCantorFullProfile : LiouvilleCantorFullProfile`, proved by the
repetition treadmill (run `nn-stretch-20261008-182125`, laps 8–13), with no cited input.
`#print axioms` = `[propext, Classical.choice, Quot.sound]`, verified 2026-10-08 by the operator.
Two independent passes: an English check against the source (no build), and a literature sweep.

## Verdict

**Accept with fixes (applied).**  The frozen statement is faithful and nothing on the route is
vacuous.  The fixes were stale docstrings, plus a few inaccuracies in the outward note.

## Statement fidelity

- `IsNormal` is full normality: every block of every length, overlapping counts, frequency `b^{-k}`,
  applied to `Int.fract x`.  `cantorSet` and `Liouville` are Mathlib's.
- `2 ≤ b ∧ ∀ s, b ≠ 3^s` is exactly "not a power of 3".  The statement is not weaker than the English.

## The formerly cited inputs

- `PadicTwoLogs.padicTwoLogs`: `t ≥ 2`, `3 ∤ t`, `tᵟa ≠ b`, `3^g ∣ tᵟa − b` ⇒
  `g ≤ C(1+log(δ+1))²(1+log max(|a|,|b|))`.  `tᵟa ≠ b` excludes `a = b = 0`, so the `log 0` trap
  cannot fire.  The shape is Bugeaud–Laurent's (JNT 61, 1996); Yu's p-adic bounds have a single `log B`.
- `laurentZeroLemma`: elementary proof checked by hand.  The rows span by a Vandermonde argument, the
  determinant has degree `≤ (K−1)L` with more roots than that, and its top coefficient is
  `∏ lc(q_l)·det V ≠ 0`.  Multiplicative independence turns out to be unused.
- The multiplicatively dependent case is handled by lifting the exponent (`PadicTwoLogs.lean`).

## Mechanism

- The shadow dichotomy (`shadow_sparse`): if the free option and the copy option are both `≥ θ_k`,
  the relevant integer is cyclically `O(K)`-sparse modulo `3^A − 1`.
- Close sparse orbit points give exact identities `tᵟU = V` (`cyclic_pair_identity`), and
  `SparseIdentityBound` caps `δ`, so sparse points cluster.
- `RunSparseDecay` takes `K ≍ √k`, so `L_K = e^{O(k)}` against `a_k ~ 2^k k!`.
- `t > 1` enters in the endgame `tᵟ < 3^{p*+1}`, and `3 ∤ t` in `PadicTwoLogs`; the guards are
  `not_sparseIdentityBound_one` and `not_sparseIdentityBound_nine`.

## Fixes applied

- Docstrings in `CantorRepetition`, `SparseIdentity`, `PadicTwoLogs` and `ZeroLemma`:
  - Stale labels removed: "Conjecture", "Confidence 60%", "open", "cited, referee needed" and
    "Source not opened" on results that are now proved.
  - Superseded routes tagged "off the proved route".
  - Corrected "Matveev is discharged" to "Matveev is not used".
  - Corrected the base-9 / `t = 1` guard explanation.
- Outward note:
  - Stated the hypotheses of the 3-adic bound.
  - Defined cyclic sparsity correctly (few digit *changes*, not few nonzero digits).
  - Added the closeness condition `tᵟ + 2 ≤ 3^{⌊A/(2K+1)⌋}`.
  - Fixed the section structure.
  - Changed "our Liouville points are never normal to base 6" to "the zero-run points…".
- A reviewer claim that the pinned SHA `11b085ce` was unpushed was false (checked with `ls-remote`).

## Novelty (~80%)

- Becher–Bugeaud–Slaman's 2014 talk lists the base-2 question for `K` as open.  Nothing found
  through arXiv 2607.06773 (Becher–Lew Deveali, July 2026) answers it.
- Closest: the Becher–Bugeaud–Slaman exponent/base-pattern theorem, announced only in talks
  (Slaman, IMS 2015 and 2019).  It would give a Liouville number simply normal to every non-power
  of 3, but not one in `K`.
- The repetition-to-approximation device is Adamczewski–Bugeaud's (Annals 2007), and is cited.
- Limits of the search:
  - Keyword search only, with no Scholar or MathSciNet citation index.
  - Bugeaud's book full text was not reopened in this pass.
  - Unpublished Becher–Bugeaud–Slaman drafts may exist.

## Not claimed

- Computability of the witness: it comes from `ae_repProfile.exists`.
- `ExponentCantorFullProfile` (finite `μ₀`) is open.
- No discrepancy rate.
