# normal-numbers

A Lean 4 / [Mathlib](https://github.com/leanprover-community/mathlib4) programme
on **normal numbers**: numbers whose base-`b` digit expansion contains every
length-`k` block with asymptotic frequency `b⁻ᵏ`.

Almost every real number is normal in every base (Borel 1909), yet no
"naturally occurring" constant (`π`, `e`, `√2`, `ln 2`, …) has ever been proven
normal in any base.  This repo formalizes the definitions, the classical
equivalences, and the two known bridges toward that open problem.

## Targets

1. **Definitions** — sequence normality, real-number normality via the digit
   map `i ↦ ⌊b^(i+1)·x⌋ mod b`, equidistribution mod 1.  (`Defs/`)
2. **The sequence ↔ real bridge** — a digit sequence not eventually `b−1`
   is recovered exactly by the digit map of the real it sums to.  (`Bridge.lean`)
3. **Wall's theorem** (1949) — `x` is normal in base `b` iff the orbit
   `(b^n·x mod 1)` is equidistributed.  (`Wall.lean`)
4. **Bailey–Crandall reduction** (2001) — if the orbit
   `x₀ = 0, xₙ = 2·xₙ₋₁ + 1/n mod 1` is equidistributed, then `ln 2` is normal
   in base 2.  Machine-checks the cleanest known statement of the open problem.
5. **Stoneham's theorem** (1973) — `α₂,₃ = Σ 1/(3ⁿ·2^(3ⁿ))` is normal in
   base 2, unconditionally: the first analysis-born number with a normality
   proof.

6. **Continued fractions and Khinchin's constant** (`CF*.lean`, `Khinchin.lean`) -
   the Gauss map as a second digit system beside multiplication by `b`: cylinder
   measure, the Gauss-Kuzmin digit law, quantitative mixing, and a Chebyshev
   block-frequency bound.

## The B5' witness

The programme's main result is a single explicit real number, `xstar`, proved to be
**absolutely normal** (normal in every base `b ≥ 2`), **continued-fraction normal**,
and **Khinchin-typical** (its CF digits have geometric mean `K₀`), all at once.

- `exists_absolutely_normal_cf_normal` - the Becher-Yuhjtman theorem (2019), built
  here without the paper's two deep imports (a CLT of Morita/Vallee and a large
  deviations result of Kifer-Peres-Weiss), which served efficiency rather than
  existence; elementary Markov and mixing substitutes replace them.  Pillai's
  theorem is formalized from scratch along the way, since Mathlib does not have it.
- `exists_absolutely_normal_cf_normal_khinchin` - the same witness, additionally
  Khinchin-typical.

Both are `sorry`-free and depend only on Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).  `STATUS.md` has the per-theorem
table; `JUDGE.md` records the verification history, including the close-out
`#print axioms` sweep and its red-team test.

As far as a survey of provers, Mathlib, the Lean Zulip and the AFP reaches (August
2026), this appears to be the first formalization of Becher-Yuhjtman in any prover.
We did not find the three-way conjunction written down anywhere, but that is not a
claim that it is new: the implication may well be routine and simply unstated, and a
search of formalization repositories says nothing about the paper literature.

## How this was built

Most of the Lean here was written by Claude (Claude Code) working under my direction,
in a harness where the headline statements were frozen up front and a separate review
pass audited every lap for statement drift and axiom hygiene.  I would rather say that
plainly than have you wonder.  Correctness claims are not softened by it: the theorems
above are machine-checked, and the axiom sweep is reproducible from `JUDGE.md`.

Sequence-level definitions are aligned with
[OldMathematician/ChampernowneNormality](https://github.com/OldMathematician/ChampernowneNormality)
(Apache 2.0), which proves normality of the base-`b` Champernowne *sequence*;
target 2 is exactly what upgrades such a result to the *real number*.

## License

Apache 2.0.  Copyright 2026 Trevor Morris.
