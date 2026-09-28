# Joint Erdős–Borwein words: prepared formalization, not launched

## Mathematical target

For every finite set of distinct integer bases at least two, any prescribed word
in each corresponding Lambert constant occurs at one common arbitrarily late
digit position.  Bases 2 and 4 are a required control, not an optional extension.

Read `papers/2026-09-26-joint-lambert-disjunctivity.md` in full.  It gives the proposed
paper proof and distinguishes the new encoding from the inherited scalar method.
Read the peer's scalar source at pinned revision
`CaptainSude/erdos-borwein-disjunctivity:bd98789a177470cc4b3e33e6769e859f6144c906`.
The attended session cloned it to `/private/tmp/nn-eb-prior-art`; fetch a persistent
clone if that temporary directory has expired.  Preserve its attribution and
inspect its license before copying source.  Reusing the mathematical argument
does not require copying its Lean files.

## Frozen statements

- `NormalNumbers.JointLambert.JointWords`
- `NormalNumbers.JointLambert.JointLambertDisjunctivity`
- `NormalNumbers.JointLambert.EvenEncoding`

They live in `src/NormalNumbers/JointLambertStatement.lean` as actual `Prop`
definitions.  No base-coprimality or multiplicative-independence hypothesis may
be added.  Do not replace the common offset by one offset per coordinate.

## First bounded target

Prove `evenEncoding : NormalNumbers.JointLambert.EvenEncoding` in a new
`JointLambertEncodingProof.lean`.  The nonresonance engine is already proved in
`JointLambertEncoding.lean`.  Filter a character's support before selecting its
smallest base.  Prove geometric-sum orthogonality for the finite cyclic measures,
then obtain an interior-box hit by torus Fourier approximation.  An equivalent
elementary proof is welcome.  Freeze the above definition unchanged.

Success is a proved finite encoding theorem with the dependent-base control and
an explicit route from it to the next arithmetic step.  An obstruction or a
counterexample must name the precise statement and preserve the witness.

## Subsequent arithmetic work

1. Generalize the existing selectable-prime CRT constructor to exponent
   `lcm(bases) - 1`; one survivor has divisor count `2a`.
2. Carry the source-faithful AGP exceptional-modulus input and prime-interval
   supply as explicit named hypotheses.  Avoid the old vacuous `PrimeDensityAP`.
3. Use one binary tail majorant for every coordinate.  Do not introduce separate
   survivor primes or a prime-tuples hypothesis.
4. Prove the common-offset digit identity and arbitrarily late occurrences.

The quantitative count in the paper can follow the qualitative headline.  It is
not the first grind target.  AGP formalization is a separate input campaign, not
permission to quietly axiomatize the conclusion.  No existing headline changes.

## Verification and execution

`./probes/swingc2_window.py test -q` exercises the exact finite encoder through
the CLI, including hand-computed witnesses and negative controls.

Run the proof-writing phase through the normal Opus/low treadmill workflow,
with its declaration and file completion gates.  This document prepares work;
it is not a launch authorization.  The attended session owns statement changes
and research review.  It should not absorb the edit/build/fix loop.
