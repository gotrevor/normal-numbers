# Opus brief for the cutoff six reservoir

Continue the mathematical investigation of the BBP prime reservoir with lower cutoff `6n`.  The first target is to prove that its exit transfers are not uniformly `O(1/n)` modulo one.  Then investigate whether those transfers vanish at all, and whether their arithmetic can help the π projection.  The first theorem is a milestone, not a proof that the modified route reaches π.

## Starting point

Work from `/Users/gotrevor/src/nn-pi-reservoir`, branch `research/pi-reservoir`, including review commit `71c754c0`.  Follow the repository instructions.  Use the NN formal ledger and negative inventory as the foundation; this brief calls for mathematical invention and proof, not a literature sweep.

Read:

- `src/NormalNumbers/PiDisjunctiveRoutes/PrimeReservoirStep.lean`: exact recurrence and the proved cutoff-four exit collapse.
- `src/NormalNumbers/PiDisjunctiveRoutes/PrimeReservoirOrbit.lean`: the cutoff-four reservoir shadows the orbit of ρ.
- `src/NormalNumbers/PiDisjunctiveRoutes/ReservoirCutoffReview.lean`: exact cutoff-six witnesses, the proved `p = 24k+1` cubic identity, and the unproved general `CutoffSixCubicLaw` node.
- `scripts/pi_route2_cutoff_review.py`: exact arithmetic probe and cutoff-four control.
- `docs/pi-routes/route2.md`: corrected interpretation of the original stopping result.

The original proofs survived an independent axiom audit.  The correction concerns their scope: a necessary condition on ρ is not a proof that the route cannot work, and the `64/p` collapse is specific to the cutoff `4n`.

## First theorem

Let `E₆(n)` be the exact rational exit transfer `CutoffReview.rationalExit 6 n`, and write `‖t‖ℤ` for distance to the nearest integer.  Freeze and prove:

```text
For every real C > 0 and every N,
there exists n ≥ N such that
    ‖E₆(n)‖ℤ > C / (n + 1).
```

This excludes an eventual uniform `C/(n+1)` bound, including after discarding any finite prefix.  Keep the full exit sum in the statement, rather than proving a result only about one selected summand.

### Proposed proof mechanism

Take primes `p ≡ 29 (mod 60)` and set `n = (p−5)/6`.

1. The exit window is `(p−5, p+1]`.  The eligible BBP denominator classes are `1 mod 4`, so its only candidates are `p−4` and `p`.  The former is a composite multiple of five.  Verify that `p` actually entered the reservoir, so the exact exit sum has precisely this one term.
2. Prove the needed cubic congruence.  For `p ≡ 5 (mod 6)`, its integer exit numerator `A` satisfies `A³ ≡ 1024 (mod p)`.  The full `CutoffSixCubicLaw` is currently unproved.  For this first theorem, proving just the two relevant classes `p ≡ 29, 89 (mod 120)` is sufficient.
3. Choose the centered residue `a` of `A` modulo `p`.  Then `‖E₆(n)‖ℤ = |a|/p` and `p` divides `a³−1024`.
4. No integer has cube 1024.  Consequently that divisible integer is nonzero, and

   ```text
   p ≤ |a³ − 1024| ≤ |a|³ + 1024.
   ```

   Thus `‖E₆(n)‖ℤ ≥ (p−1024)^(1/3)/p` for large p.  This is of order `p^(-2/3)`, which eventually exceeds every fixed `C/(n+1)` because `n+1 = (p+1)/6`.  The Lean proof can use cubic inequalities directly without introducing real cube roots.
5. Use the repository's arithmetic-progression prime theorem to obtain arbitrarily large primes `29 mod 60`.  Verify its hypotheses, including coprimality.  If a needed literature interface is missing, state it faithfully as a named hypothesis Prop and keep the conditionality explicit.

Check every index and sign against the exact witness `n=14`, `p=89`: the exit is `2945 + 39/89`.  The cutoff-four control must still reproduce its proved `64/p` formula.

## Subsequent mathematical questions

After the first theorem, distinguish these two possibilities:

```text
Vanishing:       ‖E₆(n)‖ℤ → 0.
Nonvanishing:    ∃ ε > 0, ∀ N, ∃ n ≥ N, ‖E₆(n)‖ℤ ≥ ε.
```

The first theorem does not decide between them: its lower bound tends to zero.  Nor does the finite census prove nonvanishing.  Seek an arithmetic argument, or isolate the exact additional statement about cubic residues that would settle the distinction.  Do not replace that missing statement with a larger numerical sweep.

Also derive the exact cutoff-six reservoir/residual recurrence.  Exit transfers act along `(1,−1)` and cancel in the sum `R+S`, whose orbit shadows π.  Any claimed improvement toward π must explain how the arithmetic controls this sum direction.  Mixing along a fixed-sum fiber alone does not suffice.  Establishing nonvanishing transfers would remove the original vanishing-kick argument, but would not itself prove joint support or disjunctivity.

## Review and delivery

State the targets in Lean before writing conclusions.  Preserve existing proved statements; put the new cutoff-six development in its own files.  Record exact refutations and reopen conditions in the formal ledger, with accurate Maze verdicts.  A reformulation or necessary condition should be labelled as such, rather than as a no-go theorem.

Once the first theorem is complete, obtain an independent adversarial review of the statement, full-exit identification, congruence, prime progression, quantifiers, and axioms.  Make review a separate task at that checkpoint; do not rely on an optional later treadmill lap firing.  Continue independent mathematical exploration while review is underway where the work does not depend on its outcome.

Deliver:

- The proved first theorem, its dependencies, and `#print axioms` output with a sorry-detection control.
- The status of vanishing versus nonvanishing, separating proof, hypotheses, and finite evidence.
- The precise implication, if any, for π's digits.  If none has been established, say so.
- A short handoff identifying the remaining arithmetic mechanism and any narrowly proved obstruction.

This file prepares the work; writing it does not launch a run.  A subsequent launch should use the session-owned treadmill workflow and its authorized resource envelope.
