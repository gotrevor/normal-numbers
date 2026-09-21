# Bounded probability formalization

Trevor explicitly requested an Opus treadmill on 2026-09-20.  This isolated worktree
belongs to that task.  Its inherited DIRECTION and HANDOFF files concern another
running NN job and do not govern this run.  Do not touch G4WiringRough or pursue G4.

Prove the three frozen statements in `src/NormalNumbers/PrimeModelComplement.lean`:
`probability_complement_tail`, `probability_complement_L1`,
`probability_complement_phase`.  Preserve statements verbatim.  Helpers welcome.
No axioms; no change to the analytic KMT input.  Add an import to `src/NormalNumbers.lean`.
The index type is not assumed finite: the model has arbitrarily large valuations.

Proof: split each normalized mass into the finite B sum plus its complement tsum.
Their total masses agree.  Bound the difference of the B sums by the B sum of
absolute differences.  Outside B, `|ν-μ| ≤ ν+μ`.  Summing gives the L1 result.
For phases prove absolute summability by domination, rewrite the difference as
a tsum, use norm-of-tsum ≤ tsum-of-norm, and `‖(ν-μ)f‖ ≤ |ν-μ|`.
Useful checked APIs: `Summable.sum_add_tsum_compl`, `Summable.subtype`,
`Summable.abs`, `Summable.of_norm_bounded`, `Finset.abs_sum_le_sum_abs`.
The bare identifier `tsum_le_tsum` does not exist at this pin; look up its namespace.

Start by compiling this scaffold, correct only syntax if necessary, then commit it.
Work only on this module, its root import, and `HANDOFF-prime-model-complement.md`.
Run a module build and inspect the three declarations with `#print axioms` at completion.
The global pre-commit hook supplies the repo build.  Commit green, write the handoff,
and `box done --green` once the three theorems are proved.  Do not launch another job.

The host already inspected `lake-base status 4.33.1`; dependencies are supplied from
the canonical store.  The host independently audits the arithmetic sieve application.
