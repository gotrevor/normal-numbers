# Prove the lower-sieve core, not another conditional wrapper

Read papers/prime-model-sieve-assessment.md completely.  It has the explicit
candidate proof and parameters.  Trevor asked for real progress on the sieve
obstacle; the three properties below TOGETHER are the task's success criterion.

Work only in this existing worktree.  Create PrimeModelBrunLower.lean (split into
focused imported helper modules if genuinely useful).  Root import, repo note,
handoff, full build and green commits.  Do not edit other worktrees, frozen
targets, or unrelated pre-existing sorries.  Shared deps checked and prepared.
No axioms or hypotheses equivalent to the desired conclusion.  Lean may use
ordinary temporary sorries while working, but do not claim completion with any.

TARGET: finite prime set U, all p<=y; y>=exp2; k>=1; 0<=g(p)<1; K>=1;
tail-product dimension hypothesis exactly as in the assessment.  For
s>=max(80k,40logK+4), construct lambda : Finset Nat -> Real on subsets of U
and prove all of:
(1) |lambda(E)|<=1 and lambda(E)!=0 implies product E<=y^s;
(2) for EVERY bad subset B of U, sum_{E subset B}lambda(E)<=indicator(B empty);
(3) sum_{E subset U}lambda(E)*product_{p in E}g(p)
    >= (1-2exp(-s/2))*product_{p in U}(1-g(p)).
Expose combined theorem brun_lower_fundamental with only the stated elementary
and dimension hypotheses.  Do NOT assume (2), a first-failure decomposition,
the factorial error estimate, or (3) as a new black box.

Construct lambda by decreasing prime lists and even-position cutoffs from the
assessment.  Equivalent finite-set recursive implementation is welcome if it
makes first-failure partition and sign cancellation easier.  The exact model
defect decomposes into even first-failure prefixes times the product over all
smaller remaining primes.  Pointwise version uses densities0/1 and is finite.

No need to formalize an infinite combinatorial sieve: U is finite throughout;
the final error sum may be bounded by a finite geometric sum or a convergent
geometric series.  Prime primality itself is not essential for these three
properties, just distinct ordered numbers>=2; a generalization is fine if
the prime-specialized target follows directly.

Persist numeric anchors from the assessment independently of the headline:
U={2,3,5,7}, arbitrary even cutoffs3,2 gives supported max42,
model V=8/35, lower sum23/105, defect1/105, relative defect1/24.
Unrestricted cutoffs give exact inclusion-exclusion, max210.
These are controls only; no scan substitutes for the uniform theorem.

If the entire target resists this lap, commit the strongest truthful partial
result and name the EXACT remaining combinatorial/analytic lemma.  Do not fill
time with unrelated transfer lemmas, count it as success, or declare the core
done merely because an arbitrary support bound or a conditional wrapper builds.
Do not solve the frozen KMT target or the other G4 campaign in this lap.
