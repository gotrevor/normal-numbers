# Retained-box tail and phase transfer

Continue only in this worktree, reusing PrimeModelRadical and PrimeModelComplement.
Shared dependencies are already checked/prepared.  The other session owns main.
Create PrimeModelRadicalTail.lean and import it from the root.  No axioms/sorry,
no frozen target changes, no other worktrees.  Scope is this probability layer,
not the fundamental lemma or G4 summatory work.

Define the actual radical size d_j(s) = product_i (if s i = some j then p i else 1)
as a real product (or a natural product with real cast).  p : finite index -> Nat,
p i > k, k>=1.  Let B(T) = states with d_j(s)<=T for every j.

Prove radical_box_tail: for T>=1, alpha>0, and moment budget
sum_i (((p i : Real)^alpha - 1)/(p i : Real)) <= A,
sum_{s not in B(T)} weight k (primeRecip p) s
 <= (k:Real) * exp A / T^alpha.
Use the existing radical_site_moment_le_exp, a finite Markov bound and union
bound.  Prove the real-power-of-product identity rather than assume it.
Keep hypotheses explicit: the arithmetic estimate A<=20 is NOT proved here.
Expose a reusable finite Markov/union helper only if it makes the proof shorter.

Then prove radical_box_phase_transfer: for any nonnegative normalized actual
law nu on the same finite state space, any f of complex norm<=1, and
retained L1 discrepancy sum_{s in B(T)} |nu s - weight s| <= delta,
the expectation difference <= 2*k*exp A/T^alpha + 2*delta.
Use probability_complement_phase rather than reprove its inequality.
Do not hide tail or L1 discrepancy assumptions in new axioms.

Persist independent numeric Lean anchors for k=2, primes 3,5, radical threshold:
T=1 or 2 gives tail4/5; T=3 gives2/5; T=5 gives2/15; T=15 gives0.
For T5 only assigning BOTH primes to the SAME shift exceeds5, two states,
each mass1/15.  Expand the state space independently of the general theorem.

Document precise remaining obligations in papers/prime-model-radical-tail.md,
build the full project, commit green, write HANDOFF-radical-tail.md and STOP.
Do not attempt unrelated pre-existing sorries even if supervisor reports them.
