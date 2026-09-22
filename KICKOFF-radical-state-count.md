# Active attended override: radical state identification and retained count

Trevor authorized the next lap.  Work directly in main, Opus/low, one scoped
lap.  Existing statements frozen.  No older DIRECTION campaign is a fallback.

Create src/NormalNumbers/PrimeModelRadicalState.lean importing the existing
radical tail/moment and arithmetic CRT modules.  Own only the new file, root
import and a dated handoff.  Prove both named targets below.

1. retainedBox_card_le: for arbitrary finite index type iota, injective
p:iota->Nat with every p(i) prime, every k:Nat and real T>=1,

    ((Radical.retainedBox k p T).card:Real) <= (Nat.floor T:Real)^k.

Use the EXISTING retainedBox and radSize definitions, not a replacement.
Define natural tuple d(s)(j)=product_i(if s i=some j then p i else 1);
its real cast is radSize.  Show s -> d(s) injective using unique prime
factorization, including none states and k=0.  Each retained coordinate is
in Icc 1 (floor T); there are floor(T)^k tuples.  This is the required
bound independent of the number of primes, not the trivial (k+1)^card iota.

2. actual_state_sifted_iff: for k>=1, a finite prime set P all p>k,
define actualState n : P -> Option(Fin k), recording the unique j with
p divides n+j+1, or none if no such j.  Prove uniqueness rather than assume
it.  For an arbitrary state s let A be assigned primes, U=P minus A, and
j:Nat->Fin k extend the prescribed assigned shifts (default zero elsewhere).
For any Q,r,n prove:

    (n % Q = r AND actualState n = s)
      IFF Radical.SiftedCond k A U Q r j n.

Be explicit that this is n+j+1, matching the CRT theorem and target window.
Also prove state_model_density: existing Radical.weight with primeRecip
equals (1/product A)*product_U(1-k/p).  This must refer to the same A,U,s
as the predicate equivalence.  Prove disjointness and partition helpers.

If time remains, normalize counts over n<X to an empirical joint law on
Fin Q x (P -> Option(Fin k)), for X,Q>0, and prove mass=1.
Do not substitute that optional task for either main target.

No analytic hypotheses, no new dependencies.  Reuse prime-product arguments
from PrimeModelBrunCount where useful, without editing that worker's module.
Permanent tiny examples: P={3,5}, k=2; n=0 has neither hit (1,2);
n=1 assigns3 to shift1; n=2 assigns3 to shift0; n=3 assigns5 to shift1.
These catch an n+j versus n+j+1 mismatch.

Commit a compiling skeleton early; build module/full project, write exact
hypotheses and remaining application work in the handoff, then stop.
Completion is the substantive state/count bridge and retained cardinality,
not a tally of declarations or sorries.  box done --green only after targets.
