# Exact CRT counting for the radical sieve

Work only here. New PrimeModelRadicalCRT.lean, root import, project note, handoff.
No axioms/sorry, frozen target edits, unrelated sorries or other worktrees.
Shared deps checked. Full build and green commit; stop after this bounded lap.

Reuse G4CRTInput.lean: NormalNumbers.G4.abs_card_filter_modEq_sub_le gives
|#{n<X:n congruent c mod m} - X/m|<=1 for m>0. resMean_prod and
sum_range_mul_eq_mul_sum already prove CRT product factorization. Use them
where ergonomic, or Nat.chineseRemainderOfFinset / ZMod.chineseRemainder.

PRIMARY required theorem radical_sieve_count:
k>=1; A,E disjoint finite sets of primes, all >k; Q>0 and coprime to every
prime in A union E; r<Q; assigned shift j : Nat -> Fin k.
Count n in range X satisfying:
 n mod Q=r;
 for every p in A, p divides n+(j p).val+1;
 for every p in E, exists t:Fin k, p divides n+t.val+1.
Let D=prod_{p in A}p, e=prod_{p in E}p, rho=k^E.card.
Prove |count - (X:Real)*rho/(Q*D*e)| <= rho.
All naturals cast properly. X may be0. A or E may be empty.
This counts divisibility at sieve primes, NOT exact radical tuples yet.

Supporting results (useful independently): the k negative-shift residues
mod p are distinct for p>k and have cardinality k; assigned prime gives
one residue. CRT gives exactly rho distinct classes mod QDe. Summing the
existing per-class discrepancy proves the bound. A generic finite family
of pairwise-coprime moduli with allowed residue sets may shorten this.
Do not assume the number of CRT classes as a hypothesis in the headline.

Numeric anchors, independently computed by decide/native_decide/norm_num:
k2,Q2,r0,A={3},j3=site1 (Fin value0),E={5}: classes8,14 mod30.
X20 count2, main4/3, error2/3<=2; X9 count1, main3/5, error2/5.
A={3},E={} at X20 count3 (2,8,14), main10/3,error1/3<=1.
A={},E={3,5} at X20 count3 (4,8,14), main8/3,error1/3<=4.
Do not spend the lap building a second regression harness; put anchors in Lean.

If time remains: explain how E ranges over subsets of unassigned primes for
the radical tuple sieve, why assigned primes require no exclusion, and how
the main density is rho(e)/(QDe). The two-sided fundamental lemma is NOT
proved by this result. Keep that remaining obligation explicit.
