# The finite radical model (2026-09-21)

**Sieve reassessment:** [the current assessment](prime-model-sieve-assessment.md)
shows that lower retained-probability estimates alone suffice by normalization.
The explicit lower Brun construction, support and relative error are proved
in `PrimeModelBrunLower.lean`; `PrimeModelPrimeDimension.lean` discharges its
density hypothesis for k/p.  `PrimeModelLowerTransfer.lean` proves lower-only
probability-to-phase transfer.  The two-sided interface discussed below is
historical and stronger than necessary, not a remaining proof requirement.
The arithmetic lower count is proved in `PrimeModelBrunCount.lean`
(`brun_sifted_count_lower`, main commit `3a15d2c`).
[The square-remainder audit](prime-model-square-remainder.md) shows that
R^2 suffices; the sharper divisor-sum estimate below is also no longer needed.
The remaining application work includes actual-state identification,
retained-state cardinality, phase decay and final parameter assembly.

Formalized in `src/NormalNumbers/PrimeModelRadical.lean`, namespace
`NormalNumbers.PrimeModel.Radical`.  Sorry-free, axioms
`propext, Classical.choice, Quot.sound` only.

## What changed

The earlier prime model recorded the full `p`-adic valuation of `n + j`, so each
site carried an infinite state space and the shortcut needed a tail estimate
(`PrimeModelComplement.lean` supplies exactly that transfer).  The radical model
replaces the state space at a site `p > k` by the finite set `Option (Fin k)`:

* `some j`  —  `p ∣ n + j`, **all higher valuations merged into this one state**,
  mass `1/p`;
* `none`  —  `p` divides none of `n, n+1, …, n+k-1`, mass `1 - k/p`.

This is a model *change*, not a truncation of the valuation law to squarefree
support: the mass `1/p` of `some j` is the full mass of the event `p ∣ n + j`,
not the squarefree part `1/p - 1/p²`.  The masses are a probability law exactly
when `k ≤ p`, which every prime of the window `(k, y]` satisfies.  Distinct
primes are declared independent, so the global law on `ι → Option (Fin k)` is the
product law `weight k q s = ∏_p localWeight k (q p) (s p)`.

Statements are proved for abstract reciprocals `q : ι → ℝ` and re-exposed with
`q p = 1/p` (`primeRecip`) in the `_prime` variants.

## The Lean layer

| result | content |
| --- | --- |
| `localWeight_nonneg`, `localWeight_sum` | local masses `≥ 0` (needs `k*q ≤ 1`) and sum to `1` |
| `sum_pi_prod` | independence: `∑_s ∏_p g p (s p) = ∏_p ∑_a g p a` (via `Finset.prod_univ_sum`) |
| `radical_weight_nonneg`, `radical_mass_one` | the product law is a probability law |
| `localPhase_expectation` | `E φ_p = 1 + q_p ∑_j (z_{p,j} - 1)` |
| `radical_phase_product` | `E ∏_p φ_p = ∏_p (1 + q_p ∑_j (z_{p,j} - 1))`; prime form `∏_p (1 + (∑_j (z_{p,j}-1))/p)` |
| `radical_mult_product` | real multipliers, general per-shift form |
| `radical_site_moment` | single shift `j₀`: `E ∏_p (1_{state=some j₀} t_p + …) = ∏_p (1 + q_p (t_p - 1))`; prime form `∏_p (1 + (t_p-1)/p)` |
| `radical_site_moment_uniform` | multiplier on every shift: `∏_p (1 + k q_p (t_p - 1))` |

`sum_pi_prod` is the only structural input; every identity is an instance of it
plus a three-term local computation (`Fintype.sum_option`).  Numeric anchors at
the end of the file expand the one- and two-site state spaces by hand
(`Fin.consEquiv`) and check `4/3`, `8/5`, and total mass `1` against the closed
forms — a guard against a mis-stated model, independent of the identities.

## Arithmetic bridge (documented, not formalized this lap)

For `n` in a progression and the window `(k, y]`:

* `d_j(n) = ∏_{p ∈ (k,y], p ∣ n+j} p`, and `D = ∏_{j<k} d_j`.
* The model density of a fixed assignment `d` of divisibilities is
  `μ(d) = 1/D · ∏_{p unassigned} (1 - k/p)`, which is precisely `weight` at the
  corresponding state tuple.
* After fixing `n mod Q` and the assigned divisibilities, one works in a
  progression of modulus `QD`.  Assigned primes need **no** further exclusion
  (`g = 0`); unassigned primes exclude `k` residue classes (`g = k/p`).  Hence
  the sieve main term divided by `QD` equals `μ(d)/Q`.
* With `α = 1/(2 log y)` and `y ≥ e²`, `radical_site_moment` with
  `t_p = p^α` gives
  `E d_j^α = ∏_{k<p≤y} (1 + (p^α - 1)/p) ≤ exp(∑_{p≤y} (p^α-1)/p)
   ≤ exp(√e · α ∑_{p≤y} log p / p) ≤ exp(4√e)`,
  using `p^α - 1 ≤ √e · α log p` for `α log p ≤ 1/2` and Mertens.  So the old
  `e^20` bound survives the model change with no geometric series over
  valuations.

## Residual analytic obligation

### Keep the small-prime residue in the joint law

For assembly with the counting argument, the sample space is `(r,s)`, not only
the radical assignment `s`: `r` ranges over residues modulo
`Q = product of primes <= k`.  Use model mass `mu(r,s) = weight(s)/Q` and
actual mass `nu(r,s) = #{0 <= n < x : n mod Q = r, state(n)=s}/x`.
For integer x>0 these both sum to one.  The retained box is independent of r,
so the joint model tail equals the radical model tail, without a factor Q.
The retained L1 discrepancy is the sum over ALL r and retained s.

The bounded phase is `a(r) * product_i localPhase(i,s_i)`, with |a(r)|=1.
Independence in the model factors its expectation into the small-prime average
and the already-proved radical Euler product.  Apply `probability_complement_phase`
to this JOINT law.  Do not treat the empirical residue masses as exactly 1/Q:
they are not uniform unless Q divides x.  Alternatively, conditioning each
nonempty residue class works, but changing its empirical mass to 1/Q costs
an extra endpoint estimate.  The joint-law formulation avoids that step.

The counting bridge must still prove the CRT assignment progression and the
unassigned-prime exclusion counts for general k; the persistent CLI tests are
finite controls of those statements, not their proof.

### Analytic assembly still required

### Existing counting tools to reuse

`G4CRTInput.lean` already proves `NormalNumbers.G4.abs_card_filter_modEq_sub_le`:
each residue class modulo m>0 has count within 1 of x/m on `range x`.
It also has `apSample_filter_eq` and the finite CRT factorization `resMean_prod`.
Use those for the radical counting bridge instead of weakening the remainder
to the shifted-divisibility bound `x/p+2` in `G4WiringSparse.lean`.

For a fixed assignment and small residue, the assigned-prime conditions give
one progression modulo QD.  For squarefree sieve modulus e composed of
UNASSIGNED primes, CRT gives rho(e)=k^omega(e) distinct classes modulo QDe.
Summing the existing per-class discrepancy gives error <=rho(e), relative
to x*rho(e)/(QDe).  Assigned primes have g=0 and contribute no such classes;
restricting sieve support to unassigned primes makes gcd(QD,e)=1 explicit.
Now proved in `PrimeModelRadicalCRT.lean`: distinct local roots, their CRT
product count, and the finite-interval bound `radical_sieve_count`, with the
class count discharged by `radical_sieve_admissible_card`.  The general
two-sided sieve weights remain a separate obligation, not a consequence of
exact full-period CRT.  Still to connect: an actual radical state with this
assigned-divisibility predicate and the absence of all unassigned hits.

### Counting-to-sieve interface for the next proof step

Fix an assignment s and small residue r.  Write A for assigned primes, U for
unassigned primes, D=product(A), and V=product_{p in U}(1-k/p).
For E subset U let C_E count assigned divisibilities and a hit at every p in E,
always with n mod Q=r and 0<=n<X.  The proved CRT lemma gives
`|C_E - X*rho(E)/(QD*product(E))| <= rho(E)`, `rho(E)=k^|E|`.
The actual radical atom is the count C of those same assigned divisibilities
with NO hit at any prime of U.

The still-needed two-sided weights lambdaMinus(E), lambdaPlus(E) must bound
that no-hit indicator pointwise on EVERY subset of bad primes.  Their main
sums `sum_E lambda(E)*rho(E)/product(E)` must lie between
`(1-eta)*V` and `(1+eta)*V`, in the appropriate direction.
If `L` bounds `sum_E |lambda(E)|*rho(E)` for EACH sign, then
`|C - X*V/(QD)| <= eta*X*V/(QD) + L`.
For X>0 this becomes retained-atom discrepancy
`|nu(r,s)-mu(r,s)| <= eta*mu(r,s) + L/X`, since `mu(r,s)=V/(QD)`.
This finite implication does not construct the weights or prove their estimates.

Summing retained atoms costs at most `eta + (#retained joint atoms)*L/X`.
The remaining combinatorics must inject radical assignments into their integer
tuples to justify `#retained joint atoms <= Q*floor(T)^k`; finite support alone
does not give this bound.  Level-supported weights with absolute value <=1
would allow `L <= sum_{squarefree e<=R} k^omega(e)`; the useful estimate
`<= R*(1+log R)^(k-1)` is another explicit arithmetic obligation.

The above does **not** prove the two-sided sieve fundamental lemma that the
shortcut consumes.  Mathlib's `SelbergSieve` provides upper-bound machinery only;
the matching lower bound (Rosser–Iwaniec / Brun with an explicit error
`1 + O(e^{-s})`) is not in mathlib and is not supplied here.  That remains the
major sieve input for the downstream argument.  The radical model removes the
infinite valuation state space, not the retained-box tail obligation:
the counting argument still restricts every d_j to T, and must bound the mass
outside that box with the moment estimate above and Markov's inequality.
The arithmetic CRT bridge, that tail bound, the phase-decay estimate, and the
downstream constant bookkeeping remain to be assembled in Lean.  None is
asserted to follow merely from finite support.
