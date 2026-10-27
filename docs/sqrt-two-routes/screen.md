# √2: arithmetic mechanism screen

The screen admits **no new disjunctivity campaign**.  It produces three scoped findings, all stated and proved in [`Screen.lean`](../../src/NormalNumbers/SqrtTwoRoutes/Screen.lean).  The most useful is an exact explanation of why Pell certificate searches can succeed without supplying a digit-visitation mechanism.  No numerical search was needed.

Decision date: 2026-10-27.  Apply [MAZE.md](../../MAZE.md) before proposing variants.  This is local mathematical work, with no literature or priority claim.  Namespace below: `NormalNumbers.SqrtTwoRoutes`.

## 1. Adjacent Pell synthesis: an exact reformulation

**Attraction.**  The logarithmic Padé screen encountered denominator obstructions and costly synthesis.  For √2, adjacent Pell approximations form an integer basis.  Perhaps this makes small dyadic linear forms accessible.

Write

\[
p_0=1,\quad q_0=0,\qquad
p_{n+1}=p_n+2q_n,\quad q_{n+1}=p_n+q_n,
\qquad e_n=p_n-q_n\sqrt2.
\]

`pell_norm`, `pell_det`, and `pell_error_step` prove the norm, adjacent determinant, and alternating error recurrence.  For **every** integer target `(P,Q)` and every index `n`, `pell_synthesis` gives integers

\[
u=(-1)^n(Pq_{n+1}-Qp_{n+1}),\qquad
v=(-1)^n(Qp_n-Pq_n)
\]

with `up_n+vp_{n+1}=P` and `uq_n+vq_{n+1}=Q`.  Consequently `pell_signed_error` gives

\[
ue_n+ve_{n+1}=P-Q\sqrt2.
\]

Define the natural absolute budget `pellCost` as `|ue_n|+|ve_{n+1}|`.  `pell_cost_lower` is the triangle-inequality lower bound.  The stronger finding, `pell_cost_exact`, is

\[
0\le Q<q_n+q_{n+1}
\quad\Longrightarrow\quad
|ue_n|+|ve_{n+1}|=|P-Q\sqrt2|.
\]

**Why equality holds.**  The small denominator forces `uv≤0`: if both integer coefficients were positive, their denominator combination would be at least `q_n+q_{n+1}`; if both were negative it would be negative.  Adjacent Pell errors also have opposite signs, so the two contributions have the same sign.  There is no cancellation loss.  These steps are `small_denominator_opposite_coefficients` and `pell_errors_opposite`.

Since `q_{m+1}≥2^m`, the pair at indices `m+1,m+2` already works for every numerator:

\[
\boxed{\operatorname{pellCost}(m+1,P,2^m)=|P-2^m\sqrt2|.}
\]

This is `pell_dyadic_cost_exact`.  `cheap_pell_iff` proves that a certificate below any threshold exists **if and only if the dyadic residual itself is below that threshold**.  Moreover, `pell_windowSupply_iff` proves that signed certificates visiting every interval are equivalent to binary disjunctivity of √2.

**Controls.**  `pell_small_control` checks an exact convergent.  `pell_mixed_control` uses both coefficients: at `(n,P,Q)=(2,1,1)`, they are `(-2,1)` and the budget is `√2−1`.

**Disposition.**  Abandon bare feasibility and absolute-budget optimization as a campaign with current methods.  This does not rule out a proof through Pell coordinates.  It says exactly what a finite successful certificate certifies, and why raising the search budget does not supply an independent reason for visits.

**Reopen only:** a construction or estimate producing signed, word-targeted certificates uniformly, using a constraint on the coefficients beyond these identities and without first locating the desired dyadic visit.  The formal target is `PellWindowSupply`; merely reproving its equivalence or finding another cheap example is insufficient.

## 2. Square-root remainder dynamics: fixed-modulus information loses the language

**Attraction.**  The integer square-root algorithm has a very simple exact state update:

\[
a'=2a+d,\qquad r'=4r-4ad-d,\qquad
d=1\Longleftrightarrow r\ge a+1,\qquad 1\le r\le2a.
\]

`remainder_update_identity` proves `a'²+r'=4(a²+r)` for `d∈{0,1}`.  The intended exact path starts at `(a,r)=(1,1)`; its word-supply question is stated as `ExactRemainderWordSupply`.  This screen does not prove that open input or a new disjunctivity transfer from it.

**Test.**  Retain the remainder update only modulo a fixed positive integer `M`, together with the exact bit threshold, prefix update, positivity bounds, and prescribed norm congruence `a²+r≡T (mod M)`.  Here `T` is arbitrary: the control is not restricted to moduli dividing the true norm.

For any `a≥M`, either next bit can be prescribed.  `mock_remainder` constructs

\[
r_0=M-((a^2-T)\bmod M),\qquad
r_1=a+M-((a^2+a-T)\bmod M).
\]

They obey `1≤r_0≤a` and `a+1≤r_1≤2a`, respectively, with the same prescribed norm residue.  `mock_update_congruent` checks compatibility of successive states when `T` is multiplied by four.

`every_stream_has_mock_path` assembles these into an infinite path for **any** prescribed bit stream, including the all-zero stream.  `not_finiteResidueExclusion` explicitly refutes the claim that this abstraction excludes even one stream once `a≥M`.

**Scope.**  These are mock paths of the stated abstraction.  They need not have the true initial remainder or satisfy the exact integer remainder recurrence.  The theorem does not refute a reachability invariant, a state-dependent growing modulus, or additional inequalities retaining the exact carry information.

**Disposition.**  Retire this fixed-modulus filter.  It sharpens the existing carry-state warning; it is not a new campaign reopening the old Axiom C/T routes.  Reopening requires an invariant of the actual reachable integer states that rejects these controls and forces word visits.  The named target is `ExactRemainderWordSupply`.

## 3. Prime splitting of the norm: automatic for every numerator

**Attraction.**  Factor the norm residual `2Q²−P²` for `Q=2^n`.  Could the allowed prime factors distinguish the actual prefix from a word-avoiding candidate?

The elementary test does not.  `norm_root_automatic` proves over any field that

\[
Q\ne0,\qquad P^2-2Q^2=0
\quad\Longrightarrow\quad (P/Q)^2=2.
\]

In a field modulo an odd prime dividing the residual, the denominator `2^n` is invertible.  Thus the square-root-of-two condition is already implied by the definition of the residual, for **every** numerator.  `NormSplittingFilter` states this test and `every_candidate_passes_splitting` proves it universally for nonzero denominators.

**Disposition.**  The splitting-only filter is vacuous.  This does not dismiss estimates about the size, multiplicities, or correlations of norm factors.  Reopening needs such an additional constraint tied to a missing word, together with an explanation of why it is not automatic for every candidate numerator.  Factorization alone supplies none.

## What changed

The finite-witness limitation from the ln(2) screen now has an exact analogue for √2: the Pell optimum is the original dyadic error, attained at an explicit index.  The other controls prevent two elementary arithmetic disguises from being offered again as promising mechanisms.  No result here establishes even one new infinite digit-recurrence property of √2.

All three findings have individual `Maze.register` rows and declaration links in `MazeAudit.lean`.  The two supply definitions remain unproved research inputs, not axioms or assumptions of the proved controls.
