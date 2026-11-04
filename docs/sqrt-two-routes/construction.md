# Continuing the Pell route toward √2 disjunctivity

The route is reopened at its unresolved construction.  We have proved the coefficient scale needed for interior word visits and a representation theorem attaining that scale.  We also have a finite integer certificate for each proposed word visit, with proved transfers in both directions between uniform certificate supply and disjunctivity.  **The uniform supply is still unproved.**

This continuation follows the [initial screen](screen.md) and the distinction in [MAZE.md](../../MAZE.md): a useful equivalent formulation remains a route toward the goal.  The new work examines what its coefficients must do.  All declaration names below are in `NormalNumbers.SqrtTwoRoutes`.

## The norm identifies the necessary scale

For any integers `u,v` at any adjacent Pell pair, put

\[
P=up_n+vp_{n+1},\qquad Q=uq_n+vq_{n+1},\qquad
D=u^2+2uv-v^2.
\]

[`pell_linear_combination_norm`](../../src/NormalNumbers/SqrtTwoRoutes/NormScale.lean) proves

\[
P^2-2Q^2=(-1)^nD.
\]

Suppose `Q=2^m` and the signed residual `θ=Q√2−P` lies in `[a,1]`, where `a≥0`.  Factoring the norm gives

\[
|D|=\theta(P+Q\sqrt2)\ge aQ.
\]

This is `pell_dyadic_norm_lower`.  The elementary upper bound `|D|≤(|u|+|v|)²` is `pell_coefficient_norm_bound`; their composition, `pell_dyadic_coefficient_growth`, gives

\[
\boxed{(|u|+|v|)^2\ge a\,2^m.}
\]

For a fixed interval away from zero, this forces coefficient growth at least on the `√(2^m)` scale.  More directly, `pell_dyadic_bounded_norm` proves `a·2^m≤K` whenever `|D|≤K`.  A fixed norm budget therefore bounds the possible exponent scale for interior visits.  This conclusion allows the norm to grow; it does not retire the general Pell construction.

## A construction attains the same exponent of growth

[`balanced_pell_coefficients`](../../src/NormalNumbers/SqrtTwoRoutes/Balanced.lean) proves that for **every** integer `Q≥1` and integer `P` with `|P−Q√2|≤1`, there is an index `n≥1` such that

\[
q_n\le\sqrt Q<q_{n+1},\qquad
|u|\le4\sqrt Q,\qquad |v|\le4\sqrt Q,
\]

where `u,v` are the explicit synthesis coefficients from the screen.  Thus their sum is at most `8√Q`.  For residuals in a fixed interior interval, the necessary and sufficient growth scale is `√Q`; these constants are not asserted optimal.

The construction chooses the Pell pair crossing `√Q`.  The recurrence gives `q_{n+1}≤3q_n`, and the norm gives `|p_n−q_n√2|≤1/q_n`.  Writing the coefficients in terms of the target error then yields the two bounds.  This is a representation theorem for a `P` already within one unit of `Q√2`.  It does not yet select an exponent whose residual falls in a prescribed word interval.

## The remaining target uses only integers

[`PellWordCertificate`](../../src/NormalNumbers/SqrtTwoRoutes/WordCertificate.lean) takes a word length `L`, a word value `A<2^L`, an exponent `m`, a Pell index `n`, and coefficients `u,v`.  Set

\[
Q=2^m,\qquad S=2^L,\qquad P=up_n+vp_{n+1}.
\]

The certificate consists entirely of integer equalities and inequalities:

\[
\begin{gathered}
n\ge1,\qquad q_n^2\le Q<q_{n+1}^2,\qquad
uq_n+vq_{n+1}=Q,\\
u^2\le16Q,\qquad v^2\le16Q,\qquad P\ge0,\\
(SP+A)^2<2(SQ)^2<(SP+A+1)^2.
\end{gathered}
\]

`pellWordCertificate_orbit_mem_Ioo` proves that these inequalities force

\[
\{2^m\sqrt2\}\in\left(\frac A{2^L},\frac{A+1}{2^L}\right).
\]

The open statement `PellWordCertificateSupply` asks for such a certificate for every `L,A`.  `pellWordCertificateSupply_implies_disjunctive` proves its implication to binary disjunctivity.  `pellWordCertificateSupply_of_disjunctive` proves the converse, so the square-root coefficient bounds and strict interval conditions do not lose the goal.  For each fixed exponent, the index and coefficient bounds leave a finite search; termination over exponents for every word is the unresolved part.

**The construction still needed:** given arbitrary `L,A`, produce an exponent and a bounded coefficient pair satisfying the denominator equation and the two square inequalities.  The balanced representation controls size after a near-integer target is chosen.  Neither the norm identity nor that representation theorem supplies the word-selection step.  Congruences alone and fixed-norm unit recipes did not supply it in this pass.  There is no claimed unconditional proof of `PellWordCertificateSupply`.

## Controls and disposition

[`Controls.lean`](../../src/NormalNumbers/SqrtTwoRoutes/Controls.lean) checks both ends of the binary alphabet: `00` at shift seven uses `(n,u,v)=(3,4,9)`, and `11` at shift one uses `(1,2,0)`.  Replacing `00` by `01` in the first certificate is rejected.  These are known-answer checks on the certificate's meaning and signs, not numerical evidence for uniform supply.  The coefficient norm sign is checked separately at `(P,Q)=(181,128)`.

The original Pell Maze row now records this continuation as `.wall`, with the new theorem references and the precise supply target.  The initial exact-cost equivalence remains true.  The finite-residue and splitting-only findings remain scoped to their stated mechanisms.  Further work should address the integer word-supply construction, keeping the demonstrated coefficient growth rather than searching for uniformly small coefficients.

The next [exponent-selection discovery lap](exponent-selection.md) tested two concrete arithmetic selectors.  It found a wrong-word control for complete residue periods and a numerator-independent divisibility identity for the index lift.  Neither provided the missing uniform construction; their individual dispositions are recorded separately in the Maze.
