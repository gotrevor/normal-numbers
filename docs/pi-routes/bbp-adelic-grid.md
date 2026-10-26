# What finite 2-adic precision buys at the genuine BBP denominator

The backward BBP identity suggested supplementing the real head recurrence with 2-adic information.  This pass proves a precise limitation of extracting finite congruences from that information.  It does not close every possible use of the infinite backward identity.

The declarations below are in `src/NormalNumbers/PiDisjunctiveRoutes/BBPAdelicGrid.lean`, namespace `NormalNumbers.PiDisjunctiveRoutes.BBPAdelicGrid`.

## The proved comparison

Write \(H_n\) for the genuine rational BBP head and \(D_n\) for its actual reduced denominator.  Fix **any** precision schedule \(K:\mathbb N\to\mathbb N\) and any finite prefix length \(N\).  Set

\[
E_n=2^{K(n)}/D_n.
\]

`rational_grid_comparison` proves that there are a rational number \(x\) and a rational head sequence \(Q_n\) with all of the following properties:

- \(x\) is not disjunctive in base 16.
- \(Q_n=H_n\) for every \(n\le N\), including the zero seed.
- The reduced denominator of \(Q_n\) divides \(D_n\).
- \(|Q_n-H_n|_2\le 2^{-K(n)}\).
- \(|Q_n-[16^n x-16^n\piTail(n)]|<E_n\), using the **same genuine BBP tail**.
- \(|Q_{n+1}-16Q_n-16B(n)|<E_{n+1}+16E_n\), using the **same genuine BBP kick**.

The Lean statement expresses the 2-adic bound as `padicNorm 2 (2^K(n))`; it makes no assumption that the backward sum-zero identity has been proved.  Its proof does not depend on that frozen theorem.

No decay of \(E_n\) is asserted for an arbitrary schedule \(K\).  The comparison preserves denominator divisibility, not equality of reduced denominators or every odd-prime pole.  The recurrence has the displayed error; it is not the exact BBP recurrence.  There is no single fixed rational head that agrees with the genuine head at **all** 2-adic precisions: the theorem allows a new comparison sequence for each schedule.

## Why the comparison exists

At a fixed denominator \(D\), prescribe the numerator class \(a\bmod M\).  Its possible rational values are

\[
\frac{a+Mm}{D},\qquad m\in\mathbb Z.
\]

Their real spacing is \(M/D\).  Floor rounding approximates every real target to strictly less than that spacing (`exists_congruence_grid_close`).  If \(p\nmid D\), the same choice satisfies \(|q-a/D|_p\le |M|_p\) (`congruence_grid_padic`).

The genuine BBP head has odd denominator, proved as `bbp_head_den_odd`.  Thus \(M=2^K\) gives the required real/2-adic comparison at the actual denominator budget (`bbp_head_grid`).  Choose a rational target sufficiently close to pi to retain the finite prefix, then round each later head on its congruence grid.  The recurrence error is the difference of two adjacent head errors.  The rational target is the known-false control for disjunctivity; its failure is part of the Lean theorem.

## Consequence for the research direction

At these stated tolerances, finite 2-adic precision, actual denominator budgets, and finite exact data cannot force disjunctivity.  This narrows the possible use of the backward identity.  A successful argument must use more than this comparison retains: for example, an exact relation across all indices that forces visits to real digit intervals.

The already-proved rigidity of the exact recurrence and zero seed only identifies the genuine sequence.  Identifying it is not a digit-visitation estimate.  This remains the central unsolved step; pi disjunctivity has not been proved.

The next research direction is to use the rational-function forcing globally, including its pole structure, rather than infer real escape from finite congruences alone.  No theorem asserting that this will work is being assumed.
