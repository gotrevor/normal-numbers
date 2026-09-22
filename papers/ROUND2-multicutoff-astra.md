# Pair A, Astra: unequal-cutoff joint transfer

Author: astra-multicutoff.  Round: 2026-09-22.

**Status: paper-proved and independently refereed within Pair A.**
Fable accepted Sections 4-5 and 8 in message
`20260922T202504Z-fable-multicutoff-3e221a0b-9747-490c-8209-f652da8e16ca.md`;
Astra checked Fable's companion schedule and the corrected finite ledger.
No Lean implementation or new campaign has been launched.  The two-tier
construction below gives a genuine joint saving and a schedule for the
explicit Part VI barrier set.  Section 8 generalizes only after that saving:
its geometric cutoffs give a paper proof for every relative-density-zero
prime set with divergent reciprocal sum.  The exact new finite lemma is
Sections 3-5, not an assumed independence of site marginals.

## 1. Source declarations and the restriction being replaced

Read `prime-model-assembly-2026-09-22.md`, including Part VI, and:

- `PrimeModelKMTFixedH.windowMean_sub_windowMeanLe_le_h`, whose underlying
  `sum_omegaGt_shift_le` is the per-site arithmetic estimate used below;
- `PrimeModelFamilyConsumer.FreshMassZero` and its consumer;
- `PrimeModelParameters.Regime`: the existing wrapper imposes
  `1/log log N < epsilon <= 1/(7680 J)`;
- `PrimeModelJointLaw.empLaw_lower_atom`, `joint_phase_error`;
- `PrimeModelRadicalState.retainedBox_card_le`, `state_model_density`;
- `PrimeModelRadicalMoment.radical_box_tail_exp20`,
  `radical_moment_budget`, and the prime reciprocal block bound
  `PrimeModelPrimeDimension.block_le_eight`;
- `PrimeModelBrunCount.brun_remainder_le_square` and
  `PrimeModelBrunLower.Dimension`.

The existing joint argument has three logically separate pieces: lower
bounds on state atoms, model mass outside a retained box, and the number of
retained atoms.  We preserve that architecture but construct new lower
weights.  Using the old dimension bound with dimension J and largest
cutoff y_head would still require `log R >= 1920 J log y_head`.
Changing only radical thresholds does not remove that restriction.

The negative inventory `Maze.lean` includes the full-incidence fixed-power
cutoff obstruction.  Our largest cutoff exponent tends to zero, so the
argument below does not assert that refuted approximation.

## 2. Finite definitions and the phase-transfer leg

Let N,J,m be integers, `1 <= m <= J`, and let integer cutoffs satisfy

    max(2J, 8) <= y_tail <= y_head <= N.

Sites are j=1,...,J.  Write `e(t)=exp(2 pi i t)`, `z_j=e(h/4^j)`,
`a_j=|z_j-1|`, and `B_h=4 pi |h|/3`.  Then

    a_j <= 4 pi |h| 4^(-j),       sum_j a_j <= B_h.

This deliberately uses the repository's loose phase constant.  Set y_j to
y_head for j<=m and y_tail otherwise.  Let W be the ordinary prefix mean
of `product_j z_j^(omega_P(n+j))`, n=0,...,N-1; W_y uses only primes <=y_j
at site j.  Define `S_P(a,b)=sum_(a<p<=b,p in P) 1/p`.

The exact useful finite bound is

    |W-W_y| <= sum_(j=1)^J a_j [2 S_P(y_j,N) + J/N].              (2.1)

Proof: telescope the product and use `|z^(r+c)-z^r|<=c|z-1|`.
For each p<=N the number of hits in an interval of N consecutive integers
is <=N/p+1<=2N/p.  Primes in (N,N+J] each hit at most once, and there are
at most J of them.  No prime above N+J can hit.  This handles the actual
shifted endpoints; the upper endpoint of the fresh sum stays N.

In particular (2.1) is at most

    B_h [2 S_P(y_head,N) + 2*4^(-m) S_P(y_tail,N) + J/N].         (2.2)

## 3. The actual joint model and retained radicals

Put `Q=product_(p<=2J, p prime) p`, so `Q<=4^(2J)`.  All these primes are
below all cutoffs.  Their entire contribution is the unit-modulus function
g_0(n mod Q).  For a prime p>2J define

    I_p={j:p<=y_j},        d_p=|I_p|.

Below y_tail, d_p=J; between y_tail and y_head, d_p=m.  A prime can hit at
most one active site, because p>J.  Its state is either none, of probability
`1-d_p/p`, or a specific j in I_p, of probability `1/p`.  Distinct primes
and the uniform residue modulo Q are independent in the MODEL only.
The true local phase factor is

    1 + A_p/p,             A_p=sum_(j in I_p)(z_j-1).             (3.1)

For state s, let `D_j(s)` be the product of primes assigned to site j.
Retain the box `D_j<=T_j`, with real T_j>=1.  Unique factorization injects
states into the tuple of positive integer radicals, giving

    #box <= product_j floor(T_j).                              (3.2)

At each site the model hit variables over primes are independent
Bernoulli(1/p), for p<=y_j.  At different sites they need not be independent.
The same one-site moment proof as `radical_moment_budget` gives

    E D_j^(1/(2 log y_j)) <= exp(20).

Consequently a union bound, requiring no independence between sites, gives

    model(box complement)
      <= exp(20) sum_j exp[-log T_j/(2 log y_j)].                (3.3)

For a fixed state, A denotes its assigned primes and U its unassigned
primes.  Its joint model atom is exactly

    mu(r,s) = 1/(Q product_(p in A)p) product_(p in U)(1-d_p/p).  (3.4)

The residual sieve must avoid only I_p at p, not all J sites.

## 4. A split lower sieve with explicit constants

This is the new argument.  We give the construction for a finite list of
prime bands, indexed b=1,...,B, each with constant active-site count d_b>=1
and upper endpoint Y_b.  Every prime is >2J, every d_b<=J.  The bands are
disjoint; they need not be fully populated.  Choose integers u_b>=1.

Within band b use the blocks

    (Y_b^(2^(-l-1)), Y_b^(2^(-l))],           l=0,1,...,

intersected with that band and (2J,infinity).  Empty blocks can be omitted;
only finitely many meet the finite prime set.  At the last block the lower
endpoint can be clipped to 2J.  Its upper endpoint is still at most the
square of its lower endpoint.  The prime reciprocal block bound gives

    lambda_(b,l) = sum_(p in block) d_b/p <= 8 d_b.              (4.1)

Also `0<=g_p=d_b/p<1/2`.

For a block set `r=64 d_b+2u_b+2l+4`, an even integer.  With x_p in {0,1},
let E_k(x) be the elementary symmetric polynomial of degree k, and define

    U=sum_(k=0)^r (-1)^k E_k(x),      D=E_(r+1)(x),
    I=product_p(1-x_p).

The elementary Bonferroni inequalities say `U>=I>=0` and `U-D<=I`.
For completeness, with H=sum x_p, the truncated sum at degree r, when H>0,
is `(-1)^r binom(H-1,r)`; when H=0 it is 1.  Thus the inequalities hold
even when r exceeds the number of available primes.

For ALL blocks together define

    L = product_c U_c - sum_c D_c product_(a!=c) U_a.            (4.2)

**Pointwise lower property.**  Product telescoping with `0<=I_c<=U_c`
gives `product U-product I <= sum_c (U_c-I_c) product_(a!=c) U_a`.
Since `U_c-I_c<=D_c`, (4.2) is <=product I.  This avoids the invalid step
of multiplying lower minorants, which can both be negative.

**Coefficient property.**  In `product U`, a monomial selects <=r_c primes
from each block.  In a term with D_c it selects exactly r_c+1 from block c,
and <=r_a from every other block.  These support patterns are disjoint,
and uniquely specify the selected set.  Therefore every coefficient of L
is in {-1,0,1}.  No factor equal to the number of blocks is lost here.

**Relative model error.**  Substitute g_p for x_p, put
`V_c=product_(p in c)(1-g_p)` and `delta_c=D_c(g)/V_c`.  Since g_p<1/2,

    V_c >= exp(-2 lambda_c),
    D_c(g) <= lambda_c^(r+1)/(r+1)!,
    delta_c <= exp(2lambda_c) [e lambda_c/(r+1)]^(r+1)
             <= exp(-u_b-l-2).                                (4.3)

Indeed lambda_c<=8d_b and r+1>=64d_b make the bracket <=1/2, using e<4;
`log 2>=1/2` then bounds the logarithm by
`16d_b-(64d_b+2u_b+2l+5)/2 <= -u_b-l-2`.
The expectation of Bonferroni's upper bound is between V_c and V_c+D_c.
This last assertion follows by averaging the pointwise inequalities under
independent Bernoulli(g_p), so it does not require an alternating-series
monotonicity assertion.

Writing `Delta=sum_c delta_c`, we therefore obtain

    L(g) >= product_c V_c [1-Delta exp(Delta)].                 (4.4)

In detail, `product U>=product V`, while each subtracted term is at most
`product V * delta_c * product_(a!=c)(1+delta_a)`.
For TWO bands take u_b=u>=1.  Then

    Delta <= 2 exp(-u-2)/(1-exp(-1)) < exp(-u),
    L(g) >= (1-2 exp(-u)) product_(p in U)(1-g_p).              (4.5)

For arbitrarily many bands numbered b>=1, taking u_b=u+b gives the same
bound, since the additional geometric sum is <1.  All estimates survive
removing the state-assigned primes A from the blocks.

**Product-support budget.**  Each supported monomial selects at most
r_(b,l)+1 primes from a block of upper endpoint Y_b^(2^(-l)).  Since
`sum_l 2^(-l)=2` and `sum_l l 2^(-l)=2`, its prime product is at most R,
where

    log R = sum_b (128d_b+4u_b+14) log Y_b.                    (4.6)

This is an upper bound, deliberately charging r+1 in every block even
though only one block can exceed r.  For two tiers it becomes

    R = y_tail^(128J+4u+14) y_head^(128m+4u+14).               (4.7)

This is the joint saving: the head cutoff is charged m, not J.

## 5. Arithmetic atoms, remainder and the complete finite ledger

For the fixed atom (r,s), first impose the assigned congruences A and n=r
mod Q.  They select one CRT class modulo Q product A.  For E subset U,
impose a hit at every p in E.  At prime p there are exactly d_p distinct
admissible residues.  CRT consequently gives

    count(E) = N/(Q product A) product_(p in E)(d_p/p) + error,
    |error| <= product_(p in E) d_p.                           (5.1)

The absolute error counts admissible residue classes and does not multiply
by Q product A.  Multiply (5.1) by the lower-sieve coefficients and sum.
Their absolute values are <=1 and their prime products are <=R.  Since
`d_p<p`, each summand in the error is <=product E<=R.  Unique factorization
injects E into positive integers <=floor R.  Hence total error <=R^2,
exactly the argument of `brun_remainder_le_square` with variable d_p.

For the empirical joint law nu this proves, for every state atom,

    nu(r,s) >= (1-eta) mu(r,s) - R^2/N,       eta=2 exp(-u).    (5.2)

The usual lower-atom transfer, for every complex test F with |F|<=1, gives

    |E_nu F-E_mu F|
      <= 2 exp(20) sum_j exp[-log T_j/(2 log y_j)]
         + 4 exp(-u) + 2 Q product_j floor(T_j) R^2/N.          (5.3)

One way to check the constant is to sum positive deficits `(mu-nu)_+`:
outside the box they total at most mu(box complement), and inside at most
eta+|box|R^2/N.  The L1 distance is twice the total deficit.

Apply (5.3) to the complete phase, including g_0(r).  Let j_0 be the first
site with `4^j_0` not dividing h.  Suppose j_0<=m in the two-tier case, or
j_0<=J for decreasing many-tier cutoffs.  At every p<=y_(j_0), the active
set includes j_0 and `Re A_p<=-1`; at all primes `Re A_p<=0` and
`|A_p|<=B_h`.  From `|1+w|<=exp(Re w+|w|^2/2)` and
`sum_(p>2J)1/p^2<=1/(2J)`,

    |E_mu F| <= exp[B_h^2/(4J)-S_P(2J,y_(j_0))].              (5.4)

Thus (2.1), (5.3), and (5.4) are an unconditional finite bound.  Unlike
the old wrapper, this statement assumes no `Regime N J epsilon`; its
explicit product R is the actual support budget.  A schedule must pay for
R and the radical box simultaneously.

## 6. Two-tier consumer for the explicit Part VI barrier set

Write `t=L2 N`, `w=L3 N=log t`, `v=L4 N=log w`.  For all sufficiently large
N choose

    J=floor w,    m=floor sqrt(v),    u=m,
    y_head=floor N^(m^-4),    y_tail=floor N^(J^-4),
    T_head=N^(1/(8m)),        T_tail=N^(1/(8J)).                (6.1)

Then 1<=m<=J and the finite cutoff hypotheses hold eventually.  Floors only
reduce log y.  In (4.7),

    log R/log N <= (128J+4m+14)/J^4 + (132m+14)/m^4 ->0.

In particular R<=N^(1/8) eventually.  The retained-state budget is
`T_head^m T_tail^(J-m)<=N^(1/4)`, so the last term of (5.3) is at most
`2*4^(2J)*N^(-1/2)`, tending to zero.  The other two terms are bounded by

    2 exp(20)[m exp(-m^3/16)+J exp(-J^3/16)] +4exp(-m) ->0.    (6.2)

For the explicit prime-index thinning in Part VI, its uniform upper
fresh-mass estimate on these cutoffs is

    S_P(y_head,N) = O(log m/v) ->0,
    S_P(y_tail,N) = O(log J/v) = O(1).

Both exponents exceed 1/L2 N and are <1/2 eventually, so they lie in the
range of the paper's barrier estimates.  Equation (2.2) now tends to zero.
The head accumulated mass is comparable to t/v, whereas
`S_P(2J)<=sum_(n<=2J)1/n=O(log J)`; hence (5.4) tends to zero for every
fixed h.  The ordinary full-tail error also tends to zero, since

    [S_P(2N)+5J+12]/4^J = O((t+w)/t^(log 4)) ->0.

This supplies the paper-level normality conclusion for the explicit
barrier set.  The independent review accepted the finite lemma.
It does not derive any cancellation for the full set of primes.

## 7. Why the saving is real, and its remaining two-tier limitation

The common-cutoff lower sieve would charge `J*m^-4` in log R/log N; this
diverges for J~w and m~sqrt(log w).  The split sieve charges
`J*J^-4+m*m^-4`, which tends to zero.  This is a change in the JOINT error,
not another tuning of the old epsilon majorant.

For a much slower density decay, a fixed two-tier architecture can still
leave incompatible demands: suppressing the universal tail fresh sum
requires m to grow, while a large head window can consume the very slow
density gain.  The geometric extension below is justified by the proved
two-tier saving and uses the same lower-weight construction.

## 8. Geometric many-tier consumer, including arbitrary slow divergence

Theorem, with a complete paper proof and paired review:

    pi_P(x)/pi(x) ->0 and sum_(p in P)1/p=infinity
      imply IsNormal 4 (subsetLambert P 4).

No effective density rate or divergence rate is assumed.  Let
`S_N=S_P(0,N)`, `w=L3 N`, and `Z_N=exp(sqrt(log N))`.  Define the real tail
envelope over integer x>=ceil Z_N,

    delta_N=sup pi_P(x)/pi(x).

For large N all denominators are positive.  Divergence implies unbounded
prime support, so delta_N>0; relative density zero implies delta_N->0.
Choose eventually-positive integer parameters

    J=min(floor w, floor(S_N/8)),
    u=floor min(sqrt(w), delta_N^(-1/2)),    a=u^(-2),
    y_j=floor N^(a*2^(-j)),                j=1,...,J,
    T_j=N^(2^(-j/2)/16).                                      (8.1)

Both J and u tend to infinity, even for arbitrarily slow reciprocal
divergence.  The choice of rates here is a paper existence
schedule, not a claim of computability from a density-zero predicate.

**Cutoff range.**  Since u^2<=w and J<=w,

    a*2^(-J) >= 1/(w*t^(log 2)),       t=L2 N.

The right side is much larger than `1/sqrt(log N)=exp(-t/2)`.
Thus the smallest integer cutoff y_J is >=ceil Z_N and >=max(2J,8)
eventually.  All density estimates below apply on every required interval,
including the N+1 or 2N+1 endpoint from dominated Abel summation.

**Joint sieve.**  Use bands `(y_(b+1),y_b]` with d_b=b, b=1,...,J-1,
and bottom band `(2J,y_J]` with d_J=J.  Empty bands are harmless.
Take u_b=u+b.  Equations (4.3)-(4.6) yield eta<=2exp(-u) and

    log R/log N
      <= a sum_(b=1)^J (132b+4u+14) 2^(-b)
      <= a(278+4u) ->0.                                      (8.2)

Hence R<=N^(1/8) eventually.  Also

    sum_j log T_j/log N
      <= (sqrt(2)+1)/16 <1/4.                                (8.3)

The joint CRT remainder is again <=`2*4^(2J)*N^(-1/2)`, tending to zero.

**Discarded radicals.**  Since log y_j<=a*2^(-j)*log N,

    log T_j/(2 log y_j) >= u^2 * 2^(j/2)/32.

The sum of these exponential tails tends to zero independently of J.
For example `2^(j/2)>=(1+j/4)` bounds the sum by

    exp(-u^2/32)/(exp(u^2/128)-1) ->0.                         (8.4)

Thus the entire joint error (5.3) tends to zero.

**Fresh mass with its actual phase weights.**  Floors give
`log y_j >= (a*2^(-j)*log N)/2` eventually, uniformly for j<=J.
The existing dominated-Abel inequality, for M=N or 2N, therefore gives

    S_P(y_j,M)
      <= delta_N [9+12 log(log M/log y_j)]
      <= delta_N [9+12 log 4+24 log u+12j log 2].              (8.5)

Multiplying by a_j<=4pi|h|4^(-j) and summing uses
`sum 4^(-j)=1/3`, `sum j4^(-j)=4/9`.  The transfer is at most
`C_h delta_N(1+log u)+B_h J/N`, tending to zero, since
`log u<= (1/2)log(1/delta_N)` eventually.

**Model contraction without a divergence rate.**  For fixed h and its
first nontrivial site j_0, eventually j_0<=J.  Equation (8.5) at j_0
shows `S_P(y_(j_0),N)=o(1)`.  Since J<=S_N/8,

    S_P(2J,y_(j_0))
      >= S_N-o(1)-(1+log(2J))
      >= 8J-1-log(2J)-o(1) ->infinity.                        (8.6)

This proves (5.4) tends to zero.  In particular no unproved statement
that S_P(N^epsilon) grows at a fixed rate was inserted.

**Infinite phase tail.**  Dominated Abel on (N,2N] gives
`S_P(N,2N)=O(delta_N)=o(1)`.  If J=floor(S_N/8), then
`S_P(2N)<8J+8+o(1)`, and the existing tail numerator divided by 4^J
tends to zero.  If J=floor w, use the universal mass bound
`S_P(2N)<=12 L2(2N)+21`, and `4^J>=t^(log 4)/4`.
Again the ratio tends to zero.  Ties satisfy either case.

Together the window mean tends to zero for each fixed nonzero integer h,
and the repository's existing ordinary-prefix tail and Weyl wiring give
the theorem.  These are ordinary prefix means for every large
N, not logarithmic averages or a subsequence.

## 9. Independent-review targets and handoff

Fable checked and accepted each of these load-bearing points:

1. The sign and coefficient support of the product upper-minus-defects
   construction (4.2).  This is where multiplying two negative lower
   weights would have invalidated the argument.
2. The relative defect estimate (4.3), including the finite last blocks.
3. CRT with variable active-site counts and assigned primes removed;
   the remainder must stay R^2 per atom, with no hidden factor Q product A.
4. The uniform floor and density-envelope range in (8.5), and the
   mass-dependent J in (8.6) for arbitrarily slow divergence.

No numerical probe is needed for these identities.  No assertion in this
note relies on a transient numerical test.  The paired review is complete.  Formalization still requires explicit
launch authorization; none has been given in this session.


## 10. Abstract weighted-freshness consumer and the prime-burst example

The density envelope is only one way to choose u.  More generally take
any integer u_N->infinity with u_N<=sqrt(L3 N), and use (8.1) with
`J=min(floor L3 N,floor S_N/8)`.  If

    F_N=sum_(j=1)^J 4^(-j) S_P(y_j,2N) ->0,                   (10.1)

then the same proof gives normality.  The joint ledger (8.2)-(8.4) uses no
density assumption.  Transfer is bounded by a fixed-h constant times F_N;
for each fixed j_0, `S_P(y_(j_0),N)<=4^(j_0) F_N`, yielding (8.6).
Also `S_P(N,2N)<=S_P(y_1,2N)<=4F_N`, which is all the mass-limited tail
branch needs.  Thus (10.1) is the actual hypothesis of this consumer.

For the assembly paper's prime-burst example, set u_N=floor sqrt(L3 N).
Recall its blocks in t=L2 x coordinates start at `t_n=exp(n^2)` and have
length 1/n and reciprocal mass O(1/n); their prime-density limsup is 1.
For our entire largest fresh interval (y_J,2N], in t=L2 N coordinates,

    L2(2N)-L2(y_J) <= 2 log u_N+J log 2+O(1)=O(log t).

For all large t the interval therefore meets at most one burst.  To see
this quantitatively, successive starts have exact gap

    t_(n+1)-t_n=exp(n^2)[exp(2n+1)-1],

which is much larger than log t_(n+1)=(n+1)^2.  An interval of length
C log t containing both starts would have t close to t_(n+1), and would
contradict that gap.  The tiny burst widths and rounding errors do not
change the conclusion.  If a burst is met its index tends to infinity,
since the left endpoint in t coordinates tends to infinity.  Consequently
`S_P(y_J,2N)<=C/n` there, and F_N<=C/(3n)->0; when no burst is met F_N=0.
The geometric consumer therefore also covers the prime-burst example.

For this application u is chosen directly, not from the density envelope:
that envelope is identically 1 for this example and would not give u->infinity.
The theorem for relative density zero is a sufficient class, not the exact
frontier of the mechanism.  For a set with a genuine positive limiting
relative density, the displayed fresh-mass majorant fails as the first
cutoff exponent tends to zero; that does not prove failure of normality or
of every possible phase-sensitive replacement.


## 11. Continuation: the square-root fresh-mass criterion

Status of this continuation: paper derivation, sent to Fable for independent
review in `20260922T205203Z-astra-multicutoff-baf6f147-dea6-456e-a197-d65a38087f7e.md`.
The earlier pair-reviewed conclusions are unchanged.

Define, with exact natural-number endpoints,

    r_P(N) = S_P(Nat.sqrt N,N),
    SqrtFreshMassZero(P) : iff r_P(N)->0.                      (11.1)

Here Nat.sqrt N is floor sqrt N.  The new claim is

    DivergentRecip(P) and SqrtFreshMassZero(P)
      imply IsNormal 4 (subsetLambert P 4).                    (11.2)

More precisely, assuming DivergentRecip(P), (11.1) is equivalent to the
existence of an integer schedule `u_N->infinity`, `u_N<=sqrt(L3 N)`
eventually, satisfying the weighted-freshness hypothesis (10.1) for our
geometric consumer.  Thus it characterizes that consumer, not normality
itself.  It is also equivalent to vanishing fresh mass on any one fixed
power window `(N^c,N]`, with 0<c<1, and therefore to vanishing on every
such fixed power window.

### 11.1 Exact finite root-chain estimate

Let integers M>y>=2 and Z<=y be given, and suppose

    r_P(q)<=rho       for all integers q>=Z,

with rho>=0.  Then

    S_P(y,M) <= rho ceil(log(log M/log y)/log 2).              (11.3)

Proof: start M_0=M and set M_(l+1)=Nat.sqrt M_l.  Stop at the first L
with M_L<=y.  While l<L, M_l>y>=Z, so
`S_P(M_(l+1),M_l)=r_P(M_l)<=rho`.  The intervals telescope exactly:

    S_P(y,M)<=S_P(M_L,M)=sum_(l<L)r_P(M_l)<=L rho.

No missing prime at the lower endpoint appears: all reciprocal intervals
are open on the left and closed on the right.  Let
`K=ceil(log(log M/log y)/log 2)`.  It is a positive integer, and
`M_K<=M^(2^(-K))<=y`, because rounding the square roots only decreases
them.  Hence L<=K, proving (11.3).  In particular the root-chain endpoints
at which the hypothesis is used are all ABOVE y; the final overshoot below
y is harmless.

### 11.2 Constructing the schedule without a density hypothesis

Assume r_P(N)->0 and DivergentRecip(P).  For large N write w=L3 N and

    Z_N=ceil exp(sqrt(log N)),
    rho_N=sup_(integer q>=Z_N) r_P(q),
    u_N=floor min(sqrt(w),rho_N^(-1/2)).                       (11.4)

The tail supremum is finite for all sufficiently large N and tends to zero,
simply because r_P(q)->0.  It is strictly positive: divergent reciprocal
sum implies unbounded prime support, and for p in P above Z_N,
`r_P(p)>=1/p>0`.  Thus (11.4) is defined and u_N->infinity, even for
arbitrarily slow convergence.  The schedule uses a tail supremum only as
an existence construction, as did the density-envelope argument.

Keep `J=min(floor w,floor S_P(0,N)/8)` and the cutoffs from (8.1):
`y_j=floor N^(u_N^(-2)*2^(-j))`.  Section 8's cutoff calculation is
independent of density, and gives y_J>=Z_N eventually.  Its uniform floor
margin also gives

    log(2N)/log y_j <= 4u_N^2 2^j.

Apply (11.3) with M=2N, y=y_j.  Since ceil x<=x+1,

    S_P(y_j,2N)
      <= rho_N [3+j+2 log u_N/log 2].                         (11.5)

Summing with weights 4^(-j), using the infinite geometric sums,

    F_N <= rho_N [13/9+2 log u_N/(3 log 2)] ->0,               (11.6)

because `log u_N<=(1/2)log(1/rho_N)` eventually and
`rho_N log(1/rho_N)->0`.  The theorem now follows from Section 10, including
its model contraction and both tail branches.  No density estimate was
used in (11.3)-(11.6).

### 11.3 Converse for this weighted consumer

For any admissible schedule with u_N>=1, its first cutoff satisfies
`y_1=floor N^(1/(2u_N^2))<=Nat.sqrt N`.  Once J>=1,

    r_P(N)<=S_P(y_1,2N)<=4 F_N.                              (11.7)

Thus existence of a successful weighted schedule implies (11.1).
This proves the asserted equivalence.  It is not an impossibility theorem
for alternative observables or a necessary condition for normality.

### 11.4 Other fixed powers and the previous theorem

For c in (0,1) define `r_(P,c)(N)=S_P(floor N^c,N)`.
If (11.1) holds, use (11.3) with y=floor N^c.  For large N the chain length
is at most `ceil(log_2(2/c))`, a constant, and every integer endpoint tends
to infinity.  Hence r_(P,c)(N)->0.

Conversely, suppose r_(P,c)(N)->0 for one fixed c.  Iterate the map
`M_(l+1)=floor M_l^c`, starting at M_0=N.  Choose a fixed integer K with
`c^K<=1/2`; then M_K<=N^(1/2), hence the integer M_K<=Nat.sqrt N.
Telescoping gives

    r_P(N)<=sum_(l<K)r_(P,c)(M_l)->0,

since each fixed-iterate M_l tends to infinity.  This also establishes
that changing the square-root cutoff to any other fixed power changes
neither the hypothesis nor its quantifiers.

The old `FreshMassZero(P)` of `PrimeModelFamilyConsumer` implies (11.1):
its `yI(N)=floor N^(floor(L3 N)^(-4))` is <=Nat.sqrt N eventually, so

    r_P(N)<=S_P(yI(N),2N)->0.

The implication is strict for the explicit Part VI barrier set: its
relative density tends to zero, hence (11.1) follows from dominated Abel
on this fixed-power interval, while its old `FreshMassZero` condition fails
by the already-recorded lower fresh-mass estimate.  Thus the inclusion
left open in the first handoff is now proved.

For possible later formalization the hypothesis is exactly

    def SqrtFreshMassZero (P : Nat -> Prop) [DecidablePred P] : Prop :=
      Tendsto (fun N : Nat => recipSumIoc P (Nat.sqrt N) N) atTop (nhds 0)

with the usual real-valued reciprocal sum.  This is a proposed declaration,
not a claim that the Lean theorem has been implemented.

## 12. What the local condition says, and a weaker condition it excludes

In coordinates t=log log x the map x->sqrt x translates t by -log 2.
Thus (11.1) says that the P-prime reciprocal measure of every late interval
of this fixed t-length tends to zero.  By Section 11.4, every other fixed
t-length works as well.  This includes the earlier bursts of mass O(1/n),
although their ordinary prime-density limsup is 1.

It implies the weaker global condition

    S_P(0,N)=o(log log N).                                   (12.1)

For a direct proof, given eta>0 choose a fixed integer Z>=3 with r_P(q)<=eta
for q>=Z.  Applying (11.3) with y=Z gives

    S_P(0,N)<=S_P(0,Z)+eta ceil(log_2(log N/log Z)).

After division by log log N the limsup is <=eta/log 2.  Let eta decrease
to zero.  Finite initial primes do not affect this conclusion.

The converse to (12.1) is false, even for divergent prime sets.  Here is
a precise modification of the assembly paper's burst example.  Let
`t_n=exp(n^2)` and include ALL primes in

    [ceil exp(exp(t_n)), floor exp(exp(t_n+1))].               (12.2)

Each burst now has fixed width 1 in t, rather than width 1/n.  Chebyshev
upper and lower prime-count bounds, followed by Abel summation, give
positive constant lower and upper bounds for each burst's reciprocal mass
for all large n: the integral of 1/(x log x) over the burst is 1, and the
boundary terms are O(1/log a_n).  Thus the reciprocal sum diverges.  Up to
t=L2 N there are O(1+sqrt(log t)) bursts, each of bounded mass, so

    S_P(0,N)=O(1+sqrt(log(L2 N)))=o(L2 N).

But at N_n=floor exp(exp(t_n+1)), the whole interval
`(sqrt N_n,N_n]` lies inside burst n for all large n, since its t-width
is log 2<1.  The same lower Chebyshev-Abel estimate gives

    r_P(N_n)>=c log 2-o(1)>0

for an absolute c>0.  Integer endpoint changes contribute o(1).
Therefore (11.1) fails.  This refutes replacing local fresh-mass decay by
the global estimate (12.1) in our consumer; it makes no assertion about
normality of the constant built from (12.2).
