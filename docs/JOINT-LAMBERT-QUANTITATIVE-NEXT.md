# More synchronized words from a smaller prime pool

**29 September 2026.  Research derivation by Ren (OpenAI Codex), not yet formalized.**
The qualitative theorem is already proved in `JointLambertUnconditional.lean`.
This note proposes the next mathematical target and supplies its paper argument.
Confidence in the argument after self-review: 90%.  No priority claim or outreach task.

## Target

Fix a finite set S of integer bases at least 2 and one nonempty valid word w_b
for each b in S.  Let A_w(N) count offsets 0 <= n < N at which every word starts
simultaneously in its corresponding E_b.  Offset n means digit n+1; a word may
extend past digit N.  The bases and words are fixed BEFORE C and N_0 are chosen.

Proposed unconditional bound, for every N >= N_0:

    A_w(N) >= N exp(-C (log log N)^2 log log log N),    C > 0.

Choose N_0 large enough that all three logs are positive.  In particular, for
every epsilon > 0, eventually A_w(N) >= N^(1-epsilon).  This neither gives a
positive limiting frequency nor asserts normality.  The displayed bound is
stronger than the original draft's N exp(-C (log log N)^3).

The substantive change is to split the tail into THREE ranges and pay a
divisor-count penalty in the middle range.  This permits the congruence primes
to be polynomial in the killed-window length k, instead of polynomial in log X.

## 1. First repair: the old quantitative target does not require full AGP

`exists_pointwise_exponential_distribution` in `JointLambertAGPRange.lean` gives constants
gamma,C_0 > 0 and, at every sufficiently large integer X, a P equal to 1 or a
prime, chosen BEFORE B and u, such that for B <= X^(1/3), (B,P)=(u,B)=1:

    |pi(X;B,u) - pi(X)/phi(B)| <= C_0 X exp(-gamma sqrt(log X)).

Combined with ordinary PNT, it supplies pi(X;B,u) >= X/(2 phi(B) log X)
whenever C_0 phi(B) log X exp(-gamma sqrt(log X)) <= 2/5.
For the original paper schedule log B = O((log log X)^3), this error tends to
zero.  Remove P from the prime pool if it is present; at most one prime is lost.
There is no need for P > log X.  The handoff's claim that the quantitative
consumer needs uniformity in the base and hence AGP was unjustified: the bases
are fixed in both the qualitative and quantitative statements.

Do not confuse the paper schedule with the completed Lean schedule
X=2^(4k^12), which deliberately sacrifices counting efficiency.  An existence
theorem that returns some k >= K also supplies no upper bound on that k.
The next proof must work for every sufficiently large chosen height X.

## 2. An elementary average without coprimality

For positive u,A and H >= 1, assume u+mA <= H^2 for every m < M.  Put g=gcd(u,A).
Then

    sum_{m<M} tau(u+mA)
      <= tau(g) [2M(1+log H)+2H]
      <= tau(A) [2M(1+log H)+2H].                 (1)

Proof: u'=u/g and A'=A/g are coprime, and u+mA=g(u'+mA').
The elementary inequality tau(xy) <= tau(x)tau(y) follows prime by prime from
e+f+1 <= (e+1)(f+1).  Apply the existing coprime progression estimate to u',A'
using the SAME H, since u'+mA' <= u+mA <= H^2.  Finally g divides A, so tau(g)
<= tau(A).  No coprimality of g and A/g is claimed or needed.

Permanent finite controls for the future Lean module:

- M=0: the sum is zero; u=0 and A=0 are excluded explicitly.
- u=1,A=4,M=3: tau(1)+tau(5)+tau(9)=1+2+3=6, and g=1.
- u=6,A=12,M=3: tau(6)+tau(18)+tau(30)=4+6+8=18.
  Here g=6 and the reduced progression is 1,3,5, with divisor sum 5.
  The submultiplicative bound is 18 <= 4*5=20, not an equality;
  gcd(g,A/g)=gcd(6,2)=2.  This catches an erroneous multiplicativity step.

## 3. Small primes, same encoder and CRT

Use the proved encoder once to fix a>=2, r>=1 and a positive margin delta
inside all the word cylinders.  Fix a common multiple c>=2 of the bases.
All implied constants may depend on these fixed data.  As integer X grows set

    k = ceil(4 log_2(log X)),     L = k^3.

Eventually L/log L >> k^2.  Ordinary PNT supplies the O(k^2) distinct primes
needed in (L,2L), even after removing P(X).  Use the existing arithmetic
construction, with no change to any digit or divisor-count contract:

    t = sum_{0<=j<k, j!=r}(j+1) <= k^2,
    Q = q^(a-1),
    B = q product_{j,t} p_{j,t}^c,
    A = QB = q^a product_{j,t} p_{j,t}^c,
    n_m=R+mA,   n_m+r=Q(u+mB).

Its size bounds are now

    log B <= (1+c k^2) log(2k^3) = O_c(k^2 log k),
    Q <= (2k^3)^(a-1),
    tau(A) = (a+1)(c+1)^t <= (a+1)(c+1)^(k^2).     (2)

The exact expression for tau(A) uses all allocation primes being distinct.
Equation (2), rather than tau(A) <= A, is the useful middle-tail estimate.

The installed prime estimate applies: log B + log log X - gamma sqrt(log X)
tends to minus infinity, and B <= X^(1/3) eventually.  For M=floor(X/B)+1 it
gives at least M/(4 log X) prime indices.  The same prime survivor prescribes
every base at once.  No prime-tuple or independence assumption is introduced.

## 4. The three tail ranges

Let Y=2QX and J=floor((log_2 X)^2).  Eventually k<L<J, every n_m+j for
m<M,j<J is at most Y, log Y=O_a(log X), and sqrt(Y)=o(M):

    B sqrt(Q/X) -> 0

by (2).  Use H=ceil(sqrt Y) in (1).  For T_m=sum_{j>=k} tau(n_m+j)2^(-j):

**Near: k <= j < L.**  The CRT still guarantees gcd(R+j,A)=1, because every
allocation prime exceeds L.  Existing divisor averaging gives

    sum_m sum_{k<=j<L} tau(n_m+j)2^(-j) = O_a(M log X 2^(-k)).

**Middle: L <= j < J.**  Coprimality may fail.  Equation (1) gives instead

    sum_m sum_{L<=j<J} tau(n_m+j)2^(-j)
       = O_a(M tau(A) log X 2^(-L)).

After division by the candidate scale M/log X, the two error bounds are

    O((log X)^2 2^(-k)) -> 0,
    O((log X)^2 (a+1)(c+1)^(k^2) 2^(-k^3)) -> 0.   (3)

For the first, 2^k >= (log X)^4.  For the second take logs: the exponent is
at most O_a(1) + 2 log log X + k^2 log(c+1) - k^3 log 2, which tends to
minus infinity since log log X <= k log 2/4.  The constants c,a are fixed.

**Far: j >= J.**  From n_m<Y and tau(n)<=2 sqrt(n),

    sum_m sum_{j>=J} tau(n_m+j)2^(-j)
       = O(M (sqrt Y+sqrt J) 2^(-J)).

Eventually Y <= 2^J, so this is O(M 2^(-J/2)); multiplied by log X/M it
also tends to zero.  This is the original elementary far-tail estimate,
now used only after J rather than directly after L.

Thus sum_m T_m = o(M/log X).  Markov at the FIXED threshold 2 delta discards
o(M/log X) indices.  At least M/(8 log X) prime indices survive eventually.
For all bases b>=2 their actual digit remainder is bounded by T_m/2 < delta.
The existing floor/carry bridge reads the prescribed words at n_m.

## 5. Every large N, not only chosen scales

For integer N sufficiently large, define

    k_N = ceil(4 log_2(log N)),
    D_N = 2(2 k_N^3)^(a-1),
    X = floor(N/D_N).

Then X tends to infinity, log X ~ log N and k_X <= k_N.  Choose P(X), the pool
and the CRT data only AFTER this X is fixed.  Equation (2) gives
Q <= (2 k_X^3)^(a-1) <= D_N/2.  Every selected prime p<=X yields

    1 <= n_m = Qp-r < QX <= N/2.

Distinct m give distinct starts because A>0.  The count therefore is at least

    X/(8B log X) >= N exp(-C (log log N)^2 log log log N)

after increasing C and N_0: log D_N=O_a(log k_N), log B=O_c(k_N^2 log k_N),
log log X=O(log log N), and the floor in X costs at most a factor 2 eventually.
This proves the proposed bound on paper.  The weaker cubic-log target follows
immediately.  Neither bound is yet a Lean theorem.

## 6. Formalization plan and stopping condition

First prove (1), `tau` submultiplicativity, and the explicit (2) bound in an
additive module.  Then expose prime selection for EVERY sufficiently large X,
with L=k^3 and the explicit `jointB_le` bound, not the old loose 2^(k^4) bound.
Keep the CARDINALITY of the good set after Markov; do not immediately extract
one witness as the qualitative proof does.  Assemble the three tail ranges,
the injection to word starts, and finally the all-N conversion in section 5.

Freeze the count as a filter of `Finset.range N` using the exact floor predicate
in `JointWords`.  Include controls for the empty base set (count=N), {2,4},
leading-zero words and the n+1 digit convention.  Constants depend on the fixed
bases and words; no uniform-in-bases statement is requested.

Preserve all existing JointLambert Lean modules and their qualitative theorem.
New implementation goes in new modules and the root import.  A bounded first
treadmill should attack the gcd average and quantitative prime-supply contract,
not AGP.  No treadmill is launched by this document.  The endpoint is the
displayed all-N count, or a precise refutation of a step of this proposed route.

## 7. Literature checked, as mathematical context

- [Vandehey, 2012, Proposition 2.1](https://arxiv.org/html/1206.0340v1):
  the AGP consequence used in the older scalar argument; its larger modulus
  range is not needed at either schedule above.
- [Campbell, 2026](https://arxiv.org/abs/2605.24160): recurrence of binary `11`.
- [CaptainSude's scalar disjunctivity paper](https://github.com/CaptainSude/erdos-borwein-disjunctivity/tree/bd98789a177470cc4b3e33e6769e859f6144c906),
  `paper/erdos-borwein-disjunctivity.tex`, Theorem 1 and proof steps 1-3:
  the cubic-log count, primes near (log X)^2 and a two-range tail.  That source
  was read locally at the pinned revision.  The present argument retains its
  congruence construction and candidate-count subtraction, while changing
  the pool and adding the non-coprime middle range.

A targeted search did not establish a matching simultaneous or sharper count
result.  That is a search limit, not a claim of novelty.  The result and its
proof belong in the repository; checking priority is not a prerequisite to
pursuing or recording the mathematics.
