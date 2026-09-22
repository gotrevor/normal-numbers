# G4: a geometric countermodel to fixed-prefix and tail summaries

Astra, 2026-09-22.  Research-only paper proof; no Lean theorem or arithmetic counterexample is claimed.  Mailbox proposal: `agent-mail/g4/20260922T192658Z-astra-fa74ad3a-c8bf-44c8-9b3e-d96879cd2cb0.md`.

## Result and precise scope

There is a triangular model of nonnegative integer count vectors, with exactly the G4 geometric coefficients and the actual `windowK` schedule, satisfying all of the following:

1. Every fixed prefix approaches independent Poisson counts in total variation.  In particular every fixed nontrivial-window Fourier mean tends to zero.
2. Each singleton has mean-square deviation `(1+o(1)) loglog M`, uniformly over the scheduled sites.  The usual centered geometric-tail estimate follows.
3. The centered whole window, divided by `sqrt(loglog M)`, converges to a normal distribution of variance `1/15`.
4. The limiting phase distribution is invariant under multiplication by 4.
5. Nonetheless the scheduled Fourier means at frequencies `3`, `4`, and `12` have nonzero limits.

This refutes an implication from these **summary properties together** to scheduled cancellation.  It does not refute G4 normality, `EventualPrefixDecay` for the actual omega sequence, or any argument using additional arithmetic information.

The missing structure is explicit: the random coordinates below are not `omega(n+j)` along one fixed arithmetic sequence.  In particular we do not supply exact consistency between overlapping rows or between different scales.  Limiting multiplication-by-4 invariance is preserved, but the exact temporal orbit relation is not asserted.

## 1. Construction and Fourier separation

Let `L = log log M`, `K = windowK M`, and

    R = floor((log_4 L)/4).

For all sufficiently large M, `R >= 1`, `R+2 <= K`, and `R = O(log L) = o(L)`.  Fix `0 < delta < 1`.  Under the reference law Q, let `W_1,...,W_K` be independent Poisson random variables with parameter L, and put

    T = sum_{j=1}^K W_j / 4^j,
    D_R(x) = product_{r=0}^{R-1} (1 + delta cos(2 pi 4^r x)),
    Z = E_Q D_R(T),
    dP/dQ = D_R(T)/Z.

The density is positive.  Its trigonometric expansion is

    D_R(x) = sum_q a_q e(qx),
    q = sum_{r=0}^{R-1} epsilon_r 4^r,  epsilon_r in {-1,0,1},
    a_q = (delta/2)^{#{r : epsilon_r != 0}}.

These representations are unique.  Indeed, in the difference of two representations the largest nonzero digit has magnitude at least `4^s`, whereas all lower digits together have magnitude at most `2(4^s-1)/3 < 4^s`.  Therefore

    a_0 = 1,
    sum_q a_q = (1+delta)^R =: B,
    |q| <= (4^R-1)/3.

For every integer q, independence gives the exact identity

    E_Q e(qT) = exp(L sum_{j=1}^K (e(q/4^j)-1)).                 (1)

If `0 < |q| < 4^K`, put `t = v_4(q)+1`.  Then `t <= K` and `e(q/4^t)` is `i`, `-1`, or `-i`.  Its real part is at most zero, and all other summands in the real part of the exponent are nonpositive.  Consequently

    |E_Q e(qT)| <= exp(-L).                                   (2)

In particular `|Z-1| <= (B-1) exp(-L) = o(1)`.

## 2. Nonzero scheduled means and an invariant phase law

Fix any integer m.  Eventually every nonzero `m+q` occurring in the polynomial satisfies `|m+q| < 4^K`.  Equations (1)-(2) then give

    E_P e(mT) = [a_{-m} + O(B exp(-L))]/Z.                    (3)

Here `a_{-m}=0` when the polynomial has no such frequency.  For fixed m the coefficient stabilizes as R grows: a representation involving a largest digit at s has absolute value at least `(2*4^s+1)/3`, so arbitrarily high digits cannot represent a fixed m.

Let `rho = delta/2`.  The limiting coefficient is `rho^{s(m)}` if m has a finite signed-base-4 expansion using only digits `-1,0,1`, where `s(m)` counts its nonzero digits; otherwise it is zero.  Thus

| m | signed-base-4 representation | limiting mean |
|---|---|---|
| 1 | 1 | rho |
| 2 | none | 0 |
| 3 | -1 + 4 | rho^2 |
| 4 | 4 | rho |
| 12 | -4 + 16 | rho^2 |

For example `delta=1/2` gives limits `1/4, 0, 1/16, 1/4, 1/16` in those five rows.  These values are algebraic consequences of coefficient extraction, not numerical fits.

All Fourier coefficients of the probability laws of `T mod 1` converge.  Compactness of the circle and uniqueness from trigonometric polynomials give a limiting probability measure mu.  Appending a zero digit preserves signed-base-4 representability and the number of nonzero digits.  Conversely a representable multiple of 4 has zero lowest digit.  Hence

    mu_hat(4m) = mu_hat(m) for every integer m.

This is exactly invariance of mu under multiplication by 4.  It is not Haar measure, since `mu_hat(1)=rho>0`.

## 3. Every fixed prefix still has the independent law asymptotically

Fix J, and eventually take `J<K`.  Condition on arbitrary values of `W_1,...,W_J`.  For every nonzero polynomial frequency q, the tail factor obeys

    |E_Q e(q sum_{j>J} W_j/4^j)| <= exp(-c_J L),
    c_J = 1 - cos(2 pi / 4^{J+1}) > 0.                       (4)

To check this uniformly in q, consider `t=v_4(q)+1`.  If `t>J`, its quarter/half-turn site remains in the tail and gives loss at least 1.  If `t<=J`, the residue of q modulo `4^{J+1}` is nonzero, and site `J+1` gives loss at least `c_J`.  The first case has `t<=K` by the polynomial frequency bound.

Expanding D_R and using (4), the conditional density of P relative to the Q-prefix law differs from 1 pointwise by at most

    [(B-1) exp(-c_J L) + |Z-1|]/Z = o(1).                   (5)

Thus prefix total variation tends to zero, for every fixed J.  This is stronger than a joint central limit theorem.

For a fixed integer h and fixed J with `4^J` not dividing h, Q's prefix Fourier mean has modulus at most `exp(-L)`, using the first nontrivial site exactly as in (2).  Equation (5) transfers its vanishing to P.  If `4^J` divides h, the prefix phase is identically one under either law.  So the nontrivial-window threshold is exactly `1+v_4(h)`, including h=4 and h=12.

The convergence rate in (5) depends on J through `c_J`, which shrinks on the scale `16^{-J}`.  It supplies no uniform statement up to K.  That loss of uniformity is real, since (3) exhibits the surviving scheduled bias.

## 4. Uniform singleton control and centered-tail determinism

Fix a singleton index j, now allowed to depend on M anywhere in `1,...,K`.  For each nonzero polynomial frequency q, let `t=v_4(q)+1`.  Both sites t and t+1 lie below K because `|q|<4^R` and `R+2<=K`.  At t the loss is at least 1.  At t+1 the phase is a nontrivial sixteenth root with numerator not divisible by 4, so its loss is at least

    c_* = 1-cos(pi/8) > 0.

Deleting the one coordinate j leaves at least one of these two sites.  Hence the conditional density of the P-singleton law relative to Poisson(L) is, pointwise in its integer value and uniformly in j,

    1 + O(B exp(-c_* L)).                                   (6)

Unlike an unqualified total-variation assertion, this pointwise density comparison controls unbounded nonnegative observables too.  Apply it to `(W_j-L)^2` to obtain

    E_P (W_j-L)^2 = (1+o(1)) L, uniformly in j<=K.

Minkowski's inequality therefore gives, uniformly for `0<=a<K`,

    ||sum_{a<j<=K} 4^{-j}(W_j-L)||_{L2(P)}
       <= (1+o(1)) sqrt(L) (4^{-a}-4^{-K})/3
       <= (1+o(1)) sqrt(L) 4^{-a}/3.                         (7)

Using `|e(x)-e(y)| <= 2 pi |x-y|`, for every integer h this implies

    |E_P e(hT) - e(h L sum_{j>a}4^{-j}) E_P e(hT_a)|
       <= (2 pi |h|/3)(1+o(1)) sqrt(L)4^{-a}.                (8)

The frequency dependence is explicit.  For fixed h, any cutoff with `4^a/(|h|sqrt(L)) -> infinity` makes the error vanish.  In particular the centered-tail reduction survives in precisely its advertised sufficient range, while the nonzero means (3) remain.

## 5. Even the normalized whole-window Gaussian law survives

Write `c_K=sum_{j<=K}4^{-j}`.  For fixed J, (5) and the elementary Poisson central limit theorem imply

    sum_{j<=J}4^{-j}(W_j-L)/sqrt(L)
        converges in law to N(0, sum_{j<=J}16^{-j}).

For completeness, the one-site Poisson assertion follows directly by expanding
`exp(L(exp(iu/sqrt(L))-1-iu/sqrt(L))) -> exp(-u^2/2)`.
Independence under Q gives its finite-vector form, and total variation transfers it to P.

Equation (7), divided by sqrt(L), bounds the discarded normalized tail by `(1+o(1))4^{-J}/3` in L2.  First let M tend to infinity with J fixed, then let J grow.  It follows that

    (T-c_K L)/sqrt(L) converges in law to N(0,1/15).          (9)

This Gaussian law coexists with the nonzero Fourier coefficients in (3).  A fixed nonzero Fourier frequency of T corresponds to a frequency growing like sqrt(L) for the variable in (9); weak convergence supplies no control there.

## 6. Averaging and quantifier audit

- **Ordinary vs logarithmic:** these are probability expectations, with no logarithmic averaging over scales.  They can also be represented by ordinary uniform averages of finite arrays as below.  They are not asserted to be actual arithmetic prefix averages.
- **All vs almost-all scales:** the estimates hold as M tends to infinity through every sufficiently large integer.  No exceptional scale set is used.
- **Fixed vs growing k:** every fixed nontrivial prefix cancels; `K=windowK M` does not.  This explicitly separates the quantifiers.
- **Frequency and threshold:** fixed-prefix triviality is exactly `4^J | h`; (8) retains `|h|`; (3) takes each h fixed before M tends to infinity.  No growing-frequency uniformity is inferred.
- **Resonances:** the nonzero limits at h=3,4,12 are in the table.  The h=2 scheduled mean happens to vanish in this model, so that test alone would miss the failure.
- **No renamed target:** the countermodel is constructed and its limits computed.  No cancellation premise is assumed.
- **Missing arithmetic:** exact overlapping-shift and cross-scale consistency, and an underlying multiplicative function, are not supplied.  The result rejects sufficiency of the summary inputs, not the real G4 conjecture.

To obtain literal ordinary averages, truncate the Poisson support to `0<=W_j<=ceil(2L)` and renormalize.  Under P the removed mass is at most `B/Z` times the Q-mass, which is `O(K exp(-cL))` by a Poisson Chernoff bound.  It tends to zero since B and K grow polynomially or logarithmically in L.  The same bound with polynomial moments preserves (7).  The remaining number of vectors is at most `(ceil(2L)+1)^K = exp(O((log L)^2)) = o(M)`.  Round their probabilities to multiples of 1/M, allocating the residual counts so the total is M.  The total-variation error is at most the number of vectors divided by M; its product with any fixed power of L still tends to zero.  Listing the resulting M vectors with multiplicity realizes (3), fixed-prefix total variation, (7), and (9) by uniform finite averages.  These arrays remain triangular, not overlapping windows of one sequence.

## 7. Exact singleton marginals, not merely asymptotic ones

The singleton approximation can be upgraded to equality without changing any limiting phase coefficient.  Write `w=D_R(T)/Z` and

    u_j(W_j) = E_Q(w | W_j)-1,
    w_* = w - sum_{j=1}^K u_j(W_j).

Each `u_j` has Q-mean zero.  The coordinates are independent under Q, so `E_Q(w_* | W_i)=1` for every i: the i-th subtraction cancels its conditional discrepancy and the others have conditional mean zero.  Also `E_Q w_*=1`.

Positivity is preserved for all sufficiently large M.  Indeed `w >= (1-delta)^R/Z`, whereas (6) gives

    sup |w_*-w| <= K O(B exp(-c_*L)) = o((1-delta)^R/Z).

Thus `w_*` defines a probability measure P_* with **exactly** Poisson(L) singleton marginals, and `||P_*-P||_TV=o(1)`.  The fixed-prefix laws and limiting phase coefficients survive.  The tail bound now has the exact constant

    ||sum_{j>a}4^{-j}(W_j-L)||_{L2(P_*)}
       <= sqrt(L) (4^{-a}-4^{-K})/3,

because each singleton variance is exactly L.  The argument for (9) applies unchanged.

## 8. The same construction with exact arithmetic singleton laws

One may replace Poisson(L) under Q by the exact distribution of `omega(U)`, with U uniform on `1,...,M`, taking independent copies across sites.  The only analytic inputs needed are the usual one-site root-of-unity decay, variance `L+O(1)`, and the one-site central limit theorem.  A primary reference is Féray, Méliot and Nikeghbali, [arXiv:1304.2934v4, section 7.2.1, Proposition 7.4](https://arxiv.org/pdf/1304.2934): its uniform Selberg-Delange formula gives `|E z^{omega(U)}| <= C exp(-(1-Re z)L)` for `|z|=1`.  The additive error form of Proposition 7.4 is sufficient, including at z=-1; no division by a vanishing leading constant is used.

The products in the preceding proofs still factor under Q.  At the first nontrivial site there are only the three roots `i,-1,-i`, so (2) becomes `C exp(-L)`.  For singleton deletion, the surviving site is among finitely many sixteenth roots and gives `C exp(-c_*L)`.  For a fixed prefix J, use the finitely many `4^{J+1}`-th roots to obtain `C_J exp(-c_JL)`.  Every Fourier-polynomial argument therefore survives, with constants independent of the growing R and K.

Apply the correction of section 7.  Every singleton law under P_* is now **exactly the law of omega(U)**, so all one-site information, not just a selection of moments, is preserved.  With `mu_M=E omega(U)` the centered-tail bound is `sqrt(Var(omega(U)))(4^{-a}-4^{-K})/3`; fixed-prefix total variation, the normalized Gaussian limit, and the nonzero scheduled phase limits remain as before.  The missing ingredient is still joint arithmetic/overlapping-shift structure.  This extension is not a construction of an alternative arithmetic function and does not assert that the product reference law is the true joint law of shifted omega values.

## What this adds to the failed-route inventory

The previous phase-boundary example showed that interior analytic decay alone does not determine a boundary value.  This construction is more specific: it uses the actual geometric coefficients, preserves fixed-prefix independence, uniform second moments, the centered-tail bound, the whole-window Gaussian limit, and limiting multiplication-by-4 invariance simultaneously.

A surviving G4 argument must use information not captured by that collection of summaries.  Exact arithmetic/overlapping-shift structure is an available distinction; this note supplies no estimate exploiting it.  No helper or formalization launch is warranted by the countermodel alone.

## Review and unfinished extension at wrap

Fable independently checked (2), Fourier separation and coefficient extraction, the fixed-prefix estimate, and the uniform singleton argument in `agent-mail/g4/20260922T193224Z-fable-fc2188c5-8d0a-4cdb-8b93-c88c0303bdd1.md`; no flaw was found in those steps.  Sections 7-8 were added subsequently and were not covered by that reply.  This is paper reasoning, not a formalized theorem.

An unfinished follow-up considered before wrap would address the missing overlapping-row condition with carries.  Starting from an auxiliary sequence A_n>=3, set U_n=sum_{j>=1} A_{n+j}/4^j and C_n=floor(U_n).  For digits d_n of a prescribed times-4 orbit X_n, define W_{n+1}=4C_n-C_{n+1}+d_n.  Then W is nonnegative, differs from A by at most 3, and its infinite tail is C_n+X_n, provided the tails converge.  This identity alone does NOT establish the fixed-prefix total-variation laws or the ordinary every-scale estimates; those obligations are unfinished.  No shift-consistent strengthening is claimed in this note.
