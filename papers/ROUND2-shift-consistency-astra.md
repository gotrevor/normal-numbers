# Pair B Astra: exact carry law and a one-sequence countermodel

Research proof by astra-shift-consistency, 2026-09-22.  This is paper mathematics, not a Lean result.  Companion: `ROUND2-shift-consistency-fable.md`.  The original Riesz note is unchanged.

## 1. Target and result

Write e(t)=exp(2 pi i t), L_M=log log M for M>=3, and use the actual repository schedule

    K(M)=Nat.log 2 (Nat.log 2 (Nat.log 2 M))+1.

There exists ONE deterministic sequence of nonnegative integers W_1,W_2,... such that, as M tends to infinity through ALL integers:

(P) For every fixed J>=1, the empirical probability measure

    (1/M) sum_{n=0}^{M-1} delta_(W_{n+1},...,W_{n+J})

has total variation distance tending to zero from Pois(L_M)^{tensor J}.

(V) Uniformly for 1<=j<=K(M),

    (1/M) sum_{n<M} (W_{n+j}-L_M)^2 = (1+o(1)) L_M.

Consequently, uniformly for 0<=a<K(M),

    [(1/M) sum_{n<M} |sum_{a<j<=K(M)}4^{-j}(W_{n+j}-L_M)|^2]^(1/2)
      <= (1+o(1)) sqrt(L_M) (4^{-a}-4^{-K(M)})/3.

(F) For every fixed integer h,

    (1/M) sum_{n<M} e(h sum_{j<=K(M)} W_{n+j}/4^j) -> 1.

The same statements hold with the averaging interval M<=n<2M, reference mean L_M, and window K(M).  In particular every nonzero h fails scheduled cancellation, even though every fixed prefix with 4^J not dividing h cancels by (P).

The construction also has the corresponding whole-window centered Gaussian limit of variance 1/15.  It is not an arithmetic sequence, does not have exact omega marginals, and proves nothing against G4 normality.  It shows that overlap itself does not repair this package of summary laws.

The deliberately simpler orbit X_n=0 replaces the Riesz orbit.  Keeping its particular Fourier table is not a requirement of the round-two brief.  Here all limiting phase coefficients are 1.

## 2. Exact finite block formula, including the obstruction

Let A_1,...,A_J be independent, with mass functions p_i supported on integers >=3.  Let C_J be an independent nonnegative integer.  Fix d_0,...,d_{J-1} in {0,1,2,3}.  Recursively define

    C_{i-1}=floor((A_i+C_i)/4),
    b_i=A_i+C_i-4C_{i-1} in {0,1,2,3},
    W_i=4C_{i-1}-C_i+d_{i-1}=A_i-b_i+d_{i-1}.

Put Q=4^J and q(r)=P(C_J=r mod Q).  For every integer vector w,

    P(W=w)=q(r(w,d)) product_{i=1}^J s_i(w_i),             (2.1)
    r(w,d)=sum_{i=1}^J 4^{J-i}(d_{i-1}-w_i) mod Q,
    s_i(v)=sum_{b=0}^3 p_i(v+b-d_{i-1}).

Proof: fixing c=C_J and w forces all the C_i by backward recursion.  They are integers exactly when c=r(w,d) mod Q.  In that case every b-vector in {0,1,2,3}^J gives the unique A_i=w_i+b_i-d_{i-1}; conversely every preimage has this form.  Nonnegative c and A_i ensure all earlier carries are nonnegative.  Summation over b factorizes, and summation over c yields (2.1).  No fraction of a tail was discarded in this calculation.

If q is concentrated at one residue, the whole W-vector lies in one weighted congruence class.  In particular |W-A|<=3 is NOT a TV argument.  This is the first genuine obstruction to the informal carry proposal.

For the positive estimate define ptilde_i=s_i/4, which is a probability mass function.  If

    max_r |Q q(r)-1| <= eta,

then (2.1) gives the pointwise comparison

    |P(W=w)-product_i ptilde_i(w_i)|
       <= eta product_i ptilde_i(w_i).                    (2.2)

Thus its TV distance to the product smoothed law is <=eta/2.  Also

    TV(product ptilde_i, product p_i)
       <= sum_i (1/4) sum_{b=0}^3 TV(p_i shifted by d_{i-1}-b,p_i).

These statements are exact finite estimates, not asymptotic independence assumptions.

## 3. One random input supplies the residue uniformity

Suppose C_J=floor((A_{J+1}+c)/4), with arbitrary fixed nonnegative integer c, and A_{J+1}=3+Pois(lambda).  Uniformity of A_{J+1} modulo 4Q implies uniformity of C_J modulo Q: each residue of C_J has exactly four preimages modulo 4Q.

For N~Pois(lambda), root-of-unity inversion gives, for any integer H>=2,

    max_r |H P(N=r mod H)-1|
       <= (H-1) exp[-lambda (1-cos(2 pi/H))].              (3.1)

Indeed the nonconstant Fourier terms are exp(lambda(e(k/H)-1)), and each has modulus at most the displayed exponential.  A translation by 3+c only permutes the residues.  Hence (2.2) holds, UNIFORMLY IN c, with

    eta_J(lambda)=(4^{J+1}-1)
      exp[-lambda(1-cos(2 pi/4^{J+1}))].                  (3.2)

For p_i=law(3+Pois(lambda_i)), the smoothed variable has the law of

    Pois(lambda_i)+3+d_{i-1}-B,  B uniform on {0,1,2,3}.

All its translations relative to Pois(lambda_i) have size <=6.  The elementary identity TV(Pois(lambda)+1,Pois(lambda))=max_k P(Pois(lambda)=k), plus unimodality, gives the bound <=lambda^{-1/2} for lambda>=1.  One may obtain that bound without Stirling from Fourier inversion and 1-cos t>=2t^2/pi^2 on [-pi,pi].  Telescoping translations and products therefore give

    TV(law(W_1,...,W_J), tensor_i Pois(lambda_i))
       <= eta_J(lambda_{J+1})/2 + 6 sum_{i=1}^J lambda_i^{-1/2}.     (3.3)

The estimate remains true conditional on ANY later tail which fixes c and is independent of A_1,...,A_{J+1}.  This conditional form is the key to every-scale empirical laws.

## 4. One nonstationary background, with no block gluing

Take mutually independent

    A_i=3+N_i,  N_i~Pois(lambda_i),
    lambda_i=log log(i+e^e),  i>=1.

All assertions below hold on a probability-one set; fix any one realization in their intersection to obtain the deterministic sequence.  The reference mean differs from E A_i by the bounded shift 3; this will be negligible on both TV and variance scales.

Almost surely A_i<=D log(i+2) for all i and some finite sample-dependent D.  For example exponential Markov at parameter 1 bounds

    P(A_i>D_0 log(i+2))
       <= exp(3+(e-1)lambda_i) (i+2)^(-D_0),

which is summable for a fixed sufficiently large D_0; absorb the finitely many exceptions into D.

Define the convergent tails and their floors

    U_n=sum_{j>=1} A_{n+j}/4^j,
    C_n=floor U_n,
    W_{n+1}=4C_n-C_{n+1}.                                 (4.1)

Since 4U_n=A_{n+1}+U_{n+1}, and writing U_{n+1}=C_{n+1}+F with 0<=F<1,

    C_n=floor((A_{n+1}+C_{n+1})/4).

Thus W_{n+1}=A_{n+1}-b_{n+1} with b in {0,1,2,3}.  In particular W>=0, |W-A|<=3, and W_i<=D log(i+2).  The infinite phase telescopes:

    sum_{j>=1} W_{n+j}/4^j=C_n,
    sum_{j=1}^k W_{n+j}/4^j=C_n-4^{-k}C_{n+k}.            (4.2)

Growth of C makes the telescoping remainder vanish.  These are exact identities on a single sequence, hence all finite overlaps are automatically consistent.

## 5. Every-prefix total variation: the conditional estimate is sufficient

This section proves the empirical step rather than replacing it by stationarity or an ergodic assertion.

Fix J and write D_J=J+1 and F_r=sigma(A_i:i>=r), a decreasing filtration.  For any bounded function f on nonnegative integer J-vectors with |f|<=1, set

    Y_n=f(W_{n+1},...,W_{n+J}),
    Z_n=Y_n-E(Y_n | F_{n+D_J+1}).

Y_n is F_{n+1}-measurable.  Conditional on F_{n+J+2}, the carry C_{n+J+1} is fixed, and A_{n+1},...,A_{n+J+1} are still independent Poisson translates.  Consequently (3.3) applies uniformly in the realized tail.  Let Q_{n,J}=tensor_{i=1}^J Pois(lambda_{n+i}) and

    eps_{n,J}=eta_J(lambda_{n+J+1})/2
                 +6 sum_{i=1}^J lambda_{n+i}^{-1/2}.

Then eps_{n,J}->0 and

    |E(Y_n | F_{n+D_J+1})-E_{Q_{n,J}}f| <=2 eps_{n,J}.      (5.1)

For each residue of n modulo D_J the Z_n are bounded reverse martingale differences.  For a finite sum, read their indices in decreasing order: the previously exposed variables are measurable in the next conditioning sigma-field, and the next difference has conditional mean zero.  Conditional Hoeffding, iterated in this order, yields the usual Azuma bound.  Splitting into D_J residues and taking a union bound gives, for M>=D_J and 0<t<=1,

    P(|(1/M)sum_{n<M} Z_n|>t)
       <=2D_J exp[-t^2 M/(32 D_J)].                       (5.2)

Constants are deliberately loose.  This works for an M-dependent deterministic f as well.

To pass from test functions to TV, take S_M={0,...,floor((log(M+2))^2)}^J.  Apply (5.2) to the indicators of EVERY subset B of S_M (viewed as subsets of the entire countable state space), with t_M=M^{-1/8}.  There are 2^{|S_M|} tests and |S_M|=O_J((log M)^{2J}).  The union bound is summable in M because its logarithm is

    O_J((log M)^{2J}) - M^{3/4}/(32D_J).

Borel-Cantelli implies simultaneous agreement of empirical and conditional laws for all such B, at every sufficiently large M.  The actual W-blocks lie in S_M eventually, by the logarithmic envelope in section 4.  The reference Poisson mass outside S_M tends to zero.  Equation (5.1), averaged in n, has error tending to zero by Cesaro.  It follows that the empirical law approaches (1/M)sum_{n<M}Q_{n,J} in TV.

Finally this mixture approaches Pois(L_M)^{tensor J}.  Discard n<M/log M, a fraction tending to zero.  Uniformly for M/log M<=n<M and fixed i,

    |lambda_{n+i}-L_M|=O(log log M/log M)->0.

Poisson coupling gives TV(Pois(a),Pois(b))<=|a-b|.  Apply it to the product and then the mixture.  This proves (P) with its all-integer-M quantifier.  Countably many fixed J share a probability-one set.  There is no triangular choice of W and no favorable subsequence.

## 6. Uniform integrability and second moments

TV alone cannot prove moments.  Here they follow independently from the background and bounded correction.

Put B_i=N_i-lambda_i, so E B_i=0, E B_i^2=lambda_i and Var(B_i^2)=lambda_i+2lambda_i^2.  Independence and

    sum_i (lambda_i+2lambda_i^2)/i^2 < infinity

imply, almost surely,

    (1/M)sum_{i<=M} (B_i^2-lambda_i)->0.                   (6.1)

For completeness this is the elementary independent-variable strong law: the centered series with terms divided by i converges almost surely by the summable-variance maximal inequality, and summation by parts gives (6.1).

The deterministic slowly varying parameters satisfy

    (1/M)sum_{i<=M}lambda_i=L_M+o(1),
    (1/M)sum_{i<=M}(lambda_i-L_M)^2=o(1).                 (6.2)

For the second assertion, discard i<M/(log M)^2: their squared error is O(L_M^2), with vanishing weighted contribution.  On the remaining indices the difference is O(log log M/log M).  The first assertion follows the same split.

Cauchy-Schwarz, (6.1), and (6.2) now yield

    (1/M)sum_{i<=M}(A_i-L_M)^2=L_M+O(sqrt(L_M))+o(L_M)
                                      =(1+o(1))L_M.

Since |W_i-A_i|<=3, the same estimate holds for W, by

    |(W_i-L_M)^2-(A_i-L_M)^2|<=6|A_i-L_M|+9.

Changing [1,M] to [j,M+j-1], uniformly for j<=K(M), changes at most 2K(M) terms, each O(log^2(M+K(M))) by the envelope.  Their normalized cost is o(1).  This proves (V), including uniformity over the scheduled sites.  Empirical Minkowski gives the exact geometric sum in section 1.  The constant is asymptotically 1, not merely an unspecified O(1).

## 7. Finite versus infinite phase, with the actual schedule

The preceding moment estimates imply sum_{i<=M}A_i=O(M L_M).  For any k<=K(M)+1,

    (1/M)sum_{n<M} C_{n+k}=O(L_M).                        (7.1)

To check the infinite tail explicitly, use C<=U.  In U_{n+k}=sum_{r>=1}4^{-r}A_{n+k+r}, split r<=M and r>M.  For the first part each shifted interval is contained in [1,3M] for large M, so its normalized sum is O(L_M); summing 4^{-r} keeps that bound.  For r>M use the pointwise envelope D log(M+k+r+2), whose geometrically weighted tail tends to zero.  Thus no unproved uniform-in-arbitrary-shift moment bound is being used.

For fixed h, (4.2) and |e(t)-1|<=2 pi |t| give

    |(1/M)sum_{n<M}e(h sum_{j<=k}W_{n+j}/4^j)-1|
       <=2 pi |h| 4^{-k} (1/M)sum_{n<M} C_{n+k}
       =O_h(L_M/4^k).                                   (7.2)

The nested integer logarithms in the actual schedule satisfy 4^{K(M)} asymptotic up to absolute factors to (log log M)^2.  Indeed each integer base-2 logarithm is the floor of its real logarithm; replacing the two inner floors changes log_2 log_2 M by O(1), and the outer floor changes its power of 4 by a factor between 1 and 4.  Hence L_M/4^{K(M)}=O(1/L_M)->0.  This proves (F).

We only need this asymptotic comparison; we do not rely on an exact inequality obtained by silently dropping inner Nat.log floors.

## 8. Dyadic averages and Gaussian law

For fixed J, the empirical measure on M<=n<2M equals twice the prefix empirical measure at 2M minus the one at M.  Their reference laws approach each other in TV because L_{2M}-L_M->0.  Thus (P) passes to dyadic averages directly, despite the signed algebraic combination.

For moments, recenter the 2M-prefix law at L_M.  The change of center is o(1), and its cross term is controlled by the O(L_M) second-moment estimate and Cauchy-Schwarz.  Subtract the M-prefix moment from twice this recentered moment.  This gives L_M+o(L_M), uniformly for j<=K(M), since K(M)<=K(2M).  Minkowski applies on the dyadic interval as before.

For scheduled phases it is cleaner to use (4.2) directly with k=K(M).  The dyadic average of C_{n+k} is bounded by twice its [0,2M) average, which is O(L_M) by the proof of (7.1).  Therefore (7.2) holds on dyadic intervals too.  This avoids equating K(M) and K(2M) across a schedule jump.

For the normalized whole-window Gaussian law, first fix J and use (P) and the elementary Poisson CLT on the first J coordinates, giving limiting variance sum_{j<=J}16^{-j}.  The centered tail after J, divided by sqrt(L_M), has empirical L2 norm at most (1+o(1))4^{-J}/3.  Let M tend to infinity first, then J tend to infinity.  The limiting variance is sum_{j>=1}16^{-j}=1/15.  The same proof works dyadically.

## 9. Scope and referee checklist

The finite residue obstruction is real but does not prevent this lift: one fresh Poisson input masks its entire fixed-block congruence.  The argument uses fixed J, with an exponentially bad J-dependent constant in (3.2).  It does not assert TV approximation at J=K(M), which would contradict the phase conclusion.

The zero orbit creates no hidden inconsistency.  Telescoping forces the infinite phase to be C_n, an integer; C_n diverges in size on average, while the observed counts still have asymptotically Poisson fixed-prefix laws.  The bounded carry change preserves moments by an explicit inequality, and preserves TV only by (2.1)-(3.3).  Those are different arguments.

This is an existence theorem for one deterministic sequence obtained by fixing a probability-one realization.  No algorithm to print its values is supplied or required for deterministic existence.  Exact omega singleton laws remain unproved and unclaimed.  Multiplicativity and actual arithmetic joint information remain distinctions from G4.

Load-bearing points for independent review: (i) all preimages in (2.1); (ii) uniformity in the conditioned terminal carry in (3.2); (iii) filtration indices and reverse Azuma in section 5; (iv) the TV union bound over growing finite state spaces; (v) the recentering and dyadic passage; (vi) the infinite remainder in (7.1).  No numerical probe or formalization launch is used.

## 10. Independent review and the exact-marginal quantifier

Fable independently derived the zero-orbit carry lift and reviewed each of the six load-bearing points above in `agent-mail/shift-consistency/20260922T200757Z-fable-shift-consistency-1a8e7372-3242-4424-85f9-195238f09d0e.md`.  No defect was found in the finite preimage formula, uniform conditional residue estimate, reverse-martingale filtration, growing-state-space union bound, moment/dyadic passage, or infinite remainder estimate.  This is a mutually checked paper proof, not formal verification.

A precise obstruction to one reading of the stretch target is worth separating from the construction.  Suppose, for every sufficiently large M, the empirical singleton histogram of W_1,...,W_M equals the histogram of omega(1),...,omega(M) EXACTLY.  Multiplying by M and subtracting the corresponding equality at M-1 gives

    delta_{W_M}=delta_{omega(M)}.

Therefore W_M=omega(M) eventually.  Exact every-prefix empirical marginals would force the actual arithmetic sequence, apart from a finite initial segment; that is fundamentally stronger than the triangular note's exact equality of probability marginals at each separate scale.  Our theorem supplies asymptotic empirical TV, not this exact histogram equality.  Exact probability marginals under an auxiliary random-sequence law are another possible interpretation, for which no correction mechanism is supplied here.

Likewise replacing the Poisson background by copies of the omega(U) distribution requires not only root-of-unity decay but small TV under bounded integer translations.  A weak central limit theorem alone does not imply that lattice smoothness.  No such unproved replacement is used above.
