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

## 11. Prescribed orbits: quantifier order and the original Riesz table

Fable's extension replaces zero digits by the base-4 digits d_n of a prescribed x in [0,1), keeping the same background carries and setting

    W_{n+1}=4C_n-C_{n+1}+d_n.

For EACH fixed deterministic x, the proof of sections 2-6 applies with these deterministic digits.  Almost every background, with x already fixed, yields (P), (V), the tail bound, and the Gaussian limit, while

    T_k(n)=C_n+{4^n x}-4^{-k}(C_{n+k}+{4^{n+k}x}).

Consequently its scheduled empirical Fourier mean differs from the ordinary orbit mean of e(h4^n x) by O_h(L_M/4^{K(M)}), both on prefixes and dyadic intervals.  This proves: for every prescribed x there EXISTS a suitable deterministic W.

The order cannot be reversed to claim one full-probability set of backgrounds working for all x simultaneously.  For any realized background, choose d_n in {0,1} with d_n=C_{n+1} mod 2, and let x have exactly those base-4 digits.  The resulting W is always even.  Its singleton TV distance from Pois(L_M) is at least the latter's odd probability, which tends to 1/2.  Such digits define a legitimate orbit, but it was selected after observing the background.  This counterexample corrects the initial preamble of Fable's extension; it does not affect the zero-orbit theorem or the fixed-prescribed-orbit extension.

The original Riesz Fourier table can be embedded unconditionally.  Let mu be the invariant circle measure from the earlier note, with

    a(m)=integral e(mx) dmu(x)=rho^{s(m)}

if m has a finite signed-base-4 expansion with digits {-1,0,1}, and a(m)=0 otherwise.  Here 0<rho<1/2 and s(m) counts nonzero digits.  For any fixed integers u,v,

    a(u+4^r v)=a(u)a(v) for every sufficiently large r.    (11.1)

To prove it, decode the least signed digit by the residue modulo 4: residues 0,1,3 force digits 0,1,-1; residue 2 forbids representability.  Subtract that digit and divide by 4.  For an integer this procedure either reaches 0 in finitely many steps or hits the forbidden residue: away from 0 and the terminal cases +/-1, absolute value strictly decreases.  Choose r larger than the number of steps needed for u.  Decoding u+4^r v follows precisely the same low-digit decisions.  If u fails, the sum fails at the same step.  If u succeeds, its low digits are removed, zeros fill the gap, and the remaining integer is v.  Representability and the number of nonzero digits therefore factor exactly as (11.1) states, including negative u and v.

With T(x)=4x mod 1, equation (11.1) says

    integral e(ux) e(v T^r x) dmu -> a(u)a(v).

By linearity this is mixing for trigonometric polynomials.  Density in L2(mu), Cauchy-Schwarz, and invariance extend it to L2 observables.  Thus mu is mixing and in particular ergodic.  The ergodic theorem supplies a point x generic for all integer characters simultaneously (intersect their countably many full-measure sets).  Choose such a deterministic x FIRST; then choose a good independent background for that x as above.

This produces one deterministic overlapping-window sequence satisfying (P), (V), and the Gaussian law, with scheduled means exactly the earlier note's limiting table: rho at h=1,4; zero at h=2; rho^2 at h=3,12.  Prefix limits give the same dyadic limits by subtraction.  The simpler zero-orbit theorem has coefficient 1 at all h and was already sufficient for the brief.

The extension review and elementary mixing proof were sent in `agent-mail/shift-consistency/20260922T202456Z-astra-shift-consistency-66ac94e2-ee34-443c-a053-7df65054c937.md`.  Fable owns its presentation of the general orbit theorem; the present section records Astra's quantifier counterexample and the complete Riesz argument.

## 12. Continuation: the sharp growing-window threshold

The zero-orbit construction can be chosen to satisfy the following stronger theorem, simultaneously for ALL deterministic integer schedules 1<=J(M)<=K(M).  Write Q=4^J and

    D_M(J)=TV(empirical law of (W_{n+1},...,W_{n+J}), n<M,
              Pois(L_M)^{tensor J}).

Then

    D_M(J(M))->0  if and only if  4^{J(M)}/sqrt(L_M)->0.    (12.1)

If 4^{J(M)}/sqrt(L_M)->infinity, then D_M(J(M))->1.  At the transition, whenever Q/sqrt(L_M)->c in (0,infinity),

    liminf D_M(J(M)) >= (1/2) exp(-2 pi^2/(15c^2)) > 0.    (12.2)

These statements hold at every large integer M, not only at powers of two or on a favorable subsequence; they hold on dyadic averaging intervals as well.  The same realization supports every schedule because the empirical estimates below are uniform over all J<=K(M).  This is separate from the false interchange of orbit/background quantifiers in section 11: the orbit here is fixed to zero throughout.

A more informative identity holds uniformly over all 1<=J<=K(M).  Let qemp_{M,J} be the empirical distribution of C_{n+J} modulo Q for n<M.  Then

    D_M(J)=TV(qemp_{M,J}, Uniform(Z/QZ))+o(1),              (12.3)

where the o(1) is uniform in J.  Thus the entire growing-block TV defect of this model is asymptotically its terminal carry residue defect.  This is a theorem about the constructed independent-background model, not an identity for arbitrary arithmetic sequences.

### 12a. The exact finite TV identity

Use the notation of section 2, and put D(w)=product_i ptilde_i(w_i), with ptilde_i=s_i/4.  For every residue r modulo Q,

    sum_{w:r(w,d)=r} D(w)=1/Q.                             (12.4)

One proof is to apply (2.1) with the terminal carry equal to the fixed nonnegative integer r: its total probability is 1, so sum_{w:r(w,d)=r} product_i s_i(w_i)=1.  Dividing by 4^J proves (12.4).  This also follows from the independent uniform base-4 digit introduced by each four-point smoothing.

For ANY two probability laws q,q' on Z/QZ define

    nu_q(w)=Q q(r(w,d))D(w).

Equation (12.4) says nu_q is a probability measure and gives the exact isometry

    TV(nu_q,nu_q')=TV(q,q').                               (12.5)

In particular the finite block law from (2.1) satisfies

    TV(law(W),product_i ptilde_i)=TV(q,Uniform(Z/QZ)).       (12.6)

The previous bound eta/2 was only an upper bound on the right side.  This exact identity isolates the residue obstruction without losing the rest of the joint law.

### 12b. Remove the artificial logarithmic margin

The crude root-of-unity estimate (3.1) multiplied the worst mode by H-1.  Instead, with H=4Q and a=lambda/(2Q^2), sum all modes:

    max_r |H P(Pois(lambda)=r mod H)-1|
      <= sum_{k=1}^{H-1} exp[-lambda(1-cos(2 pi k/H))]
      <= 2 sum_{k>=1} exp(-a k^2)
      <= 2 exp(-a)/(1-exp(-3a)).                           (12.7)

Indeed, 1-cos(2 pi k/H)>=8 min(k,H-k)^2/H^2, and k^2>=1+3(k-1) for k>=1.  The same bound applies to Q times the residue law of floor((3+Pois(lambda)+c)/4), uniformly in the later carry c, by summing its four preimages.  Therefore the conditional block TV estimate is now

    TV(law(W-block | later tail), tensor_i Pois(lambda_i))
      <= exp(-a)/(1-exp(-3a)) + 6 sum_i lambda_i^{-1/2}.    (12.8)

It tends to zero throughout Q=o(sqrt(lambda)) and J=O(log lambda).  No extra factor log lambda in the condition on Q is needed.

## 13. Empirical factorization, uniform in the growing block length

This supplies the all-M and simultaneous-schedule part of (12.3).  Work on one probability-one event, intersected with those already used above.  Set B_M=floor((log(M+2))^2), t_M=M^{-1/8}, and for each J<=K(M) use the state box S_{M,J}={0,...,B_M}^J.

Since K(M)=O(log L_M),

    max_{J<=K(M)} |S_{M,J}|=exp(O(L_M log L_M))=M^{o(1)}.

For each J, apply the reverse-martingale bound (5.2) to every indicator of a subset of S_{M,J}.  A union bound over these subsets AND every J<=K(M) is summable: its logarithm is at most

    log(2K(M)(K(M)+1))
      + O(exp(O(L_M log L_M))) - M^{3/4}/(32(K(M)+1)),

which tends to minus infinity faster than a positive power of M.  Thus almost surely the empirical W-block law differs, on every event inside S_{M,J}, from the average of its conditional laws by at most t_M, simultaneously for all these J and all large M.

Write q_{n,J}(r) for the conditional distribution of C_{n+J} mod Q given F_{n+J+2}.  It is random but measurable in that later tail.  Formula (2.1) gives the conditional W-block law exactly as

    Q q_{n,J}(r(w,0)) D_{n,J}(w),

where D_{n,J} is the product of the four-point smoothed laws of 3+Pois(lambda_{n+i}), 1<=i<=J.  Define D_{L,J} by replacing every lambda_{n+i} with L=L_M.

The actual W blocks lie inside S_{M,J} eventually, uniformly in J<=K, by the logarithmic envelope.  The conditional laws put vanishing mass outside that box uniformly: each is bounded above pointwise by Q D_{n,J}, Q=O(L^2), while the Poisson means are at most L+o(1), and B_M is much larger.  For example exponential Markov at parameter 1 bounds this outside mass by

    Q J exp(6+(e-1)(L+o(1))-B_M),

which tends to zero uniformly.  The same bound applies to any law Q q(r(w,0))D_{L,J}(w).  Hence the finite-state concentration extends to full TV with an error tending to zero uniformly.

Let qbar_{M,J}=(1/M)sum_{n<M}q_{n,J}.  Replacing D_{n,J} by D_{L,J} in the averaged conditional law costs o(1), uniformly in J.  Explicitly, the TV cost at n is at most Q TV(D_{n,J},D_{L,J}).  For n<M/log M the crude contribution is at most Q/log M=o(1).  For the other n, Poisson coupling and contraction under smoothing give

    TV(D_{n,J},D_{L,J}) <= J max_i |lambda_{n+i}-L|
                              = O(J L/log M).

Thus the bulk cost is O(Q J L/log M)=o(1), uniformly for Q<=4^K=O(L^2).  Consequently

    TV(empirical W-block law, nu_{qbar_{M,J}})=o(1)         (13.1)

uniformly in J, with nu now built from D_{L,J} and d=0.

It remains to identify qbar empirically; no stationarity is assumed.  For every subset R of Z/QZ,

    1_{C_{n+J} mod Q in R} - q_{n,J}(R)

is a bounded reverse martingale difference: it is F_{n+J+1}-measurable and has conditional mean zero given F_{n+J+2}.  Apply Hoeffding to n=0,...,M-1 and take the union over all 2^Q subsets and all J<=K(M), again at tolerance t_M.  This is summable because Q=O(L^2)=M^{o(1)}.  It proves

    max_{J<=K(M)} TV(qemp_{M,J},qbar_{M,J})->0.             (13.2)

Using the exact isometry (12.5), equations (13.1)-(13.2) imply

    max_{J<=K(M)} TV(empirical W-block law,nu_{qemp_{M,J}})->0.

Finally TV(D_{L,J},Pois(L)^{tensor J})<=6J/sqrt(L)=o(1) uniformly for J<=K(M).  Equation (12.5) with q'=Uniform then proves (12.3).

For Q=o(sqrt L), (12.7) bounds each conditional q_{n,J} on the bulk n>=M/log M, and the first M/log M indices have vanishing mass.  Equations (13.2) and (12.3) therefore prove the sufficient half of (12.1).  These estimates are simultaneous for all J, so this is one realization for every subcritical schedule, not an uncountable intersection of schedule-specific probability-one events.

## 14. The transition coefficient and maximal separation above it

### 14a. The empirical carry CLT

The Gaussian result in section 8 and the scheduled tail bound imply

    empirical law of (C_n-L_M/3)/sqrt(L_M), n<M,
         converges weakly to N(0,1/15).                    (14.1)

Indeed T_{K(M)}(n)=C_n-4^{-K(M)}C_{n+K(M)}.  The empirical L1 norm of their difference, divided by sqrt L, is O(sqrt L/4^K)=o(1), by (7.1).  The centering constants differ by L 4^{-K}/3, also negligible after division by sqrt L.  This proves (14.1) from the already established whole-window CLT.

For any bounded test, shifting n to n+J changes its empirical average by at most 2J/M times the sup norm.  Thus (14.1) holds uniformly for the shifted carry samples C_{n+J}, J<=K(M).  Characteristic functions of weakly convergent probability measures converge uniformly on each compact frequency interval: truncate |z| at a fixed R using tightness, use the Lipschitz bound there, then use a finite frequency net.  This elementary observation permits a moving frequency below.

### 14b. A nonzero transition Fourier coefficient

For Q=4^J, telescoping gives the exact identity

    e(L/(3Q)) (1/M)sum_{n<M} e(T_J(n))
      = (1/M)sum_{n<M} e(-(C_{n+J}-L/3)/Q).

For every fixed c0>0, (14.1) therefore gives, uniformly over all J<=K(M) with Q>=c0 sqrt L,

    e(L/(3Q)) (1/M)sum_{n<M} e(T_J(n))
      = exp(-2 pi^2 L/(15Q^2)) + o(1).                    (14.2)

This is a statement about the rotated COMPLEX mean.  Without the rotation, its modulus has the displayed asymptotic, but its argument need not converge.

Under the independent product Pois(L) law, the corresponding Fourier mean has modulus at most exp(-L): the first coordinate already contributes exp(L(i-1)), and all other factors have modulus at most one.  Since expectations of a modulus-one test differ by at most twice TV,

    D_M(J) >= (1/2) exp(-2 pi^2 L/(15Q^2)) - o(1)           (14.3)

uniformly in that same range.  This proves (12.2).  If D_M(J(M))->0 but Q/sqrt L fails to tend to zero, take a subsequence with Q>=c0 sqrt L; (14.3) contradicts the alleged TV convergence.  This proves necessity in (12.1), including oscillating schedules.

### 14c. TV tends to one in the supercritical range

Assume Q/sqrt L->infinity.  Set eps_M=(sqrt L/Q)^{1/2}->0 and consider the arc on R/Z centered at -L/(3Q), of radius eps_M.  By (14.1) and tightness, the empirical W phase T_J mod 1 belongs to this arc with probability tending to 1: leaving the corresponding interval on the real line requires

    |C_{n+J}-L/3|/sqrt L > eps_M Q/sqrt L
                               =(Q/sqrt L)^{1/2}->infinity.

Under the product Poisson law the phase lies on the Q-point grid.  Every nonconstant Fourier coefficient on that grid has modulus at most exp(-L): for 0<q<Q, its first nontrivial site is v_4(q)+1<=J and has cosine at most zero.  Fourier inversion gives

    TV(law of product-Poisson phase,Uniform(Q-grid))
          <= (Q-1)exp(-L)/2=o(1),                         (14.4)

since Q<=4^K=O(L^2).  The uniform grid puts at most 2eps_M+2/Q=o(1) mass in the chosen arc.  Its preimage under the block-phase map is consequently an event with empirical W probability tending to 1 and product Poisson probability tending to 0.  Hence D_M(J(M))->1.

For dyadic averages the empirical carry CLT follows by subtracting prefix empirical measures, recentering from L_{2M} to L_M, and using L_{2M}-L_M->0; shifts J<=K(M) still cost O(K/M).  The reverse-martingale and factorization estimates in section 13 also apply directly to n=M,...,2M-1, with the same cardinality bounds and with lambda_{n+i}=L_M+o(1) uniformly.  Thus (12.1)-(12.3), (14.2), and maximal separation all hold dyadically as stated.

## 15. What the continuation adds, and does not add

The first theorem left a gap between fixed blocks and the scheduled block.  The continuation locates it sharply in this countermodel: indistinguishability persists for every growing block with 4^J=o(sqrt(loglog M)); a nonzero Fourier coefficient appears at the fluctuation scale; the full TV distance tends to its maximal value above that scale.  The actual repository schedule has 4^K comparable to L^2, well into the last range.

The terminal carry is not just one detectable statistic here: (12.3) identifies its residue TV with the entire block TV, up to a uniform vanishing error.  That exact transfer relies on independence and lattice smoothing of the artificially chosen background.  It supplies no corresponding conditional factorization for omega and no signed arithmetic estimate.  The result strengthens the countermodel's scope while keeping that distinction explicit.

## 16. Exact transition profile: a wrapped Gaussian

The lower bound (12.2) can be sharpened to an exact limit.  For c in (0,infinity), define the wrapped-normal density on R/Z

    g_c(x)=sum_{k in Z} exp(-2 pi^2 k^2/(15c^2)) e(kx)
          =c sqrt(15/(2 pi)) sum_{m in Z} exp(-15c^2(x+m)^2/2),

and its distance from the uniform circle law

    F(c)=(1/2) integral_0^1 |g_c(x)-1| dx.                 (16.1)

For any schedule 1<=J(M)<=K(M) with 4^{J(M)}/sqrt(L_M)->c,

    D_M(J(M))->F(c).                                      (16.2)

In particular F(c)>0 for every c>0 (its first Fourier coefficient is nonzero), F(c)->0 as c decreases to zero, and F(c)->1 as c tends to infinity.  Together with sections 12-14, this describes the full transition from indistinguishable blocks to maximally separated blocks.  The Gaussian variance is 1/(15c^2) before wrapping.  The rotating mean affects the location of its peak, but not its TV distance from uniform.

### 16a. Four Fourier modes control a floored Poisson input

For Q>=2 and 0<=k<Q, put d_Q(k)=min(k,Q-k).  For N~Pois(lambda) and any fixed integer a,

    |E e(k floor((N+a)/4)/Q)|
         <=4 exp[-lambda d_Q(k)^2/(2Q^2)].                (16.3)

Here is the finite Fourier proof, avoiding any unproved local limit theorem.  The function

    f(m)=e(k floor((m+a)/4)/Q)

on Z/(4Q)Z satisfies f(m+4)=e(k/Q)f(m).  Its discrete Fourier expansion therefore uses only the four frequencies ell=k+sQ modulo 4Q, s=0,1,2,3.  Each normalized Fourier coefficient has absolute value at most 1.  At every such ell, the distance to 0 modulo 4Q is at least d_Q(k).  The Poisson transform and 1-cos(2 pi ell/(4Q))>=8 dist(ell,4QZ)^2/(4Q)^2 give (16.3).  The constant 4 is harmless; the important feature is summable Gaussian decay in the frequency k at the critical scale, uniformly in the conditioned later carry a.

### 16b. Upgrade the empirical CLT to a residue local limit

Let Q/sqrt L->c, theta_M=L/(3Q), and qemp=qemp_{M,J}.  Then

    max_{0<=r<Q} |Q qemp(r)-g_c(r/Q-theta_M)| ->0.          (16.4)

The weak CLT alone would NOT imply this local conclusion.  Its missing high-frequency control is supplied by (16.3), plus the empirical conditional-law concentration in section 13.

More explicitly, (13.2) supplies TV(qemp,qbar)<=t_M eventually, uniformly in J.  Multiplying the induced bound on a Fourier coefficient by the number Q of coefficients still gives O(Q t_M)=o(1).  For the conditional q_{n,J}, equation (16.3) applies with lambda=lambda_{n+J+1}, because the later carry is conditioned and fixed.  Discard n<M/log M; their total contribution to the SUM of Fourier magnitudes is at most Q/log M=o(1).  On the remaining indices lambda/L->1 uniformly, and Q/sqrt L->c.  For all large M this bounds each signed frequency k, |k|<=Q/2, by

    4 exp(-k^2/(4(c+1)^2)),

a summable bound independent of M.  Thus the aggregate contribution from |k|>R tends uniformly to zero as R tends to infinity, after M tends to infinity.

For each fixed k, the empirical carry CLT (14.1) gives

    e(-k theta_M) sum_r qemp(r)e(kr/Q)
          -> exp(-2 pi^2 k^2/(15c^2)).                    (16.5)

Fourier inversion on Z/QZ, first restricted to |k|<=R and then using the summable tail bound above, proves (16.4), uniformly in r.  The Fourier tail of g_c itself is absolutely summable.  This proves a residue local limit using the conditional Poisson input, not by upgrading a weak CLT without justification.

It follows that

    TV(qemp,Uniform(Z/QZ))
       -(1/(2Q))sum_{r=0}^{Q-1}|g_c(r/Q-theta_M)-1| ->0.

The translated-grid Riemann sums converge to (16.1) uniformly in theta_M, by uniform continuity of g_c on the circle.  Combine this with (12.3) to obtain (16.2).  All concentration estimates and the carry CLT have the same dyadic versions, so the identical profile holds on M<=n<2M.

As c decreases to zero, the nonconstant Fourier series of g_c tends uniformly to zero, giving F(c)->0.  As c tends to infinity, its Gaussian periodization places probability tending to 1 in an arc of length tending to zero, giving F(c)->1.  No numerical fitting or additional arithmetic assumption enters this transition profile.

### Continuation review scope

Sections 12-16 were independently reviewed by Fable in `agent-mail/shift-consistency/20260922T214529Z-fable-shift-consistency-cebae1c0-cd1a-436a-aa2d-ac8e6e4fd55f.md` (2026-09-22 21:45:29 UTC).  Fable checked the finite TV isometry, Gaussian-mode bound, uniform empirical factorization, carry CLT and critical coefficient, supercritical separation, four-mode Fourier estimate, and wrapped-Gaussian local limit; no defect was found.  Together with the earlier exchanges covering sections 1-11, the full paper has now received independent mathematical review.  This is paper reasoning, not a Lean formalization.
