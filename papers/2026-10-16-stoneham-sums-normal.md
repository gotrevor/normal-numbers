# Sums of Stoneham constants are normal (PROPOSED, UNREFEREED)

> **Status (2026-10-16):** paper proof by a proof subagent (~92% self-assessed); **independent referee:
> ACCEPT WITH MINOR REPAIRS (~88%)**, repairs applied below.  Elementary part ~98%; (F3) is used
> exactly within its stated hypotheses (verbatim quote checked, Prop. 4.1 induction re-derived,
> Korobov Lemma 2.2 probed on 107 mixed moduli).  Residual risk: [V] is an arXiv preprint with no
> journal reference found, so the one deep input may be unrefereed.  Freshness check pending.  Do
> not cite or share outward before it clears.  Referee scratch: `tmp/referee-stoneham-sums/`.
> Origin: joint Bailey–Crandall orbit long shot (`tmp/joint-bc-orbits/REPORT.md`, candidate T-A).

## Abstract

For $B\ge2$, $c\ge2$ coprime, let $\alpha_{B,c}=\sum_{k\ge1} c^{-k}B^{-c^k}$.  Stoneham,
Bailey–Crandall and others showed $\alpha_{b,c}$ is $b$-normal.  Bailey and Borwein [BB, §4, §6]
wrote: "it is not known at the present time whether the sum $\alpha_{b,c_1}+\alpha_{b,c_2}$ is
$b$-normal."  We prove that every nonzero rational combination of Stoneham constants
$\alpha_{b^{m_i},c_i}$ is $b$-normal when the $c_i$ are pairwise coprime and coprime to $b$;
equivalently the vector is jointly $b$-normal.  E.g. $\alpha_{2,3}+\alpha_{2,5}$ is 2-normal.  The
proof is an elementary $p$-adic step (the newest term survives addition, so the reduced orbit
denominator grows like $n^r$ and is smooth over a fixed prime set) plus one analytic input,
Vandehey's power saving for incomplete Korobov sums with smooth moduli [V, Cor. 1.2].  Coprimality
cannot be dropped: $\alpha_{4,3}-\alpha_{16,3}$ is not 2-normal.

## 1. Statement

Notation: $e(t)=e^{2\pi it}$; $\{t\}$ fractional part; $v_\ell$ the $\ell$-adic valuation;
$\mathbb N_P$ the positive integers with all prime factors in the finite set $P$ ($1\in\mathbb N_P$).

**Theorem A.**  Let $b\ge2$, let $c_1,\dots,c_r\ge2$ be pairwise coprime, each coprime to $b$, and
$m_1,\dots,m_r\ge1$.  Put $\alpha_i:=\alpha_{b^{m_i},c_i}=\sum_{k\ge1}c_i^{-k}b^{-m_ic_i^k}$.  Then
for every $(q_1,\dots,q_r)\in\mathbb Q^r\setminus\{0\}$, $x=\sum_iq_i\alpha_i$ is normal in base $b$.

**Corollary B (joint normality).**  Under the same hypotheses
$(\{b^n\alpha_1\},\dots,\{b^n\alpha_r\})_{n\ge0}$ is u.d. in $[0,1)^r$.  In digit form: for all $k$
and words $w_1,\dots,w_r\in\{0,\dots,b-1\}^k$, the set of $n$ with digits $n+1..n+k$ of $\alpha_i$
spelling $w_i$ for every $i$ has natural density $b^{-kr}$.

**Headline instance.**  $b=2$, $(c_1,c_2)=(3,5)$, $m=(1,1)$, $q=(1,1)$: $\alpha_{2,3}+\alpha_{2,5}$
is 2-normal.  [BB]'s question also allows non-coprime ,c_220 20 12 61 79 80 81 701 33 98 100 204 250 395 398 399 400e.g. lpha_{2,3}+\alpha_{2,9}20 20 12 61 79 80 81 701 33 98 100 204 250 395 398 399 400; Theorem A
leaves that case open, and Remark 3 shows it can fail when the x27s coincide.

## 2. Standard facts used

- **(F1)** [KN Ch.1 Thm 8.1; BC Thm 2.2(5)] $x$ is $b$-normal iff $(b^nx)$ is u.d. mod 1.
- **(F2) Weyl** [KN Ch.1 Thms 2.1, 6.2] (scalar and $\mathbb R^r$ versions).
- **(F3) Vandehey [V, Cor. 1.2].**  $P$ finite set of primes, $b\ge2$, $\varepsilon>0$: there are
  $\delta=\delta(\varepsilon)>0$, $C=C(\varepsilon,b,P)$ such that for every $m\in\mathbb N_P$ with
  $\gcd(m,b)=1$, every $a$ with $\gcd(a,m)=1$, and every integer $J\ge m^\varepsilon$,
  $\big|\sum_{n=1}^J e(ab^n/m)\big|\le C\,m^{-\delta}J(1+\log m)$.  No upper limit on $J$: [V §6.1]
  treats $J\ge m$ by the complete-sum bound [V Lemma 2.3] and $m^\varepsilon\le J\le m$ by Thm 5.1.

Nothing else is cited (no [V Thm 1.4], no Erdős–Turán, no [BC Lemma 4.2]).

## 3. Reduction to integer coefficients and frequency one

**Proposition C.**  With $b,c_i,m_i,\alpha_i$ as in Theorem A, nonzero integers $p_1..p_r$ and an
integer $L\ge1$ with $\gcd(L,b)=1$, put $\xi=\frac1L\sum_ip_i\alpha_i$.  Then
$\frac1N\sum_{n<N}e(b^n\xi)\to0$.

*Theorem A from C.*  Delete indices with $q_i=0$.  By (F1),(F2) show
$\frac1N\sum_{n<N}e(hb^nx)\to0$ for fixed $h\ne0$.  Write $hq_i=p_i'/L'$; factor $L'=L_1L_2$ with
primes of $L_1$ dividing $b$ and $\gcd(L_2,b)=1$; choose $s$ with $L_1\mid b^s$.  For $n\ge s$,
$hb^nx=b^{n-s}\xi$ with $\xi=\frac1{L_2}\sum_ip_i\alpha_i$, $p_i=(b^s/L_1)p_i'\ne0$.  So the sum is
$O(s)+o(N)$.  $\square$

*Corollary B from C.*  $h\cdot v_n=b^n\sum_{h_i\ne0}h_i\alpha_i$; apply C with $L=1$ to the
subfamily; (F2).  Digit form: the condition is $v_n\bmod1$ in a box; expansions unique since each
$\alpha_i$ is irrational.  $\square$  (Conversely joint normality implies A, so A ⟺ B.)

## 4. The orbit, its approximation, its denominators

$P$ := primes dividing $L\prod c_i$ (all coprime to $b$).  $K_i(n):=\#\{k\ge1:m_ic_i^k\le n\}$,
$$S_n:=\frac1L\sum_ip_i\sum_{k=1}^{K_i(n)}\frac{b^{\,n-m_ic_i^k}}{c_i^k}\in\mathbb Q.$$

**Lemma 1.**  $|b^n\xi-S_n|\le C_0/n$, $C_0=2\sum_i|p_i|m_i$; hence the Weyl averages of
$b^n\xi$ and $S_n$ differ by $o(1)$.  *Proof:* tail terms have $b^{n-m_ic_i^k}\le1$ and
$\sum_{k>K}c_i^{-k}=c_i^{-K}/(c_i-1)<\frac{c_i}{c_i-1}\frac{m_i}{n}$ (maximality of $K$);
$|e(u)-e(w)|\le2\pi|u-w|$; $\frac1N\sum1/n\to0$.  $\square$

**Lemma 2.**  If all $K_i$ are constant on $[s,s+J)$ then $S_{s+j}=b^jS_s$.  $\square$

Kick set $T=\{m_ic_i^k\}$ (coincidences merge); $\#(T\cap[1,N])\le r\log_2N$.  (4.1)

**Lemma 3 (newest term survives).**  $S_n=A_n/D_n$ in lowest terms.
1. $D_n\in\mathbb N_P$, $\gcd(D_n,b)=1$, $D_n\mid L\prod_ic_i^{K_i(n)}$.
2. $D_n\ge\prod_ic_i^{K_i(n)}/\prod_i|p_i|$.
3. $\kappa n^r\le D_n\le Ln^r$ for $n\ge1$, $\kappa=(\prod_i|p_i|m_ic_i)^{-1}$.

*Proof of 2.*  Fix $i$, $K=K_i(n)\ge1$, prime $\ell\mid c_i$, $e=v_\ell(c_i)$.  $LS_n=p_iU_i+V_i$
with $U_i=\sum_{k\le K}c_i^{-k}b^{n-m_ic_i^k}$.  Denominators of $U_j$ ($j\ne i$) are powers of
$c_j$, prime to $\ell$ by pairwise coprimality, so $v_\ell(V_i)\ge0$.  Terms of $U_i$ have
$v_\ell=-ek$ ($\ell\nmid b$), unique minimum at $k=K$, so $v_\ell(U_i)=-eK$.  If
$v_\ell(p_i)-eK<0$ then $v_\ell(LS_n)=v_\ell(p_i)-eK$ and $v_\ell(S_n)\le v_\ell(p_i)-eK$.  So
$v_\ell(D_n)\ge eK-v_\ell(p_i)$ always.  Multiply over $\ell$, $i$ (distinct primes):
$D_n\ge\prod_ic_i^{K_i(n)}/|p_i|$.  *Proof of 3:* $c_i^{K_i(n)}\le n$ and $>n/(m_ic_i)$.  $\square$

## 5. Proof of Proposition C

Suffices $\sum_{n<N}e(S_n)=o(N)$.  $N\ge L^2$, $u_1=\lceil\sqrt N\rceil$; cut $[u_1,N)$ at kicks into
$R\le1+r\log_2N$ pieces $I_j$ of length $J_j$, on which all $K_i$ are constant.
(i) $n<u_1$: $\le\sqrt N+1$ terms.  (ii) pieces with $J_j<\sqrt N$: $O(r\sqrt N\log N)$ terms.
(iii) A long piece, start $s\ge\sqrt N$, $J\in[\sqrt N,N]$: by Lemma 2 its sum is
$\sum_{t<J}e(b^tA/D)$, $\gcd(A,D)=1$, $D\in\mathbb N_P$, $\kappa N^{r/2}\le D\le LN^r$.  With
$a\equiv A\bar b$ it equals $\sum_{n=1}^Je(ab^n/D)$.  Apply (F3) with $\varepsilon=1/(2r+1)$:
$D^{\varepsilon}\le L^{1/(2r+1)}N^{r/(2r+1)}\le N^{1/2}\le J$.  So the piece is
$\le CJ(\kappa N^{r/2})^{-\delta}(1+\log L+r\log N)=J\eta(N)$, $\eta\to0$.
Total $\le\sqrt N+1+O(r\sqrt N\log N)+N\eta(N)=o(N)$.  $\square$

## 6. Remarks

1. **Where hypotheses enter.**  Pairwise coprimality: once, Lemma 3(2) (other families cannot cancel
   the newest $\ell$-adic term).  Coprimality to $b$: term valuations and $\gcd(D,b)=1$ in (F3).
   Denominators of $q_i$: absorbed by $L$ and the shift.  Coincident kicks: no special treatment.
2. **Why the classical argument stops at $r=1$.**  For $r=1$ pieces have length $\asymp D_n$ and the
   complete-sum bound $\ll\sqrt D\log D$ suffices (Stoneham/Bailey–Crandall).  For $r\ge2$,
   $D_n\asymp n^r$ while pieces have length $\le n\ll D^{1/r}$: complete sums are useless; one needs
   incomplete Korobov sums of length $D^\varepsilon$ with $D$ smooth over fixed primes, i.e. [V Cor
   1.2].  Korobov's prime-power estimates do not cover mixed moduli $\prod c_i^{a_i}$.
3. **Coprimality cannot be dropped.**  $x=\alpha_{4,3}-\alpha_{16,3}$ ($b=2$, $c=3,3$, $m=2,4$).
   LTE: $v_3(4^{3^k}-1)=1+k$, so the $k$-th difference is $N_k/4^{2\cdot3^k}$ with
   $N_k=(4^{3^k}-1)/3^k\in\mathbb Z$, $0<N_k<4^{3^k}/3^k$.  Then
   $\{4^{2\cdot3^k}x\}<4^{-3^k}$, so base-4 digits $2\cdot3^k+1..3^{k+1}$ vanish; $x$ is not
   4-normal, hence not 2-normal.  The base-4 zero frequency has no limit: it is /16 =2\cdot3^k /8 =3^{k+1}20 20 12 61 79 80 81 701 33 98 100 204 250 395 398 399 400referee correction).  (Same
   mechanism as the T-B flagship $\alpha_{2,3}+\alpha_{4,3}$, kickoff Part 2.)
4. **Generality (unproved, ~75%).**  The proof uses only: $O(N^{1/2-\eta})$ kicks up to $N$;
   $c_i^{K_i(n)}\le n^{O(1)}$; $K_i\to\infty$.  So it should extend to general kick sequences
   $n_{i,k}$, and to a discrepancy bound $\ll N^{-\theta(r)}$ via Erdős–Turán.

## References

- [BB] D. H. Bailey, J. M. Borwein, *Nonnormality of Stoneham constants*, Ramanujan J. 29 (2012).
- [BC] D. H. Bailey, R. E. Crandall, *Random generators and normal numbers*, Exp. Math. 11 (2002).
- [KN] L. Kuipers, H. Niederreiter, *Uniform Distribution of Sequences*, Wiley 1974.
- [V] J. Vandehey, *Differencing methods for Korobov-type exponential sums*, arXiv:1606.07911 (2016
  preprint; no journal reference found as of 2026-10-16), Cor. 1.2 (and Lemma 2.3, §6.1).

## Gaps and confidence (author's)

- (F3) exactly as used: ~92%.  arXiv v1 statement checked (all $m\in\mathbb N_P$, gcd conditions,
  every $N\ge m^\varepsilon$; §6.1 covers $N\ge m$).  Thm 5.1's induction not re-verified;
  published numbering may differ; the log factor may be $(1+\log m)^{2^{-k}}$ (harmless).
- Remark 4: ~75%, not part of the theorem.
- Checked line by line: §3, Lemmas 1–3 (Lemma 3 also by exact rational arithmetic on four parameter
  sets, $n\le300$–$400$, zero failures), §5 exponents, Remark 3 (analytic + numeric).  Headline
  instance: empirical block frequencies over $2\cdot10^5$ bits look normal for lengths 1, 4, 8.
- Overall ~92%.  Freshness: post-2019 literature not yet searched.
