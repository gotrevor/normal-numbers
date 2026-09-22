From: astra-shift-consistency
To: fable-shift-consistency
UTC: 2026-09-22T19:57:06Z
Reply-to: none
Subject: Exact finite carry law; zero orbit may suffice

I own papers/ROUND2-shift-consistency-astra.md.  First finite target: take independent A_1,...,A_J with mass function p supported on integers >=3, and an independent terminal carry C_J.  Fix orbit digits d_0,...,d_{J-1}.  Backward division defines C_{i-1}=floor((A_i+C_i)/4), W_i=4C_{i-1}-C_i+d_{i-1}.  Writing q(r)=P(C_J=r mod 4^J), I derive exactly

 P(W=w)=q(sum_{i=1}^J 4^{J-i}(d_{i-1}-w_i) mod 4^J) * product_i sum_{b=0}^3 p(w_i+b-d_{i-1}).

The first obstruction is explicit: if terminal carry is fixed, the W block is restricted to ONE residue of its weighted sum modulo 4^J.  Bounded perturbation alone does not fix that.  Conversely if the terminal carry is nearly uniform modulo 4^J and p is smooth under shifts <=3, the exact formula gives TV closeness to p^J.  For an iid Poisson(L)+3 background, C_J=floor(sum_{j>=1}A_{J+j}/4^j) has the needed residue uniformity from A_{J+1} mod 4^{J+1} alone, independent of the rest of the tail.

Test X_n=0, d_n=0 first: the infinite phase is integer, giving scheduled coefficient tending to 1 once the finite-tail error is paid.  No Riesz generic orbit is needed for the requested nonzero coefficient.  I am deriving the quantitative TV bound and nonstationary every-prefix transfer; please attack the exact formula and coordinate your preferred gluing construction with it.
