# Glendinning & Sidorov (2015), The doubling map with asymmetrical holes

**Citation.**  Paul Glendinning and Nikita Sidorov, *The doubling map with asymmetrical holes*, Ergodic Theory Dynam. Systems 35 (2015).  arXiv:1302.2486v2 (11 Sep 2013), 26 pages.  Local PDF: `glendinning-sidorov-2015-doubling-map-asymmetrical-holes.pdf` in this directory.  Page numbers below are the PDF's printed page numbers (1 to 26); all 26 pages were read.

**Reading guide.**  Sections 1 to 5 are extraction (what the paper says, with page references; verbatim statements are in quotation marks or block quotes).  Section 6 is Ren's own transferability analysis and is labelled as such throughout.  Section 7 is the related-papers check with the arXiv IDs actually opened.

**Verdict in one sentence (Ren).**  The deep machinery (extremal pairs, the substitutions $\rho_r$, the Thue-Morse threshold $\tfrac14\prod(1-2^{-2^n}) \approx 0.175092$) is welded to a *single* hole straddling the discontinuity $1/2$ and does not transfer to unions such as $\bigcup_{m\in S} H(m,w)$; what does transfer is the shallow layer (survivor set = subshift, dimension = entropy / log 2, positive dimension via an embedded positive-entropy SFT), and for our holes, which have rational endpoints, that layer already yields a decidable criterion: $S$ hits $w$ iff a certain sofic shift has zero entropy iff only finitely many periodic orbits of $t \mapsto gt$ avoid the hole.

---

## 1. Definitions and notation

### 1.1 The map, the hole, the survivor set (p. 2)

The doubling map is taken on the closed interval, not the circle:

> $Tx = 2x$ for $x \in [0, 1/2]$, and $Tx = 2x - 1$ for $x \in (1/2, 1]$.  (p. 2)

So $T(1) = 1$, and both $0$ and $1$ are fixed points; they survive every hole $(a,b)$ with $0<a<b<1$.  The survivor set is

> $\mathcal{J}(a,b) = \{x \in [0,1] : T^n x \notin (a,b) \text{ for all } n \ge 0\}$.  (p. 2; also the abstract, p. 1)

The hole is always a single **open** interval $(a,b)$.

### 1.2 Symbolic coding and order (p. 2, p. 6, p. 7)

$\Sigma := \{0,1\}^{\mathbb N}$, $\sigma$ the one-sided shift, $\pi(w_1, w_2, \dots) = \sum_{n\ge1} w_n 2^{-n}$, with $T\pi = \pi\sigma$; $\pi$ is one-to-one except on sequences ending in $0^\infty$ or $1^\infty$ (p. 2).  From p. 7 on the paper identifies a point with its dyadic expansion: "From here on we will not distinguish between $x \in [0,1]$ and its dyadic expansion, in order to simplify our notation."

Lexicographic order (p. 6): $u \prec v$ iff $u_1 < v_1$ or there is $n \ge 1$ with $u_i = v_i$ for $i = 1, \dots, n$ and $u_{n+1} < v_{n+1}$.  Words are over $\{0,1\}$; $|w|$ is the length, $|w|_1$ the number of ones, $|w|_1/|w|$ the 1-ratio; $u^\infty = uuu\cdots$ (p. 6).

**Symbolic description of $\mathcal J(a,b)$ (Ren's gloss; the paper uses it implicitly throughout, e.g. p. 7 to 12).**  Identifying reals with expansions, $x \in \mathcal J(a,b)$ iff for every $n \ge 0$ either $\sigma^n x \preceq a$ or $\sigma^n x \succeq b$.  In the essential range $a < 1/2 < b$ this is a Lorenz-map kneading condition: whenever $x_{n+1} = 0$ one needs $\sigma^n x \preceq a$, and whenever $x_{n+1} = 1$ one needs $\sigma^n x \succeq b$.  So the survivor set is the set of sequences all of whose shifts avoid the open lexicographic interval $(a,b)$.  This two-sided, single-interval structure is what all the later combinatorics exploits.

### 1.3 Reduction to the box $(1/4,1/2)\times(1/2,3/4)$ (p. 2-3)

> **Lemma 1.1.**  (i) If $a < 1/4, b > 1/2$ or $a < 1/2, b > 3/4$, then $\mathcal J(a,b) = \{0,1\}$.  (ii) If $b < 1/2$ or $a > 1/2$, then $\dim_H \mathcal J(a,b) > 0$.  (p. 2)

Proof of (i): if $a<1/4$ and $b>1/2$ the hole contains the cylinder $[w_1=0, w_2=1]$, so a survivor's expansion cannot contain $01$, forcing $x\in\{0,1\}$ (p. 2-3).  Proof of (ii): assume $[a,b] \subset (0,1/2)$; for $n \ge 2$ the subshift of finite type

> $\Sigma_n = \{w \in \Sigma : w_k = 0 \implies w_{k+j} = 1,\ j = 1, \dots, n\}$  (p. 3)

satisfies $\pi(\Sigma_n) \subset \big[\tfrac{1/2 - 2^{-n-1}}{1 - 2^{-n-1}}, 1\big)$, hence $\pi(\Sigma_n) \subset \mathcal J(a,b)$ for $n$ large, and "$\dim_H \mathcal J(a,b) \ge \dim_H \pi(\Sigma_n) = h_{top}(\sigma|_{\Sigma_n})/\log 2 > 0$" (p. 3).  This "exhibit a positive-entropy SFT inside the survivor set" move is the one piece of the paper that transfers directly to unions of intervals (section 6).

The two regions studied in the box are (p. 3)

$D_0 = \{(a,b) \in (1/4,1/2)\times(1/2,3/4) : \mathcal J(a,b) \ne \{0,1\}\}$, $\quad D_1 = \{(a,b) \in (1/4,1/2)\times(1/2,3/4) : \mathcal J(a,b) \text{ is uncountable}\}$.

### 1.4 The two threshold functions (p. 5)

> $\phi(a) = \sup\{b : \mathcal J(a,b) \ne \{0,1\}\}$, $\quad \chi(a) = \sup\{b : \mathcal J(a,b) \text{ is uncountable}\}$, for $a \in (1/4,1/2)$.  (p. 5)

Both are non-decreasing, $\phi \ge \chi$, and $D_0 = \{b \le \phi(a)\}$ (Theorem 2.7), $D_1 = \{b < \chi(a) \text{ or } b \le \chi(a)\}$ depending on $a$ (p. 5; the boundary case is Proposition 4.5).  The paper's reflection symmetry $x \mapsto 1-x$ conjugates $T$ to itself, which is why only $\chi(a)$ (not a separate function of $b$) is needed; Corollary 2.16 (p. 13) gives $\partial D_1 = \{(a,\chi(a))\} \cup \{(1-\chi(1-b), b)\}$.

### 1.5 Extremal pairs (p. 4-5)

> "A pair $(s,t)$ of finite words with alphabet $\{0,1\}$, where $s_1 = 0$ and $t_1 = 1$ is *extremal* if and only if the inequalities
> $$s^\infty \preceq \sigma^k s^\infty \prec t^\infty,\ k = 1, \dots, |s|-1, \qquad s^\infty \prec \sigma^\ell t^\infty \preceq t^\infty,\ \ell = 1, \dots, |t|-1 \qquad (2.1)$$
> *do not* hold.  In dynamical systems theory this implies that the pair $(s^\infty, t^\infty)$ is the kneading invariant of an expanding Lorenz map [17]."  (p. 4)

Gloss (Ren): "do not hold" is to be read for each $k$ and $\ell$ separately, i.e. no proper shift of $s^\infty$ lands in $[s^\infty, t^\infty)$ and no proper shift of $t^\infty$ lands in $(s^\infty, t^\infty]$.  This is consistent with p. 7 ("$\mathcal J(s^\infty, t^\infty) \supset \{T^k(s^\infty) : k \ge 0\}$", "the pair $(s,t)$ is extremal by construction") and with the proofs of Lemmas 5.1 and 5.2 (p. 23-24), which derive contradictions from $s^\infty \prec \sigma^{j} s^\infty \prec t^\infty$.  In words: the periodic orbits of $s^\infty$ and $t^\infty$ themselves avoid the hole $(s^\infty, t^\infty)$.

Notation $S(s,t)$, $T(s,t)$ (p. 4-5): for $S = S(0,1) \in \{0,1\}^n$, $S(s,t)$ is obtained by substituting $s$ for each $0$ and $t$ for each $1$.  Convention: anything called $s$ or $S$ starts with $0$, anything called $t$ or $T$ starts with $1$.

### 1.6 Balanced words, Sturmian words, and the substitutions $\rho_r$ (p. 6-7)

Definitions (p. 6): $w$ is *balanced* if any two factors $u,v$ of equal length satisfy $\big||u|_1 - |v|_1\big| \le 1$; an infinite word is *Sturmian* if balanced and not eventually periodic; a finite word $w$ is *cyclically balanced* if $w^2$ is balanced.  "It is well known that if $u$ and $v$ are two cyclically balanced words with $|u| = |v| = q$ and $|u|_1 = |v|_1 = p$ and $\gcd(p,q) = 1$, then $u$ is a cyclic permutation of $v$.  Thus, there are only $q$ distinct cyclically balanced words of length $q$ with $p$ 1s."  (p. 6)

> "For any $r = p/q \in \mathbb Q \cap (0,1)$ we define the substitution $\rho_r$ on two symbols as follows: $\rho_r(0) = \omega_r^-$, the lexicographically largest cyclically balanced word of length $q$ with 1-ratio $r$ beginning with 0, and $\rho_r(1) = \omega_r^+$, the lexicographically smallest cyclically balanced word of length $q$ with 1-ratio $r$ beginning with 1."  (p. 6)

Remark 2.4 (p. 7) constructs $\omega_r^\pm$ from standard words: for $r = p/q \le 1/2$ with continued fraction $[d_1+1, \dots, d_n]$, set $u_{-1} = 1$, $u_0 = 0$, $u_{k+1} = u_k^{d_{k+1}} u_{k-1}$; $u_n = w_1 \dots w_q$ is the $n$-th standard word, and $\omega_r^- = 01 w_1 \dots w_{q-2}$, $\omega_r^+ = 10 w_1 \dots w_{q-2}$.  For irrational $\gamma$ the limit $u_\infty$ is the *characteristic word* of $\gamma$.  For $r > 1/2$, $\omega_r^\pm = h(\omega_{1-r}^\mp)$ with $h$ swapping the letters.  Example 2.5: $\rho_{2/5}(0) = 01010$, $\rho_{2/5}(1) = 10010$, $\rho_{3/5}(0) = 01101$, $\rho_{3/5}(1) = 10101$.

### 1.7 The plateau intervals and the exceptional sets (p. 7-11)

- $\Delta(r) = [(\omega_r^-)^\infty, \omega_r^- (\omega_r^+)^\infty]$ for $r \in \mathbb Q \cap (0,1)$ (p. 7).
- $\mathcal S := (1/4,1/2) \setminus \bigcup_{r} \Delta(r)$ has zero Hausdorff dimension, quoted from [25] as (2.2) (p. 7).  On p. 10: "$\mathcal S$ consists precisely of the points whose dyadic expansion is of the form $01w$, where $w$ is a characteristic word for some irrational $\gamma \in (0,1/2)$", and its dimension is zero because balanced words of length $N$ grow polynomially in $N$ [22].
- For a finite or infinite vector $\mathbf r = (r_1, r_2, \dots)$ of rationals in $(0,1)$ (p. 8): $s_n = \rho_{r_1} \cdots \rho_{r_n}(0)$, $t_n = \rho_{r_1} \cdots \rho_{r_n}(1)$; with $r_i = p_i/q_i$, $Q_n = q_1 \cdots q_n = |s_n| = |t_n|$.  Example 2.8: $r_1 = 1/2$, $r_2 = 1/3$ gives $s_2 = 011001$, $t_2 = 100101$.
- $\Delta(r_1, \dots, r_n) = [s_n^\infty, s_n t_n^\infty]$ and $\widetilde\Delta(r_1, \dots, r_n) = [s_n t_n s_n^\infty, s_n t_n^\infty]$ (p. 8).
- $\mathcal S_n(r_1, \dots, r_{n-1}) := \widetilde\Delta(r_1, \dots, r_{n-1}) \setminus \bigcup_{r_n} \Delta(r_1, \dots, r_n)$, (2.6), p. 9; $\mathsf S_1 = \mathcal S$, $\mathsf S_n = \bigcup \mathcal S_n(\cdot)$, $\mathsf S = \bigcup_n \mathsf S_n$ (p. 10).
- $\mathfrak s(\mathbf r) = \lim_n \rho_{r_1} \cdots \rho_{r_n}(0)$, $\mathfrak t(\mathbf r) = \lim_n \rho_{r_1} \cdots \rho_{r_n}(1)$ for infinite $\mathbf r$ (p. 11).

---

## 2. The four scenarios and their exact characterizations

The abstract (p. 1) lists: (i) $\mathcal J(a,b)$ contains a point $x \in (0,1)$; (ii) $\mathcal J(a,b) \cap [\delta, 1-\delta]$ is infinite for any fixed $\delta > 0$; (iii) $\mathcal J(a,b)$ is uncountable of zero Hausdorff dimension; (iv) $\mathcal J(a,b)$ is of positive Hausdorff dimension.  Everything below is for $(a,b)$ in the box $(1/4,1/2)\times(1/2,3/4)$ unless stated; outside it Lemma 1.1 settles all four.

### 2.1 Scenario (i): nonempty beyond the fixed points, i.e. $D_0$

> **Theorem 2.7.**  We have $D_0 = \{(a,b) \in (1/4,1/2)\times(1/2,3/4) : b \le \phi(a)\}$, where $\phi$ is given by Proposition 2.6.  (p. 8)

> **Proposition 2.6.**  If $a \in \Delta(r)$ for some $r \in \mathbb Q \cap (0,1)$, then $\phi(a) \equiv (\omega_r^+)^\infty$.  Thus, $\phi$ is piecewise constant with an infinite countable set of plateaus and the exceptional set $\mathcal S$.  (p. 7)

For $a \in \mathcal S$: $\phi(a) = \chi(a) = a + 1/4$ (Proposition 3.1, p. 13, with Theorem 2.13(ii)).  Bounds (Proposition 3.3, (3.2), p. 14): $a + 1/4 \le \phi(a) \le a + 1/3$, sharp.  The proof of Proposition 2.6 (p. 7-8) is the model for everything else: with $s = \omega_r^-$, $t = \omega_r^+$, one has $\mathcal J(s^\infty, t^\infty) = \{T^k(s^\infty) : k \ge 0\}$ (equality by [25, Cor. 3.6]), $\mathcal J(s^\infty, b) = \{0,1\}$ for $b > t^\infty$, and for $a \in (s^\infty, st^\infty]$, $T^q(a) \in [s^\infty, t^\infty]$, so $\phi$ is constant on $\Delta(r)$.  Only the *periodic* orbit of $s^\infty$ survives at the plateau value.

The paper's own name for the boundary of $D_0$ is "first order critical hole" (FOCH, Definition 3.4, p. 15); Theorem 3.7 (p. 16) lists them all: $(a,1/2)$ or $(1/2, 1-a)$ for $a \in (0,1/4]$; $(a, a+1/4)$ with $a \in \mathcal S$; $(s^\infty, b)$ with $s = \omega_r^-$, $b \in [ts^\infty, t^\infty]$; $(a, t^\infty)$ with $a \in (s^\infty, st^\infty]$.  "Consequently, the length of each FOCH can take an arbitrary value between $1/4$ and $1/2$."  Example 3.5: $(1/3, b)$ is a FOCH iff $b \in [7/12, 2/3]$.

### 2.2 Scenario (ii): infinitely many survivors away from the fixed points (p. 19-20)

Trivial version: if $\mathcal J(a,b)$ contains any $x \in (0,1/2)$ then it contains all $2^{-n} x$, so it is automatically infinite (p. 19).  The non-trivial version restricts to the attractor $[2b-1, 2a]$ of $T_{a,b} := T|_{\mathcal J(a,b)}$: $\widetilde D_0 = \{(a,b) : \mathcal J(a,b) \cap [2b-1, 2a] \text{ is infinite}\}$, with $D_1 \subsetneq \widetilde D_0 \subsetneq D_0$, and $\psi(a) = \sup\{b : \mathcal J(a,b) \cap [2b-1,2a] \text{ infinite}\}$ (4.4).  The paper sketches the formula rather than stating a theorem: $\psi(a) = a + 1/4$ for $a \in \mathcal S$; $\psi(a) = \chi(a) = ts^\infty$ for $a \in [s^\infty, sts^\infty]$ ("the set $\mathcal J(a,b)$ is a $q$-cycle together with its preimages, so it becomes a finite set when intersected with any interval which does not contain 0 or 1", p. 20); $\psi(a) = t_2^\infty$ for $a \in [s_2^\infty, s_2 t_2^\infty]$ (level 2).  Consequently

> $\tfrac{3}{16} \le \psi(a) - a \le \tfrac14$, both bounds being sharp.  (The lower one is attained at $a$ with the dyadic expansion $0110(01)^\infty$, for which $\psi(a)$ has the expansion $10(01)^\infty$.)  (p. 20)

> **Proposition 4.3.**  If $b - a < \tfrac{3}{16}$, then for any fixed $\delta > 0$ the set $\mathcal J(a,b) \cap [\delta, 1-\delta]$ is infinite.  (p. 20)

Also: replacing $[2b-1, 2a]$ by $[\delta, 1-\delta]$ for any $\delta \in (0, 2b-1)$ does not change $\psi$ (p. 20).  "Thus, whilst $\phi$ is determined on level 1 and $\chi$ may require an infinite descent, $\psi$ is determined on level 1 or 2."

### 2.3 Scenario (iv): positive Hausdorff dimension, i.e. the function $\chi$

> **Theorem 1.2.**  We have $\{(a,b) \in (0,1/2)\times(1/2,1) : \dim_H \mathcal J(a,b) > 0\} = \{(a,b) : b < \chi(a)\}$, where $\chi$ is given by Theorem 2.13.  (p. 3)

This rests on the quoted result of Labarca and Moreira:

> **Theorem 2.3.**  ([18, Theorem 2]) We have $\{(a,b) \in (1/4,1/2)\times(1/2,3/4) : \dim_H \mathcal J(a,b) > 0\} = \{(a,b) : b < \chi(a)\}$.  (p. 6)

So the dimension is zero exactly on and above the graph of $\chi$, and the paper's contribution is the explicit formula:

> **Theorem 2.13.**  Any $a \in (1/4,1/2)$ falls into one of the following four categories:
> (i) Let $s_n = \rho_{r_1} \cdots \rho_{r_n}(0)$, $t_n = \rho_{r_1} \cdots \rho_{r_n}(1)$.  We have $\chi(a) \equiv t_n s_n^\infty$ for all $a \in [s_n^\infty, s_n t_n s_n^\infty]$.  (2.11)  Furthermore, $\chi(a) < t_n s_n^\infty$ for any $a < s_n^\infty$ and $\chi(a) > t_n s_n^\infty$ for any $a > s_n t_n s_n^\infty$, so this is an actual plateau of the function $\chi$.
> (ii) If $a \in \mathcal S$, then $\chi(a) = a + 1/4$.
> (iii) If $a \in \mathcal S_n(r_1, \dots, r_{n-1})$ for $n \ge 2$, then $\chi(a) = a + (1 - 2^{-Q_{n-1}})(t_{n-1} - s_{n-1})$.
> (iv) If there exists $(r_1, r_2, \dots)$ such that $a \in \widetilde\Delta(r_1, \dots, r_n)$ for all $n \ge 1$, then $a = \mathfrak s(\mathbf r)$, and $\chi(a) = \mathfrak t(\mathbf r)$.  (p. 11)

So the plateaus of $\chi$ are indexed by finite sequences of rationals $(r_1, \dots, r_n)$ (a "renormalization" tower of substitutions), the level-1 exceptional set is Sturmian (characteristic words of irrational rotation numbers), the level-$n$ exceptional sets are Sturmian words substituted through $\rho_{r_1} \cdots \rho_{r_{n-1}}$, and the infinite-descent points $\mathfrak s(\mathbf r)$ form a Cantor set of dimension $\approx 0.4732$ (Remark 2.15, p. 13; Proposition 4.2, p. 18, where the dimension $s$ solves $\sum_{q\ge2} \varphi(q)/4^{qs} = 1$, $s \approx 0.473223$).  Corollary 2.14 (p. 13): "$\chi$ is piecewise constant on a subset of $(1/4,1/2)$ whose complement $\mathsf S \cup \{\mathfrak s(\mathbf r)\}$ is nowhere dense."  The period-doubling route $\mathbf r = (1/2, 1/2, \dots)$ gives $\mathfrak s(\mathbf r) = a_*$, the Thue-Morse constant, and $\mathfrak t(\mathbf r) = 1 - a_*$.

Bounds and the sharp threshold:

> **Proposition 3.3.**  We have (3.2) $a + \tfrac14 \le \phi(a) \le a + \tfrac13$, $a \in (\tfrac14, \tfrac12)$, and (3.3) $a + 1 - 2a_* \le \chi(a) \le a + \tfrac14$, $a \in (\tfrac14, \tfrac12)$, where $a_* = \lim_{n\to\infty} \rho_{1/2}^n(0) \approx 0.412454$, i.e., the dyadic expansion of the Thue-Morse sequence sometimes called the Thue-Morse constant [26].  Furthermore, all these bounds are sharp.  (p. 14)

> **Corollary 3.9.**  The smallest length of a SOCH is $1 - 2a_* \approx 0.175092$.  Consequently, $\dim_H \mathcal J(a,b) > 0$ if $b - a < 1 - 2a_*$.  Assuming $a \in (1/4, 1/2)$, the maximum length of a SOCH is $1/4$ and it is attained if and only if $a \in \mathcal S$.  (p. 17)

Here a "second order critical hole" (SOCH, Definition 3.6, p. 16) is $(a_0, b_0)$ such that every strictly larger hole has countable survivor set and every strictly smaller hole has positive-dimension survivor set; Theorem 3.8 (p. 16-17) lists them: $(a,1/2)$ or $(1/2,1-a)$ for $a \in (0,1/4]$; $(a, a+1/4)$ for $a \in \mathcal S$; $(a, a + (1-2^{-Q_{n-1}})(t_{n-1} - s_{n-1}))$ for $a \in \mathcal S_n(\cdot)$; $(s_n^\infty, b)$ with $b \in [t_n s_n t_n^\infty, t_n^\infty]$; $(a, t_n s_n^\infty)$ with $a \in (s_n^\infty, s_n t_n s_n^\infty]$; $(\mathfrak s(\mathbf r), \mathfrak t(\mathbf r))$.  Note $1 - 2a_* = \tfrac14 \prod_{n\ge1}(1 - 2^{-2^n})$, the constant in the abstract.

### 2.4 Scenario (iii): uncountable but zero-dimensional

> **Proposition 4.5.**  The set $\mathcal J(a, \chi(a))$ is uncountable of zero Hausdorff dimension if and only if $a \in \mathcal S$ or $a = \mathfrak s(\mathbf r)$ for some $\mathbf r \in (\mathbb Q \cap (0,1))^{\mathbb N}$.  (p. 22)

> **Theorem 4.6.**  The set $\mathcal J(a,b)$ is uncountable of zero Hausdorff dimension if and only if $a \in \mathcal S$ and $b = a + 1/4$ or $a = \mathfrak s(\mathbf r)$ and $b = \mathfrak t(\mathbf r)$ for some $\mathbf r \in (\mathbb Q \cap (0,1))^{\mathbb N}$.  (p. 23)

Proof content (p. 22-23): zero dimension at $b = \chi(a)$ is [18, Theorem 2].  For $a \in \mathcal S$, $X_\gamma := \overline{\{T^n a : n \ge 0\}}$ is the Sturmian system with 1-ratio $\gamma$ (from [25, Section 2]); $a$ is its largest element beginning with $0$ and $\chi(a) = a + 1/4$ its smallest beginning with $1$, so $X_\gamma \cap (a, \chi(a)) = \emptyset$ and $\mathcal J(a, \chi(a)) \supset X_\gamma$, which has the cardinality of the continuum.  For $a = \mathfrak s(\mathbf r)$: "$s_1^{i_1} s_2^{i_2} \dots \in \mathcal J(\mathfrak s(\mathbf r), \mathfrak t(\mathbf r))$, $i_m \ge 1$, $m \ge 1$" (4.5), using the reflection inequalities (4.6) $\sigma^k(s_n) s_n^\infty \prec s_n^\infty$, $\sigma^k(t_n) s_n^\infty \prec s_n^\infty$ from Lemma 5.1.  For $a$ on a plateau the survivor set at $b = \chi(a)$ is countable by Lemma 2.12 and monotonicity.

**Ren's reading of the trichotomy in the box.**  For $(a,b) \in (1/4,1/2)\times(1/2,3/4)$: $b > \phi(a)$ gives $\{0,1\}$; $\chi(a) < b \le \phi(a)$ gives countably infinite (and, from the proofs of Lemma 2.12 and Proposition 4.4, consisting of preimages of the periodic points $s_n^\infty$, $t_n^\infty$, so all survivors are rational); $b = \chi(a)$ gives countable unless $a \in \mathcal S \cup \{\mathfrak s(\mathbf r)\}$, where it is uncountable of dimension zero; $b < \chi(a)$ gives positive dimension.  The uncountable-zero-dimension case therefore requires an endpoint $a$ that is *not* eventually periodic (a characteristic Sturmian word, or an infinite substitution limit), i.e. an irrational endpoint.  This matters for section 6.

---

## 3. The structural lemmas and the proof idea of the threshold

### 3.1 Renormalization of extremal pairs (p. 5, proofs p. 23-25)

> **Proposition 2.1.**  If $(s,t)$ and $(S,T)$ are extremal pairs, then so is $(S(s,t), T(s,t))$.  (p. 5)

"Note that we do not actually need that $(S,T)$ are well-ordered or that the length of $s$ and $t$ are equal ... This result is essentially part of the argument in [14], though the proof below is considerably shorter."  The proof (Appendix, p. 23-25) goes through:

> **Lemma 5.1.**  Suppose that $(s,t)$ is an extremal pair with $|s| = N$.  If (5.1) $\sigma^j s^\infty \prec s^\infty$ for some $j \in \{1, \dots, N-1\}$ and (5.2) $s_{j+1} \dots s_N = s_1 \dots s_{N-j}$ then $s_{N-j+1} = 1$.  An analogous statement holds for shifts of $t$.  (p. 23)

> **Lemma 5.2.**  We have (5.5) $\sigma^k I_L \cap (s^\infty, t^\infty) = \emptyset$, $k = 1, \dots, |s|-1$, with a similar equation holding for $I_R$,  (p. 24)

where $I_L = [s^\infty, st^\infty]$, $I_R = [ts^\infty, t^\infty]$ (5.4).  Any concatenation of $s$ and $t$ lies in $I_L \cup I_R$, in particular $S(s,t)^\infty \in I_L$ and $T(s,t)^\infty \in I_R$ (p. 23).  By induction on $n$ using Proposition 2.1, $(s_n, t_n)$ is extremal for every $\mathbf r$ (p. 12).

### 3.2 The positive-entropy witness (p. 5, proof p. 25)

Let $t$ be a cyclic permutation of $s$: $s_{\ell+1} \dots s_N s_1 \dots s_\ell = t_1 \dots t_N$.  For $(n_1, n_2, \dots) \in \mathbb N^\infty$ put $w(n_1, n_2, \dots) = s^{n_1} s_1 \dots s_\ell\, s^{n_2} s_1 \dots s_\ell \cdots$ and

> $W_n = \overline{\{\sigma^j w(n_1, n_2, \dots) \mid n_i \in \{n, n+1\} \text{ for all } i \text{ and } j \ge 0\}}$.  (p. 5)

"Clearly, $\sigma W_n = W_n$.  Since we have $n_i \in \{n, n+1\}$ without restrictions, the number of 0-1 words of length $N$ which can be extended to sequences in $W_n$ grows exponentially with $N$, whence $h_{top}(\sigma|_{W_n}) > 0$."

> **Proposition 2.2.**  For any 0-1 word $u \in (st^\infty, ts^\infty)$ there exists $n \in \mathbb N$ such that $W_n \cap (s^\infty, u) = \emptyset$.  (p. 5)

So for every hole $(s^\infty, u)$ with $u \prec ts^\infty$ the survivor set contains the positive-entropy subshift $W_n$, hence has positive dimension.  Combined with Proposition 2.1 this gives (2.12) $t_n s_n^\infty \preceq \chi(s_n^\infty)$ (p. 12).  The proof (p. 25) checks the shifts of $v \in W_n$ in the four positions $j \le (n_1-1)N$, $k = \ell$, $\ell < k < \ell + N$, $k = \ell + N$ using (2.1) and Lemma 5.2.

### 3.3 Tiling by plateaus and the exceptional sets (p. 8-10)

> **Lemma 2.10.**  Fix $(r_1, \dots, r_{n-1})$.  Then for any $r_n \in \mathbb Q \cap (0,1)$ we have (2.3) $\Delta(r_1, \dots, r_n) \subset \widetilde\Delta(r_1, \dots, r_{n-1})$.  Furthermore, (2.4) $\Delta(r_1, \dots, r_n) \cap \Delta(r_1', \dots, r_n') = \emptyset$ if $(r_1, \dots, r_n) \ne (r_1', \dots, r_n')$.  Finally, (2.5) $\dim_H \mathcal S_n(r_1, \dots, r_{n-1}) = 0$.  (p. 8-9)

Key computation in the proof (p. 9): for $s = 01w$, $t = 10w$ of length $q$, $st^\infty - s^\infty = 2^{-q}(t^\infty - s^\infty)$ and $t^\infty - s^\infty = \tfrac14 + st^\infty - s^\infty$, whence $|[s^\infty, t^\infty]| = \tfrac{2^q}{4(2^q - 1)}$ and $|\Delta(p/q)| = \tfrac{1}{4(2^q-1)}$; then

> $\sum_{q \ge 2,\ 1 \le p < q,\ \gcd(p,q)=1} |\Delta(p/q)| = \sum_{q=2}^\infty \frac{\varphi(q)}{4(2^q-1)}$  (2.7)

equals $1/4$ by $\sum_{q\ge1} \varphi(q) x^q/(1-x^q) = x/(1-x)^2$ at $x = 1/2$ (2.8), so the $\Delta(p/q)$ tile $(1/4,1/2)$ up to a null set, and (2.4) follows.  Proposition 2.11 (p. 10): $\mathsf S = \bigcup_n \mathsf S_n$ has zero Hausdorff dimension.

### 3.4 Countability on the plateau (p. 10-11)

> **Lemma 2.12.**  The set $\mathcal J(s_n^\infty, t_n^\infty)$ is infinite countable for any $r_1, \dots, r_n$.  (p. 10)

"The following key result is a generalization of [14, Lemma 12], where it was proved for the case $\mathbf r = (1/2, 1/2, \dots)$.  Note that our proof for the general case is completely different from that for the special case in question."  The proof uses the rotation property of cyclically balanced words: with $w_0 \prec \dots \prec w_{q-1}$ the cyclically balanced words of length $q$ with $p$ ones, there is $p'$ with (2.10) $\sigma(w_j^\infty) = w_{j+p' \bmod q}^\infty$ [15].  Under $T_k := T^{Q_k}$ the intervals $J_i = [x_i, x_{i+1}]$ between consecutive shifts of $s_{k+1}^\infty$ are permuted, $T_k(J_i) = J_{i+p' \bmod q}$, so every $x \in [x_0, x_{q-1}]$ has some iterate in $[s_{k+1}^\infty, t_{k+1}^\infty]$, "Thus, there can be only countably many $x \in (x_0, x_{q-1})$ whose trajectories do not fall into the hole $(s_{k+1}^\infty, t_{k+1}^\infty)$" (p. 11).  This is the mechanism for (2.13) $t_n s_n^\infty \succeq \chi(s_n t_n s_n^\infty)$ (p. 12): the survivors of a hole slightly larger than the plateau hole differ from $\mathcal J(s_n^\infty, t_n^\infty)$ by a countable set.

### 3.5 Lengths and the sharp threshold (p. 14-15, 17)

> **Lemma 3.2.**  Let $n \ge 2$, $\mathbf r = (r_1, \dots, r_n)$ and $s_n, t_n$ as above.  Then the length of the interval $[s_n^\infty, t_n^\infty]$ is equal to $\frac{1}{4(1 - 2^{-Q_n})} \cdot \prod_{j=1}^{n-1} (1 - 2^{-Q_j})$, where, as above, $Q_j = q_1 \cdots q_j$.  (p. 14)

with (3.1) $t_n - s_n = (1 - 2^{-Q_{n-1}}) \cdots (1 - 2^{-Q_1})(t_1 - s_1) = \tfrac14 \prod_{j=1}^{n-1}(1 - 2^{-Q_j})$, from $s_n = s_{n-1} t_{n-1} w$, $t_n = t_{n-1} s_{n-1} w$.

**Proof idea of the threshold $\approx 0.175092$ (p. 15).**  Since the complement of $\bigcup_{\mathbf r} \Delta(\mathbf r)$ is nowhere dense it suffices to bound $\chi(a) - a$ on the plateaus.  On $\Delta(\mathbf r)$, Theorem 2.13(i) and (3.1) give the upper bound $\chi(a) - a \le t_n s_n^\infty - s_n^\infty = t_n - s_n = \tfrac14 \prod_{j=1}^{n-1}(1 - 2^{-Q_j}) \le \tfrac14$, and the lower bound

$$\chi(a) - a \ge t_n s_n^\infty - s_n t_n s_n^\infty = t_n s_n - s_n t_n = \tfrac14 (1 - 2^{-Q_n}) \prod_{j=1}^{n-1}(1 - 2^{-Q_j}) = \tfrac14 \prod_{j=1}^{n}(1 - 2^{-Q_j}) \ge \tfrac14 \prod_{j=1}^{n}(1 - 2^{-2^j}),$$

"(We use the fact that $Q_j \ge 2^j$ with the equality only if $q_j \equiv 2$ for all $j$, which corresponds to $r_j \equiv 1/2$.)  Therefore, $\chi(a) - a \ge \tfrac14 \prod_{j=1}^\infty (1 - 2^{-2^j}) = 1 - 2a_*$, with the equality at $\mathbf r = (1/2, 1/2, \dots)$, i.e., at $a = a_*$."  So the worst hole is the symmetric Thue-Morse hole $(a_*, 1 - a_*)$: each level of renormalization multiplies the plateau width by $(1 - 2^{-Q_j})$, and the product is smallest when every level is the period-doubling substitution $\rho_{1/2}$ ($0 \mapsto 01$, $1 \mapsto 10$), whose fixed point is Thue-Morse.  Corollary 3.9 then converts this into the abstract's statement.

### 3.6 Periodic orbits and "routes to chaos" (p. 20-22)

> **Proposition 4.4.**  If $a \in (s_n^\infty, s_{n+1}^\infty)$ and $b \in (t_{n+1}^\infty, t_n^\infty)$, then $T_{a,b}$ has a $k$-cycle if and only if $k \in \{Q_1, \dots, Q_{n+1}\}$.  (p. 21)

Proof: "$X_n := \mathcal J(s_{n+1}^\infty, t_{n+1}^\infty) \setminus \mathcal J(s_n^\infty, t_n^\infty)$ is contained in the set of preimages of $s_{n+1}^\infty$ and $t_{n+1}^\infty$.  Therefore, the only purely periodic points in $X_n$ are $s_{n+1}^\infty$ and $t_{n+1}^\infty$ themselves, both of period $Q_{n+1}$."  Each rectangle $(s_n^\infty, s_{n+1}^\infty) \times (t_{n+1}^\infty, t_n^\infty)$ is "frequency locked", an Arnold tongue (p. 22).  For symmetric holes $(a, 1-a)$ one gets the Sharkovskii period-doubling cascade: 2-cycle at $a = 1/3$, 4-cycle at $2/5$, ..., up to $a_*$ (p. 20).

---

## 4. Unions of intervals, several holes, general open sets; periodic points; length vs dimension

### 4.1 Does the paper treat anything but one interval?

No.  The hole is a single open interval $(a,b)$ from the abstract (p. 1) and definition (p. 2) to the end.  The only other subsets of $[0,1]$ that appear are the attractor $[2b-1, 2a]$ of $T_{a,b}$ (p. 19), the symbolic sets $\Sigma_n$, $W_n$, $X_\gamma$, and the parameter-space sets $\Delta$, $\widetilde\Delta$, $\mathcal S$, $\Omega$.  There is no statement about two holes, unions of intervals, or general open sets, and no remark that the methods would extend to them.

The cited literature (from the reference list, p. 25-26; only [25] opened, see section 7):

- [25] Sidorov, *Supercritical holes for the doubling map*, arXiv:1204.1920: defines a hole as "an open connected set" and characterizes holes $H_0$ such that every strictly larger hole leaves only fixed points and every strictly smaller one leaves positive dimension.  Single connected hole only.
- [14] Glendinning and Sparrow, *Prime and renormalisable kneading invariants and the dynamics of expanding Lorenz maps*; [17] Hubbard and Sparrow; [18] Labarca and Moreira, *Essential dynamics for Lorenz maps on the real line and the Lexicographical World*: the Lorenz-map / lexicographic-world sources, all about one pair of kneading sequences, i.e. one hole (not opened).
- [4] Bundfuss, Krüger and Troubetzkoy, *Topological and symbolic dynamics for hyperbolic systems with holes* and [5]-[7] Chernov, Markarian, Troubetzkoy on Anosov maps with rectangular or small holes: cited on p. 1 as "a growing body of work describing the effect of holes on hyperbolic systems"; these do allow more general (Markov) holes but are not used in the paper (not opened).
- Not cited (it is later), but the closest thing in the literature to a union of intervals: Allaart and Kong, arXiv:2411.03516, Section 8, treats the map $kx \bmod 1$ with $k-1$ holes that are translates of one interval by multiples of $1/k$; see section 7.

### 4.2 What the paper says about holes and periodic points

- Lemma 1.1(i) (p. 2): a hole containing the cylinder $[01]$ (i.e. $[1/4, 1/2)$) or $[10]$ kills every orbit except the two fixed points, because every non-fixed orbit's expansion contains $01$ and $10$.
- Proposition 2.6's proof (p. 7): at the plateau hole $(s^\infty, t^\infty)$ the survivor set is exactly the periodic orbit of $s^\infty$ (which is also the orbit of $t^\infty$, a cyclic permutation): "$\mathcal J(s^\infty, t^\infty) \supset \{T^k(s^\infty) : k \ge 0\}$.  In fact, we have an equality here (see [25, Corollary 3.6])".
- p. 20: for $a \in [s^\infty, sts^\infty]$ and $b \in [ts^\infty, t^\infty]$, "the set $\mathcal J(a,b)$ is a $q$-cycle together with its preimages".
- Proposition 4.4 (p. 21) and the "routes to chaos" discussion (p. 20-22): the periodic orbits that survive a hole in the rectangle indexed by $(r_1, \dots, r_{n+1})$ have exactly the periods $Q_1, \dots, Q_{n+1}$; the order in which cycles appear as the hole shrinks generalizes the Sharkovskii order (p. 22: "It would be interesting to construct meaningful analogues of the classical Sharkovskii order for each $\mathbf r$").
- The notion "an integer $n$ is bad for $(a,b)$ if every $n$-cycle intersects $(a,b)$" is from Hare and Sidorov and Clark (see section 7), not from this paper.

### 4.3 Hole length versus dimension

- Lemma 1.1 (p. 2): any hole inside $[0,1/2)$ or $(1/2,1]$, whatever its length, leaves positive dimension; any hole containing $[1/4,1/2]$ or $[1/2,3/4]$ (length $\ge 1/4$, straddling $1/2$) leaves only $\{0,1\}$.
- Corollary 3.9 (p. 17): $b - a < 1 - 2a_* \approx 0.175092$ implies $\dim_H \mathcal J(a,b) > 0$, sharp at $(a_*, 1 - a_*)$; the longest zero-dimension-critical hole with $a \in (1/4,1/2)$ has length $1/4$, attained exactly at the Sturmian endpoints $a \in \mathcal S$.
- Proposition 3.3 (p. 14): $1 - 2a_* \le \chi(a) - a \le 1/4$ and $1/4 \le \phi(a) - a \le 1/3$, all sharp.  Theorem 3.7 (p. 16): first-order critical holes have every length in $[1/4, 1/2]$.
- Lemma 3.2 / (3.1) (p. 14): the plateau hole at level $n$ has length $\tfrac14 \prod_{j<n}(1 - 2^{-Q_j}) \cdot (1 - 2^{-Q_n})^{-1}$; each renormalization level shrinks the critical length by the factor $(1 - 2^{-Q_j})$.
- Proposition 4.3 (p. 20): $b - a < 3/16$ implies infinitely many survivors in every $[\delta, 1-\delta]$.
- Position matters as much as length: the paper's whole point is that the threshold is a curve $b = \chi(a)$, not a number (Figure 1, p. 4; Figure 3, p. 21 in the coordinates $u = b + a$, $v = \tfrac14 + b - a$).

---

## 5. Subshifts of finite type, sofic shifts, rational versus irrational survivors

What the paper says:

- The only explicit SFT is $\Sigma_n$ in the proof of Lemma 1.1(ii) (p. 3), used to lower-bound dimension by entropy: $\dim_H \pi(\Sigma_n) = h_{top}(\sigma|_{\Sigma_n})/\log 2$.  The words "sofic" and "finite type" do not otherwise occur; the paper never discusses rational or dyadic endpoints as a special class.
- Survivor sets are described lexicographically, as sets of sequences whose shifts avoid $(a,b)$, and the paper freely replaces the hole $(a,b)$ by $(s_n^\infty, t_n^\infty)$ or $(s_n t_n s_n^\infty, t_n s_n^\infty)$ with **periodic or eventually periodic** endpoints, i.e. by holes with rational (odd-denominator) endpoints; on these the survivor set is countable and consists of preimages of periodic points (Lemma 2.12, p. 10-11; p. 20; Proposition 4.4, p. 21).  At the endpoints of a plateau the survivor set is the single periodic orbit of $s^\infty$ (p. 7).
- Irrational survivors in the zero-dimension regime occur only at $a \in \mathcal S$ (Sturmian survivors, Proposition 4.5, p. 22) or $a = \mathfrak s(\mathbf r)$ (the survivors $s_1^{i_1} s_2^{i_2} \cdots$, (4.5), p. 22), both of which are non-eventually-periodic (irrational) endpoints.
- Dimension formula: the paper uses $\dim_H = h_{top}/\log 2$ only for the SFT $\Sigma_n$ (p. 3); the general zero/positive dichotomy at $\chi$ is imported from [18].

**Ren's inference (not stated in the paper).**  For a hole with rational endpoints the survivor set is a sofic shift (argument in 6.2 below), and a sofic shift either has positive entropy or consists entirely of eventually periodic sequences.  This is consistent with, and explains, the paper's picture: every zero-dimension-uncountable case in Theorem 4.6 has an irrational endpoint, and every rational-endpoint hole in the paper (plateau holes) has either positive dimension or a countable, all-rational survivor set.

---

## 6. Transferability assessment (Ren's own analysis)

Notation for our problem: base $g \ge 2$, block $w$ of length $k$, $[w] = [0.w, 0.w + g^{-k})$ the cylinder, $T t = gt \bmod 1$, $M_m t = mt \bmod 1$, $H(m,w) = \{t : \text{first } k \text{ digits of } M_m t \text{ are } w\}$, $J(S,w) = \{t : T^n t \notin \bigcup_{m\in S} H(m,w)\ \forall n \ge 0\}$.  All statements below are mine; confidence levels are given where the claim rests on something I did not re-derive in full.

### 6.1 A cleaner description of our survivor set (confidence 95%)

$M_m$ commutes with $T$ on the circle ($T M_m t = M_m T t = gmt \bmod 1$), and $H(m,w) = M_m^{-1}([w])$.  Hence $T^n t \notin H(m,w)$ iff $T^n(M_m t) \notin [w]$, so

$$J(S,w) = \bigcap_{m \in S} M_m^{-1}\big(J_w\big), \qquad J_w := \{x : T^n x \notin [w]\ \forall n \ge 0\} = \pi(X_w),$$

where $X_w$ is the SFT of $w$-free sequences (the survivor set of the single cylinder hole).  "$S$ hits $w$" is exactly "$J(S,w)$ contains no irrational" (an irrational $\alpha$ with $w$ occurring only finitely often in every $m\alpha$ has some $T^N \alpha \in J(S,w)$, and conversely).  So our object is an intersection of pullbacks of one fixed SFT under the circle endomorphisms $M_m$, and every pullback has the same Hausdorff dimension as $X_w$ (each $M_m$ is a local similarity).  The whole difficulty is in the intersection.  Note also that $H(m,w)$ is invariant under translation by $1/m$ (not by $1/g$), and that none of its $m$ components straddles a discontinuity $j/g$ of $T$ except by accident.  This is the structural reason the single-hole machinery does not apply (6.3).

### 6.2 What transfers: survivor sets of rational holes are sofic, so "hits" is decidable and equals "zero entropy" (confidence 90%)

Let $H = \bigcup_{i=1}^N (p_i, q_i)$ with all $p_i, q_i$ rational (every $H(m,w)$ is of this form: endpoints $(j + 0.w)/m$ and $(j + 0.w + g^{-k})/m$, $j = 0, \dots, m-1$, denominators $m g^k$).  Rational numbers have eventually periodic base-$g$ expansions.  For an eventually periodic $p$, the set of finite words $u$ with $u 0^\infty \succ p$ (equivalently, $u$ already witnesses $x \succ p$ for every $x$ extending $u$) is a regular language: an automaton reads $u$ while tracking its position in the preperiod/period of $p$ and the three states "equal so far / decided greater / decided less".  Likewise for $u 1^\infty \prec q$.  So $L_H := \{u : [u] \subset H\}$ is regular, and the symbolic survivor set

$$X_H := \{x \in \{0, \dots, g-1\}^{\mathbb N} : \text{no } \sigma^n x \text{ has a prefix in } L_H\}$$

is the subshift obtained by forbidding a regular language, hence **sofic**.  Irrational survivors of $H$ correspond exactly to non-eventually-periodic points of $X_H$ (the only discrepancies between $J(H)$ and $\pi(X_H)$ are orbits hitting an endpoint of some $(p_i,q_i)$, all rational).

Two standard facts about a sofic shift $X$ with a right-resolving presentation $G$: (a) $h_{top}(X) = 0$ iff every strongly connected component of $G$ is a single cycle, in which case every point of $X$ is eventually periodic and $X$ has finitely many periodic orbits; (b) $h_{top}(X) > 0$ iff $X$ contains an irreducible SFT of positive entropy, in which case $\pi(X)$ has positive Hausdorff dimension (the same step as Lemma 1.1(ii), p. 3) and $X$ has infinitely many periodic orbits (finite-to-one right-resolving codes preserve exponential growth of periodic points).  Therefore, for every finite $S$, block $w$ and base $g$:

> $S$ hits $w$ $\iff$ $h_{top}(X_{S,w}) = 0$ $\iff$ $\dim_H J(S,w) = 0$ $\iff$ only finitely many periodic orbits of $t \mapsto gt \bmod 1$ avoid $\bigcup_{m\in S} H(m,w)$ $\iff$ for all sufficiently large $n$, every purely periodic $\alpha$ of period $n$ (denominator $g^n - 1$) has $w$ in the period of $m\alpha$ for some $m \in S$.

Consequences.

1. The paper's scenario (iii), uncountable survivor set of dimension zero with Sturmian or substitution-limit survivors, **cannot occur** for our holes.  Those survivors need an irrational hole endpoint (section 2.4 and 5).  For us the trichotomy collapses to "positive dimension" versus "all survivors eventually periodic".
2. "$S$ hits $w$" is decidable by a finite computation: build the product automaton of the $|S|$ per-channel automata (each of size roughly $m g^k$ times a small constant, for the period of $1/m$ in base $g$), take the survivor subshift, and check that every strongly connected component is a single cycle.  This is exactly the kind of computation that could certify the known values $S(2,3) = 4$, $S(3,2) = 6$, $S(6,1) = 7$ and test N5 for the next few $(g,k)$; I do not know how those values were originally obtained, so this may or may not be new.
3. The last equivalence turns the "no irrational" condition into a statement about periodic orbits only, which is the "bad $n$" language of Hare-Sidorov and Clark (section 7): $S$ hits $w$ iff the set of bad periods is cofinite.  It also gives a cheap **necessary** test for a candidate $S$: enumerate periodic $\alpha$ of period $n$ for moderate $n$ and count survivors; exponential growth in $n$ refutes hitting.

Sanity check at $g = 2$, $k = 2$, $S = \{1, 3\}$, $w = 00$: a $00$-free irrational $x$ has isolated zeros and infinitely many $11$ factors; in the addition $x + 2x$ every column sum is $\ge 1$, so a carry generated at any $11$ propagates all the way left, and the digits of $3x$ are $1$ at the $11$ columns and $0$ at the $10$ and $01$ columns, producing $00$ at every isolated zero of $x$.  So $3x$ contains $00$ infinitely often, consistent with $S(2,2) = 2$.  The carry automaton is the concrete form of the sofic structure at base 2.

### 6.3 What does not transfer: the lexicographic-interval (Lorenz) structure and everything built on it (confidence 90%)

The paper's combinatorics needs the survivor set to be a **two-sided lexicographic interval subshift**, $\{x : \text{every } \sigma^n x \preceq a \text{ or } \succeq b\}$ with one pair $(a,b)$ straddling the discontinuity $1/2$.  That is what makes (a) the hole equivalent to a kneading pair of a Lorenz map, (b) extremal pairs closed under substitution (Proposition 2.1), (c) the plateaus indexed by rationals $r$ via the balanced words $\omega_r^\pm$, (d) the threshold a product over renormalization levels (Lemma 3.2), minimized by period doubling (Thue-Morse).  Allaart and Kong (arXiv:2411.03516, Section 8) show how far this stretches: for $T_k x = kx \bmod 1$ with $k-1$ holes $H_j = (a + \tfrac{j-1}{k}, b + \tfrac{j-1}{k})$, $0 < a < 1/k < b < a + 1/k$, i.e. **one hole around each discontinuity $j/k$, all translates by $1/k$**, the survivor set is again a lexicographic interval subshift $\Sigma_{\mathbf b', \mathbf a'} = \{z : \mathbf b' \preceq \sigma^n z \preceq \mathbf a'\}$ up to a countable set, and reduces to their $\beta$-transformation-with-a-hole-at-0 theory.  The two ingredients are (i) each hole straddles a discontinuity, so "avoid $H_j$" becomes "digit $j-1$ forces $\sigma^{n+1} z \preceq \mathbf a'$, digit $j$ forces $\sigma^{n+1} z \succeq \mathbf b'$", and (ii) the translates by $1/k$ make the same $(\mathbf a', \mathbf b')$ work in every digit cell.

Our holes fail both ingredients.  $H(m,w)$ is a union of $m$ intervals spaced by $1/m$; for $m$ not a power of $g$ they are not aligned with the digit cells $[j/g, (j+1)/g)$, and they do not straddle the discontinuities.  Even the single channel $m = 1$ (hole $= [w]$) is not of the Lorenz type: a cylinder never straddles $1/2$ (Lemma 1.1(ii) applies and gives positive dimension for $k \ge 1$, which is just "one channel never hits a block of length $\ge 2$" at base 2 in the paper's language, and $S(2,1) = 1$ is the boundary case $b = 1/2$).  The only channel-1 blocks that fit an existing theory are $w = 0^k$ and $w = (g-1)^k$: $[0^k] = [0, g^{-k})$ is a hole at $0$ in the sense of Kalle et al. and Allaart-Kong, and the survivor set is the plateau SFT of $0^k$-free sequences.  So there is no reduction of $J(S,w)$ to a single pair of lexicographic bounds, and I see no analogue of extremal pairs, $\rho_r$, or the product formula.  The Thue-Morse threshold $0.175092$ is a statement about the *position-optimal* single interval; it says nothing about a union.

Two remarks on position, for calibration (confidence 80%; both follow from Glendinning and Sidorov's 2001 result on unique $\beta$-expansions plus Urbański's $\tau(2) = 1/2$ as quoted in Allaart-Kong Section 1.1).  A single arc of the circle around the fixed point $0$, i.e. $[0,\delta) \cup (1-\delta, 1)$, leaves positive dimension iff $\delta < 1 - 2a_*$, total length $2(1 - 2a_*) \approx 0.350$, twice the threshold for the arc around $1/2$; and the one-sided hole $[0,t)$ needs $t \ge 1/2$.  The same Thue-Morse constant governs all three, but the critical *measure* varies by a factor of almost 3 with position.  Any lower bound for unions must therefore be position-aware or use the specific arithmetic of $H(m,w)$.

### 6.4 The route "N intervals each shorter than $c/N$ implies positive dimension" is closed (confidence 85% on the citation, 95% on the conclusion given it)

No such bound exists, not even with "positive dimension" weakened to "nonempty".  Mykkeltveit (1972, proving Golomb's conjecture on de Bruijn graphs) showed that the minimum size of an *unavoidable* set of binary words of length $n$ (a set $U_n$ such that every infinite binary word contains some element of $U_n$ as a factor) equals the number of binary necklaces of length $n$, which is $\sim 2^n/n$.  Take $H_n = \bigcup_{u \in U_n} [u]$: a union of $N \sim 2^n/n$ intervals of length $2^{-n} < c/N$ for every fixed $c > 0$ once $n > 1/c$, total measure $\sim 1/n \to 0$, and yet **every** orbit of the doubling map enters $H_n$ within a bounded number of steps, so the survivor set is empty.  The same works in base $g$.  Hence a hypothesis on the number and lengths of the components alone can never force survivors; the necklace lower bound $\ge 2^n/n$ also shows this construction is optimal among unions of cylinders of one length.  (I have not opened Mykkeltveit's paper this session; the lower bound direction, that an unavoidable set of $n$-words must hit each of the $\sim 2^n/n$ vertex-disjoint necklace cycles of the de Bruijn graph, is elementary.)

What survives of this route is a weaker, weighted statement that I believe is provable by the Lovász local lemma / entropy-compression arguments for subshifts avoiding sparse forbidden sets (Rumyantsev-Ushakov 2006, Miller 2012; constants not verified): if the hole is a union of intervals $I_j$ with $\sum_j |I_j| \log_g(1/|I_j|)$ below an absolute constant, then the survivor set has positive entropy.  For $\bigcup_{m\in S} H(m,w)$ this reads $|S| g^{-k} (k + \log_g m_{\max}) \lesssim c_0$, i.e. positive dimension whenever $|S| \lesssim c_0 g^k / (k + \log_g m_{\max})$.  Since $m_{\max} \ge |S|$, this would give $S(g,k) \ge c\, g^k / k$, the right exponential order but short of N5's $(g-1) g^{k-1}$ by a factor of order $k$.

### 6.5 What would have to be proved for N5, and where the obstruction is

N5 ($S(g,k) \ge (g-1) g^{k-1}$) is, by 6.2, the statement: for every $S$ with $|S| < (g-1)g^{k-1}$ there is a block $w$ with $h_{top}\big(\bigcap_{m\in S} M_m^{-1} X_w\big) > 0$, equivalently with exponentially many periodic $\alpha$ such that no $m\alpha$ contains $w$ in its period.  Two heuristics both land in the right ballpark and both identify the obstruction as **correlation between channels**:

- Independent-channel count.  There are $\sim g^n$ periodic points of period $n$; if the period-$n$ digit strings of $m\alpha$, $m \in S$, were independent and uniform, the expected number of survivors would be $g^n (1 - g^{-k})^{n|S|} \approx \exp\big(n(\log g - |S| g^{-k})\big)$, which stays exponential iff $|S| < g^k \log g$.  This predicts $S(g,k) \approx g^k \log g$; the known values are about $0.55$ to $0.75$ of that ($S(2,3) = 4$ vs $5.5$; $S(3,2) = 6$ vs $9.9$; $S(6,1) = 7$ vs $10.8$), so real channels are *more* efficient than independent ones.
- Dimension count.  $\dim X_w = \log \lambda_w / \log g$ with $\lambda_w \approx g - g^{-(k-1)}$ for a non-self-overlapping $w$, so the codimension of each pullback is $\approx g^{-k}/\log g$; if the $|S|$ pullbacks were in general position the intersection would have dimension $\approx 1 - |S| g^{-k}/\log g$, again positive iff $|S| < g^k \log g$.

Both are heuristics only.  The rigorous tools that make "general position" a theorem (Furstenberg's transversality of $\times p$- and $\times q$-invariant sets, proved by Shmerkin and by Wu in 2019) do not apply: all of our sets are invariant under the same map $T$, and $M_m^{-1}$ of a $T$-invariant set is $T$-invariant, so nothing forces transversality, and the identity $M_g^{-1} X_w \supseteq$ (a shift of) $X_w$ shows the intersection can be completely degenerate.  Any proof of N5 has to quantify how the digit strings of $m\alpha$ and $m'\alpha$ are correlated for $\alpha$ ranging over a positive-entropy set, which is an arithmetic (carry-propagation) statement and not a lexicographic one.  The sofic model of 6.2 is the natural framework for that: at base $2$ each channel is a carry automaton, and $J(S,w)$ is the survivor set of a product automaton.  The paper offers no tool for it.

A curiosity rather than evidence: N5's threshold total measure $S(g,k) g^{-k} \ge 1 - 1/g$ coincides with $\tau(g) = 1 - 1/g$, the critical length of a hole at $0$ for $x \mapsto gx$ in Allaart-Kong's Figure 1 ($\tau(2) = 1/2$, $\tau(3) = 2/3$, $\tau(4) = 3/4$).  I see no mechanism connecting the two.

### 6.6 Where balanced or Thue-Morse words might still show up (speculative, confidence 30%)

The last irrational survivors of a single hole, as it grows to critical size, are Sturmian.  One could ask whether the last survivors of $\bigcap_{m\in S} M_m^{-1} X_w$, as $S$ grows toward a hitting set, have a describable structure (low complexity, or fixed points of a substitution).  By 6.2 they cannot be Sturmian in the limit (zero entropy forces eventual periodicity), but for $|S| = S(g,k) - 1$ the positive-entropy survivor set might have a distinguished lowest-complexity element worth computing.  This is a question, not a result.

### 6.7 Bottom line

- Transfers: survivor set as a subshift; dimension = entropy/$\log g$; positive dimension via an embedded positive-entropy SFT (Lemma 1.1(ii), Proposition 2.2); and, for our rational holes specifically, the sofic dichotomy "positive dimension or all survivors eventually periodic", which makes "$S$ hits $w$" decidable and equivalent to a cofinite-bad-periods condition.
- Does not transfer: extremal pairs, the substitutions $\rho_r$ and balanced words, the plateau structure, the renormalization product, and the sharp constant $0.175092$; all require one hole straddling one discontinuity (or, per Allaart-Kong, $k-1$ aligned translates straddling all of them).
- Dead: any lower bound from component count and lengths alone (unavoidable sets).
- Open, and where the work is: an entropy lower bound for the intersection of $M_m$-pullbacks of $X_w$ that beats the LLL-type $c\, g^k/k$ and reaches $(g-1)g^{k-1}$; the obstruction is correlation between channels, which no transversality theorem covers because every set in play is $\times g$-invariant.

---

## 7. Related-papers check (abstracts opened this session)

IDs actually opened are listed; where a summary model was used, the verbatim abstract was then pulled with curl from the `/abs/` page.

- **arXiv:1412.6384**, Lyndsey Clark, *The $\beta$-transformation with a hole* (opened: abstract page).  Verbatim: "This paper extends those of Glendinning and Sidorov [3] and of Hare and Sidorov [6] from the case of the doubling map to the more general $\beta$-transformation.  Let $\beta \in (1,2)$ and consider the $\beta$-transformation $T_\beta(x) = \beta x \pmod 1$.  Let $\mathcal J_\beta(a,b) := \{x \in (0,1) : T_\beta^n(x) \notin (a,b) \text{ for all } n \ge 0\}$.  An integer $n$ is bad for $(a,b)$ if every $n$-cycle for $T_\beta$ intersects $(a,b)$.  Denote the set of all bad $n$ for $(a,b)$ by $B_\beta(a,b)$.  In this paper we completely describe the following sets: $D_0(\beta) = \{(a,b) \in [0,1)^2 : \mathcal J_\beta(a,b) \ne \emptyset\}$, $D_1(\beta) = \{(a,b) \in [0,1)^2 : \mathcal J_\beta(a,b) \text{ is uncountable}\}$, $D_2(\beta) = \{(a,b) \in [0,1)^2 : B_\beta(a,b) \text{ is finite}\}$."  **Single interval $(a,b)$ only; no unions.**  Its "bad $n$" set $B_\beta(a,b)$ is the periodic-orbit language that our criterion in 6.2 lands in ($S$ hits $w$ iff bad periods are cofinite), though Clark's $D_2$ asks for the opposite (finitely many bad periods).

- **arXiv:1803.07338**, Charlene Kalle, Derong Kong, Niels Langeveld, Wenxia Li, *The $\beta$-transformation with a hole at 0*, Ergodic Theory Dynam. Systems 40 (2020) (opened: abstract page; the ID 1904.05654 given in the brief is a queueing-theory paper by Guillemin and Quintuna Rodriguez, not this one).  Verbatim: "For $\beta \in (1,2]$ the $\beta$-transformation $T_\beta : [0,1) \to [0,1)$ is defined by $T_\beta(x) = \beta x \bmod 1$.  For $t \in [0,1)$ let $K_\beta(t)$ be the survivor set of $T_\beta$ with hole $(0,t)$ given by $K_\beta(t) := \{x \in [0,1) : T_\beta^n(x) \notin (0,t) \text{ for all } n \ge 0\}$.  In this paper we characterise the bifurcation set $E_\beta$ of all parameters $t \in [0,1)$ for which the set valued function $t \mapsto K_\beta(t)$ is not locally constant.  We show that $E_\beta$ is a Lebesgue null set of full Hausdorff dimension for all $\beta \in (1,2)$.  We prove that for Lebesgue almost every $\beta \in (1,2)$ the bifurcation set $E_\beta$ contains both infinitely many isolated and accumulation points arbitrarily close to zero.  On the other hand, we show that the set of $\beta \in (1,2)$ for which $E_\beta$ contains no isolated points has zero Hausdorff dimension.  These results contrast with the situation for $E_2$, the bifurcation set of the doubling map.  Finally, we give for each $\beta \in (1,2)$ a lower and upper bound for the value $\tau_\beta$, such that the Hausdorff dimension of $K_\beta(t)$ is positive if and only if $t < \tau_\beta$.  We show that $\tau_\beta \le 1 - 1/\beta$ for all $\beta \in (1,2)$."  Criterion: a single hole $(0,t)$; the survivor set is the lexicographic subshift $\{z : b(t,\beta) \preceq \sigma^n z \preceq \alpha(\beta)\}$ (greedy expansion of $t$ below, quasi-greedy expansion of $1$ above; this is (6.1) in Allaart-Kong), and $\dim_H K_\beta(t) = h_{top}/\log\beta$ (their Lemma 6.2, attributed to Raith).  No unions.

- **arXiv:2109.10012**, Pieter Allaart, Derong Kong, *Critical values for the $\beta$-transformation with a hole at 0*, Ergodic Theory Dynam. Systems (2023) (opened: abstract page).  Verbatim (abridged at "..."): "Given $\beta \in (1,2]$, let $T_\beta$ be the $\beta$-transformation on the unit circle $[0,1)$ such that $T_\beta(x) = \beta x \pmod 1$.  For each $t \in [0,1)$ let $K_\beta(t)$ be the survivor set consisting of all $x \in [0,1)$ whose orbit $\{T_\beta^n(x) : n \ge 0\}$ never hits the open interval $(0,t)$.  Kalle et al. proved ... that the Hausdorff dimension function $t \mapsto \dim_H K_\beta(t)$ is a non-increasing Devil's staircase.  So there exists a critical value $\tau(\beta)$ such that $\dim_H K_\beta(t) > 0$ if and only if $t < \tau(\beta)$.  In this paper we determine the critical value $\tau(\beta)$ for all $\beta \in (1,2]$ ... for the Komornik-Loreti constant $\beta \approx 1.78723$ we have $\tau(\beta) = (2-\beta)/(\beta-1)$.  Furthermore, we show that (i) the function $\tau$ is left continuous on $(1,2]$ with right-hand limits everywhere, but has countably infinitely many discontinuities; (ii) $\tau$ has no downward jumps, with $\tau(1+) = 0$ and $\tau(2) = 1/2$; and (iii) there exists an open set $O \subset (1,2]$, whose complement has zero Hausdorff dimension, such that $\tau$ is real-analytic, convex and strictly decreasing on each connected component of $O$.  Our strategy to find the critical value $\tau(\beta)$ depends on certain substitutions of Farey words and a renormalization scheme from dynamical systems."  Single hole at $0$; Farey-word substitutions play the role of $\rho_r$ here.

- **arXiv:2411.03516v3**, Allaart and Kong, *The $\beta$-transformation with a hole at 0: the general case* (opened: abstract page and the full HTML, Section 8 read in full).  Extends the above to all $\beta > 1$ (Theorem 1.1: $\tau$ left continuous, countably many discontinuities, no downward jumps, real-analytic, strictly convex and strictly decreasing on an open set whose complement has zero Hausdorff dimension).  **Section 8, "Connection with the 'times $k$' map with multiple holes", is the closest thing found to a union of intervals.**  Verbatim: "the survivor set $K_\beta(t)$ is closely related to the map $T_k : [0,1) \to [0,1)$ given by $T_k(x) := kx \pmod 1$, with $k-1$ holes that are translates of each other by multiples of $1/k$.  Precisely, let $0 < a < 1/k < b < a + 1/k$ and $H_1 := (a,b)$, $H_2 := (a + \tfrac1k, b + \tfrac1k)$, ..., $H_{k-1} = (a + \tfrac{k-2}{k}, b + \tfrac{k-2}{k})$.  Let $H := \bigcup_{i=1}^{k-1} H_i$, and consider the set $K(a,b;k-1) := \{x \in [0,1) : T_k^n(x) \notin H\ \forall n \ge 0\}$."  With $a = (0.a_1 a_2 \dots)_k$, $b = (0.b_1 b_2 \dots)_k$, $\mathbf a' = a_2 a_3 \dots$, $\mathbf b' = b_2 b_3 \dots$: "If $a_2 \le b_2$, then it is not too difficult to see that $\Omega_{a,b}$ is only countable", and otherwise $\Sigma_{\mathbf b', \mathbf a'} \subset \Omega_{\mathbf a, \mathbf b}$ with every element of $\Omega_{\mathbf a,\mathbf b}$ of the form $\mathbf w \mathbf z$, $\mathbf z \in \Sigma_{\mathbf b', \mathbf a'}$ and $\mathbf w$ one of $0^m$, $(k-1)^m$, $0^m j$, $(k-1)^m j$; conclusion "$\dim_H \widetilde{\mathcal K}_\beta(t) = \dim_H \Sigma_{\mathbf b', \mathbf a'} = \dim_H \Omega_{\mathbf a, \mathbf b} = \dim_H K(a,b;k-1)$" for a base $\beta \in (1,k)$ and $t$ determined by $\max$ and $\min$ of $\Sigma_{\mathbf b', \mathbf a'}$.  The holes are equal-length translates, one straddling each discontinuity $j/k$; the proof is "similar to that of Theorem 2.5 (vi) in [22]" and omitted.  Not our geometry (see 6.3), but it is the template for "when does a union of intervals reduce to one lexicographic interval".

- **arXiv:2604.23737**, Rui Kuang, Bing Li, Yuanfen Xiao, *The Hausdorff dimension of the survivor set* (submitted 26 Apr 2026; opened: abstract page).  Verbatim: "Let $1 < \beta < 2$, the sequence $\alpha(\beta) = \alpha(\beta)_1 \alpha(\beta)_2 \cdots$ be the quasi-greedy $\beta$-expansion of 1, and $t \in [0,1)$ be a bifurcation parameter.  The $\beta$-transformation is defined to be $T_\beta(x) = \beta x \pmod 1$ for $x \in [0,1)$.  The Hausdorff dimension of the survivor set $K(t) = \{x \in [0,1) : T_\beta^k(x) \notin (0,t), \forall k \ge 0\}$ is equal to $-\frac{\ln \lambda}{\ln \beta}$ under the condition that $\sum_{i=k}^\infty \frac{\alpha(\beta)_i}{\beta^i} \ge t$ for any $k \ge 1$, where $\lambda \in (0,1)$ is the smallest positive solution of the equation $\sum_{n=1}^\infty (\alpha(\beta)_n - t_n) x^n = 1$ with $(t_n)$ being the quasi-greedy $\beta$-expansion of $t$.  And the local Hölder exponent of the Hausdorff dimension function of $K(t)$ is larger than the value of the function itself."  Map: $\beta$-transformation, $1 < \beta < 2$; hole: the single interval $(0,t)$; gives an explicit dimension formula on the bifurcation set.  No unions.

- **arXiv:1204.1920**, Nikita Sidorov, *Supercritical holes for the doubling map* (reference [25] of the paper; opened: abstract page).  Verbatim: "For a map $S : X \to X$ and an open connected set ($=$ a hole) $H \subset X$ we define $\mathcal J_H(S)$ to be the set of points in $X$ whose $S$-orbit avoids $H$.  We say that a hole $H_0$ is supercritical if (i) for any hole $H$ such that $\overline{H_0} \subset H$ the set $\mathcal J_H(S)$ is either empty or contains only fixed points of $S$; (ii) for any hole $H$ such that $\overline{H} \subset H_0$ the Hausdorff dimension of $\mathcal J_H(S)$ is positive.  The purpose of this note to completely characterize all supercritical holes for the doubling map $Tx = 2x \bmod 1$."  Holes are open *connected* sets by definition; the $\mathcal S$-set and the "$\mathcal J(s^\infty,t^\infty)$ is the orbit of $s^\infty$" fact used in the paper come from here.

Closest to unions of intervals: **Allaart-Kong 2411.03516, Section 8** (aligned translates straddling every discontinuity of $x \mapsto kx$), and nothing else.  Not opened: Hare and Sidorov, *On cycles for the doubling map which are disjoint from an interval* (the source of "bad $n$"); Bundfuss-Krüger-Troubetzkoy [4]; Labarca-Moreira [18]; Mykkeltveit 1972; Rumyantsev-Ushakov 2006; Miller 2012.
