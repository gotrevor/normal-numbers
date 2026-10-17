# Joint Bailey–Crandall orbits: long-shot report (2026-10-16)

Research subagent report, persisted by the attended session (the subagent could not write files).
Probes: `probes/`; downloaded sources: `lit-dl/`.

## Verdict

The BBP long shot closes (sketch, ~85%): any nonzero integer combination of base-b BBP constants is
itself a base-b BBP constant, so the entropy seed (= `span_dimension_budget`) needs a normal BBP
constant, which is a Hypothesis A instance.  The live candidates sit in the ε > 0 (Stoneham) class.

## Literature (pages opened)

- **Bailey–Crandall, Exp. Math. 11 (2002)**: Thm 4.8 (single kick sequence r = 1/c^{n_i}, segments
  μ_k ≥ c^{γ n_k}, γ > 1/2 ⇒ normal); Lemma 4.2 (segment discrepancies add); p.532 ln 2 cascaded
  generator Σ (2^{d−m} mod m)/m, "difficulties may be insurmountable".
- **Bailey–Borwein, Ramanujan J. 29 (2012) §4**, verbatim: "it is not known at the present time
  whether the sum α_{b,c1} + α_{b,c2} is b-normal."  Thm 3 covers only the non-normal side.  Bailey
  talk slides: "Can we prove normality for sums of alphas, i.e. α2,3 + α2,5? … may be possible,
  although quite difficult."
- **Vandehey, arXiv:1606.07911 (J. Anal. Math. 2019) §7**, Thm 7.4: Σ 1/(c_k b^{m_k}) normal when
  c_k | c_{k+1}, c_k P-smooth, μ_k ≫ exp((1+ε) log c_k / log log c_k).  Proof uses orbit values
  a_k b^j / c_k with gcd 1, Erdős–Turán, Thm 1.4.  Does not mention the BB question.
- **CaptainSude xi-normality**, Thm "finite": Λ_P(b) normal for finite P via Vandehey; key move
  "the largest denominator power survives addition".  Full smooth support, not Stoneham sums.
- **Lagarias math/0101055 §6**: ln 2 BBP in bases 2 and 9; no HypA–Furstenberg link known.
- Freshness: two web searches + `papers followups` (0 citers for the BB DOI, thin) found no
  resolution.  Not a novelty certification.

## Candidates

### T-A. Pairwise-coprime Stoneham families are jointly normal
b ≥ 2; c_i pairwise coprime and coprime to b; m_i ≥ 1 ⇒ (α_{b^{m_i}, c_i})_i jointly b-normal
(equivalently every nonzero rational combination is b-normal).  Instance: α₂,₃ + α₂,₅ is 2-normal.
True ~85%, paper proof in 1–2 laps ~70%.  Answers the BB 2012 printed question; method is Vandehey's.
Sketch: merge kicks (kick (i,a) at position m_i c_i^a, value r_i/c_i^a); running-lcm denominators
D_n form a P-smooth divisibility chain; c_i-adic valuation of the orbit is exactly v(r_i) − a_max(i),
so the top term survives and D_n ≥ Π c_i^{a_max(i)}/const; gcd(A_n, D_n) = 1 up to a bounded factor;
only O(r log N) kicks ≤ N, so segments shorter than N^δ cover o(N) (no Baker needed); on long
segments Erdős–Turán with M = √D + Vandehey Thm 1.4; sum via BC Lemma 4.2.
Probes: `p2_joint_pairs.py` (N = 2²⁰, joint 6-block deficit 2.4e−4 vs 2.3e−4 pseudo-random);
`p2f_cross_prime.py` (coefficients ±u p^v q^w; no cross-prime constant run > 0.0034 N; same-prime
control collapses at 0.32 N; one 0.28 deficit was 98·α₈,₇ alone, a finite-N small-modulus artifact).
Open sub-case: c's sharing a prime but multiplicatively independent (b = 5, c = 2 and 6).

### T-B. Teichmüller dichotomy for same-prime pairs
p ∤ b, ω = ω_p(b) (b^{p^k} ≡ ω mod p^{k+1}).  For p ∤ m₁m₂, (α_{b^{m₁},p}, α_{b^{m₂},p}) jointly
b-normal ⟺ ω^{m₂−m₁} ≠ ±1 ⟺ ord_p(b) ∤ 2(m₂−m₁).  Failure gives an explicit combination with
constant digit windows of length ∝ position.  True ~80% (iff), ~92% (non-joint direction).
Flagship: α₂,₃ + α₄,₃ = Σ_k ((2^{3^k}+1)/3^k)·4^{−3^k}, a sum of integer blocks; digits exactly 0
on [2·3^k, 3^{k+1}) (exact for k ≤ 10, `p2b`); 1-density at 3¹⁰ is 0.2507.  Since ω = −1 for
(p, b) = (3, 2), no two distinct base-2 Stonehams over 3 are jointly normal.
Mechanism: orbit of Σ c_m α_{b^m,p} is bⁿ Σ_k S(n/p^k)/p^k with S(t) = Σ_{m p^{v(c_m)} ≤ t}
(c_m/p^{v(c_m)}) ω^{−m}; coefficients shift log-positions by p-adic valuation (Mahler equation
f(x^p) = p f(x) − x^p; e.g. 3α₂,₃ = α₈,₃ + 1/8 exactly).
Probes: `p2d` pre-registered p = 5 prediction (ω(2)² = −1 ⇒ α₂,₅ + α₈,₅ constant on [3·5^k, 5^{k+1}))
confirmed exactly k ≤ 7; controls runs ≤ 16.  `p2e`: rule v1 (m₂ < p m₁) FAILED at p = 3, (1, 4)
(3α₂,₃ + α₁₆,₃ collapses); rule v2 is post-hoc, then 12/12 including new p = 5, 7 cases.
Statistic: longest constant run (10-block deficit was fooled by p² coefficients).

### T-C. HypA ⇒ joint normality of ℚ-independent BBP families
E.g. (ln 2, ln 3) base 4 (ln 3 = 2 ln 2 − Σ 1/(n 4ⁿ); independence via Hermite).  Each combination
is a `bcOrbit`; irrationality excludes the finite-attractor branch; Weyl.  True ~92%, new: low.
One Lean lap for a `MasterConsequences` row.

### T-D. Vacuous disjunction (Maze row only)
∀ x, N: x and x − α₂,₃ disagree on ≥ (1/4 − o(1))N of the first N digits, so Dim_FS(x) +
dim_FS(x − α₂,₃) ≥ 1.  Borrow lemma; exact-checked `p1`.  True 97%, holds for every x.

## Closed routes (Maze rows)

- **R1** factor-map entropy seed for a BBP pair: restatement/wall 95% (BBP class closed under
  ℚ-span; needs a normal or positive-entropy BBP constant).  REOPEN IF one is proved.
- **R2** Stoneham sub-series pointing (ln 2 = α₂,₃ + R₃; ln 2 − ζ_Y): vacuous 97% (T-D, universal in x).
- **R3** Stoneham decomposition ln 2 = Σ_{3∤m} α_{2^m,3}/m with each term normal: falseAsStated +
  vacuous 95% (α₂,₃ + α₄,₃; remainder has a density-one driver).
- **R4** Diophantine input for a disjunctive channel: refuted 85% (pairs in C×C, C = {0,1}-digit
  Cantor set base 10: 10ⁿ(ax + cy) mod 1 ∈ aC + cC, dim ≤ 0.602, no channel disjunctive; a.e. pair
  has exponent 2 on every channel, via Bénard–He–Zhang).  `p3`: Cantor channels ≤ 5.1% of 4-words.
- **R5** "two normal constants are jointly normal" / "sums of normal Stonehams are normal":
  refuted 97%, witness α₂,₃ + α₄,₃.
- **R6** joint orbit containing ln 2: wall 95% (joint normality ⇒ each member normal; the family
  takes the worst ε).

Principle for H3: joint orbits take the minimum ε, not the average.  Joint normality is provable
exactly at ε > 0 (T-A), and even there arithmetic can obstruct it (T-B).

## Why no BBP-pair disjunction is within reach (~85%)
Available couplings: (1) ℤ-relations (universal entropy triangles); (2) a known-normal combination
(absent for BBP pairs R1, vacuous from a Stoneham partner R2); (3) Diophantine quality (R4).  A
fourth input would be Weyl-sum strength on an ε = 0 cascaded generator — the ln 2 wall.
Speculation (< 5%): "ln 2 is 2-normal or 3-normal" from its BBP formulas in two bases; needs
single-point ×2/×3 rigidity.

## Instrument incidents
1. Separately floored constants: sum 1 ulp low turned exact zero windows into all-ones runs; fixed
   (count constant runs of either digit; exact floor in `stoneham_int`).
2. p^v coefficients fool the 10-block deficit via short periods; switched to run statistics.

## Evidence tiers
Literature-confirmed: BB 2012 wording; Vandehey Thm 7.4 and BC Thm 4.8 statements/structure.
Probe-supported: T-B (1 pre-registered + 12/12 post-hoc); α₂,₃ + α₄,₃ identity (exact + elementary);
T-A (no collapse under stress); R4.  Sketch: T-A, T-B proofs, R1, R6.  Speculation: §4 two-base.
