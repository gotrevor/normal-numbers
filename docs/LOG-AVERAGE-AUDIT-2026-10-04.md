# Log-average rung audit (E2), 2026-10-04

**Verdict: the log rung does not reach `Σ ω(n)/bⁿ` or the #257 / Erdős–Borwein sums.  Best statement for the idea under audit: ≤ 5%.  Recorded as Maze rows on `audit/logavg`, not frozen as a lane.**

Lean record: `src/NormalNumbers/LogCastingOut.lean` (all proved except the cited `def … : Prop`s), `src/NormalNumbers/LogCastingOutStretch.lean` (two frozen `sorry` targets), Maze rows "log-averaged casting-out via the Elliott ledger" (wall, kernel) and "log-averaged word frequencies of an unconstructed constant as new" (prior art), both linked in `MazeAudit.lean`.

## 1. Negative inventory (what the repo already knew)

- **`SwingC1Log.lean` (2026-09-24) already ran this swing.**  `CastLawLog`, `ConjC1Log`, `castLawLog_one_iff` (the `L = 1` rung IS log-simple-normality of `G4_b` up to merging digits `0` and `b−1`), `castLawLog_of_castLaw` (natural ⇒ log), and the verdict docstring: the needed input is a growing-`K` log-correlation, because `carry_correction_unbounded` (`SwingC1LogCarry.lean`) rules out every fixed-depth truncation.  Open headlines `castLawLog_one`, `conjC1Log` are listed in `STATUS.md`.  **The verdict lived only in a docstring, with no Maze row**, which is why E2 re-proposed it ten days later.  The new Maze row fixes that.
- **`PairDecoupleProve.lean`**: the natural C1 route is `Delange + Kátai + TwoPointElliott + WeightDecouple`, and `WeightDecouple ⇐ … ⇔ multiElliott_all`, Elliott for `4K` forms with `K → ∞` (`shiftCorrSmall_iff_multiElliott` is an equivalence).  The factors come in conjugate pairs `ζ_k^{ω(pN+1+k)}·conj ζ_k^{ω(qN+1+k)}`, so the product is trivial.
- **`PairDecoupleTwoPoint.weightDecouple_of_twoPointWeighted`**: given `TwoPointElliott`, the decoupling is equivalent to the crux.  Its log twin is proved here.
- **`ElliottLedger.lean`**: `TwoPointElliottLog ⇐ ZetaLogDerivExponent θ`, `θ < 1`, axiom-clean (checked 2026-10-04: `#print axioms twoPointElliottLog_of_zetaExponent` and `nonasymptoticLogElliottMult` give only `propext, Classical.choice, Quot.sound`).  The chain passes through `UniformlyNonPretentious (zetaOmegaInt u)`, which is form-independent, so the ledger serves ANY pair of linear forms, not only `(pn+1, qn+1)`.
- **`EDensityAudit.lean` / EDENSITY audit**: the #257 sum `E = Σ 1/(2ⁿ−1) = Σ τ(m)/2ᵐ` has tail mass `≍ log N · 2^{-k}`, worse than `G4`'s `log log N · b^{-k}`.  Not re-proposed; the log weighting does not touch it.
- `ElliottArchBands` negatives concern the zeta input, not the consumer; nothing there bears on E2.

## 2. Is "logarithmically normal" a known notion, and is it strictly weaker?

- **Known.**  Chowla's conjecture is the statement that `λ` is a normal `±1` sequence (generic for the Bernoulli measure; Sarnak's framing, Frantzikinakis "Ergodicity of the Liouville system implies the Chowla conjecture", arXiv:1611.09338).  The logarithmic Chowla conjecture is the same with weights `1/n`, i.e. logarithmic normality of `λ`.  The phrases "logarithmically normal" / "logarithmic normality" for real numbers returned nothing in a web search (query recorded in §6); the concept is standard under the name "logarithmically generic".
- **Strictly weaker, proved here.**  `tendsto_logFreq_dyadicBit` + `not_tendsto_natFreq_dyadicBit`: the sequence `1[⌊log₂(n+1)⌋ even]` has log digit frequency `1/2` and no natural frequency (proof: the signed harmonic sum over alternating dyadic blocks stays in `[0,1]` because block masses decrease, `blockMass_succ_le`).  Natural ⇒ log is `CastingOut.tendsto_logAvg_of_tendsto_avg`.
- **Prior art for E2's novelty claim.**  Tao–Teräväinen 2019 (Duke 168, arXiv:1708.02610) prove the conjectured log density `1/8` of every Liouville sign pattern of length 3 (and Möbius patterns of length 4).  So the carry-free constant `Σ [λ(n)=1] 2^{-n}`, defined without a construction, already has log 3-word frequencies.  Recorded as `TaoTeravainen2019LiouvilleThree` (cited Prop).  E2's "first positive-frequency statement about a constant defined without a construction" is therefore prior art unless the constant has carries.  Also seen: Carella, arXiv:2211.09736 ("Equidistributions of sign patterns of the Liouville function and normal numbers"), not refereed here and not relied on.

## 3. Difficulty check

**Proved implications.**  Log weighting survives every *averaging* step: partial summation (`tendsto_logAvg_of_tendsto_avg`), the two-point split and its converse (`twoPointWeightedLog_of_split`, `weightDecoupleLog_of_twoPointWeightedLog`), and Kátai's criterion should transfer, since its Turán–Kubilius proof is linear in the averaging weights (not checked in the literature this session; it is not needed for the verdict).  The wiring E2 asked for is proved: `twoPointWeightedLog_iff_weightDecoupleLog_of_zetaExponent`.

**Unproved premise.**  It is an *equivalence*.  Under the ledger's input, the log pair leaf `TwoPointWeightedLog` ⇔ `WeightDecoupleLog`.  Consuming `TwoPointElliottLog` removes nothing; the crux is the log twin of `multiElliott_all`, which has trivial product (conjugate pairs), so it is Chowla-strength already at fixed `K = 2` (like even-order log Chowla), and needs `K → ∞` besides.

**Where the carries use depth, not averaging.**  The digit is `ω(n+1) + c_{n+1} − b·c_n` with `c_N = ⌊Σ_{k≥1} ω(N+k) b^{-k}⌋`.  The tail beyond depth `K` has mass `≍ b^{-K} log log n` (`≍ b^{-K} log n` for the divisor-weighted #257 sums), so any truncation needs `b^K ≫ log log X`.  This is a pointwise statement about the size of `ω`; changing the weights on positions `n` does not change it.  `carry_correction_unbounded` is the Lean form.

**Mechanism tested on the direct digit route.**  `e(h·bⁿ·G4_b) = ∏_{k≥0} ζ_k^{ω(n+1+k)}`, `ζ_k = e(h/b^{k+1})`.  At fixed depth `K` the product of the `ζ_k` is `e(h(b^K−1)/((b−1)b^K))`, a root of unity `≠ 1` when `b ∤ h` (because `(b^K−1)/(b−1) ≡ 1 mod b`), so Tao–Teräväinen's vanishing theorem applies for every fixed `K` (`TaoTeravainen2019FixedDepth`, cited).  This corrects the second reason in the `SwingC1Log` verdict ("parity: even `k ≥ 4` open"): parity blocks the *pair* route, not the direct digit route.  The exact remaining gap on the digit route is **uniformity in `K`**, stated as `GrowingDepthLogElliott` (reopen condition), with `simplyNormalLog_of_growingDepth` (frozen, 70%) certifying that it is the right condition.  No log-correlation theorem uniform in the number of shifts turned up (abstracts checked this session: Tao–Teräväinen arXiv:1708.02610, Klurman–Mangerel–Teräväinen arXiv:2304.05344, both fixed `k`; the forward-citation lists of Tao 2016 and TT 2019 in the appendix show no such title).  That is a search result, not an exhaustion: a growing-`k` result in a paper whose title does not say so would be missed.

**Known-false siblings, in Lean.**
- `dyadicBit`: right log statistics, no natural statistics (the rung is distinct).
- The carry-free sibling `Σ (ω(m) mod b) b^{-m}` (digits `ω(n+1) mod b`): log 2-word normal under the ledger's input (`omegaModDigit_logTwoWord_of_zetaExponent`, frozen, 80%).  Every mechanism step that works for it fails for `G4_b` at exactly one place, the carry.  That isolates the obstruction: the mechanism does not separate "carry-free" from "carries of unbounded depth", and only the second is the target.

**Success estimates.**
- Log-averaged 1- or 2-word frequencies of `G4_b` (or of the #257 / Erdős–Borwein sums): **≤ 5%** for this lane (needs growing-depth log Elliott; #257 sums need more).
- The wiring of E2's first deliverable: done, and it is an equivalence, so it is a wall row rather than a deliverable.
- Carry-free consumer `omegaModDigit_logTwoWord_of_zetaExponent`: 80% Lean-provable from repo pieces; low novelty (direct corollary of Tao 2016 + Delange).  It is the one place the ledger has a digit-side consumer.
- `simplyNormalLog_of_growingDepth`: 70%.

## 4. Decision

Best statement for the idea under audit is below 40%, so the conclusion is recorded as Lean on `audit/logavg` (Maze rows citing declarations, `#maze_audit` linked) rather than frozen as a lane.  The two frozen `sorry`s are optional follow-ups, not a lane.

## 5. Referee asks (cited Props)

- `TaoTeravainen2019FixedDepth`: passage from TT's generalised limits on windows `[x/ω(x), x]` to the full window `2 ≤ n ≤ X`; the weak-pretentiousness check for `ζ^ω`, `ζ` a nontrivial root of unity.
- `TaoTeravainen2019LiouvilleThree`: the `1/(n+1)` versus `1/n` weight and the shift base `n+1, n+2, n+3`.

## 6. Searches run by hand (the `prior-art` battery log is the appendix)

- Web: `"logarithmically normal" OR "logarithmic normality" digits sequence normal numbers logarithmic density` → nothing on the digit notion (log-normal distributions only).
- Web: `Tao Teräväinen structure of logarithmically averaged correlations … weakly pretend Dirichlet character` → arXiv:1708.02610; abstract confirms the vanishing case and the length-3 Liouville / length-4 Möbius log densities.
- Web: `Liouville function binary expansion normal number logarithmic Chowla … generic Bernoulli … Frantzikinakis Host` → Chowla ⇔ `λ` normal / generic for Bernoulli; Frantzikinakis arXiv:1611.09338; Frantzikinakis–Host log Sarnak.
- arXiv:2304.05344 (Klurman–Mangerel–Teräväinen) abstract: fixed `k` only (odd `k`, real `f`); no uniformity in `k`.
- `prior-art` battery (appendix): arXiv:1708.02610, "logarithmically averaged Chowla", arXiv:1509.05422, "Lambert series" + "normality"/"digits"; `papers followups` on 1509.05422 and 1708.02610.  arXiv API calls returned HTTP 429/503 (recorded as instrument errors, not zeros); Semantic Scholar and OpenAlex answered.  No hit addresses digit statistics of Lambert-type constants or growing-`k` correlations.


## Appendix: prior-art search log (instrument output, unedited)


## Prior-art log: arXiv:1708.02610 (2026-10-04 00:19 EDT)

### arXiv record: 1708.02610 - arXiv API
- query: `id_list=1708.02610`
- ERROR (not a zero - the instrument did not answer): InstrumentError: HTTP 429 from https://export.arxiv.org/api/query?id_list=1708.02610

### Forward citations of arXiv:1708.02610 - Semantic Scholar
- query: `papers followups 1708.02610`
- result: 75 hits (newest first)
- note: via `papers followups`
  1. 2026-09-29 - Truncated pretentious distances of multiplicative arithmetic functions - Thomas Renard - https://arxiv.org/abs/2609.37332
  2. 2026 - The Critical Line from First Principles: A Complete Unconditional Liouville-Collar Closure of the Riemann Hypothesis - Deep Bhattacharjee - https://doi.org/10.37648/ijrst.v16i02.002
  3. 2025-12-02 - The distribution of prime values of random polynomials - Noah Kravitz, K. Woo, Max Wenqiang Xu - https://arxiv.org/abs/2512.03292
  4. 2025-11-06 - Almost Countable Spectrum and Logarithmic Sarnak Conjecture - Wen Huang, M. Tan, Leiye Xu - https://arxiv.org/abs/2511.04419
  5. 2025-07-12 - On the correlations between character sums of division polynomials under shifts - Subham Bhakta, Igor E. Shparlinski - https://arxiv.org/abs/2507.09271
  6. 2025-06-22 - Liouville function, von Mangoldt function, and norm forms at random binary forms - Yi-Jie Diao - https://arxiv.org/abs/2506.18065
  7. 2025-02-24 - Global well-posedness of the cubic nonlinear Schrödinger equation on T2\documentclass[12pt]{minimal} \usepackage{amsmath} \usepackage{wasysym} \usepackage{amsfonts} \usepackage{amssymb} \usepackage{amsbsy} \usepackage{mathrsfs} \usepackage{upgreek} \setlength{\oddsidemargin}{-69pt} \begin{document}$ - Sebastian Herr, Beomjong Kwak - https://arxiv.org/abs/2502.17073
  8. 2025-01-19 - On variants of Chowla’s conjecture - Krishnarjun Krishnamoorthy - https://arxiv.org/abs/2501.10962
  9. 2024-11-26 - Partition regularity of homogeneous quadratics: Current trends and challenges - N. Frantzikinakis - https://arxiv.org/abs/2411.17523
  10. 2024-09-26 - Averages of arithmetic functions over polynomials in many variables - Kevin Destagnol, E. Sofos - https://arxiv.org/abs/2409.18116
  11. 2024-09-16 - The Chowla conjecture and Landau–Siegel zeroes - Mikko Jaskari, Stelios Sachpazis - https://arxiv.org/abs/2409.10663
  12. 2024-09-09 - Random Chowla's Conjecture for Rademacher Multiplicative Functions - Jake Chinis, B. Shala - https://arxiv.org/abs/2409.05952
  13. 2024-09-03 - Correlations of the Möbius and Liouville functions with their partial sums - Gordon Chavez - https://arxiv.org/abs/2409.02106
  14. 2024-08-16 - Higher Moments for Polynomial Chowla - Cameron Wilson - https://arxiv.org/abs/2408.08726
  15. 2023-10-26 - Correlation of multiplicative functions over Fq[x]$\mathbb {F}_q[x]$ : A pretentious approach - P. Darbar, Anirban Mukhopadhyay - https://doi.org/10.1112/mtk.12227
  16. 2023-10-11 - Stability under scaling in the local phases of multiplicative functions - M. N. Walsh - https://arxiv.org/abs/2310.07873
  17. 2023-05-19 - Pseudorandom Binary Sequences: Quality Measures and Number-Theoretic Constructions - Arne Winterhof - https://arxiv.org/abs/2305.11486
  18. 2023-04-11 - On Elliott's conjecture and applications - O. Klurman, Alexander P. Mangerel, Joni Teravainen - https://arxiv.org/abs/2304.05344
  19. 2023-04-06 - Furstenberg systems of pretentious and MRT multiplicative functions - N. Frantzikinakis, M. Lema'nczyk, T. de la Rue - https://arxiv.org/abs/2304.03121
  20. 2023-03-27 - Measure growth in compact semisimple Lie groups and the Kemperman Inverse Problem - Yi-Fan Jing, Chieu-Minh Tran - https://arxiv.org/abs/2303.15628
  21. 2023 - Sequence complexity, rigidity and logarithmic Sarnak conjecture - Rui Qiu, R. Wei, Leiye Xu - https://doi.org/10.3934/dcds.2022187
  22. 2022-12-20 - Bateman–Horn, polynomial Chowla and the Hasse principle with probability 1 - T. Browning, E. Sofos, Joni Teräväinen - https://arxiv.org/abs/2212.10373
  23. 2022-11-01 - Chowla and Sarnak conjectures for Kloosterman sums - Houcein El Abdalaoui, I. Shparlinski, Raphael S. Steiner - https://arxiv.org/abs/2211.00379
  24. 2022 - ON THE COVARIANCE - Gordon V. Chavez - -
  25. 2021-09-13 - The Hardy–Littlewood–Chowla conjecture in the presence of a Siegel zero - T. Tao, Joni Teräväinen - https://arxiv.org/abs/2109.06291
  26. 2021-08-25 - Divisor-bounded multiplicative functions in short intervals - Alexander P. Mangerel - https://arxiv.org/abs/2108.11401
  27. 2021-06-22 - A dynamical proof of the van der Corput inequality - N. Edeko, H. Kreidler, R. Nagel - https://arxiv.org/abs/2106.11835
  28. 2021-06-02 - Decomposition of multicorrelation sequences and joint ergodicity - S. Donoso, Andreu Ferré Moragues, Andreas Koutsogiannis, Wenbo Sun - https://arxiv.org/abs/2106.01058
  29. 2021-05-31 - Siegel zeros and Sarnak's conjecture - Jake Chinis - https://arxiv.org/abs/2105.14653
  30. 2021-03-25 - Sublacunary sets and interpolation sets for nilsequences - Anh N. Le - https://arxiv.org/abs/2103.13551
  31. 2020-10-15 - On the Liouville function at polynomial arguments - Joni Teräväinen - https://arxiv.org/abs/2010.07924
  32. 2020-09-28 - Correlations of multiplicative functions in function fields - O. Klurman, Alexander P. Mangerel, Joni Teräväinen - https://arxiv.org/abs/2009.13497
  33. 2020-09-10 - Sarnak’s Conjecture from the Ergodic Theory Point of View - J. Kułaga-Przymus, M. Lemańczyk - https://arxiv.org/abs/2009.04757
  34. 2020-09-07 - Monotone chains of Fourier coefficients of Hecke cusp forms - O. Klurman, Alexander P. Mangerel - https://arxiv.org/abs/2009.03225
  35. 2020-09-07 - Monotone chains of Fourier coefficients of Hecke cusp forms - O. Klurman, Alexander P. Mangerel - -
  36. 2020-09-04 - Polynomial mean complexity and logarithmic Sarnak conjecture - Wen Huang, Leiye Xu, Xiang-Dong Ye - https://arxiv.org/abs/2009.02090
  37. 2020-07-14 - Good weights for the Erdős discrepancy problem - N. Frantzikinakis - https://doi.org/10.19086/DA.13688
  38. 2020-06-17 - On Furstenberg systems of aperiodic multiplicative functions of Matomäki, Radziwiłł, and Tao - A. Gomilko, M. Lemánczyk, T. de la Rue - https://arxiv.org/abs/2006.09958
  39. 2020-04-24 - Structure of multicorrelation sequences with integer part polynomial iterates along primes - Andreas Koutsogiannis, Anh N. Le, Joel Moreira, F. Richter - https://arxiv.org/abs/2004.11835
  40. 2020-01-30 - A decomposition of multicorrelation sequences for commuting transformations along primes - Anh N. Le, Joel Moreira, F. Richter - https://arxiv.org/abs/2001.11523
  41. 2019-09-26 - Fourier uniformity of bounded multiplicative functions in short intervals on average - Kaisa Matomäki, Maksym Radziwiłł, T. Tao - https://arxiv.org/abs/2007.15644
  42. 2019-08-07 - Correlations of multiplicative functions along deterministic and independent sequences - N. Frantzikinakis - https://arxiv.org/abs/1908.02732
  43. 2019-06-07 - A tale of two omegas - Michael J. Mossinghoff, T. Trudgian - https://arxiv.org/abs/1906.02847
  44. 2019-05-22 - Correlation of multiplicative functions over function fields - P. Darbar, A. Mukhopadhyay - https://arxiv.org/abs/1905.09303
  45. 2019-05-01 - Interpolation sets and nilsequences - Anh N. Le - https://arxiv.org/abs/1905.00527
  46. 2019-05-01 - MULTIPLICATIVE FUNCTIONS IN SHORT INTERVALS, AND CORRELATIONS OF MULTIPLICATIVE FUNCTIONS - Kaisa Matomäki, Maksym Radziwiłł - https://doi.org/10.1142/9789813272880_0056
  47. 2019-04-10 - VALUE PATTERNS OF MULTIPLICATIVE FUNCTIONS AND RELATED SEQUENCES - T. Tao, Joni Teräväinen - https://arxiv.org/abs/1904.05096
  48. 2019-03-05 - Good weights for the Erd\"os discrepancy problem - N. Frantzikinakis - https://arxiv.org/abs/1903.01881
  49. 2019-02-26 - Sarnak's Conjecture for nilsequences on arbitrary number fields and applications - Wen-Bo Sun - https://arxiv.org/abs/1902.09712
  50. 2019-02-07 - Disjointness of the Möbius Transformation and Möbius Function - E. H. el Abdalaoui, I. Shparlinski - https://doi.org/10.1007/s40687-019-0180-6
  51. 2019-01-19 - Sarnak’s conjecture for sequences of almost quadratic word growth - Redmond McNamara - https://arxiv.org/abs/1901.06460
  52. 2018-12-18 - Mini-Workshop: Interplay between Number Theory and Analysis for Dirichlet Series - Fr'ed'eric Bayart, Kaisa Matomäki, Eero Saksmann, Kristian Seip - https://doi.org/10.4171/OWR/2017/51
  53. 2018-12-04 - Fourier uniformity of bounded multiplicative functions in short intervals on average - Kaisa Matomäki, Maksym Radziwiłł, T. Tao - https://arxiv.org/abs/1812.01224
  54. 2018-11-01 - An Inverse Theorem for an Inequality of Kneser - T. Tao - https://doi.org/10.1134/S0081543818080163
  55. 2018-10-21 - On the orbits of multiplicative pairs - O. Klurman, Alexander P. Mangerel - https://arxiv.org/abs/1810.08967
  56. 2018-09-10 - Dynamical models for Liouville and obstructions to further progress on sign patterns - W. Sawin - https://arxiv.org/abs/1809.03280
  57. 2018-09-07 - The structure of correlations of multiplicative functions at almost all scales, with applications to the Chowla and Elliott conjectures - T. Tao, Joni Teräväinen - https://arxiv.org/abs/1809.02518
  58. 2018-07-25 - Combinatorial identities and Titchmarsh’s divisor problem for multiplicative functions - S. Drappeau, Berke Topacogullari - https://arxiv.org/abs/1807.09569
  59. 2018-04-23 - Furstenberg Systems of Bounded Multiplicative Functions and Applications - N. Frantzikinakis, B. Host - https://arxiv.org/abs/1804.08556
  60. 2018-03-16 - Möbius disjointness conjecture for local dendrite maps - E. H. el Abdalaoui, Ghassen Askri, H. Marzougui - https://arxiv.org/abs/1803.06201
  61. 2018 - Joni Teräväinen: TOPICS IN MULTIPLICATIVE NUMBER THEORY - Univrsitatis Turuensis, Joni Teräväinen - -
  62. 2017-12-01 - Disjointness of the Möbius Transformation and Möbius Function - E. H. el Abdalaoui, I. Shparlinski - https://doi.org/10.1007/S40687-019-0180-6
  63. 2017-11-29 - Disjointness of the M\"obius Transformation and M\"obius Function - E. H. el Abdalaoui, I. Shparlinski - https://arxiv.org/abs/1711.11062
  64. 2017-11-12 - An Inverse Theorem for an Inequality of Kneser - T. Tao - https://arxiv.org/abs/1711.04337
  65. 2017-10-11 - Sarnak’s Conjecture: What’s New - S. Ferenczi, Joanna Kułaga-Przymus, M. Lema'nczyk - https://arxiv.org/abs/1710.04039
  66. 2017-10-05 - Odd order cases of the logarithmically averaged Chowla conjecture - T. Tao, Joni Teräväinen - https://arxiv.org/abs/1710.02112
  67. 2017-10-03 - ON BINARY CORRELATIONS OF MULTIPLICATIVE FUNCTIONS - Joni Teräväinen - https://arxiv.org/abs/1710.01195
  68. 2017-09-11 - Tao’s resolution of the Erdős discrepancy problem - K. Soundararajan - https://doi.org/10.1090/BULL/1598
  69. 2017-08-10 - Effective Asymptotic Formulae for Multilinear Averages of Multiplicative Functions - O. Klurman, Alexander P. Mangerel - https://arxiv.org/abs/1708.03176
  70. 2017-08-04 - Nilsequences and multiple correlations along subsequences - Anh N. Le - https://arxiv.org/abs/1708.01361
  71. 2017-08-02 - The logarithmic Sarnak conjecture for ergodic weights - N. Frantzikinakis, B. Host - https://arxiv.org/abs/1708.00677
  72. 2017-07-25 - Rigidity theorems for multiplicative functions - O. Klurman, Alexander P. Mangerel - https://arxiv.org/abs/1707.07817
  73. 2017-03-02 - Gowers norms control diophantine inequalities - A. Walker - https://arxiv.org/abs/1703.00885
  74. 2017-02-05 - On consecutive values of random completely multiplicative functions - J. Najnudel - https://arxiv.org/abs/1702.01470
  75. ???? - (2020). On consecutive values of random completely multiplicative functions. Electronic Journal of Probability, 25, [59] - J. Najnudel - -

### Forward citations of arXiv:1708.02610 - OpenAlex
- query: `works?filter=cites:<OpenAlex id of doi:10.48550/arXiv.1708.02610>`
- ERROR (not a zero - the instrument did not answer): InstrumentError: HTTP 404 from https://api.openalex.org/works/doi:10.48550/arXiv.1708.02610

### Exact phrase "logarithmically averaged" - arXiv API
- query: `search_query=(abs:"logarithmically averaged" OR ti:"logarithmically averaged") sortBy=submittedDate desc`
- ERROR (not a zero - the instrument did not answer): TimeoutError: The read operation timed out

### Exact phrase "logarithmically averaged" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"logarithmically averaged",to_publication_date:2026-10-04`
- result: 79 hits (showing 8, newest first)
  1. 2026-09-24 - The Pearl and the Toll: a Witnessed-Scale Chowla Regime and the Width Law of the Entropy Decrement - Jason Hickey - https://doi.org/10.5281/zenodo.22942697
  2. 2026-09-24 - The Pearl and the Toll: a Witnessed-Scale Chowla Regime and the Width Law of the Entropy Decrement - Jason Hickey - https://doi.org/10.5281/zenodo.22942698
  3. 2026-09-22 - Effective logarithmic two-point Chowla bounds in every window - Hughes, Scott D. - https://doi.org/10.48550/arxiv.2609.28526
  4. 2026-05-27 - On a conjecture of Goldmakher - Alexander P. Mangerel - https://doi.org/10.48550/arxiv.2605.29111
  5. 2026-04-19 - Besov regularity of boundary traces of conditionally convergent Dirichlet series - Theodore Deligiannis - https://doi.org/10.5281/zenodo.19655579
  6. 2026-04-19 - Besov regularity of boundary traces of conditionally convergent Dirichlet series - Theodore Deligiannis - https://doi.org/10.5281/zenodo.19655580
  7. 2026-04-13 - A smoothed Perron bound for two-point Liouville correlations under a variance hypothesis at σ = 1 - Theodore Deligiannis - https://doi.org/10.5281/zenodo.19546425
  8. 2026-04-13 - A smoothed Perron bound for two-point Liouville correlations via Sobolev regularity at σ = 1 - Theodore Deligiannis - https://doi.org/10.5281/zenodo.19655422

### formal-conjectures PRs "logarithmically averaged" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"logarithmically averaged"' --state all --json number,title,author,createdAt,url,state --limit 8`
- result: 0 hits, instrument: gh pr list (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### formal-conjectures issues "logarithmically averaged" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"logarithmically averaged"' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 8`
- result: 0 hits, instrument: gh search issues (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### Exact phrase "logarithmic density" - arXiv API
- query: `search_query=(abs:"logarithmic density" OR ti:"logarithmic density") sortBy=submittedDate desc`
- ERROR (not a zero - the instrument did not answer): TimeoutError: The read operation timed out

### Exact phrase "logarithmic density" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"logarithmic density",to_publication_date:2026-10-04`
- result: 475 hits (showing 8, newest first)
  1. 2026-10-01 - The Collatz Conjecture: Unresolved, with Reverse-Rule Modular Hints — E8 Intelligence Research - Andrew Stewart Caldin - https://doi.org/10.5281/zenodo.23075376
  2. 2026-10-01 - The Collatz Conjecture: Unresolved, with Reverse-Rule Modular Hints — E8 Intelligence Research - Andrew Stewart Caldin - https://doi.org/10.5281/zenodo.23075377
  3. 2026-09-30 - Polylogarithmic Descent for Almost All Collatz Orbits in Natural Density - Idris Ali Shaik - https://doi.org/10.5281/zenodo.23061210
  4. 2026-09-30 - A Fixed-Offset Transition for Random Stackability on Paths - John Fairfax-Ball - https://doi.org/10.48550/arxiv.2609.39633
  5. 2026-09-27 - A power saving in natural density for generalized Collatz maps - Hiroyuki Nashida - https://doi.org/10.5281/zenodo.22986677
  6. 2026-09-27 - A power saving in natural density for generalized Collatz maps - Hiroyuki Nashida - https://doi.org/10.5281/zenodo.22986678
  7. 2026-09-26 - Almost-Boundedness of Collatz-Type Maps on Number Rings via Archimedean Methods - Maxwell Siegel, Rory O’Dwyer - https://doi.org/10.48550/arxiv.2609.33018
  8. 2026-09-24 - New Theorems on Accelerated Collatz Map Parity Vectors and Paradoxical Sequences — E8 Intelligence Research - Andrew Stewart Caldin - https://doi.org/10.5281/zenodo.22930831

### formal-conjectures PRs "logarithmic density" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"logarithmic density"' --state all --json number,title,author,createdAt,url,state --limit 8`
- result: 8 hits (newest first)
- note: gh returns no total; 8 = the --limit, so more may exist
  1. 2026-09-12 - #5927 feat(ErdosProblems): formalise Erdős Problem 1123 - stantheman0128 - https://github.com/google-deepmind/formal-conjectures/pull/5927 [closed]
  2. 2026-09-11 - #5788 fix(ErdosProblems/486): only forbid residues modulo n for 0 < n < m - smmercuri - https://github.com/google-deepmind/formal-conjectures/pull/5788 [merged]
  3. 2026-07-23 - #4587 ErdosProblems 486, 788: ShouqiaoW formal_proof links (486 statement correction) - williamjblair - https://github.com/google-deepmind/formal-conjectures/pull/4587 [closed]
  4. 2026-03-17 - #3586 feat(ErdosProblems): formalize 423, 839 - ryantuck - https://github.com/google-deepmind/formal-conjectures/pull/3586 [merged]
  5. 2026-01-13 - #1640 chore(ErdosProblems): clean up docstrings - mo271 - https://github.com/google-deepmind/formal-conjectures/pull/1640 [merged]
  6. 2025-12-28 - #1424 feat(ErdosProblems/486): logarithmic density for sets avoiding modular subsets - ruskaruma - https://github.com/google-deepmind/formal-conjectures/pull/1424 [merged]
  7. 2025-12-24 - #1411 feat(ErdosProblems/25): logarithmic density of size-dependent congruences - ruskaruma - https://github.com/google-deepmind/formal-conjectures/pull/1411 [merged]
  8. 2025-10-19 - #1131 Add Erdős Problem 371 - edwag - https://github.com/google-deepmind/formal-conjectures/pull/1131 [merged]

### formal-conjectures issues "logarithmic density" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"logarithmic density"' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 8`
- result: 8 hits (newest first)
- note: gh returns no total; 8 = the --limit, so more may exist
  1. 2026-09-30 - #6717 ErdosProblems/143: `erdos_143.parts.i` is true - mo271 - https://github.com/google-deepmind/formal-conjectures/issues/6717 [open]
  2. 2026-09-25 - #6591 Open statements with known solutions 3 - KitaKen1 - https://github.com/google-deepmind/formal-conjectures/issues/6591 [open]
  3. 2026-09-18 - #6073 Erdős 486: the answer is no (Wang 2026, formal proof in plby/lean-proofs) - Konamiu - https://github.com/google-deepmind/formal-conjectures/issues/6073 [closed]
  4. 2026-09-11 - #5654 ErdosProblems/486: `erdos_486` tests every modulus `n`, including `0` and `n ≥ m`, instead of `0 < n < m` - tadamcz - https://github.com/google-deepmind/formal-conjectures/issues/5654 [closed]
  5. 2026-08-02 - #4689 ErdosProblems/486: erdos_486 is degenerate — missing activation threshold, and n = 0 admitted - ibrahimmian36 - https://github.com/google-deepmind/formal-conjectures/issues/4689 [open]
  6. 2025-10-06 - #753 Erdős Problem 486 - mo271 - https://github.com/google-deepmind/formal-conjectures/issues/753 [closed]
  7. 2025-06-10 - #200 Erdős Problem 25: logarithmic density for a sequence avoiding size-dependent congruences - mo271 - https://github.com/google-deepmind/formal-conjectures/issues/200 [closed]
  8. 2025-06-10 - #201 Erdős problem 486: logarithmic density for a sequence avoiding size-dependent congruences - mo271 - https://github.com/google-deepmind/formal-conjectures/issues/201 [closed]

### Exact phrase "normal number" - arXiv API
- query: `search_query=(abs:"normal number" OR ti:"normal number") sortBy=submittedDate desc`
- ERROR (not a zero - the instrument did not answer): InstrumentError: HTTP 429 from https://export.arxiv.org/api/query?search_query=%28abs%3A%22normal+number%22+OR+ti%3A%22normal+number%22%29&start=0&max_results=8&sortBy=submittedDate&sortOrder=descending

### Exact phrase "normal number" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"normal number",to_publication_date:2026-10-04`
- result: 2296 hits (showing 8, newest first)
  1. 2026-09-20 - What Numbers Can Say About "Does 777 Occur in π" Is That the Waiting Time Is Set by the Word's Self-Overlap ── in the decimals of π, 777 first occurs at digit 1589, its expected waiting time is 1110, and that of 123 is 1000; the mean first occurrence of the 1000 three-digit words is 991.994000 against an expected mean of 1002, indistinguishable from random digits ── the separator is whether the word overlaps itself or not ── [Paper 1032] - Yuuki Yamagishi - https://doi.org/10.5281/zenodo.22860519
  2. 2026-09-20 - What Numbers Can Say About "Does 777 Occur in π" Is That the Waiting Time Is Set by the Word's Self-Overlap ── in the decimals of π, 777 first occurs at digit 1589, its expected waiting time is 1110, and that of 123 is 1000; the mean first occurrence of the 1000 three-digit words is 991.994000 against an expected mean of 1002, indistinguishable from random digits ── the separator is whether the word overlaps itself or not ── [Paper 1032] - Yuuki Yamagishi - https://doi.org/10.5281/zenodo.22860520
  3. 2026-09-15 - Exhaustive Verification of the Normal Number Conjecture: 7 Billion Phone Numbers in the First Trillion Digits of π and e - Ming Jie Zhang - https://doi.org/10.5281/zenodo.22774606
  4. 2026-09-15 - Exhaustive Verification of the Normal Number Conjecture: 7 Billion Phone Numbers in the First Trillion Digits of π and e - Ming Jie Zhang - https://doi.org/10.5281/zenodo.22774607
  5. 2026-09-11 - The Uncomputable Coin Flip: Chaitin's Omega as Algorithmic Randomness — E8 Intelligence Research - Andrew Stewart Caldin - https://doi.org/10.5281/zenodo.22701702
  6. 2026-09-11 - The Uncomputable Coin Flip: Chaitin's Omega as Algorithmic Randomness — E8 Intelligence Research - Andrew Stewart Caldin - https://doi.org/10.5281/zenodo.22701703
  7. 2026-09-04 - An Exact Closed-Form Measure for k-Digit Prefix Coincidence in Fractional Scaling Maps - Keith Ramon Vasquez (Independent Researcher) - https://doi.org/10.5281/zenodo.22299517
  8. 2026-09-04 - An Exact Closed-Form Measure for k-Digit Prefix Coincidence in Fractional Scaling Maps - Keith Ramon Vasquez (Independent Researcher) - https://doi.org/10.5281/zenodo.22299518

### formal-conjectures PRs "normal number" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"normal number"' --state all --json number,title,author,createdAt,url,state --limit 8`
- result: 0 hits, instrument: gh pr list (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### formal-conjectures issues "normal number" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"normal number"' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 8`
- result: 2 hits (newest first)
- note: gh returns no total; count is rows returned
  1. 2026-02-10 - #2256 Normality of Irrational Algebraic Numbers - franzhusch - https://github.com/google-deepmind/formal-conjectures/issues/2256 [closed]
  2. 2026-02-10 - #2255 Normality of π - franzhusch - https://github.com/google-deepmind/formal-conjectures/issues/2255 [closed]

## Prior-art log: logarithmically averaged Chowla (2026-10-04 00:27 EDT)

### Exact phrase "logarithmically averaged Chowla" - arXiv API
- query: `search_query=(abs:"logarithmically averaged Chowla" OR ti:"logarithmically averaged Chowla") sortBy=submittedDate desc`
- ERROR (not a zero - the instrument did not answer): InstrumentError: HTTP 429 from https://export.arxiv.org/api/query?search_query=%28abs%3A%22logarithmically+averaged+Chowla%22+OR+ti%3A%22logarithmically+averaged+Chowla%22%29&start=0&max_results=8&sortBy=submittedDate&sortOrder=descending

### Exact phrase "logarithmically averaged Chowla" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"logarithmically averaged Chowla",to_publication_date:2026-10-04`
- result: 7 hits (newest first)
  1. 2019-07-23 - The structure of logarithmically averaged correlations of multiplicative functions, with applications to the Chowla and Elliott conjectures - Terence Tao, Joni Teräväinen - https://doi.org/10.1215/00127094-2019-0002
  2. 2019-03-28 - Odd order cases of the logarithmically averaged Chowla conjecture - Terence Tao, Joni Teräväinen - https://doi.org/10.5802/jtnb.1062
  3. 2018-01-01 - Ergodicity of the Liouville system implies the Chowla conjecture - Nikos Frantzikinakis - https://doi.org/10.19086/da.2733
  4. 2017-01-01 - Equivalence of the Logarithmically Averaged Chowla and Sarnak Conjectures - Terence Tao - https://doi.org/10.1007/978-3-319-55357-3_21
  5. 2016-05-16 - Equivalence of the logarithmically averaged Chowla and Sarnak conjectures - Terence Tao - https://doi.org/10.48550/arxiv.1605.04628
  6. 2016-01-01 - THE LOGARITHMICALLY AVERAGED CHOWLA AND ELLIOTT CONJECTURES FOR TWO-POINT CORRELATIONS - Terence Tao - https://doi.org/10.1017/fmp.2016.6
  7. 2015-09-17 - The logarithmically averaged Chowla and Elliott conjectures for two-point correlations - Terence Tao - https://doi.org/10.48550/arxiv.1509.05422

### formal-conjectures PRs "logarithmically averaged Chowla" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"logarithmically averaged Chowla"' --state all --json number,title,author,createdAt,url,state --limit 8`
- result: 0 hits, instrument: gh pr list (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### formal-conjectures issues "logarithmically averaged Chowla" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"logarithmically averaged Chowla"' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 8`
- result: 0 hits, instrument: gh search issues (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### Exact phrase "logarithmically generic" - arXiv API
- query: `search_query=(abs:"logarithmically generic" OR ti:"logarithmically generic") sortBy=submittedDate desc`
- ERROR (not a zero - the instrument did not answer): InstrumentError: arXiv not retried: HTTP 429 after retries earlier this run

### Exact phrase "logarithmically generic" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"logarithmically generic",to_publication_date:2026-10-04`
- result: 0 hits, instrument: OpenAlex

### formal-conjectures PRs "logarithmically generic" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"logarithmically generic"' --state all --json number,title,author,createdAt,url,state --limit 8`
- result: 0 hits, instrument: gh pr list (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### formal-conjectures issues "logarithmically generic" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"logarithmically generic"' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 8`
- result: 0 hits, instrument: gh search issues (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### Exact phrase "logarithmic averages" - arXiv API
- query: `search_query=(abs:"logarithmic averages" OR ti:"logarithmic averages") sortBy=submittedDate desc`
- ERROR (not a zero - the instrument did not answer): InstrumentError: arXiv not retried: HTTP 429 after retries earlier this run

### Exact phrase "logarithmic averages" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"logarithmic averages",to_publication_date:2026-10-04`
- result: 61 hits (showing 8, newest first)
  1. 2026-09-25 - Prime perturbations of polynomial observations: instability and incidence criteria - Brice Pouly - https://doi.org/10.5281/zenodo.22960070
  2. 2026-09-24 - Global Collision Conditions for the de Bruijn–Newman Flow:Zero localization, counting inequalities, and Weil positivity - K. Fathi - https://doi.org/10.5281/zenodo.22949572
  3. 2026-09-22 - Effective logarithmic two-point Chowla bounds in every window - Hughes, Scott D. - https://doi.org/10.48550/arxiv.2609.28526
  4. 2026-09-14 - Weighted ergodic averages along subpolynomials in Hardy fields and applications - Vitaly Bergelson, Sovanlal Mondal, Younghwan Son - https://doi.org/10.48550/arxiv.2609.14939
  5. 2025-09-14 - A Universal Space of Arithmetic Functions:The Banach--Hilbert Hybrid Space U - Es-said En-naoui - https://doi.org/10.48550/arxiv.2510.00008
  6. 2025-07-29 - On the Divergence of General Local and Fractal Dimensions of Typical Measures - Zhiming Li, Bilel Selmi - https://doi.org/10.14321/realanalexch.1745378977
  7. 2025-06-19 - Exploring Higher Order Local Entropy Functions via Baire Category Theory - Tingting Wang, Bilel Selmi, Zhiming Li - https://doi.org/10.1007/s12346-025-01321-y
  8. 2025-06-01 - Second-order logarithmic methods for the summability of Fourier series - Xhevat Zahir Krasniqi, Péter Kórus - https://doi.org/10.1515/gmj-2025-2082

### formal-conjectures PRs "logarithmic averages" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"logarithmic averages"' --state all --json number,title,author,createdAt,url,state --limit 8`
- result: 0 hits, instrument: gh pr list (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### formal-conjectures issues "logarithmic averages" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"logarithmic averages"' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 8`
- result: 0 hits, instrument: gh search issues (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

## Prior-art log: arXiv:1509.05422 (2026-10-04 00:30 EDT)

### arXiv record: 1509.05422 - arXiv API
- query: `id_list=1509.05422`
- ERROR (not a zero - the instrument did not answer): InstrumentError: HTTP 429 from https://export.arxiv.org/api/query?id_list=1509.05422

### Forward citations of arXiv:1509.05422 - Semantic Scholar
- query: `papers followups 1509.05422`
- result: 135 hits (newest first)
- note: via `papers followups`
  1. 2026-09-29 - Truncated pretentious distances of multiplicative arithmetic functions - Thomas Renard - https://arxiv.org/abs/2609.37332
  2. 2026-09-22 - Effective logarithmic two-point Chowla bounds in every window - S. D. Hughes - https://arxiv.org/abs/2609.28526
  3. 2026-08-27 - Two-point correlations of multiplicative functions with dense orbits - N. Tardy - https://arxiv.org/abs/2608.26814
  4. 2026-08-27 - Value distribution of multiplicative functions along linear fractional sequences - Sun-Kai Leung - https://arxiv.org/abs/2608.27418
  5. 2026-08-17 - Two averaged dynamical generalizations of Chowla's conjecture - Biao Wang - https://arxiv.org/abs/2608.16108
  6. 2026-07-17 - Improved bounds for multiplicative functions in almost all short intervals - Siddarth Menon - https://arxiv.org/abs/2607.15574
  7. 2026-05-13 - Helmholzian Spectra of Graphs: Novel Properties - Lu Lu, Yongtang Shi, Zoran Stanić, Jianfeng Wang, Yi Wang - https://arxiv.org/abs/2605.13733
  8. 2026-04-28 - The Subtractive Divisor Orbit: Unconditional Bounds, Parity Constraints, and a Conditional Framework - Marco Mantovanelli - https://arxiv.org/abs/2604.25446
  9. 2026-03-01 - Arithmetic progressions at the Journal of the LMS - Ben Green - https://doi.org/10.1112/jlms.70483
  10. 2026 - The Critical Line from First Principles: A Complete Unconditional Liouville-Collar Closure of the Riemann Hypothesis - Deep Bhattacharjee - https://doi.org/10.37648/ijrst.v16i02.002
  11. 2026 - Об исключительном множестве длин интервалов суммирования в бинарной задаче Чоулы - T. Preobrazhenskaya, S. Preobrazhenskii - https://doi.org/10.4213/dm1921
  12. 2025-12-02 - The distribution of prime values of random polynomials - Noah Kravitz, K. Woo, Max Wenqiang Xu - https://arxiv.org/abs/2512.03292
  13. 2025-11-06 - Almost Countable Spectrum and Logarithmic Sarnak Conjecture - Wen Huang, M. Tan, Leiye Xu - https://arxiv.org/abs/2511.04419
  14. 2025-07-01 - Sums and products in sets of positive density - F. Richter - https://arxiv.org/abs/2507.00515
  15. 2025-06-22 - Liouville function, von Mangoldt function, and norm forms at random binary forms - Yi-Jie Diao - https://arxiv.org/abs/2506.18065
  16. 2025-06-15 - Bounded exponential sums with multiplicative coefficients - Péa Bazin, Ihor Pylaiev, F. Tyrrell - https://arxiv.org/abs/2506.12845
  17. 2025-01-19 - On variants of Chowla’s conjecture - Krishnarjun Krishnamoorthy - https://arxiv.org/abs/2501.10962
  18. 2024-12-23 - On Shusterman's Goldbach-type problem for sign patterns of the Liouville function - Alexander P. Mangerel - https://arxiv.org/abs/2412.17199
  19. 2024-12-04 - On multiplicative recurrence along linear patterns - Dimitrios Charamaras, Andreas Mountakis, Konstantinos Tsinas - https://arxiv.org/abs/2412.03504
  20. 2024-11-26 - Partition regularity of homogeneous quadratics: Current trends and challenges - N. Frantzikinakis - https://arxiv.org/abs/2411.17523
  21. 2024-09-16 - The Chowla conjecture and Landau–Siegel zeroes - Mikko Jaskari, Stelios Sachpazis - https://arxiv.org/abs/2409.10663
  22. 2024-09-09 - Random Chowla's Conjecture for Rademacher Multiplicative Functions - Jake Chinis, B. Shala - https://arxiv.org/abs/2409.05952
  23. 2024-09-03 - Correlations of the Möbius and Liouville functions with their partial sums - Gordon Chavez - https://arxiv.org/abs/2409.02106
  24. 2024-08-16 - Higher Moments for Polynomial Chowla - Cameron Wilson - https://arxiv.org/abs/2408.08726
  25. 2023-11-20 - Gap problems for integer-valued multiplicative functions - Alexander P. Mangerel - https://arxiv.org/abs/2311.11636
  26. 2023-10-26 - Correlation of multiplicative functions over Fq[x]$\mathbb {F}_q[x]$ : A pretentious approach - P. Darbar, Anirban Mukhopadhyay - https://doi.org/10.1112/mtk.12227
  27. 2023-10-11 - Stability under scaling in the local phases of multiplicative functions - M. N. Walsh - https://arxiv.org/abs/2310.07873
  28. 2023-10-09 - On the Local Fourier Uniformity Problem for Small Sets - Adam Kanigowski, M. Lema'nczyk, F. Richter, Joni Teräväinen - https://arxiv.org/abs/2310.05528
  29. 2023-09-19 - Partition regularity of Pythagorean pairs - N. Frantzikinakis, O. Klurman, Joel Moreira - https://arxiv.org/abs/2309.10636
  30. 2023-06-16 - On Equal Consecutive Values of Multiplicative Functions - Alexander P. Mangerel - https://arxiv.org/abs/2306.09929
  31. 2023-05-17 - On asymptotically automatic sequences - Jakub Konieczny - https://arxiv.org/abs/2305.09885
  32. 2023-04-11 - On Elliott's conjecture and applications - O. Klurman, Alexander P. Mangerel, Joni Teravainen - https://arxiv.org/abs/2304.05344
  33. 2023-04-06 - Furstenberg systems of pretentious and MRT multiplicative functions - N. Frantzikinakis, M. Lema'nczyk, T. de la Rue - https://arxiv.org/abs/2304.03121
  34. 2023-03-22 - On a Bohr set analogue of Chowla’s conjecture - Joni Teräväinen, A. Walker - https://arxiv.org/abs/2303.12574
  35. 2023 - Sequence complexity, rigidity and logarithmic Sarnak conjecture - Rui Qiu, R. Wei, Leiye Xu - https://doi.org/10.3934/dcds.2022187
  36. 2022-12-20 - Bateman–Horn, polynomial Chowla and the Hasse principle with probability 1 - T. Browning, E. Sofos, Joni Teräväinen - https://arxiv.org/abs/2212.10373
  37. 2022-11-28 - On the multiplicative independence between $n$ and $\lfloor \alpha n\rfloor $ - David Crnvcev'ic, Felipe Hern'andez, Kevin Rizk, Khunpob Sereesuchart, Ran Tao - https://arxiv.org/abs/2211.15830
  38. 2022-11-05 - Equidistributions of Sign Patterns of the Liouville Function and Normal Numbers - N. Carella - https://arxiv.org/abs/2211.09736
  39. 2022-11-01 - Chowla and Sarnak conjectures for Kloosterman sums - Houcein El Abdalaoui, I. Shparlinski, Raphael S. Steiner - https://arxiv.org/abs/2211.00379
  40. 2022-08-18 - Note on the Chowla Conjecture and the Discrete Fourier Transform - N. Carella - https://arxiv.org/abs/2208.12219
  41. 2022-06-26 - Result on the Mobius Function over Shifted Primes - N. Carella - https://arxiv.org/abs/2206.12956
  42. 2022-04-14 - On the Collatz Conjecture - J. Czelakowski - https://doi.org/10.4204/eptcs.358.0.02
  43. 2022-02-21 - Beyond the Erdős discrepancy problem in function fields - O. Klurman, Alexander P. Mangerel, Joni Teräväinen - https://arxiv.org/abs/2202.10370
  44. 2022-02-17 - On the random Chowla conjecture - O. Klurman, I. Shkredov, M. Xu - https://arxiv.org/abs/2202.08767
  45. 2022-01-31 - Autocorrelation of the Mobius Function - N. Carella - https://arxiv.org/abs/2202.01071
  46. 2022-01-03 - Expansion, divisibility and parity: an explanation - H. Helfgott - https://arxiv.org/abs/2201.00799
  47. 2022 - ON THE COVARIANCE - Gordon V. Chavez - -
  48. 2022 - Results for the Mobius Function and Liouville Function over the Shifted Primes - N. Carella - -
  49. 2022 - Counting primes - J. Maynard - -
  50. 2021-10-07 - Complex Valued Multiplicative Functions with Bounded Partial Sums - Marco Aymone - https://arxiv.org/abs/2110.03401
  51. 2021-09-13 - The Hardy–Littlewood–Chowla conjecture in the presence of a Siegel zero - T. Tao, Joni Teräväinen - https://arxiv.org/abs/2109.06291
  52. 2021-08-27 - Additive functions in short intervals, gaps and a conjecture of Erdős - Alexander P. Mangerel - https://arxiv.org/abs/2108.12351
  53. 2021-08-25 - Divisor-bounded multiplicative functions in short intervals - Alexander P. Mangerel - https://arxiv.org/abs/2108.11401
  54. 2021-05-31 - Siegel zeros and Sarnak's conjecture - Jake Chinis - https://arxiv.org/abs/2105.14653
  55. 2021-05-31 - The upper logarithmic density of monochromatic subset sums - David Conlon, Jacob Fox, H. Pham - https://arxiv.org/abs/2105.15195
  56. 2021-02-11 - Exact formulas for partial sums of the M\"obius function expressed by partial sums weighted by the Liouville lambda function - M. Schmidt - https://arxiv.org/abs/2102.05842
  57. 2021-01-25 - Möbius Disjointness for product flows of rigid dynamical systems and affine linear flows - Fei Wei - https://arxiv.org/abs/2101.10134
  58. 2021 - ON THE CORRELATION BETWEEN MÖBIUS AND POLYNOMIAL PHASES IN SHORT ARITHMETIC PROGRESSIONS - Fei Wei - -
  59. 2020-10-15 - On the Liouville function at polynomial arguments - Joni Teräväinen - https://arxiv.org/abs/2010.07924
  60. 2020-09-30 - (Logarithmic) densities for automatic sequences along primes and squares - B. Adamczewski, M. Drmota, Clemens Müllner - https://arxiv.org/abs/2009.14773
  61. 2020-09-28 - Correlations of multiplicative functions in function fields - O. Klurman, Alexander P. Mangerel, Joni Teräväinen - https://arxiv.org/abs/2009.13497
  62. 2020-09-10 - Sarnak’s Conjecture from the Ergodic Theory Point of View - J. Kułaga-Przymus, M. Lemańczyk - https://arxiv.org/abs/2009.04757
  63. 2020-09-07 - Monotone chains of Fourier coefficients of Hecke cusp forms - O. Klurman, Alexander P. Mangerel - https://arxiv.org/abs/2009.03225
  64. 2020-09-07 - Monotone chains of Fourier coefficients of Hecke cusp forms - O. Klurman, Alexander P. Mangerel - -
  65. 2020-09-04 - Polynomial mean complexity and logarithmic Sarnak conjecture - Wen Huang, Leiye Xu, Xiang-Dong Ye - https://arxiv.org/abs/2009.02090
  66. 2020-09-01 - On Chowla's Conjecture - T. Agama - -
  67. 2020-07-14 - Good weights for the Erdős discrepancy problem - N. Frantzikinakis - https://doi.org/10.19086/DA.13688
  68. 2020-06-17 - On Furstenberg systems of aperiodic multiplicative functions of Matomäki, Radziwiłł, and Tao - A. Gomilko, M. Lemánczyk, T. de la Rue - https://arxiv.org/abs/2006.09958
  69. 2020-04-02 - Prime number theorem for analytic skew products - Adam Kanigowski, M. Lemańczyk, Maksym Radziwiłł - https://arxiv.org/abs/2004.01125
  70. 2020-02-10 - Dynamical generalizations of the prime number theorem and disjointness of additive and multiplicative semigroup actions - V. Bergelson, F. Richter - https://arxiv.org/abs/2002.03498
  71. 2020-02-10 - A Dynamical Proof of the Prime Number Theorem - Redmond McNamara - https://arxiv.org/abs/2002.04007
  72. 2020-01-01 - Chang's lemma via Pinsker's inequality - Lianna Hambardzumyan, Yaqiao Li - https://arxiv.org/abs/2005.10830
  73. 2020 - Arithmetic Functions - O. Bordellès - https://doi.org/10.1007/978-1-4471-4096-2_4
  74. 2019-11-14 - Multiplicative functions that are close to their mean - O. Klurman, Alexander P. Mangerel, C. Pohoata, Joni Teräväinen - https://arxiv.org/abs/1911.06265
  75. 2019-10-29 - On the Twin Prime Conjecture - J. Maynard - https://arxiv.org/abs/1910.14674
  76. 2019-09-26 - Fourier uniformity of bounded multiplicative functions in short intervals on average - Kaisa Matomäki, Maksym Radziwiłł, T. Tao - https://arxiv.org/abs/2007.15644
  77. 2019-09-08 - Almost all orbits of the Collatz map attain almost bounded values - T. Tao - https://arxiv.org/abs/1909.03562
  78. 2019-08-14 - On the bivariate Erdős–Kac theorem and correlations of the Möbius function - Alexander P. Mangerel - https://doi.org/10.1017/S0305004119000288
  79. 2019-08-07 - Correlations of multiplicative functions along deterministic and independent sequences - N. Frantzikinakis - https://arxiv.org/abs/1908.02732
  80. 2019-06-21 - The twin prime conjecture - James Maynard - https://doi.org/10.1007/s11537-019-1837-z
  81. 2019-06-07 - A tale of two omegas - Michael J. Mossinghoff, T. Trudgian - https://arxiv.org/abs/1906.02847
  82. 2019-05-22 - Correlation of multiplicative functions over function fields - P. Darbar, A. Mukhopadhyay - https://arxiv.org/abs/1905.09303
  83. 2019-05-16 - M{\"o}bius orthogonality in density for zero entropy dynamical systems. - A. Gomilko, M. Lemańczyk, T. de la Rue - https://arxiv.org/abs/1905.06563
  84. 2019-05-08 - Möbius disjointness for nilsequences along short intervals - Xiaoguang He, Zhiren Wang - https://arxiv.org/abs/1905.02864
  85. 2019-05-01 - MULTIPLICATIVE FUNCTIONS IN SHORT INTERVALS, AND CORRELATIONS OF MULTIPLICATIVE FUNCTIONS - Kaisa Matomäki, Maksym Radziwiłł - https://doi.org/10.1142/9789813272880_0056
  86. 2019-04-18 - Ergodic Theorems - S. Lalley - https://doi.org/10.1090/mmono/078/01
  87. 2019-04-10 - VALUE PATTERNS OF MULTIPLICATIVE FUNCTIONS AND RELATED SEQUENCES - T. Tao, Joni Teräväinen - https://arxiv.org/abs/1904.05096
  88. 2019-03-15 - Möbius disjointness for topological models of ergodic measure-preserving systems with quasi-discrete spectrum - Leiye Xu - https://doi.org/10.1016/J.JDE.2018.09.022
  89. 2019-03-05 - Good weights for the Erd\"os discrepancy problem - N. Frantzikinakis - https://arxiv.org/abs/1903.01881
  90. 2019-02-26 - Sarnak's Conjecture for nilsequences on arbitrary number fields and applications - Wen-Bo Sun - https://arxiv.org/abs/1902.09712
  91. 2019-01-19 - Sarnak’s conjecture for sequences of almost quadratic word growth - Redmond McNamara - https://arxiv.org/abs/1901.06460
  92. 2018-12-18 - Mini-Workshop: Interplay between Number Theory and Analysis for Dirichlet Series - Fr'ed'eric Bayart, Kaisa Matomäki, Eero Saksmann, Kristian Seip - https://doi.org/10.4171/OWR/2017/51
  93. 2018-12-04 - Fourier uniformity of bounded multiplicative functions in short intervals on average - Kaisa Matomäki, Maksym Radziwiłł, T. Tao - https://arxiv.org/abs/1812.01224
  94. 2018-11-16 - Variants of equidistribution in arithmetic progression and the twin prime conjecture - A. Vatwani - https://doi.org/10.1007/S00209-018-2177-Z
  95. 2018-11-16 - Variants of equidistribution in arithmetic progression and the twin prime conjecture - A. Vatwani - https://doi.org/10.1007/s00209-018-2177-z
  96. 2018-10-21 - On the orbits of multiplicative pairs - O. Klurman, Alexander P. Mangerel - https://arxiv.org/abs/1810.08967
  97. 2018-09-10 - Dynamical models for Liouville and obstructions to further progress on sign patterns - W. Sawin - https://arxiv.org/abs/1809.03280
  98. 2018-09-07 - The structure of correlations of multiplicative functions at almost all scales, with applications to the Chowla and Elliott conjectures - T. Tao, Joni Teräväinen - https://arxiv.org/abs/1809.02518
  99. 2018-07-25 - Combinatorial identities and Titchmarsh’s divisor problem for multiplicative functions - S. Drappeau, Berke Topacogullari - https://arxiv.org/abs/1807.09569
  100. 2018-04-23 - Furstenberg Systems of Bounded Multiplicative Functions and Applications - N. Frantzikinakis, B. Host - https://arxiv.org/abs/1804.08556
  101. 2018 - Joni Teräväinen: TOPICS IN MULTIPLICATIVE NUMBER THEORY - Univrsitatis Turuensis, Joni Teräväinen - -
  102. 2018 - A remark on a conjecture of Chowla - M. Murty, A. Vatwani - -
  103. 2018 - Chowla’s Conjecture: From the Liouville Function to the Moebius Function - O. Ramaré - https://doi.org/10.1007/978-3-319-74908-2_16
  104. 2017-11-01 - Twin primes and the parity problem - M. Murty, A. Vatwani - https://doi.org/10.1016/J.JNT.2017.05.011
  105. 2017-10-19 - Sarnak’s Conjecture Implies the Chowla Conjecture Along a Subsequence - A. Gomilko, Dominik Kwietniak, M. Lemańczyk - https://arxiv.org/abs/1710.07049
  106. 2017-10-11 - Sarnak’s Conjecture: What’s New - S. Ferenczi, Joanna Kułaga-Przymus, M. Lema'nczyk - https://arxiv.org/abs/1710.04039
  107. 2017-10-05 - Odd order cases of the logarithmically averaged Chowla conjecture - T. Tao, Joni Teräväinen - https://arxiv.org/abs/1710.02112
  108. 2017-10-03 - ON BINARY CORRELATIONS OF MULTIPLICATIVE FUNCTIONS - Joni Teräväinen - https://arxiv.org/abs/1710.01195
  109. 2017-09-11 - Tao’s resolution of the Erdős discrepancy problem - K. Soundararajan - https://doi.org/10.1090/BULL/1598
  110. 2017-08-10 - Effective Asymptotic Formulae for Multilinear Averages of Multiplicative Functions - O. Klurman, Alexander P. Mangerel - https://arxiv.org/abs/1708.03176
  111. 2017-08-08 - The structure of logarithmically averaged correlations of multiplicative functions, with applications to the Chowla and Elliott conjectures - T. Tao, Joni Teräväinen - https://arxiv.org/abs/1708.02610
  112. 2017-08-02 - The logarithmic Sarnak conjecture for ergodic weights - N. Frantzikinakis, B. Host - https://arxiv.org/abs/1708.00677
  113. 2017-07-25 - Rigidity theorems for multiplicative functions - O. Klurman, Alexander P. Mangerel - https://arxiv.org/abs/1707.07817
  114. 2017-02-13 - Some applications of relative entropy in additive combinatorics - J. Wolf - https://doi.org/10.1017/9781108332699.010
  115. 2017 - HARMONIC ANALYSIS ON THE POSITIVE RATIONALS. DETERMINATION OF THE GROUP GENERATED BY THE RATIOS $(an+b)/(An+B)$ - P. D. T. A. Elliott, Jonathan Kish - https://doi.org/10.1112/S0025579317000304
  116. 2017 - Normal numbers in generalized number systems in Euclidean spaces - J. de Koninck, I. Kátai - https://doi.org/10.71352/ac.46.015
  117. 2016-12-30 - On the Bivariate Erd\H{o}s-Kac Theorem and Correlations of the M\"obius Function - Alexander P. Mangerel - https://arxiv.org/abs/1612.09544
  118. 2016-11-28 - Ergodicity of the Liouville system implies the Chowla conjecture - N. Frantzikinakis - https://arxiv.org/abs/1611.09338
  119. 2016-06-27 - An averaged Chowla and Elliott conjecture along independent polynomials - N. Frantzikinakis - https://arxiv.org/abs/1606.08420
  120. 2016-06-26 - The Liouville function in short intervals [after Matomaki and Radziwill] - K. Soundararajan - https://arxiv.org/abs/1606.08021
  121. 2016-05-16 - Equivalence of the Logarithmically Averaged Chowla and Sarnak Conjectures - T. Tao - https://arxiv.org/abs/1605.04628
  122. 2016-04-25 - Higher rank sieves and applications - A. Vatwani - -
  123. 2016-03-28 - Correlations of multiplicative functions and applications - O. Klurman - https://arxiv.org/abs/1603.08453
  124. 2016-03-18 - Note on the Theory of Correlation Functions - N. Carella - https://arxiv.org/abs/1603.06758
  125. 2016-03-17 - From Ramanujan to Groups of Rationals: A Personal History of Abstract Multiplicative Functions - P. D. T. A. Elliott - https://doi.org/10.1007/978-3-319-68376-8_16
  126. 2016-02-10 - Harmonic Analysis on the Positive Rationals. Determination of the Group Generated by the Ratios $(an+b)/(An+B)$ - P. D. T. A. Elliott, Jonathan Kish - https://arxiv.org/abs/1602.03263
  127. 2016-01-06 - About Erdös discrepancy conjecture - R. Carbó-Dorca - https://doi.org/10.1007/s10910-015-0585-4
  128. 2016 - THE LIOUVILLE FUNCTION IN SHORT INTERVALS [after Matomäki and Radziwiłł] by Kannan SOUNDARARAJAN - ? - -
  129. 2016 - Black hole formation and stability : a mathematical investigation - Imperial Ballroom, M. Marquis - -
  130. 2015-11-06 - On correlations of certain multiplicative functions - R. Balasubramanian, S. Giri, Priyamvad Srivastav - https://arxiv.org/abs/1511.02221
  131. 2015-09-17 - The Erdos discrepancy problem - T. Tao - https://arxiv.org/abs/1509.05363
  132. 2015-09-04 - SIGN PATTERNS OF THE LIOUVILLE AND MÖBIUS FUNCTIONS - Kaisa Matomäki, Maksym Radziwiłł, T. Tao - https://arxiv.org/abs/1509.01545
  133. 2014-05-04 - Correlations of the Moebius and Liouville functions and the twin prime conjecture - S. Preobrazhenskii, T. Preobrazhenskaya - -
  134. 2014-05-04 - A note on correlations of arithmetic functions - S. Preobrazhenskii, T. Preobrazhenskaya - https://arxiv.org/abs/1405.0682
  135. ???? - New EMS Press book - C. Ritzenthaler - -

### Forward citations of arXiv:1509.05422 - OpenAlex
- query: `works?filter=cites:<OpenAlex id of doi:10.48550/arXiv.1509.05422>`
- result: 13 hits (showing 8, newest first)
- note: OpenAlex work W2219884900
  1. 2025-03-26 - Random Chowla’s conjecture for Rademacher multiplicative functions - Jake Chinis, Besfort Shala - https://doi.org/10.1090/tran/9457
  2. 2023-05-12 - On the multiplicative group generated by \Big\{{[\sqrt {2}n]\over n}~\mid~n\in\mathbb{N} \Big\}. V - Imre Kátai, Bui Minh Phong - https://doi.org/10.7546/nntdm.2023.29.2.348-353
  3. 2022-12-10 - Correlations of multiplicative functions in function fields - Oleksiy Klurman, Alexander P. Mangerel, Joni Teräväinen - https://doi.org/10.1112/mtk.12181
  4. 2020-04-22 - Möbius disjointness for nilsequences along short intervals - Xiaoguang He, Zhiren Wang - https://doi.org/10.1090/tran/8176
  5. 2020-03-04 - Correlations of multiplicative functions along deterministic and independent sequences - Nikos Frantzikinakis - https://doi.org/10.1090/tran/8142
  6. 2019-03-28 - Odd order cases of the logarithmically averaged Chowla conjecture - Terence Tao, Joni Teräväinen - https://doi.org/10.5802/jtnb.1062
  7. 2017-08-10 - Effective Asymptotic Formulae for Multilinear Averages of Multiplicative Functions - Oleksiy Klurman, Alexander P. Mangerel - https://doi.org/10.48550/arxiv.1708.03176
  8. 2017-01-05 - An Averaged Chowla and Elliott Conjecture Along Independent Polynomials - Nikos Frantzikinakis - https://doi.org/10.1093/imrn/rnx002

### Keyword battery - not run
- query: `-`
- SKIPPED: no phrase or --keyword given; exact-phrase arXiv, OpenAlex and formal-conjectures searches not run

## Prior-art log: Lambert series (2026-10-04 00:32 EDT)

### Exact phrase "Lambert series" - arXiv API
- query: `search_query=(abs:"Lambert series" OR ti:"Lambert series") AND submittedDate:[201501010000 TO 299912312359] sortBy=submittedDate desc`
- ERROR (not a zero - the instrument did not answer): InstrumentError: HTTP 503 from https://export.arxiv.org/api/query?search_query=%28abs%3A%22Lambert+series%22+OR+ti%3A%22Lambert+series%22%29+AND+submittedDate%3A%5B201501010000+TO+299912312359%5D&start=0&max_results=8&sortBy=submittedDate&sortOrder=descending

### Exact phrase "Lambert series" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"Lambert series",to_publication_date:2026-10-04,from_publication_date:2015-01-01`
- result: 176 hits (showing 8, newest first)
  1. 2026-10-01 - The two-block odd partition function - Mircea Merca - https://doi.org/10.1007/s11139-026-01426-1
  2. 2026-09-28 - Lambert Series Unify Totient, Möbius, and Divisor Sums — E8 Intelligence Research - Andrew Stewart Caldin - https://doi.org/10.5281/zenodo.23007377
  3. 2026-09-28 - Lambert Series Unify Totient, Möbius, and Divisor Sums — E8 Intelligence Research - Andrew Stewart Caldin - https://doi.org/10.5281/zenodo.23007376
  4. 2026-09-27 - Prime-Detecting Identities from Dirichlet Inversion - Zhichen Liu - https://doi.org/10.48550/arxiv.2609.33278
  5. 2026-09-24 - Resurgent Lambert series from Feynman and beyond - David Broadhurst, Daniele Dorigoni - https://doi.org/10.22323/1.521.0020
  6. 2026-09-07 - Zero Geometry and Curvature of Divisor Exponential Sums: Prime-Index Repunits and the Positive-Limsup Problem - K. Fathi - https://doi.org/10.5281/zenodo.22651815
  7. 2026-09-07 - Zero Geometry and Curvature of Divisor Exponential Sums: Prime-Index Repunits and the Positive-Limsup Problem - K. Fathi - https://doi.org/10.5281/zenodo.22729613
  8. 2026-08-27 - Apéry-type approximations and irrationality measures for certain $q$-series - Junnosuke Koizumi, Anju Yokoi - https://doi.org/10.48550/arxiv.2608.26918

### formal-conjectures PRs "Lambert series" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"Lambert series" created:>=2015-01-01' --state all --json number,title,author,createdAt,url,state --limit 8`
- result: 6 hits (newest first)
- note: gh returns no total; count is rows returned
  1. 2026-08-18 - #5047 Erdős 257: add four settled infinite-support families - wcook04 - https://github.com/google-deepmind/formal-conjectures/pull/5047 [closed]
  2. 2026-07-03 - #4390 feat(ErdosProblems/1050): the series ∑ 1/(2ⁿ−3) is irrational - gotrevor - https://github.com/google-deepmind/formal-conjectures/pull/4390 [merged]
  3. 2026-06-17 - #4286 feat(ErdosProblems/1049): prove lambert_series_eq_num_divisor_sum - kukushking - https://github.com/google-deepmind/formal-conjectures/pull/4286 [merged]
  4. 2026-06-14 - #4269 feat(ErdosProblems/257): prove tsum_top_eq - williamjblair - https://github.com/google-deepmind/formal-conjectures/pull/4269 [merged]
  5. 2026-03-03 - #3069 solve(ErdosProblems): formally solved geq_2_integer variant in 1049 - theaustinhatfield - https://github.com/google-deepmind/formal-conjectures/pull/3069 [closed]
  6. 2026-03-03 - #2544 solve(ErdosProblems): formally solved geq_2_integer variant in 1049 - theaustinhatfield - https://github.com/google-deepmind/formal-conjectures/pull/2544 [closed]

### formal-conjectures issues "Lambert series" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"Lambert series"' --created '>=2015-01-01' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 8`
- result: 0 hits, instrument: gh search issues (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### Exact phrase "normality" - arXiv API
- query: `search_query=(abs:"normality" OR ti:"normality") AND submittedDate:[201501010000 TO 299912312359] sortBy=submittedDate desc`
- ERROR (not a zero - the instrument did not answer): InstrumentError: arXiv not retried: HTTP 503 after retries earlier this run

### Exact phrase "normality" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"normality",to_publication_date:2026-10-04,from_publication_date:2015-01-01`
- result: 93498 hits (showing 8, newest first)
  1. 2026-10-02 - Operator-Theoretic Resolution of Multiscale Elastic Stability: Pseudospectral Breakdown Boundary, Non-Self-Adjoint Operators, and the Invariant Coupling Parameter ΠENIGMA - Maxim Kolesnikov, Wm. B. Borgers - https://doi.org/10.5281/zenodo.23092329
  2. 2026-10-02 - Geometric Analysis of Airfoil Thickness Ratio Distribution in Fixed-Pitch Propeller Blades - Ego Widoro, Bhima Shakti Arrafat, Hadi Prayitno, Andri Kurniawan, R. Adam Daffa Suratmanto - https://doi.org/10.54147/langitbiru.v19i3.1595
  3. 2026-10-02 - Students' religious moderation in multicultural madrasahs: Perceived principal managerial effectiveness, teacher competence, and Love Curriculum-aligned experiences - Nurhayati Nurhayati, Ahmad al gufron, Mohamad S. Rahman, Lutfi Sahibe, Kholida Zulfa - https://doi.org/10.66053/ri.v4i5.1116
  4. 2026-10-02 - Operator-Theoretic Resolution of Multiscale Elastic Stability: Pseudospectral Breakdown Boundary, Non-Self-Adjoint Operators, and the Invariant Coupling Parameter ΠENIGMA - Maxim Kolesnikov, Wm. B. Borgers - https://doi.org/10.5281/zenodo.23092328
  5. 2026-10-02 - Pengaruh Ukuran Perusahaan terhadap Kinerja Keuangan pada PT Bank Central Asia Tbk Tahun 2015-2024 - Sahrul Asdar, Nayla Ramadani, Fathir Dwi Pamungkas, Aisha M. Abdullah, Jamaluddin Jamaluddin, Rudy Usman - https://doi.org/10.37481/sjr.v9i4.1637
  6. 2026-10-02 - Pengaruh Entrepreneurial Leadership terhadap Pembentukan Jiwa Wirausaha Mahasiswa di Sekolah Tinggi Teologi Anugerah Aliansi Semarang (STTAAS) Surakarta - Mikhael Ananda Supriyadi, Dyah Ayu Puri Palupi - https://doi.org/10.37481/sjr.v9i4.1725
  7. 2026-10-02 - Dampak IPO terhadap Kinerja Keuangan Perusahaan Sektor Properti di Bursa Efek Indonesia - Bintang Cahaya Putra, Amin Tohari, Mar’atus Solikah - https://doi.org/10.30640/inisiatif.v5i4.8073
  8. 2026-10-02 - Pengaruh Model Game-Based Learning Berbantuan Board game Untuk Meningkatkan Pemahaman Konsep Pada Materi Aktivitas Ekonomi Kelas V SDN Tambun 01 - Siska Nur Amalia, Maha Putra - https://doi.org/10.29303/goescienceed.v7i4.3348

### formal-conjectures PRs "normality" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"normality" created:>=2015-01-01' --state all --json number,title,author,createdAt,url,state --limit 8`
- result: 5 hits (newest first)
- note: gh returns no total; count is rows returned
  1. 2026-10-02 - #6790 feat: reorganize word normality/richness, add proved equivalences - rwst - https://github.com/google-deepmind/formal-conjectures/pull/6790 [open]
  2. 2026-09-20 - #6438 feat(Book/Bugeaud): Problem 10.49 (solved) - rwst - https://github.com/google-deepmind/formal-conjectures/pull/6438 [open]
  3. 2026-09-11 - #5752 fix(ForMathlib/NumberTheory/NormalNumber): define normality via digit blocks - smmercuri - https://github.com/google-deepmind/formal-conjectures/pull/5752 [merged]
  4. 2026-07-25 - #4624 feat(Wikipedia): separate algebraic normality conjectures - kernelpanic888 - https://github.com/google-deepmind/formal-conjectures/pull/4624 [merged]
  5. 2026-05-02 - #3926 feat: Normality of pi - Sfgangloff - https://github.com/google-deepmind/formal-conjectures/pull/3926 [merged]

### formal-conjectures issues "normality" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"normality"' --created '>=2015-01-01' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 8`
- result: 4 hits (newest first)
- note: gh returns no total; count is rows returned
  1. 2026-09-11 - #5700 Wikipedia/AlgebraicNormality: `irrational_algebraic_normal_in_some_base` asks only for simple normality, not normality - tadamcz - https://github.com/google-deepmind/formal-conjectures/issues/5700 [closed]
  2. 2026-09-11 - #5710 Wikipedia/NormalityOfPi: `pi_normal_base_ten` asserts only simple normality: `IsNormalInBase` ignores digit blocks - tadamcz - https://github.com/google-deepmind/formal-conjectures/issues/5710 [closed]
  3. 2026-02-10 - #2256 Normality of Irrational Algebraic Numbers - franzhusch - https://github.com/google-deepmind/formal-conjectures/issues/2256 [closed]
  4. 2026-02-10 - #2255 Normality of π - franzhusch - https://github.com/google-deepmind/formal-conjectures/issues/2255 [closed]

### Exact phrase "digits" - arXiv API
- query: `search_query=(abs:"digits" OR ti:"digits") AND submittedDate:[201501010000 TO 299912312359] sortBy=submittedDate desc`
- ERROR (not a zero - the instrument did not answer): InstrumentError: arXiv not retried: HTTP 503 after retries earlier this run

### Exact phrase "digits" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"digits",to_publication_date:2026-10-04,from_publication_date:2015-01-01`
- result: 29871 hits (showing 8, newest first)
  1. 2026-10-02 - pq-verify: Independent verification for ML-KEM / ML-DSA implementations - Nicholas Daniel Maino - https://doi.org/10.5281/zenodo.21739510
  2. 2026-10-02 - Supplementary material from "Modularity without convergence: integrated evolution of the salamander autopodium" - Giacomo Rosa, Emma Centomo, Andrea Costa, Elisa Damonte, Julien Renet, Antonio Romano et al. - https://doi.org/10.6084/m9.figshare.c.8693409
  3. 2026-10-02 - GateMPC: identifying a canal gate law from an open archive, and what it costs predictive control - Adilbay Kudaybergenov, Mukhabbad Kazimbetova, Gulsara Ametova, Jadira Ispanova, Elzura Pulatovna Urazimbetova, Bayram Absametov - https://doi.org/10.5281/zenodo.22549213
  4. 2026-10-02 - Point-Vortex Collapse Without Rotation: A Cluster Mechanism, a Phase Diagram and a Continuum Limit - Chase Hendrick - https://doi.org/10.5281/zenodo.22969840
  5. 2026-10-02 - An Efficient Complex-CSR Sparse Matrix-Vector Multiplication Framework Under Dynamic Arbitrary-Precision Ball Arithmetic - Abraham Mateos - https://doi.org/10.5281/zenodo.23019867
  6. 2026-10-02 - GateMPC: identifying a canal gate law from an open archive, and what it costs predictive control - Adilbay Kudaybergenov, Mukhabbad Kazimbetova, Gulsara Ametova, Jadira Ispanova, Elzura Urazimbetova, Bayram Absametov - https://doi.org/10.5281/zenodo.23090666
  7. 2026-10-02 - GS1 GTIN Test Data - StanzaAPI - https://doi.org/10.5281/zenodo.23076188
  8. 2026-10-02 - International dialing codes and trunk-prefix rules (241 destinations) - InternationalCall.co - https://doi.org/10.5281/zenodo.23105931

### formal-conjectures PRs "digits" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"digits" created:>=2015-01-01' --state all --json number,title,author,createdAt,url,state --limit 8`
- result: 8 hits (newest first)
- note: gh returns no total; 8 = the --limit, so more may exist
  1. 2026-10-03 - #6832 feat(Other/SchurTruncatedExponential): formal proof of Schur's theorem on truncated exponentials - anatoliiohorodnyk - https://github.com/google-deepmind/formal-conjectures/pull/6832 [open]
  2. 2026-10-03 - #6821 feat(ErdosProblems/102): formal proofs of the hunter and upper_sqrt variants - anatoliiohorodnyk - https://github.com/google-deepmind/formal-conjectures/pull/6821 [open]
  3. 2026-09-27 - #6629 feat(ErdosProblems/482): Graham–Pollak digits of √2 - gotrevor - https://github.com/google-deepmind/formal-conjectures/pull/6629 [merged]
  4. 2026-09-24 - #6577 Erdős 249: add countable least-residue dilation independence - wcook04 - https://github.com/google-deepmind/formal-conjectures/pull/6577 [open]
  5. 2026-09-24 - #6528 Erdős 257: add weighted and mixed-support irrationality variants - wcook04 - https://github.com/google-deepmind/formal-conjectures/pull/6528 [open]
  6. 2026-09-08 - #5340 feat(OptimizationConstants): irrationality exp of pi and $Gamma 1/4$ - felixpernegger - https://github.com/google-deepmind/formal-conjectures/pull/5340 [open]
  7. 2026-08-25 - #5168 feat(Wikipedia): add the emirp infinitude question - derekste - https://github.com/google-deepmind/formal-conjectures/pull/5168 [open]
  8. 2026-08-25 - #5169 feat(Other): add the Smarandache–Wellin prime conjecture - derekste - https://github.com/google-deepmind/formal-conjectures/pull/5169 [open]

### formal-conjectures issues "digits" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"digits"' --created '>=2015-01-01' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 8`
- result: 8 hits (newest first)
- note: gh returns no total; 8 = the --limit, so more may exist
  1. 2026-09-11 - #5710 Wikipedia/NormalityOfPi: `pi_normal_base_ten` asserts only simple normality: `IsNormalInBase` ignores digit blocks - tadamcz - https://github.com/google-deepmind/formal-conjectures/issues/5710 [closed]
  2. 2026-09-11 - #5695 OEIS/87455: `SatisfiesBenford` states only the first-digit law, not the full significand distribution - tadamcz - https://github.com/google-deepmind/formal-conjectures/issues/5695 [closed]
  3. 2026-09-11 - #5700 Wikipedia/AlgebraicNormality: `irrational_algebraic_normal_in_some_base` asks only for simple normality, not normality - tadamcz - https://github.com/google-deepmind/formal-conjectures/issues/5700 [closed]
  4. 2026-08-25 - #5163 Formalize the infinitude question for emirps - derekste - https://github.com/google-deepmind/formal-conjectures/issues/5163 [open]
  5. 2026-08-25 - #5164 Formalize the Smarandache–Wellin prime infinitude conjecture - derekste - https://github.com/google-deepmind/formal-conjectures/issues/5164 [open]
  6. 2026-08-25 - #5160 Formalize the infinitude conjecture for decimal repunit primes - derekste - https://github.com/google-deepmind/formal-conjectures/issues/5160 [open]
  7. 2026-08-06 - #4788 Formalize home-prime termination (OEIS A037274) - derekste - https://github.com/google-deepmind/formal-conjectures/issues/4788 [closed]
  8. 2026-04-05 - #3697 Periodicity of finite octal games - aeroplugin - https://github.com/google-deepmind/formal-conjectures/issues/3697 [open]

### papers followups 1509.05422 (Tao 2016, log 2-point Elliott)
```
2026  arXiv:2609.37332       Truncated pretentious distances of multiplicative arithmetic functions  [Thomas Renard]
2026  arXiv:2609.28526       Effective logarithmic two-point Chowla bounds in every window  [S. D. Hughes]
2026  arXiv:2608.26814       Two-point correlations of multiplicative functions with dense orbits  [N. Tardy]
2026  arXiv:2608.27418       Value distribution of multiplicative functions along linear fractional sequences  [Sun-Kai Leung]
2026  arXiv:2608.16108       Two averaged dynamical generalizations of Chowla's conjecture  [Biao Wang]
2026  arXiv:2607.15574       Improved bounds for multiplicative functions in almost all short intervals  [Siddarth Menon]
2026  arXiv:2605.13733       Helmholzian Spectra of Graphs: Novel Properties  [Lu Lu, Yongtang Shi, Zoran Stanić]
2026  arXiv:2604.25446       The Subtractive Divisor Orbit: Unconditional Bounds, Parity Constraints, and a Conditional Framework  [Marco Mantovanelli]
2026  doi:10.1112/jlms.70483 Arithmetic progressions at the Journal of the LMS  [Ben Green]
2026  doi:10.37648/ijrst.v16i02.002 The Critical Line from First Principles: A Complete Unconditional Liouville-Collar Closure of the Riemann Hypothesis  [Deep Bhattacharjee]
2026  doi:10.4213/dm1921     Об исключительном множестве длин интервалов суммирования в бинарной задаче Чоулы  [T. Preobrazhenskaya, S. Preobrazhenskii]
2025  arXiv:2512.03292       The distribution of prime values of random polynomials  [Noah Kravitz, K. Woo, Max Wenqiang Xu]
2025  arXiv:2511.04419       Almost Countable Spectrum and Logarithmic Sarnak Conjecture  [Wen Huang, M. Tan, Leiye Xu]
2025  arXiv:2507.00515       Sums and products in sets of positive density  [F. Richter]
2025  arXiv:2506.18065       Liouville function, von Mangoldt function, and norm forms at random binary forms  [Yi-Jie Diao]
2025  arXiv:2506.12845       Bounded exponential sums with multiplicative coefficients  [Péa Bazin, Ihor Pylaiev, F. Tyrrell]
2025  arXiv:2501.10962       On variants of Chowla’s conjecture  [Krishnarjun Krishnamoorthy]
2024  arXiv:2412.17199       On Shusterman's Goldbach-type problem for sign patterns of the Liouville function  [Alexander P. Mangerel]
2024  arXiv:2412.03504       On multiplicative recurrence along linear patterns  [Dimitrios Charamaras, Andreas Mountakis, Konstantinos Tsinas]
2024  arXiv:2411.17523       Partition regularity of homogeneous quadratics: Current trends and challenges  [N. Frantzikinakis]
2024  arXiv:2409.10663       The Chowla conjecture and Landau–Siegel zeroes  [Mikko Jaskari, Stelios Sachpazis]
2024  arXiv:2409.05952       Random Chowla's Conjecture for Rademacher Multiplicative Functions  [Jake Chinis, B. Shala]
2024  arXiv:2409.02106       Correlations of the Möbius and Liouville functions with their partial sums  [Gordon Chavez]
2024  arXiv:2408.08726       Higher Moments for Polynomial Chowla  [Cameron Wilson]
2023  arXiv:2311.11636       Gap problems for integer-valued multiplicative functions  [Alexander P. Mangerel]
2023  doi:10.1112/mtk.12227  Correlation of multiplicative functions over Fq[x]$\mathbb {F}_q[x]$ : A pretentious approach  [P. Darbar, Anirban Mukhopadhyay]
2023  arXiv:2310.07873       Stability under scaling in the local phases of multiplicative functions  [M. N. Walsh]
2023  arXiv:2310.05528       On the Local Fourier Uniformity Problem for Small Sets  [Adam Kanigowski, M. Lema'nczyk, F. Richter]
2023  arXiv:2309.10636       Partition regularity of Pythagorean pairs  [N. Frantzikinakis, O. Klurman, Joel Moreira]
2023  arXiv:2306.09929       On Equal Consecutive Values of Multiplicative Functions  [Alexander P. Mangerel]
2023  arXiv:2305.09885       On asymptotically automatic sequences  [Jakub Konieczny]
2023  arXiv:2304.05344       On Elliott's conjecture and applications  [O. Klurman, Alexander P. Mangerel, Joni Teravainen]
2023  arXiv:2304.03121       Furstenberg systems of pretentious and MRT multiplicative functions  [N. Frantzikinakis, M. Lema'nczyk, T. de la Rue]
2023  arXiv:2303.12574       On a Bohr set analogue of Chowla’s conjecture  [Joni Teräväinen, A. Walker]
2023  doi:10.3934/dcds.2022187 Sequence complexity, rigidity and logarithmic Sarnak conjecture  [Rui Qiu, R. Wei, Leiye Xu]
2022  arXiv:2212.10373       Bateman–Horn, polynomial Chowla and the Hasse principle with probability 1  [T. Browning, E. Sofos, Joni Teräväinen]
2022  arXiv:2211.15830       On the multiplicative independence between $n$ and $\lfloor \alpha n\rfloor $  [David Crnvcev'ic, Felipe Hern'andez, Kevin Rizk]
2022  arXiv:2211.09736       Equidistributions of Sign Patterns of the Liouville Function and Normal Numbers  [N. Carella]
2022  arXiv:2211.00379       Chowla and Sarnak conjectures for Kloosterman sums  [Houcein El Abdalaoui, I. Shparlinski, Raphael S. Steiner]
2022  arXiv:2208.12219       Note on the Chowla Conjecture and the Discrete Fourier Transform  [N. Carella]
2022  arXiv:2206.12956       Result on the Mobius Function over Shifted Primes  [N. Carella]
2022  doi:10.4204/eptcs.358.0.02 On the Collatz Conjecture  [J. Czelakowski]
2022  arXiv:2202.10370       Beyond the Erdős discrepancy problem in function fields  [O. Klurman, Alexander P. Mangerel, Joni Teräväinen]
2022  arXiv:2202.08767       On the random Chowla conjecture  [O. Klurman, I. Shkredov, M. Xu]
2022  arXiv:2202.01071       Autocorrelation of the Mobius Function  [N. Carella]
2022  arXiv:2201.00799       Expansion, divisibility and parity: an explanation  [H. Helfgott]
2022  -                      ON THE COVARIANCE  [Gordon V. Chavez]
2022  -                      Results for the Mobius Function and Liouville Function over the Shifted Primes  [N. Carella]
2022  -                      Counting primes  [J. Maynard]
2021  arXiv:2110.03401       Complex Valued Multiplicative Functions with Bounded Partial Sums  [Marco Aymone]
2021  arXiv:2109.06291       The Hardy–Littlewood–Chowla conjecture in the presence of a Siegel zero  [T. Tao, Joni Teräväinen]
2021  arXiv:2108.12351       Additive functions in short intervals, gaps and a conjecture of Erdős  [Alexander P. Mangerel]
2021  arXiv:2108.11401       Divisor-bounded multiplicative functions in short intervals  [Alexander P. Mangerel]
2021  arXiv:2105.14653       Siegel zeros and Sarnak's conjecture  [Jake Chinis]
2021  arXiv:2105.15195       The upper logarithmic density of monochromatic subset sums  [David Conlon, Jacob Fox, H. Pham]
2021  arXiv:2102.05842       Exact formulas for partial sums of the M\"obius function expressed by partial sums weighted by the Liouville lambda function  [M. Schmidt]
2021  arXiv:2101.10134       Möbius Disjointness for product flows of rigid dynamical systems and affine linear flows  [Fei Wei]
2021  -                      ON THE CORRELATION BETWEEN MÖBIUS AND POLYNOMIAL PHASES IN SHORT ARITHMETIC PROGRESSIONS  [Fei Wei]
2020  arXiv:2010.07924       On the Liouville function at polynomial arguments  [Joni Teräväinen]
2020  arXiv:2009.14773       (Logarithmic) densities for automatic sequences along primes and squares  [B. Adamczewski, M. Drmota, Clemens Müllner]
```

### papers followups 1708.02610 (Tao-Teräväinen 2019, structure of log correlations)
```
2026  arXiv:2609.37332       Truncated pretentious distances of multiplicative arithmetic functions  [Thomas Renard]
2026  doi:10.37648/ijrst.v16i02.002 The Critical Line from First Principles: A Complete Unconditional Liouville-Collar Closure of the Riemann Hypothesis  [Deep Bhattacharjee]
2025  arXiv:2512.03292       The distribution of prime values of random polynomials  [Noah Kravitz, K. Woo, Max Wenqiang Xu]
2025  arXiv:2511.04419       Almost Countable Spectrum and Logarithmic Sarnak Conjecture  [Wen Huang, M. Tan, Leiye Xu]
2025  arXiv:2507.09271       On the correlations between character sums of division polynomials under shifts  [Subham Bhakta, Igor E. Shparlinski]
2025  arXiv:2506.18065       Liouville function, von Mangoldt function, and norm forms at random binary forms  [Yi-Jie Diao]
2025  arXiv:2502.17073       Global well-posedness of the cubic nonlinear Schrödinger equation on T2\documentclass[12pt]{minimal} \usepackage{amsmath} \usepackage{wasysym} \usepackage{amsfonts} \usepackage{amssymb} \usepackage{amsbsy} \usepackage{mathrsfs} \usepackage{upgreek} \setlength{\oddsidemargin}{-69pt} \begin{document}$  [Sebastian Herr, Beomjong Kwak]
2025  arXiv:2501.10962       On variants of Chowla’s conjecture  [Krishnarjun Krishnamoorthy]
2024  arXiv:2411.17523       Partition regularity of homogeneous quadratics: Current trends and challenges  [N. Frantzikinakis]
2024  arXiv:2409.18116       Averages of arithmetic functions over polynomials in many variables  [Kevin Destagnol, E. Sofos]
2024  arXiv:2409.10663       The Chowla conjecture and Landau–Siegel zeroes  [Mikko Jaskari, Stelios Sachpazis]
2024  arXiv:2409.05952       Random Chowla's Conjecture for Rademacher Multiplicative Functions  [Jake Chinis, B. Shala]
2024  arXiv:2409.02106       Correlations of the Möbius and Liouville functions with their partial sums  [Gordon Chavez]
2024  arXiv:2408.08726       Higher Moments for Polynomial Chowla  [Cameron Wilson]
2023  doi:10.1112/mtk.12227  Correlation of multiplicative functions over Fq[x]$\mathbb {F}_q[x]$ : A pretentious approach  [P. Darbar, Anirban Mukhopadhyay]
2023  arXiv:2310.07873       Stability under scaling in the local phases of multiplicative functions  [M. N. Walsh]
2023  arXiv:2305.11486       Pseudorandom Binary Sequences: Quality Measures and Number-Theoretic Constructions  [Arne Winterhof]
2023  arXiv:2304.05344       On Elliott's conjecture and applications  [O. Klurman, Alexander P. Mangerel, Joni Teravainen]
2023  arXiv:2304.03121       Furstenberg systems of pretentious and MRT multiplicative functions  [N. Frantzikinakis, M. Lema'nczyk, T. de la Rue]
2023  arXiv:2303.15628       Measure growth in compact semisimple Lie groups and the Kemperman Inverse Problem  [Yi-Fan Jing, Chieu-Minh Tran]
2023  doi:10.3934/dcds.2022187 Sequence complexity, rigidity and logarithmic Sarnak conjecture  [Rui Qiu, R. Wei, Leiye Xu]
2022  arXiv:2212.10373       Bateman–Horn, polynomial Chowla and the Hasse principle with probability 1  [T. Browning, E. Sofos, Joni Teräväinen]
2022  arXiv:2211.00379       Chowla and Sarnak conjectures for Kloosterman sums  [Houcein El Abdalaoui, I. Shparlinski, Raphael S. Steiner]
2022  -                      ON THE COVARIANCE  [Gordon V. Chavez]
2021  arXiv:2109.06291       The Hardy–Littlewood–Chowla conjecture in the presence of a Siegel zero  [T. Tao, Joni Teräväinen]
2021  arXiv:2108.11401       Divisor-bounded multiplicative functions in short intervals  [Alexander P. Mangerel]
2021  arXiv:2106.11835       A dynamical proof of the van der Corput inequality  [N. Edeko, H. Kreidler, R. Nagel]
2021  arXiv:2106.01058       Decomposition of multicorrelation sequences and joint ergodicity  [S. Donoso, Andreu Ferré Moragues, Andreas Koutsogiannis]
2021  arXiv:2105.14653       Siegel zeros and Sarnak's conjecture  [Jake Chinis]
2021  arXiv:2103.13551       Sublacunary sets and interpolation sets for nilsequences  [Anh N. Le]
2020  arXiv:2010.07924       On the Liouville function at polynomial arguments  [Joni Teräväinen]
2020  arXiv:2009.13497       Correlations of multiplicative functions in function fields  [O. Klurman, Alexander P. Mangerel, Joni Teräväinen]
2020  arXiv:2009.04757       Sarnak’s Conjecture from the Ergodic Theory Point of View  [J. Kułaga-Przymus, M. Lemańczyk]
2020  arXiv:2009.03225       Monotone chains of Fourier coefficients of Hecke cusp forms  [O. Klurman, Alexander P. Mangerel]
2020  -                      Monotone chains of Fourier coefficients of Hecke cusp forms  [O. Klurman, Alexander P. Mangerel]
2020  arXiv:2009.02090       Polynomial mean complexity and logarithmic Sarnak conjecture  [Wen Huang, Leiye Xu, Xiang-Dong Ye]
2020  doi:10.19086/DA.13688  Good weights for the Erdős discrepancy problem  [N. Frantzikinakis]
2020  arXiv:2006.09958       On Furstenberg systems of aperiodic multiplicative functions of Matomäki, Radziwiłł, and Tao  [A. Gomilko, M. Lemánczyk, T. de la Rue]
2020  arXiv:2004.11835       Structure of multicorrelation sequences with integer part polynomial iterates along primes  [Andreas Koutsogiannis, Anh N. Le, Joel Moreira]
2020  arXiv:2001.11523       A decomposition of multicorrelation sequences for commuting transformations along primes  [Anh N. Le, Joel Moreira, F. Richter]
2019  arXiv:2007.15644       Fourier uniformity of bounded multiplicative functions in short intervals on average  [Kaisa Matomäki, Maksym Radziwiłł, T. Tao]
2019  arXiv:1908.02732       Correlations of multiplicative functions along deterministic and independent sequences  [N. Frantzikinakis]
2019  arXiv:1906.02847       A tale of two omegas  [Michael J. Mossinghoff, T. Trudgian]
2019  arXiv:1905.09303       Correlation of multiplicative functions over function fields  [P. Darbar, A. Mukhopadhyay]
2019  arXiv:1905.00527       Interpolation sets and nilsequences  [Anh N. Le]
2019  doi:10.1142/9789813272880_0056 MULTIPLICATIVE FUNCTIONS IN SHORT INTERVALS, AND CORRELATIONS OF MULTIPLICATIVE FUNCTIONS  [Kaisa Matomäki, Maksym Radziwiłł]
2019  arXiv:1904.05096       VALUE PATTERNS OF MULTIPLICATIVE FUNCTIONS AND RELATED SEQUENCES  [T. Tao, Joni Teräväinen]
2019  arXiv:1903.01881       Good weights for the Erd\"os discrepancy problem  [N. Frantzikinakis]
2019  arXiv:1902.09712       Sarnak's Conjecture for nilsequences on arbitrary number fields and applications  [Wen-Bo Sun]
2019  doi:10.1007/s40687-019-0180-6 Disjointness of the Möbius Transformation and Möbius Function  [E. H. el Abdalaoui, I. Shparlinski]
2019  arXiv:1901.06460       Sarnak’s conjecture for sequences of almost quadratic word growth  [Redmond McNamara]
2018  doi:10.4171/OWR/2017/51 Mini-Workshop: Interplay between Number Theory and Analysis for Dirichlet Series  [Fr'ed'eric Bayart, Kaisa Matomäki, Eero Saksmann]
2018  arXiv:1812.01224       Fourier uniformity of bounded multiplicative functions in short intervals on average  [Kaisa Matomäki, Maksym Radziwiłł, T. Tao]
2018  doi:10.1134/S0081543818080163 An Inverse Theorem for an Inequality of Kneser  [T. Tao]
2018  arXiv:1810.08967       On the orbits of multiplicative pairs  [O. Klurman, Alexander P. Mangerel]
2018  arXiv:1809.03280       Dynamical models for Liouville and obstructions to further progress on sign patterns  [W. Sawin]
2018  arXiv:1809.02518       The structure of correlations of multiplicative functions at almost all scales, with applications to the Chowla and Elliott conjectures  [T. Tao, Joni Teräväinen]
2018  arXiv:1807.09569       Combinatorial identities and Titchmarsh’s
divisor problem for multiplicative functions  [S. Drappeau, Berke Topacogullari]
2018  arXiv:1804.08556       Furstenberg Systems of Bounded Multiplicative Functions and Applications  [N. Frantzikinakis, B. Host]
```
