# Linear forms in logarithms (E4): audit and freeze, 2026-10-04

Lane: engine proposal E4 (`docs/ENGINE-PROPOSALS-2026-10-04.md`).  Lean: `src/NormalNumbers/LinearFormsScales.lean` (freeze) and `src/NormalNumbers/LinearFormsScalesStretch.lean` (stretch Props), branch `proof/lfl`; Maze rows on `audit/lfl`.

## Bottom line

- **E4 has no consumer in this repo's engines.**  Baker / Matveev bound near-coincidences `2ᵐ ≈ 3ⁿ`.  The avoidance engine consumes the number of obstacles per stage, which is elementary (`band_unique_u`), and the Stoneham profile questions need short-orbit equidistribution of `3ⁿ mod 2ᶜ`, which separation does not touch.  The cited Prop is frozen anyway, with one honest consumer (`gap_of_scaleSeparation`, Tijdeman's gap principle) and its known-false sibling (`not_scaleSeparation_two_four`).
- **Best open question found:** log-rate avoidance along Furstenberg's semigroup, `FurstenbergLogAvoid` (frozen headline `furstenbergLogAvoid_holds`, `sorry`): remove the `log log q` loss from the Moshchevitin / Peres–Schlag bound.  True 55%, provable 7%.  It is not driven by linear forms.
- Because the best statement is below 40%, the closed routes are recorded as Maze rows on `audit/lfl`.

## 1. Negative inventory (read before proposing)

| Source | What it rules out |
|---|---|
| `Stoneham.lean` (`isNormal_two_stoneham23`), `StonehamSixFailure.lean` (`not_isNormal_six_stoneham23`, forced zeros in `[3ᵐ, 1.1·3ᵐ)`), `StonehamBase6.lean` (`stoneham_base6_readout`: base-6 digits read `3ᵃ mod 2ᶜ`), `StonehamBoundary.lean` (`isDisjunctive_six_stoneham23`) | Base 2 normal, base 6 non-normal and disjunctive are DONE. |
| KB `stoneham-mixed-base-audit-2026-09-13.md`, `normal-numbers-mixed-base-disjunctivity-2026-09-13.md` | Disjunctivity for every `6 ∣ B`, `B < 8^{v₂(B)}` has a reviewed paper proof; that is exactly Bailey–Borwein's non-normality region (Ramanujan J. 29 (2012), Theorem 2 and Example 1).  Base 18 is outside. |
| Maze: "sparse Stoneham relative as open" (priorArt, Vandehey 2019 Thm 7.4), "Stoneham base-6 as a new method" (priorArt, Hertling), "Hertling direct substitution" (refuted), "alpha_{2,3} abelian-normal in base 6" (kernel), "Furstenberg-intersection route" (wall) | No Stoneham-family novelty left at the easy end; intersection-theorem routes are toothless. |
| Maze header: "Three external doors … Diophantine (separation of powers, linear forms in logs), dynamical (×2×3 …)" | E4 is the Diophantine door; the header already warns all three doors stand before the same Weyl-sum wall. |
| `UniformBad.lean`, `docs/notes/bugeaud-10-36-uniform-bad.md` | 10.36 with `c = 24`, no cited input; guards `not_uniformBad_of_third_le`, `not_uniformBad_largeBases_of_le_one`.  The engine needed no separation of scales. |
| `docs/OPEN-PROBLEMS-SWEEP-2026-10-03c.md` | Bugeaud 10.19–10.30 are ×2×3-hard; 10.22 (density-zero nonzero digits in two independent bases) is the cleanest instance. |
| `docs/OPEN-PROBLEMS-SWEEP-2026-10-04.md`, E4 row | Stoneham base-3 normality (Bailey–Borwein §5, verbatim there) graded 3%: "E4 supplies scale separation, not this short-orbit equidistribution." |
| `docs/OPEN-PROBLEMS-SWEEP-2026-10-04.md` row 5 | Bugeaud Problem 7.3 below the golden ratio, 8%, tags E4 but its crux is a triangle-inequality union bound, not separation. |

## 2. Where linear forms in logarithms actually enter

| Use | Literature | In this repo |
|---|---|---|
| Gaps between consecutive `2ᵘ3ᵛ` | Tijdeman, Compositio 26 (1973) | Wired: `gap_of_scaleSeparation`. No avoidance step uses it. |
| Lattice counts of `Σ` in short multiplicative intervals; effective Furstenberg | Gayfulin–Moshchevitin arXiv:2301.08212 §3 (Feldman's irrationality measure of `log a / log b`); Bourgain–Lindenstrauss–Michel–Venkatesh, ETDS 29 (2009) | This is the DENSITY side (upper bounds on avoidance), polylog-hopeless: BLMV give `(log log log q)^{−κ}`.  Stretch Prop `FurstenbergLogOptimal`. |
| Integers with few digits in two bases | Senge–Straus 1973 (Roth, ineffective); Stewart, Crelle 319 (1980) (Baker, effective) | Integer problem, off-lane.  The real analogue (Bugeaud, Rev. Mat. Iberoam. 28 (2012), Thm 2.3: `NZ(n,ξ,b) + NZ(n,ξ,b′) ≥ c log n` for coprime independent `b, b′`) uses only `|r/bⁿ − r′/b′ʰ| ≥ 1/(bⁿb′ʰ)`.  Improving it needs lower bounds for `S`-unit sums with about `log n` terms, where Baker gives nothing effective. |
| Avoidance engines (`UniformBad`, Schmidt games) | | The per-stage obstacle COUNT is elementary (`band_unique_u`).  Near-coincident scales neither add nor remove obstacles. |
| Stoneham normality profile | Bailey–Borwein 2012 | Outside `B < 8^{v₂(B)}` no Stoneham term becomes integral before the next one is live.  Base 3: every earlier term stays a nonzero fraction with a power-of-2 denominator.  Base 18: two terms live at every position, the later one a high-bit readout of `9ˣ mod 2^{Θ(3ᵐ)}`.  Both need `ShortPowerOrbitEquidist`. |

## 3. Candidates

### C1. The Stoneham profile of `α₂,₃` (E4's own named question)

- **Exact wording.**  Bailey–Borwein, *Nonnormality of Stoneham constants*, Ramanujan J. 29 (2012) §5: "it is not known at the present time whether or not α2,3 is 3-normal, although it appears to be. … But there is no proof of 3-normality.  Similar questions remain in the more general case of αb,c" (quoted from the davidhbailey.com copy in the 10-04 sweep).
- **Known profile.**  Normal to every base `2ᵏ` (Stoneham 1973; Bailey–Crandall 2002; repo `isNormal_two_stoneham23`).  Not normal to every `B` with `6 ∣ B`, `B < 8^{v₂(B)}` (Bailey–Borwein Thm 2), and disjunctive there (repo base 6 in Lean; general paper proof in the KB).  Every other base is open: 3, 5, 7, 10, 18, 30, ….
- **Difficulty.**  Base `B` with `3 ∣ B` and `B ≥ 8^{v₂(B)}`, or `3 ∤ B`: the needed input is equidistribution of `3ⁿ mod 2ᶜ` over `n` in a window of length `O(c)` against period `2^{c−2}` (Korobov / Erdős #406 regime).  Separation of scales does not touch it.
- **Lean.**  Stretch Props `StonehamBase3Normal`, `StonehamBase18Normal`; reopen condition `ShortPowerOrbitEquidist`.  **2%.**

### C2. Log-rate avoidance along Furstenberg's semigroup (frozen headline)

- **Exact wording.**  Moshchevitin, *On some open problems in Diophantine approximation*, arXiv:1202.4539v3, §1.5 item 4: "Peres-Schlag's method gives the following result: for an arbitrary sequence η_q, q = 1, 2, 3, ... there exists irrational θ such that inf_{q⩾2} √q log q ||s_q θ − η_q|| > 0", and "I am sure that in homogemeous setting the original Theorem 9 and the results from 3), 4) are not optimal and may be improved on.  From the other hand it may happen that the order of approximation in the setting with arbitrary sequence {η_q} is optimal".  Gayfulin–Moshchevitin, arXiv:2301.08212v2, §2: `B = {α : inf_{q∈Σ} log q log log q · ||qα|| > 0}` has full dimension; Badziahin–Harrap: `{α : inf (log q)^{1+ε} ||qα|| > 0}` is Cantor-winning; "As far as we know it is not known if the set B is a Cantor-winning set or is winning in some other game."
- **Verified source for the `1+ε` bound.**  Badziahin–Harrap, *Cantor-winning sets and their applications*, arXiv:1503.04738v3, Theorem 17: `Bad_{×a,×b}(g) ∩ [0,1]` is `ε/(1+ε)`-Cantor-winning for `g(q) = (log* q)^{1+ε}`; their Remark after it: for `g₁ = log* q · log* log q` the set has full Hausdorff dimension, "However, this would not give us the Cantor winning property".  Cited as `Literature.BadziahinHarrap17`, implied by the headline (`badziahinHarrap_of_logAvoid`).
- **Statement frozen.**  `FurstenbergLogAvoid`: some irrational `α`, `c > 0`, with `‖qα‖ ≥ c / log q` for all `q = 2ᵘ3ᵛ ≥ 2` (equivalently `inf √q ‖s_q α‖ > 0`).
- **What the repo engine gives (our estimates, not proved in Lean).**  `exists_avoid_of_stagePotential` with the square-root potential: `(log q)^{−2}` (about `k` denominators per stage, two obstacles each per window).  An exponent-`γ` potential: `(log q)^{−1/γ}`, Badziahin–Harrap strength.  Stage-dependent `K`: `exp(−C√(log log q))/log q`, still short of Peres–Schlag.
- **Difficulty check.**  Proved implication: headline ⇒ published bound (`moshchevitinPeresSchlag_of_logAvoid`), so it is a strengthening, not a restatement.  Unproved premise: a carrying rule with linear cost for about `k` obstacles of relative size `c/k` per stage.  Mechanism: none known.  Lovász local lemma loses `log`; potentials lose a power.  The only extra lever identified is homogeneity (obstacles at reduced `S`-rationals, `‖2qα‖ ≤ 2‖qα‖`).  **Known-false siblings:** (i) constant rate for an independent pair is false (`not_constAvoid_of_furstenberg`, from cited Furstenberg), so any mechanism must produce a rate tending to `0`; (ii) the dependent pair `{2ᵘ4ᵛ}` has a constant rate (`constAvoid_powersOfTwo`), so the difficulty is independence, not separation; (iii) by Moshchevitin's remark the inhomogeneous order may be optimal, so a mechanism blind to `η = 0` is suspect.
- **Linear forms.**  Not expected to enter.  Same-stage denominators that nearly coincide only make obstacles overlap, which helps avoidance.
- **True 55%; provable in a campaign 7%.**
- **E1 handoff.**  Gayfulin–Moshchevitin's explicit question (is `B` Cantor-winning?) belongs to the games lane E1, about 20% there.

### C3. Two-base sparsity, the real Stewart theorem

- **Exact wording.**  Bugeaud, Rev. Mat. Iberoam. 28 (2012), Problem 1: "Are there irrational real numbers having a 'simple' expansion in two multiplicatively independent bases?"; Problem 2 (zero entropy in two independent bases); Theorem 2.3 (`NZ(n,ξ,b) + NZ(n,ξ,b′) ≥ c log n` for coprime independent bases).  Bugeaud–Kim, Ann. Inst. Fourier (arXiv:1512.06935), Theorem 1.3 answers Problem 3 via the `S`-unit theorem.
- **Newest adjacent work.**  Bugeaud, *On the binary representation of powers of 3*, arXiv:2608.23017 (2026): only finitely many powers of 3 have a simple binary representation (integer side).
- **Difficulty.**  Improving `c log n` needs `S`-unit sums with about `log n` terms to stay away from `0`.  Effective bounds do not exist at that term count; the density-zero form is Bugeaud 10.22, already ×2×3-walled.  **3%.**  Not frozen in Lean (it would need an `NZ` definition first).

### C4. Multi-base orbit avoidance with explicit rates (beyond `bugeaud_10_36`)

- The engine already handles all bases at once with no separation input.  Variants (adding bad approximability (7.15) to the uniform 10.36 bound) look provable by the same engine, about 70%, but they are modest strengthenings of our own result and use no linear forms.  Recorded here as an engine follow-up, not an E4 deliverable.

## 4. The E4 proposal, graded

E4 claimed: "Matveev Prop (refereed) plus a multi-base avoidance theorem with a rate the current potential engine cannot give: 35%."  Outcome: the Prop is frozen (`Literature.BakerScaleSeparation`, referee needed).  An avoidance rate beyond the √-potential exists in print already (Peres–Schlag, Moshchevitin, Badziahin–Harrap), and going past them needs no linear forms.  **Recommendation: demote E4 from an engine to a cited input.**  It stays available for any future step that needs the gap principle.

## 5. Freeze

- `src/NormalNumbers/LinearFormsScales.lean`: `ScaleSeparation`, `MulIndep`, `Literature.BakerScaleSeparation`, `scaleSeparation_two_three`, `not_mulIndep_two_four`, `not_scaleSeparation_two_four`, `furstenbergSet`, `band_unique_u`, `gap_of_scaleSeparation`, `Literature.Furstenberg1967`, `Literature.MoshchevitinPeresSchlag`, `Literature.BadziahinHarrap17`, `ConstAvoid`, `FurstenbergLogAvoid`, **`furstenbergLogAvoid_holds` (sorry)**, `moshchevitinPeresSchlag_of_logAvoid`, `badziahinHarrap_of_logAvoid`, `not_constAvoid_of_furstenberg`, `constAvoid_powersOfTwo`.
- `src/NormalNumbers/LinearFormsScalesStretch.lean`: `FurstenbergLogOptimal`, `StonehamBase3Normal`, `StonehamBase18Normal`, `ShortPowerOrbitEquidist`.
- Cited Props needing a referee: `Literature.BakerScaleSeparation` (check LMN 1995 Corollaire 2 and Matveev 2000 Cor. 2.3 numbering, and the derivation in its docstring), `Literature.Furstenberg1967` (Theorem IV.1 numbering), `Literature.MoshchevitinPeresSchlag` (arXiv:0709.3419; the `√ν log ν` ⇔ `log q log log q` conversion is Gayfulin–Moshchevitin's), `Literature.BadziahinHarrap17` (arXiv:1503.04738v3 Theorem 17, verified in the arXiv text; journal data not checked).
- `--require-decls src/NormalNumbers/LinearFormsScales.lean:FurstenbergLogAvoid,furstenbergLogAvoid_holds,moshchevitinPeresSchlag_of_logAvoid,badziahinHarrap_of_logAvoid,not_constAvoid_of_furstenberg,constAvoid_powersOfTwo,Literature.MoshchevitinPeresSchlag,Literature.BadziahinHarrap17,Literature.Furstenberg1967`

## 6. Searches run

Logged verbatim in the appendix (`prior-art`, 2026-10-04): arXiv 1202.4539 (Semantic Scholar 31 citers, OpenAlex 19), 0706.0223 Peres–Schlag (63 citers), 2301.08212 Gayfulin–Moshchevitin, 1512.06935 Bugeaud–Kim, exact phrases "Peres-Schlag", "sublacunary", "Furstenberg sequence", "non-lacunary semigroup", "badly approximable", "digit changes", "Stoneham", "linear forms in logarithms", authors Moshchevitin, Badziahin, Bugeaud, Kim, Bailey, Becher.  arXiv API calls hit HTTP 429 in part; those are recorded as ERROR, not as zeros.  Manual reads: Moshchevitin 1202.4539 §1.5 (full text), Gayfulin–Moshchevitin 2301.08212 §§1–3, Bugeaud Rev. Mat. Iberoam. 2012 (full text, EMS copy), Bugeaud–Kim 1512.06935 §1, Becher–Bugeaud–Slaman 1311.0332 (grep: no Baker input).  No citing paper claims `inf log q ‖qα‖ > 0` over `Σ`, or Cantor-winning of `B`.  Also read: Badziahin–Harrap 1503.04738 (Theorem 17 and remark, full text), Badziahin–Harrap–Nesharim–Simmons survey 1804.06499 (grep: no statement about `Σ`), Katz 1607.00670 abstract (qualitative density only).  Not reached: Furstenberg 1967 original, Peres–Schlag full text.

## Appendix: raw prior-art log

Verbatim output of `prior-art --append`, nine runs.  ERROR lines are instrument failures (arXiv HTTP 429/503, OpenAlex 404), not zeros.

## Prior-art log: arXiv:1202.4539 (2026-10-04 00:31 EDT)

### arXiv record: 1202.4539 - arXiv API
- query: `id_list=1202.4539`
- ERROR (not a zero - the instrument did not answer): InstrumentError: HTTP 429 from https://export.arxiv.org/api/query?id_list=1202.4539

### Forward citations of arXiv:1202.4539 - Semantic Scholar
- query: `papers followups 1202.4539`
- result: 31 hits (newest first)
- note: via `papers followups`
  1. 2026-09-02 - On the Growth of Denominators of Simultaneous Best Diophantine Approximations in a Norm Induced by an Inner Product - L. Shatunov - https://arxiv.org/abs/2609.02386
  2. 2026-03-14 - On some results of Korobov and Larcher and Zaremba's conjecture - I. Shkredov - https://arxiv.org/abs/2603.14116
  3. 2026 - Модулярные значения континуант с фиксированными краями - Игорь Давидович Кан - https://doi.org/10.4213/sm10170
  4. 2026 - Остатки континуант с большими фиксированными окончаниями - Игорь Давидович Кан - https://doi.org/10.4213/faa4296
  5. 2026 - Modular values of continuants with fixed prefixes and endings - I. Kan - https://doi.org/10.4213/sm10170e
  6. 2025-12-17 - Sums with Stern-Brocot sequences and the Minkowski question-mark function - Haomin Liu, Jia-Dong Lu, Yonghao Xie - https://doi.org/10.1007/s11139-025-01261-w
  7. 2025-04-10 - Sums with Stern-Brocot sequences and Minkowski question mark function - Haomin Liu, Jia-Dong Lu, Yonghao Xie - https://arxiv.org/abs/2504.07456
  8. 2023-12-26 - Continued Fraction Expansions Towards Zaremba’s Conjecture - K. Ayadi, Takao Komatsu - https://doi.org/10.1080/10586458.2023.2293285
  9. 2023-12-01 - Modular Generalization of the Bourgain–Kontorovich Theorem - I.-D. Kan - https://doi.org/10.1134/S0001434623110147
  10. 2023 - Модулярное обобщение теоремы Бургейна-Конторовича - Игорь Давидович Кан, Игорь Давидович Кан - https://doi.org/10.4213/mzm13942
  11. 2022-12-30 - On Korobov Bound Concerning Zaremba’s Conjecture - N. Moshchevitin, B. Murphy, I. Shkredov - https://arxiv.org/abs/2212.14646
  12. 2021 - Non-commutative methods in additive combinatorics and number theory - I. Shkredov - https://doi.org/10.1070/RM10029
  13. 2020-07-01 - Popular products and continued fractions - N. Moshchevitin, B. Murphy, I. Shkredov - https://doi.org/10.1007/s11856-020-2039-3
  14. 2019-04-12 - Applications of Siegel’s lemma to a system of linear forms and its minimal points - J. Schleischitz - https://arxiv.org/abs/1904.06121
  15. 2018-11-26 - Diophantine properties of fixed points of Minkowski question mark function - D. Gayfulin, N. Shulga - https://arxiv.org/abs/1811.10139
  16. 2018-09-10 - Localized Pisot Matrices and Joint Approximations of Algebraic Numbers - V. Zhuravlev - https://doi.org/10.1007/S10958-018-4035-2
  17. 2018-08-17 - Popular products and continued fractions - N. Moshchevitin, B. Murphy, I. Shkredov - https://arxiv.org/abs/1808.05845
  18. 2017-01-01 - A strengthening of a theorem of Bourgain and Kontorovich. IV - I.-D. Kan - https://doi.org/10.1070/IM8360
  19. 2016-01-05 - Some notes on the regular graph defined by Schmidt and Summerer and uniform approximation - J. Schleischitz - https://arxiv.org/abs/1601.00842
  20. 2014-07-15 - A strengthening of a theorem of Bourgain and Kontorovich - I. Kan, D. Frolenkov - https://arxiv.org/abs/1407.4054
  21. 2014-04-30 - A strengthening of a theorem of Bourgain and Kontorovich. III - I. Kan - https://arxiv.org/abs/1604.04884
  22. 2014 - Усиление теоремы Бургейна - Конторовича@@@A strengthening of the Bourgain - Kontorovich theorem - Игорь Давидович Кан, Игорь Давидович Кан, Дмитрий Андреевич Фроленков, D. A. Frolenkov - https://doi.org/10.4213/IM8032
  23. 2013-09-30 - On Diophantine exponents in dimension 4 - D. Gayfulin, N. Moshchevitin - https://arxiv.org/abs/1309.7826
  24. 2013-05-06 - On a Problem in Diophantine Approximation - E. Dimitrov, Y. Sinai - https://arxiv.org/abs/1305.1200
  25. 2013-02-14 - On the derivative of two functions from Denjoy-Tichy-Uitz family - D. Gayfulin - https://arxiv.org/abs/1302.3510
  26. 2012-12-29 - The winning property of mixed badly approximable numbers - Yaqiao Li - https://arxiv.org/abs/1212.6584
  27. 2012-12-22 - Khintchine's theorem on Chebyshev matrices - N. Moshchevitin - https://arxiv.org/abs/1212.5662
  28. 2012-09-08 - Diophantine exponents for systems of linear forms in two variables - N. Moshchevitin - https://arxiv.org/abs/1209.1697
  29. 2012-07-19 - A reinforcement of the Bourgain-Kontorovich's theorem - D. Frolenkov, I. Kan - https://arxiv.org/abs/1207.5168
  30. 2012-04-16 - Two-dimensional badly approximable vectors and Schmidt's game - Jinpeng An - https://arxiv.org/abs/1204.3610
  31. ???? - On the Growth of Denominators of Simultaneous Best Diophantine Approximations in the Euclidean Norm - L. Shatunov - -

### Forward citations of arXiv:1202.4539 - OpenAlex
- query: `works?filter=cites:<OpenAlex id of doi:10.48550/arXiv.1202.4539>`
- result: 19 hits (showing 10, newest first)
- note: OpenAlex work W1823809171
  1. 2023-01-01 - Модулярное обобщение теоремы Бургейна-Конторовича - Игорь Давидович Кан - https://doi.org/10.4213/mzm13942
  2. 2022-08-13 - Applications of Siegel’s lemma to a system of linear forms and its minimal points - Johannes Schleischitz - https://doi.org/10.2140/moscow.2022.11.125
  3. 2022-01-01 - Усиление теоремы Бургейна-Конторовича о малых значениях хаусдорфовой размерности - Игорь Давидович Кан - https://doi.org/10.4213/faa3894
  4. 2021-01-01 - Усиление метода Бургейна-Конторовича: три новых теоремы - Игорь Давидович Кан - https://doi.org/10.4213/sm9437
  5. 2021-01-01 - Некоммутативные методы в аддитивной комбинаторике и теории чисел - Il'ya Dmitrievich Shkredov - https://doi.org/10.4213/rm10029
  6. 2020-01-01 - Diophantine properties of fixed points of Minkowski question mark function - Dmitry Radislavovich Gayfulin, Nikita Shulga - https://doi.org/10.4064/aa181209-18-9
  7. 2019-02-25 - Верна ли гипотеза Зарембы? - Игорь Давидович Кан - https://doi.org/10.4213/sm9018
  8. 2018-09-10 - Localized Pisot Matrices and Joint Approximations of Algebraic Numbers - Владимир Георгиевич Журавлев - https://doi.org/10.1007/s10958-018-4035-2
  9. 2017-04-07 - SOME NOTES ON THE REGULAR GRAPH DEFINED BY SCHMIDT AND SUMMERER AND UNIFORM APPROXIMATION - Johannes Schleischitz - https://doi.org/10.17654/nt039020115
  10. 2017-01-01 - A strengthening of a theorem of Bourgain and Kontorovich. V - Игорь Давидович Кан - https://doi.org/10.1134/s0081543817010102

### Newest arXiv papers by Moshchevitin - arXiv API
- query: `search_query=au:"Moshchevitin" sortBy=submittedDate desc`
- ERROR (not a zero - the instrument did not answer): InstrumentError: arXiv not retried: HTTP 429 after retries earlier this run

### Exact phrase "Peres-Schlag" - arXiv API
- query: `search_query=(abs:"Peres-Schlag" OR ti:"Peres-Schlag") sortBy=submittedDate desc`
- ERROR (not a zero - the instrument did not answer): InstrumentError: arXiv not retried: HTTP 429 after retries earlier this run

### Exact phrase "Peres-Schlag" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"Peres-Schlag",to_publication_date:2026-10-04`
- result: 12 hits (showing 10, newest first)
  1. 2026-08-11 - Finite Good Witnesses for Generalized Curve Projections at the Rectifiable Endpoint - Caleb Marshall - https://doi.org/10.48550/arxiv.2608.10476
  2. 2026-07-01 - On the Peres--Schlag orthogonal projection problem and Kakeya-type sets - Guo-Dong Hong, Chong-Wei Liang, Chun‐Yen Shen - https://doi.org/10.48550/arxiv.2607.00366
  3. 2026-07-01 - Peres--Schlag's nonempty-interior problem and a shifted-product variant for product sets - Guo-Dong Hong, Chong-Wei Liang, Chun‐Yen Shen - https://doi.org/10.48550/arxiv.2607.00372
  4. 2025-10-12 - Strong exceptional parameters for the dimension of nonlinear slices - Ryan E. G. Bushling - https://doi.org/10.48550/arxiv.2510.10844
  5. 2025-03-19 - Nonempty interior of pinned distance and tree sets - Tainara Borges, Foster, Benjamin, Yumeng Ou, Eyvindur Ari Palsson - https://doi.org/10.48550/arxiv.2503.15709
  6. 2023-08-08 - Projection theorems for linear-fractional families of projections - Annina Iseli, Anton Lukyanenko - https://doi.org/10.1017/s0305004123000373
  7. 2021-12-22 - Projection theorems for linear-fractional families of projections - Anton Lukyanenko, Annina Iseli - https://doi.org/10.48550/arxiv.2112.12274
  8. 2021-07-29 - Pinned Geometric Configurations in Euclidean Space and Riemannian Manifolds - Alex Iosevich, Krystal Taylor, Ignacio Uriarte-Tuero - https://doi.org/10.3390/math9151802
  9. 2020-10-26 - On Hausdorff dimension of radial projections - Bochen Liu - https://doi.org/10.4171/rmi/1227
  10. 2019-07-04 - New Bounds on the Dimensions of Planar Distance Sets - Tamás Keleti, Pablo Shmerkin - https://doi.org/10.1007/s00039-019-00500-9

### formal-conjectures PRs "Peres-Schlag" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"Peres-Schlag"' --state all --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh pr list (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### formal-conjectures issues "Peres-Schlag" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"Peres-Schlag"' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 10`
- result: 1 hits (newest first)
- note: gh returns no total; count is rows returned
  1. 2026-09-18 - #6130 Erdős Problem 894 - Konamiu - https://github.com/google-deepmind/formal-conjectures/issues/6130 [closed]

## Prior-art log: arXiv:0706.0223 (2026-10-04 00:33 EDT)

### arXiv record: 0706.0223 - arXiv API
- query: `id_list=0706.0223`
- ERROR (not a zero - the instrument did not answer): InstrumentError: HTTP 429 from https://export.arxiv.org/api/query?id_list=0706.0223

### Forward citations of arXiv:0706.0223 - Semantic Scholar
- query: `papers followups 0706.0223`
- result: 63 hits (newest first)
- note: via `papers followups`
  1. 2026-06-27 - Maximal Gaps for Dilated Lacunary Integer Sequences - Y. Peres, Bo-Han Yang - https://arxiv.org/abs/2606.28860
  2. 2026-06-21 - Proof of the Finiteness of the Chromatic Number of Two-Dimensional Lacunary Distance Graphs - Nabh Singh - https://arxiv.org/abs/2606.22539
  3. 2026-04-20 - Near-optimal density theorems for large dilates of large point configurations - Vjekoslav Kovavc, Adian Anibal Santos Sepvci'c - https://arxiv.org/abs/2604.18544
  4. 2025-08-05 - Notes and computations on forbidden differences - C. Dean, Haley Havard, Elizabeth Hawkins, Patch Heard, Andrew Lott, Alex G. Rice - https://arxiv.org/abs/2508.03650
  5. 2025-03-26 - Local obstructions in sequences revisited - Matthieu Rosenfeld, Alexander Shen - https://arxiv.org/abs/2503.20529
  6. 2024-09-30 - The Lonely Runner Conjecture turns 60 - G. Perarnau, Oriol Serra - https://arxiv.org/abs/2409.20160
  7. 2024-06-28 - The dispersion of dilated lacunary sequences, with applications in multiplicative Diophantine approximation - Eduard Stefanescu - https://arxiv.org/abs/2406.19802
  8. 2024-06-15 - Computing Non-Repetitive Sequences with a Computable Lefthanded Local Lemma - Daniel S. Mourad - https://arxiv.org/abs/2406.10564
  9. 2024-05-08 - On Some Properties of Accessible Sets - Oscar Quester - https://arxiv.org/abs/2405.05356
  10. 2023-09-23 - Chromatic number of a line with geometric progressions of forbidden distances and the complexity of recognizing distance graphs - G. Sokolov - https://doi.org/10.2140/moscow.2023.12.247
  11. 2023-06-17 - Amending the Lonely Runner Spectrum Conjecture - Ho-Tin Fan, Alec Sun - https://arxiv.org/abs/2306.10417
  12. 2023-01-19 - On Furstenberg’s Diophantine result - D. Gayfulin, N. Moshchevitin - https://arxiv.org/abs/2301.08212
  13. 2022-10-28 - Sublacunary sequences that are strong sweeping out - Sovanlal Mondal, Madhumita Roy, M. Wierdl - https://arxiv.org/abs/2210.15894
  14. 2022 - Strong Sweeping Out Property for Non-lacunary Sequences - Sovanlal Mondal, Madhumita Roy, M. Wierdl - -
  15. 2019-12-12 - Barely lonely runners and very lonely runners: a refined approach to the Lonely Runner Problem - Noah Kravitz - https://arxiv.org/abs/1912.06034
  16. 2018-07-11 - Attacks and alignments: rooks, set partitions, and permutations - R. Arratia, S. Desalvo - https://arxiv.org/abs/1807.03926
  17. 2018-05-01 - The lonely runner problem for lacunary sequences - Sebastian Czerwinski - https://doi.org/10.1016/j.disc.2018.02.002
  18. 2017-09-11 - SOME REFINED RESULTS ON THE MIXED LITTLEWOOD CONJECTURE FOR PSEUDO-ABSOLUTE VALUES - Wen-Cai Liu - https://arxiv.org/abs/1709.03228
  19. 2017-04-28 - The Colorado Mathematical Olympiad: The Third Decade and Further Explorations - A. Soifer - https://doi.org/10.1007/978-3-319-52861-8
  20. 2017-01-30 - Fractals in Probability and Analysis - C. Bishop, Y. Peres - https://doi.org/10.1017/9781316460238
  21. 2017 - E27: Coloring Integers—Entertainment of Mathematical Kind - A. Soifer - https://doi.org/10.1007/978-3-319-52861-8_19
  22. 2016-09-06 - The probability of avoiding consecutive patterns in the Mallows distribution - Harry Crane, S. Desalvo, S. Elizalde - https://arxiv.org/abs/1609.01370
  23. 2016-06-01 - Monochromatic paths for the integers - João Guerreiro, I. Ruzsa, Manuel A. G. Silva - https://arxiv.org/abs/1606.00418
  24. 2015-09-09 - Diophantine approximations and directional discrepancy of rotated lattices - D. Bilyk, Xiao-Min Ma, J. Pipher, Craig V. Spencer - https://doi.org/10.1090/TRAN/6492
  25. 2014-07-12 - Correlation Among Runners and Some Results on the Lonely Runner Conjecture - G. Perarnau, O. Serra - https://arxiv.org/abs/1407.3381
  26. 2014-06-20 - Quantitative uniform distribution results for geometric progressions - C. Aistleitner - https://doi.org/10.1007/s11856-014-1080-5
  27. 2014-06-02 - Diophantine approximations with Pisot numbers - V. Zhuravleva - https://arxiv.org/abs/1406.0518
  28. 2014 - Around the Littlewood conjecture in Diophantine approximation - Y. Bugeaud - https://doi.org/10.5802/PMB.1
  29. 2013-12-17 - Spectral Graph Theory - Michael Doob - https://doi.org/10.1201/B16132-29
  30. 2013-08-01 - Diophantine Approximation and Coloring - A. Haynes, S. Munday - https://arxiv.org/abs/1308.0208
  31. 2013 - Coloring Distance Graphs and Graphs of Diameters - A. Raigorodskii - https://doi.org/10.1007/978-1-4614-0110-0_23
  32. 2012-12-22 - Khintchine's theorem on Chebyshev matrices - N. Moshchevitin - https://arxiv.org/abs/1212.5662
  33. 2012-10-15 - Quantitative uniform distribution results for geometric progressions - C. Aistleitner - https://arxiv.org/abs/1210.4215
  34. 2012-08-27 - A probabilistic approach to consecutive pattern avoiding in permutations - G. Perarnau - https://doi.org/10.1016/j.jcta.2013.02.004
  35. 2012-08-27 - Distribution Modulo One and Diophantine Approximation: References - Y. Bugeaud - https://doi.org/10.1017/CBO9781139017732.019
  36. 2012-08-27 - A probabilistic approach to consecutive pattern avoiding in permutations - G. Perarnau - https://arxiv.org/abs/1208.5366
  37. 2012-04-26 - On the law of the iterated logarithm for permuted lacunary sequences - C. Aistleitner, I. Berkes, R. Tichy - https://arxiv.org/abs/1311.4927
  38. 2012-04-26 - The lefthanded local lemma characterizes chordal dependency graphs - Wesley Pegden - https://arxiv.org/abs/1204.5922
  39. 2012-04-16 - Sequences with long range exclusions - K. Eloranta - https://arxiv.org/abs/1204.3439
  40. 2012-04-01 - On the law of the iterated logarithm for permuted lacunary sequences - C. Aistleitner, I. Berkes, R. Tichy - https://doi.org/10.1134/S0081543812010026
  41. 2012-03-29 - On distribution of fractional parts of linear forms - I. Rochev - https://doi.org/10.1007/s10958-012-0756-9
  42. 2012-02-21 - On some open problems in Diophantine approximation - N. Moshchevitin - https://arxiv.org/abs/1202.4539
  43. 2012-01-10 - Density modulo 1 of lacunary and sublacunary sequences: application of Peres–Schlag’s construction - N. Moshchevitin - https://doi.org/10.1007/S10958-012-0660-3
  44. 2012 - N T ] 3 0 A pr 2 01 2 On some open problems in Diophantine approximation by - N. Moshchevitin - -
  45. 2011-05-07 - On fractional parts of powers of real numbers close to 1 - Y. Bugeaud, N. Moshchevitin - https://doi.org/10.1007/s00209-011-0881-z
  46. 2011-02-26 - Nonrepetitive Sequences on Arithmetic Progressions - J. Grytczuk, Jakub Kozik, Marcin Witkowski - https://arxiv.org/abs/1102.5438
  47. 2011-01-26 - On certain Littlewood-like and Schmidt-like problems in inhomogeneous Diophantine approximations - N. Moshchevitin - https://arxiv.org/abs/1101.5032
  48. 2011 - Nonrepetitive list colourings of paths - J. Grytczuk, J. Przybylo, Xu-Ding Zhu - https://doi.org/10.1002/rsa.20347
  49. 2010-10-27 - Highly nonrepetitive sequences: Winning strategies from the local lemma - Wesley Pegden - https://arxiv.org/abs/1010.5772
  50. 2010-09-23 - On fractional parts of powers of real numbers close to 1 - Y. Bugeaud, N. Moshchevitin - https://arxiv.org/abs/1009.4528
  51. 2010-04-24 - Schmidt's conjecture and Badziahin-Pollington-Velani's theorem - N. Moshchevitin - https://arxiv.org/abs/1004.4269
  52. 2010-03-01 - Powers of Rational Numbers Modulo 1 Lying in Short Intervals - A. Dubickas - https://doi.org/10.1007/S00025-009-0001-0
  53. 2010-02-01 - On simultaneously badly approximable numbers - Nikolay G. Moshchevitin - https://doi.org/10.1112/blms/bdp107
  54. 2010 - Сингулярные диофантовы системы А. Я. Хинчина и их применение@@@Khintchine's singular Diophantine systems and their applications - Николай Германович Мощевитин, Nikolai Germanovich Moshchevitin - https://doi.org/10.4213/RM9354
  55. 2010 - Games, graphs, and geometry - Wesley Pegden - https://doi.org/10.7282/T3XP751J
  56. 2009-12-22 - Khintchine's singular Diophantine systems and their applications - N. Moshchevitin - https://arxiv.org/abs/0912.4503
  57. 2009-05-06 - Badly approximable numbers and Littlewood-type problems - Y. Bugeaud, N. Moshchevitin - https://arxiv.org/abs/0905.0830
  58. 2008-12-21 - A note on badly approximable affine forms and winning sets - N. Moshchevitin - https://arxiv.org/abs/0812.3998
  59. 2008-11-10 - On distribution of fractional parts of linear forms - I. Rochev - https://arxiv.org/abs/0811.1547
  60. 2008-05-01 - An Approximation by Lacunary Sequence of Vectors - A. Dubickas - https://doi.org/10.1017/S0963548307008899
  61. 2008 - A detailed look into two problems on lacunary sequences - Ilya Volynin - -
  62. ???? - 25 (2025) ON SOME PROPERTIES OF ACCESSIBLE SETS - Oscar Quester - -
  63. ???? - Distribution of some quadratic linear recurrence sequences modulo 1 - ? - -

### Forward citations of arXiv:0706.0223 - OpenAlex
- query: `works?filter=cites:<OpenAlex id of doi:10.48550/arXiv.0706.0223>`
- ERROR (not a zero - the instrument did not answer): InstrumentError: HTTP 404 from https://api.openalex.org/works/doi:10.48550/arXiv.0706.0223

### Newest arXiv papers by Badziahin - arXiv API
- query: `search_query=au:"Badziahin" sortBy=submittedDate desc`
- ERROR (not a zero - the instrument did not answer): InstrumentError: arXiv not retried: HTTP 429 after retries earlier this run

### Exact phrase "sublacunary" - arXiv API
- query: `search_query=(abs:"sublacunary" OR ti:"sublacunary") sortBy=submittedDate desc`
- ERROR (not a zero - the instrument did not answer): InstrumentError: arXiv not retried: HTTP 429 after retries earlier this run

### Exact phrase "sublacunary" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"sublacunary",to_publication_date:2026-10-04`
- result: 12 hits (showing 10, newest first)
  1. 2026-08-24 - Directional maximal operators in the plane - Edward Kroc, Juyoung Lee, Malabika Pramanik - https://doi.org/10.48550/arxiv.2608.23871
  2. 2022-10-28 - Sublacunary sequences that are strong sweeping out - Sovanlal Mondal, Roy, Madhumita, Μáté Wierdl - https://doi.org/10.48550/arxiv.2210.15894
  3. 2021-11-17 - Sublacunary sets and interpolation sets for nilsequences - ANH NGOC LE - https://doi.org/10.3934/dcds.2021175
  4. 2015-01-01 - Kakeya-type sets, lacunarity, and directional maximal operators in Euclidean space - Edward Kroc - https://doi.org/10.14288/1.0166114
  5. 2014-04-24 - Lacunarity, Kakeya-type sets and directional maximal operators - Edward Kroc, Malabika Pramanik - https://doi.org/10.48550/arxiv.1404.6241
  6. 2012-01-09 - Density modulo 1 of lacunary and sublacunary sequences: application of Peres–Schlag’s construction - Nikolay Moshchevitin - https://doi.org/10.1007/s10958-012-0660-3
  7. 2009-01-01 - Diophantine equations and the LIL for the discrepancy of sublacunary sequences - Christoph Aistleitner - https://doi.org/10.1215/ijm/1286212916
  8. 2007-09-21 - Density modulo 1 of sublacunary sequences: application of Peres-Schlag's arguments - Moshchevitin, Nikolai G. - https://doi.org/10.48550/arxiv.0709.3419
  9. 2005-09-01 - Sublacunary Sequences and Winning Sets - Nikolay Moshchevitin - https://doi.org/10.1007/s11006-005-0161-5
  10. 2005-05-01 - Density Modulo 1 of Sublacunary Sequences - Renat Kamilevich Akhunzhanov, Nikolay Moshchevitin - https://doi.org/10.1007/s11006-005-0075-2

### formal-conjectures PRs "sublacunary" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"sublacunary"' --state all --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh pr list (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### formal-conjectures issues "sublacunary" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"sublacunary"' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh search issues (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

## Prior-art log: Furstenberg sequence (2026-10-04 00:36 EDT)

### Newest arXiv papers by Bugeaud - arXiv API
- query: `search_query=au:"Bugeaud" AND submittedDate:[201201010000 TO 299912312359] sortBy=submittedDate desc`
- ERROR (not a zero - the instrument did not answer): InstrumentError: HTTP 503 from https://export.arxiv.org/api/query?search_query=au%3A%22Bugeaud%22+AND+submittedDate%3A%5B201201010000+TO+299912312359%5D&start=0&max_results=10&sortBy=submittedDate&sortOrder=descending

### Exact phrase "Furstenberg sequence" - arXiv API
- query: `search_query=(abs:"Furstenberg sequence" OR ti:"Furstenberg sequence") AND submittedDate:[201201010000 TO 299912312359] sortBy=submittedDate desc`
- ERROR (not a zero - the instrument did not answer): InstrumentError: arXiv not retried: HTTP 503 after retries earlier this run

### Exact phrase "Furstenberg sequence" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"Furstenberg sequence",to_publication_date:2026-10-04,from_publication_date:2012-01-01`
- result: 0 hits, instrument: OpenAlex

### formal-conjectures PRs "Furstenberg sequence" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"Furstenberg sequence" created:>=2012-01-01' --state all --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh pr list (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### formal-conjectures issues "Furstenberg sequence" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"Furstenberg sequence"' --created '>=2012-01-01' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh search issues (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### Exact phrase "non-lacunary semigroup" - arXiv API
- query: `search_query=(abs:"non-lacunary semigroup" OR ti:"non-lacunary semigroup") AND submittedDate:[201201010000 TO 299912312359] sortBy=submittedDate desc`
- ERROR (not a zero - the instrument did not answer): InstrumentError: arXiv not retried: HTTP 503 after retries earlier this run

### Exact phrase "non-lacunary semigroup" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"non-lacunary semigroup",to_publication_date:2026-10-04,from_publication_date:2012-01-01`
- result: 2 hits (newest first)
  1. 2025-07-14 - Chaotic almost minimal actions - Van Cyr, Bryna Kra, Scott Schmieding - https://doi.org/10.1090/tran/9503
  2. 2024-04-23 - Chaotic almost minimal actions - Van Cyr, Bryna Kra, Scott Schmieding - https://doi.org/10.48550/arxiv.2404.15476

### formal-conjectures PRs "non-lacunary semigroup" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"non-lacunary semigroup" created:>=2012-01-01' --state all --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh pr list (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### formal-conjectures issues "non-lacunary semigroup" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"non-lacunary semigroup"' --created '>=2012-01-01' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh search issues (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### Exact phrase "badly approximable" - arXiv API
- query: `search_query=(abs:"badly approximable" OR ti:"badly approximable") AND submittedDate:[201201010000 TO 299912312359] sortBy=submittedDate desc`
- ERROR (not a zero - the instrument did not answer): InstrumentError: arXiv not retried: HTTP 503 after retries earlier this run

### Exact phrase "badly approximable" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"badly approximable",to_publication_date:2026-10-04,from_publication_date:2012-01-01`
- result: 300 hits (showing 10, newest first)
  1. 2026-10-02 - Geometric Ratios as Generators of Hierarchical Structure: An Arithmetic Audit of π, φ, and e - Rowan Brad Quni-Gudzinas - https://doi.org/10.5281/zenodo.23097730
  2. 2026-10-02 - Geometric Ratios as Generators of Hierarchical Structure: An Arithmetic Audit of π, φ, and e - Rowan Brad Quni-Gudzinas - https://doi.org/10.5281/zenodo.23097729
  3. 2026-10-01 - Beatty First-Passage Counts: Limit Laws, Fractal Geometry, and Arithmetic Rigidity - Philippe Cochin - https://doi.org/10.5281/zenodo.23090400
  4. 2026-10-01 - Beatty First-Passage Counts: Limit Laws, Fractal Geometry, and Arithmetic Rigidity - Philippe Cochin - https://doi.org/10.5281/zenodo.23090399
  5. 2026-09-29 - Twisted Diophantine Approximation I: Asymptotic Theory - Taehyeong Kim, Vasiliy Neckrasov - https://doi.org/10.48550/arxiv.2609.36411
  6. 2026-09-18 - $\mathbf{Bad}(\mathbf{r};\mathbf{s})$ is Hyperplane Absolute Winning - Chengyang Wu - https://doi.org/10.48550/arxiv.2609.22016
  7. 2026-09-09 - A Geometric Proof of the Karpelevi\v{c} Theorem - Brecht Verbeken, Vincent Ginis - https://doi.org/10.5281/zenodo.21529143
  8. 2026-09-09 - A Geometric Proof of the Karpelevi\v{c} Theorem - Brecht Verbeken, Vincent Ginis - https://doi.org/10.5281/zenodo.22674611
  9. 2026-09-02 - The Golden Ratio's Irrationality: Slowest Convergents and Maximal Aperiodic Order — E8 Intelligence Research - Andrew Stewart Caldin - https://doi.org/10.5281/zenodo.22245479
  10. 2026-09-02 - The Golden Ratio's Irrationality: Slowest Convergents and Maximal Aperiodic Order — E8 Intelligence Research - Andrew Stewart Caldin - https://doi.org/10.5281/zenodo.22245478

### formal-conjectures PRs "badly approximable" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"badly approximable" created:>=2012-01-01' --state all --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh pr list (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### formal-conjectures issues "badly approximable" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"badly approximable"' --created '>=2012-01-01' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh search issues (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

## Prior-art log: arXiv:1512.06935 (2026-10-04 00:40 EDT)

### arXiv record: 1512.06935 - arXiv API
- query: `id_list=1512.06935`
- result: 1 hits (newest first)
- note: latest version + dates from the API entry
  1. 2015-12-22 - On the expansions of real numbers in two integer bases - Yann Bugeaud, Dong Han Kim - https://arxiv.org/abs/1512.06935 [v3 updated 2016-12-12]

### Forward citations of arXiv:1512.06935 - Semantic Scholar
- query: `papers followups 1512.06935`
- result: 1 hits (newest first)
- note: via `papers followups`
  1. 2016-09-21 - ON THE EXPANSIONS OF REAL NUMBERS IN TWO MULTIPLICATIVELY DEPENDENT BASES - Y. Bugeaud, Dong Han Kim - https://arxiv.org/abs/1609.06531

### Forward citations of arXiv:1512.06935 - OpenAlex
- query: `works?filter=cites:<OpenAlex id of doi:10.48550/arXiv.1512.06935>`
- ERROR (not a zero - the instrument did not answer): InstrumentError: HTTP 404 from https://api.openalex.org/works/doi:10.48550/arXiv.1512.06935

### Newest arXiv papers by Dong Han Kim - arXiv API
- query: `search_query=au:"Dong Han Kim" sortBy=submittedDate desc`
- result: 40 hits (showing 10, newest first)
  1. 2026-09-15 - On the number of palindromic factors of low complexity words - Dong Han Kim, Sanghoon Kwon - https://arxiv.org/abs/2609.16596 [v1 updated 2026-09-15]
  2. 2025-10-20 - On the irrationality exponent of real numbers with low complexity expansion - Yann Bugeaud, Hajime Kaneko, Dong Han Kim - https://arxiv.org/abs/2510.17177 [v3 updated 2026-03-20]
  3. 2025-10-02 - On the $b$-ary expansion of a real number whose irrationality exponent is close to 2 - Yann Bugeaud, Dong Han Kim - https://arxiv.org/abs/2510.02059 [v2 updated 2026-04-20]
  4. 2025-06-10 - On the Markoff spectrum on the Hecke group of index six - Byungchul Cha, Dong Han Kim, Deokwon Sim - https://arxiv.org/abs/2506.08358 [v2 updated 2026-01-22]
  5. 2025-04-09 - Exponential Sums by Irrationality Exponent - Byungchul Cha, Dong Han Kim - https://arxiv.org/abs/2504.06726 [v2 updated 2025-04-18]
  6. 2025-03-24 - Uniform Diophantine approximation on the Hecke group $\mathbf H_4$ - Ayreena Bakhtawar, Dong Han Kim, Seul Bee Lee - https://arxiv.org/abs/2503.18517 [v1 updated 2025-03-24]
  7. 2024-03-19 - Diophantine approximation by rational numbers of certain parity types - Dong Han Kim, Seul Bee Lee, Lingmin Liao - https://arxiv.org/abs/2403.12341 [v1 updated 2024-03-19]
  8. 2022-09-02 - Intrinsic Diophantine approximation on circles and spheres - Byungchul Cha, Dong Han Kim - https://arxiv.org/abs/2209.00848 [v2 updated 2023-08-31]
  9. 2022-06-11 - The Markoff and Lagrange spectra on the Hecke group H4 - Dong Han Kim, Deokwon Sim - https://arxiv.org/abs/2206.05441 [v7 updated 2026-02-11]
  10. 2020-09-22 - On the multiple recurrence properties for disjoint systems - Michihiro Hirayama, Dong Han Kim, Younghwan Son - https://arxiv.org/abs/2009.10566 [v2 updated 2021-07-23]

### Exact phrase "digit changes" - arXiv API
- query: `search_query=(abs:"digit changes" OR ti:"digit changes") sortBy=submittedDate desc`
- result: 6 hits (newest first)
  1. 2022-03-29 - Accurate electronic properties and intercalation voltages of olivine-type Li-ion cathode materials from extended Hubbard functionals - Iurii Timrov, Francesco Aquilante, Matteo Cococcioni, Nicola Marzari - https://arxiv.org/abs/2203.15732 [v2 updated 2022-11-02]
  2. 2021-04-28 - The Future of Employment Revisited: How Model Selection Determines Automation Forecasts - Fabian Stephany, Hanno Lorenz - https://arxiv.org/abs/2104.13747 [v1 updated 2021-04-28]
  3. 2019-08-20 - 360-Degree Textures of People in Clothing from a Single Image - Verica Lazova, Eldar Insafutdinov, Gerard Pons-Moll - https://arxiv.org/abs/1908.07117 [v1 updated 2019-08-20]
  4. 2015-10-12 - Digitally delicate primes - Jackson Hopper, Paul Pollack - https://arxiv.org/abs/1510.03401 [v2 updated 2015-10-13]
  5. 2007-09-11 - On two notions of complexity of algebraic numbers - Yann Bugeaud, Jan-Hendrik Evertse - https://arxiv.org/abs/0709.1560 [v1 updated 2007-09-11]
  6. 1998-05-20 - Noise-induced Input Dependence in a Convective Unstable Dynamical System - Koichi Fujimoto, Kunihiko Kaneko - https://arxiv.org/abs/chao-dyn/9805017 [v1 updated 1998-05-20]

### Exact phrase "digit changes" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"digit changes",to_publication_date:2026-10-04`
- result: 32 hits (showing 10, newest first)
  1. 2026-10-01 - When Digits Change: Binary Representation and the Arithmetic Beneath It - Bill Widi - https://doi.org/10.5281/zenodo.23089571
  2. 2026-10-01 - When Digits Change: Binary Representation and the Arithmetic Beneath It - Bill Widi - https://doi.org/10.5281/zenodo.23089572
  3. 2026-08-27 - Exact Carry-Propagation Distributions and Boundary Reconstruction in Canonical Beta Numeration - Paul Higham - https://doi.org/10.5281/zenodo.22123483
  4. 2026-08-27 - Exact Carry-Propagation Distributions and Boundary Reconstruction in Canonical Beta Numeration - Paul Higham - https://doi.org/10.5281/zenodo.22123482
  5. 2026-04-11 - Degeneration and adaptive evolution of digits in ratite birds - Wen Kang, Günter P. Wagner, Qi Zhou - https://doi.org/10.1093/molbev/msag101
  6. 2026-03-24 - Dual-options pseudo-random deviation-based image steganography - Yusuf Muhammad Zaki, Adifa Widyadhani Chanda D’Layla, Tohari Ahmad - https://doi.org/10.1016/j.rineng.2026.110201
  7. 2026-03-09 - Closed-Loop Temperature-Controlled Power Cycling for Accelerated Degradation Monitoring of GaN Devices - Wing Tai Leung, Yushi Wang, Mattew Appleby, Qilei Wang, Saeed Jahdi, Zhengyang Feng et al. - https://doi.org/10.1109/tpel.2026.3671968
  8. 2025-12-15 - The left-digit defending effect: a replication with extension of the left‑digit effect to spending intentions based on resources - Na Hea Park, Chan Jean Lee - https://doi.org/10.1007/s11002-025-09808-z
  9. 2025-11-26 - How Categorization Shapes the Probability Weighting Function - Dan R. Schley, Alina Ferecatu, Hang‐Yee Chan, Manissa P. Gunadi - https://doi.org/10.31234/osf.io/rufp7_v1
  10. 2025-09-10 - Round Number Preferences and Left-Digit Bias: Evidence from Credit Card Repayments - Hiroaki Sakaguchi, John Gathergood, Neil Stewart - https://doi.org/10.1287/mnsc.2020.01995

### formal-conjectures PRs "digit changes" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"digit changes"' --state all --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh pr list (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### formal-conjectures issues "digit changes" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"digit changes"' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh search issues (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### Exact phrase "two multiplicatively independent bases" - arXiv API
- query: `search_query=(abs:"two multiplicatively independent bases" OR ti:"two multiplicatively independent bases") sortBy=submittedDate desc`
- result: 2 hits (newest first)
  1. 2026-08-14 - Ratio of sum of digits functions in two bases - Pascal Jelinek - https://arxiv.org/abs/2608.14241 [v2 updated 2026-08-27]
  2. 2017-10-19 - A density version of Cobham's theorem - Jakub Byszewski, Jakub Konieczny - https://arxiv.org/abs/1710.07261 [v2 updated 2017-11-01]

### Exact phrase "two multiplicatively independent bases" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"two multiplicatively independent bases",to_publication_date:2026-10-04`
- result: 5 hits (newest first)
  1. 2026-08-14 - Ratio of sum of digits functions in two bases - Pascal Jelinek - https://doi.org/10.48550/arxiv.2608.14241
  2. 2026-03-29 - The Geometric Sieve for Artin's Conjecture: Multi-Base Energy Inequalities, the Index Moment Obstruction, and the Spectral Bound on Non-Primitive-Root Density - K. Fathi - https://doi.org/10.5281/zenodo.19315487
  3. 2019-11-08 - A density version of Cobham’s theorem - Jakub Byszewski, Jakub Konieczny - https://doi.org/10.4064/aa180626-13-1
  4. 2012-10-14 - On the expansions of a real number to several integer bases - Yann Bugeaud - https://doi.org/10.4171/rmi/697
  5. 2011-03-04 - An analogue of Cobham’s theorem for fractals - Boris Adamczewski, Jason P. Bell - https://doi.org/10.1090/s0002-9947-2011-05357-2

### formal-conjectures PRs "two multiplicatively independent bases" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"two multiplicatively independent bases"' --state all --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh pr list (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### formal-conjectures issues "two multiplicatively independent bases" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"two multiplicatively independent bases"' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh search issues (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

## Prior-art log: Stoneham (2026-10-04 00:43 EDT)

### Newest arXiv papers by David H. Bailey - arXiv API
- query: `search_query=au:"David H. Bailey" sortBy=submittedDate desc`
- result: 8 hits (newest first)
  1. 2026-04-01 - General formulas for a class of Euler sums - David H Bailey, Ross McPhedran, Bruno Salvy - https://arxiv.org/abs/2604.02384 [v1 updated 2026-04-01]
  2. 2023-11-05 - New Results for Euler Sums - Ross C. McPhedran, David H. Bailey - https://arxiv.org/abs/2311.06294 [v5 updated 2026-06-28]
  3. 2011-08-30 - Dimension Reduction Using Rule Ensemble Machine Learning Methods: A Numerical Study of Three Ensemble Methods - Orianna DeMasi, Juan Meza, David H. Bailey - https://arxiv.org/abs/1108.6094 [v1 updated 2011-08-30]
  4. 2010-05-03 - Experimental Mathematics and Mathematical Physics - David H. Bailey, Jonathan M. Borwein, David Broadhurst, Wadim Zudilin - https://arxiv.org/abs/1005.0414 [v1 updated 2010-05-03]
  5. 2008-01-06 - Elliptic integral evaluations of Bessel moments - David H. Bailey, Jonathan M. Borwein, David Broadhurst, M. L. Glasser - https://arxiv.org/abs/0801.0891 [v2 updated 2008-02-08]
  6. 2005-05-12 - Experimental determination of Apery-like identities for zeta(2n+2) - David H. Bailey, Jonathan M. Borwein, David M. Bradley - https://arxiv.org/abs/math/0505270 [v2 updated 2006-10-18]
  7. 1999-06-20 - A seventeenth-order polylogarithm ladder - David H. Bailey, David J. Broadhurst - https://arxiv.org/abs/math/9906134 [v1 updated 1999-06-20]
  8. 1999-05-09 - Parallel Integer Relation Detection: Techniques and Applications - David H. Bailey, David J. Broadhurst - https://arxiv.org/abs/math/9905048 [v1 updated 1999-05-09]

### Exact phrase "Stoneham" - arXiv API
- query: `search_query=(abs:"Stoneham" OR ti:"Stoneham") sortBy=submittedDate desc`
- result: 7 hits (newest first)
  1. 2026-09-16 - Unified Transport and Susceptibility Analysis of a Thin BSCCO Film: From Local Pairing to Global Phase Coherence - Santu Prasad Jana, Bismaya Ranjan Nayak, Sohini Guin, Akshay Naik, Dhavala Suri, Arindam Ghosh - https://arxiv.org/abs/2609.19303 [v2 updated 2026-09-24]
  2. 2018-03-14 - Some negative results related to Poissonian pair correlation problems - Gerhard Larcher, Wolfgang Stockinger - https://arxiv.org/abs/1803.05236 [v2 updated 2018-03-19]
  3. 2014-12-23 - Physical constraints for the Stoneham model for light-dependent magnetoreception - Jofre Espigulé-Pons, Christoph Goetz, Alipasha Vaziri, Markus Arndt - https://arxiv.org/abs/1412.7369 [v1 updated 2014-12-23]
  4. 2012-12-14 - An arithmetical excursion via Stoneham numbers - Michael Coons - https://arxiv.org/abs/1212.3449 [v2 updated 2013-11-28]
  5. 2011-05-28 - Quantum theory of hydrogen key of point mutation in DNA - E. K. Ivanova, N. N. Turaeva, B. L. Oksengendler - https://arxiv.org/abs/1105.6282 [v1 updated 2011-05-28]
  6. 1997-04-22 - Magnetic Photon Splitting: Computations of Proper-time Rates and Spectra - Matthew G. Baring, Alice K. Harding - https://arxiv.org/abs/astro-ph/9704210 [v1 updated 1997-04-22]
  7. 1996-05-06 - Photon Splitting in a Strong Magnetic Field: Recalculation and Comparison With Previous Calculations - Stephen L. Adler, Christian Schubert - https://arxiv.org/abs/hep-th/9605035 [v1 updated 1996-05-06]

### Exact phrase "Stoneham" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"Stoneham",to_publication_date:2026-10-04`
- result: 852 hits (showing 10, newest first)
  1. 2026-09-16 - Unified Transport and Susceptibility Analysis of a Thin BSCCO Film: From Local Pairing to Global Phase Coherence - Santu Prasad Jana, Bismaya Ranjan Nayak, Sohini Guin, Akshay K. Naik, Dhavala Suri, Arindam Ghosh - https://doi.org/10.48550/arxiv.2609.19303
  2. 2026-08-14 - Evaluation at South Stoneham House - Michael Smith - https://doi.org/10.5284/1145482
  3. 2026-08-14 - Watching Brief at South Stoneham House Archaeological watching brief on removal of existing building foundations - Michael Smith - https://doi.org/10.5284/1145483
  4. 2026-07-25 - A Water Quality Modeling Framework to Quantify Seasonal Contributions of Nitrogen and Phosphorus Loads to a Rural–Urban Watershed Given Limited Observations - Yegane Khoshkalam, Ralph D. Tasing Kouom, Alain N. Rousseau, Paul Célicourt - https://doi.org/10.1007/s11270-026-09775-9
  5. 2026-07-04 - Maine’s Finest Topaz Crystals, Lord Hill, Stoneham, Oxford County - Myles M. Felch, Carl A. Francis - https://doi.org/10.1080/00357529.2026.2645527
  6. 2026-05-28 - Hydre Médiante v7.2.1 : cartographie diophantienne des résonances entre cryptographie et théorie des nombres - Antoine Couet, Moonshot AI / Kimi K 2.6 Thinking - https://doi.org/10.5281/zenodo.20421960
  7. 2026-05-28 - Hydre Médiante v7.2.1 : cartographie diophantienne des résonances entre cryptographie et théorie des nombres - Antoine Couet, Moonshot AI / Kimi K 2.6 Thinking - https://doi.org/10.5281/zenodo.20421961
  8. 2026-02-17 - The erosion of trust: How do we find our way back? - Payam Vali - https://doi.org/10.1038/s41372-026-02588-y
  9. 2026-02-11 - George Berkeley and the Activity of Finite Spirits - Benjamin Quinn Formanek - https://openalex.org/W7205637711
  10. 2026-01-09 - Agromyza pallidiseta Malloch - Charles S. Eiseman, Owen Lonsdale, Tracy S. Feldman, John Van Der Linden - https://doi.org/10.5281/zenodo.20489144

### formal-conjectures PRs "Stoneham" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"Stoneham"' --state all --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh pr list (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### formal-conjectures issues "Stoneham" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"Stoneham"' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh search issues (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### Exact phrase "Stoneham constant" - arXiv API
- query: `search_query=(abs:"Stoneham constant" OR ti:"Stoneham constant") sortBy=submittedDate desc`
- result: 0 hits, instrument: arXiv API

### Exact phrase "Stoneham constant" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"Stoneham constant",to_publication_date:2026-10-04`
- result: 0 hits, instrument: OpenAlex

### formal-conjectures PRs "Stoneham constant" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"Stoneham constant"' --state all --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh pr list (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### formal-conjectures issues "Stoneham constant" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"Stoneham constant"' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh search issues (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### Exact phrase "Stoneham number" - arXiv API
- query: `search_query=(abs:"Stoneham number" OR ti:"Stoneham number") sortBy=submittedDate desc`
- result: 2 hits (newest first)
  1. 2018-03-14 - Some negative results related to Poissonian pair correlation problems - Gerhard Larcher, Wolfgang Stockinger - https://arxiv.org/abs/1803.05236 [v2 updated 2018-03-19]
  2. 2012-12-14 - An arithmetical excursion via Stoneham numbers - Michael Coons - https://arxiv.org/abs/1212.3449 [v2 updated 2013-11-28]

### Exact phrase "Stoneham number" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"Stoneham number",to_publication_date:2026-10-04`
- result: 1 hits (newest first)
  1. 2019-10-10 - Some negative results related to Poissonian pair correlation problems - Gerhard Larcher, Wolfgang Stockinger - https://doi.org/10.1016/j.disc.2019.111656

### formal-conjectures PRs "Stoneham number" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"Stoneham number"' --state all --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh pr list (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### formal-conjectures issues "Stoneham number" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"Stoneham number"' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh search issues (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

## Prior-art log: linear forms in logarithms (2026-10-04 00:43 EDT)

### Newest arXiv papers by Becher - arXiv API
- query: `search_query=au:"Becher" AND submittedDate:[201501010000 TO 299912312359] sortBy=submittedDate desc`
- result: 200 hits (showing 10, newest first)
  1. 2026-09-28 - Resummation of Next-to-Leading Non-Global Logarithms in Higgs Production - Thomas Becher, Rebecca von Kuk, Xinyu Qin, Nicolas Schalch - https://arxiv.org/abs/2609.35972 [v1 updated 2026-09-28]
  2. 2026-09-22 - An asymmetric atom-photon architecture for device-independent quantum key distribution over 25 km - Jonas Meiers, Christian Haen, Max Bergerhoff, Pascal Baumgart, Tobias Bauer, Christoph Becher et al. - https://arxiv.org/abs/2609.25795 [v2 updated 2026-09-23]
  3. 2026-09-08 - Two-Loop Anomalous Dimension for Non-Global and Clustering Logarithms - Thomas Becher, Jürg Haag, Nicolas Schalch - https://arxiv.org/abs/2609.09104 [v1 updated 2026-09-08]
  4. 2026-08-12 - LIGO A$^\sharp$: Detector Design and Science Prospects Beyond A+ - L. Sun, K. Kuns, B. J. J. Slagmolen, P. Fritschel, P. Schmidt, B. T. Lantz et al. - https://arxiv.org/abs/2608.11673 [v1 updated 2026-08-12]
  5. 2026-07-31 - Telecom-compatible polarization-to-time-bin conversion of atom-photon entanglement for heterogeneous quantum networks - Christian Haen, Julian Groß-Funk, Max Bergerhoff, Pascal Baumgart, Jonas Meiers, Tobias Bauer et al. - https://arxiv.org/abs/2607.29609 [v1 updated 2026-07-31]
  6. 2026-07-24 - Highly indistinguishable photons from a tin-vacancy spin qubit in diamond - Dennis Herrmann, Robert Morsch-Golsong, Tobias Bauer, Marlon Schäfer, David Lindler, Linus Ehre et al. - https://arxiv.org/abs/2607.22439 [v1 updated 2026-07-24]
  7. 2026-07-07 - Normal numbers in sparse Cantor sets - Verónica Becher, Simón Lew Deveali - https://arxiv.org/abs/2607.06773 [v1 updated 2026-07-07]
  8. 2026-06-25 - GPU-accelerated superiorization on constrained physical problems with SupPy - Tobias Becher, Yair Censor, Kay Barshad, Niklas Wahl - https://arxiv.org/abs/2606.27086 [v1 updated 2026-06-25]
  9. 2026-06-10 - Quantum repeater segment with free-space coupled co-trapped ions using telecom photon interference - Max Bergerhoff, Pascal Baumgart, Christian Haen, Jonas Meiers, Tobias Bauer, Jonas Haferkamp et al. - https://arxiv.org/abs/2606.12313 [v1 updated 2026-06-10]
  10. 2026-05-25 - Brownian Convergence of Planar Domains and Stability of the Planar Skorokhod Embedding Problem - Maher Boudabra, Mrabet Becher, Fathi Haggui - https://arxiv.org/abs/2605.25762 [v1 updated 2026-05-25]

### Exact phrase "linear forms in logarithms" - arXiv API
- query: `search_query=(abs:"linear forms in logarithms" OR ti:"linear forms in logarithms") AND submittedDate:[201501010000 TO 299912312359] sortBy=submittedDate desc`
- result: 81 hits (showing 10, newest first)
  1. 2026-09-09 - Pencils of norm form equations and a conjecture of Thomas, II - Francesco Amoroso, David Masser, Umberto Zannier - https://arxiv.org/abs/2609.09995 [v1 updated 2026-09-09]
  2. 2026-08-05 - Powers as Fibonacci Sums - Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel, Pagdame Tiebekabe - https://arxiv.org/abs/2608.04445 [v1 updated 2026-08-05]
  3. 2026-07-28 - On certain $D(9)$ and $D(64)$ Diophantine triples - Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel - https://arxiv.org/abs/2607.25168 [v1 updated 2026-07-28]
  4. 2026-07-22 - On a Diophantine Equation with Jacobsthal and Fibonacci Numbers - Daeyeoul Kim, Zekiye Pinar Cihan, Zeynep Demirkol Ozkaya, Ilker Inam - https://arxiv.org/abs/2607.20763 [v1 updated 2026-07-22]
  5. 2026-06-26 - Perfect powers in sequences of polygonal numbers - Andrzej Dąbrowski, Salah Eddine Rihane, Gökhan Soydan, Paul M. Voutier - https://arxiv.org/abs/2606.28227 [v1 updated 2026-06-26]
  6. 2026-06-26 - Large common values of generalized Ankeny-Brauer-Chowla recurrences - Armand Noubissie, Robert F. Tichy - https://arxiv.org/abs/2606.27885 [v1 updated 2026-06-26]
  7. 2026-06-18 - On common values of $F_n$ and Nathanson's totient function $Φ(m)$ - Sagar Mandal - https://arxiv.org/abs/2606.24908 [v1 updated 2026-06-18]
  8. 2026-06-16 - On the Diophantine Inequality $\lvert x^{2} - 2^{a}\cdot 3^{b}\rvert < 3\max\{a,b\}$ - Banu İrez Aydın, Herbert Batte, İlker İnam, Florian Luca, Zeynep Demirkol Özkaya - https://arxiv.org/abs/2606.18500 [v1 updated 2026-06-16]
  9. 2026-05-18 - Sum of consecutive powers as a perfect power - Angelos Koutsianas, Nikos Tzanakis - https://arxiv.org/abs/2605.18348 [v1 updated 2026-05-18]
  10. 2026-05-17 - Multiplicative independence in the sequence of $k$-generalized Pell numbers - Cherif B. Deme, Kancou D. Fall, Khady Faye, Bernadette Faye - https://arxiv.org/abs/2605.17699 [v2 updated 2026-09-17]

### Exact phrase "linear forms in logarithms" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"linear forms in logarithms",to_publication_date:2026-10-04,from_publication_date:2015-01-01`
- result: 336 hits (showing 10, newest first)
  1. 2026-10-02 - ykelanemer/goldbach-fixedpoint-framework: better reference for Baker lower bounds - ykelanemer - https://doi.org/10.5281/zenodo.21712619
  2. 2026-10-02 - ykelanemer/goldbach-fixedpoint-framework: better reference for Baker lower bounds - ykelanemer - https://doi.org/10.5281/zenodo.23092954
  3. 2026-09-29 - On the Convergence of the 3x + 1 Sequences - Minh Phuong Huynh Nguyen - https://doi.org/10.5281/zenodo.23039458
  4. 2026-09-29 - On the Convergence of the 3x + 1 Sequences - Minh Phuong Huynh Nguyen - https://doi.org/10.5281/zenodo.23039457
  5. 2026-09-27 - A power saving in natural density for generalized Collatz maps - Hiroyuki Nashida - https://doi.org/10.5281/zenodo.22986677
  6. 2026-09-27 - A power saving in natural density for generalized Collatz maps - Hiroyuki Nashida - https://doi.org/10.5281/zenodo.22986678
  7. 2026-09-26 - The Generalized Beal Conjecture: Directed Arithmetic Geometry, Fermat–Catalan Hyperbolic Rigidity, and the Complete Classification of Primitive Power Sums - August Tudor - https://doi.org/10.5281/zenodo.22968502
  8. 2026-09-26 - An effective finiteness theorem for an exceptional set of Erdős and Selfridge - Haoyu Chen - https://doi.org/10.5281/zenodo.22962743
  9. 2026-09-26 - The Generalized Beal Conjecture: Directed Arithmetic Geometry, Fermat–Catalan Hyperbolic Rigidity, and the Complete Classification of Primitive Power Sums - August Tudor - https://doi.org/10.5281/zenodo.22968501
  10. 2026-09-26 - An effective finiteness theorem for an exceptional set of Erdős and Selfridge - Haoyu Chen - https://doi.org/10.5281/zenodo.22980220

### formal-conjectures PRs "linear forms in logarithms" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"linear forms in logarithms" created:>=2015-01-01' --state all --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh pr list (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### formal-conjectures issues "linear forms in logarithms" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"linear forms in logarithms"' --created '>=2015-01-01' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh search issues (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### Exact phrase "normal number" - arXiv API
- query: `search_query=(abs:"normal number" OR ti:"normal number") AND submittedDate:[201501010000 TO 299912312359] sortBy=submittedDate desc`
- result: 122 hits (showing 10, newest first)
  1. 2026-09-21 - On Normality Preserving Operations - Chokri Manai - https://arxiv.org/abs/2609.24665 [v1 updated 2026-09-21]
  2. 2026-08-16 - On the Hausdorff dimension of the difference sets between typical and normal numbers - Bill Mance, Jakub Tomaszewski - https://arxiv.org/abs/2608.15866 [v1 updated 2026-08-16]
  3. 2026-08-08 - Random Bernoulli measures in a random environment - Changhao Chen, Zhi Liu - https://arxiv.org/abs/2608.07883 [v1 updated 2026-08-08]
  4. 2026-07-07 - Normal numbers in sparse Cantor sets - Verónica Becher, Simón Lew Deveali - https://arxiv.org/abs/2607.06773 [v1 updated 2026-07-07]
  5. 2026-06-22 - The Expected Number of Pairwise Stable Networks - P. Jean-Jacques Herings, Christian Seel, Arkadi Predtetchinski - https://arxiv.org/abs/2606.23440 [v1 updated 2026-06-22]
  6. 2026-03-04 - Abelian-normal decimal expansions - John M. Campbell - https://arxiv.org/abs/2603.04396 [v2 updated 2026-08-21]
  7. 2026-02-01 - On Normality and Equidistribution for Separator Enumerators - Subin Pulari - https://arxiv.org/abs/2602.01199 [v2 updated 2026-02-03]
  8. 2026-01-15 - Distribution of particles near the front in supercritical branching Brownian motion with compactly supported branching - Pratima Hebbar, Leonid Koralov - https://arxiv.org/abs/2601.10833 [v1 updated 2026-01-15]
  9. 2026-01-06 - On Constructions of full-dimensional absolutely normal sets of uniqueness - Chun-Kit Lai, Yu-Hao Xie - https://arxiv.org/abs/2601.03402 [v1 updated 2026-01-06]
  10. 2025-12-16 - Concentration of the truncated variation of fractional Brownian motions of any Hurst index, their $1/H$-variations and local times - Witold M. Bednorz, Rafał M. Łochowski - https://arxiv.org/abs/2512.14021 [v1 updated 2025-12-16]

### Exact phrase "normal number" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"normal number",to_publication_date:2026-10-04,from_publication_date:2015-01-01`
- result: 617 hits (showing 10, newest first)
  1. 2026-09-20 - What Numbers Can Say About "Does 777 Occur in π" Is That the Waiting Time Is Set by the Word's Self-Overlap ── in the decimals of π, 777 first occurs at digit 1589, its expected waiting time is 1110, and that of 123 is 1000; the mean first occurrence of the 1000 three-digit words is 991.994000 against an expected mean of 1002, indistinguishable from random digits ── the separator is whether the word overlaps itself or not ── [Paper 1032] - Yuuki Yamagishi - https://doi.org/10.5281/zenodo.22860519
  2. 2026-09-20 - What Numbers Can Say About "Does 777 Occur in π" Is That the Waiting Time Is Set by the Word's Self-Overlap ── in the decimals of π, 777 first occurs at digit 1589, its expected waiting time is 1110, and that of 123 is 1000; the mean first occurrence of the 1000 three-digit words is 991.994000 against an expected mean of 1002, indistinguishable from random digits ── the separator is whether the word overlaps itself or not ── [Paper 1032] - Yuuki Yamagishi - https://doi.org/10.5281/zenodo.22860520
  3. 2026-09-15 - Exhaustive Verification of the Normal Number Conjecture: 7 Billion Phone Numbers in the First Trillion Digits of π and e - Ming Jie Zhang - https://doi.org/10.5281/zenodo.22774606
  4. 2026-09-15 - Exhaustive Verification of the Normal Number Conjecture: 7 Billion Phone Numbers in the First Trillion Digits of π and e - Ming Jie Zhang - https://doi.org/10.5281/zenodo.22774607
  5. 2026-09-11 - The Uncomputable Coin Flip: Chaitin's Omega as Algorithmic Randomness — E8 Intelligence Research - Andrew Stewart Caldin - https://doi.org/10.5281/zenodo.22701702
  6. 2026-09-11 - The Uncomputable Coin Flip: Chaitin's Omega as Algorithmic Randomness — E8 Intelligence Research - Andrew Stewart Caldin - https://doi.org/10.5281/zenodo.22701703
  7. 2026-09-04 - An Exact Closed-Form Measure for k-Digit Prefix Coincidence in Fractional Scaling Maps - Keith Ramon Vasquez (Independent Researcher) - https://doi.org/10.5281/zenodo.22299517
  8. 2026-09-04 - An Exact Closed-Form Measure for k-Digit Prefix Coincidence in Fractional Scaling Maps - Keith Ramon Vasquez (Independent Researcher) - https://doi.org/10.5281/zenodo.22299518
  9. 2026-08-25 - Kolmogorov Complexity Defines Randomness as Incompressibility, Not Geometry — E8 Intelligence Research - Andrew Stewart Caldin - https://doi.org/10.5281/zenodo.22090342
  10. 2026-08-25 - Kolmogorov Complexity Defines Randomness as Incompressibility, Not Geometry — E8 Intelligence Research - Andrew Stewart Caldin - https://doi.org/10.5281/zenodo.22090343

### formal-conjectures PRs "normal number" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"normal number" created:>=2015-01-01' --state all --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh pr list (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### formal-conjectures issues "normal number" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"normal number"' --created '>=2015-01-01' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 10`
- result: 2 hits (newest first)
- note: gh returns no total; count is rows returned
  1. 2026-02-10 - #2256 Normality of Irrational Algebraic Numbers - franzhusch - https://github.com/google-deepmind/formal-conjectures/issues/2256 [closed]
  2. 2026-02-10 - #2255 Normality of π - franzhusch - https://github.com/google-deepmind/formal-conjectures/issues/2255 [closed]

## Prior-art log: arXiv:2301.08212 (2026-10-04 00:59 EDT)

### arXiv record: 2301.08212 - arXiv API
- query: `id_list=2301.08212`
- result: 1 hits (newest first)
- note: latest version + dates from the API entry
  1. 2023-01-19 - On Furstenberg's Diophantine result - Dmitry Gayfulin, Nikolay Moshchevitin - https://arxiv.org/abs/2301.08212 [v2 updated 2023-04-26]

### Forward citations of arXiv:2301.08212 - Semantic Scholar
- query: `papers followups 2301.08212`
- result: 1 hits (newest first)
- note: via `papers followups`
  1. 2026-04-20 - Near-optimal density theorems for large dilates of large point configurations - Vjekoslav Kovavc, Adian Anibal Santos Sepvci'c - https://arxiv.org/abs/2604.18544

### Forward citations of arXiv:2301.08212 - OpenAlex
- query: `works?filter=cites:<OpenAlex id of doi:10.48550/arXiv.2301.08212>`
- ERROR (not a zero - the instrument did not answer): InstrumentError: HTTP 404 from https://api.openalex.org/works/doi:10.48550/arXiv.2301.08212

### Newest arXiv papers by Moshchevitin - arXiv API
- query: `search_query=au:"Moshchevitin" sortBy=submittedDate desc`
- result: 78 hits (showing 10, newest first)
  1. 2026-07-28 - Brjuno condition through best approximations and the linearization problem - Nicolas Chevallier, João Lopes Dias, José Pedro Gaivão, Antoine Marnat, Nikolay Moshchevitin - https://arxiv.org/abs/2607.25610 [v1 updated 2026-07-28]
  2. 2026-07-05 - On the number of perfect positive definite quadratic forms - Nikolay Moshchevitin - https://arxiv.org/abs/2607.04239 [v1 updated 2026-07-05]
  3. 2026-05-25 - A note on uniform version of Littlewood inequality and Fibonacci numbers - Nikolay Moshchevitin - https://arxiv.org/abs/2605.26188 [v1 updated 2026-05-25]
  4. 2026-03-26 - Weak approximations, Diophantine exponents and two-dimensional lattices - Nikolay Moshchevitin - https://arxiv.org/abs/2603.25071 [v1 updated 2026-03-26]
  5. 2025-12-31 - On Diophantine exponents of lattices - Nikolay Moshchevitin - https://arxiv.org/abs/2512.24913 [v1 updated 2025-12-31]
  6. 2025-09-30 - A note on general isolation result in Diophantine Approximation - Sergei Pitcyn, Nikolay Moshchevitin - https://arxiv.org/abs/2509.25628 [v3 updated 2025-10-15]
  7. 2025-05-21 - Bad approximability, bounded ratios and Diophantine exponents - Antoine Marnat, Nikolay Moshchevitin, Johannes Schleischitz - https://arxiv.org/abs/2505.15964 [v3 updated 2026-07-21]
  8. 2025-03-27 - Metric theory of inhomogeneous Diophantine approximations with a fixed matrix - Nikolay Moshchevitin, Vasiliy Neckrasov - https://arxiv.org/abs/2503.21180 [v3 updated 2025-11-15]
  9. 2024-09-23 - Singularity, weighted uniform approximation, intersections and rates - Dmitry Kleinbock, Nikolay Moshchevitin, Jacqueline Warren, Barak Weiss - https://arxiv.org/abs/2409.15607 [v4 updated 2025-08-22]
  10. 2024-08-12 - Dirichlet improvability in $L_p$-norms - Nikolay Moshchevitin, Nikita Shulga - https://arxiv.org/abs/2408.06200 [v3 updated 2026-06-22]

### Exact phrase "Furstenberg's Diophantine" - arXiv API
- query: `search_query=(abs:"Furstenberg's Diophantine" OR ti:"Furstenberg's Diophantine") sortBy=submittedDate desc`
- result: 2 hits (newest first)
  1. 2023-01-19 - On Furstenberg's Diophantine result - Dmitry Gayfulin, Nikolay Moshchevitin - https://arxiv.org/abs/2301.08212 [v2 updated 2023-04-26]
  2. 2016-07-03 - Generalizations of Furstenberg's Diophantine result - Asaf Katz - https://arxiv.org/abs/1607.00670 [v1 updated 2016-07-03]

### Exact phrase "Furstenberg's Diophantine" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"Furstenberg's Diophantine",to_publication_date:2026-10-04`
- result: 1 hits (newest first)
  1. 1994-09-01 - Elementary Proof of Furstenberg's Diophantine Result - Michael Boshernitzan - https://doi.org/10.2307/2160842

### formal-conjectures PRs "Furstenberg's Diophantine" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"Furstenberg'"'"'s Diophantine"' --state all --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh pr list (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### formal-conjectures issues "Furstenberg's Diophantine" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"Furstenberg'"'"'s Diophantine"' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh search issues (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

## Prior-art log: Cantor-winning (2026-10-04 00:59 EDT)

### Newest arXiv papers by Bugeaud - arXiv API
- query: `search_query=au:"Bugeaud" AND submittedDate:[202001010000 TO 299912312359] sortBy=submittedDate desc`
- result: 30 hits (showing 10, newest first)
  1. 2026-09-24 - Refinements of Peck's theorem on simultaneous approximation to algebraic numbers - Yann Bugeaud, Bernard de Mathan - https://arxiv.org/abs/2609.29360 [v1 updated 2026-09-24]
  2. 2026-08-24 - On the binary representation of powers of $3$ - Yann Bugeaud - https://arxiv.org/abs/2608.23017 [v1 updated 2026-08-24]
  3. 2026-04-30 - On the difference between perfect powers and integral $S$-units - Yann Bugeaud - https://arxiv.org/abs/2604.27490 [v1 updated 2026-04-30]
  4. 2025-12-02 - Remarks on uniform recurrence properties for beta-transformation - Yann Bugeaud - https://arxiv.org/abs/2512.02620 [v1 updated 2025-12-02]
  5. 2025-10-20 - On the irrationality exponent of real numbers with low complexity expansion - Yann Bugeaud, Hajime Kaneko, Dong Han Kim - https://arxiv.org/abs/2510.17177 [v3 updated 2026-03-20]
  6. 2025-10-02 - On the $b$-ary expansion of a real number whose irrationality exponent is close to 2 - Yann Bugeaud, Dong Han Kim - https://arxiv.org/abs/2510.02059 [v2 updated 2026-04-20]
  7. 2025-07-22 - Simultaneous multiplicative rational approximation to a real and a $p$-adic numbers - Yann Bugeaud, Bernard de Mathan - https://arxiv.org/abs/2507.16503 [v1 updated 2025-07-22]
  8. 2025-03-28 - On the difference between squares and integral $S$-units - Yann Bugeaud - https://arxiv.org/abs/2503.22084 [v2 updated 2025-04-23]
  9. 2024-11-14 - Effective approximation to complex algebraic numbers by quadratic numbers - Prajeet Bajpai, Yann Bugeaud - https://arxiv.org/abs/2411.09570 [v1 updated 2024-11-14]
  10. 2023-10-15 - Explicit bounds for the solutions of superelliptic equations over number fields - Attila Bérczes, Yann Bugeaud, Kálmán Győry, Jorge Mello, Alina Ostafe, Min Sha - https://arxiv.org/abs/2310.09704 [v1 updated 2023-10-15]

### Exact phrase "Cantor-winning" - arXiv API
- query: `search_query=(abs:"Cantor-winning" OR ti:"Cantor-winning") AND submittedDate:[202001010000 TO 299912312359] sortBy=submittedDate desc`
- result: 0 hits, instrument: arXiv API

### Exact phrase "Cantor-winning" - OpenAlex
- query: `filter=title_and_abstract.search.exact:"Cantor-winning",to_publication_date:2026-10-04,from_publication_date:2020-01-01`
- result: 1 hits (newest first)
  1. 2024-04-19 - Schmidt games and Cantor winning sets - Dzmitry Badziahin, Stephen Harrap, Erez Nesharim, DAVID SIMMONS - https://doi.org/10.1017/etds.2024.23

### formal-conjectures PRs "Cantor-winning" - gh pr list (google-deepmind/formal-conjectures)
- query: `gh pr list --repo google-deepmind/formal-conjectures --search '"Cantor-winning" created:>=2020-01-01' --state all --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh pr list (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

### formal-conjectures issues "Cantor-winning" - gh search issues (google-deepmind/formal-conjectures)
- query: `gh search issues '"Cantor-winning"' --created '>=2020-01-01' --repo google-deepmind/formal-conjectures --json number,title,author,createdAt,url,state --limit 10`
- result: 0 hits, instrument: gh search issues (google-deepmind/formal-conjectures)
- note: gh returns no total; count is rows returned

## Prior-art log: arXiv:0709.3419 (2026-10-04 00:59 EDT)

### arXiv record: 0709.3419 - arXiv API
- query: `id_list=0709.3419`
- result: 1 hits (newest first)
- note: latest version + dates from the API entry
  1. 2007-09-21 - Density modulo 1 of sublacunary sequences: application of Peres-Schlag's arguments - Nikolai G. Moshchevitin - https://arxiv.org/abs/0709.3419 [v2 updated 2007-10-20]

### Forward citations of arXiv:0709.3419 - Semantic Scholar
- query: `papers followups 0709.3419`
- result: 10 hits (newest first)
- note: via `papers followups`
  1. 2012-01-10 - Density modulo 1 of lacunary and sublacunary sequences: application of Peres–Schlag’s construction - N. Moshchevitin - https://doi.org/10.1007/S10958-012-0660-3
  2. 2012-01-10 - Density modulo 1 of lacunary and sublacunary sequences: application of Peres–Schlag’s construction - N. Moshchevitin - https://doi.org/10.1007/s10958-012-0660-3
  3. 2011-05-07 - On fractional parts of powers of real numbers close to 1 - Y. Bugeaud, N. Moshchevitin - https://doi.org/10.1007/s00209-011-0881-z
  4. 2010-09-23 - On fractional parts of powers of real numbers close to 1 - Y. Bugeaud, N. Moshchevitin - https://arxiv.org/abs/1009.4528
  5. 2010-01-28 - Wall Crossing Phenomenology of Orientifolds - D. Krefl - https://arxiv.org/abs/1001.5031
  6. 2010 - Сингулярные диофантовы системы А. Я. Хинчина и их применение@@@Khintchine's singular Diophantine systems and their applications - Николай Германович Мощевитин, Nikolai Germanovich Moshchevitin - https://doi.org/10.4213/RM9354
  7. 2009-12-22 - Khintchine's singular Diophantine systems and their applications - N. Moshchevitin - https://arxiv.org/abs/0912.4503
  8. 2009-05-06 - Badly approximable numbers and Littlewood-type problems - Y. Bugeaud, N. Moshchevitin - https://arxiv.org/abs/0905.0830
  9. 2008-11-10 - On distribution of fractional parts of linear forms - I. Rochev - https://arxiv.org/abs/0811.1547
  10. 2008-10-04 - Badly approximable numbers related to the Littlewood conjecture - N. Moshchevitin - https://arxiv.org/abs/0810.0777

### Forward citations of arXiv:0709.3419 - OpenAlex
- query: `works?filter=cites:<OpenAlex id of doi:10.48550/arXiv.0709.3419>`
- result: 7 hits (newest first)
- note: OpenAlex work W1639634142
  1. 2012-03-28 - On distribution of fractional parts of linear forms - Igor Petrovich Rochev - https://doi.org/10.1007/s10958-012-0756-9
  2. 2012-01-09 - Density modulo 1 of lacunary and sublacunary sequences: application of Peres–Schlag’s construction - Nikolay Moshchevitin - https://doi.org/10.1007/s10958-012-0660-3
  3. 2011-05-06 - On fractional parts of powers of real numbers close to 1 - Yann Bugeaud, Nikolay Moshchevitin - https://doi.org/10.1007/s00209-011-0881-z
  4. 2011-01-12 - Badly approximable numbers and Littlewood-type problems - Yann Bugeaud, Nikolay Moshchevitin - https://doi.org/10.1017/s0305004110000605
  5. 2010-09-23 - On fractional parts of powers of real numbers close to 1 - Yann Bugeaud, Nikolay Moshchevitin - https://doi.org/10.48550/arxiv.1009.4528
  6. 2010-01-28 - Wall Crossing Phenomenology of Orientifolds - Daniel Krefl - https://doi.org/10.48550/arxiv.1001.5031
  7. 2010-01-01 - Сингулярные диофантовы системы А. Я. Хинчина и их применение - Николай Германович Мощевитин, Nikolai Germanovich Moshchevitin - https://doi.org/10.4213/rm9354

### Newest arXiv papers by Badziahin - arXiv API
- query: `search_query=au:"Badziahin" sortBy=submittedDate desc`
- result: 38 hits (showing 10, newest first)
  1. 2026-08-26 - Simultaneous Diophantine approximation on the three-dimensional Veronese curve: the complete Hausdorff dimension story - Dmitry Badziahin, Nikita Shulga - https://arxiv.org/abs/2608.25335 [v1 updated 2026-08-26]
  2. 2026-08-22 - Positive Logarithmic Hausdorff Measures of Exceptional Sets for the $p$-adic and $t$-adic Littlewood Conjectures - Dzmitry Badziahin, Volodymyr Pavlenkov, Evgeniy Zorin - https://arxiv.org/abs/2608.22078 [v1 updated 2026-08-22]
  3. 2025-09-16 - On the $P(t)$-adic Littlewood Conjecture in Characteristics $\ell \equiv 3\pmod{4}$ - Faustin Adiceam, Dzmitry Badziahin - https://arxiv.org/abs/2509.12826 [v3 updated 2026-08-10]
  4. 2025-09-01 - Distance between cubics and rationals - Dmitry Badziahin - https://arxiv.org/abs/2509.01105 [v2 updated 2026-01-05]
  5. 2025-08-12 - Generating random factorisations of polynomial values - Dmitry Badziahin - https://arxiv.org/abs/2508.08929 [v1 updated 2025-08-12]
  6. 2025-07-29 - Simultaneous Diophantine approximation on the three dimensional Veronese curve - Dmitry Badziahin - https://arxiv.org/abs/2507.21401 [v1 updated 2025-07-29]
  7. 2025-06-20 - Estimating lower limit in the $p$-adic Littlewood conjecture - Dmitry Badziahin - https://arxiv.org/abs/2506.16860 [v1 updated 2025-06-20]
  8. 2024-03-26 - Simultaneous Diophantine approximation to points on the Veronese curve - Dzmitry Badziahin - https://arxiv.org/abs/2403.17685 [v3 updated 2025-03-13]
  9. 2023-01-06 - On effective irrationality exponents of cubic irrationals - Dzmitry Badziahin - https://arxiv.org/abs/2301.02391 [v1 updated 2023-01-06]
  10. 2022-11-16 - Continued fractions of cubic Laurent series - Dmitry Badziahin - https://arxiv.org/abs/2211.08663 [v5 updated 2024-11-14]

### Keyword battery - not run
- query: `-`
- SKIPPED: no phrase or --keyword given; exact-phrase arXiv, OpenAlex and formal-conjectures searches not run
