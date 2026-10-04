# Entropy lane (E5) audit, 2026-10-04

Direction doc for the E5 lane of `docs/ENGINE-PROPOSALS-2026-10-04.md`.  Lean files are the record: `src/NormalNumbers/EntropyProfiles.lean` (cited Props, wiring, frozen headline) and `src/NormalNumbers/EntropyProfilesStretch.lean` (stretch conjectures).

## Verdict

- **The E5 premise mostly fails.**  "Refereed Props plus one new profile theorem at the a.e. level" has no new target: the a.e. normality profile of every relevant measure is already settled, and it is `{b : b ≁ p}`.
  - Cantor and `×p` product measures: Cassels 1959, Schmidt 1960, Feldman–Smorodinsky 1992.
  - `×p`-ergodic measures of positive entropy: Host 1995, Lindenstrauss 2001, Hochman–Shmerkin 2015 Thm 1.10.
  - Self-similar measures, with or without overlaps or separation: Hochman–Shmerkin Thm 1.4, Algom–Baker–Shmerkin 2111.10082 Thm 1.1, Bárány–Käenmäki–Pyörälä–Wu.
  - Same-ratio IFS with irrational translations: Dayan–Ganguly–Weiss 2002.00455.
  - Existence of any profile closed under `∼`: Schmidt 1960, Becher–Slaman (computable).
  - Rajchman and Frostman measures carried by `N(B, B')`: Pramanik–Zhang 2408.03473.
  - Recorded in Lean as `ae_isNormal_iff_not_multDep`, a wiring theorem and not new.
- **Product measures do not need entropy.**  Wherever a measure has product (Bernoulli or Cantor) structure, Cassels–Schmidt second moments already give rates, and the repo's `CantorLiouville` and `SchedDerandomize` engines use exactly these.  Entropy is needed only for non-product, non-weak-Bernoulli `×p` measures.  Making those effective is Algom's open Problem 1 (2504.18192 §5.1), which the 2026-10-02 sweep graded at 5%.
- **Frozen headline instead:** a negative answer to Hochman–Shmerkin's own open question on bi-Lipschitz stability.  It is not entropy-unlocked; it is a sharpness guard on the cited Diff¹ Prop.

## The question answered

Hochman–Shmerkin, *Equidistribution from fractal measures*, Invent. Math. 202 (2015) 427–479 (DOI 10.1007/s00222-014-0573-5; note: **Inventiones, not Annals**), §1.2.1 after Corollary 1.8 (arXiv:1302.5792 numbering):

> "Bugeaud, Fishman, Kleinbock and Weiss have shown that for many fractal sets, including self-similar sets satisfying the open set condition, there is a full-dimension subset consisting of numbers which are *not* normal in any integer base.  Moreover their result holds for any bi-Lipschitz image of the set.  The stability of our results under bi-Lipschitz transformations remains open."

**Frozen claim** (`exists_strictMono_biLipschitz_cantorSet_not_isNormal_two`): there is a strictly increasing bi-Lipschitz `g : ℝ → ℝ` with `g(x)` not 2-normal for every `x` in the middle-third Cantor set `K`.  Consequences, wired: `exists_biLipschitz_ae_not_isNormal_two`, `not_biLipschitz_stable`, and `headline_map_not_isC1Diffeo`.  The last says that, given the HS Prop, such a `g` cannot be a C¹ diffeomorphism.

**Mechanism.**  The target set is `F = {no hex digit 15}`, which is closed, has dimension `log 15/log 16 > log 2/log 3`, and contains no 2-normal point.
- **Gap estimate:** from a left-type point `0.w000…` of `F`, every gap of `F` at distance `D` has length `≤ 1.15 D`.  So windows of ratio `≥ 2.3` always meet `F`.
- **Construction:** nested intervals with endpoints in `F`, grouped by `L` levels of `K` with `(3/2)^L` large.  The diameters are `≍ 3^{-n}` and the sibling gaps are `≍ 3^{-n}`.
- **Extension:** extend affinely on the gaps of `K`.  Since `K` and `g(K)` are null, the extension is bi-Lipschitz on `ℝ`.
- **Why `g` is not C¹:** the local scale ratio of `g` on `K` has no limit, which is exactly what keeps it outside HS's Diff¹ hypothesis.

## Difficulty check

- **Proved implications:**
  - HS Thm 1.4 implies Cassels–Schmidt: `casselsSchmidt_of_hochmanShmerkin`.
  - Cassels–Schmidt plus the missing digit give the exact a.e. profile: `ae_isNormal_iff_not_multDep`.
  - The headline gives failure of bi-Lipschitz stability: `not_biLipschitz_stable`.
  - The headline plus HS show that `g` is not C¹: `headline_map_not_isC1Diffeo`.
- **Unproved premise:** the headline, an elementary nested-interval construction with no cited input.
- **Mechanism test on a known-false sibling:**
  - The construction must fail when the target has dimension `< dim K`, because bi-Lipschitz maps preserve dimension.  The budget inequality `2^L B < 3^L A/2` encodes this through the window ratio.
  - It must also fail for C¹ maps, by HS.  It does, because the scale ratio does not converge.
- **Lean guard on the cited Props' hypothesis (`log p/log q ∈ ℚ`):** `not_isNormal_three_pow_cantorPt`, `not_ae_isNormal_three_pow`, and `not_ae_isNormal_nine`.  Every Cantor point fails every base `3^k`, so `b ≁ 3` cannot be dropped.
- **Success estimates:**
  - The mathematics is right: 85%.
  - Not already answered in print: 65%.
  - Lean proof within a few laps: 55%.
  - Above the 40% bar, so it goes on `proof/entropy` with no Maze rows.

## Cited Props needing a referee

| Prop | Source | Faithfulness note |
|---|---|---|
| `CasselsSchmidtCantor` | Cassels, Colloq. Math. 7 (1959); Schmidt, Pacific J. Math. 10 (1960); also HS Thm 1.4 with `g = id` | Faithful. |
| `HochmanShmerkinCantorDiff1` | HS Thm 1.4 (`thm:dissonant-IFSs`), IFS `{x/3, x/3+2/3}` | Our `∀ᵐ x ∂μ, IsNormal b (f x)` is implied by their `fμ`-a.e. statement (`ae_of_ae_map`).  `IsC1Diffeo` = C¹, `f' ≠ 0`, bijective. |
| `HochmanShmerkinTimesP` | HS Thm 1.10 (`thm:application-HostLindenstrauss`); Host 1995 Thm 1 for the coprime case | "Positive entropy" is replaced by a Frostman bound `μ(B(x,r)) ≤ C r^δ`.  This is stronger, since for `T_p`-ergodic `μ` we have `dim μ = h/log p`, so the Prop is weaker.  A referee should check the support convention (`μ` on `[0,1)`, `timesMap = fract(p·x)`). |

Theorem numbers follow the arXiv source we read (`\newtheorem{thm}{Theorem}[section]`, shared counter): 1.1 `thm:WM-case`, 1.2 Pisot case, 1.3 Cor., 1.4 dissonant IFS, 1.5, 1.6, 1.7 analytic images, 1.8 Cor. `x²`, 1.9 Host, 1.10 Host–Lindenstrauss application.  Algom 2504.18192 also cites "[HS, Theorem 1.4]" for the dissonant-IFS statement, which agrees.

## Candidates considered

| Candidate | Source / wording | Verdict | % |
|---|---|---|---|
| **HS bi-Lipschitz stability** | HS §1.2.1, quoted above | **Frozen headline** (negative) | 55 (Lean), 85 (math) |
| Absolute version: `g(K)` avoids normality in every base | same | Stretch 1, `exists_strictMono_biLipschitz_cantorSet_absAbnormal` | 45 |
| Nonlinear image of a general `×p`-ergodic measure, same base `p` | Not posed in print.  HS 1.10 covers only `m ≁ p`; HS 1.7, Baker–Banaji and ARW need self-similar or Gibbs structure | Stretch 2, `ae_isNormal_self_base_sq_of_timesP_ergodic` | 5 (ours), 70 true |
| Algom Problem 1, effective rates | 2504.18192 §5.1: "Can one specify a rate of convergence here?" | Open, hard.  The martingale-difference ergodic theorem is the non-effective step.  BLMV 2009 (effective Rudolph) is the only effective `×a×b` input and it is log-log | 5 |
| Algom Problems 2–3, `β`-normality beyond Pisot; Rajchman implies normal in Pisot bases | 2504.18192 §5.2 | Open, no engine | 3 |
| Algom Problem 4, Poissonian `k`-correlations of `T_b^n x` | 2504.18192 §5.3 | The Cantor-measure `k = 2` instance looks reachable by a Cassels-type 4th moment, but it is a Fourier lane, not E5 | 25 (separate lane) |
| HS: Cantor-a.e. point Gauss-normal? | HS §1.2, BA-numbers subsection | Open, CF statistics on `K`, no engine | 3 |
| HS: a Gauss-normal number not normal in any base | HS §1.2, BA-numbers subsection, "not even known" | Very likely answered since 2013 (Vandehey, absolutely abnormal CF-normal numbers); not verified | n/a |
| Computable generic point of a non-product `×p` measure, normal in independent bases | Becher–Lew Deveali 2607.06773 claims the generalisation to prescribed non-uniform frequencies ("can be generalized…"), unproved there | Folklore-adjacent; for weak-Bernoulli measures Feldman–Smorodinsky's Fourier route is likely effective | 15 |
| Zero-entropy profiles | Hochman 2609.21481 Problems 1–3; BLD conjecture | Swept 2026-10-03 at 8%; entropy methods do not apply | 8 |

## Negative inventory read

- `Maze.lean` row "measure-theoretic non-disjunctive witness" (refuted by Host 1995).  Host's theorem blocks every measure-theoretic absolutely non-disjunctive witness.  Same mechanism here: entropy Props yield normality and never non-normality, so E5 can only feed positive profile halves.
- `docs/disjunctive-vs-normal.md` §4.2.  `STATUS.md` (10.37 profile `3 ∤ b`, Baker–Banaji lanes).
- `OPEN-PROBLEMS-SWEEP-2026-10-02` row 14 (Algom open problems, 5%).  `-10-03` row 8 (Hochman zero entropy, 8%).  `-10-03b` (Bernoulli convolutions "done").  `-10-03c` (10.31, 10.37 profile).
- `docs/notes/*` (Baker–Banaji, BAD, 10.37).

## Searches (2026-10-04)

1. `papers followups 1302.5792`: 84 citers, all listed (the file is in the session scratchpad).  We read the TeX of 2504.18192 (Algom survey), 1904.12506 (simultaneous Host), 2103.08938 (Hochman, short proof of Host), 2002.00455 (DGW), 2111.10082 (ABS), 2107.02699, 2002.11607, 2608.29569, 2609.21481, 2607.06773 (BLD), 2408.03473 (Pramanik–Zhang) and 2407.16262.  We grepped them for `bi-Lipschitz`, open, question, problem, effective and rate.  The only `bi-Lipschitz` hits outside HS are dimension-invariance remarks (1904.12506 l.302; 2609.21481).
2. arXiv API: six queries (effective / Host / quantitative / rate / pointwise normal / Rudolph).  **All returned HTTP 503**, so this is a null instrument and not a negative result.
3. OpenAlex: "bi-Lipschitz image Cantor set normal numbers", "bi-Lipschitz invariance normality self-similar measure", "Lipschitz embedding Cantor set non-normal numbers", "stability of normality under bi-Lipschitz maps".  The hits were BFKW 0909.4251, Pramanik–Zhang 2408.03473 and HS itself; none answers the question.
4. Web: "Hochman Shmerkin bi-Lipschitz pointwise normal … open question answered" and a "bi-Lipschitz image Cantor set not normal every point" phrase search.  Both surface only HS's own sentence.
5. Web: "effective version Host theorem rate …" surfaced only Algom 1904.12506, HS, and Badea–Grivaux 2303.01089.
6. Newest work (OpenAlex, from 2025-06) by Hochman, Shmerkin, Algom, S. Baker and Bugeaud.  Nothing on bi-Lipschitz normality.  Possibly adjacent: Shmerkin et al. "Full measure universality for Cantor sets" (2026), which is about affine copies, and Algom et al. "Van der Corput and metric theorems for geometric progressions for self-similar measures" (2025).  A referee should look at both.
7. Not done: a `formal-conjectures` PR search, which is not relevant to a non-Erdős question, and the published Inventiones text.  The published version might reword §1.2.1, so check the journal PDF before outreach.

## Next lap

Prove the headline: the `F` gap estimate, then the block construction, then the bi-Lipschitz extension.  The engine is new, a monotone nested-interval embedding, and it should be reusable for Stretch 1.
