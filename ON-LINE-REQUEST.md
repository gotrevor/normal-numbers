# ON-LINE REQUEST (box has no egress; a host session answers as ON-LINE-FINDINGS-<date>-<topic>.md)

## 2026-10-08 (repetition review lap 10): sources for the 3-adic two-logarithm bound

Needed for `SparseIdentity.Literature.PadicTwoLogs` (transcription check) and for its
formalization (DIRECTION.md, P3).  Please fetch and summarize, quoting statements verbatim:

1. **Y. Bugeaud, M. Laurent**, *Minoration effective de la distance p-adique entre puissances de
   nombres algébriques*, J. Number Theory 61 (1996) 311–342.  Needed: (i) the exact statement of
   the main corollary for two logarithms (shape `v_p(α₁^{b₁} − α₂^{b₂}) ≤ c·D⁴·(max{log b' + …})²
   log A₁ log A₂`; exact definitions of `b'`, `A_i`, the constant, and every hypothesis, e.g.
   `v_p(α_i) = 0`, multiplicative independence, `p`-adic disc conditions); (ii) the structure of
   the proof: the interpolation matrix (rows/columns, entries), the p-adic analytic upper bound
   (lemma statement), the zero lemma used (statement + hypotheses), the parameter choice.
2. **M. Laurent**, *Linear forms in two logarithms and interpolation determinants*, Acta Arith.
   66 (1994) 181–199: the zero lemma for two logarithms (statement and proof; the sumset
   condition `Card{α₁^r α₂^s} ≥ L`, `Card{r b₂ + s b₁} > (K−1)L`, `R = R₁ + R₂ − 1`, …).
3. Any expository source giving a complete, short proof of a p-adic two-logarithm lower bound
   for RATIONAL numbers (e.g. lecture notes; Waldschmidt's book ch. 7/9; Bugeaud's 2018 book
   *Linear Forms in Logarithms and Applications*, ch. on p-adic two logarithms).

Also useful: whether any Lean/Isabelle/Coq formalization of a linear-forms-in-logarithms bound
(any case) exists.

## 2026-10-09 (repetition lap 11): zero-lemma orientation check (high priority)
`PadicTwoLogs.Literature.LaurentZeroLemma` now reads: `Card{α₁^r α₂^s : r<R₁, s<S₁} ≥ L` and
`Card{r b₂ + s b₁ : r<R₂, s<S₂} > (K−1)L` ⇒ no nonzero `P = Σ_{l<L} q_l(X) Yˡ`, `deg q_l < K`,
vanishes on `(r b₂ + s b₁, α₁^r α₂^s)`, `r < R₁+R₂−1`, `s < S₁+S₂−1`.  (The first transcription had
the conditions swapped and is refuted in Lean.)  Please quote LMN 1995 Lemme 1 / Laurent 1994
verbatim so the orientation, the `−1`s and any extra hypothesis can be checked.

## 2026-10-07 (nn-cstar, proof/uniformbad-threshold)
Please fetch arXiv 2102.01186 (Falconer–Yavicoli, "Intersections of thick compact sets in R^d")
and transcribe verbatim the statement of Theorem 6 (countable intersections) and the definitions
it uses (thickness in R^d, any diameter/gap hypotheses), plus the d=1 specialization if stated.
Also Yavicoli "Patterns in thick compact sets" (Israel J. Math 2021): statement of the finite
intersection theorem with Σ 1/(1+τ_i) style condition, if present.

### Answer (Ren, host, 2026-10-07 01:50) - transcribed from the arXiv PDF of 2102.01186
- **Definition 1 (thickness in ℝ).**  C ⊂ ℝ compact, convex hull I, (Gₙ) the bounded open complementary
  intervals ordered by non-increasing length; Gₙ is removed from a closed interval Iₙ (a component of
  I \ (G₁ ∪ … ∪ G_{n−1})), leaving left/right closed intervals Lₙ, Rₙ.  τ(C) := inf_n min{|Lₙ|, |Rₙ|}/|Gₙ|.
  A point has thickness 0, a non-degenerate interval +∞.
- **Theorem 2 (Newhouse gap lemma).**  C₁, C₂ ⊂ ℝ compact, neither lies in a gap of the other, τ(C₁)τ(C₂) > 1
  ⇒ C₁ ∩ C₂ ≠ ∅.  (Paper: "does not generalise in any simple way to intersections of 3 or more sets.")
- **Definition 3 (ℝᵈ).**  Gaps (Gₙ) bounded components of Cᶜ by non-increasing diameter, E the unbounded
  component(s); τ(C) := inf_n dist(Gₙ, ⋃_{i<n} Gᵢ ∪ E)/diam(Gₙ).  Agrees with Definition 1 in d = 1.
- **Definition 5.**  K₁ := 2d(24√d)ᵈ log(16√d)/(1 − 2^{−d}),  K₂ := (24√d)ᵈ(1 + 4d²)/(1 − 2^{−d}).
  For d = 1: K₁ = 96 log 16 ≈ 266, K₂ = 240.
- **Theorem 6.**  (Cᵢ) countably many compact sets in ℝᵈ, τᵢ := τ(Cᵢ) > 0, with (i) supᵢ diam Cᵢ < ∞,
  (ii) a ball B with B ∩ Eᵢ = ∅ for every i, (iii) some c ∈ (0, d) with
  Σᵢ τᵢ^{−c} ≤ (1/K₂) β^c (1 − β^{d−c}),  β := min{1/4, diam(B)/supᵢ diam(Cᵢ)}.
  Then dim_H(B ∩ ⋂ᵢ Cᵢ) ≥ d − K₁ (Σᵢ τᵢ^{−c})^{d/c} / (βᵈ |log β|) > 0.
  (The PDF text extraction renders the right side of (iii) as "1/K2 · βc(1−β d−c)"; read it against the
  PDF if a constant matters.  The authors: "In practice, the thicknesses needed are rather large as a
  consequence of the large constants K₁ and K₂.")
- Not fetched: Yavicoli, "Patterns in thick compact sets" (Israel J. Math 2021).
- **Host note on fit:** with d = 1, β ≤ 1/4 and K₂ = 240, (iii) needs Σ_b τ_b^{−c'} ≲ 4^{−c'}/240 for some
  c' ∈ (0, 1).  With τ_b ≈ b^C/2 that forces C far above 4 (the base-2 term alone is (2^{C}/2)^{−c'}), so
  Theorem 6 as stated will not reach c⋆ ≤ 4 and probably not beat 12.  Newhouse (Theorem 2) is pairwise
  only.  A c ≤ 4 proof needs its own multi-set gap argument for the small bases (that is new math, and
  the place to invent), with Theorem 6-type potential handling only the tail.

## 2026-10-07 (c⋆ lap 5) — thickness-of-intersection results
Context: a Newhouse route to c⋆ ≤ 4 (A = E₂(4) has thickness exactly 3; need B ⊂ ⋂_{b≥3} E_b(4)
compact with thickness > 1/3; raw ⋂ has thickness 0 from cross-base near-coincident windows).
Please transcribe (statements + definitions, verbatim where possible):
1. Hunt–Kan–Yorke, "When Cantor sets intersect thickly", Trans. AMS 339 (1993) 869–888
   (https://www.yorke.umd.edu/Yorke_papers_most_cited_and_post2000/1993_11_Hunt_Kan_Trans_AMS_Cantor_sets_intersect_thickly.pdf):
   the main theorem with the explicit (τ₁,τ₂) curve and the lower bound on the thickness of the Cantor
   set inside K₁ ∩ K₂ (any formula like τ(K) ≥ f(τ₁,τ₂)).
2. arXiv 2212.02023 ("A survey on Newhouse thickness, fractal intersections and patterns"): every
   theorem about (a) intersections of 3 or more / countably many sets on the line with explicit
   thickness conditions, (b) thickness of an intersection, (c) stability of thickness when a compact
   set is cut by small intervals or perturbed.

### Answer (Ren, host, 2026-10-07 04:55)
1. **Hunt–Kan–Yorke 1993: NOT REACHED.**  The yorke.umd.edu URL gives no response and the AMS copy needs a login
   (Trevor's Cornell access could get it if it becomes decisive).  Do not cite it from memory.  The survey below
   cites it as [13] but does not restate its theorem.
2. **Yavicoli, arXiv 2212.02023 (survey), transcribed from the PDF:**
   - **Theorem 8 (Newhouse gap lemma, survey form).**  C₁, C₂ ⊂ ℝ compact with (1) conv(C₁) ∩ conv(C₂) ≠ ∅,
     (2) neither set lies in a gap of the other, (3) τ(C₁)τ(C₂) ≥ 1.  Then C₁ ∩ C₂ ≠ ∅.  (Note **≥ 1**, not > 1;
     unbounded complementary components are not gaps.)  Observation 9: sharp, for any τ₁τ₂ < 1 there are
     disjoint examples.
   - **Theorem 13.**  τ(C) > 0 ⇒ dim_H C ≥ log 2 / log(2 + 1/τ(C)).
   - **Lemma 24 (countable intersection property)** is stated for *winning* sets (Schmidt-game side), not for
     thickness; Theorem 22 (Broderick–Fishman–Simmons) is about M_ε winning.  The survey says the Gap Lemma
     "does not generalize in any simple way to intersections of 3 or more sets" and notes its own ℝᵈ countable
     result ([10] = Falconer–Yavicoli, answered above) needs large thickness.
   - **Stability:** "the hypotheses are robust under perturbations of the Cantor sets ... under C¹ perturbations
     whose derivatives are close to the identity ... and if the sets are self-homothetic, under perturbations of
     the generating IFS" (for Theorem 31, the ℝᵈ gap lemma, citing [28, Lemmas 7 and 8]).  No quantitative
     statement on thickness of a set cut by small intervals, and no thickness-of-intersection formula, in the
     survey text.
- **Host note:** nothing found gives a usable lower bound on the thickness of an intersection of many sets, so
  `ThickCore` (thickness of ⋂_{b≥3} E_b(4) after merging near-coincident windows) is your own lemma to prove;
  with E₂(4) at thickness exactly 3, you need τ(B) ≥ 1/3 (Theorem 8 allows equality).
