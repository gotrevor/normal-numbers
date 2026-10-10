# ON-LINE FINDINGS 2026-10-10: request queue cleared (3-adic two-log items self-resolved)

Host session (Ren), 2026-10-10.  Clears the whole `ON-LINE-REQUEST.md` (identical in `nn-stretch`
and `normal-numbers`).

## 2026-10-08 / 2026-10-09 items (Bugeaud–Laurent 1996, Laurent 1994, LMN 1995 Lemme 1): self-resolved

Not researched.  Repetition lap 13 (`b70bd94b`, 2026-10-09) proved the zero lemma elementarily
(`PadicTwoLogs.laurentZeroLemma`, `src/NormalNumbers/ZeroLemma.lean`) and made
`PadicTwoLogs.padicTwoLogs` unconditional.  `HANDOFF-2026-10-09-repetition-lap13.md` records
`#print axioms liouvilleCantorFullProfile = [propext, Classical.choice, Quot.sound]`.  The
corrected `Literature.LaurentZeroLemma` is now a theorem, so the transcription's fidelity no longer
carries weight, and the swapped form is refuted in Lean (`not_laurentZeroLemmaMisread`).  The host
re-checked only that the three PadicTwoLogs/ZeroLemma files contain no `sorry` (a grep, 2026-10-10).

Still open, but no longer blocking: (a) a verbatim check that `Literature.PadicTwoLogs` really is a
special case of Bugeaud–Laurent's corollary, as `docs/notes/bugeaud-10-37-cantor-liouville.md`
says; (b) whether any proof assistant has a formalized linear-forms-in-logarithms bound (the note
makes no priority claim here).  Re-ask either one if a note will lean on it.

## 2026-10-07 items (nn-cstar: Falconer–Yavicoli, thickness survey): moved here from inline

These answers were committed inline in the request file (`b359ac03`, `ca9403da`) and reached this
branch through merges.  They are reproduced verbatim below, so that deleting the request file loses
nothing.

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

## Addendum (same day): Bugeaud–Laurent 1996 checked against the authors' preprint

**Source read:** the authors' preprint `logpadicdef.ps`, linked from Bugeaud's publication list
(`https://irma.math.unistra.fr/~bugeaud/travaux/logpadicdef.ps`; headed "Journal of Number
Theory", 29 pp.).  ScienceDirect (DOI 10.1006/jnth.1996.0152) served a bot check to the host, so
the typeset version was **not** read.  Statements below were read from page images, not OCR, but
should be checked against the published version before anything quotes a constant.  The PDF is at
`papers/bugeaud-laurent-1996-padic-two-logs-preprint.pdf`, a gitignored symlink into
`~/personal/papers/` that the box may not be able to follow.

**Setup (§2).**  `v` is the valuation on `Q̄_p` with `v(p) = 1`, and `Λ = α₁^{b₁} − α₂^{b₂}` with
`b₁, b₂` positive integers.  `K_v = Q_p(α₁, α₂)` has ramification index `e` and residue degree
`f`, and `D = [Q(α₁, α₂) : Q] / f` (note the division by `f`).  The hypothesis throughout is
`α₁, α₂ ∈ U_v`, i.e. `v(αᵢ) = 0`.  `g` is the least positive integer with `αᵢ^g ∈ U_v¹` (principal
units), and `g ∣ p^f − 1`.  `A₁, A₂ > 1` satisfy `log Aᵢ ≥ max{h(αᵢ), log p / D}`, and
`b' = b₁/(D log A₂) + b₂/(D log A₁)`.

**Théorème 3** (verbatim in substance).  *If `α₁, α₂` are multiplicatively independent, then*
`v(Λ) ≤ 24pg/((p−1)(log p)⁴) · D⁴ · (max{log b' + log log p + 0.4, 10 log p / D, 10})² · log A₁ log A₂.`
**Corollaire 1** replaces `g` by `p^f − 1`.  **Corollaire 2** adds `αᵢ ∈ U_v¹` (so `g = 1`), and
the bound is then `≤ 208 D⁴ (max{…})² log A₁ log A₂`.  **Théorème 2** is the asymptotic version, with
`c > 64/9` in place of 24, valid for `b' ≥ b(c, p)`.  **Théorème 4** is a table `c(μ, ν)` for other
coefficients in the max.

**Verdict on `Literature.PadicTwoLogs` (SparseIdentity.lean:915).**  Its docstring formula is
Théorème 3 / Corollaire 1, with `c(p) = 24pg/((p−1)(log p)⁴)`.  One imprecision: "a field of degree
`D`" should be `D = [Q(α₁,α₂):Q]/f`, which is 1 for rationals in any case.  The Lean statement
follows from Théorème 3 with `p = 3`, `D = 1`, `g ≤ 2`, `α₁ = t`, `α₂ = b'/a'` (with the 3-parts
stripped), `b₁ = δ`, `b₂ = 1`, but **only in the multiplicatively independent case**.  The dependent
case (`b'/a' = ±t₀ʲ`) is outside BL and is lifting the exponent, as the docstring and `g_le_dep`
already handle it.  So "special case of Bugeaud–Laurent" overstates it slightly; "follows from BL
Théorème 3 in the independent case" is exact.

**Zero lemma: orientation confirmed.**  BL **Lemme 6** (§4), verbatim in substance: *let
`a₁, a₂, b₁, b₂` lie in a field, `a₁ ≠ 0`, `a₂ ≠ 0`, `K, L` positive integers, `E₁, E₂ ⊂ Z²` finite,
and `P ∈ K[X,Y]` nonzero of partial degree `≤ K−1` in `X` and `≤ L−1` in `Y`.  If
`Card{a₁^r a₂^s : (r,s) ∈ E₁} ≥ L` and `Card{b₂r + b₁s : (r,s) ∈ E₂} > (K−1)L`, then at least one of
`P(b₂r + b₁s, a₁^r a₂^s)`, `(r,s) ∈ E₁ + E₂`, is nonzero.*  Taking `Eᵢ = [0,Rᵢ) × [0,Sᵢ)` gives
`E₁ + E₂ = [0, R₁+R₂−1) × [0, S₁+S₂−1)`, which is exactly the corrected `LaurentZeroLemma`: the
multiplicative condition is `≥ L` on `(R₁,S₁)`, the additive one is strict `> (K−1)L` on `(R₂,S₂)`.
BL's lemma needs **no** multiplicative independence, so that hypothesis in the Lean statement is
harmless but unnecessary.  BL's proof is short: eliminate `Y` with a nonzero generalized
Vandermonde `det((a₁^{r'} a₂^{s'})^ℓ)` (citing Lemme 1 of their [5], = Laurent–Mignotte–Nesterenko
1995), then count the degree of the resulting `Δ(X)`, `≤ L(K−1)`.  That is the same shape as the
proof in `ZeroLemma.lean`.  Théorème 1's version adds the congruence classes mod `g` and `p^t`-th
powers: `Card{α₁^{p^t r} α₂^{p^t s} : r<R₁, s<S₁, m₁r+m₂s ≡ c₁ (g)} ≥ L` and
`Card{rb₂ + sb₁ : r<R₂, s<S₂, m₁r+m₂s ≡ c₂ (g)} > (K−1)L`.
(Yamada, arXiv math/0607072, restates Théorème 1 with `≥ (K−1)L` in the second condition.  The BL
preprint has strict `>`, and Lemme 6 needs it.)

**Prior formalizations of linear forms in logarithms.**  None found as a proved bound.
- Lean 4: Karatarakis–Wiedijk, *A formalization of the Gelfond–Schneider theorem*, arXiv
  2603.24823 (March 2026; abstract read).  This is qualitative transcendence, not an effective
  lower bound.
- The lean-eval problem list carries a Baker–Wüstholz statement marked "Not yet solved"
  (`lean-lang.org/eval/problems/bakerWustholz_linearForms_logs/`; this comes from a search
  summary, and the page was not opened).
- No Isabelle/AFP or Coq/Rocq hit came up in two web searches, which is not an exhaustive check.
  So as far as this search reaches, `padicTwoLogs` may be the first proved effective linear-forms
  bound in a proof assistant (p-adic, two rational logarithms).  That is a priority claim and needs
  a proper AFP / Zulip check before any note makes it.
