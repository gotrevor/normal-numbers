# Attack map: Vandehey §7 problem 1 (quadratic-irrational LFTs preserve CF-normality?)

*Ren, 2026-08-23.  Companion to `papers/vandehey-2017-matrix-actions-cf-normality.md`.
Question: x CF-normal, q,r quadratic irrationals, q ≠ 0 ⇒ qx + r CF-normal?
Simplest instances: x ↦ φx, x ↦ x + φ.  Status: open (posed Compositio 2017).*

## 1. The structural diagnosis: it dies on Dirichlet's unit theorem

Vandehey's proof rides on one finiteness: matrices over ℤ with |det| = D and
his Type I–VI window conditions form a FINITE state set M_D, because entry
bounds |α| ≤ D pin down finitely many integers.  Run the same transducer for
M = (q r; 0 1) with q,r ∈ ℚ(√5): after clearing denominators the states live
over ℤ[φ], digit matrices A_j, J stay integer (self-conjugate), so det(state)
is fixed up to sign and the states have entries in ℤ[φ] with the SAME
real-place window bounds.  But bounded real embedding does not make a subset
of ℤ[φ] finite — ℤ[φ] is dense in ℝ.  Finiteness over ℤ worked because
ℤˣ = {±1}; over a real quadratic ring O_K, Dirichlet gives infinite units
(±φⁿ), equivalently a second archimedean place where entries drift.  Wall and
Vandehey are theorems about number fields with finite unit group (ℚ); the
quadratic question is the first infinite-regulator case.

Cute reframing for q = φ, r ∈ ℤ[φ]: N(φ) = φ(1−φ) = −1, so det M is a UNIT
and the state matrices sit in GL₂(ℤ[φ]) — the Hilbert modular group for
ℚ(√5).  So "multiply by φ" is the det = ±1 case over O_K, the analogue of the
TRIVIAL (Serret) case over ℤ.  Serret fails anyway because GL₂(ℤ[φ]) is far
bigger than the regular CF's symmetry group: its projection to the real place
is dense in PGL₂(ℝ) (irreducible lattice in PGL₂(ℝ)², projections dense), so
there is no fundamental-domain/tail-surgery argument.  Also explains why the
base-b analogue of the problem degenerates: the eventually-periodic numbers
of base b are the RATIONALS, so "Wall for base-b-periodic coefficients" is
just Wall.  The CF question is genuinely richer because CF-periodic points
are irrational.

## 2. Dead ends (know why, don't relitigate)

- **Serret/commensurator**: g = diag(√φ, 1/√φ) ∉ Comm(PSL₂(ℤ)); Γ and gΓg⁻¹
  incommensurable, equidistribution on one quotient says nothing pointwise
  about the translate.  This is the geodesic-flow face of the same unit drift.
- **Soft rigidity**: reformulated on X × X, the pair (Γh_t, Γg h_t) is a
  single orbit whose empirical limits are self-joinings of the geodesic flow
  with Haar first marginal.  Geodesic flow is Bernoulli — self-joinings are
  wild, no Ratner (not unipotent), no measure rigidity applies.  Same wall as
  "normal base 2 ⇒ normal base 3".  Nothing pointwise available off the shelf.

## 3. Route A (the real attack): Vandehey with a COMPACT fiber

Key observation: the conjugate place never feeds back.  The transducer update
M_{n+1} = A_out⁻¹ M_n A_{a_{n+1}} and the emission rule read ONLY the real
embedding of M_n (as a projectivized Möbius map on the interval).  The
real-place state evolves autonomously; the conjugate place was only
Vandehey's finiteness certificate, not part of the dynamics.  So replace
finiteness by compactness:

- **State space**: W = closure of {real embeddings of post-emission states},
  a compact window in PGL₂(ℝ) of bounded-distortion maps.  Post-emission
  boundedness should be automatic exactly as in the integer case: emission
  fires when the image interval falls deep into a cylinder, and pulling the
  emitted digits off re-expands the map; degeneration toward a singular map
  = deep-cylinder image = emission, so the renormalization enforces the
  window.  (This is the first lemma to prove carefully; it is the compact
  analogue of "entries ≤ D".)
- **Merging**: his finite-chain transitivity + Saloff-Coste–Zúñiga becomes a
  Doeblin/coupling condition for a time-inhomogeneous chain on compact W.
  The fiber maps are compositions of POSITIVE matrices: Birkhoff–Hopf
  contraction of the Hilbert projective metric supplies asymptotic loss of
  memory — cone contraction replaces finite-state merging.
- **Counting (§5–6)**: trigger strings become trigger WINDOWS (C_s × U,
  U ⊂ W open); his f_j^± upper/lower approximant machinery is already shaped
  for Riemann-squeeze over such families; needs ρ(∂U) = 0 bookkeeping
  (Portmanteau) instead of finiteness.
- **Endgame is FREE**: his either-or trick (E_M ⊆ E or E_M ∩ E = ∅, and
  E_M = M(co-null) has positive measure) works verbatim for any M.  So the
  ENTIRE problem reduces to: every string appears in Mx with a limiting
  frequency independent of the CF-normal x.  No limit identification needed.

Crux risks, in order: (i) uniform merging on W along arbitrary CF-normal
inputs (CF-normality controls fixed-rank cylinder frequencies; excursion
events are unbounded-rank — must be squeezed by the f_j^± method); (ii) the
window lemma; (iii) stationary measure on W may be singular/weird — fine,
nothing needs smoothness.  Estimate: months-scale research program, paper-
sized.  P(this program closes it) ≈ 50%; P(wall at uniform merging) ≈ 35%.

✅ **Lit sweep DONE 2026-08-24** (§6 below).  Fisher–Schmidt ETDS 2014 read in
full: **no Theorem-3.1 analogue, and its fiber is finite, not continuous** — see
`papers/fisher-schmidt-2014-approximants-geodesic-flows.md`.  Forward-citation
crawl of Vandehey 2017: §7 problem 1 still open and untouched (~85%).

## 4. Route B (our lane, concrete): an explicit WITNESS via the brick method

Weaker but new and in-programme: construct an explicit x* with x* CF-normal
AND φx* CF-normal (a.e. x works; no explicit witness is known — the
existence statement is trivial, the witness is not).  Mechanism: the B5′
brick framework already tracks incommensurable digit systems (base 2..t + CF)
by nesting intervals and paying discrepancy rent.  "CF of φx" is one more
digit system whose cylinders are φ⁻¹·C_s — an interval family with
Gauss∘(×φ) measure; ×φ maps bricks to intervals with distortion exactly φ.
Every Lemma-13-style estimate needed is the image-interval version of what
W1–W3 supply (cylinder measure toolkit, digit law, mixing on φI).  Greedy
version composes with B5′ itself: one witness that is absolutely normal +
CF-normal + Khinchin-typical + φ·(it) CF-normal; extends to any finite set
of quadratic maps (φx, x+φ, x/φ, …).  P(structurally sound) ≈ 75–90%; risk
is bookkeeping bloat, not a conceptual wall.  This directly pokes Vandehey's
question with a constructive data point and would be first-in-any-prover by
a wide margin (it'd be first on PAPER).

## 4½. Updates (2026-08-24)

- **B5′ landed** (both tiers axiom-clean), so Route B's machinery exists and
  is battle-tested.  Route B is now speced as **B6** in `KHINCHIN.md` (lemma
  table L1–L5, tiers, size).  Key upgrade found while spec-ing: the witness
  construction uses only that ψ(x) = qx + r has constant distortion — **q
  need not be quadratic**; Tier 2 handles a countable family of arbitrary
  real affine maps simultaneously.  The quadratic-irrational restriction
  matters only for Route A (where the transducer needs O_K arithmetic).
- **Lit sweep run** (web-search tier): no sign §7 problem 1 is resolved
  (~85%).  Finds: Heersink–Vandehey arXiv:1509.05501 (CF normality NOT
  preserved along arithmetic progressions — the fragility direction).
  ⚠️ Its third claim was garbled: the CF-vs-base-b **incomparability** result is
  **Jackson–Mance–Vandehey 2021** (arXiv:2111.11522, unconditional and
  descriptive-set-theoretic: the two normalities are *maximally* logically
  separate, `D₂(Π⁰₃)`-complete), superseding Vandehey's GRH-conditional
  arXiv:1512.00337.  Scheerer 2017 is a different paper (a construction, already
  pinned).  Both Route-A pre-steps are now DONE — see §6.

## 5. Bonus separations worth remembering

- Khinchin-value transfer is a SEPARATE gap even over ℤ (pin note §
  "Khinchin-value transfer"): CF-normal ⇒ geometric mean → K₀ needs a
  uniform-integrability tail argument nobody has written.  Two publishable
  gaps, one elementary-looking.
- Mendès France's simple-normality version (§7 problem 2) is independent and
  might be MUCH harder (Vandehey's proof needs full normality).

## 6. Forward-citation crawl, 2026-08-24 🕸️

**Instruments** (two independent aggregators + targeted arXiv sweeps; Google Scholar
unreachable from here, so preprints/theses outside these indexes are a blind spot):
OpenAlex `cites:W1898830595` → **6** citing works; Semantic Scholar
`DOI:10.1112/s0010437x16007740/citations` → **9**; union = 9 distinct.  Plus arXiv
metadata sweeps (`au:Vandehey`, `abs:"continued fraction" AND abs:"normal number"`,
`abs:"continued fraction normality"`), and a PDF-level read of every citing arXiv paper
grepped for `matrix action | quadratic irrational | Möbius | fractional linear`.

**Headline: §7 problem 1 is untouched.**  Every one of the 9 citing works cites the paper
in passing (bibliography or "Theorem 3.1 gives us the lifted-normality tool"); not one
restates, attacks, or reports partial progress on the quadratic-irrational question.
Vandehey himself has published 12+ papers since and never returned to it — including
Lukyanenko–Vandehey *A geometric proof of Lagrange's theorem for continued fractions*
(arXiv:2603.12425, **March 2026**), which is entirely about characterizing quadratic
irrationals as fixed points of loxodromic elements and would be the natural place to say
something if he had it.  Confidence §7-1 is open: **~90%** (up from 85%).

### 6.1 🚨 The one thing that changes our plans: Vandehey's Lemma 3.2 is false as stated

**Airey–Mance, *Hotspot lemmas for non-compact spaces*** (arXiv:1912.10265, Math. Notes
108 (2020)) prove that **Theorems 1, 4 and 5 of Moshchevitin–Shkredov** [Math. Notes 73
(2003), *On the Pyatetskii-Shapiro criterion for normality*] **are incorrect as stated on
non-compact spaces**.  The error: a `lim sup` distributed over an *infinite* sum.  Their
counterexample is `x₀ = (1,2,3,4,…) ∈ ℕ^ℕ` under the shift — every cylinder has visit
frequency `0 ≤ φ(µ(I))`, so the hypothesis holds vacuously while `x₀` is not normal.

Vandehey's **Lemma 3.2** (the Pyatetskii-Shapiro criterion in the form his whole §3 runs
on) says in its proof: *"This is a simple consequence of Theorem 1 in [17]"* — that is
**exactly the broken theorem** — and he applies it on `Ω̃ = Ω × M` where `Ω` is the CF
space: countably infinite alphabet, **non-compact**, escape of mass available.  The
counterexample lifts verbatim, so Lemma 3.2 as stated is false.

**Theorem 1.1 is almost certainly fine**, because Lemma 3.2 is only ever applied to
`(x, M)` with `x` **CF-normal**, and CF-normality forces the empirical measures
`E(x,n) = (1/n) Σ δ_{Tⁱx}` to be **tight** (digit-`≤K` cylinder frequencies converge to
Gauss measure, `µ(a₁ > K) = O(1/K)`; the finitely many small `n` are absorbed into the
compact set).  Tightness is precisely the hypothesis Airey–Mance add in their **Theorem
A** (and Theorem B, stated for the Gauss map itself).  But that argument is **nowhere in
the paper**, and it is a real lemma, not a typo fix.

Consequences, in order of who cares:
- **Formalizing §3 (Route A pre-req, and the "formalize Vandehey" target on the shelf)
  now owes an extra obligation**: state the *corrected* hot-spot criterion with the
  tightness hypothesis, and prove tightness of the empirical measures of a CF-normal
  point.  Our pin note's dependency list said "P-S criterion (self-contained counting
  lemma)" — that was written against the broken statement.  Budget the tightness lemma.
- Nobody appears to have written this down: the erratum's own citers are Farhangi–Mance,
  Seiller–Simonsen, Nandakumar et al., and one unrelated paper — none mentions Compositio
  2017.  This is a live **literature hole** of the [[formalization-literature-holes]]
  kind, found by crawling rather than by proving.
- ✅ **Our landed work is unaffected**: the only hot-spot machinery in this repo is
  `HotSpot.lean`, base-`b` (Bailey–Misiurewicz, compact alphabet), where the
  Moshchevitin–Shkredov defect does not arise.

### 6.2 Route B / B6 has a paper-level precedent — cite it, do not claim around it

**Becher–Madritsch, *On a question of Mendès France on normal numbers***
(arXiv:2108.06804, 2021) construct a **computable** `x` such that **`x` and `1/x` are
both CF-normal and normal to every integer base**.  Read the content correctly: CF
normality of `1/x` is free (inversion is the det = ±1 / Serret case), so their theorem is
the *base-b* half — but the **method is exactly B6's play**: build one explicit witness
that survives a map which is not known to preserve normality, by refining intervals under
two incommensurable digit systems at once.  It is Becher–Yuhjtman-family machinery, which
we have now formalized.  Implication: B6's framing is "first *formalization*, and the
first witness for an **affine** `ψ(x) = qx + r`", not "first witness for any map".

### 6.3 A shovel-ready adjacent target: CF-Pillai

**Nandakumar–Pulari–Vishnoi–Viswanathan, *An analogue of Pillai's theorem for continued
fraction normality…*** (arXiv:1909.03431, Bull. LMS 2021): overlapping-occurrence and
disjoint-occurrence CF-normality coincide, and the proof needs genuinely different
technique from base-`b` "since the continued fraction expansion utilizes a countably
infinite alphabet, leading to a non-compact space" (same wall as §6.1).  They also reprove
Heersink–Vandehey from it.  We formalized **base-`b` Pillai from scratch** during B5′
(`Pillai.lean`, not in mathlib) — the CF analogue is self-contained, sits directly on our
`CFCylinder`/`CFDigitLaw` stack, and is the cheapest publishable-adjacent thing in this
whole cone.

### 6.4 The rest of the cone (nothing to act on, recorded so we do not re-crawl)

- **Carton–Vandehey**, *Preservation of normality by non-oblivious group selection*
  (arXiv:1905.05801, Theory Comput. Syst. 2020) — uses Theorem 3.1 verbatim with the fiber
  = states of a **finite automaton**.  Together with Vandehey's own arXiv:1607.03531
  (Theorem 3.1 re-run over base-`b`), this confirms the pattern: **every application of
  Theorem 3.1 in print uses a FINITE fiber**.  Route A's compact-fiber version is
  unexplored territory, not a gap someone quietly filled.
- **Blackman**, *A geometric interpretation of the p-adic Littlewood conjecture*
  (arXiv:1809.09670) and **Blackman–Kristensen–Northey** (arXiv:2306.09853, 2023) — an
  independent, *geometric* realization of the "multiply a CF by an integer" transducer
  (Raney automata, cutting sequences on the Farey complex), driven by p-adic Littlewood.
  Live community working on Vandehey's §2 layer with different tools; a real contact
  point if Route A ever needs the transducer drawn geometrically.
- **Jackson–Mance–Vandehey** (arXiv:2111.11522) — CF-normal vs base-`b` normal are
  maximally separate; see §4½ correction above.
- **Dajani–Kraaikamp–Nakada–Natsui** (arXiv:2405.10921, 2024) — the set of α-CF normal
  numbers does **not** depend on `α ∈ (0,1)`; the transfer-between-CF-algorithms line.
- Airey–Jackson–Mance (complexity), Lukyanenko–Vandehey (Iwasawa CF ergodicity),
  Vandehey (uncanny subsequences), Steiner (numeration-systems survey) — passing cites.
