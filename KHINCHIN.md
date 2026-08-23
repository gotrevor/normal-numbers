# Track B — metric theory of continued fractions (Khinchin / Gauss–Kuzmin) 🎲

*Added 2026-08-23 from the Khinchin research session.  This doc is the source of
truth for the track; ROADMAP.md carries only the status line.  Campaign
oversight: `JUDGE.md` (the attended architect/judge charter + ledger).*

## Why this lives in the normal-numbers repo

The programme's real subject is **Birkhoff's ergodic theorem applied to a
measure-preserving map on [0,1]** (Trevor, 2026-08-23).  Normality and the
metric theory of continued fractions are the two classical harvests of that one
machine, applied to two different digit-reading dynamical systems:

| | base-b digits (Track A, existing) | CF partial quotients (Track B, this doc) |
|---|---|---|
| Digit map | ×b: x ↦ bx mod 1 | Gauss map T: x ↦ {1/x} |
| Digit function | ⌊b·T^n x⌋ | aₙ₊₁ = ⌊1/(T^n x)⌋ |
| Invariant measure | Lebesgue | Gauss: dγ = dx/((1+x) ln 2) |
| a.e. theorem | Borel: a.e. x normal | Gauss–Kuzmin freqs; Khinchin (a₁⋯aₙ)^{1/n} → K₀ |
| Explicit witness | Champernowne 1933 | Adler–Keane–Smorodinsky 1981 (CF-normal); Wieting 2008 (Khinchin-typical) |
| Orbit-transfer theorem | Wall: normal ⟺ orbit equidistributed | Vandehey: CF-normality preserved by rational LFTs (⚠️ ~70% on exact scope — pin against the paper) |

And the founding hook has an exact twin.  Track A: no naturally-occurring
constant is proven normal in any base.  Track B: **no naturally-occurring
number is proven to satisfy Khinchin's law** — π, γ, and K₀ itself all track it
empirically, none is proven (the two Numberphile videos below are built on
exactly this).  The precise statement (Wikipedia, citing Wieting 2008): it has
not been proven for *any* real number not specifically constructed for the
purpose — so purpose-built witnesses DO exist, and Wieting's paper constructs
one explicitly.

- 🎥 Numberphile, "2.685 is (almost) everywhere" — https://www.youtube.com/watch?v=-mXaU3N9e8Y
- 🎥 Numberphile, "Khinchin's Constant (extra footage)" — https://www.youtube.com/watch?v=jl8Fk7PPeOc

## The mathematics

**Setup.**  T x = {1/x} on (0,1); aₙ₊₁(x) = ⌊1/(T^n x)⌋ for irrational x.
The Gauss measure γ(A) = (1/ln 2) ∫_A dx/(1+x) is a probability measure on
(0,1), T-invariant, and T is ergodic w.r.t. γ (ergodicity first fully proved
by Ryll-Nardzewski 1951, ~85% on attribution; Rényi 1957 gives the
bounded-distortion route).  Everything below is Birkhoff + one observable:

1. **Gauss–Kuzmin digit law** (observable = indicator of a₁ = k): for a.e. x
   the frequency of quotient k is
   `log₂(1 + 1/(k(k+2)))  =  −log₂(1 − 1/(k+1)²)` — the two forms in
   circulation are equal because `1 + 1/(k(k+2)) = (k+1)²/(k(k+2))` and
   `1 − 1/(k+1)² = k(k+2)/(k+1)²` are reciprocals.  It is exactly
   γ((1/(k+1), 1/k]).  ≈ 41.5% ones, 17.0% twos, 9.3% threes; tail ~ 1/(k² ln 2).
2. **Khinchin's theorem** (observable = log a₁, which is L¹(γ) since
   Σ log k / k² < ∞): for a.e. x, (a₁a₂⋯aₙ)^{1/n} → K₀ where
   `K₀ = ∏ₖ (1 + 1/(k(k+2)))^{log₂ k} ≈ 2.685452001…`.
   The arithmetic mean diverges a.e. (E_γ[a₁] = ∞, that 1/k² tail), which is
   *why* the geometric mean is the headline statistic.
3. **Lévy's constant** (observable = −log x, plus a comparison argument):
   for a.e. x, (1/n) log qₙ → π²/(12 ln 2), i.e. qₙ^{1/n} → e^{π²/(12 ln 2)} ≈ 3.2758.
4. **Historical rate ladder** (for the write-up, not the formalization): Gauss
   stated the digit law in an 1812 letter to Laplace; Kuzmin (1928) and Lévy
   (1929) proved convergence 116 years later; Wirsing (1974) got the sharp
   rate λ ≈ 0.30366 (second eigenvalue of the transfer operator).

**Provable failures** (good test exhibits): rationals (finite CF) and
quadratic irrationals (eventually periodic CF — √2 = [1;2,2,2,…] has geometric
mean 2 ≠ K₀) fail Khinchin's law; e = [2;1,2,1,1,4,1,1,6,…] fails with
geometric mean → ∞ ((2ⁿn!)^{1/3n} ~ (n/e)^{1/3}).  Note √2 and e are
*conjectured normal* in every base — the two a.e. properties come apart
pointwise, in both directions.

**Open, for flavor**: whether K₀ is irrational (even that!), whether any
naturally-occurring constant is Khinchin-typical, whether CF-normality and
base-b normality imply each other pointwise (they don't a.e.-trivially, and no
implication is known).

## Both expansions at once? (2026-08-23 follow-up)

Trevor's question: can a number be *both* normal and Khinchin-typical?

- **Existence is free**: a.e. x is simultaneously absolutely normal, CF-normal
  and Khinchin-typical (intersection of full-measure sets).  Explicitness is
  the whole game.
- **Why cheap constructions fail**: you get to steer exactly ONE expansion.
  Fixing base-b digits determines the CF digits (opaquely) and vice versa —
  the two digit systems don't commute, so concatenation/steering tricks
  control one side and forfeit the other.
- **The research answer — normal + CF-normal is DONE**: Scheerer
  (arXiv:1701.07979) constructs a computable number that is absolutely normal
  (all integer bases) AND CF-normal, via Sierpiński-style interval refinement
  + large deviations for mixing random variables; Becher–Yuhjtman
  (arXiv:1704.03622, IMRN 2019) give a faster construction (~n⁴ operations
  for n CF digits).
- **CF-normal ⇏ Khinchin-typical**: plant digit ⌈e^{2^j}⌉ at position 2^j of
  a CF-normal number — a density-zero change preserves every pattern
  frequency, but the running log-average gains Σ_{j≤J} 2^j/2^J ≈ 1–2 and
  oscillates, so the geometric mean never converges to K₀.  Conversely
  Khinchin ⇏ CF-normal (steer with 2s and 3s only: log 2 < log K₀ < log 3,
  digit-1 frequency 0).  So the conjunction genuinely needs digit-size
  control on top of CF-normality.
- **Apparent literature gap**: neither abstract above claims Khinchin's
  geometric-mean law for its constructed number (checked 2026-08-23; abstracts
  only).  ⭐ **B5′ upgrade**: a machine-checked witness that is
  *absolutely normal + CF-normal + Khinchin-typical* would be a
  first-anywhere exhibit — strictly stronger write-up bait than B5.

## B5′ effort assessment (Becher–Yuhjtman read in full, 2026-08-23)

Full dependency map → `papers/becher-yuhjtman-2019-abs-normal-cf-normal.md`.
Headline: **the paper has exactly two deep imports (Morita/Vallée CLT;
Kifer–Peres–Weiss large deviations), and both serve only the O(n⁴)
efficiency claim** — which "a number in hand" does not need.  Dropping
efficiency, the CLT is replaced by a two-line Markov argument
(E[log qₙ] ≤ Cn elementarily) + the free Fibonacci upper bound, and the LD
weakens to "any summable correlation decay + Chebyshev" (per-stage bad
measure < ¼ is all the construction uses).  Everything else — continuant
algebra, distortion Lemma 3, discrepancy concatenation, Hardy–Wright block
counting, t-brick bookkeeping — is the repo's established counting culture,
Birkhoff-free and ergodicity-free, exactly like the Stoneham route.

Work packages (sizes calibrated against Stoneham = ~1k lines, 2 fable/low
laps off a fully pinned plan):

| WP | Content | Size | Risk |
|----|---------|------|------|
| W1 ✅ | CF cylinder toolkit: continuant α-algebra (Prop 2), distortion (Lemma 3), lengths, Fibonacci bound, Prop 12 — **complete 2026-08-23**, 3 laps, 12/12 axiom-clean (judge-verified) | ~0.8–1.5k lines | low |
| W2 ✅ | digit laws + Markov length substitute for Lemma 5 — **complete 2026-08-23**, 3 laps, 10/10 axiom-clean (judge-verified); `CFDigitLaw.lean` | ~0.4–0.8k | low |
| W3 | **the core**: summable CF correlation decay — route DECIDED, see below; **scaffold staged 2026-08-23** (`CFMixing.lean`, 4 frozen statements incl. the B1 + B4 flags; escape valve on the geometric rate) | ~1.5–3k | **moderate** |
| W4 | LD/Chebyshev assembly + b-ary side (Lemmas 8, 9; overlaps Counting/Visits) | ~0.8–1.2k | low |
| W5 | t-bricks, main lemma (worse constants), schedule, limit x, three correctness proofs, + the Pillai powers-equivalence for "absolutely normal" | ~1.5–2.5k | medium (bookkeeping-dense) |
| W6 | Khinchin graft: digit caps D_t in the refinement + uniform-integrability bookkeeping, K₀ as tprod | ~0.5–1k | medium (new on paper, ~90% sound) |

**Total ≈ 5.5–10k lines, ~8–16 treadmill laps + a few attended
scaffold/judge sessions; calendar ≈ 2–4 weeks of campaign time, dominated by
W3** (estimate confidence ~65%; tail risk = W3 statement-shape + W5
constant-wrangling).  Prize: one artifact = first formalized
absolutely-normal number, first formalized CF-normal number, first
Khinchin-typical witness (the conjunction apparently new even on paper) —
and a natural reach-out to Becher/Yuhjtman/Scheerer.  B2/B3 (ergodicity,
Birkhoff) stay a separate thread; B5′ does not wait on them.

### W3 route — decided 2026-08-23 (pre-flight done)

KPW 2001 has no open-access copy (Springer
https://link.springer.com/article/10.1007/BF02772607, EZproxy-able if ever
wanted) — and it is **non-blocking**: Scheerer's §2 (pin note in `papers/`)
shows the standard chain is Philipp-1967 exponential ψ-mixing + a generic
mixing-LD theorem, both heavy imports, and reading it crystallized a fully
**self-contained elementary route**:

1. The conditional density of `Tⁿx` given `x ∈ I_w` is exactly
   `h_t(y) = (1+t)/(1+ty)²` with `t = qₙ₋₁/qₙ ∈ [0,1]` — two lines from the
   `cylMap` LFT algebra (W1), and `h_t ∈ [1/2, 2]` on the unit square
   (`tailDensity` in `CFDefs.lean`).
2. The transfer operator preserves the cone of `h_t`-mixtures
   (`L h_t = Σₖ P(a=k|t) · h_{1/(k+t)}` — conditioning on one more digit),
   and a Lévy-style ratio-oscillation argument contracts the density
   envelope geometrically (fallback: Kuzmin's `e^{-c√n}` from Khinchin's
   book ch. III — still summable, still sufficient).
3. Summable covariance decay for cylinder events + the W1 distortion lemma
   (conditioned version) + **Chebyshev** give the per-stage bad-measure
   `< ¼` bound — no Philipp, no MPR, no KPW, no exponential LD anywhere.

Bonus: step 2's statement *is* a quantitative Gauss–Kuzmin theorem, so W3
plants Track B's B4 flag as a lemma of the expedition.

### Staged so far (2026-08-23)

- **W1 ✅ COMPLETE** (same day it launched): `CFDefs.lean` (all real bodies)
  + `CFCylinder.lean` — all 12 statements proved in 3 treadmill laps
  (fable/low), statements character-frozen throughout, judge-verified
  axiom-clean (`#print axioms` sweep = the standard triple on every one).
  Highlights: Euler gluing by `cfK.induct` list induction (no `α_{r,s}`
  combinatorics), `volume_cfCylinder` via `bumpLast` endpoints + countable
  junk, distortion pair via the sharper `K(wu) ≤ (K(w)+K(w⁻))K(u)` gluing
  bound.  Judged ledger: `JUDGE.md`.
- **W2 ✅ COMPLETE** (same day, 3 laps): `CFDigitLaw.lean` — all 10 proved,
  statements character-frozen throughout, judge-verified axiom-clean.
  Highlights: the partition crux went through outright cylinder
  measurability (obsoleting W1's "never need measurability" stance);
  `tsum_mul_log_cfK_le` by first-digit peeling + `genConsEquiv`
  reindexing, summability via `log x ≤ 2√x` against the 3/2-p-series.
  Per-lemma record: `archive/handoff/PENDING_WORK-2026-08-23-W2-final.md`.
- **W3 scaffold LIVE**: `CFMixing.lean` (4 sorry'd frozen statements:
  `measurePreserving_gaussMap` = the **B1 flag**; the conditional-density
  identity `|I_w ∩ T^{-|w|}A| = (∫_A h_t)·|I_w|`; `cylinder_mixing` = the
  workhorse — cylinder-conditioned quantitative Gauss–Kuzmin–Lévy with
  multiplicative `1 ± Cρᵏ` envelope, uniform in `w`; `gauss_kuzmin` = the
  unconditioned corollary = the **B4 flag**).  ⚠️ Judge-governed escape
  valve on `cylinder_mixing`: if only Kuzmin's `e^{-c√k}` materializes,
  the judge weakens the rate to summable-error (W4 accepts either).
  Builds green on v4.33.1; 4 kernel-checked anchors frozen (incl. the
  `t = K(w⁻)/K(w)` direction anchor).

## Formalization landscape (surveyed 2026-08-23; greps + searches, not proofs)

**Nothing found in any prover** for Gauss–Kuzmin or Khinchin's theorem, ~92%.
Instruments: reservoir mirror grep (`khinchin|kuzmin`), GitHub code search
(Khinchin, Kuzmin, gauss_kuzmin, GaussKuzmin, "pointwise ergodic", "Birkhoff
ergodic", each per-language), mathlib source + full open/closed PR search,
zulip-ro corpus (both names genuinely absent; bounded by 24 channels/365 days),
web search for AFP/Coq (weak instrument — site-restricted search returned
nothing from isa-afp.org at all, so treat as unseen, not absent).  All
"Khinchin" code hits were Lévy–Khinchine, entropy axiomatics, or the
convergent-recovery bound in a Shor's-algorithm repo — different theorems.

**What exists to build on:**

- **mathlib CF library is algebraic only** — `Mathlib.Algebra.ContinuedFractions.*`
  has `GenContFract.of` (the expansion algorithm) with `of_convergence`;
  no Gauss map, no measure theory.
- **mathlib ergodic infrastructure**: `Ergodic` (Dynamics/Ergodic/Ergodic.lean),
  `birkhoffAverage` (Dynamics/BirkhoffSum/), von Neumann mean ergodic theorem
  (InnerProductSpace/MeanErgodic).  **The pointwise Birkhoff theorem is in
  flight**: PR #42078 (open, touched 2026-08-20, successor to Butterley's
  closed #26923) + maximal ergodic theorem PR #34031 (open).  Standalone Lean
  proofs exist: `lua-vr/pointwise-birkhoff`, `oliver-butterley/BET`.
- **`ronut01/erdos1002-lean`** (Kwon's Erdős #1002 proof; active 2026-08-23;
  2,464 theorems under axiom-clean CI) has the deepest Gauss-map machinery in
  Lean: exact Gauss-measure slice masses (`gauss_slice_real`), quantitative
  Gauss–Kuzmin normalisation (`markTailMean_bounds`, `tendsto_markTailMean`),
  the Lévy-constant identity π²/(12 ln 2) = E_γ[−log] (`LDLyapunov.integral_neg_log_gauss`),
  BV Lasota–Yorke + mixing for the Gauss map, large deviations for log qᵣ
  (`continuant_large_deviation`).  No Khinchin statement — not their target.
  README mentions an independent 1002 formalization by Shouqiao Wang.  These
  are **peers in the same ecosystem**, and their transfer-operator route is
  morally stronger than the bare ergodicity we need — worth reading before
  building, and worth a friendly pointer when our track goes public.

## Plan sketch (dependency order)

- ⬜ **B0 defs**: `gaussMap`, `cfDigit n x` (= ⌊1/T^n x⌋), `gaussMeasure` via
  `Measure.withDensity` — decide interop: our own digit stream vs
  `GenContFract.of` (bridge lemma either way; Track A's Bridge.lean is the
  pattern).
- ⬜ **B1 invariance**: `MeasurePreserving gaussMap gaussMeasure gaussMeasure`.
  A change-of-variables sum over the branches x ↦ 1/(x+k); short.
- ⬜ **B2 ergodicity**: `Ergodic gaussMap gaussMeasure` — **the meat**.
  Routes: (a) Rényi bounded-distortion + Knopp/Lebesgue-density (classical,
  self-contained), (b) transfer-operator à la erdos1002-lean (heavier, more
  reusable).  Start with (a).
- ⬜ **B3 pointwise Birkhoff**: consume mathlib #42078 if merged by then;
  else vendor/adapt a standalone proof behind our own interface so B4 is
  insulated from the mathlib timeline.
- ⬜ **B4 harvests**: Gauss–Kuzmin digit frequencies; `L¹` membership of
  log a₁ + Khinchin's theorem with `K₀` defined by the tprod; Lévy's constant
  (stretch); arithmetic-mean divergence (fun negative).
- ⬜ **B5 exhibit (stretch)**: a machine-checked Khinchin-typical witness à la
  Wieting 2008 — "the number the videos say nobody knows" — strong write-up bait.

## References

- A. Ya. Khinchin, *Continued Fractions*, 3rd ed., Univ. of Chicago Press, 1964.
- T. Wieting, *A Khinchin Sequence*, Proc. AMS 136 (2008) 815–824,
  doi:10.1090/S0002-9939-07-09202-7.  (The purpose-built witness.)
- C. Ryll-Nardzewski, *On the ergodic theorems II* (ergodic theory of continued
  fractions), Studia Math. 12 (1951).  (⚠️ ~85%, verify volume/pages.)
- R. O. Kuzmin (1928); P. Lévy (1929); E. Wirsing, *On the theorem of
  Gauss–Kusmin–Lévy…*, Acta Arith. 24 (1974).  (Rate ladder.)
- R. L. Adler, M. Keane, M. Smorodinsky, *A construction of a normal number for
  the continued fraction transformation*, J. Number Theory 13 (1981) 95–105.
- J. Vandehey, on CF-normality under rational LFTs (~2016; ⚠️ locate the exact
  paper before citing outward).
- A.-M. Scheerer, *On the continued fraction expansion of absolutely normal
  numbers*, arXiv:1701.07979.  (Absolutely normal + CF-normal, computable.)
- V. Becher, S. A. Yuhjtman, *On absolutely normal and continued fraction
  normal numbers*, IMRN 2019(19) 6136–6161, arXiv:1704.03622.  (Same
  conjunction, ~n⁴ operations.)
- M. Iosifescu, C. Kraaikamp, *Metrical Theory of Continued Fractions*, Kluwer
  2002.  (The comprehensive reference.)
- M. Einsiedler, T. Ward, *Ergodic Theory: with a view towards Number Theory*,
  GTM 259, ch. 3.  (Gauss map + Birkhoff route, textbook form.)
