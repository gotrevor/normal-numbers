# Literature review — route synthesis for the B5′ witness

*Created 2026-08-23 (reflection lap) from the on-disk `papers/` corpus. This is
the route-oriented read: what the sources COLLECTIVELY say about the open
strategic questions, not a per-paper summary (those are the sibling `.md`s).
Keep it current — the next reflection lap inherits THIS read.*

## ⚠️ Two campaigns live in this file

The synthesis below (`## The strategic question` onward) is the **B5′ / normality**
campaign — Becher–Yuhjtman, Scheerer, image-Khinchin.  That campaign is **CLOSED
and axiom-clean**; keep the section as the record of how its route was chosen.
The **live** campaign since 2026-09-14 is **G4 disjunctivity**; its route synthesis is the
section immediately below (added 2026-09-14 reflection lap; it was missing, which is why
nine grind laps judged the route from handoffs instead of from sources).  The
Mahler-multiplier chapter that follows it is COMPLETE and kept for provenance.

## G4 disjunctivity chapter — route synthesis (2026-09-14 DEEP REFLECTION lap)

*This section was MISSING until 2026-09-14, which is why nine grind laps judged the route
from handoffs rather than sources.  The `papers/` corpus contains **no** source on the
prime-Lambert constants; the route's only external anchors are the campaign brief's own
citations plus what a web sweep turns up.  Stated plainly so the next lap does not mistake
"nothing on disk" for "nothing exists".*

### The strategic question

Is `G₄ = ∑_{p prime} 1/(4ᵖ−1) = ∑_{n≥1} ω(n)/4ⁿ` **disjunctive** in base four (every finite
base-four word occurs), hence in base two?  Disjunctivity is strictly stronger than
irrationality: an irrational expansion may omit finite words.

### What the sources actually give

| claim | source | status | this repo |
|---|---|---|---|
| **irrationality** of the base-two prime-Lambert constant, with the remark that any integer base `≥ 2` may replace `2` | **Tao–Teräväinen**, arXiv 2512.01739, Thm 1.3 + following remarks (per the campaign brief §1; PDF **not on disk**) | proved | *not inherited* — the G4 route deliberately avoids their two-point correlation input |
| `L_{b,r}` (a **power**-Lambert constant, `PowerLambert.powerLambert_full_theorem`) is `b`-disjunctive and `b`-nonnormal, Lean-verified, hypotheses `2 ≤ b`, `2 ≤ r` | `github.com/CaptainSude/generalized-Lambert-disjunctivity-and-nonnormality` (web sweep, 2026-09-14) | proved (Lean) | **different constant** — its index set is the sparse/lacunary `r`-power set, whose congruence structure forces words directly.  Ours is indexed by the **primes**, where `ω(n) ≍ log log n` is far more rigid and no congruence argument reaches it. |
| divisor-Lambert `∑_{n≥1} 1/(bⁿ−1) = ∑ d(m)/bᵐ` (Erdős) | classical | irrationality proved | not this constant; `d(m)` is wildly varying, `ω(m)` is not |

**Decisive source-grounded finding**: there is no source to copy.  The nearby Lean
precedent (`L_{b,r}`) and the nearby analytic precedent (Tao–Teräväinen irrationality) are
both about *easier or weaker* statements.  The prime-indexed disjunctivity must be
originated, and this campaign is originating it.  The brief itself is explicit that the
argument is a **candidate**, model-generated, never externally validated — Lean is the
validator, and the campaign must never report the conditional wiring theorem as the
endpoint.

### Feasibility read (2026-09-14, and this is the part that changed)

After ten laps the picture is no longer "an unproved analytic program".  Every named input
of brief §4 — exact affine Lambert transport (A), the zonotope/spectral tube volume (B),
uniform joint small-prime Fourier control (C), the three-range remainders and far tail (D),
and product-Fejér smoothing (E) — is a **machine-checked theorem about one concrete frame**,
`#print axioms`-clean.  The residue is brief §5 alone: a finite list of explicit real
inequalities (`ScheduleWitness`).

The reflection lap re-derived all five from the Lean definitions.  They close, and the
*shape* of the remaining risk changed accordingly: it is no longer "is the mathematics
right?" but "do the constants close simultaneously?", which is checkable.  Two recorded
parameter values were refuted this lap (`lam = 1` ⇒ `hbudget` false; `N ≈ 10K log K` ⇒
`hfar` false), and a two-sided window on `K` was found —
`0.58 log log L ≲ K ≲ log L/(2 log log L)` — whose **lower** edge (the medium-prime
`8^{−K/2}√(log Mc)` term) is the real reason the brief forbids freezing `K`.

### What is still missing from the on-disk corpus

1. **Tao–Teräväinen arXiv 2512.01739** — cited by the brief for the irrationality baseline
   and for "any integer base ≥ 2".  Not on disk; worth an `ON-LINE-REQUEST` if a novelty
   claim is ever contemplated.  It is *not* a prerequisite for the proof.
2. Any literature on disjunctivity of prime-indexed lacunary series.  The web sweep found
   none; absence of evidence, recorded as such.
3. A source for the entropy consequence (`Ent₂(Z) ≥ mH − O(H√K)`) in the expansion ladder.
   That ladder rung is explicitly *not* ordinary normality and must never be reported as it.

### Claim hygiene, standing

No novelty claim.  The brief's own assessment ("90% confidence this warrants a focused
campaign; that is **not** a probability that the candidate is correct or historically new")
is the ceiling on what may be said.  State OUR quantifiers, never attribute; no publishing,
no outreach.

## Mahler chapter — route synthesis (2026-09-08 reflection lap)

### The strategic question

Pin `M(g,k)` := the least `M` such that for **every** irrational `α` and **every**
length-`k` base-`g` block `w`, some `1 ≤ m ≤ M` has `w` occurring infinitely often
in `m·α`.  Upper bounds are covering arguments; lower bounds are explicit
constructions of one `(α, w)` defeating every `m ≤ M`.

### What the on-disk sources actually give

| claim | source | status in the literature | this repo |
|---|---|---|---|
| `M(g,k) < g^(2k+1)` | **Mahler 1973** Thm 1 (`mahler-1973-digits-of-multiples.md`) | proved | `mahler_multiplier`, sharpened |
| `M(g,k) < 2g^(k+1)` | **B–B 1994** Thm 1.1 (`berend-boshernitzan-1994-mahler-multiples.md`) | proved | `Literature.berendBoshernitzan_bound_holds` |
| **`M(g,k) < g^(k+1)`?** | **B–B 1994, stated OPEN** | open | ✅ **PROVED** here (`mahler_multiplier_lt`) |
| `M(g,k) ≥ a(gᵏ−1)`, `a ∣ g` proper | B–B 1994 Thm 3.1 | proved | subsumed by `mahler_lower_bound_smooth` |
| `M(g,k) ≥ (1−ε)g^(k+1)`, `g` not a prime power, `k ≥ K(ε)` | B–B 1994 Thm 3.2 | proved | `mahler_constant_one_sharp` is stronger (every `k ≥ 1`) |
| **`M(g,1) ≥ (3/2)(g−1)`, odd `g ≥ 5`** | B–B 1994 Thm 3.3 | proved — **LINEAR** | ✅ this repo has **QUADRATIC** `M(p,1) > (⌊p/2⌋²−2)/3` |
| explicit-interval refinement under digit hypotheses on `α` | Thangadurai–Tripathi 2025 (`…-mahler-ii.md`) | proved | not used; does not subsume anything here |
| `M(3,1) = 2` | B–B 1994 p. 318 | proved | `Literature.berendBoshernitzan_M31_lower_holds`; tower C1 was a rediscovery — **cite, never headline** |

**The decisive source-grounded finding**: for PRIME bases the literature's lower
bound is only linear.  The quadratic prime lower bound, the exact `k = 1` census,
and the `g^(k+1)/4` upper bound are all campaign-original.  There is no source to
copy for the lower side — it must be originated, and it has been.

### Where the remaining gap is, and what the sources say about closing it

* `k = 1`, prime `p`: `p²/12 ≤ M(p,1) ≤ p²/4 + O(p)`; census truth `⌊p/2⌋² − O(1)`.
  **The factor 3 is the crux.**  No source addresses it — B–B stop at linear.
* `k ≥ 2`, prime `p`: `p^k − 1 ≤ M(p,k) < p^{k+1}`, a factor-`p` gap and the widest
  in the chapter.  B–B Thm 3.2 covers only non-prime-powers.  Exact `M(7,2) = 176 =
  0.51·7³` refutes the `k = 1` constant `1/4` persisting.  **Untouched; the natural
  second target once `k = 1` is settled.**
* Composite `g`: essentially closed — `mahler_lower_bound_smooth` gives within a
  factor `2` for every composite `g`, and the universal constant `1` is sharp.

### Feasibility read on the `k = 1` crux (2026-09-08, and this is the part that
### changed)

The certificate space is now MAPPED (derivations and validation in
`PENDING_WORK.md` §Reflection 2026-09-08).  Three frames are closed:
orbit-free cycles (refuted — forced to `O(1)` backgrounds, linear cost),
closed-form single backgrounds (ceiling **exactly** `1/12`), single-background
multi-offset cycles (ceiling `1/5`, **no** uniform floor).  The survivor is the
**run+jump chain** — the run of consecutive integers `p−b … b` closed by
`b → p−b` — whose sole arithmetic input is `−1 ∈ ⟨p⟩ (mod b)`, free when
`b ∣ p+1`.  Consequence for the route: `2/9` and `3/16` are reachable
UNCONDITIONALLY (covering every `p ≢ 1 mod 12`), while pushing to `1/4` for ALL
primes needs a divisor of some `p^e + 1` near `p/2` — a prime-in-short-interval /
prescribed-Legendre-symbol statement of Linnik strength with no elementary
substitute (Burgess-type least-non-residue bounds give size `p^{1/4+ε}`, useless
because the constant is `b/p`).  **Precedent check: nothing in the corpus proves,
or attempts, such an unconditional statement.**  So the honest ceiling of the
unconditional wing is a constant below `1/4`, with `1/4` available conditionally
on a cleanly stated arithmetic hypothesis.

## The strategic question

Build ONE explicit real number that is simultaneously **(1) absolutely normal**
(normal to every integer base ≥ 2), **(2) CF-normal** (Gauss–Kuzmin-typical
continued-fraction digit frequencies), and — as a stretch — **(3)
Khinchin-typical** (geometric mean of CF partial quotients → K₀ ≈ 2.6854520).
Existence of such a number is free (a.e. real qualifies); the entire game is
EXPLICITNESS + a machine-checked proof.

## What the sources give — and the Tier 1 / Tier 2 split this forces

| leg | source | status in the literature | our route |
|---|---|---|---|
| abs-normal ∧ CF-normal | **Becher–Yuhjtman 2019** (IMRN; arXiv:1704.03622) | PROVED on paper (O(n⁴) construction) | formalizing it — Tier 1 |
| abs-normal ∧ CF-normal | Scheerer 2017 (arXiv:1701.07979) | PROVED (Sierpiński refinement + large deviations) | not chosen (heavier imports) |
| + Khinchin-typical | **none** | apparently UNPROVEN even on paper | campaign-original graft — Tier 2 |

**The decisive strategic finding (re-confirmed this lap): the conjunction we can
LOCK is Tier 1 (abs-normal ∧ CF-normal), which is exactly the Becher–Yuhjtman
theorem. The Khinchin leg is NOT in B–Y, NOT in Scheerer, and (checked
2026-08-23, abstracts) not claimed anywhere.** It is a genuine original
contribution the campaign hopes to make — "new even on paper, ~90% sound" per
the B–Y pin note's Khinchin-graft section. It therefore carries more feasibility
risk than any remaining Tier-1 bookkeeping, AND it revisits the construction
itself (adds digit caps `D_t` to Def 11's refinement predicate). Consequence for
the route: **lock Tier 1 as a stated, axiom-clean theorem BEFORE grafting
Khinchin** — do not let the stretch destabilize a first-anywhere Tier-1 result.

## Why Becher–Yuhjtman over Scheerer

Both prove the same Tier-1 conjunction. B–Y was chosen because its proof
decomposes into an **elementary layer** (continuant algebra, distortion Lemma 3,
discrepancy concatenation Lemmas 7/9, Hardy–Wright block counting Lemma 8,
t-brick bookkeeping, Prop 12) that IS this repo's established counting culture —
Birkhoff-free and ergodicity-free, exactly like the proven Stoneham route — plus
**exactly two deep imports that serve ONLY the O(n⁴) efficiency claim** (which "a
number in hand" does not need). Scheerer routes through Philipp-style exponential
ψ-mixing + a generic mixing large-deviation theorem — heavier, less aligned with
the repo.

## The two deep imports — and their discharge (both DONE, axiom-clean)

1. **Lemma 4** (Morita 1994 / Vallée 1997 CLT for log qₙ) → fed only Lemma 5
   ("many subintervals of relative order n have length ≈ e^{−2nL}, total mass
   ≥ K|I|/√n"). **Discharged** by an elementary Markov substitute:
   `E[log qₙ | cylinder] ≤ Cn` + the free Fibonacci upper bound — proved in
   `CFDigitLaw` (W2). Worse constants, correctness intact.
2. **Lemma 6** (Kifer–Peres–Weiss 2001 large deviations) — the "one genuinely
   deep ingredient". **Discharged** by proving a self-contained quantitative
   Gauss–Kuzmin / γ-mixing engine: `gaussMeasure_cylinder_mixing` (geometric
   rate (9/10)ᵍ, W4) + Chebyshev (`chebyshev_blockCount`). The construction
   needs only per-stage bad-measure < ¼, so summable correlation decay suffices;
   the proven geometric rate is stronger than needed. Bonus: this engine IS
   Track B's B4 (`gauss_kuzmin`) flag.

**Both discharges are proved and `#print axioms`-clean (trust triple).** So the
Tier-1 headline, when stated, can be trust-triple-only — no cited deep axiom.

## What is precedented vs must-be-originated (for what REMAINS)

- **d-ary simple normality of the witness** (frontier): precedented as B–Y §2.2
  bookkeeping. The single genuinely-new analytic input is the **`m`-growth
  interior estimate** (per-stage base-d digit gain vanishes relative to the
  accumulated count) — must be originated here, but it is the exact analogue of
  the CF interior condition ALREADY closed by the schedule dominance, and all its
  tools are in the repo. The rest of the chain transcribes the proven CF chain.
- **Pillai powers-equivalence** (`simple normal to all bᵏ ⇒ normal to b`):
  classical (Pillai 1940; Niven–Zuckerman; Long), but **NOT in mathlib** (checked
  2026-08-23 — every mathlib "Normal" is order/field/group-normal) and NOT in the
  repo. Must be formalized to state "absolutely normal". Self-contained; the
  repo's `Sandwich`/`Counting` window-frequency machinery may supply pieces.
- **Khinchin graft** (Tier 2): must be originated end-to-end — uniform
  integrability of `log a`, K₀ as a tprod. No source. **Route status (2026-08-24
  reflection):** the graft is realized NOT by hard digit caps `D_t` but by an
  ADDITIVE family of log-tail bad zones in the refinement selection, with measure
  controlled by **Markov's first-moment inequality** on the *nonnegative* tail
  `Σ_{aᵢ>K} log aᵢ` (we need only the `limsup ≤ log K₀` upper direction; the
  lower is free from CF-normality). This is a genuine simplification over the
  originally-planned Chebyshev/variance bound (no two-sided deviation, no L²
  moment machinery beyond `E[log a₁]<∞`). The uniform-integrability transfer to a
  FIXED cutoff is secured by a summable family `(khinchinK j, khinchinEta j)` with
  a geometric coefficient budget `≤1/7` (fixing a real design bug: a level-tied
  cutoff `K_t→∞` never transfers to a fixed external `K`). All the analytic
  machinery is proved axiom-clean; the sole remaining step is wiring it through
  the schedule construction. This is the campaign's original contribution — the
  Markov-tail realization of uniform integrability inside an explicit
  normal-number construction appears nowhere in the sources.

## Related Lean ecosystem (peers, not dependencies)

- `ronut01/erdos1002-lean` (Kwon, Erdős #1002; axiom-clean CI) has the deepest
  Gauss-map machinery in Lean today — exact Gauss-slice masses, quantitative
  Gauss–Kuzmin, Lévy-constant identity, BV Lasota–Yorke + mixing, large
  deviations for log qᵣ. No Khinchin statement. mathlib v4.27 vs our v4.33 — a
  port carries statement-shape risk; we discharged Lemma 6 independently instead.
- mathlib CF library is algebraic only (`GenContFract.of`); no Gauss map / measure.
- Pointwise Birkhoff is in-flight (PR #42078) but the B5′ route is Birkhoff-free.

## Open at the frontier of knowledge (flavor, not blockers)

Whether K₀ is even irrational; whether any naturally-occurring constant is
Khinchin-typical (none proven — the founding hook); whether CF-normality and
base-b normality imply each other pointwise (unknown either direction). None of
these gate the construction — the witness is purpose-built.

## Track C (B6 / Vandehey §7) — what the 2026-08-24 crawl added

The B5′ read above is settled.  The next expedition's literature is crawled and lives in
`vandehey-2017-open-problem-attack-map.md` §6, indexed from `papers/README.md`.  The four
things that change decisions:

| Finding | Consequence |
|---|---|
| Fisher–Schmidt ETDS 2014 has a **finite** fiber, free ergodicity from finite volume, and an a.e. conclusion | Route A gains a sharper statement of its own obstruction, and no machinery.  Do not re-open FS hoping for a Theorem-3.1 analogue |
| Vandehey's **Lemma 3.2 is false as stated** (Moshchevitin–Shkredov Thm 1, refuted on non-compact spaces by Airey–Mance 2019) | Formalizing §3 owes a tightness lemma nobody has written.  Our base-`b` `HotSpot.lean` is unaffected |
| **Becher–Madritsch 2021** already build a witness for a map (`x`, `1/x` jointly CF-normal + absolutely normal) | B6's novelty is *formalization* + the **affine** family, not the witness idea.  Cite them |
| **CF-Pillai** (Nandakumar et al. 2019) exists on paper, unformalized | Cheapest adjacent target on the landed CF stack, and the same non-compactness technology |

Method and instrument caveats (Scholar unreachable; Unpaywall + Semantic Scholar are one
instrument) are recorded once, in `papers/README.md` — re-use that recipe rather than
improvising the next crawl.

## References
See KHINCHIN.md §References and the per-paper `.md` pin notes
(`becher-yuhjtman-2019-*.md`, `scheerer-2017-*.md`, `bailey-misiurewicz-2006-*.md`).
