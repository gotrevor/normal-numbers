# Literature review — route synthesis for the B5′ witness

*Created 2026-08-23 (reflection lap) from the on-disk `papers/` corpus. This is
the route-oriented read: what the sources COLLECTIVELY say about the open
strategic questions, not a per-paper summary (those are the sibling `.md`s).
Keep it current — the next reflection lap inherits THIS read.*

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
