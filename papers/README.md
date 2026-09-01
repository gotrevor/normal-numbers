# `papers/` — the pinned literature corpus 📚

**Start here before any literature question in this repo.**  Each source we actually
*read* gets a pin note (`<author>-<year>-<slug>.md`) beside its PDF (PDFs are gitignored,
the notes are the durable artifact).  A pin note records what the source proves, in our
notation, plus the parts we depend on — so a statement can be checked against print
without re-reading the paper.

## The corpus

| Pin note | Source | Why it is here |
|---|---|---|
| `bailey-misiurewicz-2006-hot-spot.md` | Bailey–Misiurewicz, *A strong hot spot theorem*, Proc. AMS 134 (2006) | The hot-spot criterion behind `HotSpot.lean` and Stoneham.  **Base-`b`, i.e. compact alphabet** — see the erratum note below for why that matters |
| `becher-yuhjtman-2019-abs-normal-cf-normal.md` | Becher–Yuhjtman, IMRN (arXiv:1704.03622) | The B5′ theorem: absolutely normal ∧ CF-normal.  Tier 1 formalizes exactly this |
| `scheerer-2017-cf-abs-normal.md` | Scheerer (arXiv:1701.07979) | The same conjunction by a different route; not chosen (heavier imports) |
| `vandehey-2017-matrix-actions-cf-normality.md` | Vandehey, Compositio 153 (2017) (arXiv:1504.05121) | CF-normality survives every integer matrix action.  Its §7 problem 1 is the **B6 target**; its §3 is the Route-A engine |
| `vandehey-2017-open-problem-attack-map.md` | *(our analysis, not a source)* | How one would actually attack §7 problem 1: Route A (compact fiber, paper-track) vs Route B (= B6, the witness).  **§6 holds the 2026-08-24 citation crawl** |
| `fisher-schmidt-2014-approximants-geodesic-flows.md` | Fisher–Schmidt, ETDS 34 (2014) (arXiv:1208.0131) | Vandehey's Remark 4.2 points at it.  Read in full 2026-08-24: **not usable for Route A** |
| `literature-review.md` | *(our synthesis)* | The route-oriented read across the corpus — what the sources *collectively* say.  The next reflection lap inherits it |
| `mahler-1973-digits-of-multiples.md` | Mahler, Bull. Austral. Math. Soc. 8 (1973) | Original multiplier theorem.  Theorem 2 already puts every fixed-length word into one multiple |
| `alon-peres-1992-uniform-dilations.md` | Alon–Peres, GAFA 2 (1992) | Corollary 7.2 and its remark: all digits in one multiple; good multipliers have density one |
| `berend-boshernitzan-1994-mahler-multiples.md` | Berend–Boshernitzan, Acta Arith. 66 (1994) | The exact classical identification `M(3,1)=2`, hence tower claim C1 |
| `berend-boshernitzan-1995-complicated-decimal-expansions.md` | Berend–Boshernitzan, Acta Math. Hungar. 66 (1995) | Saturating multiplier sets and why finite sets can only solve a bounded-word-length truncation |
| `adamczewski-bugeaud-2005-decimal-expansion.md` | Adamczewski–Bugeaud (2005) | Citation-cone survey read; complexity/transcendence, no fixed finite multiplier theorem |
| `waldschmidt-2009-words-and-transcendence.md` | Waldschmidt (arXiv:0908.4034) | Survey of the word/transcendence neighborhood; no tower subsumption found |
| `meher-kumar-thangadurai-2017-mahler.md` | Meher–Kumar–Thangadurai, Proc. AMS 145 (2017) | Conditional frequency refinement under source zero-block hypotheses |
| `thangadurai-tripathi-2025-mahler-ii.md` | Thangadurai–Tripathi, Proc. Indian Acad. Sci. 135 (2025) | Explicit multiplier interval, again conditional on source digit patterns |
| `tower-forward-citation-crawl-2026-08-30.md` | *(our cited-by ledger)* | Three-index forward crawl of all eight tower seeds, including every hit, false positive, body-read verdict, and access gap |
| `kelly-le-2013-uniform-dilations-higher-dimensions.md` | Kelly–Le, JLMS 88 (2013) | Strongest higher-dimensional Alon–Peres descendant; still chooses from an infinite matrix family |
| `kra-1999-furstenberg-diophantine.md` | Kra, Proc. AMS 127 (1999) | Only substantive B-B 1995 citer; nonlacunary semigroup density, not a finite hitting set |
| `hong-zheng-2024-g-decimal-function-fields.md` | Hong–Zheng (2024) | Closest later Mahler analogue, over function fields |
| `bulinski-fish-2022-unipotent-glasner.md` | Bulinski–Fish, Israel J. Math. 255 (2023) | Polynomial matrices and unipotent group actions |
| `bulinski-fish-2023-glasner-products.md` | Bulinski–Fish, Math. Z. 303 (2023) | Product Glasner actions, the closest two-track-looking descendant |
| `dong-2019-density-infinite-subsets-I.md` | Dong, DCDS 39 (2019) | Glasner property for `SL(n,Z)` torus actions |
| `dong-2019-density-infinite-subsets-II.md` | Dong, Proc. AMS 147 (2019) | Glasner actions on homogeneous spaces and tori |
| `badea-grivaux-2024-times-p-times-q.md` | Badea–Grivaux, Discrete Analysis (2024) | Times-`p`, times-`q` measure rigidity; Alon–Peres is background only |
| `rajchert-2025-glasner-prime-matrices.md` | Rajchert, IJNT 21 (2025) | Quantitative polynomial prime-entry matrix actions |
| `le-liu-wooley-2025-function-field-equidistribution.md` | Le–Liu–Wooley, Adv. Math. 479 (2025) | Function-field equidistribution and Glasner sets |
| `kra-schmieding-2026-invariant-random-compacts.md` | Kra–Schmieding (arXiv:2605.03993) | Multiplicatively large successful dilations under entropy/invariance hypotheses |
| `peres-yang-2026-maximal-gaps.md` | Peres–Yang (arXiv:2606.28860) | Almost-everywhere gap laws for growing lacunary dilation families |
| `../docs/tower-novelty-audit-2026-08-29.md` | *(our synthesis)* | Claim-by-claim correctness and novelty audit for C1–C10 and the flagship |

## Standing findings (2026-08-24 crawl) — read before re-searching 🕸️

Four results that a future exploration should not have to rediscover.  Detail and
evidence in `vandehey-2017-open-problem-attack-map.md` §6.

1. 🚨 **Vandehey's Lemma 3.2 is false as stated.**  It rests on Moshchevitin–Shkredov
   Theorem 1, which **Airey–Mance** (arXiv:1912.10265, Math. Notes 108 (2020)) refute on
   **non-compact** spaces — and the CF alphabet is countably infinite, hence non-compact.
   Their counterexample `x₀ = (1,2,3,4,…)` satisfies his hypothesis vacuously.  Theorem 1.1
   survives, but only via a **tightness** lemma the paper never proves, so **formalizing §3
   owes that lemma**.  Our `HotSpot.lean` is base-`b`/compact and is unaffected.
2. **§7 problem 1 (quadratic-irrational LFTs) is untouched since 2017 (~90%).**  The
   citation cone is 9 papers, all citing in passing, and **every published use of Vandehey's
   Theorem 3.1 has a FINITE fiber** — the compact-fiber generalization Route A wants is
   unexplored, not quietly filled.
3. **B6 has a paper-level precedent: Becher–Madritsch** (arXiv:2108.06804, 2021) build a
   computable `x` with `x` and `1/x` both CF-normal and absolutely normal.  Same
   witness-for-a-map play, Becher–Yuhjtman-family machinery.  Frame B6 as *first
   formalization + first **affine** witness*, never as first witness of any kind.
4. **`CF-Pillai` is a shovel-ready adjacent target**: Nandakumar–Pulari–Vishnoi–Viswanathan
   (arXiv:1909.03431, Bull. LMS 2021) prove the CF analogue of Pillai's theorem
   (overlapping ≡ disjoint occurrences), explicitly wrestling the same non-compactness.
   We formalized base-`b` Pillai from scratch in `Pillai.lean`; the CF version sits directly
   on `CFCylinder` + `CFDigitLaw`.

## How to run a citation crawl here 🔧

The 2026-08-24 crawl, as a recipe — cheap to re-run when a target's status matters.
No API keys.  Order matters: aggregators first (they bound the work), then arXiv, then a
PDF-level read of the citing papers (that is where finding #1 came from — it is invisible
to titles and abstracts).

```bash
# 1. resolve the work, then its forward cone (OpenAlex)
curl -s "https://api.openalex.org/works?filter=title.search:<TITLE>&mailto=<email>"
curl -s "https://api.openalex.org/works?filter=cites:<W-ID>&per_page=50&mailto=<email>"

# 2. second aggregator (Semantic Scholar) — usually a slightly larger cone
curl -s "https://api.semanticscholar.org/graph/v1/paper/DOI:<doi>/citations?fields=title,year,authors,externalIds,venue&limit=100"

# 3. the author's own trajectory + the subject frontier (arXiv API, metadata only)
#    search_query=au:"<Name>"   |   abs:"continued fraction" AND abs:"normal number"

# 4. READ THE CITING PAPERS.  Download each citing arXiv PDF, pdftotext -layout, and grep
#    for how they use the cited result, not just that they cite it.
```

⚠️ **Instrument hygiene** (each of these bit us once):
- **Google Scholar is unreachable** from a Claude session.  The cone above is therefore a
  *floor*: theses and unindexed preprints can hide there.  Say "no citing work found",
  never "nobody has done this".
- **Unpaywall and Semantic Scholar's OA field are ONE instrument** — S2 sources its OA
  status from Unpaywall, so "both say it is free" is a single claim.  The live page decides.
- A citing paper's **bibliography entry proves nothing** about engagement.  Grep the body.
- zbMATH's review (free API, `api.zbmath.org/v1/document/_search`) is a useful third read
  on what the *published* version says when the PDF is gated.

## Access notes

- **Vandehey 2017 published version is still unread**: Unpaywall flags it bronze-OA at
  Cambridge, but the live page refuses access (Cambridge was mid-"Temporary Disruption",
  2026-08-24), and Cornell's Shibboleth is not registered with Cambridge Core
  (`SHIBBOLETH_NOT_FOUND`).  **All pin-note claims about this paper are against arXiv v1**,
  which is stated inside each claim.  Retry reminder set for 2026-09-07; the fallback is to
  ask the author for a reprint.
- AMS journal backfiles (Proc. AMS etc.) are free in a **browser** — Cloudflare fakes a
  paywall for `curl`, which cost us an hour once on Bailey–Misiurewicz.
