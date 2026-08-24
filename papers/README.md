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
