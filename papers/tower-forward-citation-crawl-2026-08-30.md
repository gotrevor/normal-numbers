# Tower forward-citation crawl, 2026-08-30 🕸️

This is the durable record of the **cited-by search** requested after the initial
tower novelty audit.  “Forward citation” here means a later work that cites one of
our seed papers.  It is the reverse direction from reading a paper's bibliography.

## Scope and method

The seed set was the eight papers downloaded for the tower audit:

1. Mahler 1973;
2. Alon-Peres 1992;
3. Berend-Boshernitzan 1994;
4. Berend-Boshernitzan 1995;
5. Adamczewski-Bugeaud 2005;
6. Waldschmidt 2009;
7. Meher-Kumar-Thangadurai 2017;
8. Thangadurai-Tripathi 2025.

For every seed that the service could identify, the crawl queried OpenAlex,
Semantic Scholar, and OpenCitations COCI.  The result counts below are raw index
records, not deduplicated works.  Different years can denote an arXiv version and
its later publication, and Semantic Scholar contains a few duplicate or
bibliography-only records.

| Seed | OpenAlex | Semantic Scholar | COCI | Notes |
|---|---:|---:|---:|---|
| Mahler 1973 | 10 | 11 | 6 | DOI resolved in all three |
| Alon-Peres 1992 | 14 | 22 | 16 | broadest cone; one malformed COCI record |
| B-B 1994 | 4 | 6 | 4 | all substantive hits read |
| B-B 1995 | 1 | 2 | 1 | one substantive hit, Kra 1999 |
| Adamczewski-Bugeaud 2005 | unresolved | 6 | no DOI | obscure proceedings metadata |
| Waldschmidt 2009 | 6 | 12 | 0 | duplicate Russian/English records |
| Meher-Kumar-Thangadurai 2017 | 1 | 1 | 1 | only the 2025 sequel |
| Thangadurai-Tripathi 2025 | 0 | 0 | 0 | no citing work indexed |

The crawl then did four checks that a citation graph alone does not supply:

- exact-title searches for both Berend-Boshernitzan papers;
- a full-text search for their notation `M(g,k)`;
- subject searches in zbMATH for digits of irrational multiples and Mahler's
  `g`-adic problem;
- body-level reading of every hit whose theorem shape could plausibly touch a
  fixed multiplier family or a higher-dimensional linear-form statement.

Semantic Scholar rate-limited the final free-text query batch.  OpenAlex and
zbMATH supplied the corresponding subject searches, so the failure is recorded but
is not counted as an independent negative result.

## Mahler 1973 cone

The deduplicated union contains:

- Mahler's 1982 mathematical memoir and a 1991 obituary;
- Michel Mendes France, “A Diophantine Problem” (1989);
- Alon-Peres 1992;
- Berend-Boshernitzan 1994 and 1995;
- the 1997 German book chapter “Interessante reelle Zahlen”;
- Adamczewski-Bugeaud 2005;
- Waldschmidt 2009;
- a references-only record for Bugeaud's 2012 book;
- Meher-Kumar-Thangadurai 2017;
- Thangadurai-Tripathi 2025.

The Mendes France chapter was gated, but zbMATH's full review identifies its main
result: an operator estimate with consequences for Pisot numbers, using Mahler only
as an ingredient.  The memoir, obituary, and bibliography-only book records do not
advance the multiplier problem.  Every theorem-level digit-expansion paper in this
union is pinned separately in this directory.

The exact subject search also surfaced Mahler's 1974 paper “On the digits of the
multiples of an irrational p-adic number.”  It is a positive-characteristic/p-adic
analogue, not a real fixed-multiplier refinement.  The publisher reports no open
copy, so no PDF was archived.

## Alon-Peres 1992 cone

This cone is large because the paper founded a quantitative Glasner-method branch.
The plausible theorem-neighborhood hits were:

- Berend-Boshernitzan 1995, already pinned;
- Nair-Velani 1998, polynomial values at primes;
- Konyagin-Ruzsa-Schlag 2000, uniformly distributed real dilates of finite integer
  sequences;
- Kamarul Haili-Nair 2003, quantitative Glasner criteria for integer sequences;
- Kelly-Le 2013, polynomial matrix dilations between higher-dimensional tori;
- Le-Liu-Wooley 2013/2025, function-field equidistribution and Glasner sets;
- Dong's two 2017/2019 papers on group actions and homogeneous spaces;
- “On uniform distribution of polynomials and good universality” (2018);
- Bulinski-Fish 2022/2023 on unipotent, linear-group, and product Glasner actions;
- Badea-Grivaux 2024 on times-`p`, times-`q` invariant measures;
- Rajchert 2025 on polynomial prime-entry matrices;
- Kra-Schmieding 2026 on invariant random compacts;
- Peres-Yang 2026 on maximal gaps of lacunary dilates.

All accessible papers in that list were read at theorem/body level and archived
locally.  For the inaccessible older trio, the conclusion was checked against full
zbMATH reviews and against later papers that restate their theorems:

- **Nair-Velani 1998:** `f(p)` is an infinite Glasner set with a quantitative
  cardinality threshold.
- **Konyagin-Ruzsa-Schlag 2000:** given a finite real/integer sequence, choose a
  real dilate making it close to uniformly distributed; the bounds depend on the
  sequence length.
- **Kamarul Haili-Nair 2003:** an infinite integer sequence satisfying two uniform
  distribution conditions is a quantitative Glasner set.

Every one of these theorems retains an existential choice from an **infinite** set
of multipliers, matrices, or group elements.  None replaces that infinite choice by
a universal two-element set.  The higher-dimensional papers likewise choose a
matrix/group element from an infinite action; they do not state a disjunction among
a prescribed finite list of two-real linear forms.

The remaining indexed records are citation noise or use an Alon-Peres estimate far
from the number-theoretic theorem: proper holomorphic maps (1996), interval-graph
algorithms (1997), non-averaging subsets (1999), CR manifolds (2001), invisible
runners over finite fields (2008), random Cayley graphs (2013), arithmetic Kakeya
(2018), stable super-resolution (2020), and linear hashing (2026).  A Penn State
dissertation concerns group-action density but states no fixed-multiplier theorem.

One COCI record has no citing DOI or title.  Its year is 2024 and it adds no
identifiable work beyond the OpenAlex/Semantic Scholar union.

## Berend-Boshernitzan cones

The 1994 paper's union is especially diagnostic because it introduces `M(g,k)`:

- Berend-Boshernitzan 1995;
- Adamczewski-Bugeaud 2005;
- Waldschmidt 2009;
- the references section of Bugeaud's 2012 book;
- Meher-Kumar-Thangadurai 2017;
- Thangadurai-Tripathi 2025.

Every substantive item was read.  None improves the exact `M(3,1)=2` statement to
an all-digits fixed pair or studies simultaneous two-real forms.

The 1995 paper has one substantive direct citer, Kra 1999, plus the same
references-only book record.  Kra proves density for infinite nonlacunary
multiplicative-semigroup expressions, not a bounded hitting family.

The exact full-text search for `M(g,k)` returned Berend-Boshernitzan 1994 as the
only mathematically relevant work.  The exact-title search for “Numbers with
complicated decimal expansions” returned only that paper and Kra 1999.  This is
stronger evidence than relying on either citation index alone.

## Later-seed cones

Adamczewski-Bugeaud 2005 is cited by surveys and books on numeration, words, and
Cobham-type results, plus a paper on p-adic Ruban continued fractions.  Waldschmidt
2009 is cited by books/surveys on automata and transcendence, work on near-periodic
sequences and the Kempner number, and unrelated spectrum-problem records.  No hit
studies a finite universal multiplier family.

Meher-Kumar-Thangadurai 2017 is cited only by Thangadurai-Tripathi 2025.  The 2025
paper has no indexed citers as of the crawl date.

## New mathematical information from the citing papers

The forward cone did add genuine context, even though it did not kill a surviving
tower claim:

1. **Higher-dimensional Glasner theory is extensive.**  Kelly-Le, Dong,
   Bulinski-Fish, and Rajchert make it unsafe to call “move an infinite torus set by
   a matrix until it is dense” a new idea.
2. **The quantifier distinction is the novelty-bearing point.**  Those results
   choose from an infinite acting family.  C2 asks one fixed pair to work for every
   irrational, and the two-track tower claims prescribe every allowed linear form
   in advance.
3. **Hong-Zheng 2024 is the closest later Mahler analogue.**  It obtains all fixed
   length words in one polynomial multiple over a function field, with a uniform
   size bound.  It does not supply a fixed two-element real family.
4. **Kra-Schmieding 2026 proves multiplicative largeness under entropy and
   invariance hypotheses.**  This is stronger than bare existence in that special
   dynamical setting, but it does not apply to every irrational orbit.
5. **A finite union of lacunary sequences is not a Glasner set.**  Badea-Grivaux
   cite this negative result.  It concerns arbitrary epsilon-density and therefore
   does not rule out a fixed family for the coarse length-one digit problem.

## Effect on the novelty judgment

No direct citer, exact-notation hit, or body-level descendant states C2's pair
`{2,11}` or a theorem that implies it.  No inspected source states a fixed finite
two-real linear-form digit-recurrence disjunction of the flagship/C6/C7/C10 type.

The post-crawl estimates that the exact statements are absent from the inspected
literature are **75% for C2** and **70% for the exact two-track families**.  The
confidence is not higher because Google Scholar was unavailable, MathSciNet has no
open cited-by API, some older books/chapters are gated, and non-English or poorly
indexed literature can escape all three graphs.

This is a complete **first-hop cited-by crawl of the eight defined seeds**, plus
targeted snowballing through every plausible theorem-level descendant.  It is not
the recursive transitive closure of every citing paper.  That closure rapidly enters
general harmonic analysis, dynamics, combinatorics, and computer science and does
not define a finite literature search.  It is also not proof of priority.  Before a
public “first” claim, an expert should still check MathSciNet/zbMATH reviews by hand
and Google Scholar from an ordinary browser.

## Local archive status

The eight original PDFs and twelve accessible forward-cone PDFs are present beside
their pin notes in `papers/`.  PDFs remain gitignored by repository policy; the pin
notes, hashes, theorem summaries, access failures, and this crawl ledger are tracked.

Unavailable full texts recorded above:

- Mendes France 1989, closed book chapter;
- Berend-Peres 1993, closed journal article surfaced while snowballing;
- Nair-Velani 1998, AMS/ResearchGate endpoints rejected automated download;
- Konyagin-Ruzsa-Schlag 2000, closed journal article;
- Kamarul Haili-Nair 2003, closed journal article;
- Mahler 1974 p-adic analogue, closed journal article;
- the 1997 German book chapter.

For each theorem-bearing inaccessible item, the ledger says exactly which secondary
review or later restatement was used.  No inaccessible item is silently treated as
having been read in full. 🪷

