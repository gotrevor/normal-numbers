# Forward-citation sweep — Mahler 1973 / B–B 1994 / A–R 2008 🔎

*2026-08-30, attended session.  Instrument: web search + paper bibliographies +
full-text reads of the local PDFs.  ⚠️ zbMATH and MathSciNet were NOT queryable
(403/paywall), so this is bibliography-graph coverage, not a database
cited-by sweep — absence below is absence in THIS instrument's sight.*

## Headline: Mahler already proved a JOINT all-blocks form — over a huge interval

Mahler 1973 **Theorem 2** (read from the local PDF): for every irrational a and
every N, some X in `[1, g^(2(g^N+N−1)+1))` has **every** length-N block occurring
i.o. in Xa — proof feeds a de Bruijn block through his per-block Theorem 1.  His
base-10, N=1 example: one X < 10²¹ realizes every decimal digit.  He also shows
the joint form fails for every *fixed* X (some α dodges it), so an interval (or
set) is essential.

**Corollary that bounds C2's novelty**: push the all-digits block `012` (k = 3)
through B–B 1994's improved bound `X < 2g^(k+1)`: for every irrational x some
**single m < 162** has `012` (hence all three ternary digits) i.o. in mx.  So
"one multiplier realizes all ternary digits" is CLASSICAL with |S| = 161; C2's
content is exactly the collapse **161 → the explicit pair {2, 11}**.
🚨 Any outward write-up of C2 must state this comparison.

## The definitional fine print on M(3,1) = 2

B–B's M is **per-block**: for every irrational α and every digit d, some m ≤ 2
has d i.o. in mα — *with m allowed to depend on d*.  Our `c1_ternary_digit`
matches this exactly (disjunction per digit).  The joint form (one m for all
digits at once) is what C2 adds; B–B never state it.

## The citing lane (all read or bibliographically placed)

- **Szüsz–Volkmann 1983** (J. Reine Angew. Math. 339, 199–206, "On numbers
  containing each block infinitely often") — the class of reals containing every
  block i.o.; sits between Mahler and B–B.  ⚠️ NOT yet read — GDZ viewer:
  http://gdz.sub.uni-goettingen.de/dms/resolveppn/?PPN=GDZPPN002200279
- **Alon–Peres 1992** (GAFA 2, "Uniform dilations"; local PDF held) —
  quantitative dilations nX mod 1; B–B credit its Cor. 7.2 with a short
  finiteness proof of M(g,k).  Higher-dim: Kelly–Lê 2013 (arXiv:1210.2083).
- **B–B 1994 itself** (local PDF): M(g,k) < 2g^(k+1); lower bounds g^k − 1,
  a(g^k−1), (1−ε)g^(k+1) for g not a prime power, M(g,1) ≥ (3/2)(g−1) for odd
  g ≥ 5; M(3,1) = 2 exact; polynomial Mahler theorem (blocks i.o. in P(m)α).
  Open: is M(g,k) < g^(k+1)?
- **Meher–Senthil Kumar–Thangadurai 2017** (PAMS 145; local PDF) — conditional
  frequency version (zero-block hypothesis ⟹ explicit-ish X with frequency
  ≥ ν/b^(m+1)); notes the per-block/joint gap explicitly.
- **Tripathi 2025** (Math. Student 94; not located online) and
  **Thangadurai–Tripathi 2025** (Proc. Indian Acad. Sci. 135:39; local PDF) —
  explicit *intervals* of X under zero-block hypotheses; still one block, one
  multiplier, one real.
- **A–R 2008** (local PDF) — pattern-shaped disjunctions (7/3-powers; ternary
  squares-or-{010, 02120}); its citation trail runs into the automatic-sequence
  transcendence literature (A–B complexity I/II, both local), not multiplier
  sets.
- Checked-and-distinct: Bloom–Croot (arXiv:2509.02835, small digits of
  integers), ×2×3 two-base rigidity, Bugeaud's Z-number problem.

## Verdicts

- **(a) {2,11}-style explicit joint product block: NOT FOUND** in this
  instrument's sight.  The gap between per-digit M(3,1)=2 and the 161-interval
  de Bruijn corollary appears untouched.  Novelty of C2 = smallness +
  explicitness of the set (plus the kernel certificate).  Confidence limited by
  the zbMATH/MathSciNet blind spot — the operator-owned sweep should hit those
  databases before any outward claim.
- **(b) Two-real linear combinations aX+bY (the adder theorems): NOT FOUND**,
  anywhere in the lane.  Nearest neighbors are dilations nX of one real and
  B–B's polynomial Mahler theorem.  The adder disjunction family remains the
  only statement of its shape we can see.
- **(c) Remaining fetches** (operator, one click each): Szüsz–Volkmann via the
  GDZ viewer above; Tripathi 2025 (Math. Student — try the author's page);
  optionally Bugeaud's 2012 book (staff.dc.uba.ar/becher/aa/Bugeaud2012.pdf)
  for its Mahler-multiples exercises.

## Local corpus status after this sweep

All load-bearing anchors are on disk: Mahler 1973, B–B 1994 (+1995 sequel),
MST 2017, T–T 2025, A–R 2008, A–B complexity I (Annals 2007) + II (CF) + ABL
CRAS 2004, Alon–Peres 1992, Waldschmidt survey.  Missing: Szüsz–Volkmann 1983,
Tripathi 2025.
