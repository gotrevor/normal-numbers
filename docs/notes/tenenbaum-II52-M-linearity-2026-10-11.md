# Tenenbaum Thm II.5.2: the error term is linear in M (checked 2026-10-11)

The check behind ledger step 7 (`coefmass-bv-ledger-2026-10-11.md`).  Below is a paraphrase in our
notation with page references; nothing is reproduced from the book.

**Source.**  G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, 3rd ed., AMS
Graduate Studies in Mathematics 163 (2015), DOI `10.1090/gsm/163`, §II.5.2, pp. 280–281.
Trevor and the host session checked it against the page images.

**What the hypotheses require (paraphrase):**
- **Property P.**  A Dirichlet series F has property P with parameters (z, c₀, δ, M) when
  `F(s)ζ(s)^{−z}` continues holomorphically to a zero-free-type region `σ ≥ 1 − c₀/(1 + log⁺|t|)`.
  There it must be bounded by M times a sub-linear power `(1+|t|)^{1−δ}`.
  - P has no separate derivative-summability condition.
- **Type T.**  F is of type T when it has property P and its coefficients are dominated by
  non-negative ones whose series also has property P (with some exponent w).
  - Both series use the same c₀, δ and M.
  - A series with non-negative coefficients is its own majorant.

**What the theorem gives (paraphrase).**  For F of type T and `|z|, |w| ≤ A`, the partial sums are
`x(log x)^{z−1}` times a finite expansion in `1/log x`, plus an error that is **M times** a fixed
decaying function of x.  The constants in that error depend only on c₀, δ and A.  The book notes
that this uniformity in M is used later (§II.6.2).

**Consequences for step 7:**
- **M-linearity holds**, so the S₀- and τ-dependence passes through M exactly as the ledger needs.
- **One shared (c₀, δ, M)** covers F and its majorant.  The ledger takes the max of the two M's and
  the min of the c₀'s and δ's.
- **The bounds must hold on the whole P-region.**  Our bounds are proved on σ ≥ 3/4, so the ledger
  takes c₀ ≤ 1/4 (and c₀ ≤ c(q₀) for the L-function factor).

**How it was found.**  Google Books search-inside (volume `UEk-CgAAQBAJ`) located the pages.
The method is in the KB's Cornell-access leaf.
