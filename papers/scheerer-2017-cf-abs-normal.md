# Scheerer 2017 — pin note (§1–2 read 2026-08-23)

A.-M. Scheerer, *On the continued fraction expansion of absolutely normal
numbers*, arXiv:1701.07979.  PDF alongside (gitignored).  The predecessor to
Becher–Yuhjtman: same conjunction (absolutely normal + CF-normal), Sierpiński/
Becher–Figueira-style construction, doubly exponential complexity.

## Why we keep it

Its §2 documents the standard *citation chain* for CF large deviations, which
B–Y's Lemma 6 compresses into a KPW reference:

- **Theorem 2.1 (Philipp 1967, Satz 3)**: the CF digits are exponentially
  **ψ-mixing** under the Gauss measure —
  `|μ(A∩B) − μ(A)μ(B)| ≤ ρⁿ μ(A)μ(B)` with `ρ < 0.8`, for `A` in the past
  σ-algebra and `B` in the `n`-shifted future.  (Rate later improved;
  Iosifescu–Kraaikamp Prop 2.3.7.)
- **Theorem 2.2 (Merlevède–Peligrad–Rio, Cor 12)**: generic LD bound for
  bounded α-mixing sequences.
- **Theorem 2.3**: the combination, `μ(bad) ≤ exp(−η N/log N)` — note the
  `N/log N` (not `N`) exponent, an artifact of the generic MPR route.

Also documents (p. 2–3): the open problem "absolutely normal + CF-normal"
appeared in Quéffelec 2006 and Bugeaud's book (Problem 10.49); the base-b
side of his construction is plain Hoeffding for i.i.d. digits (§2.1) — our
W4 can do the same.

## What B5′ takes from this

Nothing load-bearing: our W3 route is self-contained (the `tailDensity`
family + ratio-contraction, see `KHINCHIN.md`), needing neither Philipp nor
MPR nor KPW.  This note exists so the citation chain doesn't have to be
re-excavated, and as the fallback map if the elementary route stalls.
