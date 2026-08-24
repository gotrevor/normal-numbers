# Fisher–Schmidt 2014 — pin note (read in full 2026-08-24)

A. M. Fisher and T. A. Schmidt, *Distribution of approximants and geodesic flows*,
Ergodic Theory Dynam. Systems **34** (2014) 1832–1848; DOI 10.1017/etds.2013.23;
arXiv:1208.0131v1 (16 pp, numbering below is v1).  PDF alongside (gitignored).
Read because Vandehey's Remark 4.2 says his transducer skew product "bears a
non-trivial resemblance… although there appears to be no direct overlap", and the
attack map wanted to know whether FS already contains a Route-A analogue of his
Theorem 3.1.

## 🔴 Verdict for Route A: it does not, and the premise was wrong

**FS's fiber is FINITE, not continuous.**  The skew product is
`S(A, γ mod H) = (M A E_t, γ M⁻¹ mod H)` on `A × H\Γ`, where `H ⊂ Γ = PSL(2,ℤ)` is a
**finite-index** subgroup, `H\Γ` carries **counting measure**, and `A` is Arnoux's
cross-section of the geodesic flow (Theorem 3).  The attack map's "skew-product with
continuous fiber" is not what this paper has.  Three structural mismatches, each on its
own fatal for reuse:

1. **Fiber is a finite coset space, acting by an invertible group action.**  Vandehey's
   is a finite set of transducer *states* `M_D` under a non-invertible semigroup action
   (µ̃ is not even T̃-invariant, which is why his Theorem 3.1 must construct ρ).  Route A
   wants a compact continuum `W ⊂ PGL₂(ℝ)`.  Nothing in FS is set up to vary the fiber.
2. **Their ergodicity is FREE and comes from finite volume** (Corollary 1 = Hopf's
   theorem: the geodesic flow is ergodic on the unit tangent bundle of any finite-volume
   hyperbolic surface, and a finite-index `H` gives a finite cover).  That hypothesis is
   *exactly* what dies in the quadratic case: over `ℤ[φ]` Dirichlet's unit theorem makes
   the relevant group infinite-index / non-discrete in the real place (Hilbert modular,
   dense projection), so there is no finite-volume quotient to run Hopf on.  FS therefore
   **restates Route A's unit-drift obstruction in geometric language** — a diagnostic
   gain, not machinery.
3. **Their conclusion is almost-everywhere, via BIRKHOFF** (Lemma 6, Corollary 2).
   Vandehey's Theorem 3.1 is pointwise for *each* CF-normal `x`, deliberately avoiding
   Birkhoff (Pyatetskii-Shapiro instead), because Birkhoff says nothing about a specified
   number.  FS never mention normality at all.

So: no Theorem-3.1 analogue, no compact-fiber lemma, nothing to graft.  Vandehey's
"resemblance, no direct overlap" is accurate and the resemblance is genealogical — both
descend from **Jäger–Liardet 1988**, the skew-product-over-the-Gauss-map proof of
Moeckel's theorem (zbMATH's reviewer names Jäger–Liardet as ingredient (i) of Vandehey's
proof).  FS re-derive Jäger–Liardet geometrically; Vandehey upgrades it to pointwise.

## What the paper actually proves

- **Theorem 1 (Moeckel 1982 + Nakanishi 1989, reproved).**  For `H ⊂ SL(2,ℤ)` of finite
  index and a.e. real `x`, the RCF approximants `pₙ/qₙ` are distributed among the cusps of
  `H` proportionally to relative cusp width `w(κ)/[Γ:H̄]`.  For `Γ(m)` this is
  equidistribution of `(pₙ, qₙ) mod m`; `m = 2` gives frequency ⅓ each for
  odd/odd, odd/even, even/odd.
- **Theorem 3** = the lifting lemma above (finite cover ⇒ skew product over the
  cross-section), **Corollary 1** = ergodicity by Hopf, **Lemma 5** = the bookkeeping that
  `proj₂ Sᵏ` is the matrix `(qₖ, −qₖ₋₁; −pₖ, pₖ₋₁)` (columns alternate with parity),
  **Lemma 6** = Birkhoff, **Corollary 2** = Theorem 1 after an `ι = (0 −1; 1 0)` twist
  (they compute `−qₖ/pₖ` and conjugate `H ↦ ιHι` to land on `pₖ/qₖ`).
- **Theorem 4**: same for Nakada's α-continued fractions, any `α ∈ (0,1]`.
- **Theorem 6**: same for Rosen's `λ_m`-CFs over the Hecke triangle groups `Γ_m`, i.e.
  approximants that are quotients of algebraic integers.  Example 1 (`m = 5`, `λ₅ = φ`):
  a.e. real has its Rosen-φ approximants equidistributed among five cusp types
  (odd/even, even/odd, 1/1, 1/λ₅, 1/(λ₅+1)) — note this is `ℤ[φ]`-flavored, but it is a
  statement about *approximants of a fixed CF algorithm*, not about transporting
  normality along a map, so it does not touch §7 either.

## The one idea worth stealing (§7 Further remarks)

Their Theorem 3 holds for the flow of **any one-parameter subgroup** `F_t`, not just
`E_t`; only the ergodicity input changes.  For the **horocycle** flow, Hedlund and
Dani–Smillie give *essential unique ergodicity* — and unique ergodicity is the one
ergodic-theoretic hypothesis that yields **every** orbit equidistributing rather than
a.e.  That is the shape of statement Route A needs on its compact fiber `W`.  Caveat
before getting excited: horocycle equidistribution controls Farey/approximant statistics,
not the CF digit string of `Mx`, and the whole forward cone of this paper (below) went
that way and stayed there.

## Forward cone (checked 2026-08-24; OpenAlex 6, Semantic Scholar 10)

All of it is Farey/horocycle-section work, none of it normality:
Heersink (Poincaré sections for the horocycle flow in covers, 2016; Farey equidistribution
on horospheres, ETDS 2021), Taha (Boca–Cobeli–Zaharescu map for Hecke groups `G_q`, 2018),
**Borda, *Equidistribution of CF convergents in SL(2,ℤ_m)…*, J. Mod. Dyn. 2025**
(arXiv:2303.08504 — upgrades the Szüsz/Moeckel/Jäger–Liardet SLLN to CLT, LIL and
invariance principles; the quantitative frontier of exactly this theorem), and
Vandehey 2017 itself.  Nobody has pointed FS at normality in twelve years.
