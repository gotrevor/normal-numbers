# ON-LINE REQUEST (box has no egress; a host session answers as ON-LINE-FINDINGS-<date>-<topic>.md)

## 2026-10-08 (repetition review lap 10): sources for the 3-adic two-logarithm bound

Needed for `SparseIdentity.Literature.PadicTwoLogs` (transcription check) and for its
formalization (DIRECTION.md, P3).  Please fetch and summarize, quoting statements verbatim:

1. **Y. Bugeaud, M. Laurent**, *Minoration effective de la distance p-adique entre puissances de
   nombres algébriques*, J. Number Theory 61 (1996) 311–342.  Needed: (i) the exact statement of
   the main corollary for two logarithms (shape `v_p(α₁^{b₁} − α₂^{b₂}) ≤ c·D⁴·(max{log b' + …})²
   log A₁ log A₂`; exact definitions of `b'`, `A_i`, the constant, and every hypothesis, e.g.
   `v_p(α_i) = 0`, multiplicative independence, `p`-adic disc conditions); (ii) the structure of
   the proof: the interpolation matrix (rows/columns, entries), the p-adic analytic upper bound
   (lemma statement), the zero lemma used (statement + hypotheses), the parameter choice.
2. **M. Laurent**, *Linear forms in two logarithms and interpolation determinants*, Acta Arith.
   66 (1994) 181–199: the zero lemma for two logarithms (statement and proof; the sumset
   condition `Card{α₁^r α₂^s} ≥ L`, `Card{r b₂ + s b₁} > (K−1)L`, `R = R₁ + R₂ − 1`, …).
3. Any expository source giving a complete, short proof of a p-adic two-logarithm lower bound
   for RATIONAL numbers (e.g. lecture notes; Waldschmidt's book ch. 7/9; Bugeaud's 2018 book
   *Linear Forms in Logarithms and Applications*, ch. on p-adic two logarithms).

Also useful: whether any Lean/Isabelle/Coq formalization of a linear-forms-in-logarithms bound
(any case) exists.
