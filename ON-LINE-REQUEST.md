# ON-LINE REQUEST — for a host session with egress

## 2026-09-25 (DEEP REFLECTION lap 112) — Tao 2016, arXiv:1509.05422

**What:** the PDF (or a full text extract) of

> Terence Tao, *The logarithmically averaged Chowla and Elliott conjectures for two-point
> correlations*, Forum of Mathematics Pi **4** (2016), e8.  arXiv:1509.05422.

Drop it at `papers/tao-2016-log-chowla-elliott.pdf` (plus a `pdftotext` extract
`papers/tao-2016-log-chowla-elliott.txt` if the PDF is large).

**Why it is route-decisive now, specifically.**  This repo has *proved* Theorem 1.3
(`NormalNumbers.ElliottGeneral.nonasymptoticLogElliottMult`, axiom-clean).  The live campaign is
verifying its **non-pretentiousness hypothesis** for `g = ζ^{ω}`:

> `D(g, χ·n^{it}; X)² ≥ A` for every Dirichlet character of modulus `q ≤ A` and every `|t| ≤ A·X`.

Lap 112 re-derived from scratch that the *top* of that `t`-range (`|t| ≍ X`) is exactly borderline
for the classical de la Vallée Poussin zero-free region, and needs a sub-classical bound
`|ζ(1+it)| ≪ (log t)^{2/3}` (Vinogradov–Korobov).  The two questions the paper would settle:

1. **Is the `|t| ≤ A·x` range in Theorem 1.3's hypothesis really that, or is it `|t| ≤ x^{o(1)}` /
   `|t| ≤ (log x)^{A}`?**  Our Lean `Prop` (inherited from the dependency) says `|t| ≤ A·X`; if the
   paper is weaker, the Vinogradov wall **disappears** and the campaign finishes with no cited axiom.
2. **How does Tao's own §1 discharge the hypothesis for his applications (λ, and `e(αΩ(n))`)?**  If
   he cites Vinogradov–Korobov, our 🟠 classification is confirmed; if he has a cheaper device, that
   device is the route.

Anything else about §2's handling of `g(pn) = g(p)g(n)` failing at `p ∣ n` is a bonus, not needed.

**Not needed:** no other sources requested this lap.
