# ON-LINE FINDINGS — Tao 2016, arXiv:1509.05422 (2026-09-26)

**Answers:** `ON-LINE-REQUEST.md` of 2026-09-25 (DEEP REFLECTION lap 112).  Fulfilled by a host
session after lap 121, so read it against the lap-121 state (`ZetaLogDerivExponent θ`, owned
`θ ≥ 9`, needed `θ < 1`).

**Sources read:**
- `papers/tao-2016-log-chowla-elliott.pdf` (arXiv v4, 29 Jul 2016, 32 pp.; downloaded this session,
  gitignored if `*.pdf` is) + `papers/tao-2016-log-chowla-elliott.txt` (`pdftotext -layout`).
  Read: §1 in full (pp. 1–8), §2 through Proposition 2.4 (pp. 8–13), bibliography.
- One web search on Littlewood's zero-free region (sources at the bottom).

---

## Q1 — Is the range really `|t| ≤ A·x`?  **Yes.  The Vinogradov wall does not disappear this way.**

Theorem 1.3 (p. 5), verbatim in substance: `a₁,a₂ ∈ ℕ`, `b₁,b₂ ∈ ℤ`, `a₁b₂ − a₂b₁ ≠ 0`, `ε > 0`,
`A` sufficiently large depending on `ε,a₁,a₂,b₁,b₂`, `x ≥ ω ≥ A`, `g₁,g₂ : ℕ → ℂ` multiplicative with
`|gᵢ| ≤ 1`, and `g₁` non-pretentious:

> (1.6)  `Σ_{p≤x} (1 − Re g₁(p) χ(p) p^{−it}) / p ≥ A`  (conjugation bars, if any, are lost in the text extract)
> for all Dirichlet characters `χ` of period at most `A`, and all real `t` with **`|t| ≤ A·x`**.

Conclusion (1.7): `|Σ_{x/ω<n≤x} g₁(a₁n+b₁) g₂(a₂n+b₂)/n| ≤ ε log ω`.

Corollary 1.5 (asymptotic form) uses `inf_{|t|≤Ax} D(...)→∞` (1.8).  The range is **linear in x**
in both, not `x^{o(1)}` or `(log x)^A`.

**Why it is `A·x` — it is inherited, not a choice.**  Tao says (p. 13, after Prop 2.4): *"Proposition
2.4 is the only way in which we will take advantage of the hypothesis (2.3), which may now be
discarded."*  Prop 2.4 is the short-sum bound
`Σ_{x/ω<n≤x} (1/n) sup_α |(1/H) Σ_{j≤H} g₁(n+j) e(jα)| ≪ (log log H / log H) log ω`,
proved by quoting **[23] = Matomäki–Radziwiłł–Tao, *An averaged form of Chowla's conjecture*,
Algebra Number Theory 9 (2015), Lemma 2.2 + Theorem 2.3** (with `W := log⁵ H`), applied dyadically
on `2ω ≤ X ≤ 2x` and averaged.  MRT's Theorem 2.3 hypothesis is the `|t| ≤ X`-range
non-pretentiousness, so `|t| ≤ Ax` is the price of the MRT/Matomäki–Radziwiłł short-interval input.
To shrink the range you would have to re-prove MRT with a weaker hypothesis — not an option.

(Also inherited: Prop 2.1 reduces `|g₁| ≤ 1` to `|g₁| = 1` using (1.6) + triangle inequality, same
range; the reduced Theorem 2.3-form, p. 12, restates (2.3) with `|t| ≤ Ax` and `x ≥ x/log x ≥ ω ≥ A`,
completely multiplicative `g₁,g₂ : ℕ → S¹`.)

## Q2 — How does Tao discharge (1.8) for his applications?  **Vinogradov–Korobov, by citation.  No cheaper device.**

p. 6, Remark 1.6, verbatim:

> *"Using Vinogradov-Korobov error term zero-free region for L-functions (see [25, §9.5]), it is not
> difficult to establish (1.8) when g is the Liouville function; see [22, Lemma 2] for a closely
> related calculation.  Thus Corollary 1.5 implies Theorem 1.2."*

- [25] = H. Montgomery, *Ten lectures on the interface between analytic number theory and harmonic
  analysis*, CBMS 84, AMS 1994, §9.5.
- [22] = K. Matomäki, M. Radziwiłł, *A note on the Liouville function in short intervals*,
  arXiv:1502.02374, Lemma 2.
- The only other named applications in the paper are `μ` (Möbius, via the same remark) and
  Corollary 1.7 (Möbius sign patterns).  **`e(αΩ(n))` does not appear in this paper** (no `Ω` in the
  text); that application is in later work, not here.  Nothing here treats `ζ^{ω(n)}`.

So the repo's 🟠 classification is **confirmed at the source**: the author himself routes the
`|t| ≍ x` end through Vinogradov–Korobov and offers no alternative.  Tao gives no argument for the
top of the range at all — "not difficult" + a citation.

## §2 bonus — `g(pn) = g(p)g(n)` at `p | n`

Handled by a reduction, not in the core argument: Prop 2.1 → `|g₁| = 1`, then (pp. 9–11, the
`h(d)` / `d | a₁n+b₁` step and the `A₀` truncation) reduces to **completely multiplicative**
`g₁,g₂ : ℕ → S¹` before Theorem 2.3's form (p. 12) is stated.  The main argument (entropy decrement,
the `λ(pn) = −λ(n)` trick) is run only in the completely multiplicative case.  For `ζ^{ω}` (not
completely multiplicative) this means the repo's port must carry that reduction; I did not read
pp. 9–11 line by line, so treat the mechanism as "a Dirichlet-convolution split `g = g' * h` with
`h` supported near prime powers", **unverified** in detail.

---

## A lead the request did not ask for — ⚠️ check before building on it

The lap-121 interface demands a **power** saving, `‖ζ'/ζ‖ ≪ (log t)^θ`, `θ < 1`.  But per the
lap-120 handoff the exponent enters in exactly one place, `log(1/T) = θ·log log`, i.e. the chain
needs `log(1/T) ≤ log log x − (margin)` where the margin must exceed the fixed non-pretentiousness
constant.  If the chain only needs the margin to **tend to infinity** (x large depending on A), then
a **Littlewood-strength** bound would do:

> Littlewood (1922, via Weyl's exponential-sum method): no zeros in
> `σ > 1 − c·log log t / log t`; consequently (standard, Titchmarsh ch. III)
> `ζ'/ζ(1+it), 1/ζ(1+it) ≪ log t / log log t`.

This gives `log(1/T) = log log t − log log log t + O(1)`, margin `log log log x → ∞`.  It is **not**
`≤ C(log t)^θ` for any `θ < 1`, so it does not satisfy `ZetaLogDerivExponent`; it would need a
weaker sibling Prop (e.g. `‖ζ'/ζ(s)‖ ≤ C·log(|t|+16)/log log(|t|+16)`) and a check that every
consumer tolerates a `log log log` margin rather than a `(1−θ) log log` one.

Confidence: zero-free region **95%** (confirmed by web sources below).  The `ζ'/ζ ≪ log t/log log t`
consequence **~80%** from memory of Titchmarsh §3.6, not opened this session.  Whether the chain
tolerates a `log log log` margin: **not checked** — that is the lap's to verify in
`ElliottZetaTheta.lean`.  Cost comparison: Weyl-differencing / van der Corput is well short of
Vinogradov's mean value theorem, but still a real formalization job; none of it is in
`PNTPort` as far as I know.  If the margin must be `≥ δ·log log x`, this lead is dead and the record
is "Vinogradov or nothing".

---

Sources (web):
- [Kadiri, *Zero-free regions close to the real axis* (BIRS 2023)](https://www.birs.ca/workshops/2023/23ss001/files/Habiba%20Kadiri%20-%20Zero-free%20regions%20close%20to%20the%20real%20axis.pdf)
- [arXiv:2301.03165](https://arxiv.org/pdf/2301.03165) — explicit Littlewood region `σ > 1 − log log t /(21.233 log t)`
- [*Littlewood's theorem and Weyl's method* (Springer chapter)](https://link.springer.com/chapter/10.1007/978-3-642-50026-8_3)
