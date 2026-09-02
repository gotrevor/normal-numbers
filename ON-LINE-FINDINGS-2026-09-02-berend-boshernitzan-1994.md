# ON-LINE-FINDINGS 2026-09-02 — Berend–Boshernitzan 1994, upper AND lower bounds

Answers **both** open items in `ON-LINE-REQUEST.md` (2026-09-01 upper-bound
question, 2026-09-02 lower-bound follow-up).

**Source read: the full paper, verbatim text layer, not a secondary source.**
D. Berend and M. D. Boshernitzan, *On a result of Mahler on the decimal
expansions of (nα)*, Acta Arithmetica **66** (1994), fasc. 4, 315–322.
DOI `10.4064/aa-66-4-315-322`.  Free scan (text layer, TeX-set) from the ICM
digital library: `http://matwbn.icm.edu.pl/ksiazki/aa/aa66/aa6642.pdf`.

⚠️ **The PDF was already in this repo** as
`papers/berend-boshernitzan-1994-mahler-multiples.pdf` (pinned 2026-08-30,
gitignored by `papers/*.pdf`).  I re-downloaded independently and the bytes are
identical — SHA-256 `3a65a8516a6c9c064c9cd4371d1e3ce77225183772169481000be1d63f1fed37`,
matching the hash recorded in `papers/berend-boshernitzan-1994-mahler-multiples.md`.
It is now mirrored into the `normal-numbers-cfsched` clone as well.  **Read it
directly next lap** (`pdftotext papers/berend-boshernitzan-1994-mahler-multiples.pdf -`)
rather than re-asking.

**Title check:** the title in the request is exactly right.  The ledger
docstring calling it *"Renewal-type theorems…"* is a **misattribution** — no
paper of that name appears on Berend's publication list
(`https://www.cs.bgu.ac.il/~berend/pub/pub.html`), and the Acta Arith. 66
(1994) 315–322 slot is the "On a result of Mahler…" paper.  Fix the docstring.

---

## 1. Upper bound — Theorem 1.1 (p. 316), verbatim

> **Theorem 1.1.** Let α be an irrational, g ≥ 2 an integer and B a g-block of
> length k.  Then there exists a positive integer m < 2gᵏ⁺¹ such that the g-ary
> expansion of mα contains the block B infinitely often.

- Constant is **`2·g^(k+1)`, strict `<`** — the secondary-source transcription
  was **correct**.  (Intro, p. 315, states the base-10 case as `M(k) < 2·10^(k+1)`,
  improving Mahler's `M(k) < 10^(2k+1)` / `M(g,k) < g^(2k+1)`.)
- Quantifiers: `∀ α irrational, ∀ g ≥ 2, ∀ k ≥ 1, ∀ B` a g-block of length k,
  `∃ m` with `0 < m < 2g^(k+1)` — i.e. the bound is uniform in α and in B.
- 🎯 **Our `m ≤ g^(k+1)` is genuinely a factor-2 improvement over the published
  theorem** — the tier-S claim survives.  But state it carefully: B–B themselves
  note in **Case I** of the proof (p. 317) *"(Note that in this case we could
  have replaced the upper bound 2gᵏ⁺¹ by gᵏ⁺¹.)"* — they knew `g^(k+1)` holds in
  the easy case and only lost the factor 2 in Case IV, where they need a
  `2gᵏ`-net.  So the honest framing is **"we remove the factor 2 that B–B's
  Case IV argument costs them"**, not "they never considered `g^(k+1)`."

### Their proof route (question 3) — NOT Dirichlet + AP

Purely **topological-dynamical**, §2, pp. 317–318.  Let `E ⊆ T = ℝ/ℤ` be the set
of limit points of the orbit `{gⁿα : n ≥ 0}`.  Four cases on which rationals
`p/q` lie in `E`, each reduced to Case I (a rational in `E` with
`gᵏ < q ≤ gᵏ⁺¹`, whose multiples form a `g^(-k)`-net in `T`).  Case IV uses a
rational approximation with `|β − p/q| < 1/(2g^(k+1)q)`, `2gᵏ < q ≤ 2gᵏ⁺¹`.
They credit **Furstenberg**, via a result of **Glasner** (Israel J. Math. 32
(1979) 161–172), for the idea, and cite **Alon–Peres**, *Uniform dilations*,
GAFA 2 (1992), Cor. 7.2 for a short finiteness proof of `M(g,k)`.

✅ **Our Dirichlet + arithmetic-progression route is a different proof**, so the
novelty note in `BRIEF-literature-statements.md` is safe on the *method* axis —
just don't claim novelty for the *statement* shape.

---

## 2. Lower bounds — §3, pp. 318–320.  🚨 Theorem 3.1 is our result

> **Proposition 3.1** (p. 318).  `M(g,k) ≥ gᵏ − 1` for every `g ≥ 2`, `k ≥ 1`.

Witness: `α = Σⱼ g^(−nⱼ)` with `n_{j+1} − nⱼ → ∞`, `B` = k consecutive `(g−1)`s.

> **Theorem 3.1** (p. 318).  Let `a` be a proper divisor of `g`.  Then
> `M(g,k) ≥ a(gᵏ − 1)`, `k ≥ 1`.

🚨 **This is exactly the repo's 2026-09-02 "sharpening."**  Their `a` is our `t`
in `g = t·c`, `c ≥ 2` ("proper divisor" ⇔ the cofactor is `≥ 2`); their witness
is `α = (g/a)·Σⱼ g^(−nⱼ)`, ours is `α = c·Σⱼ g^(−i!)` — the **same
construction**.  Their proof even gives *equality* for that α: the least
multiple of `g/a` containing k consecutive `(g−1)`s is `g^(k+1) − g = (g/a)·a(gᵏ−1)`.
So `M(g,k) ≥ t(gᵏ − 1)` must be **attributed to B–B Theorem 3.1**, not claimed.
They also note the best choice is `a` = maximal proper divisor, and that Thm 3.1
improves Prop 3.1 **unless g is prime**.

> **Theorem 3.2** (p. 319).  If `g` is not a prime power, then for every `ε > 0`
> there exists `K = K(ε)` with `M(g,k) ≥ (1 − ε)g^(k+1)` for `k ≥ K`.

Proof: pick a prime `p | g`; `log p / log g` irrational ⇒ choose `l, r` with
`g^l < p^r < (1+ε)g^l`; take `α = (p^r/g)·Σⱼ g^(−nⱼ)`.  **This beats our bound
asymptotically** for every non-prime-power base.

> **Example 3.1** (p. 320).  For `g = 10`: `p=2, l=0, r=1` ⇒ `M(10,k) ≥ 5(10ᵏ−1)`,
> `k ≥ 1`; `p=5, l=2, r=3` ⇒ `M(10,k) ≥ 8(10ᵏ−1)`, `k ≥ 1`;
> `p=2, l=3, r=10` ⇒ `M(10,k) ≥ 9.765(10ᵏ−1)` for `k ≥ 7`.

So **our `8(10ᵏ−1)` for base 10 is also already in the paper**, with the same
`k ≥ 1` quantifier, and they go further to `9.765`.

> **Theorem 3.3** (p. 320).  Let `g ≥ 5` be odd.  Then `M(g,1) ≥ (3/2)(g−1)`.

Witness `α = 1/2 + Σⱼ g^(−nⱼ)`; the bad digit is `(g−3)/2` when `g ≡ 1 (mod 4)`
and `g−2` when `g ≡ 3 (mod 4)`.  This is their prime-base analogue of Thm 3.1.

### Exact values (the follow-up's third question)

**No exact `M(g,k)` for any composite base appears in the paper.**  The only
exact values stated are the two where Prop 3.1 is tight: `g=2, k=1` and
`g=3, k=1` (p. 318, "This is the case, for example, for g = 2, k = 1 and for
g = 3, k = 1"), i.e. `M(2,1) = 1` and `M(3,1) = 2`.  They explicitly record two
open points:

- p. 320: *"We do not know whether it is true in general that `M(g,k) < g^(k+1)`."*
- p. 318: their lower bounds *"depend on the arithmetic nature of g … and may
  hint that there is no simple formula for M(g,k)."*
- p. 320: except for `g = 2, 3`, **never** `M(g,1) = g − 1`.

So **sharpness of our `t(gᵏ−1)` is open in the literature too** — nothing to
compare against.

---

## 3. What to change in the repo

1. **`MahlerMultiplier.lean` / `BRIEF-literature-statements.md`** — keep the
   upper-bound novelty claim (`g^(k+1)` vs published `2g^(k+1)`), but cite the
   Case-I parenthetical so the delta is stated honestly as "removes the Case-IV
   factor 2."  Method novelty (Dirichlet + AP vs orbit-closure/ε-nets) is real.
2. **`MahlerLowerBoundGeneral.lean`** — the general bound `M(g,k) ≥ t(gᵏ−1)` is
   **Berend–Boshernitzan 1994, Theorem 3.1** (and `8(10ᵏ−1)` is their Example
   3.1).  Re-file it as a **formalization of a known theorem**, not a new
   result; that is still a real contribution (Thm 3.1 has, as far as I can see,
   no Lean formalization), but the docstring must attribute.
3. **`Literature.lean`** — Prop 3.1, Thm 3.1, Thm 3.2, Thm 3.3 and the
   `M(2,1)=1`, `M(3,1)=2` exact values can now all be transcribed verbatim from
   the statements above.
4. **Open frontier that is genuinely ours:** B–B leave `M(g,k) < g^(k+1)?` open,
   and Thm 3.2 gives `(1−ε)g^(k+1)` from below for non-prime-power `g`.  Our
   `m ≤ g^(k+1)` upper bound **closes that gap to a constant-free `g^(k+1)`** and
   makes the pair `(1−ε)g^(k+1) ≤ M(g,k) ≤ g^(k+1)` asymptotically **sharp** for
   every non-prime-power base.  That is the headline worth writing up, and it is
   an *answer to an open question stated in the paper*.
5. Fix the ledger docstring: the paper is *"On a result of Mahler on the decimal
   expansions of (nα)"*, not *"Renewal-type theorems…"*.

## Sources

- Full paper text: `http://matwbn.icm.edu.pl/ksiazki/aa/aa66/aa6642.pdf`
  (= `papers/berend-boshernitzan-1994-mahler-multiples.pdf`, SHA-256 above).
- Berend's publication list: `https://www.cs.bgu.ac.il/~berend/pub/pub.html`
  (author's DVI link `ftp://ftp.cs.bgu.ac.il/…/mahler-decimal.dvi` is dead).
- Mahler's original: K. Mahler, *Arithmetical properties of the digits of the
  multiples of an irrational number*, Bull. Austral. Math. Soc. **8** (1973),
  191–203 (ref `[M]`) — bound `M(g,k) < g^(2k+1)`, geometry-of-numbers proof.
