# Adamczewski–Rampersad 2008 — On patterns occurring in binary algebraic numbers

B. Adamczewski, N. Rampersad, *Proc. Amer. Math. Soc.* **136** (2008), no. 9, 3105–3109.
S 0002-9939(08)09319-2.  PDF: `adamczewski-rampersad-2008-binary-patterns.pdf` (AMS copy,
fetched 2026-08-30).

## Their theorems

- **Theorem 1.1**: the binary expansion of every algebraic number contains infinitely many
  occurrences of **7/3-powers** (W^α with α = 7/3; e.g. `011010 011010 01` is a 7/3-power of
  `011010`).  **Corollary 1.2**: infinitely many overlaps (xXxXx).
- **Theorem 3.1** (ternary): the ternary expansion of every algebraic number contains either
  infinitely many squares or infinitely many occurrences of one of the blocks **010** or
  **02120**.
- **Open Questions 3.2/3.3**: arbitrarily large squares / arbitrarily large palindromes in
  binary algebraic expansions (both expected yes).

Proof shape: rationals are eventually periodic (trivial); for algebraic irrationals, a word
avoiding 7/3-powers is shown to be a *stammering sequence* (Karhumäki–Shallit structure theorem
for 7/3-power-free words, iterated Thue–Morse morphism factorization), and Theorem ABL
(Adamczewski–Bugeaud–Luca 2004, p-adic Schmidt subspace) says stammering ⟹ rational or
transcendental.  Occurrence counts are about *patterns* (XX, xXxXx), not fixed blocks — they
cannot name an explicit square in an explicit algebraic number.

## ⚠️ The "boundary" this repo cites (attribution precision)

The fact our docs and `src/NormalNumbers/Literature.lean` call the **Adamczewski–Rampersad
boundary** — *the words 0, 1, 01, 10 occur infinitely often in the binary expansion of every
irrational* — is **stated in their §1 as the only known result and "somewhat trivial"** (a
straightforward consequence of non-eventually-periodic expansions), i.e. it is folklore they
record, **not their theorem**.  What IS theirs is the frontier framing right after it: for
algebraic irrational α and any finite word W ∉ {0, 1, 01, 10}, whether W occurs i.o. in α is
**open**.  Cite the boundary as "classical, recorded in A–R 2008 §1"; cite the 7/3-power results
as theirs.  (Our `Literature.adamczewskiRampersad_boundary_holds` proves the folklore fact for
ALL irrationals, machine-checked — consistent with their §1.)

## Relevance to this repo

- Pins the openness frontier the adder briefs rely on: single fixed blocks beyond
  {0, 1, 01, 10} are open even for algebraic numbers — so the disjunction theorems
  (occurrence forced in *some* channel of a family) sit strictly between the trivial boundary
  and the open per-block problem.
- Their Borel-context intro (§1) is a clean citation for "every block i.o." being the expected
  but unproven normality picture.
- References carry the toolchain lineage: Adamczewski–Bugeaud (Annals 2007) complexity lower
  bounds, ABL 2004 transcendence criterion, Karhumäki–Shallit, Thue 1912, Mahler 1929
  (Thue–Morse transcendence).
