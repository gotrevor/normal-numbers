# Product blocks, part 2: rungs and binary words 🪜

2026-10-06.  Follows `base5-product-block-2026-10-05.md`.  Lean:
`src/NormalNumbers/MahlerProductBlock.lean` (sections "Rungs" and "Word blocks").  Probe:
`experiments/mahler_block_rs` (`lift`, `rung`, `wfail`, `wsearch`, `wgreedy`, `wminimize`,
`wswap21`), with tests in `experiments/test_mahler_product_block.py`.

## BLUF

- The base-5 12-block is **inclusion-minimal** (`not_isProductBlock_five_twelve_erase`).
- **Binary 2-words: for every irrational x, one of x, 3x, 5x has both `00` and `11` infinitely
  often** (`isWordBlock_two_two_one_three_five`).  No pair up to 40 works
  (`not_isWordBlock_two_two_pair`).  This is the binary analogue of "2x or 11x": base 2 has no
  digit question, so words are the first rung with content.
- **Binary 3-words: a 13-member block**, all members at most 239:
  `{1, 5, 19, 29, 97, 103, 133, 175, 197, 205, 209, 211, 239}`.  The Liouville bound forces a
  member at least `23 = 10111₂`.  No block of size at most 5 within `[1, 48]`.
- **The digit ladder is dead.**  Rungs `a → a+1` compose (`IsRung.mul`, proved), but the top rung
  is nearly the whole problem (Maze row "Digit-count ladder for product blocks").
- **The dimension heuristic is not a lower bound.**  It predicts about `g ln g` members (8 in
  base 5), but base 3's `{2, 11}` beats its prediction of 3 (Maze row "Dimension count as a
  block-size lower bound").

## Rungs

A rung `(a → b)` lifts every irrational with at least `a` digits occurring i.o. to a multiple with
at least `b`.  If `S` is `(a → b)` and `T` is `(b → c)`, then `S·T` is `(a → c)`.  A ladder
`2 → 3 → ⋯ → g` is a product block, so the hope was cheap rungs with small members, giving
explicit blocks in base 7 and up.

The rung checker refines the carry automaton with "n·y stays inside a digit set M,
|M| = b − 1".  It keeps only SCCs that could carry an irrational y with at least `a` digits:
not a simple cycle, and at least `a` distinct input labels.  A path is eventually inside one
SCC, so the filter is sound.

Base 5 results:

| rung | smallest witness found |
|---|---|
| 2 → 3 | pairs: 709 of 1081 in `[2, 60]`, `{2, 11}` first |
| 3 → 4 | none of size ≤ 3 in `[2, 60]`, none of size 2 in `[2, 400]` |
| 4 → 5 | none of size ≤ 3 in `[2, 60]`, none of size 2 in `[2, 400]` |

The top rung is the block problem with one fewer free digit.  An irrational avoiding one digit
already has dimension `log(g−1)/log g`, so the ladder pays the full price at its last step and
multiplies it by the earlier steps.

## The dimension heuristic, and why it fails

"m·x avoids d" cuts dimension by `1 − log(g−1)/log g`.  If these cuts were transversal, a block
would need about `log g / −log(1 − 1/g) ≈ g ln g` members: 2.7 in base 3, 7.2 in base 5.  Base
3 refutes it: `{2, 11}` is a block with 2.  The constraint sets all live in one base, so their
product automaton can have zero entropy while the codimensions sum to less than 1.  So the
heuristic gives no lower bound, and a base-5 block smaller than 8 is still possible.  The proved
floor is 3.

## Binary word blocks

A **k-word block**: for every irrational x, some m ∈ S has every length-k base-g word i.o. in
m·x.  The checker's channel state is (carry, last k−1 emitted digits), and the emitted window
must not equal the avoided word.  Doubling is a shift, so even members never help.

- **k = 2**: `{1, 3, 5}`.  240 of the 1140 triples in `[1, 40]` work and no pair does.  `{3, 5}`
  fails with `3x` avoiding `00` and `5x` avoiding `11`.
- **k = 3**: greedy over odd m < 256 found 14 members in about 2 minutes, and `wminimize` dropped
  `3`, leaving 13.  Liouville: `X = Σ 2^(−i!)` shows the bits of `m` between zero gaps, and the
  first `m` whose padded expansion holds all eight 3-words is `23 = 10111₂`.
- **k = 4**: the same Liouville count needs a member of at least `2479 = 100110101111₂`
  (12 bits, since `0^∞ m 0^∞` has only `len(m) + 4` distinct 4-windows).  Not attempted.

The 2026-08-29 note's "base-2 {00, 11} block floored at k = 8" is the **two-track** (x and y)
problem.  The single-track one closes at three members.

## Novelty

The genre (Mahler 1973, Berend–Boshernitzan 1994, Szüsz–Volkmann 1983) gives existence and
size bounds for the multiplier.  Explicit joint word blocks were not found in the 2026-10-05
sweep.  Estimated novelty: about 60% as stated.

## The joint multiplier is doubly exponential (later, 2026-10-06)

The Liouville witness plus a window count gives the lower side that Szüsz–Volkmann lacked.
`0^∞ m 0^∞` has at most `len(m) + k` distinct `k`-windows, so a `k`-word block needs a member
with `len(m) ≥ g^k − k`, that is `m ≥ g^(g^k − k − 1)` (`IsWordBlock.exists_ge`).  With
Szüsz–Volkmann's `12·g^(g^k + k)` (`Literature.SzuszVolkmann1983`), the exponent of the joint
multiplier is `g^k ± O(k)` (`wordBlock_exponent_pinned`).  Bugeaud–Coons's joint
`B(b,k) = b^k(b+1)` therefore fails whenever `b^k(b+1) < b^(b^k − k − 1)`, for example binary
`k = 4` (48 against 2048) and every base at `k = 2` from `b = 3` on
(`not_isWordBlock_Icc_bugeaudCoons`).  At small cases the Liouville bound is close to the
truth: 125 vs 194 (base 5, digits), 16 vs 23 (binary 3-words), 2048 vs 2479 (binary 4-words).

**Magnitude is pinned; block SIZE is not.**  Binary sizes run 1, 3, at most 12 for
`k = 1, 2, 3`.  No finite S works for every k at once (pigeonhole: some member would work for
infinitely many k, so its multiple would be disjunctive, and the Liouville number kills that).
Whether the minimum size stays bounded as k grows is open here.

## Hand proof of x, 3x or 5x (later, 2026-10-06)

Suppose x is irrational and none of x, 3x, 5x has both `00` and `11` i.o.  Complementing
(x ↦ −x) swaps `00` and `11` everywhere, so assume x eventually avoids `11`: isolated 1s.

1. **3x** is x with every 1 widened to `11`, with no carries (the pairs `{n−1, n}` are
   disjoint).  So 3x has `11` i.o. and must avoid `00`, which forces every gap between 1s to be
   2 or 3.  The tail of x is a word in `A = 01` and `B = 001`, both i.o.
2. **5x = x + 4x.**  At each `1·A·B` (bits `1 0 1 0 0 1 0 …`), column sums from the right give
   `0011`: the incoming carry is at most 1 and cannot pair with a next-token 1, then the
   columns read `?, 1, 1, 0, 0`.  So 5x has both `00` and `11` i.o.

Contradiction.  The proof also says why 5 is needed: any irrational `A`/`B` word beats
`{1, 3}`.  It is now in `isWordBlock_two_two_one_three_five`'s docstring, and the test suite
checks both halves (`test_rust_x_3x_5x_hand_proof`).
