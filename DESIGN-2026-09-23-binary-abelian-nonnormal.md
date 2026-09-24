# A binary number that is abelian-normal but not normal (2026-09-23)

Campbell (arXiv:2603.04396) builds one in base 10 via a cyclic swap on digit pairs; the swap needs
three digits and has no base-2 analogue at block length 2.  In base 2 it works at block length 4.

## Construction

Let `c` be any base-16 normal digit sequence (e.g. hex Champernowne, or the base-16 digits of
`fullRealW`, normal in base 2 hence in base 16 via `IsNormal b x → IsNormal (b^K) x`).  Apply

    hexSwap:  2 → 3,  5 → 4,  B → A,  C → D   (identity on the other 12 hex digits)

and read the result in binary (4 bits per hex digit, most significant first).  In bits:
`0010→0011, 0101→0100, 1011→1010, 1100→1101`.  The induced block law μ on `{0,1}^4` is
`1/8` on `0011, 0100, 1010, 1101`, `0` on `0010, 0101, 1011, 1100`, `1/16` elsewhere: the extreme
point of the unique free direction (probe `probes/abelian_block_intervals.py`, k = 4: 1 direction;
it is the `separation_four` witness).

## Why it is abelian-normal

Under μ, the one-count of **every contiguous interval inside a block** is Binomial (10 intervals,
checked exactly).  Base-16 normality of `c` makes consecutive blocks behave as i.i.d. μ for every
fixed window (Campbell's (10)).  A length-L window at offset r is a block suffix, whole blocks, and
a block prefix; independent binomials sum to a binomial.  So every offset class, hence the
average, has the Binomial(L, 1/2) one-count law.  `probes/abelian_hex_construction.py` confirms
exactly for L ≤ 9 at every offset.

## Why it is not normal

Limiting frequency of `0011` (and of `0100, 1010, 1101`) is **5/64 ≠ 1/16** (average over the four
offsets); 20 of the 32 length-5 words are off.  Lengths 2 and 3 are exactly uniform, as
`rigid_three` forces.

## Sanity check on real digits

Hex Champernowne prefix, 2.4M bits: `0011` at 0.0789 (model 0.0781).  Champernowne prefixes are
zero-heavy (convergence ~1/log N), so the finite check is loose; the exact i.i.d. computation is
the verification.

Lean: `src/NormalNumbers/AbelianBinaryExample.lean`, kickoff `KICKOFF-2026-09-23-abelian-binary-example.md`.
