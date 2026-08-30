# PROBE: word-level (k = 2) product blocks and Mahler sets, base 3 🧯

**2026-08-30, autonomous session, standing-mandate exploration after the
tower closed.**  Instrument: `experiments/adder_baseg_emit.py`'s collapse
check (prune → SCC → simple-cycle), single-track base 3.  Negative results
are floors of the METHOD (certificate non-collapse ≠ falsity of the
statement); per the tower brief's §2 discipline they are recorded here,
never formalized.

## Findings (all negative so far)

1. **C2 does NOT extend from digits to length-2 words for {2, 11}**: all
   81 avoid-pair families "`2x` avoids `w₁` ∧ `11x` avoids `w₂`",
   `w₁, w₂ ∈ {0,1,2}²`, FAIL to collapse (live 29–34 states each, live
   cycles with unforced branching).  The digit-level product block
   (`c2_product_block`) is the ceiling for this multiplier pair.
2. **No multiplier pair reaches length-2 words at all**: for
   `1 ≤ m₁ < 15, m₁ < m₂ ≤ 30`, no pair collapses all 81 word-pair
   assignments; indeed no pair even collapses 5 of the 9 DIAGONAL
   assignments (same word avoided in both channels).  The k = 2 frontier
   genuinely needs larger multiplier sets — consistent with the
   Berend–Boshernitzan lower-bound intuition (`g^k − 1 = 8`ish set size
   for their {1..M} form).
3. Triple scan `{m₁,m₂,m₃} ⊂ {1..10}` for the 9 diagonal words: running
   (`experiments/mahler_k2_triple_scan.py`); result to be appended.

## Reading

The certificate method's power at k = 1 (C1's 2-state collapse) does not
survive one word-length step with small channel sets.  Any word-level
theorem in this genre will need either (a) many more channels (state
products grow multiplicatively — kernel cost), (b) two-track freedom, or
(c) a genuinely different collapse mechanism.  This bounds the standing
mandate's cheap frontier: the digit-level tower was the harvest.

## Appended results

3. (completed) Triple scan `{m₁,m₂,m₃} ⊂ {1..10}`: **zero** of the 120
   triples collapses even ONE diagonal length-2 word.  Harness sanity
   checks pass on the known k = 1 positives (C1 {1,2}, C3 {1,5}).
4. Larger sets, word `00`: `{1,2,4,8}` and `{1,2,3,4,5}` both FAIL.

**Conclusion (method floor, strong form): simple-cycle certificates give
NO length-2 ternary word theorem for any single-track multiplier set of
size ≤ 5 with multipliers ≤ 10 tried; the entire k = 2 diagonal frontier
is out of reach of the current collapse mechanism at small scale.**  The
digit-level tower (C1–C6) is the harvest of this genre; further positives
need a new mechanism (period-carrying certificates beyond simple cycles,
two-track interaction, or non-certificate arguments).
