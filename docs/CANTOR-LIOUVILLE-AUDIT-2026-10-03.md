# Bugeaud 10.37 (Cantor ∩ Liouville ∩ base-2 normal): audit 2026-10-03

Lean record: `src/NormalNumbers/CantorLiouville.lean`, namespace `NormalNumbers.CantorLiouville`, branch `proof/cantorliou`.  This doc gives direction only; every claim cites a declaration.

## Target, transcribed

Bugeaud, *Distribution modulo one and Diophantine approximation* (2012), p. 219: "**Problem 10.37.** Prove that the middle third Cantor set contains Liouville numbers which are normal to base 2."  The preceding sentence says each pairwise intersection is known to be nonempty.  Headline: `exists_liouville_mem_cantorSet_isNormal_two` (Mathlib `cantorSet`, Mathlib `Liouville`, repo `IsNormal 2`); computable strengthening: `exists_computable_liouville_mem_cantorSet_isNormal_two`.

## Verdict

- **Sound, 80% for the a.e. headline within 3–4 laps**; the paper argument is about 85%.  The headline and `ae_isNormal_two` are wired and proved from the leaves.  No literature `Prop` is assumed.
- **Computable version: 60%.**  It needs a rate-generic derandomization; `ComputableNormal` hard-codes polynomial decay at `n^{10}`.

## Prior art (open as far as found, about 75%)

The searches run, and what each returned:
- `papers followups`: 2607.06773 had 0 citers; 1601.00153 had 7; math/0505074 had 95; 1305.6501 had 40; 2005.09300 had 17.  Grepped for normal, Liouville and equidistribution: nothing.
- Semantic Scholar was rate-limited, so OpenAlex citers were scanned instead: Bluhm 2000 (19), Bugeaud 2002 C. R. Acad. Sci. 335 (20), Becher–Heiber–Slaman 2015 (12), Bugeaud 2008 Math. Ann. (82).  None of them treats Cantor ∩ Liouville ∩ normal.
- Full texts were grepped for Liouville, Cantor, "10.37" and problem: 2607.06773, 2408.03473, 1311.0332, 1601.00153, 1410.1017, 2609.24665, 1512.06935.  None cites Problem 10.37.
- Becher's publication list and Bugeaud's CV were checked, and about 8 web searches plus arXiv keyword queries were run.  All came up empty.

The closest results, and why each falls short:
- **Becher–Lew Deveali 2607.06773, Thms 1 and 3.** Sparse binary Cantor sets, normal in every odd base, with a computable witness.  Their sparsity condition requires `≳ log k` points of `S` in every window `[a, a+k]` with `a ≤ k`, and a Liouville point needs gaps `[n, w n]`.  Our argument uses only the *cumulative* free count below `log₃ N / 2`, never a per-window count.
- **Bluhm 2000 + Bugeaud 2002.** They give absolutely normal Liouville numbers, but by a Rajchman measure.  `K` is a set of uniqueness and carries no Rajchman measure (Pramanik–Zhang 2408.03473 §1), so that route is closed for 10.37.
- **Becher–Reimann–Slaman 1601.00153.** Its irrationality exponent is finite, it makes no normality claim, and its set is not `K`.

Instrument limits: we had no full-text search of all of the book's citers (OpenAlex counts about 200), so a journal-only answer could have been missed.

## Difficulty check

1. **Proved implications.**
   - `K` membership (`pt_mem_cantorSet`, proved).
   - The base-3 sibling fails, as it must (`not_isNormal_three_cantorLiouvilleReal`, proved).
   - Base-3 frequencies have no low digit changes (`tdig_mul_three_pow`, proved).
   - The run structure is correct (`isForced_anchor`, `isForced_of_mem_run`, proved).
   - The a.e. statement and the headline wiring (`ae_isNormal_two` and `exists_liouville_mem_cantorSet_isNormal_two`, both proved).
2. **Unproved premise, the content.**  `secondMoment_le` (85%), a quantitative Cassels lemma for an arbitrary free set, with bound `C N² (exp(−c F(N)) + N^{-1/2})`.  It splits into three leaves:
   - `charFun_norm_le`, the Riesz product (94%);
   - `abs_cos_le_of_tdig_ne` (97%);
   - `sum_pow_changes` (93%): an exact identity, that digit changes of `c·2ʲ` over a period are i.i.d. with probability 2/3.  It uses `orderOf_two_zmod_three_pow` (99%, LTE).  The tripwire `probes/cantorliou_changes_probe.py` checks 236 exact cases, and the base-3 sibling breaks the identity.
3. **Bookkeeping leaves.**
   - `ae_isNormal_two_of_secondMoment`: DEL along a schedule with ratio → 1 (97%).  The `j²` schedule of `DecayAeNormal` is too sparse for a sub-polynomial saving.
   - `sched_ratio` (97%).
   - `le_freeCount` (95%).
   - `summable_sched_bound` (92%).
   - `liouville_cantorLiouvilleReal` (93%).
   - `ae_frequently_free` (98%).
4. **Which quantitative condition keeps enough free digits.**  The free count below `M` must satisfy `F(M) ≥ C log M` for a large enough `C` (we have `M/(2(log₂ M + 2))`), so that `exp(−c F(log N))` is summable along a ratio-1 schedule.  The other two cases:
   - All digits forced makes `F ≡ 0`, and the bound degenerates to the trivial `C N²`.
   - Free digits of density `o(log log N / log N)` give no summable saving.
5. **Liouville is genuinely forced.**  Truncating at `a k` gives `|x − p/3^{a k}| < 3^{-(k+2) a k} = q^{-(k+2)}`.  Then `x ≠ p/q`, because a free `2` lies past the run.

## Treadmill objective

> In `CantorLiouville.lean`, prove the bookkeeping leaves first: `sched_ratio`, `le_freeCount`, `summable_sched_bound`, `liouville_cantorLiouvilleReal`, `ae_frequently_free`, `ae_isNormal_two_of_secondMoment`.  Then the content: `abs_cos_le_of_tdig_ne`, `charFun_norm_le`, `orderOf_two_zmod_three_pow`, `sum_pow_changes`, `secondMoment_le`.  Frozen statements stay byte-identical; a refutation of any leaf is an advance and goes in `Maze.lean`.
