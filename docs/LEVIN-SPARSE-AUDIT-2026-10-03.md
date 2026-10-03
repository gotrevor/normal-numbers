# Audit + freeze: Levin's rate in base 2, normal in every odd base (2026-10-03)

Source: `docs/OPEN-PROBLEMS-SWEEP-2026-10-03b.md` candidate #3.  Branch `proof/discr`, module
`NormalNumbers.LevinSparse`.

| Item | Verdict | Lean |
|---|---|---|
| Headline: `x` normal in every odd base and every `2^k`, base-2 `D*_N = O((log N)²/N)` | **sound**, rate improved from the sweep's `(log N)³/N` to Levin's own `(log N)²/N`; no prior art found (~80%) | `exists_levinRate_oddNormal` (**proved from leaves**) |
| Cited inputs | Levin 1999 Thm 2; BLD 2607.06773 Lemma 5 | `Literature.Levin1999`, `Literature.BLDLemma5` |
| Absolute-normality upgrade (`o(N^{-1/2})` in base 2, normal in all bases) | open; BLD's "extends via Schmidt" is asserted, not proved | `exists_absNormal_base2_fast` (open node, 20%) |
| Computable version | stretch | `exists_computable_bld_odd_add` (65%) |

## Prior art

Searched, per item:
- `papers followups` 1707.02628 (11 citers: Manai ×4, Nandakumar–Pulari, Carella ×2, one untitled Carella-style entry, Seiller–Simonsen, Becher–Carton, Lutz–Mayordomo), 1510.02004 (7), 1511.03582 (10), 2607.06773 (0).  None gives a rate below `N^{-1/2}` in one base together with normality in an independent base.
- Manai 2508.09319v4 §1 (TeX): "We only know about the rather recent construction from [ABSS17] … `D_N^b ≤ C(b)N^{-1/2}`.  It is a very difficult, yet also interesting, problem to construct numbers with lower discrepancy."
- Manai 2609.24665 (Sep 2026): extends Rauzy to absolute normality "by a sparse random perturbation argument"; qualitative, no rates.  Closest in spirit; does not do this.
- ABSS 1707.02628 (TeX): barrier remark and Bugeaud's 2017 question (all bases at once) recorded as open; cites Levin 1999 for one base.
- Alvarez–Becher 1510.02004 (TeX): Levin 1979 (absolutely normal, `(log N)²ω(N)/√N`) and Levin 1999 (one base, `(log N)²/N`); "the computational complexity of this construction has not been studied yet".
- Levin's normal-number papers on zbMATH (14 titles): simultaneously normal *vectors* use a different number per coordinate (JTNB 2001, Levin–Volinsky 2008/2010); 1979 and "jointly absolutely normal" (1990) are `≥ N^{-1/2}` or qualitative.  Hofer–Larcher 2205.01566, 2211.04212: Levin's `(log N)²` is sharp in prime bases; nothing on other bases.
- Becher's publication list (2026): nothing combining a fast base-2 rate with other-base normality.  Scheerer's thesis (TU Graz 2017): results stop near `N^{-1/2}`.  Becher–Slaman *On the normality of numbers to different bases* Thm 4: slow discrepancy in one base, the opposite direction.
- Web / arXiv API: "normal to all odd bases", "normal base 2 and base 3 low discrepancy", "discrepancy barrier absolutely normal", "Bugeaud question discrepancy", `abs:"normal number" AND discrepancy` (10 hits, all checked).

Freshness ~80%.  Folklore risk: the field is active (BLD Jul 2026, Manai Sep 2026), and "translate a low-discrepancy number by a BLD point" is one step from both.

## Cited inputs, exact

- **Levin, Acta Arith. 88 (1999) 99–111, Theorem 2** (full text matwbn.icm.edu.pl/ksiazki/aa/aa88/aa8821.pdf): explicit `α` (digit-block concatenation via Pascal's triangle mod 2), normal to base `q`, `D(N, {αqⁿ}) = O(N⁻¹ log² N)`, `D` the star discrepancy of eq. (1).  The Prop takes `q = 2`, existential `α`, all `N ≥ 2` (constant enlarged).  Faithful-or-weaker.  (Theorem 1 there is a different construction with `log³`.)
- **BLD 2607.06773v1 Lemma 5** (p. 8), with the thresholds of Lemmas 1, 3, 4 (`δ₄(a) = 2^{max((a^{1/ρ}+1)K_S, 10³⁰)}`).  The Prop uses threshold `2^{K(a+1)^{1/ρ}+10³⁰}` (`K = 3K_S` dominates) and `Sparse`, which implies BLD's sparsity; so it is faithful-or-weaker.  **Referee needed**: the threshold transcription (the PDF text of `δ₁`, `δ₄` is garbled in extraction; the reading above is from the proofs of Lemmas 1 and 4) and the `|cos|` in Lemma 5's display.

BLD Lemma 7's *statement* bounds `∫ |A_N|² dμ`, which does not see translates.  Its *proof* bounds the cosine double sum `Σ_{p,q} Π_{k∈S}|cos(πh(rᵖ−r^q)/2ᵏ)|` and only then the integral.  That intermediate inequality is the leaf `bld_doubleSum_le`, proved on paper from Lemma 5 and Lemma 6 (LTE); it is not cited as a stated lemma.

## Difficulty check

- **Proved implications (Lean):** the headline wiring `exists_levinRate_oddNormal`, the base-2 transfer `discLe_add_bldPoint`, `perturbBudget_dense_ge_one`, `zero_not_mem_expSet`.
- **Unproved premises:** the two cited Props.  Leaves (sorry + confidence + English proof): `discLe_fract_add` 92, `fract_bldPoint_small` 92, `isNormal_of_discLe` 95, `del_ae_tendsto` 95, `secondMoment_translate_le` 88, `bld_doubleSum_le` 85, `ae_isNormal_odd_add` 85, `sparse_expSet` 85, `sIcc_expSet_le` 97, `rate_arith` 99, `exists_not_isNormal_two_dense` 92.
- **Translation invariance, checked:** `𝔼|N⁻¹Σ e(hrʲ(α+y))|² = N⁻² Σ_{p,q} e(h(rᵖ−r^q)α) μ̂_S(h(rᵖ−r^q)) ≤ N⁻² Σ |μ̂_S(…)|`.  BLD's proof uses only `|μ̂_S|` (their p. 9: "Expanding the square and using `|μ̂(t)| = Π|cos|`").
- **Carries, checked:** `{2ⁿ(α+y)} = {{2ⁿα} + {2ⁿy}}`, a shift mod 1; no carry issue beyond the wrap-around, which the shift lemma pays for (`#{u ≥ 1−η} ≤ N(η + D)`).
- **The sweep's density worry, resolved:** BLD sparsity needs only `S(a, a+k) > 30 log k` for windows starting at `a ≤ k^ρ`, so `#(S ∩ [1,N]) = Θ(log N)` is allowed (BLD's own `{⌈e^{j/100}⌉}`, `ρ < 0.7`).  The base-2 budget is `(log₂N+2)·#(S∩[1,2N])/N = O((log N)²/N)`.  So the rate is Levin's `(log N)²/N`, not `(log N)³/N`.  General form: budget `O(#(S∩[1,N]) log N / N)`.
- **Which bases are blocked, and why:** powers of 2 are free (`isNormal_pow`).  Odd bases work.  Bases `2ᵃm` with `a ≥ 1`, `m > 1` odd (6, 10, 12, …) fail for this `S`: `h(rᵖ−r^q)` is divisible by `2^{aq}`, so only `S ∩ (aq, O(p)]` matters, and a log-count `S` has `O(1)` points there; the cosine product does not tend to 0 and the second-moment route gives nothing (BLD Thm 2 even exhibits base-6 non-normal points of `C(S)`).
- **Known-false siblings:** dense digits (`S = {k ≥ 1}`): the budget is `≥ 1` (`perturbBudget_dense_ge_one`, proved), and some dense `y` makes `α + y` an integer (`exists_not_isNormal_two_dense`), so the every-`y` base-2 claim genuinely needs sparsity.  `α = 0`: every `y ∈ C(S)` has digit-1 frequency 0, not base-2 normal; the content is in the split.

## The upgrade (open)

A sparse `S` with exponent `1 < ρ < 2` (primes: count `≈ N^{1−1/ρ}`) keeps the base-2 budget at `O(N^{-1/ρ} log² N) = o(N^{-1/2})`.  Absolute normality would then need decay for bases `2ᵃm` at shifts `≍ N` over windows of length `≫ log N`, beyond BLD Lemma 4's residue count; BLD assert a Schmidt-tools extension to all bases independent of 2 without proof.  That is `exists_absNormal_base2_fast`, the one node here that would beat the ABSS barrier with absolute normality.

## For `--require-decls`

`NormalNumbers.LevinSparse.exists_levinRate_oddNormal`, `…discLe_fract_add`, `…fract_bldPoint_small`, `…isNormal_of_discLe`, `…del_ae_tendsto`, `…secondMoment_translate_le`, `…bld_doubleSum_le`, `…ae_isNormal_odd_add`, `…sparse_expSet`, `…sIcc_expSet_le`, `…rate_arith`, `…exists_not_isNormal_two_dense`.
