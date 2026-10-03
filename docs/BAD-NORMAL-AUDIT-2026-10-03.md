# Audit + freeze: computable normal in BAD, and Bugeaud 10.17/10.18 (2026-10-03)

Source: `docs/OPEN-PROBLEMS-SWEEP-2026-10-03b.md` candidates #1 and #4.  Branch `proof/bad`.

| Target | Verdict | Lean | Cited input |
|---|---|---|---|
| (A) computable absolutely normal number with all partial quotients in {1,2} | sound, no prior art found; freshness ~70% | `NormalNumbers.BadNormal.exists_computable_absNormal_bad` (wired; 5 leaves + 1 anchor `sorry`) | `BadNormal.Literature.SahlstenStevensBernoulli12` (referee pending) |
| (B) Bugeaud 10.18 + 10.17 (b = 2, normal) | sound, no prior art found; freshness ~65% | `NormalNumbers.ReciprocalNormal.exists_computable_absNormal_recip_not_normal` (wired; 3 leaves) | `ExplicitSquare.BakerBanajiQuarterCantor` (refereed 93%) |
| (B') Bugeaud 10.17, every b ≥ 2, simply normal and normal | sound | `ReciprocalNormal.exists_computable_absNormal_recip_not_simplyNormal` (wired; 2 leaves) | `ReciprocalNormal.Literature.BakerBanajiSparse` (referee pending) |

## (A) Prior art, searched deeper than the sweep

Statements of the gap:
- Bugeaud 2012 §7.7 (p. 162, copy at `staff.dc.uba.ar/becher/aa/Bugeaud2012.pdf`): "On [517, p. 203], Montgomery asked for 'a normal number whose continued fraction coefficients are bounded'.  No explicit example of such a number has been exhibited yet."  Theorem 7.24 there (Queffélec–Ramaré) is existence.
- Queffélec 2006 (math/0608249) §4: "no explicit normal numbers in BAD have been constructed yet".

Searched, nothing constructing a point:
- forward citations (`papers followups`) of Jordan–Sahlsten 1312.3619 (86), Hochman–Shmerkin 1302.5792 (85), Sahlsten–Stevens 2009.01703 (30), filtered for comput / explicit / construct / algorithm / normal / badly / partial quotient;
- TeX grep (explicit, computab, Montgomery, badly approximable near normal, Kaufman, Jordan, Sahlsten) of: Manai 2508.09319 and 2609.24665, Lai–Xie 2601.03402, Becher–Lew Deveali 2607.06773, Sahlsten survey 2311.00585, Algom survey 2504.18192, Fraser 2503.17277;
- Becher–Heiber–Slaman 2015 (Math. Comp., the computable absolutely normal Liouville number): their method is the closest (derandomize a Rajchman measure, using decay uniform over dyadic intervals), but the paper states only the Liouville case and no generalization to BAD;
- Becher's publication list (all titles 1993–2026): only Becher–Yuhjtman (CF-normal, not BAD), Becher–Reimann–Slaman 1601.00153 (irrationality exponent, not BAD normality);
- web searches (8 phrasings: computable/explicit/algorithm × BAD/bounded partial quotients/{1,2} × absolutely normal/Kaufman); every hit restates "none exhibited".
- Not re-run: Scheerer's thesis and the Becher–Carton 2018 chapter (sweep §1.1 read both: existence only).

Folklore risk: an expert would say "BHS's method plus Kaufman/JS decay does it".  No written statement found.  The repo's contribution is the derandomizer in general form plus the CF cylinder approximations.

## (A) Cited decay: hypothesis check

Primary: Sahlsten–Stevens, Amer. J. Math. 146 (2024) 945–982, Thm 1.1(2) (`thm:nonlinear`, read from the arXiv TeX): disjoint `I_a`, analytic branches, full shift, uniform expansion, bounded distortion, totally non-linear, non-atomic equilibrium state of a potential with exponentially vanishing variations ⇒ polynomial decay.  Instance on `J = [1/3, 3/4]`: `f₁J = [4/7, 3/4]`, `f₂J = [4/11, 3/7]` disjoint; `|f_a'| ≤ 9/16`; total non-linearity by the periodic-orbit test (`S₂τ` on the `12` orbit is `2 log(2+√3)`, the sum of the letter values is `2 log(φ(1+√2))`, and `3.732 ≠ 3.906`); Bernoulli(1/2) = equilibrium state of the constant potential `−log 2`.  Full detail in the docstring of `SahlstenStevensBernoulli12`.

Cross-check: Jordan–Sahlsten, Math. Ann. 364 (2016), Thm 1.3(2) (arXiv numbering), needs `dim μ > 1/2`.  `probes/bad_bernoulli12_dimension.py` brackets the Lyapunov exponent between cylinder endpoints: `λ ∈ [1.341565, 1.348663]` at depth 4, so `dim μ ∈ [0.51395, 0.51667] > 1/2`; at depth 12, `λ = 1.346022`, `dim μ = 0.514960`.  The sweep's 0.515 is confirmed; JS covers this measure with margin 0.015.

## Difficulty check (A)

- Proved implications: the engine `ComputableNormalB.exists_computable_absNormal` (proved), the headline wiring (proved).
- Unproved premise: the decay Prop (cited, two independent theorems cover it).  Leaves are elementary CF bookkeeping: `PsiBad_eq`, `primrec_PsiBad`, `measurable_cfCoin`, `Abad_bounds`, `cfDigit_cfCoin`, and the anchor `cfCoin_const_false`.
- Known-false siblings, in Lean: `not_decay_const` (proved: no Dirac has polynomial decay, so the derandomizer cannot be fed an atom such as a periodic CF) and `not_decay_cfCoin_fixed` (proved, the one-letter and periodic siblings).  CF-normality is false for these points and is not claimed.

## (B) Prior art

- Existence: Manai 2609.24665 Thm 1.2.  Its TeX contains no reciprocal / Rivoal / Bugeaud-problem / explicit-example statement.  Manai 2606.08325 and 2508.09319 have none either; 2508.09319 cites Becher–Madritsch for the opposite question (`x` and `1/x` both normal).
- Bergelson–Downarowicz 2506.12929 §8.6 Q1 asks "Is the reciprocal of a normal number always normal?"; Manai answers it non-constructively.
- Web searches: nothing computable.
- Repo: `ExplicitSquare` (√ ↔ x²) is the same pipeline.  Row 5 (`exists_oneFreqZero_inv_normal`) is a different, open question (deterministic `y`).

## Difficulty check (B)

- `inv_bakerBanaji_hyp` is proved.  Leaves: `PsiInv_eq`, `primrec_PsiInv`, `Ainv_bounds` (two-case bound: `D ≤ 1` via `1/y ∈ [3/2, 2]`; `D ≥ 2` via `4·4^{-D} ≤ 2^{-D}`), `not_isSimplyNormal_ySparse`, `sparse_engine_inputs`.
- Known-false sibling: rational affine `F` has no decay (`ExplicitSquare.not_polyDecay_rat_affine`, proved).  The mechanism cannot claim `1/ξ = cantorReal e` normal, because `not_isNormal_cantorReal` is proved.
- Scope note: on the refereed input alone, 10.17 is answered only for `b = 2` (normal version).  The simply-normal version at `b = 2` needs the sparse point, because the derandomized `e` could have true-frequency 1.  The all-`b` form rests on `BakerBanajiSparse`, which is the same BB Cor 1.5 applied to a different homogeneous self-similar measure.

## `--require-decls`

`NormalNumbers.BadNormal.exists_computable_absNormal_bad`, `NormalNumbers.BadNormal.not_decay_const`, `NormalNumbers.ReciprocalNormal.exists_computable_absNormal_recip_not_normal`, `NormalNumbers.ReciprocalNormal.exists_computable_absNormal_recip_not_simplyNormal`.
