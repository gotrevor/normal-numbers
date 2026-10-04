# Entropy lane (E5) referee, 2026-10-04

Referee of `src/NormalNumbers/EntropyProfiles.lean` and `docs/ENTROPY-AUDIT-2026-10-04.md` on `proof/entropy`.  No `.lean` edits, no build.

## Bottom line

- **The question is read faithfully (85%), and the answer is correct.  But it is not new mathematics: it follows almost at once from a bilipschitz-embedding theorem in print since 2009.**  Mattila–Saaranen 2009 (quoted in Deng–Wen–Xiong–Xi 2011) embeds any `s`-regular set, `s < 1`, into any `t`-regular set with `t > s`.  DWX 2011 Thm 1 embeds any SSC self-similar set into any self-similar set of larger dimension.  Either gives `K ↪ F` with `F = {no hex digit 15}`.  The only extra step is making the map monotone, so that it extends to all of ℝ.
  - Already known in substance: 70%.
  - Explicitly written down as an answer to HS somewhere: 10% (every search came back empty).
  - HS would call it immediate once asked: 70%.
- **The docstring's gap estimate is false.**  The construction can be repaired, and the repair is the standard tree embedding (fix below).
- **All three cited Props pass:** `CasselsSchmidtCantor` is implied (faithful), and `HochmanShmerkinCantorDiff1` and `HochmanShmerkinTimesP` are both weaker than their sources (sound).  None needs a fix.

## 1. The question

**Source text.**  The sentence is word-for-word the same in arXiv v1 (2013-02-23), v2 (2013-08-07), v3 (2014-12-08, TeX `normality.tex`) and Hochman's homepage copy, which is the post-revision text with the Kaufman paragraph (`math.huji.ac.il/~mhochman/preprints/normality.pdf`).  I could not reach the Inventiones text (Springer login wall).  v3 says "minor corrections" and postdates acceptance, so the published wording is almost certainly the same (90%).  The paragraph (v1 §1.3.1, v3 §1.2.1, after Cor 1.8 "x² is 3-normal for μ-a.e. x"):

> The corollary above is immediate from the previous theorem and the use of the square function is incidental. In fact for we could replace x² with f(x) for f ∈ diff². From Theorem 1.4 we can reduce the regularity to diff¹ if we only want n-normality for n ≁ 3. These differences perhaps indicate that our regularity assumptions may be suboptimal. Note that for f = identity, this again is the theorem of Cassels and Schmidt, and their spectral methods carry over to translations, but the stability under perturbation is new even for affine f. Related to this question, we note that Bugeaud, Fishman, Kleinbock and Weiss have shown that for many fractals sets, including self-similar sets satisfying the open set condition, there is a full-dimension subset consisting of numbers which are *not* normal in any integer base. Moreover their result holds for any bi-Lipschitz image of the set. The stability of our results under bi-Lipschitz transformations remains open.

The abstract frames the same thing as: "This condition is robust under C¹ coordinate changes".

**What "our results" and "stability" mean.**
- "This question" is how low the regularity of the coordinate change `f` can go.  Their results are Thm 1.4 and Thm 1.5, which give "`gμ` pointwise β-normal for all `g ∈ diff¹(ℝ)`", plus Thm 1.7, Cor 1.8 and Thm 1.10 for `diff²`.
- The measures are quasi-product measures of regular `C^{1+ε}` IFSs.  Thm 1.4 also needs some contraction ratio `≁ β`.
- So "stability under bi-Lipschitz transformations" means: is `gμ` still pointwise `n`-normal when `g` is only bi-Lipschitz?  Bi-Lipschitz is the natural floor below `diff¹`, and it is the class BFKW's non-normal result survives.
- The lane's `g` answers exactly this: `μ` = Cantor–Lebesgue, the IFS `{x/3, x/3+2/3}` is regular and affine, `n = 2 ≁ 3`, and `g` is a bi-Lipschitz homeomorphism of ℝ.
- The answer also settles the "stability of the hypotheses" reading.  HS's fractal-geometric condition implies the conclusion, and `μ` satisfies it, so `gμ` cannot.
- It also settles the set-level reading (does a bi-Lipschitz image contain normal numbers?), because `g(K)` contains no 2-normal point.
- I found no reading that excludes the example.  It is not a misreading (misreading: 10%).

**Prior art.**
- **DWX**: J. Deng, Z.-Y. Wen, Y. Xiong, L.-F. Xi, *Bilipschitz embedding of self-similar sets*, J. Anal. Math. 114 (2011) 63–97 (mp_arc 09-210).
  - Thm 1: "Suppose E₁, E₂ are self-similar sets with dim_H E₁ < dim_H E₂.  If E₁ satisfies the SSC, then there is a bilipschitz map g : E₁ → g(E₁) ⊂ E₂."  Remark 2: OSC is not needed for E₂.
  - Same paper: "It is also proved in [12] [Mattila–Saaranen, Ann. Acad. Sci. Fenn. Math. 34 (2009)] that any s-regular set with s ∈ (0,1) can be embedded into any t-regular set F with t > s."
- Both predate HS (2013).  Applied with `E₁ = K` and `E₂ = F`, they give a bi-Lipschitz `g : K → F` and so a bi-Lipschitz `g` with `gμ` carried by non-2-normal numbers.
- What they do not state is that the map is **order-preserving** and so extends to a bi-Lipschitz homeomorphism of ℝ.  For `K ⊂ ℝ` an arbitrary bi-Lipschitz embedding need not extend.  Their block/tree construction can be made monotone on ℝ in a line or two (see §2).
- Ying Xiong (a DWX author) also cites HS (Xiong–Zhao, Nonlinearity 35 (2022)).  I could not read its text; that is a null, not a negative.

**Later papers.**
- `papers followups 1302.5792` lists 84 citers; I reused the session list.
- The audit had already grepped the TeX of 12 citers for "bi-Lipschitz" and found nothing.
- I added Manai 2609.24665, *On Normality Preserving Operations*.  It shows that every locally `C²` normality-preserving map is rational-affine, and builds a non-affine `C^{1,1}` diffeomorphism preserving `N_b` for all `b`.  This is the adjacent "maps preserving normality" question.  No bi-Lipschitz statement.
- Chang–Gao 1710.07131 (differential images): no Lipschitz hit in its extracted text.
- Web search: only HS's own sentence.

**Verdict:**
- Faithful answer: 85%.
- Known in substance, as a corollary of MS09/DWX11 plus monotone extension: 70%.
- Not answered explicitly in print: 90%.

**Recommendations:**
- Keep the headline as a sharpness guard.
- Rewrite the docstring and audit claim from "negative answer to HS's open question" to "HS's question has an essentially immediate negative answer (cf. Mattila–Saaranen 2009, DWX 2011 Thm 1)".
- Do not count it as new math or as outreach material.
- The interesting residue is the gap between `diff¹` and bi-Lipschitz.  Example: is `gμ` pointwise normal for a bi-Lipschitz `g` that is differentiable with `g′ ≠ 0` at μ-a.e. point?  The lane's `g` fails this, because its scale ratio wanders on `K`.

## 2. The English construction (headline docstring)

**The gap estimate is false.**  Counterexample: take `e = 0.0ED000…` in hex, which is left-type, with `e ≈ 0.0578613`.
- Piece `0` of `F` has hull `[0, (14/15)/16] = [0, 0.0583333]`.
- `(0.0583333, 0.0625)` is a gap of `F`.  Its length `1/240 ≈ 0.0041667` sits at distance `D ≈ 0.000472`, so the length is about `8.8 D`, not `≤ 1.15 D`.
- With `w` ending in `EE` the ratio is `16²/14 ≈ 18`.  In general it is unbounded as the trailing structure varies.
- The window claim fails with it: `e + [1.01 D, 2.3·1.01 D]` lies inside the gap.
- `F` is two-sided uniformly perfect but not one-sided at left-type points.

**The "affine image position" placement also fails as written.**
- Inside `J_u` there are `F`-gaps of length about `|J_u|/240`, which is much larger than `3^{-(n+1)L}`.
- So children cannot sit at prescribed affine positions with error `≪ 3^{-(n+1)L}`.

**Repair: the standard tree embedding.**
- Let each `J_u` be the hull of a 16-adic cylinder of `F`.  Its endpoints `0.v000…` and `0.vEEE…` are in `F`, and its length is `(14/15)·16^{-|v|}`.
- Take level `M_n = ⌈nL·log 3/log 16⌉`, so `|J_u| ≍ 3^{-nL}` within a factor of 16.
- One level-`M_n` cylinder has `15^{M_{n+1}−M_n} ≥ 15^{0.396L−1} = 2^{≈1.55L}/15` descendants at level `M_{n+1}`.  That is far more than `2·2^L` for large `L`.
- Assign the `2^L` children of `I_u` in order to every other descendant.  Consecutive chosen cylinders are then separated by at least one sibling hull, which is `≳` their own size.
- Two `K`-points that split inside block `n` are `≍_L 3^{-nL}` apart, and so are their images.  The constants depend only on `L`, which is fixed.

**What is correct as written:**
- `g(K) ⊆ F`, because `F` is closed and the nested endpoints converge.
- Points of `F` are not 2-normal, via 16 = 2⁴ (rationals are not normal anyway).
- `dim F > dim K`.
- The extension is bi-Lipschitz across gaps at all scales.  On each gap `(a,b)` of `K`, with `a, b ∈ K`, the slope is `(g b − g a)/(b − a) ∈ [C⁻¹, C]`.  For `s < t`, both `t − s` and `g t − g s` are sums over the gaps in `[s,t]`, since `K` and `g(K)` are Lebesgue-null and `g` is monotone and continuous.  Outside `[0,1]`, use slope 1.
- The "not C¹" remark.

**Verdict:**
- The Lean statement is true (95%).
- The docstring proof has a real hole: the gap estimate and the placement are false.  The tree-embedding repair is routine.
- Fix the docstring before the proving lap, so the lap does not formalize a false lemma.

## 3. Cited Props

| Prop | Quantifier check against the source | Verdict |
|---|---|---|
| `CasselsSchmidtCantor` | Cassels 1959: Cantor–Lebesgue-a.e. `x` is normal to every base that is not a power of 3.  Repo: `MultDep b 3 ↔ b = 3^k` (`eq_three_pow_of_multDep`).  `cantorLebesgue` = law of `Σ 2ω_i 3^{-(i+1)}` under fair `Fin 2` digits (`digitMeasure 1`, uniform on `Fin 2`), which is the Cantor–Lebesgue measure.  HS Thm 1.4 with `g = id` also gives it. | **Implied (faithful).** |
| `HochmanShmerkinCantorDiff1` | HS Thm 1.4 needs: a regular `C^{1+ε}` IFS (orientation-preserving injections of `I`, images disjoint except endpoints); `{x/3, x/3+2/3}` on `[0,1]` qualifies.  `λ(f) = 1/3 ≁ b` uses HS's `∼` ("integer powers of a common number"), so this is `b ≁ 3`.  β Pisot includes integers (footnote).  Bernoulli(½) is quasi-product with `C = 1`.  The conclusion is "`gμ` pointwise β-normal" = `gμ`-a.e. normal, which gives `μ`-a.e. `IsNormal b (g x)` by `ae_of_ae_map` (`g` is continuous).  `diff¹(ℝ)` is not defined in the TeX; the standard reading is C¹ diffeomorphisms of ℝ.  `IsC1Diffeo` (C¹, `deriv ≠ 0` everywhere, bijective) is exactly that class or a subclass.  `IsNormal` reads `Int.fract`; for integer `b`, `{bⁿx} = {bⁿ fract x}`, so values outside `[0,1)` match HS. | **Weaker (sound).** |
| `HochmanShmerkinTimesP` | HS Thm 1.10: β Pisot (here `m`), `γ = p`, `β ≁ γ`; `T_γ`-invariant ergodic of positive entropy, conclusion pointwise β-normal.  Lean `Ergodic` includes `MeasurePreserving`, so invariance is there, and `timesMap` is measurable, so the hypothesis is not vacuous.<br>**Support:** HS's `T_n : [0,1] → [0,1]`, `x ↦ nx mod 1`, puts no mass at 1, because `T⁻¹{1} = ∅` and invariance then forces `μ{1} = 0`.  So `μ([0,1)ᶜ) = 0` with `fract(p·x)` on ℝ is equivalent.<br>**Frostman implies positive entropy, directly:** an `n`-cylinder has length `p^{-n}`, so its mass is `≤ C' p^{-nδ}`.  Then `H(ξ_n) ≥ nδ log p − O(1)`, which gives `h ≥ δ log p > 0`.  No dimension formula is needed.  `C ≤ 0` would force `μ = 0`, so there is no junk case.<br>**Non-vacuous:** Lebesgue (`δ = 1`) and Cantor measure with `p = 3` both satisfy it. | **Weaker (sound).**  Strictly weaker: zero-dimension pieces are excluded, but positive entropy is all HS need. |

No fixes are needed for the Props.  The only docstring nit: `HochmanShmerkinTimesP` cites "dim μ = h/log p".  That is true but not needed; the direct cylinder-entropy bound above is cleaner.
