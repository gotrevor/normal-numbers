# Referee: `SahlstenStevensBernoulli12` + `BakerBanajiSparse` (2026-10-03)

**Verdicts.**

| Prop | Verdict | Confidence |
|---|---|---|
| `NormalNumbers.BadNormal.Literature.SahlstenStevensBernoulli12` | **implied** (exactly equivalent to the cited conclusion, not merely weaker), by three published theorems, two of them independent in method | SS route 93%, JS route 92%, BB Thm 1.2 route 90%; Prop true ≥ 97% |
| `NormalNumbers.ReciprocalNormal.Literature.BakerBanajiSparse` | **implied** (faithful-or-weaker, the "in particular" clause of BB Cor 1.5) | 93% |

Neither is vacuous and neither is false.  Docstring changes only; **no change to either Prop is needed** (§4).

Sources read in TeX, fetched fresh from arXiv: Sahlsten–Stevens **2009.01703v5** (2022-02-16, `NonlinearFinal.tex`); Jordan–Sahlsten **1312.3619v3** (2015-02-02, `FourierGibbsFinal.tex`; journal ref Math. Ann. 364(3-4) 983–1023, 2016); Baker–Banaji **2401.01241v2** (2025-01-17; Math. Ann. 392 (2025) 209–261).  The arXiv ids and titles were checked against the arXiv API.  The SS journal ref comes from Crossref: Amer. J. Math. **146**(4) (2024) 945–982, doi 10.1353/ajm.2024.a932433.  ⚠️ The AJM typeset numbering was not checked, so cite the label alongside the number.

## 1. `SahlstenStevensBernoulli12`

Lean: `∃ C δ > 0, ∀ ξ ≠ 0, ‖∫ ee(ξ · cfCoin ω) d coins‖ ≤ C|ξ|^{-δ}`, where `ee t = exp(2πit)` (`DecayAeNormal.ee`), `coins` is the fair product measure, and `cfCoin ω = lim cfVal(bWord(pre ω n)) = [0; 1+ω₀, 1+ω₁, …]`, since `cfVal (a::l) = 1/(a + cfVal l)`.  So the integral is `μ̂_SS(−ξ)` for `μ = cfCoin_* coins`, which is the stationary measure of `{f₁ = 1/(1+t), f₂ = 1/(2+t)}` with weights ½.

### 1a. SS Theorem 1.1(2) (`thm:nonlinear`), quantifier by quantifier

| SS hypothesis (TeX l. 272–307) | Instance, after the affine `A(x) = 12(x − 1/3)/5 : J = [1/3, 3/4] → [0,1]` | Status |
|---|---|---|
| `I_1..I_N ⊂ [0,1]` closed, `N ≥ 2`, `T_a = T|I_a` a C² diffeo, `T` conjugate to the full shift | `I₁ = A f₁J = A[4/7, 3/4] = [4/7, 1]`, `I₂ = A f₂J = A[4/11, 3/7] = [4/55, 8/35]`; each `T_a = A f_a⁻¹ A⁻¹` maps `I_a` onto `[0,1]` | ✅ (hand: `4/7 − 1/3 = 5/21`, `·12/5 = 4/7`; `4/11 − 1/3 = 1/33 → 4/55`; `3/7 − 1/3 = 2/21 → 8/35`) |
| (1) uniform expansion `|(Tⁿ)'| ≥ D⁻¹γⁿ` | `|f_a'(t)| = (a+t)^{-2} ≤ (4/3)^{-2} = 9/16` on `J`, and an affine conjugacy preserves `|f_a'|`, so `γ = 16/9`, `D = 1` | ✅ |
| (2) Markov | full branches | ✅ |
| (3) bounded distortion `‖T''/T'‖∞ ≤ B` | `T(x) = 1/x − a`, `T''/T' = −2/x`, bounded on `[4/11, 3/4]`; conjugation multiplies it by the constant `5/12` | ✅ |
| (4) total non-linearity: `τ = log|T'| ≠ ψ₀ + g∘T − g`, `ψ₀` constant per branch, `g ∈ C¹(I)` | Any such relation makes periodic-orbit sums `S_pτ` additive in the letters.  Fixed points: `2 log φ` (word 1), `2 log(1+√2)` (word 2); the 12-orbit gives `2 log(2+√3)`, since `[[0,1],[1,1]]·[[0,1],[1,2]] = [[1,2],[1,3]]` (trace 4, det 1).  Then `φ(1+√2) = 3.9062 ≠ 3.7321 = 2+√3`.  This rules out even continuous `g` | ✅ (re-derived by hand) |
| (2) of the theorem: `I_a` disjoint, `f_a` analytic | `8/35 < 4/7`; Möbius | ✅ |
| potential `φ < 0` continuous, `var_n φ = O(ρⁿ)`; μ the `L_φ^*`-fixed equilibrium state with `P(φ) = 0` (l. 358–366) | `φ ≡ −log 2`: `var_n = 0`, `P = log 2 − log 2 = 0`, `L_φ g = ½Σ g∘f_a`, so `L_φ^*μ = μ` **is** the IFS stationarity equation, and μ is the law of `cfCoin`.  No variational-principle step is needed | ✅ |
| μ non-atomic | Bernoulli on a full 2-shift with disjoint images | ✅ |
| conclusion: "Fourier coefficients tend to zero with a polynomial rate" | ξ ranges over **ℝ** (l. 254–256, l. 999 "Fix a frequency ξ ∈ ℝ"), normalisation `e^{−2πiξx}`.  `A_*μ` has transform `phase · μ̂(12ξ/5)`, so the real rescaling is legitimate.  `|μ̂(−ξ)| = |μ̂(ξ)|` for a real measure, so the sign of the exponent is immaterial | ✅ |
| `O(|ξ|^{-α})` as `|ξ| → ∞` versus Lean's `∀ ξ ≠ 0` | `|μ̂| ≤ 1`, so take `C' = max(C, ξ₀^δ)` on `0 < |ξ| < ξ₀` | ✅ equivalent |

Exponent and constant: SS gives no explicit `α` and the Lean Prop asserts none (`∃ C δ`).  Nothing was transcribed that could be wrong.

### 1b. Jordan–Sahlsten cross-check (independent method: Kaufman / Queffélec–Ramaré Diophantine large deviations)

JS **Theorem 1.3(2)** (`thm:main`; `theorem` counter per section, preceded by Thm 1.1 DEL and Thm 1.2 Kaufman/QR): `𝒜 ⊂ ℕ` finite, μ any Gibbs measure for the Gauss map restricted to `B(𝒜)`, `dim μ > 1/2` ⇒ `μ̂(ξ) = O(|ξ|^{-η})`, with normalisation `e^{−2πiξx}` (l. 285).  Bernoulli measures are Gibbs, with potential `log p_{a₁(x)}` (Remark `rmk:examples`(1); `p_a = 0` off `𝒜` is allowed by "0 ≤ p_a").

**dim μ, re-derived independently.**  `probes/sahlsten_stevens_cf12_probe.py` Part A computes `λ = ∫ log|T'| dμ = −P'(0)`, with `P(t) = log ρ(L_t)` and `L_t g(x) = Σ_a ½(a+x)^{-2t} g(1/(a+x))`.  It uses Chebyshev collocation and a Richardson central difference, which shares no code or method with `bad_bernoulli12_dimension.py` (that probe uses cylinder-endpoint averages).
- Known-answer controls on the same operator code: `ρ(L₀) = 1` to 1e-12, and the unweighted operator gives `dim_H E_{1,2} = 0.531280506277`, against the literature value `0.5312805062772` (Jenkinson–Pollicott).
- **`λ = 1.34602223`**, the same at 24 and 40 nodes.  This is inside the audit's bracket `[1.341565, 1.348663]` and matches its depth-12 value `1.346022`.
- **`dim μ = log 2/λ = 0.514960`**, so `> 1/2` with margin 0.015.  `λ < 2 log 2 = 1.386294` holds with room 0.040.  ✅

### 1c. Third route: Baker–Banaji Theorem 1.2 (`thm:analyticthm`, arXiv v2)

"Let `{φ_a : [0,1] → [0,1]}` be an IFS with each `φ_a` analytic and some `φ_a` not affine.  Then for **every** self-conformal measure, `|μ̂(ξ)| ≤ C|ξ|^{-η}` for all `ξ ≠ 0`."  The instance is `φ_a = A f_a A⁻¹`, contractions of ratio `≤ 9/16` on `[0,1]`, Möbius so analytic and non-affine, with weights ½ (BB's stationary measures require `p_a > 0`).  The conclusion is already in Lean's `∀ ξ ≠ 0` form.  Independence caveat: for a non-conjugate IFS, BB Thm 1.2 rests on Algom–Rodriguez Hertz–Wang 2306.01275 and Baker–Sahlsten 2306.01389.  Those are spectral-gap methods, the same family as SS, so this route is independent in *authors* (AHW), not in *method*.  JS is the method-independent check.

### 1d. Numeric tripwire (`probes/sahlsten_stevens_cf12_probe.py`, exit 0, ~80 s)

The probe averages exactly over all `2^24` depth-24 CF{1,2} words, one point per cylinder.  The max cylinder width is `1/(F₂₅F₂₆) = 1.098e-10` (all-ones word), so the phase error is `≤ 2π|ξ|·1.1e-10 = 4.5e-5` at `ξ = 2^16`.  Support hand-check: the point cloud spans `[0.366025, 0.732051] = [(√3−1)/2, √3−1]`.  These are the 2-periodic CFs, from solving `x² + 2x − 2 = 0` by hand.

| `k` | `|μ̂(2^k)|` | envelope `sup_{[2^k, 2^{k+1}]} |μ̂|` (48 log-spaced pts) | Dirac at `1/φ`, same pipeline |
|---|---|---|---|
| 6 | 1.639e-1 | 3.401e-1 | 1.000000 |
| 8 | 2.013e-1 | 2.722e-1 | 1.000000 |
| 10 | 2.093e-1 | 2.093e-1 | 1.000000 |
| 12 | 9.050e-2 | 1.624e-1 | 1.000000 |
| 13 | 8.575e-2 | 1.509e-1 | 1.000000 |
| 14 | 8.732e-3 | 1.180e-1 | 1.000000 |
| 15 | 1.394e-2 | 7.653e-2 | 1.000000 |
| 16 | 1.180e-2 | 5.762e-2 | 1.000000 |

- The fitted envelope exponent is **−0.250**.  That is consistent with the ceiling `η ≤ dim μ / 2 = 0.2575`, the potential-theoretic bound JS quote at l. 288.  So the measure looks nearly Salem; this is a sanity check, not a theorem.  Single dyadic points are noisy (`|μ̂(2^13)| > |μ̂(2^7)|`), which is why the assertions use the envelope.
- **Control 1, Dirac at `[0;1,1,…]`:** same enumeration with one map.  It stays at `1.000000` (it is `not_decay_const`, proved).
- **Control 2, middle-third Cantor measure** (`{t/3, t/3 + 2/3}`, same `word_points`/`ft`).  Along `ξ = 3^k`, `k = 3..11`, the value stays flat at **0.371437**.  It equals the closed form `∏_{j=1}^{20−k}|cos(2π3^{-j})|` to 1e-6.  **Hand check:** `cos(2π/3) = −0.5`, `cos(2π/9) = 0.76604`, `cos(2π/27) = 0.97304`, `cos(2π/81) = 0.99699`, `cos(2π/243) = 0.999666`.  Their product is `0.5·0.76604 = 0.38302 → 0.37269 → 0.37157 → 0.37145`, and the tail `≈ 0.99996` takes it to `0.3714`.

## 2. `BakerBanajiSparse`

Lean: `∀ b ≥ 2, ∀ F U` (U open ⊇ `[1/2,1]`, F C² on U, `F'' ≠ 0` on `[1/2,1]`), `∃ C δ > 0, ∀ ξ ≠ 0, ‖sparsePushFourier b F ξ‖ ≤ C|ξ|^{-δ}`.  Here `sparsePushFourier` uses `exp(+2πiξF(y))` under `coinMeasure` (fair product), with `y = ySparse b ω = realOfDigits b (sparseDigits b ω)`.

| Item | BB Cor 1.5 (`t:self-similar`), arXiv v2 l. 200–213 | Instance | Status |
|---|---|---|---|
| measure | stationary for a **non-trivial** (no common fixed point, l. 115) CIFS of similarities **acting on `[0,1]`** (`φ_a : [0,1] → [0,1]`, l. 157), `p_a > 0`, `Σp_a|r_a|^{-τ} < ∞` | `y = c + z` with `c = ⌊(b+1)/2⌋/b ∈ [1/2, (b+1)/(2b)]` and `z = Σ_k ω_k b^{-(3k+3)}` (digit `3k+2` sits at `b^{-(3k+3)}`).  After `s = 2y − 1`: `ψ_ω(s) = s/b³ + a(1 − b⁻³) + 2ω/b³`, with `a = 2c − 1 ∈ [0, 1/b]` | ✅ |
| maps into `[0,1]` | needed for "acting on [0,1]" | `ψ₀(0) = a(1 − b⁻³) ≥ 0`; `ψ₁(1) = a + (3 − a)b⁻³ ≤ 1/b + 3/b³ ≤ 7/8` | ✅ |
| non-trivial | distinct fixed points | `a ≠ a + 2/(b³ − 1)` | ✅ |
| weights / sum | finite IFS, `p = (½, ½)`, ratio `b⁻³` | trivial | ✅ |
| homogeneity / separation | not required | homogeneous anyway; images of the hull are disjoint | n/a |
| map class | `F̃ : [0,1] → ℝ` C², `F̃'' ≠ 0` on `[0,1]` (the second clause needs this only on `supp μ`) | `F̃ = F∘((s+1)/2)`: C² on the open preimage of U ⊇ `[0,1]`, `F̃'' = F''/4 ≠ 0` on `[0,1]`.  `deriv (deriv F) = F''` on open U (as in the prior referee) | ✅ Lean hypothesis is stronger than needed |
| conclusion | "In particular… `∃ C_{F,μ}`, `|\widehat{Fμ}(ξ)| ≤ C_{F,μ}|ξ|^{-η}` for all `ξ ≠ 0`", with `e^{−2πiξx}` (l. 104) | `F̃_*ν_s = F_*μ_y`; opposite sign, same modulus; Lean picks `C, δ` per `(b, F)`, which is weaker than BB's `η` uniform in F | ✅ |
| integrand measurability | — | F is continuous on U ∋ y(ω), so `F∘ySparse` is measurable.  If it were not, the Bochner integral would be 0, which only weakens the Prop | ✅ |

**The constant-monotonicity caveat from `BAKER-BANAJI-ANALYTIC-REFEREE-2026-10-02.md` (κ, η, `|ξ| < 1`) does not arise.**  This Prop quotes the "in particular" clause, which has existential `C_{F,μ}` and already covers all `ξ ≠ 0`.  The only consumer, `exists_computable_absNormal_recip_not_simplyNormal`, feeds the existential `C, δ` straight into the engine, and no rational constants are hard-coded.

Support check: `y ∈ [c, c + 1/(b³−1)] ⊆ [1/2, 1)`.  For example, `b = 2`: `[0.5, 0.643]`; `b = 3`: `[0.667, 0.705]`.

## 3. Vacuity / falsity

- `SahlstenStevensBernoulli12`: a closed Prop with no hypotheses, so it cannot be vacuous.  It would be false only for an atomic measure (`not_decay_const`), and this measure is non-atomic.  Three theorems imply it, and the numerics show envelope decay at the Fourier-dimension ceiling.  One caveat: if `cfCoin` were non-measurable, the Bochner integral would be 0 and the Prop trivially true.  The engine separately demands `measurable_cfCoin` (leaf, 92%), so this cannot leak a false headline.
- `BakerBanajiSparse`: its hypotheses are inhabited for every `b ≥ 2` by `F = 1/t` (`inv_bakerBanaji_hyp`, proved), so it is not vacuous.  Affine F, the known-false sibling, is excluded by `F'' ≠ 0`.  Not false.

## 4. Exact Lean fixes (docstrings only; Props unchanged)

`src/NormalNumbers/BadNormal.lean`, `SahlstenStevensBernoulli12` docstring:
- Replace `**Faithful-or-weaker:** the statement below is the specialisation to `μ` = law of `cfCoin` under `coins`.  Referee pass pending.` with: `**Faithful (equivalent):** the specialisation to μ = law of cfCoin under coins.  Refereed 2026-10-03, implied (93%): docs/BAD-NORMAL-REFEREE-2026-10-03.md; tripwire probes/sahlsten_stevens_cf12_probe.py.`
- In the hypothesis check, name the conjugacy and the image intervals: `A(x) = 12(x − 1/3)/5`, `I₁ = [4/7, 1]`, `I₂ = [4/55, 8/35]`.  Add that `L_φ^*μ = μ` for `φ ≡ −log 2` is literally the IFS stationarity equation, with `P(φ) = 0`.
- Under "Independent cross-check", add: `Third route: Baker–Banaji, Math. Ann. 392 (2025), Thm 1.2 (arXiv 2401.01241v2, label thm:analyticthm): any self-conformal measure of an analytic IFS on [0,1] with a non-affine map has |μ̂(ξ)| ≤ C|ξ|^{-η} for all ξ ≠ 0.  Non-conjugate case via AHW 2306.01275 / Baker–Sahlsten 2306.01389 (spectral gap).`
- Update the λ sentence to: `λ = 1.34602223 (transfer-operator pressure derivative, probes/sahlsten_stevens_cf12_probe.py; agrees with the cylinder bracket of bad_bernoulli12_dimension.py), dim μ = 0.514960`.
- Optional: the SS citation can carry `(arXiv v5; label thm:nonlinear)`.

`src/NormalNumbers/ReciprocalNormal.lean`, `BakerBanajiSparse` docstring:
- `Corollary 1.5` → `Corollary 1.5, second ("In particular") clause (arXiv v2, label t:self-similar)`.
- Replace the Window bullet's reference to the quarter-Cantor change with the explicit rescaled IFS: `s = 2y − 1, ψ_ω(s) = s/b³ + a(1 − b⁻³) + 2ω/b³, a = 2⌊(b+1)/2⌋/b − 1 ∈ [0, 1/b]; ψ_ω[0,1] ⊆ [0, 7/8], fixed points a ≠ a + 2/(b³−1)`.
- Replace `Referee pending.` with `Refereed 2026-10-03, implied (93%): docs/BAD-NORMAL-REFEREE-2026-10-03.md.  No κ/η monotonicity issue: the existential C_{F,μ} clause is used directly.`
- Module docstring line `(…; referee pending)` → `(refereed 2026-10-03, 93%)`.  Do the same for `BadNormal.lean` l. 24 and the audit table rows in `docs/BAD-NORMAL-AUDIT-2026-10-03.md`.

## Residual risks

1. The AJM typeset version of SS may renumber Theorem 1.1; the arXiv v5 TeX was read.
2. SS's proof relies on Stoyanov's spectral gap via the UNI ⇔ TNL Lemma `lma:NLI`(2), which the paper proves only by pointing to AGY/Naud ("follows by investigating the proof").  JS does not depend on this, which is why the JS route matters.
3. No erratum to any of the three papers was searched for.
