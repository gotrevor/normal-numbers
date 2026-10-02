# Referee: `BakerBanajiQuarterCantor` vs Baker–Banaji Cor. 1.5 (2026-10-02)

**Verdict: (a) implied as published.**  Confidence 93%.  Sources read: arXiv 2401.01241**v2** (17 Jan 2025) Thm 1.4 + Cor 1.5 (pp. 6-7); Manai 2609.24665v1 Thm 4.1 (`thm:BB`, p. 17).  Mosquera–Shmerkin 2018 not re-read (not needed: BB covers the inhomogeneous case, a fortiori ours).

**BB Cor 1.5 (exact).**  Φ a non-trivial (no common fixed point) countable IFS of similarities on `[0,1]`, weights `p_a > 0`, `Σ p_a|r_a|^{-τ} < ∞` for some τ > 0; μ its stationary measure.  Then ∃ η, κ, C > 0 (depending on μ only) such that for **all** `C²` `F : [0,1] → ℝ` with `F'' ≠ 0` on `[0,1]`: `|\hat{F_*μ}(ξ)| ≤ C(1 + max|F'| + (max|F'|)^{-κ} + max|F''|)(1 + (min|F''|)^{-κ}) |ξ|^{-η}` for all ξ ≠ 0.  (Second clause: `F'' ≠ 0` on `supp μ` only, constant `C_{F,μ}`.)  Manai's `thm:BB` is a faithful weakening (finite IFS, non-atomic, `C²` on a nbhd of `[0,1]`, per-F constants).

| Quantifier | BB / Manai | Ours | Status |
|---|---|---|---|
| Measure class | stationary for non-trivial similarity IFS on `[0,1]`, p_a > 0 | law of `cantorReal` under fair coins | ✅ see IFS check |
| IFS | maps `[0,1]→[0,1]` | `cantorDigits`: digit 0 forced `1` (weight 1/2), digit `2k+2` = `e k`, odd = 0 ⇒ `y = 1/2 + (1/8)Σ e_k 4^{-k}` ⇒ `y = φ_{e_0}(shift y)`, `φ_b(t) = 1/2 + (t−1/2)/4 + b/8`; fixed points 1/2, 2/3 differ (non-trivial); supp ⊂ `[1/2, 2/3]` | ✅ docstring IFS correct |
| Separation / ratio / homogeneity | none required; τ-condition automatic for finite IFS | homogeneous r = 1/4 | ✅ |
| Regularity of F | `C²` on `[0,1]` (Manai: nbhd of `[0,1]`) | `ContDiffOn ℝ 2 F U`, U open ⊇ `[1/2,1]`; F arbitrary off U | ✅ after affine change (pushforward only sees F on supp μ) |
| `F'' ≠ 0` | on `[0,1]` (main clause) | `deriv (deriv F) t ≠ 0` on `[1/2,1]`; on open U `deriv (deriv F)` is the true F'' | ✅ stronger than needed (supp ⊂ `[1/2,2/3]`) |
| Constants | η uniform in F, C explicit in F | `∃ C δ` per F | ✅ weaker |
| Range of ξ | all real ξ ≠ 0 | all real ξ ≠ 0, `C|ξ|^{-δ}` | ✅ |
| Sign convention | `e^{-2πiξx}` | `e^{+2πiξF}` | ✅ modulus even in ξ |
| Window | `[0,1]` | `[1/2,1]` | ✅ `A(s) = 1/2 + s/2`: `ν := A^{-1}_*μ` is stationary for `ψ_b(s) = s/4 + b/4` on `[0,1]`, `F_*μ = (F∘A)_*ν`, `F∘A` is `C²` on `A^{-1}(U) ⊇ [0,1]`, `(F∘A)'' = F''∘A / 4 ≠ 0` on `[0,1]` |
| Vacuity | - | integrand bounded, `cantorReal` measurable (pointwise limit of partial sums), so `pushFourier` is the genuine transform; hypotheses inhabited (√ below) | ✅ not vacuous |

**Downstream √.**  `Real.sqrt` is `C^∞` on `U = Ioi 0 ⊇ [1/2,1]`, `√'' = −t^{−3/2}/4 ≠ 0`.  Note √ is **not** `C²` on `[0,1]` itself (fails at 0), so the window/rescaling step is load-bearing, not cosmetic: applying BB to μ on `[0,1]` with F = √ directly would be illegal.  The Prop routes around it correctly.  `sqrt_bakerBanaji_hyp` is true as stated (99%).

**Residual risk (7%).**  Only the published proof of BB Thm 1.4 itself (refereed, Math. Ann.; independently matched by Algom–Rodriguez Hertz–Wang for the analytic case); plus a Lean-encoding slip I did not machine-check (`ContDiff` order literal `2 : WithTop ℕ∞`, which is the usual `C²`).

**Minimal repair.**  None needed.  Optional cosmetic: the docstring's "C² on a neighbourhood of `[0,1]` with F'' ≠ 0 on `[0,1]`" is Manai's paraphrase; BB's own hypothesis is `C²` on `[0,1]`, which ours implies.

**Probe** (`probes/bakerbanaji_sqrt_decay_probe.py`, exit 0).  Exact average over all 2^20 coin prefixes (40 binary digits; tail phase error ~1e-12), so no Monte Carlo noise.  √: `|FT|` falls from 0.18 (ξ = 2^8) to 0.010-0.023 (ξ = 2^18..2^20), fitted exponent ≈ −0.31 over k = 8..20 (non-monotone, as expected from 4-adic resonances).  Affine control `F = 4t`: modulus `Π_k |cos(π ξ 4^{-k}/2)|`, hand-computed; at ξ = 2·4^j it is a constant ≈ 0.6926 (matched to 1e-6, j = 2..9: no decay), and at ξ = 4^j it is exactly 0 (factor `cos(π/2)`).  So the probe separates the curved case from the affine sibling, consistent with `not_polyDecay_rat_affine`.
