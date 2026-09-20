# Blueprint: normality of G₄ = ∑_p 1/(4^p − 1) (hypothetical blueprint, moonshot lane)

Conjecture graph, 2026-09-19 21:10.  A node is a frozen Lean Prop; an edge is a wiring theorem.
Status: 🟢 proved (axiom-clean) · 🟡 classical, not formalized · 🔴 open conjecture · ⚫ refuted.
Files: `src/NormalNumbers/G4WiringCRT.lean`, `WeylCriterion.lean`, `DyadicToPrefix.lean`, `Wall.lean`.

```
IsNormal 4 G₄
   ▲ 🟢 isNormal_G4_of_windowDecay        (W1 Wall + W3 Weyl + W4 dyadic→prefix + L1 tail, all proved)
   │
[N0] WindowDecay h  for all h ≠ 0 :  W_{J_N}(N) = 𝔼_{[N,2N)} ∏_{j≤J_N} e(h 4^{-j} ω(n+j)) → 0,  J_N = ⌈log₂log₂N⌉+1
   │
   ├── v₂(h) even  (SD sector: every site's CRT main term nonvanishing)
   │      ▲ 🟢 fullWindowMean_tendsto_zero_of_law
   │      [N1] CRTConstant h   🔴  W = c_J ∏ m_j (1 + O(1/log N)), uniform in J.  Measured to 10⁸ (§2f).
   │             ├── [N1a] small-prime part = CRT local factor         🟡 fundamental lemma (provable)
   │             ├── [N1b] P-rough parts asymptotically independent    🔴 the crux ("SD with shifts")
   │             └── [N1c] two-point case ∑ z^{ω(n)} w^{ω(n+1)}       🔴 open: DT 2019 does τ_z × τ (full divisor
   │                    function); TT 2025 gives only (log N)^{-c} decay, below the (log N)^{-1} main term
   │      [N3] SiteDecayFull   🟡  Delange–Wirsing–Halász, not in Mathlib
   │
   └── v₂(h) odd   (Chowla sector: z_j = −1 at j = (v₂(h)+1)/2, CRT prediction singular)
          [N2] WindowDecay h directly   🔴  Chowla-type: 𝔼 (−1)^{ω(n+j)} · (other sites) → 0 at every scale.
                 ⚫ CRTConstant h refuted here (probe 2026-09-19: ratio wanders 2.5…45, W at √N floor)
                 known: log-averaged two-point (Tao 2016), density-1 set of scales (KMT 2023), and the frontier
                 Tao–Teräväinen 2025 Thm 3.1: two-point, natural averages, (log N)^{-c}, all scales outside a
                 log-density-o(1) exceptional set.  TT §4: triple correlations + exceptional-set removal are
                 "not within current technology".  Numerically W ≈ N^{-1/2}: decay is robust, proof is hard.
```

## What would move a node

- **N1c (two-point SD)**: settle whether ∑_{n≤x} z^{ω(n)} w^{ω(n+1)} has a known asymptotic for fixed
  |z| = |w| = 1 (Erdős–Pomerance/Halberstam give the CLT scaling and moments only).  If open, it is the
  cleanest self-contained research sub-target: divisor expansion + Bombieri–Vinogradov for multiplicative
  functions (Granville–Shao) covers d ≤ x^{1/2−ε}; the large-d bilinear range is the open half.
- **N1 (uniform in J)**: probe J = 24 → 64 at h = 1, 3, 5 to check the far sites really contribute nothing
  (the lap's `∀ᶠ N, ∀ J` strengthening is unmeasured beyond J = 24).
- **N2**: no route at ordinary averages without a Chowla-type advance.  A conditional edge "corrected
  Elliott at k = J_N ⟹ N2" needs uniformity in k that the standard conjecture does not state; do not freeze
  a fabricated conjecture.  Record, don't wire.
- **N3**: known-results lane; large (Halász).  Only worth it once N1 or N2 moves.
- **Sparse cousin** (`G4WiringSparse.lean`): same graph with ω_𝒫, where N2's analogue is KMT Prop 4.3 —
  the one place the Chowla-type node is a theorem.  That is why it is the programme's live target.

## Refutation targets (cheap, run before proving)
1. ✅ PASSED 2026-09-19 21:05: N1 at h = 1, 3, 5, N = 10⁷ and 10⁸, J = 8, 16, 24, 32 — the constant is
   identical to four decimals across J (far sites add ≤ h·log₂N/4^j to the phase; J > 32 is below double
   precision and below relevance).  `∀ᶠ N, ∀ J` is safe.
2. ✅ PASSED 21:15: h = 4, 16 reproduce h = 1 exactly, h = 12 tracks h = 3 (h → 4h shifts the window by
   one site; the mean is shift-invariant).
3. ✅ PASSED 21:15: h = 6, 8, 24 all at the noise floor (|W|√N ≈ 0.5 … 2.3), ratios random (118, 2.5, 118 →
   146, 3.1, 145).  The sector classification {v₂(h) odd} is exact.
4. ✅ PASSED 23:05: N1's *rate*.  Log-log slope of |c/CRT − 1| vs log N is −1.01 (h=1), −1.29 (h=3),
   −0.99 (h=5) over N = 10⁶ … 10⁸.  The coefficient κ (c/CRT = 1 + κ/log N) matches the Hardy–Littlewood
   coupling through cofactor sizes, κ_B = −Σ_j (z_j−1) Σ_p (log p/(p−1))[Π_{r(j)}/μ_p − z_j/(1+(z_j−1)/p)]:
   h=1 fit −0.55−0.93i vs κ_B −0.59−0.83i (10%, no free parameter); h=3 fit 2.6−2.1i (spread 2.1…3.8) vs
   3.34−2.00i; h=5 low power (κ₂/log N ≈ κ).  The multiplicative-model coefficient κ_A (Selberg–Delange on
   ζ(s)∏(1+b_p p^{-s})) is in the wrong quadrant and its amplitude ∏Γ(z_j)/Γ(Z) = 2.6, 0.12, 46 is refuted
   by c/CRT → 1.  KB verdict §4h; `lambert_carry_probe.py --window-rate-fit data-2026-09-19-window-rate-sweep.json`.
   Was: N1's *rate*.  c/CRT − 1 should be ≍ 1/log N with a computable coefficient (next Selberg–Delange
   term); fit the coefficient at h = 1, 3, 5 from N = 10⁶ … 10⁸ and compare with the derivative of the
   local factor.  A wrong sign or a wrong order would be the first crack in the SD law.
5. ⚫ **Divisor-expansion route to N1c is numerically dead** (2026-09-20 13:40).  Writing
   z^{ω(n)} = Σ_{d|n} μ²(d)(z−1)^{ω(d)} splits T = 𝔼 z^{ω(n)}w^{ω(n+1)} (z = i, w = e(1/16), the h=1 sites 1,2)
   into a d ≤ x^θ part (Bombieri–Vinogradov-for-multiplicative-functions range, Granville–Shao) and a
   bilinear tail.  At x = 3·10⁷, |T| = 0.251 while the d > x^{1/2} tail is 0.41 and the partial sums swing
   to 4|T| at small θ: the tail is not a correction, it carries the sign.  The route needs the open half
   to give an *asymptotic*, not an upper bound.  `--two-point-split`; data
   `instruments/data-2026-09-20-two-point-split-h1-s12.json`.
6. ✅ **N1b (rough parts asymptotically independent) PASSED** (13:41).  For ω_{>y} = primes above y,
   R(y,x) = 𝔼[z^{ω_{>y}(n)}w^{ω_{>y}(n+1)}] / (𝔼 z^{ω_{>y}(n)} · 𝔼 w^{ω_{>y}(n+1)}) divided by the CRT product
   ∏_{p>y}(1+(z+w−2)/p)/((1+(z−1)/p)(1+(w−1)/p)) satisfies |R/CRT − 1| = c(y)/log x with c(y) stable to
   three digits across x = 10⁶, 10⁷, 3·10⁷ (y=1: 1.15, 1.14, 1.13; y=3: 0.319, 0.319, 0.317; y=10: 0.119,
   0.122, 0.122) and c(y) ≈ 1/y (y = 1, 3, 10, 30, 100 → 1.14, 0.32, 0.12, 0.03, 0.010; floor ≈ 10⁻³ from
   y ≥ 1000, the 1/√x noise on the ratio).  So the rough two-point correlation factorises up to the CRT
   product with the same 1/log x cofactor-coupling residue as target 4 (Σ_{p>y} log p/p² ≍ 1/y).
   `--rough-independence`; data `instruments/data-2026-09-20-rough-independence-h1-s12.json`.

- **N1c, TT 2025 read closely (13:36)**: Thm 3.1(ii) applies to g = z^{ω} with L = (log X)^{1−Re z}
  (M(g;X²,·) ≍ (1−Re z) log log X), giving 𝔼 z^{ω(n)}w^{ω(n+1)} ≪ (log N)^{−c(1−Re z)} off a
  log-density-L^{−c} exceptional set, with c "sufficiently small" and never stated.  The expected main
  term is ≍ (log N)^{(Re z−1)+(Re w−1)}, smaller than the bound for every z, w since c < 1: TT never
  captures the main term at any site, including the far sites where z_j → 1.  N1c stays open at every site.

## Sparse-𝒫 node probes (2026-09-20)
5. ✅ NOT REFUTED 13:20: the frozen `KMT_quant₂` shape on three prime sets (π-indexed leaf-6 set, p ≡ 1 mod 4,
   a two-block set), x ≤ 10⁸, J ≤ 3, h = 1: LHS/(t1+t2+t3) ≤ 0.15 at every admissible ε, non-increasing in x.
   ⚠️ Low power: the admissible window (1/log log x, 1/2) is (0.36, 0.5) here and exp(−1/(8J²ε)) ≥ 0.7, so the
   Prop is satisfied by C₂ ≥ 1.5 regardless of arithmetic.  Measurable sharpening: LHS ≤ 1.6·exp(−S_𝒫(⌊x^ε⌋))
   (Euler-product picture).  `lambert_carry_probe.py --kmt-probe`; data in the KB instruments dir; KB verdict §4l.

