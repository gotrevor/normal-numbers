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
