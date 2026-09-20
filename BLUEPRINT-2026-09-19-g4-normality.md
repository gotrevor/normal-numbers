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
   │             └── [N1c] two-point case ∑ z^{ω(n)} w^{ω(n+1)}       ❓ literature question first
   │      [N3] SiteDecayFull   🟡  Delange–Wirsing–Halász, not in Mathlib
   │
   └── v₂(h) odd   (Chowla sector: z_j = −1 at j = (v₂(h)+1)/2, CRT prediction singular)
          [N2] WindowDecay h directly   🔴  Chowla-type: 𝔼 (−1)^{ω(n+j)} · (other sites) → 0 at every scale.
                 ⚫ CRTConstant h refuted here (probe 2026-09-19: ratio wanders 2.5…45, W at √N floor)
                 known: log-averaged two-point (Tao 2016), density-1 set of scales (KMT 2023) — neither
                 gives all scales, which Weyl needs.  Numerically W ≈ N^{-1/2}: decay is robust, proof is hard.
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
2. N1 at h = 4·odd, 16·odd (v₂ even but ≥ 2): the leading site is trivial (phase ∈ ℤ) — does the law hold
   with the first nontrivial site as leader?
3. N2 at h = 6, 8, 24: is |W|√N bounded (noise floor) at every Chowla-sector h, or does some h show a
   polylog main term the sector classification missed?
