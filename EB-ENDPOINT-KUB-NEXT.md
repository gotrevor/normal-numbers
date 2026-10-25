# EB endpoint without FDEK: the Kubilius-model route 🎯

**Objective:** make `src/NormalNumbers/CoefmassErdosBorweinEndpointKub.lean` sorry-free.  The
headline `ebPowerCandidateNormal_of_kubilius` must be axiom-clean (`[propext, Classical.choice, Quot.sound]`).

**Do not change** any statement in that file; they are verbatim from the KB packet.  `KubiliusTV` is a
named HYPOTHESIS: never prove, weaken or axiomatize it.  Helpers go above the theorems or in a new
`CoefmassErdosBorweinEndpointKubAux.lean`.  No `native_decide`, no new `axiom`.
**NEVER git push:** `research/eb-endpoint` is local only.

**Reuse what is proved.**
- Step 1, the criterion: `ebRandom_ae_normal_of_divisorVariance_diverges`.
- The FDEK assembly: `ebRandom_ae_normal_le_ln2_of_EK` and `ebPowerCandidateNormal_of_EK`.  Copy their
  structure; only Step 2's input changes.
- The deterministic chain bound and prime-jump walk cap in `CoefmassErdosBorweinEndpointEK*.lean`
  (`prove endpoint prime-jump walk cap`, `finite-cutoff walk bridge`).  They do not use FDEK.
- Mertens: `RS_prime.mertens_second_theorem'`, i.e. `∃ C, ∀ x ≥ 2, |Σ_{p ≤ x} 1/p − log log x| ≤ C`
  (axiom-clean).

## Plan for `divisorVariance_diverges_at_ln2_of_kubilius`

Write `L = log log N`, `z = ⌊exp((log N)^{1−η})⌋`, and `S(n) = (n+a₀).primeFactors.filter (· ≤ z)`.
1. **Reduce to primes ≤ z.**  The chain bound only uses primes `p ≤ z`.  So `{W ≤ T}` is contained in
   `{S(n) ∈ A_N}`, where `A_N` is the set of prime sets on which the walk
   `#(S ∩ [1,p]) − log log p` stays `≤ C_T + log₂(2L)` at every `p ∈ S` with `P₀ < p`, or `#S > 2L`.
   This is deterministic and decidable on finite sets.
2. **Shift and transfer.**  `n ↦ n + a₀` moves `[1, N]` by `a₀`, a density change `≤ 2a₀/N`.  Apply
   `KubiliusTV` at `(N + a₀, z)`.  Here `u = log N/log z ≈ (log N)^η → ∞`, so `u^{−u} → 0`.  So
   `density ≤ kubiliusMass z A_N + o(1)`.
3. **The model.**  Under `kubiliusMass`, `S` is an independent Bernoulli(`1/p`) subset of the primes `≤ z`.
   Show `kubiliusMass z A_N → 0` with an elementary independent-sum argument; no CLT is needed.
   - `#S > 2L` has small mass: mean `Σ 1/p ≤ L + C` by Mertens; use Chebyshev.
   - **Crossing.**  Group the primes into geometric blocks in `u = log log p`, with ratio `r` (say `r = 16`)
     over `u ∈ [log log P₀, (1−η)L]`.  That is `≍ log L` blocks, and they are independent.
   - In each block the centered increment `Δ` has variance `σ² ≍` block length.  By fourth moments,
     `P(Δ ≥ σ/2) ≥ q > 0`, uniformly.  Use `E Δ = 0`, `E Δ⁴ ≤ 3σ⁴ + σ²` for centered Bernoulli sums,
     and Paley–Zygmund on `Δ⁺`.
   - The running value before a block is `≥ −M·√(previous length)` except with probability `≤ 1/M²`
     (Chebyshev), and `√(previous) ≤ σ/(4M)` for `r` large.  So each block independently crosses the
     cap `C_T + log₂(2L) = o(σ)` with probability `≥ q/2`.
   - Hence `P(no crossing) ≤ (1 − q/2)^{#blocks} + #blocks/M² → 0`: choose `M`, then `N` large.
     Mertens keeps the centering `Σ_{p ≤ x} 1/p` within `O(1)` of `log log x`.
4. Conclude `density{W ≤ T} → 0`.

## Assembly
`ebPowerCandidateNormal_of_kubilius`: as `ebPowerCandidateNormal_of_EK`, with Step 2 from the Kubilius
route.

**Verify:** `lake build NormalNumbers.CoefmassErdosBorweinEndpointKub`, then `#print axioms` on both theorems.
