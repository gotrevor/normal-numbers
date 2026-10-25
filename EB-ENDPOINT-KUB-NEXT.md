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
   - **Crossing, with constants chosen in the right order.**  Fix `K` (number of blocks), then `M`, then a
     ratio `r ≥ 64·M²`, enlarged by any fixed numerical factor needed below.
     - Take `K` geometric blocks `[u_k, r·u_k]` in `u = log log p`.  A floor-friendly concrete
       schedule is `s_k = r^k/(4r^K)`, `u_k = s_k L`, with natural endpoints
       `⌊exp((log M)^s_k)⌋` for `M = N+a₀`.  The last block ends at exponent `1/4`, below the
       Kubilius cutoff exponent `1/2`; the first exponent is fixed and positive, so its endpoint
       eventually exceeds `collisionCutoff N`.  The blocks are independent.
     - The cap `C_T + log₂(2L) + O(1)` is `o(σ_k)`, since every fixed `s_k` is positive and each
       block variance grows linearly in `L`.
     - Each centered block increment `Δ_k` has variance `σ_k² ≍ (r−1)·u_k`.  The proved finite-law
       bound `bernoulliSubsetMass_blockCenteredSum_ge_sqrt_eighth` gives
       `P(Δ_k ≥ σ_k/8) ≥ 1/64` once `σ_k² ≥ 1`, from `E Δ = 0` and
       `E Δ⁴ ≤ 3σ_k⁴ + σ_k²`.  (The earlier `σ_k/2` threshold did not follow from those moments alone;
       the smaller fixed threshold is sufficient.)
     - Control the **centered reciprocal-prime prefix**
       `X(a_k) = #(S ∩ [1,a_k]) − Σ_{p≤a_k} 1/p` directly.  It is `≥ −M·√(u_k)` except with
       probability `≤ 1/M²` (Chebyshev).  At the block endpoint,
       `ω(S;b_k) − log log b_k = X(a_k) + Δ_k + (Σ_{p≤b_k}1/p − log log b_k)`, so Mertens is
       spent only once, at `b_k`; no start-point Mertens loss is needed.  Enlarge `r` after choosing
       `M` so that the start loss, the fixed Mertens constant, and the logarithmic cap together are
       at most `σ_k/8`.
     - `P(no crossing) ≤ (63/64)^K + K/M²`: choose `K` with `(63/64)^K < ε/2`, then `M` with
       `K/M² < ε/2`, then `r`.
     - A crossing at a block end gives a crossing at a prime jump `p > P₀` inside the block, because the walk
       only decreases between jumps.
     - Mertens keeps the endpoint centering `Σ_{p ≤ b_k} 1/p` within `O(1)` of `log log b_k`.
4. Conclude `density{W ≤ T} → 0`.

## Assembly
`ebPowerCandidateNormal_of_kubilius`: as `ebPowerCandidateNormal_of_EK`, with Step 2 from the Kubilius
route.

**Verify:** `lake build NormalNumbers.CoefmassErdosBorweinEndpointKub`, then `#print axioms` on both theorems.
