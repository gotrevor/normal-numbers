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

## SD sector after the 2026-09-20 laps (`G4WiringRough.lean`, sorry-free, axiom-clean, verified 20:11 EDT)

`CRTConstant` is no longer the input.  N1 in schedule form (`J = windowJ N`) is a theorem from strictly
weaker, individually probed nodes, and the small-prime half is machine-checked:

```
[N1] CRTConstantSched h   🟢 crtConstantSched_of_roughAt / isNormal_G4_of_parity / isNormal_G4_of_prefixLimit
   ├── N1a  smooth CRT half              🟢 smoothWindowCRT (periodic_mean_close, primorial-periodicity), and
   │        SmoothNonvanishing at y = 2  🟢 smoothNonvanishingAt_two: |cos(πh/4^j)| ≠ 0 ⟺ ¬ChowlaSector
   ├── N1a′ SmoothRoughDecoupling        🟡→ reduced: both halves are EXACT covariance identities at y = 2
   │        └── [N1a″] ParityDiscrepancy h  🔴 = the rough mean moves by O(1/log N) when the scale halves
   │              (parityDisc_eq_scale; probe 9 ✅: flat in N, C ≈ 1.5, decays 4^{-j} in the site)
   └── N1b  RoughIndependenceAt h 2      🔴 the crux: rough window mean = c(J)·∏ rough site means, rel. O(1/log N)
            (probe 8 ✅: C ≈ 0.8/log x, bounded in J)
            └── [N1b′] PrefixLimit h     🔴 relative prefix correlation at step k → ρ k with |ρ k| ≤ C/4^k
                  (probe 10 ✅: ρ = 0, 0.82, 0.32, 0.03, 0.004 at h = 5; ρ 1 = 0 forced; J-uniformity now DERIVED)
                  ⚫ "c = 1" (full decorrelation) REFUTED: E∏r_j/∏Er_j → 1.14 / 0.69 / 2.32 at h = 1/3/5
```

Both surviving nodes compare a rough mean at scale `N` with one at scale `αN` or with a product of shorter
correlations; a single summatory node `R(M) = M·c·(log M)^κ(1 + O(1/log M))` for the `k`-site rough
correlation sums would yield both (lap HANDOFF §"Next steps" item 2).  That node *is* Selberg–Delange with
shifts (N1c generalised to `k` sites), so the crux has not become classical; it has become one statement.

**Probe 11 (Ren, 2026-09-20 20:32 EDT, `probes/summatory_node.py`, data `probes/data-2026-09-20-summatory-node*.txt`)** -
the summatory node `R_k(M) = Σ_{m<M} ∏_{j≤k} e(h ω_{>2}(m+j)/4^j) = c_k·M·(log M)^{κ_k}(1+O(1/log M))`
with `κ_k = Σ_{j≤k}(e(h/4^j) − 1)` ✅ consistent: at `M = 2^26` the fitted exponent lags the prediction by the
same amount as the known-answer control `k = 1` (classical SD), `Q_k` moves `< 1%` per doubling (`h = 1, 3`),
prefix ratios `|Q_k/Q_{k−1}| → 1` geometrically, singleton secondary terms decay like `4^{-k}` (the prefix
secondary does not: `0.26` flat in `k`), `|c_{\{k\}}| → 1` geometrically.  Parity-class constants equal to
within the expected `O(1/log M)` scale term (not sharply tested).  `h = 5` is the hard regime
(`Re κ = −2.5`, main term `M/(log M)^{2.5}`): same shape, larger secondary.  Frozen as `RoughSummatory h` in
`KICKOFF-2026-09-20-summatory-node-lap.md` with `C/log M` (prefix) and `C·4^{-k}/log M` (singleton) errors;
the parity-class form removes the bootstrap circularity of HANDOFF item 1.

## SD sector after the summatory laps (`G4WiringSummatory.lean`, `G4SummatorySplit.lean`; sorry-free, axiom-clean, verified 22:36 EDT)

```
[N1] CRTConstantSched h   🟢 from RoughIndependenceAt h 2 ∧ ParityDiscrepancy h (isNormal_G4_of_parity)
   ├── RoughIndependenceAt h 2   🟢 roughIndependenceAt_two_of_summatory   ⎫
   └── ParityDiscrepancy h       🟢 parityDiscrepancy_of_summatory         ⎬ from ONE node:
[N1s] RoughSummatory h   🟢 roughSummatory_of_split, from                  ⎭
   ├── RoughSummatoryPrefix h  🔴 THE CRUX: SD with k DISTINCT SHIFTS, Σ_{m<M} ∏_{j≤k} z_j^{ω_{>2}(m+j)} on each
   │        parity class, same constant, rel. error C/log M, uniform in k ≤ windowJ M
   │        (probe 11 ✅ exponents κ_k = Σ(z_j−1); probe 12 ✅ parity-class constants equal to O(1/log M))
   │        ⚫ pointwise truncation of the shift product REFUTED (exists_re_sdExponent_le_neg_one: Re κ ≤ −1 past
   │          v₄(h), so the budget is M/(log M)², and any truncation costs M·log log M/(log M)²)
   └── SDOdd h                 🟡 CLASSICAL, not in Mathlib: Landau–Selberg–Delange for n ↦ z^{ω_{>2}(n)}, no shift,
            odd n only, rel. error C·4^{-k}/log X (the 4^{-k} is analyticity in z, exact at z = 1);
            the even class is DERIVED (2-adic unrolling, ω_{>2}(2m) = ω_{>2}(m)) - the singleton
            parity-class clause is a theorem, not a hypothesis.
```

Headline: `isNormal_G4_of_oddNode : (∀ h≠0 off Chowla, RoughSummatoryPrefix h) → (∀ h≠0 off Chowla, SDOdd h) →
(Chowla → WindowDecay) → SiteDecayFull → IsNormal 4 G₄`.  Everything between the two primitive objects and
normality is machine-checked.  The crux is a named classical-shaped statement: for k = 2 it is the Ingham/Estermann
shifted-divisor asymptotic for ω-twists; for k ≥ 3 it is open territory.  The one route that would change the class
of the problem (`HANDOFF-2026-09-21-summatory-split.md` §Next lap): can the G₄ wiring run with k ≤ K FIXED instead
of k ≤ windowJ M?  That is a question about `G4WiringCRT`/`G4WiringRough`, not about the node.

**Probe 13 (Ren, 22:43 EDT, `probes/window_truncation.py`): the fixed-K question is settled - ⚫ NO for fixed K,
✅ YES for K ≈ log₂log₂log₂N.**  `|W_K − W_J|` scales like `4^{-K}` (`0.33 / 0.10 / 0.023 / 0.005` at `K = 1..4`, `h = 1`,
`N = 2^24`) and does not shrink with `N` at fixed `K`; the L¹ bound `4π|h|·(avg ω)·4^{-K}/3` holds with ~4× slack.
Since the tail is controlled by the window AVERAGE of ω (≈ log log N, `sum_omegaR_add_le`) rather than its maximum
(≈ log N, which is what `windowJ` was built for), the schedule drops from double-log to triple-log.  Consequence for the
graph (lap fired 22:43): a new minimal node **N0′ `WindowDecayK`** and the crux in **o(1) form, no sectors**:
`PrefixDecay h`: `∑_{m<M} ∏_{j≤k} e(h ω(m+j)/4^j) = o(M)` uniformly for `k ≤ windowK M`, every `h ≠ 0`, with
`isNormal_G4_of_prefixDecay`.  The SD-sector asymptotic route (`RoughSummatoryPrefix` + `SDOdd`) stays as the route with
main terms; `PrefixDecay` is the route where Elliott/Tao–Teräväinen-type *decay* technology lives (its two known
barriers: `k → ∞`, and all scales rather than a log-density-1 set).  It does not change the class of the problem; it
states it in the weakest form the wiring can use.

## Minimal route after the windowK lap (`G4WindowK.lean`, sorry-free, axiom-clean, verified 23:35 EDT)

```
IsNormal 4 G₄  🟢 isNormal_G4_of_prefixDecay
   ▲
[N0″] PrefixDecay h  (∀ h ≠ 0)   🔴 THE CRUX, o(1) form, NO SECTORS:
        ‖Σ_{m<M} ∏_{j≤k} e(h ω(m+j)/4^j)‖ ≤ ε M  eventually, uniformly for 1 ≤ k ≤ windowK M = ⌊log₂log₂log₂M⌋+1
   ▲ 🟢 windowDecayK_of_prefixDecay
[N0′] WindowDecayK h              (window mean along the TRIPLE-log schedule → 0)
   ▲ 🟢 windowDecay_of_windowDecayK  (window_tail_tendsto_zero: dropping sites above windowK costs ≤ 28π|h|/log₂log₂N,
   │                                  because only the window AVERAGE of ω enters - sum_omegaR_add_le - not its maximum)
[N0]  WindowDecay h               (double-log schedule windowJ; the old minimal node)
```

Two routes into `PrefixDecay`: (1) the SD-sector asymptotic chain above (`RoughSummatoryPrefix` + `SDOdd`, plus a
separate Chowla-sector argument); (2) a direct Elliott/Daboussi-type decay for `k ≤ log₂log₂log₂M` shifted ω-twists.
The triple-log shift count is the leverage for (2): a shift-uniform loss of `exp(O(k))` per shift is now affordable.
Known barriers for (2) stand: `k → ∞` (Tao–Teräväinen 2025 is two-point) and all scales vs a log-density-1 set.

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
   **Window version (13:57)**: J = 1..4 sites (z_j = e(1/4^j)), same normalisation with the exact local
   factor L_p = (1/p)Σ_r ∏_{p|r+j} z_j: c(y,J)·log x stable in x to three digits and *bounded in J* -
   y=1: 1.13 / 1.20 / 1.22 (J = 2,3,4); y=3: 0.32 / 0.40 / 0.43; y=10: 0.12 / 0.16 / 0.17; y=100: 0.010 /
   0.008 / 0.008.  Far sites add almost nothing (|z_j − 1| → 0), so the residue converges in J.  N1b holds
   at the window level with error ≍ 1/(y log x), uniformly in J on the range measured.  `--rough-window`;
   data `instruments/data-2026-09-20-rough-window-h1.json`.

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

