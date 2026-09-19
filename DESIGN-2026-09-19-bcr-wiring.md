# DESIGN 2026-09-19 — the BCR wiring node: `IsNormal 4 G₄` from a frozen quasi-independence hypothesis

Author: Ren / Fable 5.1, attended session 2026-09-19.  **Prep only; no lap launched.**  KB source of truth: `claude/knowledge/core/projects/normal-numbers-fable-verdict-2026-09-19.md` (§§1–4).  This document freezes the conjecture node and lists the wiring theorem's exact obligations against what the repo already has.

## 0. Verdict that motivates this node

Normality of the unchanged `G₄ = primeLambertAtBase 4` is, for every `h ≠ 0`, the vanishing of the ordinary dyadic mean of `∏_{j≤J} e(h4^{-j} ω(n+j))` with `J ≍ log₄ log log N`.  That is an ordinary-average, all-scales, growing-window instance of the Elliott conjecture; no 2026 technique reaches it (literature checked through Guo Aug-2026, Pilatte Apr/Sep-2026).  The prime-peeling criteria of 2026-09-19 ((7), `C_N → 0`, (BL)) are restatements.  Measurements to `N = 10⁸` show the truncated means are governed by the **product of one-site truncated means** up to a bounded cross-site factor (≤ 6 for `h = 1,2,3,6,7` and the parity control).  The honest conjecture-graph node is therefore **quasi-independence up to a constant**, not asymptotic independence.

## 1. The frozen node (Prop, to be stated in Lean, never proved here)

Notation (all in `ℝ`/`ℂ`, `n` ranges over `Finset.Ico N (2N)`):

- `ωle (P : ℕ) (m : ℕ) : ℕ := (m.primeFactors.filter (· ≤ P)).card` — truncated distinct-prime count.
- `phase (t : ℝ) : ℂ := Complex.exp (2πi t)`.
- `siteMean (N P : ℕ) (h j : ℤ) : ℂ := (1/N) ∑_{n ∈ Ico N 2N} phase (h * 4^{-j} * ωle P (n+j))`.
- `windowMean (N P J : ℕ) (h : ℤ) : ℂ := (1/N) ∑_{n ∈ Ico N 2N} phase (h * ∑_{j=1}^{J} 4^{-j} ωle P (n+j))`.

```lean
/-- Bounded cross-site ratio (BCR): on the middle prime range the truncated
window mean is at most a constant times the product of the one-site truncated
means.  Conjecture-graph node; measured C ≤ 6 through N = 10^8 (KB verdict §2c). -/
def BCR (h : ℤ) (δ θ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ᶠ N in atTop, ∀ P : ℕ, (N : ℝ)^δ ≤ P → (P : ℝ) ≤ (N : ℝ)^θ →
    ‖windowMean N P (J N) h‖ ≤ C * ∏ j ∈ Finset.Icc 1 (J N), ‖siteMean N P h j‖
```
with `J N := ⌈2 * logb 4 (1 + log (log N))⌉₊` (the window schedule of the localization theorem; any `J` with `4^{-J}(1 + log log N) → 0` and `J = N^{o(1)}` works).

Guard by name, per `decisions/lean-decisions.md`: `BCR` is ratified as *this* statement.  Two sanity probes to ship with it (Prop-level, both must be provable, neither is the node):

- `BCR_trivial_bound`: with `C := 1 / ∏‖siteMean‖` the inequality is vacuous whenever the product is nonzero — so the node's content is the *uniformity* of `C` in `N, P`.  Record, do not "prove BCR" this way.
- `BCR_fails_for_smoothness_mask`: the §1 counterexample of the strategy note (`W_P = 1_{n+1 squarefree, P-smooth}`) is a bounded past-measurable weight for which the analogous ratio is unbounded — shows the node is about the *phase* rule, not measurability.  Optional.

## 2. The wiring theorem and its obligations

```lean
theorem isNormal_G4_of_BCR
    (hBCR : ∀ h : ℤ, h ≠ 0 → ∀ δ θ : ℝ, 0 < δ → δ < θ → θ < 1 → BCR h δ θ)
    (hSite : OneSiteDecay) :
    IsNormal 4 (primeLambertAtBase 4)
```
where `OneSiteDecay` is the second frozen input (classical, see §3):

```lean
/-- For every z on the unit circle with z ≠ 1 and fixed 0<δ<θ<1, the one-site
truncated mean tends to 0 uniformly for N^δ ≤ P ≤ N^θ. -/
def OneSiteDecay : Prop :=
  ∀ h j : ℤ, (h * 4^{-j} : ℝ) ∉ ℤ → ∀ δ θ, 0 < δ → δ < θ → θ < 1 →
    Tendsto (fun N => ⨆ P ∈ Icc (N^δ) (N^θ), ‖siteMean N P h j‖) atTop (𝓝 0)
```

Chain, with the repo/mathlib inventory (✅ exists, 🔨 to build):

| step | statement | status |
|---|---|---|
| W1 | `IsNormal 4 x ↔ Equidistributed (orbit 4 x)` | ✅ `Wall.isNormal_iff_equidistributed_orbit` |
| W2 | cell frequencies → `Equidistributed` | ✅ `Sandwich.equidistributed_of_badic` |
| W3 | **Weyl criterion**: `∀ h ≠ 0, (1/n)∑_{k<n} phase(h·u k) → 0` ⟹ every b-adic cell frequency → its length | ✅ **PROVED** 2026-09-19, `src/NormalNumbers/WeylCriterion.lean`, `equidistributed_of_weyl`, axiom-clean.  (Was: not in repo or mathlib.)  Route: squeeze `1_{[a,c)}` between continuous functions, approximate those by trigonometric polynomials via `span_fourier_closure_eq_top` (`Mathlib/Analysis/Fourier/AddCircle.lean:245`), finish with `ε/3`.  Bounded, one lap. |
| W4 | dyadic means → prefix means: if `(1/N)∑_{N≤n<2N} F(n) → 0` then `(1/n)∑_{k<n} F(k) → 0` (bounded `F`) | 🔨 elementary (dyadic decomposition, finitely many rounding endpoints). |
| L1 | tail: `|T(n) − T_J(n)| ≤ ∑_{j>J} ω(n+j)4^{-j}`, dyadic mean `≪ 4^{-J}(1 + log log N) + N4^{-N}` | 🔨 needs `∑_{m≤3N} ω(m) ≪ N(1+log log N)` — from `∑_{p≤x} 1/p ≤ log log x + O(1)`, which `G4Mertens.log_log_le_sum_inv_primesBelow` has in the lower direction only; the upper Mertens bound is mathlib's `Nat.Primes.sum_one_div_le`-type or `Chebyshev`; check `G4MertensAP` first. |
| L2 | localization: `|dyadic mean of e(hT) − C_N(δ,θ)| ≤ (δ/θ)^{c_h} + G_h log(1/θ) + o(1)` | 🔨 the peeling audit §6 proof: exact recurrence `A_{≤p} = μ_p A_{<p} + d_p` (finite algebra), `|Q(y,z)| → (δ/θ)^{c_h}` (needs the Mertens *rate* both ways: repo has `mertensRate_of_sumLog`), late primes (`∑_{z<p≤X} 1/p → log(1/θ)` + `π(X)/N → 0`). |
| L3 | **the new step**: `BCR + OneSiteDecay ⟹ sup_{N^δ≤P≤N^θ} ‖windowMean‖ → 0`, hence the middle term `C_N(δ,θ) → 0`.  Elementary from the definitions once L2 is in the form "middle term = windowMean at N^θ minus transported windowMean at N^δ". | 🔨 short |
| L4 | assemble: L1–L3 + W4 + W3 + W2 + W1, then `β → 0`, cuts to endpoints | 🔨 |

Estimated effort: W3 one Opus/low lap; L1–L2 two to three laps (the analytic prime sums are where laps stall — commit named `sorry` leaves per inequality); L3–L4 one lap.  No `native_decide`, no kernel-heavy computation anywhere.

## 3. Why `OneSiteDecay` is a separate frozen input, and what it costs

The one-site truncated mean `E e(α ω_{≤P}(n+1))` at `P = N^t` is the model `∏_{p≤P}(1 + (e(α)−1)/p)` times a factor that is **bounded but not universal in `t`** when `Re e(α) ≤ 0` (KB verdict §2d: at fixed `t = 1/2` it moves 0.69 → 1.22 as `P` runs 100 → 10⁴, the signature of `A(u) + B(u)(log P)^{−z}`).  Its proof needs Selberg–Delange plus a Dickman/Buchstab convolution with the discrete cutoff sum `∑_{n≤K} z^{ω(n)}/n` carried exactly.  Classical technology, not in mathlib (no Selberg–Delange, no Dickman function), and a multi-week formalization.  Freezing it is honest: it is a theorem in the literature's reach, the node `BCR` is not.

Cheaper unconditional surrogate for `OneSiteDecay`, if wanted: only *boundedness by a constant times a decaying scale* is used.  ⚠️ The scale must be the analytic one, `(log P)^{Re z − 1}` with `z = e(h 4^{-j})`, **not** the CRT product `∏_{p≤P}(1+(z−1)/p)`: at `z = −1` (h = 2, 6 at the leading site) that product is identically 0 from `p = 2` on, so a statement against it is vacuous or false (KB verdict §2e).  So `OneSiteDecay` may be replaced by

```lean
/-- Leading-site surrogate: the one-site truncated mean is bounded by the
Selberg–Delange scale on the middle range.  Measured against the CRT prefix at
z = ±i the ratio climbs 2.98 → 3.27 → 3.51 across N = 10^6..10^8 (top edge), so
the constant is not small; but it is classical (KB verdict §2e). -/
def OneSiteRatioBounded : Prop :=
  ∀ h j : ℤ, (h * 4^{-j} : ℝ) ∉ ℤ → ∀ δ θ, 0 < δ → δ < θ → θ < 1 → ∃ C : ℝ, ∀ᶠ N in atTop,
    ∀ P : ℕ, (N : ℝ)^δ ≤ P → (P : ℝ) ≤ (N : ℝ)^θ →
      ‖siteMean N P h j‖ ≤ C * (Real.log P) ^ (Real.cos (2 * π * h * 4^{-j}) - 1)
```

and `(log P)^{Re z − 1} → 0` is immediate for `Re z < 1`.  Provability (KB verdict §2e): on `P ≥ N^{1/2}` an exact one-large-prime identity reduces `siteMean` to full-ω Selberg–Delange means at scales `N/p`, and for `Re z = 0` the prime sum is bounded because `∫(1−t)^{z−1}dt = −(1−t)^z/z` has modulus `1/|z|` (it does not converge: the fixed-u ratio is `a(u) + b(u)(log N)^{−z}`, bounded and periodic in `log log N`, KB verdict §2e); down to `N^δ` the Buchstab expansion has depth `⌊1/δ⌋`.  Classical, multi-week to formalize (no Selberg–Delange in mathlib), but not a conjecture.  The measured phase of `siteMean / CRT prefix` rotates two thirds of a turn across the middle range at every N, so no *complex* proportionality to the CRT prefix should be stated.

Measured shape of `BCR` itself (KB verdict §2e): the ratio `windowMean / ∏ siteMean` is a slowly varying **real positive** factor, phase within ±0.015 turns (h = 1) and ±0.042 (h = 3) over the whole middle range at N = 10^8, magnitudes 1.1–1.4 and 0.3–0.65.  A future sharpening of the node is `∃ c_h > 0, windowMean / ∏ siteMean → c_h`; not frozen yet, the magnitude bound is what the wiring uses.

## 3b. The sharper node: `CRTConstant` (measured 2026-09-19, KB verdict §2f)

At full ω (no truncation) the ratio `windowMean / ∏ siteMean` converges geometrically in `J` (sites `j ≥ 4` move it < 0.5%) and approaches the CRT local factor `∏_p [1+∑_j(z_j−1)/p] / ∏_j(1+(z_j−1)/p)` at rate `≍ 1/log N` (|c/CRT| = 0.945, 0.955, 0.962 at h = 1 and 1.327, 1.257, 1.216 at h = 3 for N = 10⁶, 10⁷, 10⁸).  Frozen as a *stronger* node than `BCR`, for when a lap wants the untruncated route (no L1/L2 peeling at all):

```lean
/-- Hardy–Littlewood-type law for ω-phases: shifted correlations factor as the
CRT local density times one-site means, with a 1/log N error (measured shape). -/
def CRTConstant (h : ℤ) : Prop :=
  ∃ C : ℝ, ∀ J : ℕ, ∀ᶠ N in atTop,
    ‖fullWindowMean N J h - crtFactor h J * ∏ j ∈ Finset.Icc 1 J, fullSiteMean N h j‖
      ≤ C / Real.log N * ∏ j ∈ Finset.Icc 1 J, ‖fullSiteMean N h j‖
```

with `fullWindowMean`, `fullSiteMean` the untruncated versions of §1's means and `crtFactor` the absolutely convergent product.  `CRTConstant h` for all `h ≠ 0`, plus Selberg–Delange for the one-site means (classical, `|fullSiteMean N h j| ≍ (log N)^{cos(2πh4^{-j}) − 1}`) and the `J_N` schedule, gives `IsNormal 4 G₄` through W1–W4 plus the tail lemma L1, skipping the peeling layers L2–L3 entirely.  Not provable by any 2026 method (it is Elliott with a main term); it is the cleanest statement of what the numerics say.

Second wiring theorem (untruncated route; shorter than §2, and the one to lap first once W3 is green):

```lean
/-- Delange–Wirsing–Halász: a 1-bounded multiplicative f with ∑_p (1 − Re f(p))/p = ∞
has mean zero.  Here f(p) = e(h 4^{-j}) is constant on primes, so the series diverges
whenever e(h 4^{-j}) ≠ 1.  Classical; frozen as an input, not a node. -/
def SiteDecayFull : Prop :=
  ∀ h j : ℤ, (h * 4^{-j} : ℝ) ∉ ℤ → Tendsto (fun N => ‖fullSiteMean N h j‖) atTop (𝓝 0)

theorem isNormal_G4_of_CRTConstant
    (hLaw : ∀ h : ℤ, h ≠ 0 → CRTConstant h) (hSite : SiteDecayFull) :
    IsNormal 4 (primeLambertAtBase 4)
```

Chain: for each `h ≠ 0` pick `J₀` with some `j ≤ J₀` having `e(h4^{-j}) ≠ 1` (any `j` with `4^j ∤ h`); by `hLaw` at `J = J₀`, `‖fullWindowMean N J₀ h‖ ≤ (‖crtFactor h J₀‖ + C/log N) ∏_{j≤J₀} ‖fullSiteMean‖ → 0` by `hSite` (the product has a factor tending to 0 and the rest are ≤ 1).  Then L1 (tail, `4^{-J} (1 + log log N)` with `J = J_N ≥ J₀` eventually; the law is applied at `J = J_N`, so the `∀ J` in `CRTConstant` must carry uniformity of `C` in `J`: ⚠️ **freeze `CRTConstant` with `C` independent of `J`**, which the measurement supports since `c_h(J)` converges geometrically), then W4 (dyadic → prefix), W3 (Weyl), W2, W1.  Obligations: W1 ✅, W2 ✅, W3 ✅ (2026-09-19, one lap), W4 🔨 skeleton `DyadicToPrefix.lean`, L1 🔨 skeleton in `G4WiringCRT.lean` (crude `ω ≤ log₂` suffices with `J_N = log₂ log₂ N + 1`, **no Mertens**), assembly 🔨 `isNormal_G4_of_CRTConstant` with named leaves — `KICKOFF-2026-09-19-closing-lap.md`.  No Selberg–Delange, no Dickman, no peeling.  ⚠️ The Lean `CRTConstant` quantifies the constant existentially with a uniform bound `B`; its CRT identity is documentation, not part of the Prop.

## 4. What not to do

- Do not formalize the ledger, the covariance notation, (BL), or the band-freezing lemmas; they are restatements (KB verdict §1).
- Do not launch a treadmill from this document; Trevor fires it.  When he does: Opus/low, `--allow-from-agent`, branch off `wip/g5-prime-subset`, first lap = W3 only.
- Do not report `sorry` counts; report which row of §2 is green.

## 5. New node (2026-09-19, late): sparse prime subsets through KMT Proposition 4.3

KB verdict §4d.  Klurman–Mangerel–Teräväinen, arXiv:2304.05344, Prop. 4.3 is an ordinary-average,
every-scale k-point correlation bound in terms of truncated pretentious distances.  It gives nothing
for `G₄` (the leading site `i^ω` has truncated distance `≫ √log(1/ε)` on every range), but for
`c_𝒫(4) = ∑_{p∈𝒫} 1/(4^p − 1)` with `𝒫` of relative density 0 and `∑_{p∈𝒫} 1/p = ∞` it gives, for
every fixed `J` and `h ≠ 0`, `prefixMean (fun n => e(h · truncTail_𝒫 J n)) → 0` at every scale.

Frozen input to state in Lean (a theorem in the literature, not a conjecture):

```lean
/-- KMT 2023 Prop 4.3 specialised: shifts n+1, …, n+J, χ = 1, t = 0, fixed J. -/
def KMT_sparse (𝒫 : Set ℕ) : Prop :=
  ∀ J : ℕ, ∀ h : ℤ, h ≠ 0 → (∃ j, 1 ≤ j ∧ j ≤ J ∧ ¬ (∃ m : ℤ, (h : ℝ) / 4 ^ j = m)) →
    Tendsto (fun n => prefixMean (fun n => ePhase (h * truncTailS 𝒫 J n)) n) atTop (𝓝 0)
```

Wiring `isNormal_cP4_of_KMT_sparse (hSparse : …) (hDiv : ¬ Summable (fun p ∈ 𝒫 => 1/p))
(hKMT : KMT_sparse 𝒫) (hRate : …) : IsNormal 4 (TWeight.subset 𝒫).lambert 4`: same chain as
§3b with `TWeight.subset`, W3 fed prefix means directly (no W4), tail lemma in L¹ form
(`∑_{m≤X} ω_𝒫(m) ≤ X · S_𝒫(X)`, with `J_N := ⌈log₄ S_𝒫(3N)⌉ + 1`), and one extra hypothesis
`hRate` expressing that the fixed-`J` convergence is fast enough for `J = J_N` (the diagonal
condition; discharged by choosing `𝒫` sparse enough, or by a `k`-uniform reading of Prop 4.3).
Existence statement first: `∃ 𝒫, ¬Summable ∧ IsNormal 4 (c_𝒫 4)`.  Not fired; Trevor's call.

**Stated in Lean (2026-09-19, `src/NormalNumbers/G4WiringSparse.lean`, compiles):** `truncTailS`,
`windowMeanS` (prefix mean directly, no W4), `RelDensityZero`, `DivergentRecip`, `NontrivialWindow`,
the frozen `KMT_sparse S` (fixed `J`), the diagonal form `KMT_along S Jsched` actually consumed, and
`TailOK S Jsched`.  Tail: the crude `ω_S ≤ ω ≤ log₂` route works for every `S` with the same
`windowJ` as `G₄` (`tail_error_le_subset`, `tailOK_windowJ`), so the L¹ form above is not needed
unless one wants a slower schedule.  Wiring `isNormal_subsetLambert_of_KMT_along` (leaves
`orbit_eq_fract_tailB_subset`, `prefix_fourier_tendsto_zero`, one inline `fourierMean = prefixMean`
sorry), `isNormal_subsetLambert_of_KMT_windowJ`, and the existence theorem `exists_sparse_normal`
(sorry-free modulo `exists_relDensityZero_divergent`) under the hypothesis
`∀ S, RelDensityZero S → DivergentRecip S → KMT_along S windowJ`.  The gap between `KMT_sparse` and
`KMT_along S windowJ` is exactly the `k`-dependence of Prop 4.3 with `k = J_N ≍ log log N`.

**Sharper (same evening): existence needs no `k`-uniformity, only a growth bound on the constant.**
Prop 4.3 holds for *all* 1-bounded multiplicative `f_j` with a constant `C(k)` depending on `k` and
the shifts alone, so it is uniform over `𝒫`.  Specialised to `f_j = e(h 4^{-j} ω_𝒫)` the distances
are explicit (`𝔻(f_j,1;y,x)² ≤ 2 ∑_{y<p≤x,p∈𝒫} 1/p`; at the first nontrivial site `1 − cos ≥ 1`, so
`max_j 𝔻(f_j,1;y)² ≥ S_𝒫(y)`), giving the elementary frozen Prop `KMT_quant C`.  Block
construction: `𝒫 = ⋃ Bᵢ`, `Bᵢ ⊆ (xᵢ, xᵢ₊₁]`, `∑_{Bᵢ} 1/p = δᵢ = 1/i`, `xᵢ₊₁ ≥ xᵢ^{1/εᵢ₊₁}`,
schedule `J_N = Jᵢ` on `(xᵢ, xᵢ₊₁]`, `εᵢ = 1/(8Jᵢ² log i)`.  Terms: `C(Jᵢ)√(2/i)√log(8Jᵢ² log i)`,
`C(Jᵢ)/i^{1-o(1)}` (from `exp(−S_𝒫(x^ε))`, `S_𝒫(x^ε) ≥ log i − O(1)`), `C(Jᵢ)/i`; L¹ tail needs
`log i = o(4^{Jᵢ})`.  Sandwich `log C(Jᵢ) + ω(1) ≤ log i ≤ o(4^{Jᵢ})` is solvable iff
`log C(k) = o(4^k)`.  `exists_sparse_normal_of_KMT_quant` states this; `tail_error_L1` is the slow-
schedule tail.  Reading KMT §4.1–4.2, `C(k)` collects `(log k)^k` (sum over `e_j ∣ A^∞`,
`A ⊇ ∏_{p<k} p`), the dimension-`k` fundamental lemma (IK 6.3, constant in `κ = k` and
`K = exp(O(k/log k))`), dimension-`k` Mertens products, and the smooth-number truncation
`d_j ≤ x^{1/(4k)}`, which needs only `kε → 0` (the paper's fixed `exp(−1/(2ε))` form silently
requires `ε ≤ e^{−4k}/(4k)`, which would *conflict* with the tail; re-running (4.20) removes it).
Net `C(k) = exp(O(k log k))`, comfortably `o(4^k)` in the log.  Status: a theorem-shaped target
whose proof is "KMT §4 with the `k`-dependence made explicit + the block construction"; no new
idea needed, real bookkeeping.  Lean cost dominated by the fundamental lemma of sieve theory
(not in Mathlib).
