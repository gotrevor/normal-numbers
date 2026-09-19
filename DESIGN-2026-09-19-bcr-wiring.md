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
| W3 | **Weyl criterion**: `∀ h ≠ 0, (1/n)∑_{k<n} phase(h·u k) → 0` ⟹ every b-adic cell frequency → its length | 🔨 not in repo or mathlib.  Route: squeeze `1_{[a,c)}` between continuous functions, approximate those by trigonometric polynomials via `span_fourier_closure_eq_top` (`Mathlib/Analysis/Fourier/AddCircle.lean:245`), finish with `ε/3`.  Bounded, one lap. |
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

and `(log P)^{Re z − 1} → 0` is immediate for `Re z < 1`.  Provability (KB verdict §2e): on `P ≥ N^{1/2}` an exact one-large-prime identity reduces `siteMean` to full-ω Selberg–Delange means at scales `N/p`, and for `Re z ≤ 0` the prime sum converges by the oscillation of `(1−t)^{z}`; down to `N^δ` the Buchstab expansion has depth `⌊1/δ⌋`.  Classical, multi-week to formalize (no Selberg–Delange in mathlib), but not a conjecture.  The measured phase of `siteMean / CRT prefix` rotates two thirds of a turn across the middle range at every N, so no *complex* proportionality to the CRT prefix should be stated.

Measured shape of `BCR` itself (KB verdict §2e): the ratio `windowMean / ∏ siteMean` is a slowly varying **real positive** factor, phase within ±0.015 turns (h = 1) and ±0.042 (h = 3) over the whole middle range at N = 10^8, magnitudes 1.1–1.4 and 0.3–0.65.  A future sharpening of the node is `∃ c_h > 0, windowMean / ∏ siteMean → c_h`; not frozen yet, the magnitude bound is what the wiring uses.

## 4. What not to do

- Do not formalize the ledger, the covariance notation, (BL), or the band-freezing lemmas; they are restatements (KB verdict §1).
- Do not launch a treadmill from this document; Trevor fires it.  When he does: Opus/low, `--allow-from-agent`, branch off `wip/g5-prime-subset`, first lap = W3 only.
- Do not report `sorry` counts; report which row of §2 is green.
