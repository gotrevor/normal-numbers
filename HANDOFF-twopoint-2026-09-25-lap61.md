# HANDOFF twopoint — lap 61, 2026-09-25: **DEEP REFLECTION — the two 🔴 leaves are 🟠 outside a small set of scales**

Branch `wip/twopoint-avg`, HEAD **`29a4d7d`**.  Working tree **clean**.  Two green commits this
lap, the Lean one gated by the pre-commit `lake build` (**9299 jobs**).  Every new declaration
`#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).  **No `sorry` introduced.**

> ⚠️ `DIRECTION.md`'s CURRENT DIRECTIVE was REWRITTEN this lap and **OUTRANKS this handoff**.
> Read it first.  The lap-60 handoff's "next session" items 2 and 3 are **superseded**; item 3
> ("leaf B is a cheaper alternative route") is **withdrawn as wrong**.

## The finding that reorganised the lap

Re-grounding the route against the *sources* rather than the handoffs turned up
`papers/tao-teravainen-2025-quantitative-correlations.txt` (arXiv 2512.01739v2, 265 KB) **on disk
and unread**, while `papers/literature-review.md` asserted it was not on disk.  What it contains:

* **Theorem 1.3**: `∑_n ω(n)/2ⁿ = ∑_p 1/(2^p−1)` is irrational, unconditionally, and the method is
  stated to extend to every base `b ≥ 2` (`b > 2` *easier*).  That series is this repo's `G4_b`.
* **Theorem 3.1** (on Pilatte 2025's decoupling inequality) — the reusable tool.  For 1-bounded
  multiplicative `g₁,g₂` with `g₁` non-pretentious, and `1 ≤ L ≤ log X`, there is `E ⊂ [√X,X]` of
  **logarithmic density `≪ L^{−c}`** with

      (W/N) ∑_{N<n≤2N} (g₁(n+h₁) − δ_N)·g₂(n+h₂)·1_{n ≡ b (W)}  ≪  L^{−c}   for all N ∉ E,

  all `W ∈ [L^c]`, all `b, h₁ ≠ h₂ = O(L^c)`.
* **Remark 3.2 bullet 3**, spelled out: `(1/N)∑ λ(a₁n+b₁)λ(a₂n+b₂) ≪ (log N)^{−c}` for
  `a_i,b_i ≤ (log N)^c`, `a₁b₂ ≠ a₂b₁`, *"follows from Theorem 3.1(ii)"* — hence for any
  non-pretentious 1-bounded multiplicative function, not just `λ`.
* **§5.2** "taking an alternating sum to cancel terms" (*"inspired by the theory of the Gowers
  uniformity norms"*): pick `p_ε = p₀+ε₁v₁+⋯+ε_Kv_K` all prime, alternate over `ε ∈ {0,1}^K`, and
  the first `K` terms of `∑_h ω(n+h)b^{−h}` cancel **identically**.  The literature's way to reduce
  a **growing-depth** combination to **pairwise** correlations.  The repo has no analogue.

**Both open leaves of this worktree are verbatim instances of Theorem 3.1:**

| leaf | instance |
|---|---|
| C1 `PairDecorr` — `(1/N)∑ z^{ω(pn+1)}\bar z^{ω(qn+1)} → 0` | Rmk 3.2 bullet 3 with `(a₁,b₁,a₂,b₂) = (p,1,q,1)`, `a₁b₂ = p ≠ q = a₂b₁`, `p,q ≤ w ≤ (log N)^c` |
| C3 depth-2 rung — `(1/N)∑ e(jn/Q) z₁^{ω_{>P}(n+1)} z₂^{ω_{>P}(n+2)} → 0` | (3.4) with `h₁=1, h₂=2, W=Q` |

`z^ω`, `z^{ω_{>P}}` are 1-bounded multiplicative and non-pretentious for `‖z‖=1, z≠1`
(`exp M ≈ (log X)^{1−Re z} ≫ L`).  **So "natural-density two-point Elliott for `ζ^ω` is open" is
HALF-STALE: only "for every `N`" is open.**  Ledger colour: `🔴 at every scale; 🟠 outside E`.

## The decisive asymmetry (this is why C3 goes first)

`IsRich` (`CastingOut.lean:405`) is `∀ w, ∃ c>0, ∀ᶠ N, c·N ≤ #{n<N : OccursAt …}` — a **lower**
bound on a **monotone** count, so it absorbs bad scales (`C(M) ≥ C(N) ≥ cN ≥ cM/2` for a good
`N ∈ [M/2,M]`).  `ConjC1`'s `CastLaw` is a two-sided density **limit** with no monotonicity and
does **not** absorb `E`.

Honest accounting: `E` can contain a run of up to `≍ L^{−c} log X` consecutive dyadic blocks, so
one good scale per block is not guaranteed and the fallback costs `X^{o(1)}`.  That yields not
`IsRich` but **`IsRichSubpoly`** — every word occurs at `≥ N^{1−o(1)}` positions below `N` — a rung
**strictly between** the PROVED `isDisjunctive_base` and `ConjC3`, which the repo has never named.

## Landed this lap

**`d770e07` — the synthesis.**  `DIRECTION.md` CURRENT DIRECTIVE rewritten (rungs 0–3 below);
`PENDING_WORK.md` gains the full dated reflection at the top; `STATUS.md` header, "Where it
stands", one dated bullet, the axiom ledger (re-run from real `#print axioms`, 16 declarations) and
"Outstanding" all refreshed; `papers/literature-review.md` gains a casting-out chapter and the
stale "not on disk" claim is corrected in place.  New probe `probes/c3_euler_product.py` +
`probes/data-2026-09-25-c3-euler-product.txt`.

**`29a4d7d` — RUNG 1, a real theorem.**  `src/NormalNumbers/TwoPointC3Depth.lean` (new, imported
from `src/NormalNumbers.lean`):

    addCharTail_depthOne :  (1/N) ∑_{n<N} e(jn/Q)·e(h·ω_{>P}(n+1)/b)  →  0

unconditionally, for every `b ≥ 1`, `P`, `Q > 0`, **every** `j` (the depth-1 rung does NOT need
`j ≢ 0 (mod Q)`; the cancellation comes from `z ≠ 1` alone) and every `h` with `b ∤ h`.  It is the
depth-1 truncation of `CastingOut.AddCharTail`, i.e. of the C3 crux, and its proof is a re-index
`m = n+1` of `DelangeSlot.twisted_omegaLarge_mean_tendsto_zero` — proved in an earlier campaign,
trust-triple, and **never consumed outside its own namespace** until now.  Supporting bridges, all
new and clean: `omegaLarge_eq_delangeSlot` (the join between `SwingC3Split`'s `omegaLarge` and
`DelangeSlot`'s — without it the C3 vocabulary cannot reach the Delange campaign at all),
`ee_nat_mul`, `ee_depthOne_eq_pow`, `ee_div_eq_one_iff` (so the `b ∤ h` hypothesis is sharp).

## Other corrections issued this lap

* **Lap 60's item 3 is WRONG.**  `SwingC3Rotation.tailLargeDecouple_holds` is not a cheaper
  alternative route: `tailLargeDecoupleC_of_weyl` (in-tree, trust-triple) already derives leaf B′
  from the Weyl hypothesis, and the converse is Fourier inversion on `ℤ/Q` plus Weyl's criterion.
  **Leaf B IS the crux.**
* **C2's `PrimeDensityAP` is too weak to be useful as stated.**  `Y / M` is ℕ-division, so whenever
  `M > N+1` the choice `Y = N+1` satisfies every clause with an **empty** prime set, while its
  consumer `TauMomentPrimesShiftStruct` needs `0 < P.card`.  So
  `tauMomentPrimesShiftStruct_of_primeDensity` is not a real reduction.  (At large `B` the
  statement is also *provable* here — Siegel–Walfisz range, `PNTPort` in-tree — so it is not 🔴
  either.)  Flagged, not fixed; C2's headline runs through `shiftedDivisorIncidence_holds`.
* **Against myself:** the "Euler product" analysis I re-derived this lap
  (`tailLarge P b n = ∑_{p>P} b^{−r_p(n)}/(1−b^{−p})`, rate exponent
  `A = ∑_i(1−cos 2πh b^{−i})`) was **already in `SwingC3Signed.lean`'s docstring** from lap 11/16,
  with `primeFactor`, `ee_tailTrunc_eq_prod`, `sum_range_ee_tailTrunc_eq` and
  `norm_primeFactor_sq_le` all proved.  My probe confirms it at 10× larger `N` with a FLAT
  Euler-product ratio (7.71 / 3.85 / 2.55 / 8.75; exponent matching to four digits) — real
  confirmation, not a new idea.  **Third inventory miss in two laps**, hence the new standing rule.

## NEXT SESSION — obey `DIRECTION.md`, in this order

0. **Rung 0 — the re-plumb (the 🔴→🟠 move; do this first).**  Name `WeylTailAlmostAll` (the
   quantitative, outside-`E` form TT2025 Thm 3.1 actually supplies).  Prove the **absorption
   lemma**: a monotone count plus one good scale per dyadic block gives positive lower density;
   a run of `R` bad blocks degrades it to `N/2^R`.  Then state and derive **`IsRichSubpoly`**.
1. **Rung 1 — DONE this lap** (`addCharTail_depthOne`).
2. **Rung 2 — machine-check the wall.**  `(1/N)∑_{n<N} tailLarge P b n → ∞` (rate
   `(log log N)/(b−1)`; crude `≥ c·log₂N` suffices).  This is exactly what refutes EVERY
   fixed-depth truncation, turning "the peel must grow" into a kernel fact.
   *Asset to reuse:* the C1 campaign's `TwoPointMertensLower.mertens_lower` (proved laps 43–52) —
   nothing in C3 consumes it.
3. **Rung 3 — the pin.**  `WeylTailHypothesis b ⟺ ShiftElliott` (growing depth
   `K ≈ log_b log log N`), C3's analogue of `multiElliottWeighted_iff_growing`; then read TT2025
   §5.2's alternating-sum/Gowers trick.
4. **Adjacent, unconditional, and explicitly named as "the next lap" by `SwingC3Signed.lean`'s own
   docstring — and never done:** `∏_{P<p≤K} ‖primeFactor b p h‖ → 0` as `K → ∞`.  Route checked
   this lap and it is short: a ONE-TERM lower bound `Sig_p ≥ ‖1 − e(h·b^{p−1}/(b^p−1))‖² → ‖1−e(h/b)‖² > 0`
   feeds `norm_primeFactor_sq_le` (already proved) to give `‖primeFactor‖ ≤ 1 − σ/(4p)` for large
   `p`, and then `mertens_lower` closes it.  Cross-campaign wiring, exactly the systemic gap.

**Do NOT**: book either leaf as flat 🔴; attempt the crux at a FIXED peel depth; treat
`tailLargeDecouple_holds` as a cheaper route; retry the `L¹` prime-size truncation family (refuted
in-tree); re-open the C1 arithmetic leaf; touch the designated-open `PrimeLambertOscillation` /
`MahlerDriftOne`; edit `twoPointWeightedAvg_all` or any frozen file.
**Standing first move every lap: grep `src/` for the statement AND `papers/` for the theorem.**

## Confidence at wrap
- `DelangeMean t` for all `t ∉ ℤ`: **DONE** (lap 60, two independent kernel proofs).
- `ConjC1` free of all cited-but-unproved theorems: **DONE**.
- `twoPointWeightedAvg_all` TRUE: **90%**; provable with known techniques: **3%** (untouched, as
  ratified).
- `WeylTailHypothesis` (C3 crux) TRUE: **97%** (Selberg–Delange mechanism confirmed numerically to
  four digits).  Provable at EVERY scale with known techniques: **8%**.  Provable **outside a
  log-density-small set of scales** with known techniques (TT2025 Thm 3.1): **70%** — this is the
  number that moved, and it is why rung 0 exists.
- `IsRichSubpoly` reachable: **55%** (new statement; the absorption lemma is elementary, the input
  is a 2026 theorem that would be cited, not formalised).
