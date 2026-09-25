# HANDOFF c3-mrt lap 1 — the crux is an Elliott correlation with `log log N` points

Worktree `~/src/nn-c3mrt`, branch `wip/c3-mrt`.  Kickoff `KICKOFF-2026-09-24-c3-mrt.md`
(ratified 2026-09-24, newer than `DIRECTION.md`'s 2026-09-23 Theorem-C′ directive; the
C3/MRT moonshot is this run's assigned scope).

## The crux

`weylLambertTwist_holds` in `src/NormalNumbers/SwingC3Leaf.lean` (unchanged, still the one
named `sorry` carrying `ConjC3`).

## This lap's advance

**The route-decisive discovery: truncate VERTICALLY, not horizontally.**

Every prior lap truncated `tailLarge P b n = ∑_{i≥0} ω_{>P}(n+i+1)/b^{i+1}` at a *prime*
cutoff `K` (`tailTrunc`), buying `∏_{P<p≤K} p`-periodicity but paying discarded mass
`≍ N ∑_{K<p} 1/p` — the impossible window `log N ≪ K ≪ N` that `SwingC3Leaf`'s docstring
records as missing.  Truncating instead at *digit depth* `D` costs, **pointwise**,

    tailLarge P b n − tailDepth P b D n ≤ (log₂(n+1) + D + 1) / ((b−2) b^D)
    (`C3MrtShape.tailLarge_sub_tailDepth_le`, `…_le_of_lt` uniform on n < N)

only *logarithmic* in `n`.  So depth `D ≍ log_b log N` is already free, and the required
correlation length collapses from `N` to `log log N`.

### New, all axiom-clean, no `sorry` in either new module

`src/NormalNumbers/C3MrtShape.lean`
* `tailLarge_sub_tailDepth_le` / `_le_of_lt` / `_nonneg` — the vertical price.
* `ee_tailDepth_eq_prod` — the depth-`D` phase is **exactly**
  `∏_{i<D} ζ_i^{ω_{>P}(n+i+1)}`, `ζ_i = e(h/b^{i+1})`: the machine-checked identification of
  the C3 crux as an Elliott-type correlation of the multiplicative functions `ζ_i^{ω_{>P}}`.
* `depthSchedule b N = 2(⌊log_b(log₂N+1)⌋+1)`, `sq_log_le_pow_depthSchedule`,
  `depthSchedule_err_le` (error `≤ 3/(log₂N+1)` along the schedule).
* `DepthElliott b` — the named reduction target.
* **`weylLambertTwist_of_depthElliott : DepthElliott b → WeylLambertTwist b`**, axioms
  `[propext, Classical.choice, Quot.sound]`.

`src/NormalNumbers/C3MrtRungOne.lean`
* **`depthAvg_one_tendsto`** — rung `D = 1` of `DepthElliott` is **PROVED**, in natural
  density, no MRT, no log averaging: it is exactly the repo's own Leaf-B Delange slot
  `DelangeSlot.twisted_omegaLarge_mean_tendsto_zero` (itself axiom-clean).  Wiring lemmas
  `omegaLarge_eq_delange`, `norm_depthRoot`, `sum_range_shift_eq_sum_Icc`.

## Kickoff items, answered

1. **Correlation shape — decided.**  `K`-point, with `K = D_N = O(log log N)` consecutive
   shifts `n+1,…,n+D`.  **The twist `e(jn/Q)` supplies no cancellation**: the hypothesis
   `0 < j < Q` is not load-bearing, and no CRT/periodicity argument in `Q` can close the leaf.
   Cancellation is entirely non-pretentiousness of `ζ_0^{ω_{>P}}` (`∑_p (1−Re ζ_0)/p = ∞`),
   predicting decay `(log N)^{−a}` with
       `a(b,h) = ∑_{i≥1} (1 − cos(2π h / b^i)) < ∞`,
   finite because `1 − cos(2πh/b^i) ≍ b^{−2i}` — consistent with the probe's measured
   `a ≈ 1.3–3.7` and with `a ≈ 1.9` for `h = 1` at small `b`.
2. **`K = 1` in natural density — DONE**, and it did not even need Delange re-proved: it was
   already in the repo.
3. **What `K ≥ 2` needs — stated precisely.**  `DepthElliott` is *not* a fixed-`D` statement,
   and provably cannot be reduced to one: for fixed `D` the discarded phase
   `h ∑_{i≥D} ω_{>P}(n+i+1)/b^{i+1}` has typical size `≍ log log N / b^D → ∞`, and its
   *fluctuation* is `≍ √(log log N)/b^D → ∞` too, so the deep tail is neither negligible nor
   an asymptotically constant rotation.  Hence the requirement is **Elliott's conjecture
   uniform in the number of points `k`, with `k ≍ log log N`**.  Tao's
   `Erdos67b.unitCircleLogElliott` (`k = 2`, log density) and Tao–Teräväinen (odd `k`, log
   density) are fixed-`k`; that uniformity in `k` is the whole remaining obstruction.

## Confidence

* leaf TRUE: high (≈ 95%).  Two independent numerics agree on `(log N)^{−a}`, and the
  predicted `a(b,h) = ∑_{i≥1}(1−cos(2πh/b^i))` now has a mechanism, not just a fit.
* leaf PROVABLE with known techniques: low (≈ 15%).  Fixed-`k` Elliott is not enough (proved
  heuristically above, not yet in Lean); uniform-in-`k` Elliott is open.

## NEXT (attack order)

1. **Narrow the `k`-uniformity.**  Try to prove `DepthElliott` from fixed-`D` correlations
   **plus** a second-moment/variance estimate on the deep tail
   `θ_D(n) = h ∑_{i≥D} ω_{>P}(n+i+1)/b^{i+1}`.  The heuristic above says the fluctuation is
   `√(log log N) b^{-D}`; if a *Turán–Kubilius over the D-window* bound gives
   `‖θ_D − μ‖_{L²} ≪ √(log log N)/b^D`, then the honest conclusion is a *quantitative* trade:
   the fixed-`D` correlation must decay faster than `√(log log N)/b^D`.  Formalise that trade
   as a Prop — it may be reachable, since the `D = 1` rung has a *power of log* decay
   (Selberg–Delange), which beats `√(log log N)` comfortably.  **This is the crux now.**
2. Prove rung `D = 2` unconditionally if `lean-proofs-latest`'s `unitCircleLogElliott` can be
   instantiated at the two shifts `n+1, n+2` with `ζ_0^{ω_{>P}}, ζ_1^{ω_{>P}}` — log density
   only, so it gives the log-averaged variant of rung 2, not the natural-density one.
3. Extend the numerics: measure the fitted `a` against `∑_{i≥1}(1−cos(2πh/b^i))` directly
   (stdlib-only probe in `probes/`), which is a sharp falsifiable test of the mechanism.

---

# lap 2 addendum — the mean bound: required depth drops to `log log log N`

`src/NormalNumbers/C3MrtMean.lean` (axiom-clean, no `sorry`).

Lap 1 spent the **pointwise** truncation price `(log₂ n + D + 1)/((b−2)b^D)`, needing
`b^{D_N} ≳ log N`, i.e. `D_N ≍ log_b log N` points.  But only the *mean* discarded phase is
ever spent, and the mean of `ω` is `log log`, not `log`:

* `tailLarge_sub_tailDepth_le_omegaTail` : `tailLarge − tailDepth ≤ omegaTail b (n+D) / b^D`
  — the exact shape of the deep tail (pointwise, no crude `ω ≤ log₂` step).
* `sum_range_deep_le` : `∑_{n<N}(tailLarge − tailDepth) ≤ N·LL(N)/b^D` for `D + 3 ≤ N`, where
  `LLbound N = 4 log(log₂ N) + 11`.  Mertens input: the repo's own
  `PairDecouple.sum_omegaTail_AP_le'`.
* **`weylLambertTwist_of_schedule`** : for ANY depth schedule `Dsch` with
  `∀ᶠ N, Dsch N + 3 ≤ N`, `LL(N)/b^{Dsch N} → 0`, and the `Dsch N`-point twisted correlations
  `→ 0`, the crux `WeylLambertTwist b` follows.  Axioms
  `[propext, Classical.choice, Quot.sound]`.  Subsumes `weylLambertTwist_of_depthElliott`.

**Consequence.** `LL(N)/b^{D_N} → 0` needs only `b^{D_N} ≳ log log N`, so

> **`D_N ≍ log_b log log N` correlation points suffice.**

That is one whole `log` better than lap 1, and it materially changes the plausibility of the
route: the number of Elliott points needed is now *triple*-logarithmic, e.g. `D_N ≤ 4` for all
`N < 2^(2^81)` at `b = 3`.  A fixed-`k` Elliott with `k` in the single digits, plus an explicit
`log log N`-sized budget, is a far more realistic target than uniformity in `k`.

## NEXT (lap 3)

1. Instantiate `weylLambertTwist_of_schedule` with the explicit schedule
   `DschLL b N := Nat.clog b ((15*(Nat.log 2 (Nat.log 2 N) + 1))^2)`: needs
   (a) `LL N ≤ 15*(Nat.log 2 (Nat.log 2 N) + 1)` (use `PairDecouple.log_le_natLog_succ`),
   (b) `Nat.le_pow_clog` for `b^{DschLL} ≥ (…)^2`, (c) `∀ᶠ N, DschLL b N + 3 ≤ N`.
   Result: a named Prop `DepthElliottLLL b` with only `log log log N` points.
2. Then the real target: prove the `D`-point correlation `→ 0` for `D = 2` (and ideally uniformly
   for `D ≤ k` with the `κ^D` constant), from `lean-proofs-latest`'s `unitCircleLogElliott`
   (log density) or a Selberg–Delange product over the `D` shifts.

---

# lap 3 addendum — the explicit schedule, and the quantitative target

`src/NormalNumbers/C3MrtSchedule.lean` (axiom-clean, no `sorry`).

The repo already carried the right schedule, built for the Pair-B decoupling:
`PairDecouple.depthLL b N = ⌊log_b (u_N+1)²⌋ + 1`, `u_N = log₂ log₂ N`, with
`pow_depthLL_gt` (`b^{depthLL} > (u_N+1)²`) and `eventually_depthLL_add_le`.  Nothing new was
needed to build it.

* `llProxy N = u_N + 1`, `tendsto_llProxy`, `LLbound_le_llProxy` (`LL(N) ≤ 15 llProxy N`).
* `tendsto_LLbound_div_pow_depthLL` — the mean discarded phase `LL(N)/b^{depthLL b N} ≤
  15/llProxy N → 0`.
* **`weylLambertTwist_of_depthElliottLL`** — the crux follows from the twisted
  `depthLL b N`-point correlations vanishing.  `O(log log log N)` points.
* **`QuantDepthElliott`** and **`weylLambertTwist_of_quantDepthElliott`** — the quantitative
  target, axiom-clean:

      ∃ κ : ℕ, ∃ η : ℕ → ℝ,  0 ≤ η,
        ‖depthAvg b P Q j h D N‖ ≤ b^{κD} · η N   for ALL D, N,
        and  llProxy^m · η → 0  for every m.

  The constant is allowed to grow like **any fixed power of `b^D`**, because the schedule only
  needs `b^{D_N} ≳ log log N`.  And the `D = 1` rung already supplies `η(N) = (log N)^{-a}`
  (Selberg–Delange, `depthAvg_one_tendsto`), which beats every power of `llProxy`.

## State of the reduction chain (all axiom-clean, no `sorry` in the C3Mrt* modules)

    QuantDepthElliott b                       (the remaining obligation)
      → weylLambertTwist_of_quantDepthElliott
      → weylLambertTwist_of_depthElliottLL     (O(log log log N) points)
      → weylLambertTwist_of_schedule           (any schedule with LL(N)/b^{D_N} → 0)
      → WeylLambertTwist b
      → conjC3_of_weylLambertTwist → ConjC3

and `D = 1` of `QuantDepthElliott`'s correlation is PROVED (`depthAvg_one_tendsto`).

## NEXT (lap 4)

The only thing left is the multi-point bound itself.  Attack order:
1. **`D = 2` with an explicit power-of-log saving.**  `depthAvg b P Q j h 2 N` is
   `(1/N) ∑ e(jn/Q) ζ_0^{ω_{>P}(n+1)} ζ_1^{ω_{>P}(n+2)}`.  Route A: the repo's own
   `DelangeSlot` machinery generalised to a product over two shifts — the Dirichlet-character
   expansion of `e(jn/Q)` is unchanged; what is new is that the summand is a product of two
   *shifted* multiplicative functions, so `IsCharLike`-style orthogonality no longer applies
   directly and one needs either Tao's entropy-decrement (log density, so it gives the
   log-averaged variant) or a Kubilius/sieve model of the joint law of
   `(ω_{>P}(n+1), ω_{>P}(n+2))`.
2. Route B (worth a probe first): the **Kubilius model** may give `D` points at once, since the
   D-window law of `(ω_{>P}(n+1),…,ω_{>P}(n+D))` is what `SwingC3Split`'s
   `OmegaLargeDecouple` already names.  If the joint law factorises to within `o(1)` in total
   variation for `D = O(log log log N)`, then `depthAvg` factorises into `D` one-point Delange
   means, each `→ 0`, and the crux CLOSES.  **This is the highest-value lead**: the `D` shifts
   are `n+1,…,n+D` with `D` triple-logarithmic, an extremely short window, exactly the regime
   where sieve independence is strongest.

---

# lap 4 addendum — the crux is a LEGITIMATE Elliott instance (certified)

`src/NormalNumbers/C3MrtElliottForm.lean` (axiom-clean, no `sorry`).

For `QuantDepthElliott` to *be* an instance of Elliott's conjecture rather than a degenerate
statement, the `f_i = ζ_i^{ω_{>P}}` must satisfy Elliott's hypotheses.  Now machine-checked:

* `depthFun_mul_coprime` — each `f_i` is multiplicative on coprime arguments (via the repo's
  `DelangeSlot.omegaLarge_mul_of_coprime` and the lap-1 bridge `omegaLarge_eq_delange`).
* `norm_depthFun` — each `f_i` is unimodular.
* `ee_tailDepth_eq_prod_depthFun` — the depth-`D` phase in Elliott normal form.
* `re_depthRoot_lt_one`, `re_lt_one_of_norm_one`.
* **`tendsto_principalDist_atTop`** — the non-pretentiousness witness:
  `∑_{P<p≤x} (1 − Re ζ_0)/p → ∞`, from mathlib's `not_summable_one_div_on_primes`.  This is the
  divergence Halász/Elliott needs, and it is exactly why the `D = 1` rung holds.

## Two routes REFUTED this lap (recorded, do not retry)

1. **Smooth/rough split (the sieve/Kubilius route).**  Split `ω_{>P} = ω_{(P,y]} + ω_{>y}`.
   Sieve independence over the `D`-window needs `y^D ≤ N^{o(1)}`, which the triple-log `D`
   satisfies with enormous room — but the discarded rough factor costs
   `(1/N)∑_m |ζ^{ω_{>y}(m)} − 1| ≍ ∑_{y<p≤N} 1/p = log(log N / log y)`, and that is `o(1)` ONLY
   for `y = N^{1−o(1)}`, where sieve independence dies.  This is precisely the obstruction that
   makes Chowla hard; it is not circumvented by the short window.  (Compare the repo's
   `PROBE-2026-09-20-smooth-rough-decoupling.md`.)
2. **Self-similar recursion.**  `tailLarge` satisfies the exact recursion
   `T(n) = (ω_{>P}(n+1) + T(n+1))/b`, so `e(tT(n)) = e((t/b)ω_{>P}(n+1))·e((t/b)T(n+1))`.
   Iterating it *is* the depth truncation — it reproduces `ee_tailDepth_eq_prod` and nothing
   more; the residual parameter `h/b^D` shrinks but the residual phase `e((h/b^D)T(n+D))` still
   needs `b^D ≳ log log N`.  No new leverage, and the recursion is not a contraction on any
   sum-level quantity because the scale-`t/b` object reappears with an extra one-point weight at
   the SAME argument, i.e. it is its own shift.

## Also determined (correcting lap 1)

`Tao's Erdos67b.unitCircleLogElliott` in `lean-proofs-latest` is **not** instantiable here, for
two independent reasons: (a) it is the `f(n)·conj f(n+h)` form (one function, conjugated), while
our `D = 2` case has two *different* functions `ζ_0^{ω}, ζ_1^{ω}`; (b) it requires
`IsCompletelyMultiplicativeOnPositive`, and `ζ^{ω}` is multiplicative but NOT completely
multiplicative (`ω(p²) = 1`).  The general `NonasymptoticLogElliott` in the same file takes two
functions but carries the same complete-multiplicativity hypothesis.  So the MRT/log-Elliott
dependency does not reach this crux as it stands; a `ζ^{Ω}`-vs-`ζ^{ω}` bridge would be needed
and there is none (they differ on the non-squarefree numbers, density `1 − 6/π² ≈ 0.39`).

## NEXT (lap 5)

1. Finish the non-pretentiousness certificate: the `χ` nonprincipal `t = 0` case, from the
   repo's `WeakPNT_AP` (Dirichlet in APs).  This is bounded, concrete work and completes the
   "legitimate Elliott instance" claim for all `t = 0` twists.
2. State `QuantDepthElliott`'s `D = 2` case as its own named Prop and try the
   Selberg–Delange product route directly: `∑_n χ(n) ζ_0^{ω(n+1)} ζ_1^{ω(n+2)}` — the
   Dirichlet-series approach needs the *joint* generating function of `(ω(n+1), ω(n+2))`,
   which is a two-variable shifted-convolution problem.  Expect this to be the real wall.
3. If (2) walls, the honest end-state is the current chain plus the `D = 1` rung: `ConjC3` is
   reduced, axiom-clean, to a quantitative Elliott correlation with `O(log log log N)` points,
   a generous `b^{κD}` constant budget, certified-legitimate hypotheses, and the base rung
   proved.  That IS the "equivalence with a named open problem" success criterion.

---

# lap 5 addendum — the non-pretentiousness certificate, generalised; and the diagonal escape closed

`src/NormalNumbers/C3MrtElliottForm.lean` (axiom-clean, no `sorry`).

## Structural check: `P` is fixed before `N` — no diagonal escape

If `P` could grow with `N` the crux would collapse (`ω_{>P}(m) = 0` for `m ≤ N < P`, and the sum
is then `∑ e(jn/Q)/N → 0` by periodicity alone).  It cannot: `rotationRouteC_of_weyl`
(`SwingC3ContGlue.lean:276`) obtains `P` from `exists_rotationCover_core hb α len …`, i.e. `P`
is determined by the target word `(α, len)` and is then held fixed while `N → ∞`.  So the mean of
`ω_{>P}` over `n < N` really is `≍ log log N` and the depth truncation really is needed.  **This
escape route is now definitively closed** (do not re-examine).

## New, general

* `re_lt_one_of_norm_le_one` — generalises lap 4's unimodular version to `‖z‖ ≤ 1`.
* `tendsto_constDist_atTop` — `∑_{P<p<x} c/p → ∞` for every `c > 0` (lap 4's proof, extracted).
* `twistDist b h P κ x = ∑_{P<p<x} (1 − Re(ζ_0 κ(p)))/p` — the pretentious distance to a twist.
* **`tendsto_twistDist_atTop`** — the uniform-gap criterion: a fixed gap `c > 0` between
  `Re(ζ_0 κ(p))` and `1` along primes `> P` gives non-pretentiousness.
* **`tendsto_twistDist_atTop_of_finite_values`** — non-pretentiousness against EVERY
  finite-valued twist whose value set misses `ζ_0⁻¹`.  Covers every Dirichlet character `χ` with
  `ζ_0⁻¹ ∉ image χ`.
* **`tendsto_twistDist_principal`** — non-pretentiousness against the principal character mod
  **any** `q` (not just `q = 1`, which is all lap 4 gave).

## What the certificate still lacks, and why it is not cheap

Two twist families remain, both true and standard, neither reachable from mathlib as it stands:

1. `t = 0`, `χ` nonprincipal with `ζ_0⁻¹ ∈ image χ`.  Reduces (by grouping primes by the value
   `χ(p) ∈ μ_d` and using `∑_p 1/p = ∞`) to: **`∑_{p : χ(p)=1} 1/p = ∞`**, i.e. Dirichlet with
   `1/p` weights.  Mathlib's `PrimesInAP` only reaches the `Λ`-weighted
   `not_summable_residueClass_prime_div` (`∑ Λ(p)/p`), and `Λ(p)/p = log p · (1/p)` is the WRONG
   direction — divergence of the `Λ`-weighted sum does not give divergence of `∑1/p`.  Getting
   `∑1/p` needs `L(1,χ) ≠ 0` plus a Mertens-type partial summation: a multi-lap formalisation.
2. `t ≠ 0`: `∑_{p≤x} χ(p)p^{it}/p = log L(1+it,χ) + O(1)` is bounded, so
   `twistDist ≥ ∑1/p − O_t(1) → ∞`.  Needs `L(1+it,χ) ≠ 0` (mathlib has
   `LFunction_ne_zero_of_one_le_re`) plus the same Euler-product/Mertens bridge.

Both are "a constant cannot pretend to be `χ(p)p^{it}`" — the softest possible instance of
non-pretentiousness, with no conspiracy available.  That is exactly why the `D = 1` rung was
provable outright (`depthAvg_one_tendsto`, via the repo's `DelangeSlot`, which does its own
analytic work and does not go through the pretentious-distance formulation).

## NEXT (lap 6)

The wall is `D = 2`.  Every soft route is now refuted and recorded (smooth/rough sieve split;
self-similar recursion; growing `P`; Tao's `unitCircleLogElliott`, which needs complete
multiplicativity).  Remaining ideas, in order:
1. **Turán–Kubilius halving** (a real but modest gain): centring `ω_i` at its mean `μ` makes the
   residual tail phase have SD `≍ √(log log N)/b^D` rather than mean `≍ log log N/b^D`, so the
   required depth drops by a factor 2, to `D_N ≍ ½ log_b log log N`.  Does not remove the wall.
   Needs a variance bound for `ω` — check `PairDecouple`/entropy modules for one.
2. **`ω → Ω` bridge**: if `ζ^{Ω}` could replace `ζ^{ω}` the dependency's log-Elliott would
   apply (`ζ^Ω` IS completely multiplicative).  They differ on non-squarefree `n` (density
   `1 − 6/π² ≈ 0.39`), so no pointwise bridge — but the *correlation* difference may be
   controllable, since `ζ^{ω(n)} = ζ^{Ω(n)}` unless a prime square divides `n`, and the
   squarefull part is a convolution one can sum over. **This is the most promising untried
   lead**: `ζ^{ω} = ζ^{Ω} * g` for an explicit `g` supported on squarefull numbers, so a
   `D`-point correlation of `ζ^ω`'s expands as a finite-weight sum of `D`-point correlations of
   `ζ^Ω`'s along dilated shifts — and THOSE are in scope for `unitCircleLogElliott`/
   `NonasymptoticLogElliott` (log density).  Worth a careful attempt.
