# Handoff — swing at C1, lap 26: the orbit is almost periodic; `model × decoupling`

**Branch** `wip/swing-c1` · **HEAD** `fc1dd13` · tree clean, NOT pushed
**Build**: full `lake build` green, **9179 jobs**.
**New files** (all in `src/`, all additive — nothing existing was edited):
`SwingC1Periodic.lean` (sorry-free), `SwingC1CRT.lean` (sorry-free), `SwingC1Model.lean` (2 named
leaves).  `SwingC1.lean` is untouched: still exactly `hDepthAll` + `hAutoCorrAll` open, `conjC1`
still present and still a `sorry`, per the kickoff addendum.

## What changed: a NEW handle on the crux

### 1. The orbit of `G₄_b` is an explicit almost-periodic sequence  (`SwingC1Periodic.lean`)

```
omegaTail b N  =  Σ_{p prime}  b^{N mod p} / (b^p − 1)      omegaTail_eq_tsum_primePeriodic
fract(b^n·G₄_b) = fract( Σ_p b^{n mod p}/(b^p − 1) )        fract_orbit_eq_fract_tsum
orbitCorrSum b j L N = … the same sum …                     orbitCorrSum_eq_primePeriodic
```
Proof: exchange `ω(m) = Σ_p [p ∣ m]` with the `b`-adic weights and sum each prime's arithmetic
progression `{k : p ∣ N+k}` as a geometric series.  **The `p`-th summand depends on `n` only
through `n mod p`** — so the crux's object is Besicovitch almost periodic with the primes as
periods.  No `ω`, no carry, no real number left in the statement.

Exact quantitative companions (no error terms):
* `sum_primePeriodicTerm_period` / `sum_primePeriodicTerm_range_mul` — the mass of the `p`-th
  summand over `t` full periods is **exactly** `t/(b−1)`.  Summing over `p ≤ P` is Mertens.
* `truncTail_add_period` / `truncTail_add_mul_primorial` — the truncation to primes `≤ P` is
  exactly `Π_{p≤P} p`-periodic.

### 2. The crux decomposed: `model × decoupling`  (`SwingC1CRT.lean`, sorry-free)

For ANY `Q`-periodic `A` and any `B`, both of modulus `≤ 1` (PROVED,
`norm_fullMean_mul_le_periodMean_add_defect`, pure finite algebra):

```
‖mean_{m<QR} A(m)B(m)‖ ≤ ‖periodMean A Q‖ + mean_c ‖progMean B Q R c − fullMean B (QR)‖
```

Instantiated at `A(n) = e(h·θ^{(P)}_n)` (small primes, exactly `Q = Π_{p≤P}p`-periodic) and
`B(n) = e(h·ρ^{(P)}_n)` (large primes), the Weyl sum of the orbit splits into

* **(M) the model term** `periodMean A Q` — elementary, Mertens-driven, PROVABLE; and
* **(D) the decoupling defect** — the large primes do not see the small-prime residues.

Why this is a genuine narrowing over the previous localisation: `corrSum_eq_elliott` put the
*whole* difficulty in the natural-density Elliott correlations of `f_j(m) = ζ^{jω(m)}` — an open
conjecture with no accessible sub-case.  Here (M) supplies **all** the randomness and is a
theorem; (D) is a progression-equidistribution statement for a slowly growing modulus, the shape
Siegel–Walfisz / Bombieri–Vinogradov arguments address.  Quantitatively (M) alone gives
`(log log N)^{−c_h}` decay (take `P ≍ ε log N`, so `Q ≤ N^ε` and `log P ≍ log log N`), which is
enough — and matches Delange's `(log N)^{−δ}` mechanism.

### 3. Leaf (M), CRT half PROVED  (`SwingC1CRT.lean` + `SwingC1Model.lean`)

```
sum_range_mul_mod_mul   Σ_{c<qQ} g(c mod q)·h(c mod Q) = (Σ_{a<q} g a)(Σ_{b<Q} h b)   (coprime)
sum_range_prod_mod      the same over a pairwise-coprime finset of moduli
periodMean_phase_truncTail :
     periodMean (n ↦ e(h·truncTail b P n)) (primorialLe P) = Π_{p ≤ P} localFactor b h p
```
with `localFactor b h p = (1/p) Σ_{s<p} e(h·b^s/(b^p−1))`.  All sorry-free, trust triple.
That IS the statement that over one full period the residues `(n mod p)_{p≤P}` are jointly
uniform.

## Exactly two named leaves are open in the new work (both believed elementary)

Both in `src/NormalNumbers/SwingC1Model.lean`:

1. **`norm_localFactor_le`** — `∃ c > 0, ∀ᶠ p, p.Prime → ‖localFactor b h p‖ ≤ 1 − c/p`.
   Mechanism, fully worked out: for `s = p−1−i` the summand is `e(h·b^{−1−i}/(1−b^{−p}))`, which
   for large `p` is near the FIXED root `e(h/b^{1+i})`; pick `i` minimal with `|h|/b^{1+i} < 1/2`
   (so also `≥ 1/(2b)`, hence bounded away from `ℤ` uniformly in `p`).  The `s = 0` summand is
   `e(h/(b^p−1)) → 1`.  So two of the `p` unit vectors differ by a fixed `δ > 0`, and
   `‖z₁+z₂‖ = √(4−‖z₁−z₂‖²) ≤ 2 − δ²/4`, giving `‖(1/p)Σ_s z_s‖ ≤ 1 − δ²/(4p)`.
   The only analytic input is a lower bound on `‖e(x) − 1‖ = 2|sin πx|` for `x` in a fixed compact
   subinterval of `(0,1)` — handle with `Real.cos_lt_one` / `Complex.norm_exp_ofReal_mul_I_sub_one`
   style lemmas, or via `Real.cos_eq_one_iff` + continuity on the compact `[1/(2b), 4/7]`.
2. **`prod_localFactor_tendsto_zero`** — `‖Π_{p≤P} localFactor b h p‖ → 0`.
   Bound the finitely many small `p` factors by `1` (`norm_localFactor_le_one`, already proved),
   and `Π_{p₀<p≤P}(1 − c/p) ≤ exp(−c Σ_{p₀<p≤P} 1/p) → 0`.  **Check mathlib for `Σ_p 1/p = ∞`**
   (`Nat.Primes.not_summable_one_div…` / `Theorems100`) and for the repo's own Mertens layer
   (`primeRecipSum_le`, `recipSumLe_le_crude` in the Pair-A files — read-only, do not edit).

`periodMean_tendsto_zero` already assembles those two.

## Exact next moves, in order

1. **Close `norm_localFactor_le`.**  Smallest self-contained probe first: the two-vector lemma
   `‖z₁‖=‖z₂‖=1 → ‖z₁−z₂‖ ≥ δ → ‖z₁+z₂‖ ≤ 2 − δ²/4` (pure algebra, `Complex.norm_sq`), then the
   root-of-unity separation.
2. **Close `prod_localFactor_tendsto_zero`** (needs only Mertens divergence + `1−x ≤ exp(−x)`).
   When both land, **leaf (M) is DONE and the route has its first unconditional randomness
   input** — that is the milestone to aim at.
3. **Only then state (D)** as a named Prop in `src/` and prove the assembly
   `(M) ∧ (D) → Weyl sums → 0`.  The assembly is already half-built: it needs `A·B = e(h·θ)`
   (`phase_add` + the split of `θ` into `truncTail` and the `p>P` remainder) and the choice
   `R = ⌊N/Q⌋` with an `O(Q/N)` edge correction.
4. Weyl → `ConjC1`: do NOT reprove it.  `conjC1_conjC3_of_normal` (CastingOut.lean) and the
   base-4 bridge `isNormal_G4_of_windowDecay` / `isNormal_G4_of_prefixDecay` (G4WiringCRT,
   G4WindowK) already exist.  Note `PrefixDecay` is the repo's own open normality crux and is
   literally `e(h·truncTail J m)` at depth `J ≤ log₂log₂log₂ M` — the SAME shape as this split,
   so the `model × decoupling` bound applies there verbatim and would attack the repo headline too.
   (Use those files read-only; the kickoff scopes edits to `SwingC1*.lean`.)

## Standing constraints (unchanged)

* `CastingOut.lean`, `CastingOutCount.lean`, `CastingOutLambert.lean`, `Maze.lean`, `papers/`,
  `agent-mail/`, other KICKOFFs: **do not edit**.
* `conjC1`, `hAutoCorrAll`, `hDepthAll` stay in `SwingC1.lean` as `sorry`s until proved — deleting
  or restating them is a failure, not completion (kickoff addendum).
* The lap-25 record stands and is NOT superseded: the six equivalent forms, the Elliott
  localisation (`corrSum_eq_elliott`), the four refuted sub-approaches, and the `b=3` numerics
  false-alarm guard are all still true.  `model × decoupling` is a *different axis* on the same
  object (primes rather than shifts), not a replacement.
