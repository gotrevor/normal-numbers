# Handoff: Wall 1949 (rational affine maps preserve normality) — reduction complete

**Branch**: `wip/wall-rational` · **Scope**: `sorry-free:src/NormalNumbers/WallRational.lean`

## Status

`NormalNumbers.isNormal_rat_mul_add` (ratified statement, unchanged) is **proved modulo
one crux**.  The whole reduction chain is machine-checked; `lake build` green.

Remaining `sorry`s in the file — exactly two, both on the crux path:

1. `WallRational.isNormal_add_int_div_coprime` — **the crux**.
   `IsNormal b x → gcd(B,b) = 1 → IsNormal b ((x + M)/B)`.
2. `WallRational.tendsto_blockAverage` — the engine the crux needs: for normal `x`,
   `(1/N) ∑_{n<N} F (blockVal b x n l) → b^{-l} ∑_{v<b^l} F v`.  This is
   `IsNormalSequence` + linearity over the `b^l` blocks (no new mathematics), so it is
   the right thing to close first.

## Proved this lap (all in `WallRational`)

* `fract_intMul_fract`, `fract_neg_fract`, `orbit_add_intCast`, `orbit_intMul`
* `equidistributed_natMul` — dilation by a positive integer: the preimage of `[a,c)`
  under `t ↦ {m t}` is the disjoint union of `[(j+a)/m, (j+c)/m)`, `j < m`
* `density_level_zero` — level sets of an equidistributed sequence have density 0
* `equidistributed_negFract` — reflection `t ↦ {-t}`, via three density-zero level sets
  (`0`, `1-c`, `1-a`) and a two-sided card squeeze
* `equidistributed_of_shift` — dropping `κ` initial terms (`Finset.sum_range_add`)
* `isNormal_add_intCast`, `isNormal_intMul`, `isNormal_div_pow`
* `exists_smooth_coprime_split` — `V = A*B`, `A ∣ b^κ`, `gcd(B,b)=1`, by strong
  induction stripping `gcd(V,b)`
* `isNormal_rat_mul_add` itself: `q*x+r = ((cc*q.num*r.den)*x + cc*q.den*r.num)/B / b^κ`
  where `b^κ = A*cc` and `q.den*r.den = A*B`.

## The crux, and the attack

`orbit b ((x+M)/B) n = (r n + orbit b x n)/B` with `r n = (⌊b^n x⌋ + b^n M) mod B` the
long-division state.  So the crux is the **joint** equidistribution of `r n` with the
future digits of `x`.  `r n` depends on the unbounded digit prefix, so no fixed-depth
block count reaches it directly.

Dead end, recorded: **Weyl does not linearise this.**  The Fourier test at frequency `h`
for `(x+M)/B` is the test at the *rational* frequency `h/B` for `x`, i.e. the same
problem.  Weyl only hands over integer dilations for free (and those are already proved
by the elementary interval decomposition, no Weyl needed).

Attack to run next (worked out on paper this lap, no obstruction found):
`gcd(B,b)=1` gives `T` with `b^T ≡ 1 (mod B)`, hence `r (n + Tk) ≡ r n + W (Tk) n`,
`W l n` = value of the digit block `x[n, n+l)`.  For a nontrivial additive character
`χ` mod `B` and a test function `f`, shift invariance of the Cesàro mean in `n` gives

    A = lim (1/N) ∑_n χ(r n) · (1/K) ∑_{k≤K} χ(W (Tk) n) · f (orbit b x (n+Tk)),

so `χ(r n)` (the unbounded-prefix factor) is *k-free* and Cauchy–Schwarz bounds `|A|²`
by the off-diagonal correlations
`(1/N) ∑_n χ(W (Tk) n) conj(χ(W (Tk') n)) · (f-factors)`.  Approximating `f` by a
depth-`d` b-adic step function makes each of those a fixed-depth block average, i.e. a
`tendsto_blockAverage` instance; its value is a character sum over the free digit range
between the two windows, hence `O(B·b^{-(T(k'-k)-d)})`.  Choosing `K₀ ≪ K` kills the
near-diagonal.

## Next actions

1. Close `tendsto_blockAverage` (linearity over `padWord`-indexed blocks; the pieces are
   `blockNatVal_padWord`, `length_padWord`, `card_filter_matchesAt_le`, and the existing
   `IsNormalSequence` frequency limits).
2. Then build the crux in named sub-leaves: (a) `r n` recursion and the `b^T ≡ 1` shift
   identity; (b) finite-Fourier reduction on `ℤ/B`; (c) the Cauchy–Schwarz step;
   (d) geometric character-sum bound on a free digit range.
3. When the crux closes, repoint the `Maze.lean` row "Mahler block-occurrence analogue"
   (cites Wall 1949) from `.cited` to the theorem.
