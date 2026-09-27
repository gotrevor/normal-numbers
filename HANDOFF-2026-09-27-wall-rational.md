# Handoff: Wall 1949 (rational affine maps preserve normality) — reduction complete

**Branch**: `wip/wall-rational` · **Scope**: `sorry-free:src/NormalNumbers/WallRational.lean`

## Status

`NormalNumbers.isNormal_rat_mul_add` (ratified statement, unchanged) is **proved modulo
one crux**.  The whole reduction chain is machine-checked; `lake build` green.

**Exactly one `sorry` remains in the file**: `WallRational.tendsto_jointDensity`.

    for j < B, v < b^l:  #{n < N : divState b B x M n = j ∧ blockVal b x n l = v}/N
        → (1/B)·b^{-l}

i.e. the long-division state is asymptotically uniform on `ℤ/B` and asymptotically
independent of the digits of `x` from position `n` on.  Everything else — including the
headline `isNormal_rat_mul_add` and the full reduction to this one statement — is
machine-checked.

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

## Also proved (the crux's scaffolding, all sorry-free)

* `divState b B x M n = (b^n M + ⌊b^n x⌋) mod B`, `divState_lt`, `divState_modEq`
* `floor_orbit_mul_pow : ⌊b^l·(b^n x mod 1)⌋ = blockVal b x n l`
* `divState_shift : r(n+j) ≡ b^j r(n) + blockVal b x n j (mod B)` — the identity the
  attack runs on; restricting `j` to multiples of `T = ord_B(b)` makes `b^j ≡ 1`
* `orbit_add_div : orbit b ((x+M)/B) n = (r n + orbit b x n)/B`
* `tendsto_blockAverage` — the fixed-depth block-average engine the Cauchy–Schwarz step
  consumes
* the grid assembly `tendsto_jointDensity ⟹ isNormal_add_int_div_coprime`: the depth-`k`
  b-adic cell of the target is exactly `{n : b^k·r n + blockVal b x n k ∈ [mB, (m+1)B)}`,
  so the cell is a disjoint union of exactly `B` joint (state, block) classes, each of
  density `1/(B b^k)` — total `b^{-k}`, fed to `equidistributed_of_badic`.

## Next actions

1. Close `tendsto_jointDensity`.  Sub-leaves to name, in order:
   (a) `T` with `b^T ≡ 1 (mod B)` (`ZMod.pow_totient` / `orderOf`), and the collapsed
       shift identity `r (n + T*k) ≡ r n + blockVal b x n (T*k)`;
   (b) finite-Fourier reduction: the joint density statement ⟺ for every nontrivial
       additive character `χ` of `ℤ/B` and every block `w`,
       `(1/N) ∑_n χ(r n)·1[block at n = w] → 0`;
   (c) shift-average: `|A| ≤ lim (1/N) ∑_n |(1/K) ∑_{k≤K} χ(W(Tk) n)·1[…]|`, with the
       `χ(r n)` factor pulled out because it is `k`-free;
   (d) Cauchy–Schwarz + `tendsto_blockAverage` to turn the square into fixed-depth block
       correlations, and the geometric character-sum bound: a free digit range of length
       `g` contributes `∏ (1/b)|∑_{e<b} e(s·e·b^j/B)|`, every factor `< 1` strictly
       because `gcd(B,b)=1` forces `e(s b^j/B) ≠ 1` for `s ≢ 0`.
   Note (c)/(d) must be phrased with `limsup`/ε, not `lim`: convergence of the Cesàro
   means of `χ(r n)` is not known a priori.
2. When it closes, repoint the `Maze.lean` row "Mahler block-occurrence analogue"
   (cites Wall 1949) from `.cited` to the theorem.
