# C4 — the rectangle design: a block law with a PRESCRIBED FINITE defect set

Found 2026-09-25 (lap 10).  Verified numerically in exact rationals by
`probes/c4_rectangle_design.py`; the Lean engine is `src/NormalNumbers/AbelianWindowGf.lean`.

## The coordinates

Run the block-i.i.d. process of `AbelianWindowBlocks.blockSeq`: i.i.d. blocks of length `q` with
law `ν` on `{0,1}^q`, uniform offset.  Write `ν` in Fourier coordinates,
`ν̂(U) = E[(-1)^{Σ_{i∈U} x_i}]`, and for `I ⊆ [0,q)` set `W_I(x) = Σ_{U⊆I} ν̂(U) x^{|U|}`.

*   `W_I ≡ 1` ⟺ the one-count of `ν` restricted to `I` is exactly Binomial(`|I|`,1/2).
    (Because `E[y^{ones(I)}] = ((1+y)/2)^{|I|} · W_I((1-y)/(1+y))`.)
*   The window defect polynomial is `Φ_L(x) = (1/q) Σ_{r<q} Π_b W_{I_b^{(r)}}(x)`, where the
    `I_b^{(r)}` are the traces the length-`L` window at offset `r` makes on the blocks, and
    `IsAbelianAt L ⟺ Φ_L = 1`.

Every trace is a prefix, a suffix, a full block, or — ONLY when `L < q` — a strictly interior
interval.  Hence:

> **If `W_I ≡ 1` for every prefix and every suffix `I`, the ONLY possible defects are at `L < q`,
> and come from interior intervals.**

This is `isAbelianAt_blockSeq_of_binomSeg` (Lean, proved, axiom-clean): prefix/suffix binomiality
⇒ abelian at every `L ≥ q`.

## The rectangle

For `m₁ < m₂ ≤ M₁ < M₂` in `[0,q)` put `ν̂` on the four pairs

    {m₁,M₁}: +c    {m₁,M₂}: −c    {m₂,M₁}: −c    {m₂,M₂}: +c

Then for `I = [p, p+L)` with `P = p+L−1`,

    Σ_U ν̂(U)[U ⊆ I] = c·([p≤m₁]−[p≤m₂])·([P≥M₁]−[P≥M₂]),

which for `m₂ = m₁+1`, `M₂ = M₁+1` is `−c·[p = m₂]·[P = M₁]`: a defect at the SINGLE interval
`[m₂, M₁]`, of length `a = M₁−m₂+1`.  Prefixes have `p = 0` and suffixes have `P = q−1`, so with
`m₂ ≥ 1` and `M₁ ≤ q−2` all prefixes and suffixes stay trivial.

Take `(m₁,m₂,M₁,M₂) = (0,1,a,a+1)`.  Superposition is linear and distinct `a` give defects at
distinct lengths, so for ANY finite `D ⊆ [2, q−2]`, with `q = max D + 2`,

    ν(x) = 2^{-q} (1 + Σ_{a∈D} c_a (χ_0−χ_1)(χ_a−χ_{a+1})),   χ_i = (−1)^{x_i},

is a probability law (nonnegative as soon as `4 Σ c_a ≤ 1`) whose block process is abelian at
EXACTLY the lengths outside `D`.  With `c_a = 1/(4|D|)` the weights are rational; with a single
`a` and `c = 1/4` they are `0, 2^{-q}, 2^{1-q}`, i.e. a digit alphabet `B = 2^q` with
multiplicities `0,1,2`.

`probes/c4_rectangle_design.py` verifies this in exact arithmetic for
`D = ∅,{2},{3},{4},{5},{2,3},{2,4},{3,5},{2,3,4},{2,4,5},{2,3,4,5,6}`, over all `L ≤ 4q`.

## Consequence and the remaining gap

**Every `S` with `1 ∈ S` and FINITE complement is realizable** by a single block-i.i.d. sequence.
That subsumes the `S = {1}` and `S = odds` witnesses in spirit and is the next Lean target.

The general case needs infinitely many scales, and the architecture is now explicit:

1.  A single block length `q` gives an eventually-`q`-periodic abelian set (the large-`L` value of
    `Φ_L` depends on `L` only through `L mod q`), so ONE scale can never realize an arbitrary `S`.
2.  Mixtures do not cancel: the `a`-design has its defect only in the `x²` coefficient and only at
    `L = a`, so mixing designs `P_a` (`a ∈ Sᶜ`) with any positive weights `λ_a` gives
    `F_2(L) = Σ_a λ_a F_2^{(a)}(L)`, which vanishes for `L ∈ S` and equals `λ_{a₀}F_2^{(a₀)}(a₀) ≠ 0`
    at `L = a₀ ∈ Sᶜ`.  **No sign or cancellation obstruction exists.**
3.  What remains is REALIZING the mixture by one sequence: either a multi-scale concatenation with
    densities `λ_a` (boundary error `O(1/chunk)`, uniform over all `L` simultaneously), or a
    stationary renewal process whose block length is `q_a` with probability `λ_a` — the latter is
    ergodic, so a typical sequence works, and all of §1's prefix/suffix cancellations survive
    verbatim because every trace on a block of ANY length is still prefix/suffix/full/interior.

## Refuted en route (do not retry)
*   `W ≡ 1` does NOT force `ν` uniform — only that each level `Σ_{|U|=ℓ} ν̂(U) = 0`.  (The lap-9
    odds witness has `ν̂({0}) = −1/2`, `ν̂({1}) = +1/2`.)
*   `ν̂` supported on singletons (`ν(x) = 2^{-q}(1 + Σ m_i χ_i)`, `Σ m_i = 0`) gives, for large `L`,
    `F_2(L) = −R(L mod q)/q` with `R` the cyclic autocorrelation of the prefix-sum vector.  Since
    `R(0) = Σ A_r² > 0`, every multiple of `q` is a defect: this sub-family can only realize
    complements of unions of full residue classes.  Pairs (`|U| = 2`) are essential.
