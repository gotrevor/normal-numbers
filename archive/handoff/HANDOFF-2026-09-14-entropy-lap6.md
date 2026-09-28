# HANDOFF — entropy expedition, lap 6 (2026-09-14, Opus grind)

**Branch** `wip/g4-entropy`.  **HEAD** `7620389`.  `lake build` green, 8947 jobs.
New module `src/NormalNumbers/G4EntropyBudget.lean`, sorry-free, no new axioms.

## What was proved

**E0 is no longer conditional.**

```
NormalNumbers.G4.Sched.entropy_E0 :
  ∀ {K k₄}, K = 4 * k₄ → 33856 ≤ K →
    (1/5) * k₄ * ((K^2+1)^K) < (jointLaw (gridOf K (N K)) _ k₄ (primeLambertAtBase 4)).H₂
```

`#print axioms` = `[propext, Classical.choice, Quot.sound]`.  The joint quantized sample of
`G₄ = ∑_p 1/(4^p−1)` — `m_K = k₄`-bit binary windows at the base-four orbit positions — carries
at least a fifth of the maximal entropy `m_K H_K`, for the infinite family `K = 4k₄ ≥ 33856`.

Supporting declarations (same file):

| declaration | content |
|---|---|
| `entropy_cover_bound` | the entropy analogue of `gridB_bound` (see below) |
| `entropy_cover_sum_le` | the same, summed over `goodSets`, arbitrary nonneg prefactor |
| `hDim_le_one_add_mul_rDim` | `H ≤ (1+2/K)r`, the sharper form the exponent count needs |
| `Sched.budget_terms_le`, `Sched.smallPrime_term_le` | `Λδ₃ ≤ 3e^{−4}+1/32` |
| `Sched.b₀_lt_X` | `P_K ≠ ∅` at the schedule's outer scale |

## The mathematics that made it work

`gridB_bound` beats the cylinder count `((b^ℓ−1)^M)^H` with the **covering deficit of an omitted
word**.  E0 has no omitted word: the prefactor is `(2^m)^H` with `2^{−m} ≤ η`, so per unit of
`r = (K²)^K` the prefactor contributes `+(K/4)log 2` and the tube fraction `η^g` contributes
`−(1−1/K)(K/4)log 2`.  They cancel to `O(1)·log 2`, which **loses** to the spectral term
`11.5√K`.  The **entropy deficit** is what supplies the room: with prefactor `2^{(1−δ/2)mH}` the
cancellation leaves `−δK(log 2)/8`, and the cover term closes exactly when

    92√K + 46  ≤  δ · K · log 2,      i.e.   δ ≳ 133/√K.

`entropy_cover_bound` is stated with that hypothesis, so it **already covers the whole
`δ ↓ C/√K` range**.  Only the three fixed allowances inherited from disjunctivity force `δ = 4/5`
here.

## Budget ledger at `δ = 4/5` (`δ/(2−δ) = 2/3`)

| term | bound | source |
|---|---|---|
| cover | `≤ 1/8` | `entropy_cover_bound` |
| `δ₂ = δbig+δfar` | `= 1/4` | `hbig_holds`, `hfar_holds` |
| `2κ` | `≤ 1/8` | `jackson_term_le` |
| `Λδ₃` | `≤ 3e^{−4}+1/32 ≈ 0.106` | `smallPrime_term_le` |
| **total** | **`< 0.607`** | vs `2/3` |

## Next, hardest first: E1 / qualitative E0 need `δ_K ≍ 1/√K`

Brief §4's `e_K = a_K/ρ_K + 2κ_K + Λ_K q_K = o(K^{−1/2})` is now the *only* obstruction, and
`m_K = K/4` makes the arithmetic match E1 exactly: `δ_K = C/√K` gives
`H₂ ≥ m_K H_K − (C/4)·H_K·√K`, which **is** E1's claimed rate.

Slack audit of the four allowances (done this lap, on paper):

1. **`2κ`** — free.  With `D = (16K²2^{k₄})²` instead of `Dj = (16K2^{k₄})²`,
   `εη√(D+1) ≥ 16K`, so `2κ ≤ 1/(8K)`.  Side conditions `hN` and `2D+1 ≤ 4^K` both survive
   with room (`2^K D ≈ 2^{1.5K}K⁴` against `4^{N−1}`, `N = 100K²`).
2. **`δfar`** — free, pure arithmetic on the *existing* `hfar_holds`: it gives
   `≤ (1/8)(1/K)(1/2)^K` whereas `ε·η = (1/K)(1/2)^{k₄}`, so `δfar = (1/8)2^{−3k₄}`.
3. **`δbig`** — needs a copy-edit of `hbig_holds` (its exported inputs `dyadic_factor_le`,
   `sample_term_le`, `log_Mx_div_le` are all top-level).  Its core is
   `2Ka⁶ + 34a⁴ ≤ δbig·((1/K)a)` with `a = 2^{−k₄}`; `δbig = a²` works with room
   (`4K²a³ ≤ 1` and `68Ka ≤ 1`).
4. **`Λδ₃`** — the real work.  `main_term_le`/`term_a..d_le` are stated with RHS `e^{−4}`,
   `1/64`, but their proofs have astronomical slack (the main term's exponent is
   `2Kr − 10.78Kr`, and `term_a/d` compare `2^{e₁}` against `2^{100·2^m}`).  Strengthened
   copies with RHS `2^{−K}` are mechanical but ~200 lines.

**Lap 7 plan:** do 1–3, state 4 as a named disclosed `sorry` in `src/`
(`smallPrime_term_small`), and assemble `entropy_E0_rate` / E1 on top.  Lap 8 grinds 4.

## Claim discipline

`entropy_E0` is an unconditional theorem about the implemented schedule.  It is **not** the
brief's qualitative E0 (`H₂/(m_K H_K) → 1`), which needs `δ_K → 0`; it is the `δ = 4/5` instance.
Nothing here asserts normality of `G₄`, and the transfer `T_E` (brief §6) is untouched.
