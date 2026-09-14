# HANDOFF — entropy expedition, lap 13 (2026-09-14, Opus grind)

**Branch** `wip/g4-entropy`.  `lake build` green, 8954 jobs.  `G4EntropyScales.lean` extended,
sorry-free, axiom-clean.  Previous baton: `HANDOFF-2026-09-14-entropy-lap12.md`.

## Headline: the last restriction is gone — the §6 negative answer is unconditional

```
G4Entropy.card_le_of_scalePairs   : |U' ∩ [0,L)| ≤ (1/8)·L
G4Entropy.not_dense_of_scalePairs : 0 < L → ¬ (L ≤ 2·|U' ∩ [0,L)|)
```

for **any** finite set `S` of distinct scale *pairs* `(K,N)` with `K ≥ 2`, **any** family `F` of
grids carrying the schedule's parameter functions `gridQ/gridD₀/gridUmax` at those pairs, **any**
sample ranges `XX` and block lengths `mm p ≤ K`, and any position set `U'` the family covers.

Lap 12 fixed one layer count `nn K` per scale; lap 13 removes that, which was the only surviving
gap in the averaging direction.  **No admissible sampler family of any shape reads half of any
prefix of the digit positions** — and by `G4EntropyBarrier.exists_nonnormal_of_digitLocal` no
statement about any such sample can imply ordinary binary normality.

### What made it work

`pairWeight_le`: `w(K,N) = (U+1)m/(2(1+Q D₀)) ≤ 1/U ≤ (4(K+N))^{-K}`, using
`4(K+N) ≤ gridB K N = K²(K+N)+1` for `K ≥ 2` and `gridB^K ≤ gridUmax`.

`sum_double_le`: `Σ_{(K,M) distinct, K,M ≥ 2} (4M)^{-K} ≤ 1/8`, from
* `sum_pow_Icc_le` — `Σ_{K ∈ T, K ≥ 2} r^K ≤ 2r²` for `0 ≤ r ≤ 1/2`, uniform in the ratio
  (shift `K ↦ K-2`, inject into `range n`, `geom_sum_mul` for the tail);
* `sum_inv_sq_le` — `Σ_{M=2}^{n} 1/M² ≤ 1 − 1/n` by telescoping `1/M² ≤ 1/(M−1) − 1/M`.

The reindexing `(K,N) ↦ (K, K+N)` is injective, so a finite set of scale pairs maps into the
double-series index set.

## Where the expedition stands (complete §6 picture)

| statement | status |
|---|---|
| `entropy_E0`, `entropy_E1` (§2–§4) | proved, unconditional, clean (laps 1–7) |
| `T_E` (§6 primary) | **refuted** (lap 8: `not_T_E`), structurally (lap 9) |
| `T_S`, `T_mix` | refuted-or-vacuous (lap 9) |
| any joint-law statement | cannot imply normality (lap 9, `exists_nonnormal_jointLocal`) |
| repair by translated grids | refuted (lap 10) |
| repair by any family at one scale | refuted (lap 11) |
| repair by any family over any scales `K` | refuted (lap 12) |
| repair by any family over any scale pairs `(K,N)` | **refuted (lap 13)** |
| §5 (S) | defined (`S_freq`), open, off the critical path |

The brief's §8 outcome condition — E0/E1 settled AND `T_E` proved or refuted with a witness
meeting its exact premise — is met, and the §6 positive branch has been answered negatively as
far as the interface allows.

## What is NOT claimed

Nothing about the normality of `G₄`.  Nothing about samplers outside the `GridParams` interface
at the schedule's parameter functions — a genuinely different arithmetic input (one whose
frozen modulus `Q` does not dominate the alphabet size `H_K·m_K`) is untouched by all of this,
and is the only conceivable route left.  That is the honest residue of the expedition.

## Next bounded test, hardest first

1. **Is `2 d_min ≤ C·H_K·m_K` achievable at all?**  Every negative result above traces to
   `d_α ≥ 1 + Q D₀` with `Q = (U+K+N+2)!` while the alphabet is `H_K m_K = (K²+1)^K·K/4`.  State
   `ReadableScale C : ∃ admissible parameters with 2(1+Q D₀) ≤ C·H·m` and decide it against
   `G4CRTInput`'s requirements on `Q` (the freezing needs `m ∣ Q` for all `m ≤ U`, hence
   `Q ≥ lcm(1..U) ≥ 2^U`).  If `Q ≥ 2^U ≥ 2^{B^K}` is forced, the answer is *no* and the
   expedition's §6 column is closed with a proof that the obstruction is intrinsic to freezing.
2. §5's (S): state what `entropy_E0` actually controls about `S_freq`.  Now a clean leaf.
3. A reflection/altitude lap could record the §6 table above in `STATUS.md`/`DIRECTION.md`
   (grind laps do not edit the directive).

## Lean gotchas from this lap

- `geom_sum_eq` gives `(x^n − 1)/(x − 1)`, whose denominator is *negative* for `x < 1`; use
  `geom_sum_mul` (`(Σ x^i)·(x−1) = x^n − 1`) and `nlinarith` instead of dividing.
- `Finset.Icc_succ_right` does not exist; `ext x; simp only [Finset.mem_Icc, Finset.mem_insert];
  omega` is the reliable way to peel the top of an `Icc`.
- `congrArg Prod.fst h` fails on a `Prod.mk` equation; `simp only [Prod.mk.injEq] at h` first.
- After `Finset.sum_image`, the summand is `f (g x)` *unreduced* — follow with
  `Finset.sum_congr rfl` + `push_cast` rather than expecting syntactic match.
