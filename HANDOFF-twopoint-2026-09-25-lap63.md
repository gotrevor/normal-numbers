# HANDOFF twopoint — lap 63, 2026-09-25: **RUNG 2 LANDED — the wall is a theorem**

Branch `wip/twopoint-avg`.  Full `lake build` green (**9301 jobs**).  All new declarations
`#print axioms`-clean.  **No `sorry` introduced.**  New file only:
`src/NormalNumbers/TwoPointC3Wall.lean` (imported from `src/NormalNumbers.lean`); no frozen file
touched.  Lap 62 landed rung 0 (`6978dd5`).

## The advance

`DIRECTION.md` rung 2 — "machine-check the wall" — is done, unconditionally:

    tendsto_mean_tailLarge_atTop :  2 ≤ b →  ∀ P,
      Tendsto (fun N => (∑_{n<N} tailLarge P b n) / N) atTop atTop

with the quantitative form

    sum_tailLarge_lower :  (∑_{p≤N}1/p − ∑_{p≤P}1/p − 2)/b  ≤  (1/N)∑_{n<N} tailLarge P b n .

So **no fixed-depth truncation of the large-prime tail can control it**: the crux's object has
unbounded mean.  "The peel must grow with `N`" is now a kernel fact, which is exactly what
`DIRECTION.md` asked rung 2 to supply (and what forbids the refuted fixed-depth family).

### How it goes (cheaper than the rate suggests)

Only the `i = 1` term of `T_n = ∑_{i≥1} ω_{>P}(n+i)b^{−i}` is used, plus Mertens' second theorem
in divergence form.  New lemmas:

* `omegaLarge_eq_card_primesBigLe` — for `1 ≤ m ≤ N`, `ω_{>P}(m)` counts the primes in `(P,N]`
  dividing `m`.  Moving to an `m`-independent ambient set is what makes the double count possible.
* `sum_omegaLarge_succ` — **the double count**: `∑_{n<N} ω_{>P}(n+1) = ∑_{P<p≤N} ⌊N/p⌋`
  (`Finset.sum_comm` on `card_filter`, then `Nat.card_multiples`).
* `tailLarge_ge_first`, `cast_div_ge`, `sum_inv_primesBigLe_ge`, `card_primesBigLe_le`,
  `primesBigLe`.
* The Mertens input is the in-tree `TwoPointDelangeOmega.tendsto_delangeL_atTop`
  (`∑_{p≤N}1/p → ∞`).  Note: `TwoPointMertensLower.mertens_lower` (which the lap-61 handoff
  pointed at) is the `∑ log p/p ≥ log N − 9` form and is the *wrong* shape for this — extracting
  `∑1/p → ∞` from it needs dyadic partial summation.  `delangeL`'s divergence was already there.

The true rate is `(log log N)/(b−1)` (all `i`); the crude divergence is all a consumer needs.

## Ladder state

| rung | status |
|---|---|
| 0 — scale re-plumb `WeylTailAlmostAll → IsRichSubpoly` | **DONE** lap 62 (`6978dd5`) |
| 1 — depth-1 peel `addCharTail_depthOne` | **DONE** lap 61 (`29a4d7d`) |
| 2 — the wall `tendsto_mean_tailLarge_atTop` | **DONE** this lap |
| 3 — the pin `WeylTailHypothesis ⟺ ShiftElliott`, then TT2025 §5.2 | open |

## NEXT SESSION

1. **Rung 3, the pin.**  State `ShiftElliott` for growing depth `K ≈ log_b log log N` and prove
   `WeylTailHypothesis b ⟺ ShiftElliott` — C3's analogue of `multiElliottWeighted_iff_growing`.
   Rung 2 is the ingredient that makes the "growing" side forced.
2. **The adjacent unconditional item** `SwingC3Signed.lean`'s docstring names and nobody did:
   `∏_{P<p≤K} ‖primeFactor b p h‖ → 0`.  Route: one-term lower bound
   `Sig_p ≥ ‖1 − e(h·b^{p−1}/(b^p−1))‖² → ‖1−e(h/b)‖² > 0` into the proved
   `norm_primeFactor_sq_le`, giving `‖primeFactor‖ ≤ 1 − σ/(4p)`, then `mertens_lower`
   (this IS the right shape for `mertens_lower`, unlike rung 2).
3. Harden rung 0: derive `ScalesDense` from a logarithmic-density hypothesis on the complement,
   so the input is literally TT2025's `log dens E ≪ L^{-c}`.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%; provable with known techniques 3% (untouched, as ratified).
- `WeylTailHypothesis` (every scale) TRUE 97%; provable with known techniques 8%.
- `WeylTailAlmostAll` provable from 2026 literature 70%; `⇒ IsRichSubpoly` **in the kernel**.
- No fixed-depth route to the crux exists: **certain** (this lap).
