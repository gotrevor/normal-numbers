# HANDOFF 2026-09-24 — Delange slot: L7 proved, L2/L4 open

Branch `wip/delange-slot`, HEAD `d3c8084`, tree clean, `lake build` green.
Objective (KICKOFF-2026-09-24-delange-slot.md): prove `omegaLarge_mean_tendsto_zero` and
`twisted_omegaLarge_mean_tendsto_zero` in `src/NormalNumbers/DelangeSlot.lean` (both still `sorry`).

## Route (settled this session — see DESIGN-2026-09-24-delange-route.md)

Levin–Fainleib, NOT Halász.  `S N log N = z · N · m N + O_P(N)` where `m N = ∑_{k≤N} h k/k`;
discrete Abel turns that into the recursion `(log N − z) σ N = z Ψ N + O(1)`, and the recursion
forces `σ N → 0` because `Re z < 1`.

**Refuted sub-routes (do not retry):** plain PNT (`Δ = o(x)`) is insufficient — the `k ≤ √N`
range needs `|Δ(x)| ≪ x/log x` and `k > √N` needs `∫ δ(y) dy/y < ∞`.  The Selberg-`Λ₂` variant
relaxes the error budget by a factor `u` and would run on the *elementary* symmetry formula
`ψ₂ = 2x log x + O(x)`, but it needs `θ₁` and `ψ₁₁` separately (coefficients `z` vs `z²`) and only
their **sum** is elementary.  Hence a quantitative PNT is unavoidable.

## Landed

* `PNTPort/` — PrimeNumberTheoremAnd's `MediumPNT` import closure (14 files, ~12k lines) vendored
  and compiling on v4.33.1 with **no math edits**; `#print axioms MediumPNT` clean.  Separate
  `lean_lib`, not in `defaultTargets`.  Provenance/licence in `src/PNTPort/README.md`.
* `DelangeSlotBasic.lean` — `omegaLarge` additivity + the prime-power insertion rule.
* `DelangeSlotIdentity.lean` — sorry-free: general Dirichlet swap, `sum_hfun_mul_log`
  (`A N = ∑_{d≤N} Λ d ∑_{m≤N/d} h (d m)`), shift lemmas at large/small primes, `‖T_p X‖ ≤ X/p`.
* `DelangeSlotAnalytic.lean` — L3 (hyperbola transpose), L5 (`‖A N − S N log N‖ ≤ N`),
  L6 (discrete Abel) **proved**; **L2 and L4 open** (disclosed `sorry`, on-path).
* `DelangeSlotRecursion.lean` — **L7 fully proved, axiom-clean**: MVT telescoping
  `∑_{3≤n≤N} 1/(n log n) ≤ loglog N − loglog 2` (sharp constant is load-bearing: a dyadic bound
  would break `Re z > 0.69`), the one-step modulus bound, discrete Gronwall, tail estimates,
  and the assembly `recursion_tendsto_zero`.
* `probes/delange_slot.py` — N = 10^6 data; decay is `(log N)^{Re z −1}` with an O(1)
  Selberg–Delange constant.  No power saving ⟹ no `native_decide` anchor is possible.

## Next (in order)

1. **L4** (`exists_L4` in `DelangeSlotAnalytic.lean`): `‖∑_k h k ψ(N/k) − N·m N‖ ≤ C N`.
   Reduce to `∑_{k≤N} |Δ(N/k)| = O(N)`, `Δ = ψ − id`.  Split at `k ≤ √N` (use `MediumPNT`:
   `exp(−c (log x)^{1/10})` beats every power of `log`) and `k > √N` (substitute `y = N/k`; the
   sum becomes `N ∫_3^{√N} dy/(y (log y)^A)`, convergent for `A > 1`).  Plus `|Δ(x)| ≤ Cx`
   from Chebyshev for `x < 3`.
2. **L2** (`exists_L2`): routine — `∑_{p,j} log p / p^{j+1} < ∞` for the `p ∣ m` correction, and
   the `p ≤ P` block is `O_P(N)` because `P` is fixed.
3. Assemble L2+L3+L4+L5 ⟹ `S N log N = z N m N + O_P(N)`; with L6 that is exactly the hypothesis
   of `recursion_tendsto_zero`, giving `omegaLarge_mean_tendsto_zero`.
4. Rung 2 (twist): `m = s·t` smooth×rough, expand the residue class of `t` in Dirichlet
   characters, run the same machinery on `χ·h` (the Λ-identity holds verbatim).

## Watch-outs

* `Finset.one_le_prod` (not `one_le_prod'`, which wants `MulLeftMono`), `div_le_div₀`,
  `div_le_div_iff₀`, `card_insert_of_notMem`, `Real.pow_div_factorial_le_exp` (explicit `x`).
* The PNTAnd port needed: strip `import Architect`, `@[blueprint …]` (bracket-match while
  skipping `/-- … -/`, LaTeX contains brackets) and `blueprint_comment /-- … -/`; plus two
  one-line repairs in `Fourier.lean` (`Circle.norm_coe`, `norm_num`).
