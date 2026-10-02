# HANDOFF — C′ quant lap 1 (2026-10-02), branch proof/cprime-quant

Scope: sorry-free `src/NormalNumbers/CPrimeQuant.lean` (directive: DIRECTION.md CURRENT DIRECTIVE).

## Done (all green, axiom-clean where finished)
- Glue `cPrimeQuant_of_parts`; `cPrimeQuant_holds := cPrimeQuant_of_parts`.
- CRUX PROVED: `windowWeylQuant` → `orbitWeylQuant` (C₁=10⁶, ρ₁=1/3, u=max(3000,⌈log 1/ρ⌉)).
  Infra: gap 4 `orbitWeylLe_of_window`; tail `tailOK_of_sqrtFreshMassLe`; gap 3 `siteBudget`
  capped at 2 upstream; gap 1 `CPrimeQuantSchedule.lean` (fixed-u port + term leaves
  termE1_le / termE4a_le / termE4b_le / termE4c_tendsto / termE5_tendsto / epsG_eventually_le).
- Gap 5 in progress, `CPrimeQuantET.lean` (Fejér sandwich, NO Fourier series): fejK facts
  (nonneg, expand, unit period mass, `fejK_le` decay 1/(4δ²(H+1)) for δ≤|t|≤1−δ),
  `fejG` window, `window_mean_eq`, `norm_winCoef_le`, `window_mean_err`
  (|avg g − (β−α)| ≤ 2Σ_{k≤H}‖W_k‖/(πk)).

## Open sorries in scope
1. `orbitDefectLe_of_weyl` (CPrimeQuant.lean). Plan:
   - upper sandwich: α=a−δ, β=c+δ; for x∈[a,c): fejG ≥ ∫_{−δ}^{δ}K ≥ 1−η (period mass at p=−1/2
     minus two side pieces ≤ η via fejK_le; integral_mono_interval); so 1_I ≤ g+η. Trivial case
     c−a+2δ ≥ 1.
   - lower sandwich: α=a+δ, β=c−δ; x∈[0,1)\[a,c) ⇒ t=x−y has δ≤|t|≤1−δ ⇒ g ≤ η; x∈I ⇒ g ≤ 1
     (β−α ≤ 1, period mass). Trivial case c−a ≤ 2δ.
   - RESTATE remainder as `2δ + 1/(4δ²(H+1)) + Σ_{h∈Icc 1 H} 2B h/h` (needs δ ≤ 1/2) and
     re-tune glue: δ=ρ, H=⌈1/ρ³⌉, log(H+1) ≤ 4L (ρ≤1/3), harmonic ≤ 5L → C = O(C₁).
2. `cPrimeResidueRich_holds` — not started (Mertens-in-AP upper bound, DivergentRecip from
   `not_summable_residueClass_prime_div`, orbit→digit translation).
