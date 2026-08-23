# PENDING WORK — B5′ campaign (updated 2026-08-23, post-W3)

**W3 ✅ COMPLETE** (2026-08-23, 8 laps): all four frozen `CFMixing.lean`
statements proved, axiom-clean — `measurePreserving_gaussMap` (B1),
`volume_inter_preimage_eq_integral`, `cylinder_mixing` (C = 8 log 2,
ρ = 9/10, geometric — escape valve unused), `gauss_kuzmin` (B4).
`src/` is sorry-free.  See `HANDOFF-2026-08-23-2040.md`.

**W4 groundwork STARTED (this lap)**: `CFGammaMixing.lean` proves the
KPW-Lemma-6 substitute — the W4 correlation-decay engine — axiom-clean:

- `setIntegral_inter_preimage`: the s-started conditional density
  identity `∫_{I_w ∩ T^{-|w|}B} h_s = (∫_B h_{tChain s w})·(∫_{I_w} h_s)`
  (generalizes aux from `h_0 = 1` to any `h_s`, s ∈ [0,1]).
- `gaussMeasure_cylinder_mixing` (**γ-mixing, geometric rate**):
  `|γ(I_v ∩ T^{-(|v|+g)}A) − γ(I_v)γ(A)| ≤ (9/10)^g·4|A|·γ(I_v)`.
  Route: mixture Fubini γ = ∫₀¹ h_s·Leb dλ(s) + the pin bound, which is
  uniform in the start t — no new analysis was needed.

**W4 frontier — `CFBlockFreq.lean` (lap-authored groundwork).**
`S_n x = blockCount A n x = Σ_{k<n} 1_A(Tᵏx)` (Birkhoff sum). Route DE-RISKED:
γ-mixing is geometric ⇒ covariances summable ⇒ Var(S_n)=O(n).

DONE this lap (all axiom-clean, `#print axioms` = trust triple):
  ✅ `integral_blockCount` — first moment `∫ S_n dγ = n·γ(A)`.
  ✅ `gaussMeasureReal_pair_shift` — `γ(T^{-j}A ∩ T^{-(j+m)}A) = γ(A ∩ T^{-m}A)`.
  ✅ `integral_blockCount_sq` — second moment
     `∫ S_n² dγ = Σ_{j,j'<n} γ(T^{-j}A ∩ T^{-j'}A)`.
  ✅ `abs_cov_le` — **per-pair covariance bound** (the γ-mixing consumer):
     `|γ(I_v∩T^{-m}I_v) − γ(I_v)²| ≤ (9/10)^{m−|v|}·4|I_v|·γ(I_v)` (m≥|v|),
     `≤ 2γ(I_v)` (m<|v|).  ← the route-decisive step; mixing→covariance done.

REMAINING (2 disclosed sorries in src, pure Finset arithmetic — no more
measure theory):
  ⬜ `variance_blockCount_le` — `Var(S_n) ≤ (4|v|+80)·n·γ(I_v)`.  Route: combine
     `integral_blockCount_sq` + `abs_cov_le` (via `pair_shift` at gap `|j−j'|`);
     the only work is the double-sum gap-count reindex `Σ_{j,j'<n} B(|j−j'|) ≤
     2n·Σ_{d<n}B(d)` + geometric tail `Σ_d B(d) ≤ (2|v|+40)γ(I_v)`.
  ⬜ `chebyshev_blockCount` — `γ{|S_n/n − γ(I_v)| ≥ δ} ≤ (4|v|+80)γ(I_v)/(δ²n)`.
     Markov on `(S_n − nγ(I_v))²` (`meas_ge_le_variance_div_sq` or
     `mul_meas_ge_le_lintegral₀`) fed by `variance_blockCount_le`.

Then: conditioned-on-brick version (s-started identity → same pin), and the
b-ary side (B–Y Lemmas 8/9 — check Counting.lean/Visits.lean overlap).

Tools confirmed: `measurePreserving_gaussMap`, `gaussMeasure_univ`=1 (⇒
`IsProbabilityMeasure gaussMeasure` instance added in CFBlockFreq),
`gaussMeasure_cylinder_mixing`, `measureReal_preimage`, mathlib
`meas_ge_le_variance_div_sq` (Probability/Moments/Variance.lean).
2. Conditioned version on a base cylinder I_w (B–Y need per-stage bad
   measure < ¼ *given the current brick*): same computation under the
   conditional measure — the s-started identity makes every conditional
   a tailDensity mixture, so the same pin applies.  Alternatively work
   with Leb-conditionals directly via `volume_inter_preimage_horizon`.
3. b-ary side: Lemma 8 (Hardy–Wright Thm 148 Chernoff block counting)
   + Lemma 9 (BHS 3.1 concatenation) — check overlap with
   `Counting.lean`/`Visits.lean` first.
4. DRAFT frozen W4 statements for judge ratification (do NOT put
   unratified "frozen" statements in a scaffold file claiming authority;
   put proposals in drafts/).

**Judge attention requested**: ratify W4 statement shapes; note the
γ-mixing bonus (stronger than the planned Leb-only route: it is exact
γ-correlation decay, geometric, multiplicative in γ(I_v)).
