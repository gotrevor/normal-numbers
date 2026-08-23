# PENDING WORK — B5′ / W3 campaign (staged 2026-08-23)

**Campaign**: discharge the 4 sorries in `src/NormalNumbers/CFMixing.lean`
(work package W3 of expedition B5′, **the core** — see `HANDOFF.md` for the
route and `KHINCHIN.md` "W3 route" for the plan).  Everything else in
`src/` is sorry-free: Stoneham ✅, W1 (12/12) ✅, W2 (10/10) ✅ — all
axiom-clean, judge-verified; records in `ROADMAP.md`, `JUDGE.md`, and
`archive/handoff/`.

**Open (4/4)**: `measurePreserving_gaussMap` ·
`volume_inter_preimage_eq_integral` · `cylinder_mixing` · `gauss_kuzmin`

**Lap advance (2026-08-23, this lap)**: the analytic crux of
`cylinder_mixing` is settled.  New module `CFContraction.lean` proves
`stepOp_lipschitz` (axiom-clean, sorry-free): the tail-parameter transfer
operator `(Pφ)(t) = Σ_k (1+t)/((k+t)(k+1+t))·φ(1/(k+t))` maps `L`-Lipschitz
functions on `[0,1]` to `(9/10)L`-Lipschitz — hence `Pᵏ` contracts at rate
`(9/10)ᵏ`, the geometric GKL rate, with **no coupling / Wasserstein /
Birkhoff cones** (Abel-resummed weight difference + telescoping majorants;
route numerically validated, true factor ≈ 0.41).  Remaining plan for
`cylinder_mixing`: (1) prove step-1 (`volume_inter_preimage_eq_integral`,
cylMap change of variables); (2) continuant algebra: `t(w++[k]) = 1/(k+t(w))`
and `|I_{w++[k]}|/|I_w| = stepWeight (t w) (k-1)`; (3) recursion:
`Σ_{|v|=k}(|I_{wv}|/|I_w|)Φ(t(wv)) = (Pᵏ Φ)(t(w))` via W2's
`volume_eq_tsum_extensions`; (4) stationarity `∫ Pφ dν = ∫ φ dν` for
`dν = dt/((1+t)log 2)` (per-branch substitution — same telescope as
`measurePreserving_gaussMap`); (5) assembly with `Φ(t) = ∫_A tailDensity t`,
`Lip(Φ) ≤ 2·vol A ≤ (4 log 2)·γ(A)`, giving `C = 4 log 2`, `ρ = 9/10`.
`gauss_kuzmin` = same assembly from start `t = 0`.

**Crux**: `cylinder_mixing` (the cone/ratio-contraction — expect it to be
most of the campaign; ⚠️ it carries the judge-governed escape valve, see
HANDOFF).  `volume_inter_preimage_eq_integral` is the real-analysis
substitution (LFT image measure).  `measurePreserving_gaussMap` is the
classical telescoping branch sum.  `gauss_kuzmin` should fall out of the
`cylinder_mixing` development (`t = 0` start), not get its own machinery.

**Done-when**: `src/` sorry-free (the default self-stop gate) + the 4
axiom-clean.  Toolchain: v4.33.1, present in the box store — no gate.
