# Non-normality below the sub-power weight, `c > 3` 🎯

**Objective:** make `src/NormalNumbers/CoefmassErdosBorweinSubpower.lean` sorry-free.  The headline
`ebRandom_ae_not_normal_subpower` must be axiom-clean (`[propext, Classical.choice, Quot.sound]`).

**Do not change** `subpowerWeight` or the headline statement: they are verbatim from the KB packet.
Helpers go above the headline or in a new `CoefmassErdosBorweinSubpowerAux.lean`.  No
`native_decide`, no new `axiom`, no edits to existing files except deleting `private` on helpers in
`CoefmassErdosBorweinNegative.lean` that you need.
**NEVER git push:** `research/eb-random` is local only.

## Status

### Lap 1 checkpoint (2026-10-26): marginal/Fatou criterion proved; headline has 1 sorry

- Added `CoefmassErdosBorweinSubpowerAux.lean` and proved the axiom-clean theorem
  `ae_not_normal_of_capped_marginal_residual`.  It reduces the frozen headline to a deterministic
  statement: the Cesàro average of
  `min 1 (Σ_j b^{-(j+1)} μ_M(n+j+1))` tends to zero uniformly in the averaging cutoff.
- This is the reusable marginal-only skeleton requested in step 1.  It proves, without independence:
  the exact marginal expectation identity for selected-divisor counts; the finite-residual cap
  bound; passage to the infinite residual by Fatou; the normal-orbit positive lower bound; and the
  final Markov/continuity-from-below contradiction.  It reuses the deleted-head orbit identity and
  rational-shift normality from `CoefmassErdosBorweinNegative.lean`.
- The theorem statement and `subpowerWeight` in `CoefmassErdosBorweinSubpower.lean` remain byte-for-byte
  unchanged.  Its import now points at the auxiliary module.  No `native_decide`, new axiom, or edit
  to `CoefmassErdosBorweinNegative.lean` was made.
- Exact verification:
  - `lake env lean src/NormalNumbers/CoefmassErdosBorweinSubpowerAux.lean` — succeeds.
  - `lake env lean src/NormalNumbers/CoefmassErdosBorweinSubpower.lean` — succeeds with exactly the
    expected headline `sorry` warning.
  - `~/personal/bin/lean-green . --target NormalNumbers.CoefmassErdosBorweinSubpowerAux --import
    NormalNumbers.CoefmassErdosBorweinSubpowerAux --axioms
    NormalNumbers.ErdosBorweinSubpower.ae_not_normal_of_capped_marginal_residual` —
    FORMALIZE-TIER GREEN; axioms exactly `propext`, `Classical.choice`, `Quot.sound`.
  - `~/personal/bin/lean-green .` — FORMALIZE-TIER GREEN, 10847 jobs.

**Current blocker / next attack.**  Prove the deterministic capped-residual tail hypothesis for
`delta m ≤ C * subpowerWeight c m`.  Start with the one-block domination by
`smoothDivisorCount (dyadicExpCutoff (ℓ+1)) n`, then formalize the per-block exponent
`s_ℓ = sqrt(c * log u_ℓ / u_ℓ) / log 2` and its explicit Chernoff bound.  This is now the
only mathematical input between the proved criterion and the frozen headline.

## Reuse (CoefmassErdosBorweinNegative.lean, PROVED)
- `ebRandom_ae_not_normal_of_marginal_bound` and `ebRandom_ae_not_normal`: the Fatou/orbit-average
  skeleton, the exact residual `R_M(n) = Σ_{j≥1} b^{−j} D_M(n+j)` with `frac(b^n Y_M) ≤ R_M(n)`, and
  the Wall rational-shift invariance.  Copy that skeleton.
- `momentEulerProduct_le_log_rpow`, the uniform-in-`T` bound
  `(1/T)Σ_{n≤T} τ(smoothPart y n)^s ≤ exp((2^s − 1)·mertensBound + 1)·(log y)^{2^s − 1}` for
  `0 < s ≤ 1`.  Its constant is uniform in `s ∈ (0,1]`, which is the key fact.
- `smoothPart`, and the dyadic-block decomposition used for `largeDivisorMass_moment_small`.

## The proof (the fixed-`s` moment of the old proof DIVERGES here; use a per-block `s` instead)

Write `w(m) = C·subpowerWeight c m`, `μ_M(n) = Σ_{d ∣ n, d > M} w(d)`, and
`u = log log d`, so `w = C·2^{−u}·2^{−√(c u log u)}`.

1. **Log-moment criterion (marginal-only).**  Assume that for every `ε > 0`,
   `lim_{M→∞} sup_N Σ_{j≥1} (1/N)·#{n ≤ 2N : μ_M(n) > ε b^{j/2}} = 0`.  Then the conclusion follows.
   - Let `G(n)` be the event `∀ j, μ_M(n+j) ≤ ε b^{j/2}`.  On `G(n)`,
     `E_X min(1, R_M(n)) ≤ Σ_j b^{−j} μ_M(n+j) ≤ ε Σ_j b^{−j/2}`.
   - Off `G(n)` the bound is `1`.  Its density is `≤ Σ_j dens{μ_M(n + j) > ε b^{j/2}}`.  Shifts
     `j ≤ N` land in `[1, 2N]`.  For `j > N`, use `μ_M(m) ≤ C·τ(m) ≤ C·2√m < ε b^{j/2}` for large `j`.
   - Then Fatou exactly as in `ebRandom_ae_not_normal_of_marginal_bound`: on the normal event the
     orbit average of `frac` tends to `1/2`.
2. **Blocks.**  Block `ℓ` holds the divisors with `log d ∈ (2^ℓ, 2^{ℓ+1}]`, so `u ∈ (ℓ ln 2, (ℓ+1) ln 2]`.
   Its divisors divide `smoothPart y_ℓ n` with `log y_ℓ = 2^{ℓ+1}`, so there are at most
   `τ(smoothPart y_ℓ n)` of them.  `w` is eventually decreasing (check this; only `ℓ ≥ ℓ₀` matters),
   so block `ℓ` has mass `≤ τ(smoothPart y_ℓ n)·w_ℓ` with `w_ℓ := w(e^{2^ℓ})`.
   Union bound with weights `ℓ^{−2}`: `μ_M > X ⇒ ∃ ℓ ≥ log₂ log M` with
   `τ·w_ℓ > X ℓ^{−2}/ζ(2)`, or any convenient summable weights.
3. **Per-block Chernoff with `s = s_ℓ`.**  Let `σ_ℓ = √(c·log u_ℓ/u_ℓ)` and `s_ℓ = σ_ℓ/ln 2 ≤ 1`
   (for large `ℓ`).  Then
   `P_n(τ·w_ℓ > Y) ≤ K·Y^{−s}·w_ℓ^s·e^{(u_ℓ + ln 2)(2^s − 1)}`, and the exponent is
   `u(e^σ − 1 − σ) − σ√(c u log u) + O(1) ≤ −(c/2)·log u + o(log u)`, since `e^σ − 1 − σ ≤ σ²/2 + σ³`
   and `u σ³ → 0`.
4. **Sum over `j`.**  `Σ_j (ε b^{j/2})^{−s} ≤ ε^{−1}·(1 − b^{−s/2})^{−1} ≲ 1/(s ln b) ≍ √(u/(c log u))`.
5. **Sum over blocks.**  `Σ_{ℓ ≥ ℓ_M} ℓ^{1/2 − c/2 + o(1)}·(log ℓ)^{−1/2} → 0` as `M → ∞` iff `c > 3`.
   This is where `hc : 3 < c` is used.  Pick explicit slack, e.g. bound everything by
   `ℓ^{−(c−3)/4 − 1}` for `ℓ ≥ ℓ₀(c)`.

Degenerate cases: `C ≤ 0` forces `δ ≡ 0` (BernoulliLawNat gives `δ ≥ 0`), and `E_b = 0` is not normal,
so it is consistent.  The hypothesis is implied by `δ ≤ C′(log m)^{−a}` with `a > ln 2`, so this
strictly extends `ebRandom_ae_not_normal`.

## Order of attack
1 (criterion, reusing the Fatou skeleton) → 2 → 3 (the analytic exponent bound as a standalone
real-analysis lemma) → 4 → 5 → assemble.  Commit each green lemma.
