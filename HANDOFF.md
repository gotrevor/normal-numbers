# HANDOFF — B5′ / W3 campaign: prove the 4 sorries in `src/NormalNumbers/CFMixing.lean`

**Objective**: work package W3 of expedition B5′ — **the core**: Gauss-map
mixing via the decided self-contained route (`KHINCHIN.md` "W3 route":
conditional density → transfer-operator cone → Lévy ratio contraction).
All 4 `src/` sorries live in `CFMixing.lean`; `src/` sorry-free = done (the
self-stop gate).  W1 (`CFCylinder.lean`) and W2 (`CFDigitLaw.lean`) are
complete and axiom-clean — build on both freely.

**Read first**: `KHINCHIN.md` "W3 route" (the three steps + the Kuzmin
fallback), the module docstrings of `CFDefs.lean` / `CFMixing.lean`, and
the W2 technique notes in
`archive/handoff/HANDOFF-2026-08-23-W2-final.md` (ENNReal gotchas,
`gcongr`, tsum reindexing).  References: Khinchin *Continued Fractions*
ch. III; Iosifescu–Kraaikamp ch. 2 (Gauss–Kuzmin–Lévy).

**Statement discipline** 🎯: the 4 statement shapes are FROZEN
(guard-by-name; the 4 anchors are kernel-checked and must keep passing).
Add as many private intermediate lemmas as you like — in `CFMixing.lean`
or a new imported module — but do not weaken, reshape, or re-hypothesize a
frozen statement.  Oversight: `JUDGE.md`.
⚠️ **Escape valve, `cylinder_mixing` only**: if the geometric `ρᵏ`
envelope resists and only Kuzmin's `e^{-c√k}` materializes, do NOT grind
laps against the wall — STOP on it, write the evidence here, and the judge
weakens the frozen rate to a summable-error form.  That is a judge edit,
never a lap edit.

**Suggested order**:

1. `measurePreserving_gaussMap` — branch change of variables:
   `T⁻¹(A) ∩ (0,1) = ⋃ₖ (branch k)⁻¹` with branch maps `y ↦ 1/(k+y)`;
   per-branch substitution + `lintegral`/`withDensity` bookkeeping; the
   density identity `Σₖ g(1/(k+y))·1/(k+y)² = g(y)` is the classical
   telescoping sum (`1/((k+y)(k+1+y))` telescopes).  Junk `{Tx = 0}` is
   countable → `γ`-null.
2. `volume_inter_preimage_eq_integral` — `cylMap w` is an injective LFT
   `(0,1) → int(I_w)` with `|det| = 1` Jacobian `1/(qₙ+qₙ₋₁y)²`
   (determinant pieces already inside W1's `abs_cfVal_sub_bumpLast`
   development); `T^{|w|}(cylMap w y) = y` off a countable set (W1's
   digit-reading privates in `CFCylinder.lean` — lift like W2 lifted
   `one_le_cfK`).  Then `integral_image_eq_integral_abs_deriv_smul`-style
   substitution + `tailDensity` normalization by `volume_cfCylinder`.
   Sanity rail: `A = (0,1)` must recover `volume_cfCylinder` (∫h_t = 1).
3. `cylinder_mixing` — the cone argument.  Key algebra (check it early):
   extending `w` by digit `k` sends `t ↦ 1/(k+t)` (from Euler gluing:
   `K(w++[k]) = k·K(w) + K(w⁻)`), so the transfer step maps `h_t`-mixtures
   to `h_t`-mixtures; a Lévy-style ratio-oscillation argument contracts
   the log-density envelope geometrically (two transfer steps give a
   uniform positive overlap — digits 1 and 2 branches already suffice).
   Freeze private defs for the cone/envelope as you like.  Then integrate
   the pointwise envelope against `A` and normalize via `gaussMeasure`
   (`γ(A)` vs `∫_A g` is definitional unfolding of `withDensity`).
4. `gauss_kuzmin` — same machinery started at `h₀ = 1` (`t = 0` is in the
   cone; anchor `tailDensity 0 y = 1` pins it).  Should be a short
   corollary of the step-3 development, not a re-proof.

**Warnings** ⚠️: the W2 measurability helpers
(`measurable_gaussMap`/`measurable_cfDigit`/`measurableSet_cfCylinder`)
are `private` in `CFDigitLaw.lean` — lift them public when needed
(the W2→W1 lift is the precedent).  ENNReal: `gcongr` over
`mul_le_mul_right'`; cancellation via `ENNReal.mul_le_mul_iff_left/right`;
finiteness from cylinder ⊆ `Ioo 0 1`.  `push_neg` warns in this pin
(prefer `push Not`).  The `1 − C·ρᵏ` lower bounds are vacuous for small
`k` (`ofReal` of a nonpositive is `0`) — that is intended, don't
"strengthen" around it.  Work up to measure zero; digit-positivity
hypotheses stay load-bearing.

**Gates**: `lake build` green every commit; anchors keep passing; once all
4 are discharged, `#print axioms` each of the 4 = exactly
`propext`, `Classical.choice`, `Quot.sound`.
