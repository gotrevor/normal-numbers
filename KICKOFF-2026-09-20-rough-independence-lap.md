# KICKOFF 2026-09-20 — split N1 into N1a (smooth/CRT, elementary) and N1b (`RoughIndependence`, the crux)

Branch `wip/g5-prime-subset`.  Engine Opus/low.  New file `src/NormalNumbers/G4WiringRough.lean`, importing
`G4WiringCRT`.  **Do not change any existing statement**; add new ones.  Why: blueprint probe 6
(`BLUEPRINT-2026-09-19-g4-normality.md`) measured that, after stripping the primes `≤ y`, the window mean
factorises into the product of its site means up to a CRT constant with error `≍ 1/(y log N)`, uniformly
in the number of sites.  That is the crux of the SD sector, isolated from the elementary small-prime part.
This lap freezes it and wires it back into the existing `CRTConstant` route.

## Vocabulary (fixed; use these names)

`omegaR m` is `ω(m)` (real-valued) in the repo; `ePhase`, `truncTail J n = ∑_{j<J} ω(n+j+1)/4^{j+1}`,
`fullWindowMean N J h`, `fullSiteMean N h j`, `windowJ N`, `CRTConstant h`, `SiteDecayFull`, `WindowDecay h`,
`ChowlaSector h`, `isNormal_G4_of_split` are all in `G4WiringCRT.lean`.  Mathlib: `Nat.primeFactors`,
`primorial` (`∏ p ≤ n prime`), `Nat.primorial_...` lemmas.

## The ratified new statements (verbatim; only their proofs are yours)

```lean
/-- Distinct prime divisors of `m` that exceed `y` (the `y`-rough part of `ω`). -/
def omegaAbove (y m : ℕ) : ℕ := (m.primeFactors.filter (fun p => y < p)).card
/-- Distinct prime divisors of `m` that are `≤ y` (the `y`-smooth part of `ω`). -/
def omegaLe (y m : ℕ) : ℕ := (m.primeFactors.filter (fun p => p ≤ y)).card

theorem omegaR_eq_omegaLe_add_omegaAbove (y m : ℕ) :
    omegaR m = (omegaLe y m : ℝ) + omegaAbove y m

/-- `ω_{≤y}(n + j)` depends only on `n mod primorial y`. -/
theorem omegaLe_add_primorial (y m : ℕ) : omegaLe y (m + primorial y) = omegaLe y m

noncomputable def smoothTail (y J n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, (omegaLe y (n + j + 1) : ℝ) / (4 : ℝ) ^ (j + 1)
noncomputable def roughTail (y J n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, (omegaAbove y (n + j + 1) : ℝ) / (4 : ℝ) ^ (j + 1)

theorem truncTail_eq_smooth_add_rough (y J n : ℕ) : truncTail J n = smoothTail y J n + roughTail y J n
theorem ePhase_truncTail_factor (y J n : ℕ) (h : ℤ) :
    ePhase (h * truncTail J n) = ePhase (h * smoothTail y J n) * ePhase (h * roughTail y J n)
theorem smoothTail_add_primorial (y J n : ℕ) : smoothTail y J (n + primorial y) = smoothTail y J n

noncomputable def smoothWindowMean (N J : ℕ) (h : ℤ) (y : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico N (2 * N), ePhase (h * smoothTail y J n)) / N
noncomputable def roughWindowMean (N J : ℕ) (h : ℤ) (y : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico N (2 * N), ePhase (h * roughTail y J n)) / N
noncomputable def smoothSiteMean (N : ℕ) (h : ℤ) (j y : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico N (2 * N), ePhase (h * omegaLe y (n + j) / (4 : ℝ) ^ j)) / N
noncomputable def roughSiteMean (N : ℕ) (h : ℤ) (j y : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico N (2 * N), ePhase (h * omegaAbove y (n + j) / (4 : ℝ) ^ j)) / N

/-- Schedule form of `CRTConstant`: the law only along `J = windowJ N`. -/
def CRTConstantSched (h : ℤ) : Prop :=
  ∃ (c : ℕ → ℂ) (B C : ℝ), (∀ J, ‖c J‖ ≤ B) ∧ ∀ᶠ N : ℕ in atTop,
    ‖fullWindowMean N (windowJ N) h - c (windowJ N) * ∏ j ∈ Finset.Icc 1 (windowJ N), fullSiteMean N h j‖
      ≤ C / Real.log N * ∏ j ∈ Finset.Icc 1 (windowJ N), ‖fullSiteMean N h j‖

theorem crtConstantSched_of_crtConstant {h : ℤ} (hL : CRTConstant h) : CRTConstantSched h

theorem fullWindowMean_tendsto_zero_of_sched {h : ℤ} (hL : CRTConstantSched h)
    (hSite : SiteDecayFull) (hh : h ≠ 0) :
    Tendsto (fun N => fullWindowMean N (windowJ N) h) atTop (𝓝 0)

/-- **Frozen node N1b** (blueprint probe 6, 2026-09-20): after stripping the primes `≤ y`, the window mean
factorises into the product of its site means up to a bounded constant, with error `≍ 1/(y log N)`
(measured `c(y)/log N`, `c(y) ≈ 1/y`, stable in `N` and bounded in the number of sites). -/
def RoughIndependence (h : ℤ) : Prop :=
  ∃ (c : ℕ → ℕ → ℂ) (B C : ℝ), (∀ y J, ‖c y J‖ ≤ B) ∧ ∀ y : ℕ, 2 ≤ y → ∀ᶠ N : ℕ in atTop,
    ‖roughWindowMean N (windowJ N) h y
        - c y (windowJ N) * ∏ j ∈ Finset.Icc 1 (windowJ N), roughSiteMean N h j y‖
      ≤ C / ((y : ℝ) * Real.log N) * ∏ j ∈ Finset.Icc 1 (windowJ N), ‖roughSiteMean N h j y‖

/-- **Frozen node N1a′** (decoupling of the periodic small-prime phase from the rough phase; the
"multiplicative functions in progressions mod `primorial y`" statement).  Unprobed - probe before proving. -/
def SmoothRoughDecoupling (h : ℤ) : Prop :=
  ∃ C : ℝ, ∀ y : ℕ, 2 ≤ y → ∀ᶠ N : ℕ in atTop,
    ‖fullWindowMean N (windowJ N) h - smoothWindowMean N (windowJ N) h y * roughWindowMean N (windowJ N) h y‖
      ≤ C / Real.log N * ∏ j ∈ Finset.Icc 1 (windowJ N), ‖fullSiteMean N h j‖ ∧
    ‖(∏ j ∈ Finset.Icc 1 (windowJ N), fullSiteMean N h j)
        - (∏ j ∈ Finset.Icc 1 (windowJ N), smoothSiteMean N h j y)
          * ∏ j ∈ Finset.Icc 1 (windowJ N), roughSiteMean N h j y‖
      ≤ C / Real.log N * ∏ j ∈ Finset.Icc 1 (windowJ N), ‖fullSiteMean N h j‖

/-- **Frozen, elementary** (N1a, the CRT product over `p ≤ y` is nonvanishing off the Chowla sector and
`→ 1` along the sites): the product of smooth site means is bounded below. -/
def SmoothNonvanishing (h : ℤ) : Prop :=
  ∀ y : ℕ, 2 ≤ y → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
    δ ≤ ∏ j ∈ Finset.Icc 1 (windowJ N), ‖smoothSiteMean N h j y‖

/-- The average over `[N, 2N)` of a `P`-periodic function bounded by `1` is within `2P/N` of its
average over one period. -/
theorem periodic_mean_close (F : ℕ → ℂ) (P : ℕ) (hP : 0 < P) (hper : ∀ n, F (n + P) = F n)
    (hb : ∀ n, ‖F n‖ ≤ 1) (N : ℕ) (hN : 0 < N) :
    ‖(∑ n ∈ Finset.Ico N (2 * N), F n) / N - (∑ n ∈ Finset.range P, F n) / P‖ ≤ 2 * P / N

/-- N1a proper: the smooth window mean is the CRT constant times the product of smooth site means, up to
`O_y(windowJ N · primorial y / N)`.  `c'` is the ratio of period averages. -/
theorem smoothWindowCRT (h : ℤ) (y : ℕ) (hy : 2 ≤ y) (hS : SmoothNonvanishing h) :
    ∃ (c' : ℕ → ℂ) (B : ℝ), (∀ J, ‖c' J‖ ≤ B) ∧ ∀ᶠ N : ℕ in atTop,
      ‖smoothWindowMean N (windowJ N) h y
          - c' (windowJ N) * ∏ j ∈ Finset.Icc 1 (windowJ N), smoothSiteMean N h j y‖
        ≤ B * (windowJ N : ℝ) * primorial y / N

/-- **Wiring**: N1 (schedule form) from N1a + N1a′ + N1b. -/
theorem crtConstantSched_of_rough {h : ℤ} (hR : RoughIndependence h) (hD : SmoothRoughDecoupling h)
    (hS : SmoothNonvanishing h) : CRTConstantSched h

theorem isNormal_G4_of_rough
    (hSD : ∀ h : ℤ, h ≠ 0 → ¬ ChowlaSector h →
      RoughIndependence h ∧ SmoothRoughDecoupling h ∧ SmoothNonvanishing h)
    (hCh : ∀ h : ℤ, h ≠ 0 → ChowlaSector h → WindowDecay h)
    (hSite : SiteDecayFull) : IsNormal 4 (primeLambertAtBase 4)
```

## Leaves, in order (commit a compiling skeleton with named sorries FIRST)

1. `omegaAbove`/`omegaLe`, `omegaR_eq_omegaLe_add_omegaAbove` (unfold `omegaR`; a `filter` split of
   `primeFactors`), `omegaLe_add_primorial` (a prime `p ≤ y` divides `m + primorial y` iff it divides `m`;
   `Nat.dvd_primorial`-type lemma), then `smoothTail`/`roughTail`, `truncTail_eq_smooth_add_rough`,
   `ePhase_truncTail_factor` (`ePhase_add`), `smoothTail_add_primorial`.
2. `CRTConstantSched`, `crtConstantSched_of_crtConstant` (trivial), `fullWindowMean_tendsto_zero_of_sched`
   - adapt the proof of `fullWindowMean_tendsto_zero_of_law` in `G4WiringCRT.lean` (it only ever uses
   `J = windowJ N`); do not edit the original.
3. `periodic_mean_close`: split `[N,2N)` into `⌊N/P⌋` full periods plus a remainder of `< P` terms and
   compare with the period average; the two boundary blocks cost `≤ 2P/N`.
4. `smoothWindowCRT`: `smoothTail y J` and each site phase are `primorial y`-periodic (leaf 1), bounded by
   1; take `c' J := A_W / ∏ A_j` (period averages, Lean division); use `hS` to get `∏ A_j ≠ 0` and
   `‖c'‖ ≤ 1/δ` eventually; the product of `J` site means moves by `≤ J · 2P/N` (each factor `≤ 1`).
5. `crtConstantSched_of_rough`: fix `y = 2`; `fullWindow ≈ S_W·R_W` (hD.1), `S_W ≈ c'∏S_j` (leaf 4),
   `R_W ≈ c∏R_j` (hR), `∏S_j∏R_j ≈ ∏full_j` (hD.2); convert `∏‖R_j‖` into `∏‖full_j‖` via hD.2 + hS
   (`∏‖R_j‖ ≤ (1 + C/log N)/δ · ∏‖full_j‖`); `c J := c' J * c 2 J`, bounded by `B·B'`.  Errors of size
   `J·P/N` are `≤ 1/log N` eventually.
6. `isNormal_G4_of_rough` from `isNormal_G4_of_split`'s shape: SD sector via
   `fullWindowMean_tendsto_zero_of_sched ∘ crtConstantSched_of_rough`, Chowla sector as given.

Frozen Props (`RoughIndependence`, `SmoothRoughDecoupling`, `SmoothNonvanishing`) are **never proved**.
If leaf 3 or 4 resists after a real attempt, leave it as a named `sorry` with a comment and finish the
wiring on top of it - the wiring theorems are the deliverable.  `native_decide`, long `omega`/`nlinarith`
steps, deprecations are all fine.  Report the crux advance, not the sorry count.
