import NormalNumbers.WeylCriterion
import NormalNumbers.DyadicToPrefix
import NormalNumbers.G4TransportW
import NormalNumbers.Disjunctive
import NormalNumbers.Wall

/-!
# The untruncated wiring: `IsNormal 4 G₄` from `CRTConstant` + `SiteDecayFull`
(DESIGN-2026-09-19-bcr-wiring.md §3b)

Frozen inputs (Props, never proved here):
* `CRTConstant h` — the Hardy–Littlewood-type law for ω-phases at frequency `h`, with the
  constant uniform in the window size `J` (KB verdict §2f–§2g: measured to `N = 10⁸`).
* `SiteDecayFull` — Delange–Wirsing–Halász: a one-site mean `𝔼 e(α ω(n+j))`, `α ∉ ℤ`, tends to `0`.

Everything else is elementary or already in the repo:
* `orbit 4 G₄ n ≡ tailB 4 n (mod 1)` — `TWeight.coe_tailB` + `lambert_omega`.
* L1 (`tail_error_le`): `|tailB n − truncTail J n| ≤ ∑_{j>J} ω(n+j)/4^j ≤ (log₂(n+J+2) + J + 3)/4^J`,
  from `omegaR_le_log`; with `J = J_N := ⌈log₂ log₂ N⌉ + 1` this is `o(1)` on `[N, 2N)` — no Mertens.
* W4 (`prefixMean_tendsto_zero_of_dyadic`), W3 (`equidistributed_of_weyl`), W1
  (`isNormal_iff_equidistributed_orbit`).
-/

open Filter Topology Finset
open scoped BigOperators

namespace NormalNumbers.G4

open NormalNumbers.PrimeLambert

/-- `e(x) = exp(2πi x)`. -/
noncomputable def ePhase (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

/-- The truncated tail `∑_{1 ≤ j ≤ J} ω(n+j) 4^{-j}`. -/
noncomputable def truncTail (J n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, omegaR (n + j + 1) / (4 : ℝ) ^ (j + 1)

/-- Full (untruncated) window mean `𝔼_{[N,2N)} ∏_{j≤J} e(h 4^{-j} ω(n+j))`. -/
noncomputable def fullWindowMean (N J : ℕ) (h : ℤ) : ℂ :=
  (∑ n ∈ Finset.Ico N (2 * N), ePhase (h * truncTail J n)) / N

/-- Full one-site mean `𝔼_{[N,2N)} e(h 4^{-j} ω(n+j))`, `j ≥ 1`. -/
noncomputable def fullSiteMean (N : ℕ) (h : ℤ) (j : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico N (2 * N), ePhase (h * omegaR (n + j) / (4 : ℝ) ^ j)) / N

/-- **Frozen node** (KB verdict §2f): the window mean is a bounded constant `c J` (the CRT local
factor `∏_p [1 + ∑_{j≤J}(z_j − 1)/p] / ∏_j (1 + (z_j − 1)/p)`, measured 1.36 / 0.33 / 6.1 at
`h = 1, 3, 5`) times the product of one-site means, with a `C / log N` relative error uniform in
`J`.  The constant is existentially quantified with a uniform bound `B`, which is all the wiring
uses; its arithmetic identity is recorded in the design doc, not asserted here. -/
def CRTConstant (h : ℤ) : Prop :=
  ∃ (c : ℕ → ℂ) (B C : ℝ), (∀ J, ‖c J‖ ≤ B) ∧ ∀ J : ℕ, ∀ᶠ N : ℕ in atTop,
    ‖fullWindowMean N J h - c J * ∏ j ∈ Finset.Icc 1 J, fullSiteMean N h j‖
      ≤ C / Real.log N * ∏ j ∈ Finset.Icc 1 J, ‖fullSiteMean N h j‖

/-- **Frozen input** (Delange–Wirsing–Halász, classical): a nontrivial one-site mean vanishes. -/
def SiteDecayFull : Prop :=
  ∀ (h : ℤ) (j : ℕ), 1 ≤ j → ¬ (∃ m : ℤ, (h : ℝ) / (4 : ℝ) ^ j = m) →
    Tendsto (fun N => ‖fullSiteMean N h j‖) atTop (𝓝 0)

/-- Window schedule: `J_N = ⌈log₂ log₂ N⌉ + 1`; any `J_N → ∞` with `4^{-J_N} log N → 0` works. -/
def windowJ (N : ℕ) : ℕ := Nat.log 2 (Nat.log 2 N) + 1

/-! ### L1: the tail lemma, elementary -/

/-- `|tailB 4 n − truncTail J n| ≤ (log₂(n + J + 2) + J + 3) / 4^J`. -/
theorem tail_error_le (J n : ℕ) :
    |TWeight.omega.tailB 4 n - truncTail J n|
      ≤ ((Nat.log 2 (n + J + 2) : ℝ) + J + 3) / (4 : ℝ) ^ J := by
  sorry

/-- The tail error is `o(1)` uniformly on `[N, 2N)` along the schedule `windowJ`. -/
theorem tail_error_uniform :
    Tendsto (fun N : ℕ => ((Nat.log 2 (2 * N + windowJ N + 2) : ℝ) + windowJ N + 3)
      / (4 : ℝ) ^ (windowJ N)) atTop (𝓝 0) := by
  sorry

/-! ### Assembly -/

/-- The orbit of `G₄` is the tail mod one (repo: `coe_tailB` + `lambert_omega`). -/
theorem orbit_eq_fract_tailB (n : ℕ) :
    orbit 4 (primeLambertAtBase 4) n = Int.fract (TWeight.omega.tailB 4 n) := by
  sorry

/-- For every `h ≠ 0` some site `j ≤ windowJ N` (eventually) has `h 4^{-j} ∉ ℤ`, and the product
of site means then tends to `0`; with the law, the window mean tends to `0`. -/
theorem fullWindowMean_tendsto_zero (hLaw : ∀ h : ℤ, h ≠ 0 → CRTConstant h)
    (hSite : SiteDecayFull) (h : ℤ) (hh : h ≠ 0) :
    Tendsto (fun N => fullWindowMean N (windowJ N) h) atTop (𝓝 0) := by
  sorry

/-- Dyadic Fourier means of the orbit vanish: tail error (L1) + `fullWindowMean_tendsto_zero`. -/
theorem dyadic_fourier_tendsto_zero (hLaw : ∀ h : ℤ, h ≠ 0 → CRTConstant h)
    (hSite : SiteDecayFull) (h : ℤ) (hh : h ≠ 0) :
    Tendsto (dyadicMean (fun n => ePhase (h * orbit 4 (primeLambertAtBase 4) n))) atTop (𝓝 0) := by
  sorry

/-- **Wiring theorem**: normality of `G₄` from the two frozen inputs. -/
theorem isNormal_G4_of_CRTConstant (hLaw : ∀ h : ℤ, h ≠ 0 → CRTConstant h)
    (hSite : SiteDecayFull) : IsNormal 4 (primeLambertAtBase 4) := by
  rw [isNormal_iff_equidistributed_orbit 4 (by norm_num)]
  refine equidistributed_of_weyl _ (orbit_mem_Ico 4 _) ?_
  intro h hh
  have hd := dyadic_fourier_tendsto_zero hLaw hSite h hh
  have := prefixMean_tendsto_zero_of_dyadic _ 1 (fun n => ?_) hd
  · -- `fourierMean u h = prefixMean (fun n => ePhase (h * u n))`
    sorry
  · sorry

end NormalNumbers.G4
