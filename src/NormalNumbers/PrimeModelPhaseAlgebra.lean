import NormalNumbers.G4WiringSparse
import NormalNumbers.PrimeModelRadical

/-!
# Prime model, assembly part A: complex phase algebra

Elementary complex-number and real inequalities used by the end-to-end assembly of the
frozen `KMT_quant₂` (`papers/prime-model-assembly-2026-09-22.md`).  Nothing here is
arithmetic: these are the inequalities behind E1 (restoring primes above `y`) and E5 (the
model phase contracts, uniformly in the frequency `h`).

* `norm_one_add_le_exp` : `|1+w| ≤ exp(Re w + |w|²/2)` for every `w ∈ ℂ` (global; no `|w|<1`).
* `norm_prod_sub_prod_le` : `|∏ a − ∏ b| ≤ ∑ |a − b|` for `1`-bounded factors.
* `norm_pow_sub_pow_le` : `|z^{a+c} − z^a| ≤ 2c` for `|z| = 1`.
* `sum_inv_sq_le` : distinct naturals `> k` have `∑ 1/n² ≤ 1/k`.
* `exists_site_re_nonpos` : the least nontrivial window site has `Re z ≤ 0` (the site phase is
  `e(m/4)` with `4 ∤ m`).
* `model_phase_norm_le` : `‖∏_i (1 + A/p_i)‖ ≤ e^{2k} exp(−∑_i 1/p_i)` when `Re A ≤ −1`, `|A| ≤ 2k`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.PhaseAlgebra

open NormalNumbers.G4 NormalNumbers.G4Sparse

/-- `|1+w|² = 1 + (2 Re w + |w|²) ≤ exp(2 Re w + |w|²)`; take square roots. -/
theorem norm_one_add_le_exp (w : ℂ) : ‖1 + w‖ ≤ Real.exp (w.re + ‖w‖ ^ 2 / 2) := by
  sorry

/-- Telescoping: `|∏ a − ∏ b| ≤ ∑ |a − b|` when every factor has norm `≤ 1`. -/
theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℂ)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ ∑ i ∈ s, ‖a i - b i‖ := by
  sorry

/-- `|z^c − 1| ≤ c |z − 1|` for `|z| = 1`. -/
theorem norm_pow_sub_one_le (z : ℂ) (hz : ‖z‖ = 1) (c : ℕ) :
    ‖z ^ c - 1‖ ≤ c * ‖z - 1‖ := by
  sorry

/-- `|z^{a+c} − z^a| ≤ 2c` for `|z| = 1`. -/
theorem norm_pow_sub_pow_le (z : ℂ) (hz : ‖z‖ = 1) (a c : ℕ) :
    ‖z ^ (a + c) - z ^ a‖ ≤ 2 * c := by
  sorry

/-- Distinct naturals exceeding `k ≥ 1` have `∑ 1/n² ≤ ∑_{n>k} 1/(n(n−1)) = 1/k`. -/
theorem sum_inv_sq_le {ι : Type*} [Fintype ι] (p : ι → ℕ) (hinj : Function.Injective p)
    {k : ℕ} (hk : 1 ≤ k) (hkp : ∀ i, k < p i) :
    ∑ i, (1 : ℝ) / ((p i : ℝ) ^ 2) ≤ 1 / k := by
  sorry

/-- The site phases of the window: site `j+1` (for `j : Fin k`) carries `e(h/4^{j+1})`.  This is
exactly the phase attached to `ω_S(n+j+1)` in `truncTailS`. -/
noncomputable def zPhase (h : ℤ) (k : ℕ) : Fin k → ℂ :=
  fun j => ePhase ((h : ℝ) / (4 : ℝ) ^ (j.val + 1))

@[simp] lemma norm_zPhase (h : ℤ) (k : ℕ) (j : Fin k) : ‖zPhase h k j‖ = 1 :=
  norm_ePhase _

/-- **The least nontrivial site has `Re z ≤ 0`.**  If `j₀ ∈ [1,k]` is least with `h/4^{j₀} ∉ ℤ`
then `h/4^{j₀−1} = m ∈ ℤ` (minimality, or `j₀ = 1`) and `h/4^{j₀} = m/4` with `4 ∤ m`, so the
phase is `e(m/4) ∈ {i, −1, −i}`.  Uniform in `h`: no constant depends on it. -/
theorem exists_site_re_nonpos (k : ℕ) (h : ℤ) (hntw : NontrivialWindow k h) :
    ∃ j : Fin k, (zPhase h k j).re ≤ 0 := by
  sorry

/-- **E5, model phase contraction.**  With `A = ∑_j (z_j − 1)`, `|z_j| = 1`, some `Re z_{j₀} ≤ 0`
(so `Re A ≤ −1`, `|A| ≤ 2k`), and distinct primes `p_i > k`:
`‖∏_i (1 + A/p_i)‖ ≤ exp(∑_i (Re A/p_i + |A|²/(2p_i²))) ≤ e^{2k} · exp(−∑_i 1/p_i)`. -/
theorem model_phase_norm_le {ι : Type*} [Fintype ι] (p : ι → ℕ) (hinj : Function.Injective p)
    {k : ℕ} (hk : 1 ≤ k) (hkp : ∀ i, k < p i) (z : Fin k → ℂ) (hz : ∀ j, ‖z j‖ = 1)
    (j₀ : Fin k) (hre : (z j₀).re ≤ 0) :
    ‖∏ i, (1 + (∑ j, (z j - 1)) / (p i : ℂ))‖
      ≤ Real.exp (2 * k) * Real.exp (- ∑ i, (1 : ℝ) / (p i : ℝ)) := by
  sorry

/-- The window mean is `1`-bounded (trivial bound used in regime R1). -/
theorem norm_windowMeanS_le_one (S : ℕ → Prop) [DecidablePred S] (J : ℕ) (h : ℤ) (x : ℕ) :
    ‖windowMeanS S J h x‖ ≤ 1 := by
  sorry

end NormalNumbers.PrimeModel.PhaseAlgebra
