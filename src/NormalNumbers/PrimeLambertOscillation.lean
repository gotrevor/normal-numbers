import NormalNumbers.PrimeLambertConfig

/-!
# The oscillation hypothesis and the conditional irrationality wiring

`PhaseOscillation` is the precise analytic statement (equation (5) of the proof draft,
`docs/prime-lambert-irrationality.md`): for every nonzero integer `q` there is a sequence of
transported configurations `c N`, cutoffs `K N`, and finite progression samples with frozen
quotient residues, such that `c N` cancels at all sites `1..K N` and the normalized
progression average of `e(q · F_N(n))` tends to zero.

The wiring theorem `irrational_of_phaseOscillation` derives `Irrational primeLambert` from it,
using only Theorem A (`phaseSum_sub_int`): under rationality the phase is constant of modulus one
on every such progression, so its average has modulus one and cannot tend to zero.

The headline `irrational_primeLambert` is *sorry-gated* through `phaseOscillation` — the open
analytic obligation.  It is NOT a proved irrationality result; see the docs for the chain of
sub-obligations that would discharge it.
-/

open Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeLambert

/-- `e(x) = exp(2π i x)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e; exact Complex.norm_exp_ofReal_mul_I _

lemma e_add_int (x : ℝ) (w : ℤ) : e (x + w) = e x := by
  unfold e
  have : (((2 * Real.pi * (x + w) : ℝ) : ℂ) * Complex.I)
      = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I + (w : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- A finite progression sample for a configuration, with quotient data frozen modulo every
prime dividing each multiplier. -/
structure ProgressionFamily (c : TConfig) where
  /-- the sampled points `n` -/
  P : Finset ℤ
  nonempty : P.Nonempty
  /-- quotients `k n a` with `n = d·k + s` -/
  k : ℤ → ℕ × ℤ → ℕ
  onProg : ∀ n ∈ P, OnProgression c k n
  frozen : ∀ n ∈ P, ∀ n' ∈ P, ∀ a ∈ c.support, ∀ p ∈ a.1.primeFactors, k n a ≡ k n' a [MOD p]

/-- Normalized phase average `𝔼_{n ∈ P} e(q F(n))`. -/
noncomputable def phaseAverage (c : TConfig) (K : ℕ) (P : Finset ℤ) (q : ℤ) : ℂ :=
  (∑ n ∈ P, e (q * phaseSum c K n)) / P.card

/-- **The oscillation hypothesis** (draft eq. (5)).  For each `q ≠ 0`: configurations `c N`
cancelling at sites `1..K N`, with frozen progression samples, whose phase averages tend to `0`.
-/
def PhaseOscillation : Prop :=
  ∀ q : ℤ, q ≠ 0 →
    ∃ (c : ℕ → TConfig) (K : ℕ → ℕ) (D : ∀ N, ProgressionFamily (c N)),
      (∀ N j, 1 ≤ j → j ≤ K N → CancelsAt (c N) j) ∧
      Tendsto (fun N => ‖phaseAverage (c N) (K N) (D N).P q‖) atTop (𝓝 0)

/-- Under rationality, the phase is constant on a frozen progression, so its average has
modulus one. -/
theorem norm_phaseAverage_eq_one {q z : ℤ} (hq : (q : ℝ) * primeLambert = z)
    (c : TConfig) (K : ℕ) (D : ProgressionFamily c)
    (hc : ∀ j, 1 ≤ j → j ≤ K → CancelsAt c j) :
    ‖phaseAverage c K D.P q‖ = 1 := by
  obtain ⟨n₀, hn₀⟩ := D.nonempty
  have hconst : ∀ n ∈ D.P, e (q * phaseSum c K n) = e (q * phaseSum c K n₀) := by
    intro n hn
    obtain ⟨w, hw⟩ := phaseSum_sub_int hq c K D.k n n₀ (D.onProg n hn) (D.onProg n₀ hn₀)
      (D.frozen n hn n₀ hn₀) hc
    have : (q : ℝ) * phaseSum c K n = q * phaseSum c K n₀ + w := by linear_combination hw
    rw [this, e_add_int]
  have hcard : (D.P.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr D.nonempty).ne'
  rw [phaseAverage, Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul,
    mul_div_cancel_left₀ _ hcard, norm_e]

/-- **Conditional wiring.**  `PhaseOscillation → Irrational primeLambert`. -/
theorem irrational_of_phaseOscillation (h : PhaseOscillation) : Irrational primeLambert := by
  rw [irrational_iff_ne_rational]
  intro a b hb hG
  have hq : (b : ℝ) * primeLambert = (a : ℤ) := by
    rw [hG]; field_simp
  obtain ⟨c, K, D, hc, hT⟩ := h b hb
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) :=
    hT.congr (fun N => norm_phaseAverage_eq_one hq (c N) (K N) (D N) (hc N))
  exact one_ne_zero (tendsto_const_nhds_iff.mp h1)

/-- The open analytic obligation (draft §5).  **Disclosed `sorry`**: this is the target of the
compressed-cancellation campaign, decomposed in `PrimeLambertAnalytic`; it is not proved. -/
theorem phaseOscillation : PhaseOscillation := by
  sorry

/-- Headline, **sorry-gated through `phaseOscillation`**.  Not a proved theorem. -/
theorem irrational_primeLambert : Irrational primeLambert :=
  irrational_of_phaseOscillation phaseOscillation

end NormalNumbers.PrimeLambert
