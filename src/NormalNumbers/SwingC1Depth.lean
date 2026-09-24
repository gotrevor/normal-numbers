import NormalNumbers.SwingC1Model

/-!
# The truncation depth: replacing `θ_n` by its finite-depth window

The kickoff's item 1 warns that `ω ≈ log log N` is unbounded, so the depth at which the carry may
be truncated must GROW with `N`.  This file turns that warning into an explicit, unconditional
bound, and so pins the depth at which hypothesis `H` must be stated.

`omegaTail_pow` (`SwingC1.lean`) is the exact shift identity `b^L · θ_n = H_L(n) + θ_{n+L}` with
`H_L(n) = omegaHead b L n = Σ_{i<L} ω(n+1+i) b^{L−1−i}` an INTEGER.  Hence

`h·θ_n − h·H_L(n)/b^L = h·θ_{n+L}/b^L`,

so the entire truncation question is the SIZE of `θ`, and that is settled unconditionally by
`omegaTail_le_log : θ_N ≤ log₂(N+1) + 1` (already in `SwingC1.lean`, from `2^{ω(m)} ≤ m`).

Results here:

* `norm_phase_omegaTail_sub_head` — pointwise, `‖e(h θ_n) − e(h H_L(n)/b^L)‖ ≤ 4π·|h|(log₂(n+L+1)+1)/b^L`;
* `norm_fullMean_phase_sub_head` — the same for the Weyl mean over `n < M`, with the uniform
  constant `D = |h|(log₂(M+L)+1)/b^L`;
* `depthBound_tendsto_zero` — `D → 0` along any depth schedule `L(M)` with
  `b^{L(M)} / log₂ M → ∞`; in particular `L(M) = ⌈2 log_b log₂ M⌉` works.

**Consequence for the crux.**  The Weyl sums of the `×b`-orbit of `G₄_b` are, to `o(1)`, the
finite-depth sums `mean_{n<M} Π_{i<L} z_i^{ω(n+1+i)}` with `z_i = e(h b^{i+1−L}/1)` — a
correlation of `L(M) ≍ log_b log₂ M` shifted copies of the multiplicative function `z^{ω}`.  So
hypothesis `H` needs depth exactly `log_b log log N + O(1)`, which is Delange's regime: at `L = 1`
it is Delange's theorem `mean z^{ω(n)} → 0` (`Re z < 1`), and the growth of `L` is what makes the
general case Elliott-hard.  This is the honest statement of where the difficulty sits.
-/

open Finset Filter Topology NormalNumbers.PrimeLambert

namespace NormalNumbers.CastingOut

/-- The uniform truncation error at depth `L` for the window `n < M`. -/
noncomputable def depthBound (b : ℕ) (h : ℝ) (M L : ℕ) : ℝ :=
  |h| * ((Nat.log 2 (M + L) : ℝ) + 1) / (b : ℝ) ^ L

lemma depthBound_nonneg (b : ℕ) (h : ℝ) (M L : ℕ) (hb : 2 ≤ b) : 0 ≤ depthBound b h M L := by
  have hbpos : (0 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  rw [depthBound]
  positivity

/-- **The pointwise truncation bound.**  The phase of the tail agrees with the phase of its
depth-`L` window to within `4π·|h|(log₂(n+L+1)+1)/b^L`. -/
theorem norm_phase_omegaTail_sub_head (b : ℕ) (hb : 2 ≤ b) (h : ℝ) (L n M : ℕ)
    (hn : n < M) (hsmall : 2 * Real.pi * depthBound b h M L ≤ 1) :
    ‖phase (h * omegaTail b n)
        - phase (h * ((omegaHead b L n : ℤ) : ℝ) / (b : ℝ) ^ L)‖
      ≤ 4 * Real.pi * depthBound b h M L := by
  have hbpos : (0 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hbL : (0 : ℝ) < (b : ℝ) ^ L := by positivity
  -- the exact difference of arguments
  have hkey : h * omegaTail b n - h * ((omegaHead b L n : ℤ) : ℝ) / (b : ℝ) ^ L
      = h * omegaTail b (n + L) / (b : ℝ) ^ L := by
    have hpow := omegaTail_pow b hb L n
    field_simp
    linear_combination h * hpow
  -- its size
  have htail : omegaTail b (n + L) ≤ (Nat.log 2 (n + L + 1) : ℝ) + 1 :=
    omegaTail_le_log b hb (n + L)
  have hmono : Nat.log 2 (n + L + 1) ≤ Nat.log 2 (M + L) :=
    Nat.log_mono_right (by omega)
  have hmonoR : ((Nat.log 2 (n + L + 1) : ℝ)) ≤ ((Nat.log 2 (M + L) : ℝ)) := by
    exact_mod_cast hmono
  have hnonneg : 0 ≤ omegaTail b (n + L) := omegaTail_nonneg b hb (n + L)
  have hsize : |h * omegaTail b (n + L) / (b : ℝ) ^ L| ≤ depthBound b h M L := by
    rw [abs_div, abs_of_pos hbL, abs_mul, abs_of_nonneg hnonneg, depthBound,
      div_le_div_iff_of_pos_right hbL]
    have habs : 0 ≤ |h| := abs_nonneg h
    nlinarith [htail, hmonoR, hnonneg]
  -- transfer through `phase`
  rw [norm_phase_sub_phase, hkey]
  have hsm : 2 * Real.pi * |h * omegaTail b (n + L) / (b : ℝ) ^ L| ≤ 1 := by
    have : 2 * Real.pi * |h * omegaTail b (n + L) / (b : ℝ) ^ L|
        ≤ 2 * Real.pi * depthBound b h M L :=
      mul_le_mul_of_nonneg_left hsize (by positivity)
    linarith
  have hbnd := norm_phase_sub_one_le hsm
  have : 4 * Real.pi * |h * omegaTail b (n + L) / (b : ℝ) ^ L|
      ≤ 4 * Real.pi * depthBound b h M L :=
    mul_le_mul_of_nonneg_left hsize (by positivity)
  linarith

/-- **The Weyl mean is the finite-depth Weyl mean, up to `4π·D`.**  This is the reduction the
crux needs: it replaces the infinite-depth object `θ_n` by the depth-`L` window
`H_L(n)/b^L = Σ_{i<L} ω(n+1+i) b^{−1−i}`, uniformly for `n < M`. -/
theorem norm_fullMean_phase_sub_head (b : ℕ) (hb : 2 ≤ b) (h : ℝ) (M L : ℕ)
    (hsmall : 2 * Real.pi * depthBound b h M L ≤ 1) :
    ‖fullMean (fun n => phase (h * omegaTail b n)) M
        - fullMean (fun n => phase (h * ((omegaHead b L n : ℤ) : ℝ) / (b : ℝ) ^ L)) M‖
      ≤ 4 * Real.pi * depthBound b h M L := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp only [fullMean, Nat.cast_zero, div_zero, sub_zero, norm_zero]
    have := depthBound_nonneg b h 0 L hb
    positivity
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hMc : ((M : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [fullMean, fullMean, div_sub_div_same, ← Finset.sum_sub_distrib, norm_div,
    Complex.norm_natCast, div_le_iff₀ hMr]
  calc ‖∑ n ∈ range M, (phase (h * omegaTail b n)
          - phase (h * ((omegaHead b L n : ℤ) : ℝ) / (b : ℝ) ^ L))‖
      ≤ ∑ n ∈ range M, ‖phase (h * omegaTail b n)
          - phase (h * ((omegaHead b L n : ℤ) : ℝ) / (b : ℝ) ^ L)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ range M, (4 * Real.pi * depthBound b h M L) :=
        Finset.sum_le_sum fun n hn =>
          norm_phase_omegaTail_sub_head b hb h L n M (Finset.mem_range.mp hn) hsmall
    _ = 4 * Real.pi * depthBound b h M L * M := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-! ### The depth requirement, stated crisply -/

/-- **The depth requirement.**  The truncation error vanishes along a depth schedule `L(M)`
exactly when `b^{L(M)}` beats `log₂ M`.  So the crux's finite-depth hypothesis `H` must hold at
depth `L(M) ≍ log_b log₂ M` — Delange's regime — and no slower schedule will do: by
`omegaTail_le_log` the tail really is of size `log₂ M`, and by `sum_primePeriodicTerm_period`
(mean `1/(b−1)` per prime, no decay) no truncation of the PRIME expansion is uniformly small
either.  Depth `L` bounded is therefore refuted, not merely unproven. -/
theorem depthBound_tendsto_zero_of_pow_div_atTop (b : ℕ) (hb : 2 ≤ b) (h : ℝ) (L : ℕ → ℕ)
    (hL : Tendsto (fun M => (b : ℝ) ^ (L M) / ((Nat.log 2 (M + L M) : ℝ) + 1)) atTop atTop) :
    Tendsto (fun M => depthBound b h M (L M)) atTop (𝓝 0) := by
  have hbpos : (0 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have h1 : Tendsto
      (fun M => ((b : ℝ) ^ (L M) / ((Nat.log 2 (M + L M) : ℝ) + 1))⁻¹) atTop (𝓝 0) :=
    hL.inv_tendsto_atTop
  have h2 : Tendsto
      (fun M => |h| * ((b : ℝ) ^ (L M) / ((Nat.log 2 (M + L M) : ℝ) + 1))⁻¹) atTop (𝓝 0) := by
    simpa using h1.const_mul |h|
  refine h2.congr fun M => ?_
  have hA : ((b : ℝ) ^ (L M)) ≠ 0 := by positivity
  have hB : ((Nat.log 2 (M + L M) : ℝ) + 1) ≠ 0 := by positivity
  rw [depthBound, inv_div]
  field_simp

end NormalNumbers.CastingOut
