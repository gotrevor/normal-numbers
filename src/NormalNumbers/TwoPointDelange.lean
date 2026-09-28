import NormalNumbers.TwoPointGrowingCut

/-!
# Chipping the last PROVEN input of the C1 chain: `DelangeMean`

After `TwoPointKataiFree.lean` and `TwoPointGrowingCut.lean`, `ConjC1` rests on exactly two
inputs: the open leaf (D) / `MultiElliott`, and

    DelangeMean t :  E_{m ≤ N} e(t·ω(m)) → 0      (`SwingC1Delange.lean`)

for `t = m₀/b`, `b ∤ m₀`.  Writing `z = e(t)`, a `b`-th root of unity `≠ 1`, this is Delange's
theorem (1969): `Σ_{m ≤ x} z^{ω(m)} ≍ x (log x)^{z−1} = o(x)` since `Re z < 1`.  It is the only
axiom on the chain that is a PROVEN theorem, so it is the 🟡 debt to chip.

## This file: the elementary skeleton, and the exact analytic residue

The classical elementary opening is the Dirichlet convolution `z^ω = 1 * h_z` with

    h_z(n) = (z − 1)^{ω(n)}  if `n` is squarefree,  0 otherwise

(`delangeKernel`), because `Σ_{n | m, n squarefree} (z−1)^{ω(n)} = ((z−1)+1)^{ω(m)} = z^{ω(m)}`
— a powerset expansion, `sum_delangeKernel_divisors`.  Hyperbola summation then gives the exact
identity `sum_zpow_omega_eq` :

    Σ_{m ≤ N} z^{ω(m)} = Σ_{n ≤ N} h_z(n) · ⌊N/n⌋ ,

so `|E_{m≤N} z^{ω(m)}| ≤ |Σ_{n≤N} h_z(n)/n| + (1/N) Σ_{n≤N} |h_z(n)|` (`delangeMean_of_kernel`).

Both pieces are named below, and the reason the first one is *supposed* to vanish is proved here
unconditionally: the Euler product of `h_z` decays, because

    ‖1 + (z−1)/p‖² = 1 − 2(1 − Re z)(1/p − 1/p²)      (`norm_delangeLocal_sq`, an EQUALITY)

so `‖1 + (z−1)/p‖ ≤ 1 − (1 − Re z)/(2p)` for `p ≥ 2` and Mertens finishes
(`prod_delangeLocal_tendsto_zero`, via the repo's `prod_tendsto_zero_of_norm_le` — the same engine
as leaf (M) and `prod_pairLocalFactor_tendsto_zero`).

## Status of the two residues, honestly

* `DelangeKernelMean z` — `Σ_{n≤N} h_z(n)/n → 0`.  This is the truncated sum, not the Euler
  product; `prod_delangeLocal_tendsto_zero` is the corresponding product statement and the gap
  between them is a Wirsing/Levin–Fainleib-type comparison.
* `DelangeKernelTail z` — `(1/N) Σ_{n≤N} |h_z(n)| → 0`, i.e.
  `Σ_{n≤N} μ²(n) |z−1|^{ω(n)} = o(N)`.  **This is TRUE exactly when `|z − 1| < 1`** (then
  `w^{ω(n)} ≤ w^K + [ω(n) ≤ K]` and `#{n ≤ N : ω(n) ≤ K} = o(N)` by Turán–Kubilius
  (`TwoPointTuranKubilius.lean`) closes it), and FALSE in general — for `|z−1| ≥ 1` the kernel sum
  is `≫ N`, and the route must be replaced by Halász / Selberg–Delange with the zero-free region
  (`src/PNTPort/ZetaBounds.lean`: `ZetaNoZerosOn1Line`, `ZetaZeroFree9`).

So the decomposition is honest about where it stops: `|z−1| < 1` (i.e. `‖t‖_{ℝ/ℤ} < 1/6`) is
elementary from here; the rest needs the contour machinery that `PNTPort` provides.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-! ### The Dirichlet kernel of `z^ω` -/

/-- `h_z = μ * z^ω`: supported on squarefree `n`, where it is `(z−1)^{ω(n)}`. -/
noncomputable def delangeKernel (z : ℂ) (n : ℕ) : ℂ :=
  if Squarefree n then (z - 1) ^ omegaNat n else 0

lemma norm_delangeKernel (z : ℂ) (n : ℕ) :
    ‖delangeKernel z n‖ = if Squarefree n then ‖z - 1‖ ^ omegaNat n else 0 := by
  unfold delangeKernel
  split <;> simp

/-- **`z^ω = 1 * h_z`.**  The squarefree divisors of `m` are the products of subsets of its prime
factors, so the divisor sum of `h_z` is the powerset expansion of `((z−1)+1)^{ω(m)}`. -/
theorem sum_delangeKernel_divisors (z : ℂ) (m : ℕ) (hm : m ≠ 0) :
    ∑ n ∈ m.divisors, delangeKernel z n = z ^ omegaNat m := by
  classical
  have h1 : ∑ n ∈ m.divisors, delangeKernel z n
      = ∑ n ∈ m.divisors with Squarefree n, (z - 1) ^ omegaNat n := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun n _ => by rw [delangeKernel]
  rw [h1, Nat.sum_divisors_filter_squarefree hm]
  have hbridge : (UniqueFactorizationMonoid.normalizedFactors m).toFinset = m.primeFactors := by
    simp [Nat.factors_eq]
  rw [hbridge]
  have hterm : ∀ i ∈ m.primeFactors.powerset,
      (z - 1) ^ omegaNat i.val.prod = (z - 1) ^ i.card := by
    intro i hi
    have hsub : i ⊆ m.primeFactors := Finset.mem_powerset.mp hi
    have hprime : ∀ p ∈ i, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)
    have hprod : i.val.prod = ∏ p ∈ i, p := by
      rw [Finset.prod_eq_multiset_prod]
      simp
    rw [omegaNat, hprod, Nat.primeFactors_prod hprime]
  rw [Finset.sum_congr rfl hterm]
  simpa [omegaNat] using
    (Finset.prod_add (fun _ => (z - 1)) (fun _ => (1 : ℂ)) m.primeFactors).symm

/-- **Hyperbola summation.**  The exact identity the elementary route runs on. -/
theorem sum_zpow_omega_eq (z : ℂ) (N : ℕ) :
    ∑ m ∈ Finset.Ioc 0 N, z ^ omegaNat m
      = ∑ n ∈ Finset.Ioc 0 N, delangeKernel z n * ((N / n : ℕ) : ℂ) := by
  classical
  have hdiv : ∀ m ∈ Finset.Ioc 0 N, ∑ n ∈ m.divisors, delangeKernel z n
      = ∑ n ∈ Finset.Ioc 0 N, if n ∣ m then delangeKernel z n else 0 := by
    intro m hm
    simp only [Finset.mem_Ioc] at hm
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext n
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hdvd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd hm.1, le_trans (Nat.le_of_dvd hm.1 hdvd) hm.2⟩, hdvd⟩
    · rintro ⟨_, hdvd⟩
      exact ⟨hdvd, by omega⟩
  have hleft : ∑ m ∈ Finset.Ioc 0 N, z ^ omegaNat m
      = ∑ m ∈ Finset.Ioc 0 N, ∑ n ∈ m.divisors, delangeKernel z n := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : m ≠ 0 := by
      simp only [Finset.mem_Ioc] at hm; omega
    rw [sum_delangeKernel_divisors z m hm0]
  rw [hleft, Finset.sum_congr rfl hdiv, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul,
    mul_comm]

/-! ### The Euler product of the kernel decays -/

/-- The local factor of `h_z` at `p`, to first order: `1 + (z−1)/p`. -/
noncomputable def delangeLocal (z : ℂ) (p : ℕ) : ℂ := 1 + (z - 1) / (p : ℂ)

/-- **An exact identity.**  For `‖z‖ = 1`, `‖1 + (z−1)r‖² = 1 − 2(1 − Re z)(r − r²)`. -/
lemma norm_delangeLocal_sq (z : ℂ) (hz : ‖z‖ = 1) (r : ℝ) :
    ‖1 + (z - 1) * (r : ℂ)‖ ^ 2 = 1 - 2 * (1 - z.re) * (r - r ^ 2) := by
  have hn : Complex.normSq z = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [hz] at h; simpa using h
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.ofReal_re, Complex.ofReal_im]
  simp only [Complex.normSq_apply] at hn
  ring_nf
  nlinarith [hn]

/-- `Re z < 1` whenever `‖z‖ = 1` and `z ≠ 1`. -/
lemma re_lt_one_of_norm_one (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) : z.re < 1 := by
  have hn : z.re * z.re + z.im * z.im = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [hz] at h
    simp only [Complex.normSq_apply] at h
    nlinarith [h]
  rcases lt_or_ge z.re 1 with h | h
  · exact h
  · exfalso
    have habs : |z.re| ≤ 1 := by rw [← hz]; exact Complex.abs_re_le_norm z
    have hre : z.re = 1 := by have := (abs_le.mp habs).2; linarith
    have him : z.im = 0 := by nlinarith [hn, hre]
    exact hz1 (Complex.ext (by simpa using hre) (by simpa using him))

lemma re_le_one_of_norm_one (z : ℂ) (hz : ‖z‖ = 1) : z.re ≤ 1 := by
  have h := Complex.abs_re_le_norm z
  rw [hz] at h
  exact le_trans (le_abs_self _) h

lemma norm_delangeLocal_le_one (z : ℂ) (hz : ‖z‖ = 1) {p : ℕ} (hp : 0 < p) :
    ‖delangeLocal z p‖ ≤ 1 := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hone : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have heq : delangeLocal z p = 1 + (z - 1) * (((1 : ℝ) / p : ℝ) : ℂ) := by
    rw [delangeLocal]; push_cast; rw [div_eq_mul_inv, one_div]
  have hr : (0 : ℝ) < 1 / (p : ℝ) := by positivity
  have hr1 : (1 : ℝ) / (p : ℝ) ≤ 1 := by rw [div_le_one hpR]; exact hone
  have hrr : (0 : ℝ) ≤ 1 / (p : ℝ) - (1 / (p : ℝ)) ^ 2 := by nlinarith [hr, hr1]
  have hre := re_le_one_of_norm_one z hz
  have hsq := norm_delangeLocal_sq z hz (1 / (p : ℝ))
  have hAnn : 0 ≤ ‖1 + (z - 1) * (((1 : ℝ) / p : ℝ) : ℂ)‖ := norm_nonneg _
  have hA2 : ‖1 + (z - 1) * (((1 : ℝ) / p : ℝ) : ℂ)‖ ^ 2 ≤ 1 := by
    rw [hsq]; nlinarith [hrr, hre]
  rw [heq]
  nlinarith [hA2, hAnn]

lemma norm_delangeLocal_le (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) {p : ℕ} (hp : 2 ≤ p) :
    ‖delangeLocal z p‖ ≤ 1 - ((1 - z.re) / 2) / p := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have ha : 0 < 1 - z.re := by linarith [re_lt_one_of_norm_one z hz hz1]
  have ha2 : 1 - z.re ≤ 2 := by
    have h := Complex.abs_re_le_norm z
    rw [hz] at h
    linarith [(abs_le.mp h).1]
  have heq : delangeLocal z p = 1 + (z - 1) * (((1 : ℝ) / p : ℝ) : ℂ) := by
    rw [delangeLocal]; push_cast; rw [div_eq_mul_inv, one_div]
  have hsq := norm_delangeLocal_sq z hz (1 / (p : ℝ))
  set A := ‖1 + (z - 1) * (((1 : ℝ) / p : ℝ) : ℂ)‖ with hA
  have hAnn : 0 ≤ A := norm_nonneg _
  have hkey : (1 : ℝ) / (p : ℝ) - (1 / (p : ℝ)) ^ 2 - 1 / (2 * (p : ℝ))
      = ((p : ℝ) - 2) / (2 * (p : ℝ) ^ 2) := by
    field_simp
    ring
  have hrr : (1 : ℝ) / (2 * (p : ℝ)) ≤ 1 / (p : ℝ) - (1 / (p : ℝ)) ^ 2 := by
    have hnn : (0 : ℝ) ≤ ((p : ℝ) - 2) / (2 * (p : ℝ) ^ 2) := by
      apply div_nonneg (by linarith) (by positivity)
    linarith [hkey, hnn]
  have hA2 : A ^ 2 ≤ 1 - (1 - z.re) / (p : ℝ) := by
    rw [hA, hsq]
    have hid : 2 * (1 - z.re) * (1 / (2 * (p : ℝ))) = (1 - z.re) / (p : ℝ) := by field_simp
    nlinarith [hrr, ha, hid]
  have hB : (0 : ℝ) ≤ 1 - ((1 - z.re) / 2) / (p : ℝ) := by
    rw [sub_nonneg, div_le_one hppos]
    linarith [ha2, hpR]
  have hBsq : (1 - ((1 - z.re) / 2) / (p : ℝ)) ^ 2
      = 1 - (1 - z.re) / (p : ℝ) + ((1 - z.re) / (2 * (p : ℝ))) ^ 2 := by
    field_simp
    ring
  rw [heq]
  nlinarith [hA2, hAnn, hB, hBsq, sq_nonneg ((1 - z.re) / (2 * (p : ℝ)))]

/-- **The kernel's Euler product decays.**  Mertens plus the exact norm identity. -/
theorem prod_delangeLocal_tendsto_zero (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (fun P => ‖∏ p ∈ primesLe P, delangeLocal z p‖) atTop (𝓝 0) := by
  refine prod_tendsto_zero_of_norm_le (delangeLocal z)
    (fun p hp => norm_delangeLocal_le_one z hz hp)
    (c := (1 - z.re) / 2) (by linarith [re_lt_one_of_norm_one z hz hz1]) ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with p hp _
  exact norm_delangeLocal_le z hz hz1 hp

/-! ### The two analytic residues, named -/

/-- The truncated kernel mean: `Σ_{n ≤ N} h_z(n)/n → 0`.  The corresponding *Euler product*
statement is the theorem `prod_delangeLocal_tendsto_zero`; the gap is a Wirsing/Levin–Fainleib
comparison between a truncated multiplicative sum and its product. -/
def DelangeKernelMean (z : ℂ) : Prop :=
  Tendsto (fun N : ℕ => ∑ n ∈ Finset.Ioc 0 N, delangeKernel z n / (n : ℂ)) atTop (𝓝 0)

/-- The kernel's `ℓ¹` mass is `o(N)`: `Σ_{n ≤ N} μ²(n) |z−1|^{ω(n)} = o(N)`.

**TRUE exactly when `‖z − 1‖ < 1`**, and then elementary: `w^{ω(n)} ≤ w^K + [ω(n) ≤ K]` and
`#{n ≤ N : ω(n) ≤ K} = o(N)` by Turán–Kubilius (`turanKubilius`,
`TwoPointTuranKubilius.lean`).  For `‖z − 1‖ ≥ 1` it FAILS and the elementary route must be
replaced by Halász / Selberg–Delange over the zero-free region (`PNTPort.ZetaBounds`). -/
def DelangeKernelTail (z : ℂ) : Prop :=
  Tendsto (fun N : ℕ => (∑ n ∈ Finset.Ioc 0 N, ‖delangeKernel z n‖) / (N : ℝ)) atTop (𝓝 0)

/-- **THE ELEMENTARY ASSEMBLY.**  `DelangeMean` from the two kernel residues.

`⌊N/n⌋/N = 1/n − δ_n/N` with `δ_n ∈ [0,1)`, so the hyperbola identity `sum_zpow_omega_eq` gives
`|E_{m≤N} z^{ω(m)}| ≤ ‖Σ_{n≤N} h_z(n)/n‖ + (1/N) Σ_{n≤N} ‖h_z(n)‖`. -/
theorem delangeMean_of_kernel (t : ℝ) (hM : DelangeKernelMean (phase t))
    (hT : DelangeKernelTail (phase t)) : DelangeMean t := by
  classical
  set z : ℂ := phase t with hzdef
  have hmaj : Tendsto (fun N : ℕ =>
      ‖∑ n ∈ Finset.Ioc 0 N, delangeKernel z n / (n : ℂ)‖
        + (∑ n ∈ Finset.Ioc 0 N, ‖delangeKernel z n‖) / (N : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => ‖∑ n ∈ Finset.Ioc 0 N, delangeKernel z n / (n : ℂ)‖)
        atTop (𝓝 0) := by simpa using hM.norm
    simpa using h1.add hT
  rw [DelangeMean, tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _) ?_ hmaj
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNc : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- the fractional part of `N/n`
  set frac : ℕ → ℝ := fun n => (N : ℝ) / n - ((N / n : ℕ) : ℝ) with hfracdef
  have hidx : ∑ n ∈ Finset.range N, phase (t * (omegaNat (n + 1) : ℝ))
      = ∑ m ∈ Finset.Ioc 0 N, z ^ omegaNat m := by
    have hIoc : Finset.Ioc 0 N = Finset.Ico 1 (N + 1) := by
      ext m; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [hIoc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show 1 + n = n + 1 by omega, hzdef, ← phase_omegaNat_pow]
  have hptwise : ∀ n ∈ Finset.Ioc 0 N,
      delangeKernel z n * ((N / n : ℕ) : ℂ) / (N : ℂ)
        = delangeKernel z n / (n : ℂ) - delangeKernel z n * ((frac n : ℝ) : ℂ) / (N : ℂ) := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hcast : ((frac n : ℝ) : ℂ) = (N : ℂ) / (n : ℂ) - ((N / n : ℕ) : ℂ) := by
      simp only [hfracdef]; push_cast; ring
    rw [hcast]
    field_simp
    ring
  have hfracle : ∀ n ∈ Finset.Ioc 0 N, ‖((frac n : ℝ) : ℂ)‖ ≤ 1 := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    have h1 : ((N / n : ℕ) : ℝ) ≤ (N : ℝ) / n := cast_div_le N n
    have h2 : (N : ℝ) / n - 1 ≤ ((N / n : ℕ) : ℝ) := sub_one_le_cast_div N n hn.1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    simp only [hfracdef]
    constructor <;> linarith
  have hmean : fullMean (fun n => phase (t * (omegaNat (n + 1) : ℝ))) N
      = (∑ n ∈ Finset.Ioc 0 N, delangeKernel z n / (n : ℂ))
        - (∑ n ∈ Finset.Ioc 0 N, delangeKernel z n * ((frac n : ℝ) : ℂ)) / (N : ℂ) := by
    rw [fullMean, hidx, sum_zpow_omega_eq, Finset.sum_div, Finset.sum_congr rfl hptwise,
      Finset.sum_sub_distrib, ← Finset.sum_div]
  rw [hmean]
  have hB : ‖∑ n ∈ Finset.Ioc 0 N, delangeKernel z n * ((frac n : ℝ) : ℂ)‖
      ≤ ∑ n ∈ Finset.Ioc 0 N, ‖delangeKernel z n‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n hn => ?_)
    rw [norm_mul]
    nlinarith [hfracle n hn, norm_nonneg (delangeKernel z n),
      norm_nonneg ((frac n : ℝ) : ℂ)]
  calc ‖(∑ n ∈ Finset.Ioc 0 N, delangeKernel z n / (n : ℂ))
        - (∑ n ∈ Finset.Ioc 0 N, delangeKernel z n * ((frac n : ℝ) : ℂ)) / (N : ℂ)‖
      ≤ ‖∑ n ∈ Finset.Ioc 0 N, delangeKernel z n / (n : ℂ)‖
        + ‖(∑ n ∈ Finset.Ioc 0 N, delangeKernel z n * ((frac n : ℝ) : ℂ)) / (N : ℂ)‖ :=
        norm_sub_le _ _
    _ ≤ ‖∑ n ∈ Finset.Ioc 0 N, delangeKernel z n / (n : ℂ)‖
        + (∑ n ∈ Finset.Ioc 0 N, ‖delangeKernel z n‖) / (N : ℝ) := by
        rw [norm_div, Complex.norm_natCast]
        have : ‖∑ n ∈ Finset.Ioc 0 N, delangeKernel z n * ((frac n : ℝ) : ℂ)‖ / (N : ℝ)
            ≤ (∑ n ∈ Finset.Ioc 0 N, ‖delangeKernel z n‖) / (N : ℝ) :=
          div_le_div_of_nonneg_right hB hNR.le
        linarith [this]

end NormalNumbers.CastingOut
