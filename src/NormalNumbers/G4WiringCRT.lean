import NormalNumbers.WeylCriterion
import NormalNumbers.PrimeLambertTail
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
uses; its arithmetic identity is recorded in the design doc, not asserted here.

⚠️ 2026-09-20: the quantifier order is `∀ᶠ N, ∀ J` (uniform in `J`), not `∀ J, ∀ᶠ N`.  This is the
intended reading of KB verdict §2f (the relative error `C / log N` has no `J`-dependence) and it is
*required*: with `∀ J, ∀ᶠ N` the `N`-threshold `n_J` may grow arbitrarily fast in `J`, so no
schedule `J_N → ∞` fast enough for the L1 tail (`J_N ≳ log₂ log₂ N`) can be certified.  The
kickoff authorised exactly this strengthening. -/
def CRTConstant (h : ℤ) : Prop :=
  ∃ (c : ℕ → ℂ) (B C : ℝ), (∀ J, ‖c J‖ ≤ B) ∧ ∀ᶠ N : ℕ in atTop, ∀ J : ℕ,
    ‖fullWindowMean N J h - c J * ∏ j ∈ Finset.Icc 1 J, fullSiteMean N h j‖
      ≤ C / Real.log N * ∏ j ∈ Finset.Icc 1 J, ‖fullSiteMean N h j‖

/-- **Frozen input** (Delange–Wirsing–Halász, classical): a nontrivial one-site mean vanishes. -/
def SiteDecayFull : Prop :=
  ∀ (h : ℤ) (j : ℕ), 1 ≤ j → ¬ (∃ m : ℤ, (h : ℝ) / (4 : ℝ) ^ j = m) →
    Tendsto (fun N => ‖fullSiteMean N h j‖) atTop (𝓝 0)

/-- Window schedule: `J_N = ⌈log₂ log₂ N⌉ + 1`; any `J_N → ∞` with `4^{-J_N} log N → 0` works. -/
def windowJ (N : ℕ) : ℕ := Nat.log 2 (Nat.log 2 N) + 1

/-! ### Elementary facts about `ePhase` and the site means -/

lemma norm_ePhase (x : ℝ) : ‖ePhase x‖ = 1 := by
  have hx : ePhase x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    unfold ePhase; congr 1; push_cast; ring
  rw [hx]; exact Complex.norm_exp_ofReal_mul_I _

lemma ePhase_add_int (x : ℝ) (w : ℤ) : ePhase (x + w) = ePhase x := by
  unfold ePhase
  have hx : (2 * Real.pi * Complex.I * ((x + w : ℝ) : ℂ))
      = 2 * Real.pi * Complex.I * (x : ℂ) + (w : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [hx, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma ePhase_add (x y : ℝ) : ePhase (x + y) = ePhase x * ePhase y := by
  unfold ePhase; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma ePhase_eq_e (x : ℝ) : ePhase x = NormalNumbers.PrimeLambert.e x := by
  unfold ePhase NormalNumbers.PrimeLambert.e; congr 1; push_cast; ring

/-- `‖e(a) − e(b)‖ ≤ 4π|a − b|`. -/
lemma norm_ePhase_sub (a b : ℝ) : ‖ePhase a - ePhase b‖ ≤ 4 * Real.pi * |a - b| := by
  have hsplit : ePhase a - ePhase b = ePhase b * (ePhase (a - b) - 1) := by
    rw [mul_sub, ← ePhase_add, mul_one]
    congr 2
    ring
  rw [hsplit, norm_mul, norm_ePhase, one_mul, ePhase_eq_e]
  exact NormalNumbers.PrimeLambert.norm_e_sub_one_le _

lemma norm_fullSiteMean_le_one (N : ℕ) (h : ℤ) (j : ℕ) : ‖fullSiteMean N h j‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [fullSiteMean]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [fullSiteMean, norm_div, Complex.norm_natCast, div_le_one hNR]
  calc ‖∑ n ∈ Finset.Ico N (2 * N), ePhase (h * omegaR (n + j) / (4 : ℝ) ^ j)‖
      ≤ ∑ n ∈ Finset.Ico N (2 * N), ‖ePhase (h * omegaR (n + j) / (4 : ℝ) ^ j)‖ :=
        norm_sum_le _ _
    _ = ((Finset.Ico N (2 * N)).card : ℝ) := by
        rw [Finset.sum_congr rfl (fun n _ => norm_ePhase _), Finset.sum_const, nsmul_eq_mul,
          mul_one]
    _ = (N : ℝ) := by rw [Nat.card_Ico]; congr 1; omega

lemma tendsto_windowJ : Tendsto windowJ atTop atTop := by
  have hlog : Tendsto (fun N : ℕ => Nat.log 2 N) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨2 ^ b, fun a ha => Nat.le_log_of_pow_le (by norm_num) ha⟩)
  exact tendsto_atTop_atTop.mpr (fun b =>
    ⟨2 ^ (2 ^ b), fun a ha => by
      have h1 : 2 ^ b ≤ Nat.log 2 a := Nat.le_log_of_pow_le (by norm_num) ha
      have h2 : b ≤ Nat.log 2 (Nat.log 2 a) := Nat.le_log_of_pow_le (by norm_num) h1
      simpa [windowJ] using Nat.le_succ_of_le h2⟩)

/-! ### L1: the tail lemma, elementary -/

/-- `|tailB 4 n − truncTail J n| ≤ (log₂(n + J + 2) + J + 3) / 4^J`. -/
theorem tail_error_le (J n : ℕ) :
    |TWeight.omega.tailB 4 n - truncTail J n|
      ≤ ((Nat.log 2 (n + J + 2) : ℝ) + J + 3) / (4 : ℝ) ^ J := by
  set A : ℝ := (Nat.log 2 (n + J + 2) : ℝ) with hA
  have hsum : Summable (fun i : ℕ => omegaR (n + i + 1) / (4 : ℝ) ^ (i + 1)) := by
    have h := TWeight.summable_tailB (W := TWeight.omega) (b := 4) (by norm_num) n
    exact h.congr (fun i => by rw [TWeight.omega_wN]; norm_num)
  have hsplit := hsum.sum_add_tsum_nat_add J
  have hdiff : TWeight.omega.tailB 4 n - truncTail J n
      = ∑' t : ℕ, omegaR (n + (t + J) + 1) / (4 : ℝ) ^ (t + J + 1) := by
    have htB : TWeight.omega.tailB 4 n = ∑' i : ℕ, omegaR (n + i + 1) / (4 : ℝ) ^ (i + 1) := by
      rw [TWeight.tailB]; exact tsum_congr fun i => by rw [TWeight.omega_wN]; norm_num
    rw [htB, truncTail, ← hsplit]
    ring
  -- majorant: term ≤ (1/4^J) * ((A + J + t) / 2^(t+1))
  have hterm : ∀ t : ℕ, omegaR (n + (t + J) + 1) / (4 : ℝ) ^ (t + J + 1)
      ≤ (1 / (4 : ℝ) ^ J) * ((A + J + t) / 2 ^ (t + 1)) := by
    intro t
    rw [show n + (t + J) + 1 = n + J + t + 1 from by ring]
    have h1 : omegaR (n + J + t + 1) ≤ (Nat.log 2 (n + J + t + 1) : ℝ) := by
      exact_mod_cast omegaR_le_log (n + J + t + 1)
    have h2 : (Nat.log 2 (n + J + t + 1) : ℝ) ≤ A + t := by
      have := log_add_le (n + J) t
      have hmono : Nat.log 2 (n + J + 1) ≤ Nat.log 2 (n + J + 2) :=
        Nat.log_mono_right (by omega)
      have : Nat.log 2 (n + J + t + 1) ≤ Nat.log 2 (n + J + 2) + t := by omega
      rw [hA]; exact_mod_cast this
    have hnum : omegaR (n + J + t + 1) ≤ A + J + t := by
      have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
      linarith
    have hden : (2 : ℝ) ^ (t + 1) * 4 ^ J ≤ 4 ^ (t + J + 1) := by
      have : (2 : ℝ) ^ (t + 1) ≤ 4 ^ (t + 1) := by
        gcongr <;> norm_num
      calc (2 : ℝ) ^ (t + 1) * 4 ^ J ≤ 4 ^ (t + 1) * 4 ^ J := by gcongr
        _ = 4 ^ (t + J + 1) := by rw [← pow_add]; ring_nf
    have hnn : (0 : ℝ) ≤ A + J + t := by
      have : (0 : ℝ) ≤ A := by rw [hA]; positivity
      have : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
      have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
      positivity
    have hpos1 : (0:ℝ) < 4 ^ (t + J + 1) := by positivity
    have hpos2 : (0:ℝ) < 2 ^ (t + 1) * (4:ℝ) ^ J := by positivity
    rw [one_div, inv_mul_eq_div, div_div, div_le_div_iff₀ hpos1 hpos2]
    nlinarith [hnum, hden, hnn, omegaR_nonneg (n + J + t + 1), hpos1.le, hpos2.le]
  have hAJ : (0 : ℝ) ≤ A + J := by
    have h1 : (0 : ℝ) ≤ A := by rw [hA]; positivity
    have h2 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
    linarith
  have hmajsum0 : Summable (fun t : ℕ => ((A + J) + (t : ℝ)) / 2 ^ (t + 1)) := by
    have := (summable_geom_shift.mul_left (A + J)).add summable_i_geom
    refine this.congr (fun i => ?_); ring
  have hmajsum : Summable (fun t : ℕ => (1 / (4 : ℝ) ^ J) * (((A + J) + (t : ℝ)) / 2 ^ (t + 1))) :=
    hmajsum0.mul_left _
  have hmaj : ∑' t : ℕ, ((A + J) + (t : ℝ)) / 2 ^ (t + 1) = A + J + 1 := by
    have h := tsum_majorant (A + J) 0
    simpa using h
  have hLsum : Summable (fun t : ℕ => omegaR (n + (t + J) + 1) / (4 : ℝ) ^ (t + J + 1)) := by
    have := (summable_nat_add_iff J).mpr hsum
    exact this.congr (fun t => by rw [show t + J + 1 = t + J + 1 from rfl])
  have hterm' : ∀ t : ℕ, omegaR (n + (t + J) + 1) / (4 : ℝ) ^ (t + J + 1)
      ≤ (1 / (4 : ℝ) ^ J) * (((A + J) + (t : ℝ)) / 2 ^ (t + 1)) := by
    intro t; have := hterm t; linarith [this]
  rw [hdiff, abs_of_nonneg (tsum_nonneg (fun t => by
    have := omegaR_nonneg (n + (t + J) + 1); positivity))]
  calc ∑' t : ℕ, omegaR (n + (t + J) + 1) / (4 : ℝ) ^ (t + J + 1)
      ≤ ∑' t : ℕ, (1 / (4 : ℝ) ^ J) * (((A + J) + (t : ℝ)) / 2 ^ (t + 1)) :=
        Summable.tsum_le_tsum hterm' hLsum hmajsum
    _ = (1 / (4 : ℝ) ^ J) * (A + J + 1) := by rw [tsum_mul_left, hmaj]
    _ ≤ (A + J + 3) / (4 : ℝ) ^ J := by
        rw [one_div, inv_mul_eq_div]
        gcongr
        linarith

/-- The tail error is `o(1)` uniformly on `[N, 2N)` along the schedule `windowJ`. -/
theorem tail_error_uniform :
    Tendsto (fun N : ℕ => ((Nat.log 2 (2 * N + windowJ N + 2) : ℝ) + windowJ N + 3)
      / (4 : ℝ) ^ (windowJ N)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Nat.log 2 N) atTop atTop := by
    refine tendsto_atTop_atTop.mpr (fun b => ⟨2 ^ b, fun a ha => ?_⟩)
    exact Nat.le_log_of_pow_le (by norm_num) ha
  have hgtends : Tendsto (fun L : ℕ => 4 / (L : ℝ)) atTop (𝓝 0) := by
    have hL : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    exact Tendsto.div_atTop tendsto_const_nhds hL
  have hcomp := hgtends.comp hlog
  refine squeeze_zero' (Eventually.of_forall (fun N => by positivity)) ?_ hcomp
  filter_upwards [eventually_ge_atTop 16] with N hN
  set L := Nat.log 2 N with hLdef
  set M := Nat.log 2 L with hMdef
  have hN0 : N ≠ 0 := by omega
  have hL4 : 4 ≤ L := Nat.le_log_of_pow_le (by norm_num) (by omega : 2 ^ 4 ≤ N)
  have hJ : windowJ N = M + 1 := rfl
  -- numerator bound
  have hJle : windowJ N ≤ L := by
    have : M < L := Nat.log_lt_self 2 (by omega)
    omega
  have hnum : (Nat.log 2 (2 * N + windowJ N + 2) : ℝ) + windowJ N + 3 ≤ 2 * (L : ℝ) + 5 := by
    have harg : 2 * N + windowJ N + 2 ≤ 4 * N := by
      have : windowJ N ≤ L := hJle
      have hLN : L ≤ N := Nat.log_le_self 2 N
      omega
    have h1 : Nat.log 2 (2 * N + windowJ N + 2) ≤ Nat.log 2 (4 * N) := Nat.log_mono_right harg
    have h2 : Nat.log 2 (4 * N) ≤ L + 2 := by
      have hNlt : N < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
      have : 4 * N < 2 ^ (L + 3) := by
        calc 4 * N < 4 * 2 ^ (L + 1) := by omega
          _ = 2 ^ (L + 3) := by rw [show L + 3 = 2 + (L + 1) by ring, pow_add]; ring
      have := Nat.log_lt_of_lt_pow (by omega : 4 * N ≠ 0) this
      omega
    have : Nat.log 2 (2 * N + windowJ N + 2) + windowJ N + 3 ≤ 2 * L + 5 := by omega
    exact_mod_cast this
  -- denominator bound
  have hden : ((L : ℝ)) ^ 2 ≤ (4 : ℝ) ^ (windowJ N) := by
    have hpow : L < 2 ^ (M + 1) := Nat.lt_pow_succ_log_self (by norm_num) L
    have : (L : ℝ) ^ 2 ≤ ((2 : ℝ) ^ (M + 1)) ^ 2 := by
      have : (L : ℝ) ≤ (2 : ℝ) ^ (M + 1) := by exact_mod_cast hpow.le
      have h0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
      nlinarith
    calc (L : ℝ) ^ 2 ≤ ((2 : ℝ) ^ (M + 1)) ^ 2 := this
      _ = (4 : ℝ) ^ (M + 1) := by
          rw [← pow_mul, mul_comm (M + 1) 2, pow_mul]; norm_num
      _ = (4 : ℝ) ^ (windowJ N) := by rw [hJ]
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hdenpos : (0 : ℝ) < (4 : ℝ) ^ (windowJ N) := by positivity
  have hL4R : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL4
  calc ((Nat.log 2 (2 * N + windowJ N + 2) : ℝ) + windowJ N + 3) / (4 : ℝ) ^ (windowJ N)
      ≤ (2 * (L : ℝ) + 5) / (L : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ hdenpos (by positivity)]
        have hn0 : (0 : ℝ) ≤ (Nat.log 2 (2 * N + windowJ N + 2) : ℝ) + windowJ N + 3 := by
          positivity
        nlinarith [hnum, hden, hn0, hdenpos.le]
    _ ≤ 4 / (L : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) hLpos]
        nlinarith
    _ = ((fun L : ℕ => 4 / (L : ℝ)) ∘ fun N : ℕ => Nat.log 2 N) N := rfl

/-! ### Assembly -/

/-- The orbit of `G₄` is the tail mod one (repo: `coe_tailB` + `lambert_omega`). -/
theorem orbit_eq_fract_tailB (n : ℕ) :
    orbit 4 (primeLambertAtBase 4) n = Int.fract (TWeight.omega.tailB 4 n) := by
  rw [TWeight.tailB_eq (W := TWeight.omega) (b := 4) (by norm_num) n,
    TWeight.lambert_omega (b := 4) (by norm_num)]
  rw [Int.fract_sub_natCast, orbit, mul_comm]

/-- For every `h ≠ 0` some site `j ≤ windowJ N` (eventually) has `h 4^{-j} ∉ ℤ`, and the product
of site means then tends to `0`; with the law, the window mean tends to `0`. -/
theorem fullWindowMean_tendsto_zero (hLaw : ∀ h : ℤ, h ≠ 0 → CRTConstant h)
    (hSite : SiteDecayFull) (h : ℤ) (hh : h ≠ 0) :
    Tendsto (fun N => fullWindowMean N (windowJ N) h) atTop (𝓝 0) := by
  obtain ⟨c, B, C, hcB, hlaw⟩ := hLaw h hh
  set j₀ : ℕ := h.natAbs + 1 with hj₀def
  have hj₀1 : 1 ≤ j₀ := by omega
  have hnotint : ¬ ∃ m : ℤ, (h : ℝ) / (4 : ℝ) ^ j₀ = m := by
    rintro ⟨m, hm⟩
    have h4 : ((4 : ℝ) ^ j₀) ≠ 0 := by positivity
    have hR : (h : ℝ) = (m : ℝ) * (4 : ℝ) ^ j₀ := by field_simp at hm; linarith [hm]
    have hZ : h = m * 4 ^ j₀ := by exact_mod_cast hR
    have hm0 : m ≠ 0 := by rintro rfl; simp at hZ; exact hh hZ
    have hlb : (4 : ℤ) ^ j₀ ≤ |h| := by
      rw [hZ, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 4 ^ j₀)]
      have : 1 ≤ |m| := Int.one_le_abs (by omega)
      nlinarith [abs_nonneg m, (by positivity : (0 : ℤ) < 4 ^ j₀)]
    have hub : h.natAbs < 4 ^ j₀ := by
      calc h.natAbs < 2 ^ h.natAbs := Nat.lt_two_pow_self
        _ ≤ 4 ^ (h.natAbs + 1) := by
            calc 2 ^ h.natAbs ≤ 4 ^ h.natAbs := Nat.pow_le_pow_left (by norm_num) _
              _ ≤ 4 ^ (h.natAbs + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have habs : |h| = (h.natAbs : ℤ) := Int.abs_eq_natAbs h
    have : ((4 : ℤ) ^ j₀) ≤ (h.natAbs : ℤ) := by rw [habs] at hlb; exact hlb
    have hub' : ((h.natAbs : ℤ)) < 4 ^ j₀ := by exact_mod_cast hub
    omega
  have hsite := hSite h j₀ hj₀1 hnotint
  have hBnn : (0 : ℝ) ≤ B := le_trans (norm_nonneg _) (hcB 0)
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall (fun N => norm_nonneg _))
    (g := fun N => (B + |C|) * ‖fullSiteMean N h j₀‖) ?_ (by simpa using hsite.const_mul (B + |C|))
  filter_upwards [hlaw, tendsto_windowJ.eventually_ge_atTop j₀, eventually_ge_atTop 3]
    with N hN hNJ hN3
  set J := windowJ N with hJ
  set P : ℝ := ∏ j ∈ Finset.Icc 1 J, ‖fullSiteMean N h j‖ with hP
  have hPnn : 0 ≤ P := Finset.prod_nonneg (fun j _ => norm_nonneg _)
  have hmem : j₀ ∈ Finset.Icc 1 J := Finset.mem_Icc.mpr ⟨hj₀1, hNJ⟩
  have hPle : P ≤ ‖fullSiteMean N h j₀‖ := by
    rw [hP, ← Finset.prod_erase_mul _ _ hmem]
    have h1 : (∏ j ∈ (Finset.Icc 1 J).erase j₀, ‖fullSiteMean N h j‖) ≤ 1 :=
      Finset.prod_le_one (fun j _ => norm_nonneg _) (fun j _ => norm_fullSiteMean_le_one _ _ _)
    nlinarith [norm_nonneg (fullSiteMean N h j₀),
      Finset.prod_nonneg (fun j (_ : j ∈ (Finset.Icc 1 J).erase j₀) => norm_nonneg
        (fullSiteMean N h j))]
  have hN3R : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hlogN : (1 : ℝ) ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hCbound : C / Real.log N ≤ |C| := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [le_abs_self C, abs_nonneg C]
  have hprodnorm : ‖c J * ∏ j ∈ Finset.Icc 1 J, fullSiteMean N h j‖ ≤ B * P := by
    rw [norm_mul, norm_prod]
    exact mul_le_mul (hcB J) le_rfl hPnn hBnn
  calc ‖fullWindowMean N J h‖
      ≤ ‖fullWindowMean N J h - c J * ∏ j ∈ Finset.Icc 1 J, fullSiteMean N h j‖
          + ‖c J * ∏ j ∈ Finset.Icc 1 J, fullSiteMean N h j‖ := by
        simpa using norm_add_le (fullWindowMean N J h
          - c J * ∏ j ∈ Finset.Icc 1 J, fullSiteMean N h j)
          (c J * ∏ j ∈ Finset.Icc 1 J, fullSiteMean N h j)
    _ ≤ C / Real.log N * P + B * P := by gcongr; exact hN J
    _ ≤ |C| * P + B * P := by nlinarith
    _ = (B + |C|) * P := by ring
    _ ≤ (B + |C|) * ‖fullSiteMean N h j₀‖ := by
        have : (0 : ℝ) ≤ B + |C| := by positivity
        nlinarith

/-- Dyadic Fourier means of the orbit vanish: tail error (L1) + `fullWindowMean_tendsto_zero`. -/
theorem dyadic_fourier_tendsto_zero (hLaw : ∀ h : ℤ, h ≠ 0 → CRTConstant h)
    (hSite : SiteDecayFull) (h : ℤ) (hh : h ≠ 0) :
    Tendsto (dyadicMean (fun n => ePhase (h * orbit 4 (primeLambertAtBase 4) n))) atTop (𝓝 0) := by
  set F : ℕ → ℂ := fun n => ePhase (h * orbit 4 (primeLambertAtBase 4) n) with hF
  have hFtail : ∀ n : ℕ, F n = ePhase (h * TWeight.omega.tailB 4 n) := by
    intro n
    have hshift : (h : ℝ) * Int.fract (TWeight.omega.tailB 4 n)
        = (h : ℝ) * TWeight.omega.tailB 4 n
          + ((-(h * ⌊TWeight.omega.tailB 4 n⌋) : ℤ) : ℝ) := by
      rw [Int.fract]; push_cast; ring
    rw [hF]
    simp only
    rw [orbit_eq_fract_tailB, hshift, ePhase_add_int]
  have hmain := fullWindowMean_tendsto_zero hLaw hSite h hh
  have hgoal : Tendsto (fun N => dyadicMean F N - fullWindowMean N (windowJ N) h) atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
      (g := fun N => 4 * Real.pi * |(h : ℝ)| *
        (((Nat.log 2 (2 * N + windowJ N + 2) : ℝ) + windowJ N + 3) / (4 : ℝ) ^ (windowJ N))) ?_
      (by simpa using tail_error_uniform.const_mul (4 * Real.pi * |(h : ℝ)|))
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    set J := windowJ N with hJ
    have hsub : dyadicMean F N - fullWindowMean N J h
        = (∑ n ∈ Finset.Ico N (2 * N),
            (ePhase (h * TWeight.omega.tailB 4 n) - ePhase (h * truncTail J n))) / N := by
      rw [dyadicMean, fullWindowMean, ← sub_div, ← Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_congr rfl (fun n _ => by rw [hFtail n])
    rw [hsub, norm_div, Complex.norm_natCast]
    rw [div_le_iff₀ hNR]
    calc ‖∑ n ∈ Finset.Ico N (2 * N),
            (ePhase (h * TWeight.omega.tailB 4 n) - ePhase (h * truncTail J n))‖
        ≤ ∑ n ∈ Finset.Ico N (2 * N),
            ‖ePhase (h * TWeight.omega.tailB 4 n) - ePhase (h * truncTail J n)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Ico N (2 * N), 4 * Real.pi * |(h : ℝ)| *
            (((Nat.log 2 (2 * N + J + 2) : ℝ) + J + 3) / (4 : ℝ) ^ J) := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          have hnlt : n < 2 * N := (Finset.mem_Ico.mp hn).2
          have hterr := tail_error_le J n
          have hmono : ((Nat.log 2 (n + J + 2) : ℝ) + J + 3) / (4 : ℝ) ^ J
              ≤ ((Nat.log 2 (2 * N + J + 2) : ℝ) + J + 3) / (4 : ℝ) ^ J := by
            have : Nat.log 2 (n + J + 2) ≤ Nat.log 2 (2 * N + J + 2) :=
              Nat.log_mono_right (by omega)
            have hc : (Nat.log 2 (n + J + 2) : ℝ) ≤ (Nat.log 2 (2 * N + J + 2) : ℝ) := by
              exact_mod_cast this
            gcongr
          calc ‖ePhase (h * TWeight.omega.tailB 4 n) - ePhase (h * truncTail J n)‖
              ≤ 4 * Real.pi * |(h : ℝ) * TWeight.omega.tailB 4 n - (h : ℝ) * truncTail J n| :=
                norm_ePhase_sub _ _
            _ = 4 * Real.pi * |(h : ℝ)| * |TWeight.omega.tailB 4 n - truncTail J n| := by
                rw [← mul_sub, abs_mul]; ring
            _ ≤ 4 * Real.pi * |(h : ℝ)| *
                  (((Nat.log 2 (n + J + 2) : ℝ) + J + 3) / (4 : ℝ) ^ J) := by
                have hpi := Real.pi_pos
                have : (0:ℝ) ≤ 4 * Real.pi * |(h : ℝ)| := by positivity
                exact mul_le_mul_of_nonneg_left hterr this
            _ ≤ 4 * Real.pi * |(h : ℝ)| *
                  (((Nat.log 2 (2 * N + J + 2) : ℝ) + J + 3) / (4 : ℝ) ^ J) := by
                have hpi := Real.pi_pos
                have h0 : (0:ℝ) ≤ 4 * Real.pi * |(h : ℝ)| := by positivity
                exact mul_le_mul_of_nonneg_left hmono h0
      _ = 4 * Real.pi * |(h : ℝ)| *
            (((Nat.log 2 (2 * N + J + 2) : ℝ) + J + 3) / (4 : ℝ) ^ J) * N := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico, show 2 * N - N = N from by omega]
          ring
  have := hmain.add hgoal
  simpa using this

/-- **Wiring theorem**: normality of `G₄` from the two frozen inputs. -/
theorem isNormal_G4_of_CRTConstant (hLaw : ∀ h : ℤ, h ≠ 0 → CRTConstant h)
    (hSite : SiteDecayFull) : IsNormal 4 (primeLambertAtBase 4) := by
  rw [isNormal_iff_equidistributed_orbit 4 (by norm_num)]
  refine equidistributed_of_weyl _ (orbit_mem_Ico 4 _) ?_
  intro h hh
  have hd := dyadic_fourier_tendsto_zero hLaw hSite h hh
  have hb : ∀ n : ℕ, ‖(fun n => ePhase (h * orbit 4 (primeLambertAtBase 4) n)) n‖ ≤ 1 :=
    fun n => le_of_eq (norm_ePhase _)
  have hpre := prefixMean_tendsto_zero_of_dyadic _ 1 hb hd
  have heq : fourierMean (orbit 4 (primeLambertAtBase 4)) h
      = prefixMean (fun n => ePhase (h * orbit 4 (primeLambertAtBase 4) n)) := by
    funext n
    rw [fourierMean, prefixMean]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [ePhase]
    congr 1
    push_cast
    ring
  rw [heq]
  exact hpre

end NormalNumbers.G4
