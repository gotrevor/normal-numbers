import NormalNumbers.SwingC1Pair

/-!
# Daboussi–Kátai: `ShiftIndep` reduced to `PairDecorr`

`SwingC1Delange.lean` reduced the crux to two named hypotheses:

* `DelangeMean (h/b)` — Delange's theorem (1969), KNOWN, Selberg–Delange, not in mathlib;
* `ShiftIndep b (h/b)` — one decorrelation between the leading digit `ω(n+1)` and the tail
  `θ_{n+1}`.

This file discharges `ShiftIndep` into `PairDecorr`, using one further KNOWN theorem stated as a
named hypothesis: the **Daboussi–Kátai orthogonality criterion** `KataiOrthogonality` (Kátai
1986; Daboussi–Delange 1974; the multiplicative case of Bourgain–Sarnak–Ziegler 2013).

The point is that `PairDecorr b t` — `mean_n e(t(θ_{pn} − θ_{qn})) → 0` for distinct primes
`p ≠ q` — contains **no multiplicative function at all**.  It is a pure statement about the
orbit `θ` at multiplicatively shifted indices, and `SwingC1Pair.lean` proves its periodic-model
form unconditionally (`periodMean_pair_tendsto_zero`).  The one remaining gap is therefore
leaf (D): natural density versus one full primorial period.

So after this file the crux of `conjC1` is exactly:

  **(D)** `PairDecorr b (h/b)`,  plus the two KNOWN theorems `DelangeMean` and
  `KataiOrthogonality`.

Sorry-free.
-/

open Finset Filter Topology NormalNumbers.PrimeLambert

namespace NormalNumbers.CastingOut

/-! ### Small facts about `phase` and `ω` -/

lemma conj_phase (x : ℝ) : (starRingEnd ℂ) (phase x) = phase (-x) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.ext_iff]

lemma omegaNat_zero : omegaNat 0 = 0 := by simp [omegaNat]
lemma omegaNat_one : omegaNat 1 = 0 := by simp [omegaNat]

lemma omegaNat_mul_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    omegaNat (m * n) = omegaNat m + omegaNat n := by
  unfold omegaNat
  rw [Nat.primeFactors_mul hm hn, Finset.card_union_of_disjoint h.disjoint_primeFactors]

/-! ### Shifting the index in a Cesàro mean -/

/-- A bounded sequence's Cesàro mean is unchanged, in the limit, by a one-step index shift. -/
lemma tendsto_fullMean_shift {g : ℕ → ℂ} (hg : ∀ n, ‖g n‖ ≤ 1)
    (h : Tendsto (fun N => fullMean g N) atTop (𝓝 0)) :
    Tendsto (fun N => fullMean (fun n => g (n + 1)) N) atTop (𝓝 0) := by
  have hbound : ∀ᶠ N : ℕ in atTop, ‖fullMean (fun n => g (n + 1)) N‖
      ≤ 2 * ‖fullMean g (N + 1)‖ + 1 / N := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNR : (0:ℝ) < N := by exact_mod_cast hN
    have hsum : ∑ n ∈ range N, g (n + 1) = (∑ m ∈ range (N + 1), g m) - g 0 := by
      rw [Finset.sum_range_succ']; ring
    have hfm : (∑ m ∈ range (N + 1), g m) = fullMean g (N + 1) * ((N : ℂ) + 1) := by
      rw [fullMean]
      field_simp
      push_cast
      ring
    rw [fullMean, hsum, hfm, norm_div, Complex.norm_natCast]
    rw [div_le_iff₀ hNR]
    have h1 : ‖fullMean g (N + 1) * ((N:ℂ) + 1) - g 0‖
        ≤ ‖fullMean g (N + 1)‖ * ((N:ℝ) + 1) + 1 := by
      refine le_trans (norm_sub_le _ _) ?_
      have : ‖fullMean g (N + 1) * ((N:ℂ) + 1)‖ = ‖fullMean g (N + 1)‖ * ((N:ℝ)+1) := by
        rw [norm_mul]
        congr 1
        rw [show ((N:ℂ) + 1) = ((((N:ℕ) + 1 : ℕ)) : ℂ) by push_cast; ring,
          Complex.norm_natCast]
        push_cast; ring
      rw [this]
      linarith [hg 0]
    have h2 : (2 * ‖fullMean g (N + 1)‖ + 1 / (N:ℝ)) * (N:ℝ)
        = 2 * ‖fullMean g (N + 1)‖ * (N:ℝ) + 1 := by field_simp
    have hNle : ((N:ℝ) + 1) ≤ 2 * (N:ℝ) := by
      have : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
      linarith
    rw [h2]
    nlinarith [norm_nonneg (fullMean g (N + 1)), h1, hNle]
  have hlim : Tendsto (fun N : ℕ => 2 * ‖fullMean g (N + 1)‖ + 1 / (N:ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => 2 * ‖fullMean g (N + 1)‖) atTop (𝓝 0) := by
      have := (h.comp (tendsto_add_atTop_nat 1)).norm
      simpa using this.const_mul 2
    have h2 : Tendsto (fun N : ℕ => (1:ℝ) / N) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
    simpa using h1.add h2
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _) hbound hlim)

/-! ### The criterion, and the reduction -/

/-- **The pair decorrelation input.**  The orbit at multiplicatively shifted indices
decorrelates: `mean_n e(t(θ_{pn} − θ_{qn})) → 0` for distinct primes `p ≠ q`. -/
def PairDecorr (b : ℕ) (t : ℝ) : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
    Tendsto (fun N => fullMean
      (fun n => phase (t * (omegaTail b (p * n) - omegaTail b (q * n)))) N) atTop (𝓝 0)

/-- **The Daboussi–Kátai orthogonality criterion, as a named hypothesis.**  A KNOWN theorem
(Kátai 1986; Daboussi–Delange 1974; the multiplicative case of Bourgain–Sarnak–Ziegler 2013),
not in mathlib: a bounded sequence whose multiplicatively-shifted autocorrelations vanish is
orthogonal to EVERY bounded multiplicative function. -/
def KataiOrthogonality : Prop :=
  ∀ (a f : ℕ → ℂ), (∀ n, ‖a n‖ ≤ 1) → (∀ n, ‖f n‖ ≤ 1) →
    (∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) →
    (∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      Tendsto (fun N => fullMean (fun n => a (p * n) * (starRingEnd ℂ) (a (q * n))) N)
        atTop (𝓝 0)) →
    Tendsto (fun N => fullMean (fun n => f n * a n) N) atTop (𝓝 0)

/-- **`e(t·ω(·))` is multiplicative.**  `ω` is additive on coprime arguments. -/
lemma phase_omegaNat_multiplicative (t : ℝ) (m n : ℕ) (h : Nat.Coprime m n) :
    phase (t * (omegaNat (m * n) : ℝ))
      = phase (t * (omegaNat m : ℝ)) * phase (t * (omegaNat n : ℝ)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.coprime_zero_left] at h
    subst h
    simp [omegaNat_zero, omegaNat_one, phase]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.coprime_zero_right] at h
    subst h
    simp [omegaNat_zero, omegaNat_one, phase]
  rw [omegaNat_mul_coprime (by omega) (by omega) h, ← phase_add]
  congr 1
  push_cast
  ring

/-- **The crux, one step further down.**  Granted the Daboussi–Kátai criterion (known) and
Delange's theorem (known), the single decorrelation `ShiftIndep` that `SwingC1Delange.lean`
needs follows from `PairDecorr` — a statement purely about the orbit `θ` at multiplicatively
shifted indices, with no multiplicative function left in it. -/
theorem shiftIndep_of_pairDecorr (b : ℕ) (t : ℝ) (hDK : KataiOrthogonality)
    (hD : DelangeMean t) (hP : PairDecorr b t) : ShiftIndep b t := by
  set a : ℕ → ℂ := fun n => phase (t * omegaTail b n) with ha
  set f : ℕ → ℂ := fun n => phase (t * (omegaNat n : ℝ)) with hf
  have hanorm : ∀ n, ‖a n‖ ≤ 1 := fun n => le_of_eq (norm_phase _)
  have hfnorm : ∀ n, ‖f n‖ ≤ 1 := fun n => le_of_eq (norm_phase _)
  have hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n := fun m n h =>
    phase_omegaNat_multiplicative t m n h
  have hpair : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      Tendsto (fun N => fullMean (fun n => a (p * n) * (starRingEnd ℂ) (a (q * n))) N)
        atTop (𝓝 0) := by
    intro p q hp hq hpq
    have heq : ∀ n : ℕ, a (p * n) * (starRingEnd ℂ) (a (q * n))
        = phase (t * (omegaTail b (p * n) - omegaTail b (q * n))) := by
      intro n
      rw [ha, conj_phase, ← phase_add]
      congr 1
      ring
    simpa only [heq] using hP p q hp hq hpq
  have hDKc : Tendsto (fun N => fullMean (fun n => f n * a n) N) atTop (𝓝 0) :=
    hDK a f hanorm hfnorm hmul hpair
  have hshift : Tendsto (fun N => fullMean (fun n => f (n + 1) * a (n + 1)) N) atTop (𝓝 0) :=
    tendsto_fullMean_shift (g := fun n => f n * a n)
      (fun n => by rw [norm_mul]; nlinarith [hfnorm n, hanorm n, norm_nonneg (f n),
        norm_nonneg (a n)]) hDKc
  -- the product of the two means also vanishes (Delange)
  set A : ℕ → ℂ := fun n => phase (t * (omegaNat (n + 1) : ℝ)) with hA
  set B : ℕ → ℂ := fun n => phase (t * omegaTail b (n + 1)) with hB
  have hBnorm : ∀ N, ‖fullMean B N‖ ≤ 1 := fun N =>
    norm_fullMean_le_one B N (fun m => le_of_eq (norm_phase _))
  have hprod : Tendsto (fun N => (fullMean A N) * (fullMean B N)) atTop (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    filter_upwards [(NormedAddGroup.tendsto_nhds_zero.mp hD) ε hε] with N hN
    calc ‖(fullMean A N) * (fullMean B N)‖ = ‖fullMean A N‖ * ‖fullMean B N‖ := norm_mul _ _
      _ ≤ ‖fullMean A N‖ * 1 := by
          nlinarith [hBnorm N, norm_nonneg (fullMean A N), norm_nonneg (fullMean B N)]
      _ = ‖fullMean A N‖ := by ring
      _ < ε := hN
  have hfin := hshift.sub hprod
  rw [sub_zero] at hfin
  exact hfin

end NormalNumbers.CastingOut
