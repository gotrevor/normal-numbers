import NormalNumbers.SwingC1Depth

/-!
# The crux, reduced to Delange's theorem plus one independence statement

Lap 28 pinned the crux to the finite-depth correlations
`mean_{n<M} Π_{i<L} z_i^{ω(n+1+i)}` with `L = L(M) → ∞`, and labelled that "Elliott-hard".  That
label is too pessimistic, because the object obeys an EXACT one-step recursion
(`omegaTail_rec`):

`b·θ_n = ω(n+1) + θ_{n+1}`,   hence   `e(h·θ_n) = e((h/b)·ω(n+1)) · e((h/b)·θ_{n+1})`.

So the depth-`L` product is not an unstructured correlation of `L` shifts: it is a single
one-step twist, iterated.  The whole Weyl sum therefore vanishes as soon as

* **(Delange)** the one-coordinate mean `mean_{n<N} e(t·ω(n+1))` vanishes for `t ∉ ℤ` — this is
  **Delange's theorem** (1969): `Σ_{n≤N} z^{ω(n)} ∼ C_z N (log N)^{z−1}`, so the mean is
  `≍ (log N)^{Re z − 1} → 0` whenever `z = e(t) ≠ 1`.  A KNOWN theorem (Selberg–Delange method),
  not in mathlib; and
* **(ShiftIndep)** the leading coordinate `ω(n+1)` decorrelates from the tail `θ_{n+1}` at the
  frequency `h/b`.

`weylMean_tendsto_zero_of` below is that reduction, sorry-free.  It replaces "Elliott's conjecture"
by "Delange's theorem + one decorrelation", which is a strictly, and substantially, weaker pair.

**Why `ShiftIndep` is the right target.**  It is exactly the hypothesis supplied by the
Daboussi–Kátai orthogonality criterion (the multiplicative form of Bourgain–Sarnak–Ziegler): for
a bounded sequence `a_n`, `mean_n f(n) a_n → 0` for every non-pretentious multiplicative `f` with
`|f| ≤ 1` provided `mean_n a_{pn} \bar a_{qn} → 0` for all distinct primes `p ≠ q`.  Here
`f(n) = e((h/b)ω(n))` (non-pretentious for `b ∤ h`, by Delange) and `a_n = e((h/b)θ_n)`, so the
criterion's hypothesis is a statement about the orbit at **multiplicatively shifted indices**,
`mean_n e((h/b)(θ_{pn} − θ_{qn})) → 0` — and THAT is directly attackable by the prime-periodic
form of `SwingC1Periodic.lean`, since `θ_m` depends on `m` only through `(m mod r)_r` and the map
`n ↦ (pn mod r, qn mod r)` is an explicit equidistributing map.  That is the next lap's target.
-/

open Finset Filter Topology NormalNumbers.PrimeLambert

namespace NormalNumbers.CastingOut

/-- The Weyl mean of the `×b`-orbit of `G₄_b` at frequency `h`, in tail form. -/
noncomputable def weylMean (b : ℕ) (h : ℝ) (N : ℕ) : ℂ :=
  fullMean (fun n => phase (h * omegaTail b n)) N

/-- **Delange's theorem, as a named hypothesis.**  The mean of the character `e(t·ω(n))` of the
number of distinct prime factors vanishes.  True for every `t ∉ ℤ` (Delange 1969, via
Selberg–Delange; the mean is `≍ (log N)^{cos 2πt − 1}`). -/
def DelangeMean (t : ℝ) : Prop :=
  Tendsto (fun N => fullMean (fun n => phase (t * (omegaNat (n + 1) : ℝ))) N) atTop (𝓝 0)

/-- **The one decorrelation the route needs.**  At frequency `t` the leading coordinate `ω(n+1)`
and the tail `θ_{n+1}` decorrelate in mean.  Supplied by the Daboussi–Kátai orthogonality
criterion from `mean_n e(t(θ_{pn} − θ_{qn})) → 0`, `p ≠ q` primes. -/
def ShiftIndep (b : ℕ) (t : ℝ) : Prop :=
  Tendsto (fun N =>
      fullMean (fun n => phase (t * (omegaNat (n + 1) : ℝ)) * phase (t * omegaTail b (n + 1))) N
        - (fullMean (fun n => phase (t * (omegaNat (n + 1) : ℝ))) N)
          * (fullMean (fun n => phase (t * omegaTail b (n + 1))) N)) atTop (𝓝 0)

/-- The exact one-step factorisation of the orbit's phase. -/
lemma phase_omegaTail_factor (b : ℕ) (hb : 2 ≤ b) (h : ℝ) (n : ℕ) :
    phase (h * omegaTail b n)
      = phase ((h / b) * (omegaNat (n + 1) : ℝ)) * phase ((h / b) * omegaTail b (n + 1)) := by
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  rw [← phase_add]
  congr 1
  have hrec := omegaTail_rec b hb n
  field_simp
  linear_combination h * hrec

/-- **The reduction.**  Delange's theorem at the frequency `h/b`, plus the single decorrelation
`ShiftIndep b (h/b)`, force the Weyl mean of the orbit to vanish. -/
theorem weylMean_tendsto_zero_of (b : ℕ) (hb : 2 ≤ b) (h : ℝ)
    (hD : DelangeMean (h / b)) (hI : ShiftIndep b (h / b)) :
    Tendsto (fun N => weylMean b h N) atTop (𝓝 0) := by
  set t : ℝ := h / b with ht
  set A : ℕ → ℂ := fun n => phase (t * (omegaNat (n + 1) : ℝ)) with hA
  set B : ℕ → ℂ := fun n => phase (t * omegaTail b (n + 1)) with hB
  -- the product of the two means vanishes
  have hBnorm : ∀ N, ‖fullMean B N‖ ≤ 1 := fun N =>
    norm_fullMean_le_one B N (fun m => by rw [hB]; exact le_of_eq (norm_phase _))
  have hprod : Tendsto (fun N => (fullMean A N) * (fullMean B N)) atTop (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    filter_upwards [(NormedAddGroup.tendsto_nhds_zero.mp hD) ε hε] with N hN
    calc ‖(fullMean A N) * (fullMean B N)‖ = ‖fullMean A N‖ * ‖fullMean B N‖ := norm_mul _ _
      _ ≤ ‖fullMean A N‖ * 1 := by
          have := hBnorm N
          nlinarith [norm_nonneg (fullMean A N), norm_nonneg (fullMean B N)]
      _ = ‖fullMean A N‖ := by ring
      _ < ε := hN
  -- and the mean of the product differs from it by `o(1)`
  have hsplit : ∀ N, weylMean b h N
      = (fullMean (fun n => A n * B n) N - (fullMean A N) * (fullMean B N))
        + (fullMean A N) * (fullMean B N) := by
    intro N
    have : weylMean b h N = fullMean (fun n => A n * B n) N := by
      rw [weylMean, fullMean, fullMean]
      congr 1
      exact Finset.sum_congr rfl fun n _ => by
        rw [hA, hB]; exact phase_omegaTail_factor b hb h n
    rw [this]; ring
  have hfinal : Tendsto (fun N =>
      (fullMean (fun n => A n * B n) N - (fullMean A N) * (fullMean B N))
        + (fullMean A N) * (fullMean B N)) atTop (𝓝 ((0 : ℂ) + 0)) := hI.add hprod
  rw [add_zero] at hfinal
  exact Filter.Tendsto.congr (fun N => (hsplit N).symm) hfinal

end NormalNumbers.CastingOut
