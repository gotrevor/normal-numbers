import NormalNumbers.PrimeLambertDefs

/-!
# Transported signed configurations and the exact phase identity

A *transported configuration* is a finitely supported integer weighting `c` of
atoms `(d, s) : ℕ × ℤ` (multiplier `d`, numerator shift `s`).  Its site-`j`
projection is `r_{j}(d,s) = j·d − s`; the configuration *cancels at site `j`*
when the pushforward of `c` along that projection vanishes (`CancelsAt`).

The signed tail functional attached to `c`, cut at `K`, is

  `phaseSum c K n = ∑_{(d,s)} c(d,s) · ∑_{j > K} 2^{-j} ω(n + j·d − s)`.

**Theorem A** (`phaseSum_sub_int`): if `q · primeLambert ∈ ℤ`, `c` cancels at every site
`1 ≤ j ≤ K`, and `n, n'` lie on the constructed progression (each `n + j d − s = d(k+j)`
with `k ≥ 0`, and the quotients `k` frozen modulo every prime dividing `d`), then
`q · (phaseSum c K n − phaseSum c K n') ∈ ℤ`.  Hence `e(q · phaseSum c K ·)` is
*constant* on such a progression.  This is the entire arithmetic content of the
rational-tail contradiction; the analytic input (that the average of that phase tends
to zero) is isolated in `PrimeLambertOscillation`.
-/

open Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeLambert

/-- A transported signed configuration: integer weights on atoms `(d, s)`. -/
abbrev TConfig := (ℕ × ℤ) →₀ ℤ

/-- Site-`j` projection of an atom: `j·d − s`. -/
def proj (j : ℕ) (a : ℕ × ℤ) : ℤ := (j : ℤ) * a.1 - a.2

/-- `c` cancels at site `j`: the signed weight over every fibre of `proj j` is zero. -/
def CancelsAt (c : TConfig) (j : ℕ) : Prop := Finsupp.mapDomain (proj j) c = 0

/-- `ω` on integers via `natAbs` (all arguments in use are positive). -/
noncomputable def omegaZ (m : ℤ) : ℝ := omegaR m.natAbs

lemma omegaZ_natCast (m : ℕ) : omegaZ m = omegaR m := by simp [omegaZ]

/-- Cancellation kills every fibre-constant signed sum. -/
theorem CancelsAt.sum_eq_zero {c : TConfig} {j : ℕ} (hc : CancelsAt c j) (f : ℤ → ℝ) :
    c.sum (fun a w => (w : ℝ) * f (proj j a)) = 0 := by
  have h := Finsupp.sum_mapDomain_index (f := proj j) (s := c) (h := fun r (w : ℤ) => (w : ℝ) * f r)
    (fun r => by simp) (fun r w₁ w₂ => by push_cast; ring)
  rw [← h, hc, Finsupp.sum_zero_index]

/-- The site-`j` cancellation in the form used by the tail: `∑_a c(a) ω(n + j·d − s) = 0`. -/
theorem CancelsAt.omega_sum_eq_zero {c : TConfig} {j : ℕ} (hc : CancelsAt c j) (n : ℤ) :
    c.sum (fun a w => (w : ℝ) * omegaZ (n + (j : ℤ) * a.1 - a.2)) = 0 := by
  have := hc.sum_eq_zero (fun r => omegaZ (n + r))
  refine Eq.trans ?_ this
  refine Finsupp.sum_congr (fun a _ => ?_)
  simp only [proj]; ring_nf

/-- The tail of one atom beyond site `K`: `∑_{j > K} 2^{-j} ω(n + j·d − s)` (index `j = i+1`). -/
noncomputable def atomTail (K : ℕ) (a : ℕ × ℤ) (n : ℤ) : ℝ :=
  ∑' i : ℕ, if K ≤ i then omegaZ (n + ((i : ℤ) + 1) * a.1 - a.2) / 2 ^ (i + 1) else 0

/-- The signed tail functional `F(n)` of a configuration, cut at `K`. -/
noncomputable def phaseSum (c : TConfig) (K : ℕ) (n : ℤ) : ℝ :=
  c.sum (fun a w => (w : ℝ) * atomTail K a n)

/-- On the progression, `n + (i+1) d − s = d (k + i + 1)`. -/
lemma arg_eq {d : ℕ} {s : ℤ} {n : ℤ} {k : ℕ} (hn : n = (d : ℤ) * k + s) (i : ℕ) :
    n + ((i : ℤ) + 1) * d - s = ((d * (k + i + 1) : ℕ) : ℤ) := by
  subst hn; push_cast; ring

/-- The atom tail on the progression equals the full dilated tail minus the first `K` sites. -/
theorem atomTail_eq {d : ℕ} {s : ℤ} {n : ℤ} {k : ℕ} (hd : d ≠ 0) (hn : n = (d : ℤ) * k + s)
    (K : ℕ) :
    atomTail K (d, s) n =
      dilatedTail d k - ∑ i ∈ Finset.range K, omegaR (d * (k + i + 1)) / 2 ^ (i + 1) := by
  have hfun : ∀ i : ℕ, (if K ≤ i then omegaZ (n + ((i : ℤ) + 1) * d - s) / 2 ^ (i + 1) else 0)
      = omegaR (d * (k + i + 1)) / 2 ^ (i + 1)
        - (if i < K then omegaR (d * (k + i + 1)) / 2 ^ (i + 1) else 0) := by
    intro i
    rw [arg_eq hn i, omegaZ_natCast]
    by_cases h : K ≤ i
    · simp [h, not_lt.mpr h]
    · simp [h, not_le.mp h]
  have hs1 := summable_dilatedTail d k hd
  have hs2 : Summable (fun i : ℕ => if i < K then omegaR (d * (k + i + 1)) / 2 ^ (i + 1) else 0) :=
    summable_of_ne_finset_zero (s := Finset.range K) (fun i hi => by
      rw [Finset.mem_range] at hi; simp [hi])
  have h2 : ∑' i : ℕ, (if i < K then omegaR (d * (k + i + 1)) / 2 ^ (i + 1) else 0)
      = ∑ i ∈ Finset.range K, omegaR (d * (k + i + 1)) / 2 ^ (i + 1) := by
    rw [tsum_eq_sum (s := Finset.range K) (fun i hi => by rw [Finset.mem_range] at hi; simp [hi])]
    exact Finset.sum_congr rfl (fun i hi => by rw [Finset.mem_range] at hi; simp [hi])
  rw [atomTail, tsum_congr hfun, Summable.tsum_sub hs1 hs2, h2]
  rfl

/-- Progression data for a configuration: quotients `k n a` with `n = d·k + s` on every atom. -/
structure OnProgression (c : TConfig) (k : ℤ → ℕ × ℤ → ℕ) (n : ℤ) : Prop where
  pos : ∀ a ∈ c.support, a.1 ≠ 0
  quot : ∀ a ∈ c.support, n = (a.1 : ℤ) * k n a + a.2

/-- The `j ≤ K` part of the signed tail vanishes by cancellation. -/
theorem finite_part_eq_zero (c : TConfig) (K : ℕ) (k : ℤ → ℕ × ℤ → ℕ) (n : ℤ)
    (hn : OnProgression c k n) (hc : ∀ j, 1 ≤ j → j ≤ K → CancelsAt c j) :
    c.sum (fun a w => (w : ℝ) * ∑ i ∈ Finset.range K,
      omegaR (a.1 * (k n a + i + 1)) / 2 ^ (i + 1)) = 0 := by
  have h1 : ∀ a ∈ c.support, ∀ i : ℕ,
      omegaR (a.1 * (k n a + i + 1)) = omegaZ (n + ((i + 1 : ℕ) : ℤ) * a.1 - a.2) := by
    intro a ha i
    have hq := hn.quot a ha
    rw [show n + ((i + 1 : ℕ) : ℤ) * a.1 - a.2 = ((a.1 * (k n a + i + 1) : ℕ) : ℤ) by
      push_cast; linear_combination hq, omegaZ_natCast]
  calc c.sum (fun a w => (w : ℝ) * ∑ i ∈ Finset.range K,
          omegaR (a.1 * (k n a + i + 1)) / 2 ^ (i + 1))
      = ∑ i ∈ Finset.range K, (1 / 2 ^ (i + 1) : ℝ) *
          c.sum (fun a w => (w : ℝ) * omegaZ (n + ((i + 1 : ℕ) : ℤ) * a.1 - a.2)) := by
        unfold Finsupp.sum
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun a ha => ?_)
        rw [h1 a ha i]; ring
    _ = 0 := by
        refine Finset.sum_eq_zero (fun i hi => ?_)
        rw [(hc (i + 1) (by omega) (by rw [Finset.mem_range] at hi; omega)).omega_sum_eq_zero n,
          mul_zero]

/-- The signed tail on the progression: `F(n) = ∑_a c(a) (T(k_a) + ω d_a − E_{d_a}(k_a))`. -/
theorem phaseSum_eq (c : TConfig) (K : ℕ) (k : ℤ → ℕ × ℤ → ℕ) (n : ℤ)
    (hn : OnProgression c k n) (hc : ∀ j, 1 ≤ j → j ≤ K → CancelsAt c j) :
    phaseSum c K n =
      c.sum (fun a w => (w : ℝ) * (tailT (k n a) + omegaR a.1 - transportCorr a.1 (k n a))) := by
  have h : phaseSum c K n =
      c.sum (fun a w => (w : ℝ) * (tailT (k n a) + omegaR a.1 - transportCorr a.1 (k n a)))
      - c.sum (fun a w => (w : ℝ) * ∑ i ∈ Finset.range K,
          omegaR (a.1 * (k n a + i + 1)) / 2 ^ (i + 1)) := by
    rw [phaseSum, ← Finsupp.sum_sub]
    refine Finsupp.sum_congr (fun a ha => ?_)
    rw [← mul_sub, atomTail_eq (hn.pos a ha) (hn.quot a ha) K, dilatedTail_eq _ _ (hn.pos a ha)]
  rw [h, finite_part_eq_zero c K k n hn hc, sub_zero]

/-- **Theorem A.**  If `q · primeLambert ∈ ℤ` and `c` cancels at sites `1..K`, then for any two
points `n, n'` of the progression whose quotients agree modulo every prime dividing each
multiplier, `q · (F(n) − F(n'))` is an integer. -/
theorem phaseSum_sub_int {q z : ℤ} (hq : (q : ℝ) * primeLambert = z)
    (c : TConfig) (K : ℕ) (k : ℤ → ℕ × ℤ → ℕ) (n n' : ℤ)
    (hn : OnProgression c k n) (hn' : OnProgression c k n')
    (hfrozen : ∀ a ∈ c.support, ∀ p ∈ a.1.primeFactors, k n a ≡ k n' a [MOD p])
    (hc : ∀ j, 1 ≤ j → j ≤ K → CancelsAt c j) :
    ∃ w : ℤ, (q : ℝ) * (phaseSum c K n - phaseSum c K n') = w := by
  rw [phaseSum_eq c K k n hn hc, phaseSum_eq c K k n' hn' hc, ← Finsupp.sum_sub, Finsupp.mul_sum]
  have hterm : ∀ a ∈ c.support, ∃ w : ℤ,
      (q : ℝ) * ((c a : ℝ) *
        (tailT (k n a) + omegaR a.1 - transportCorr a.1 (k n a)) -
        (c a : ℝ) * (tailT (k n' a) + omegaR a.1 - transportCorr a.1 (k n' a))) = w := by
    intro a ha
    obtain ⟨w₁, hw₁⟩ := rational_tail_int hq (k n a)
    obtain ⟨w₂, hw₂⟩ := rational_tail_int hq (k n' a)
    refine ⟨c a * (w₁ - w₂), ?_⟩
    rw [transportCorr_congr a.1 (k n a) (k n' a) (hfrozen a ha)]
    push_cast
    linear_combination (c a : ℝ) * hw₁ - (c a : ℝ) * hw₂
  choose w hw using hterm
  refine ⟨∑ a ∈ c.support.attach, w a a.2, ?_⟩
  unfold Finsupp.sum
  rw [← Finset.sum_attach c.support]
  push_cast
  refine Finset.sum_congr rfl (fun a _ => ?_)
  exact hw a a.2

end NormalNumbers.PrimeLambert
