import NormalNumbers.SwingC1Delange

/-!
# The Daboussi–Kátai input: the pair factors `e(t(θ_{pn} − θ_{qn}))`

`SwingC1Delange.lean` reduced the crux to Delange's theorem plus the single decorrelation
`ShiftIndep b (h/b)`, and noted that the Daboussi–Kátai orthogonality criterion (multiplicative
Bourgain–Sarnak–Ziegler) supplies `ShiftIndep` from

`mean_{n<N} e(t·(θ_{pn} − θ_{qn})) → 0`,  `p ≠ q` primes.

By the prime-periodic form (`omegaTail_eq_tsum_primePeriodic`) the integrand is an explicit
function of the residues `(n mod r)_{r prime}`:

`θ_{pn} − θ_{qn} = Σ_r (b^{pn mod r} − b^{qn mod r})/(b^r − 1)`,

so the SAME CRT + Mertens machinery that proved leaf (M) applies verbatim, with `localFactor`
replaced by the **pair factor**

`pairLocalFactor b t r p q = (1/r) Σ_{s<r} e( t·(b^{ps mod r} − b^{qs mod r})/(b^r − 1) )`.

Proved here (sorry-free): the CRT factorisation `periodMean_phase_truncPairTail`, and the
Mertens consequence `prod_pairLocalFactor_tendsto_zero`.  The one open leaf is the separation
bound `norm_pairLocalFactor_le`, whose mechanism is worked out in its docstring: it is
`norm_localFactor_le` plus one pigeonhole, because the second exponent `qs mod r` can collide
with the top window only `O(1)` times.
-/

open Finset Filter Topology NormalNumbers.PrimeLambert

namespace NormalNumbers.CastingOut

/-- The `r`-local pair factor of the difference `θ_{pn} − θ_{qn}`. -/
noncomputable def pairLocalFactor (b : ℕ) (t : ℝ) (r p q : ℕ) : ℂ :=
  (∑ s ∈ range r,
      phase (t * (primePeriodicTerm b r (p * s) - primePeriodicTerm b r (q * s)))) / r

lemma norm_pairLocalFactor_le_one (b : ℕ) (t : ℝ) (r p q : ℕ) (hr : 0 < r) :
    ‖pairLocalFactor b t r p q‖ ≤ 1 := by
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  rw [pairLocalFactor, norm_div, Complex.norm_natCast, div_le_one hrr]
  calc ‖∑ s ∈ range r,
        phase (t * (primePeriodicTerm b r (p * s) - primePeriodicTerm b r (q * s)))‖
      ≤ ∑ s ∈ range r,
        ‖phase (t * (primePeriodicTerm b r (p * s) - primePeriodicTerm b r (q * s)))‖ :=
        norm_sum_le _ _
    _ = r := by simp

/-- The primes `≤ P` part of the difference `θ_{pn} − θ_{qn}`. -/
noncomputable def truncPairTail (b P p q n : ℕ) : ℝ :=
  ∑ r ∈ primesLe P, (primePeriodicTerm b r (p * n) - primePeriodicTerm b r (q * n))

/-- The residue reduction: each summand depends on `n` only through `n mod r`. -/
lemma primePeriodicTerm_mul_mod (b r p n : ℕ) :
    primePeriodicTerm b r (p * n) = primePeriodicTerm b r (p * (n % r)) := by
  unfold primePeriodicTerm
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · congr 2
    rw [Nat.mul_mod, Nat.mul_mod p (n % r) r, Nat.mod_mod_of_dvd n (dvd_refl r)]

/-- **The CRT factorisation of the pair mean.**  Over one full period `Q = Π_{r ≤ P} r` the mean
of `e(t·(θ^{(P)}_{pn} − θ^{(P)}_{qn}))` is the product of the local pair factors. -/
theorem periodMean_phase_truncPairTail (b P p q : ℕ) (t : ℝ) :
    periodMean (fun n => phase (t * truncPairTail b P p q n)) (primorialLe P)
      = ∏ r ∈ primesLe P, pairLocalFactor b t r p q := by
  classical
  have hA : ∀ n : ℕ, phase (t * truncPairTail b P p q n)
      = ∏ r ∈ primesLe P,
          phase (t * (primePeriodicTerm b r (p * (n % r))
            - primePeriodicTerm b r (q * (n % r)))) := by
    intro n
    rw [truncPairTail, Finset.mul_sum, phase_sum]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [primePeriodicTerm_mul_mod b r p n, primePeriodicTerm_mul_mod b r q n]
  have hcop : ((primesLe P : Finset ℕ) : Set ℕ).Pairwise Nat.Coprime := by
    intro x hx y hy hne
    exact (Nat.coprime_primes (prime_of_mem_primesLe hx) (prime_of_mem_primesLe hy)).mpr hne
  have hpos : ∀ r ∈ primesLe P, 0 < r := fun r hr => (prime_of_mem_primesLe hr).pos
  rw [periodMean, primorialLe, Finset.sum_congr rfl (fun n _ => hA n),
    sum_range_prod_mod
      (fun r s => phase (t * (primePeriodicTerm b r (p * s) - primePeriodicTerm b r (q * s))))
      (primesLe P) hpos hcop,
    Nat.cast_prod, ← Finset.prod_div_distrib]
  rfl

/-! ### The one open leaf: the pair separation bound -/

/-- **The pair separation bound.**  OPEN.

Mechanism (a pigeonhole on top of `norm_localFactor_le`).  Fix `r` prime with `r > p*q + |p−q|`,
so `p, q` are invertible mod `r` and `p ≢ q`.  For `j ≥ 0` put `s_j := p⁻¹(r−1−j) mod r`, so the
FIRST exponent is `p·s_j ≡ r−1−j` and the summand's argument is

`t·(b^{r−1−j} − b^{c_j})/(b^r − 1)`,  `c_j := q p⁻¹ (r−1−j) mod r`.

* `s = 0` contributes the argument `0`, i.e. the unit vector `1`.
* The first term tends to `t·b^{−1−j}`; pick `j = i` minimal with `|t|·b^{−1−i} < 1/4`, so
  `0 < |t|b^{−1−i}` is a FIXED nonzero number.
* The second term is `≤ b^{−1}` times the first as soon as `c_j ≤ r − 2 − i`.  The `c_j` for
  `j = i, …, i+i+2` are distinct (an AP of step `−q p⁻¹ ≢ 0`), and at most `i+1` residues exceed
  `r − 2 − i`, so SOME `j` in that window works.  (`c_j = r−1−j` itself is impossible: it forces
  `r ∣ (q−p)s_j` with `s_j ≢ 0`, i.e. `r ∣ q−p`.)

For that `j` the summand's argument tends to a limit in `[t b^{−1−i}(1 − b^{−1}), t b^{−1−i}]`, an
interval of fixed nonzero numbers inside `(0, 1/4)`, hence bounded away from `ℤ`.  So two of the
`r` unit vectors are a fixed `δ > 0` apart, and the parallelogram bound
`norm_add_le_of_norm_sub_ge` gives `‖pairLocalFactor‖ ≤ 1 − δ²/(16 r)` exactly as in
`norm_localFactor_le`.

TODO(alt: a second-moment bound on `Σ_s |b^{ps mod r} − b^{qs mod r}|` would also separate, but
the pigeonhole is elementary and reuses the proved two-vector lemma.) -/
theorem norm_pairLocalFactor_le (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (ht : t ≠ 0) (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℕ in atTop,
      r.Prime → ‖pairLocalFactor b t r p q‖ ≤ 1 - c / r := by
  sorry

/-- **The pair model term vanishes.**  Granted the separation bound, Mertens finishes — the same
engine as leaf (M), now shared via `prod_tendsto_zero_of_norm_le`. -/
theorem prod_pairLocalFactor_tendsto_zero (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (ht : t ≠ 0)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Tendsto (fun P => ‖∏ r ∈ primesLe P, pairLocalFactor b t r p q‖) atTop (𝓝 0) := by
  obtain ⟨c, hc, hev⟩ := norm_pairLocalFactor_le b hb t ht p q hp hq hpq
  exact prod_tendsto_zero_of_norm_le (fun r => pairLocalFactor b t r p q)
    (fun r hr => norm_pairLocalFactor_le_one b t r p q hr) hc hev

/-- **The pair model term, assembled.**  The period mean of the pair phase vanishes as the cut
`P → ∞` — the periodic-model form of the Daboussi–Kátai hypothesis. -/
theorem periodMean_pair_tendsto_zero (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (ht : t ≠ 0)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Tendsto (fun P => ‖periodMean (fun n => phase (t * truncPairTail b P p q n))
      (primorialLe P)‖) atTop (𝓝 0) := by
  simpa only [periodMean_phase_truncPairTail] using
    prod_pairLocalFactor_tendsto_zero b hb t ht p q hp hq hpq

end NormalNumbers.CastingOut
