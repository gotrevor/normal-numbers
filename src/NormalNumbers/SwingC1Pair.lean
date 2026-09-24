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

**This file is now sorry-free.**  It proves the CRT factorisation `periodMean_phase_truncPairTail`,
the separation bound `norm_pairLocalFactor_le` (a residue pigeonhole, `exists_pair_residue`, plus
the elementary bound `‖e(x) − 1‖ ≥ |sin 2πx|`), and the Mertens consequences
`prod_pairLocalFactor_tendsto_zero` and `periodMean_pair_tendsto_zero`.

So the periodic-model form of the Daboussi–Kátai input is **unconditional**: for every `b ≥ 2`,
every `t ≠ 0` and every pair of distinct primes `p ≠ q`, the period mean of
`e(t(θ^{(P)}_{pn} − θ^{(P)}_{qn}))` tends to `0` as the prime cut `P → ∞`.  What remains between
this and `ShiftIndep` is leaf (D): natural density versus one full period.
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

/-! ### The pair difference has exactly zero drift -/

/-- Multiplying the index by a unit mod `r` permutes the residues, so the full-period sum of
`primePeriodicTerm b r (p·s)` is the same `1/(b−1)` as for `p = 1`. -/
lemma sum_primePeriodicTerm_mul_period (b : ℕ) (hb : 2 ≤ b) (r p : ℕ) (hr : r.Prime)
    (hp : ¬ (r ∣ p)) :
    ∑ s ∈ range r, primePeriodicTerm b r (p * s) = 1 / ((b : ℝ) - 1) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : NeZero r := ⟨hr.pos.ne'⟩
  have hpne : (p : ZMod r) ≠ 0 := fun h => hp ((ZMod.natCast_eq_zero_iff p r).mp h)
  set pinv : ℕ := ((p : ZMod r)⁻¹).val with hpinv
  rw [← sum_primePeriodicTerm_period b hb r hr]
  refine Finset.sum_nbij' (i := fun s => (p * s) % r) (j := fun u => (pinv * u) % r)
    ?_ ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_range.mpr (Nat.mod_lt _ hr.pos)
  · intro a _; exact Finset.mem_range.mpr (Nat.mod_lt _ hr.pos)
  · intro a ha
    rw [Finset.mem_range] at ha
    have hc : ((pinv * ((p * a) % r) : ℕ) : ZMod r) = ((a : ℕ) : ZMod r) := by
      push_cast
      rw [ZMod.natCast_mod, hpinv, ZMod.natCast_val, ZMod.cast_id]
      push_cast
      field_simp
    have h2 : (pinv * ((p * a) % r)) % r = a % r := by
      rw [← ZMod.val_natCast r, ← ZMod.val_natCast r a, hc]
    rw [h2, Nat.mod_eq_of_lt ha]
  · intro a ha
    rw [Finset.mem_range] at ha
    have hc : ((p * ((pinv * a) % r) : ℕ) : ZMod r) = ((a : ℕ) : ZMod r) := by
      push_cast
      rw [ZMod.natCast_mod, hpinv]
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id]
      field_simp
    have h2 : (p * ((pinv * a) % r)) % r = a % r := by
      rw [← ZMod.val_natCast r, ← ZMod.val_natCast r a, hc]
    rw [h2, Nat.mod_eq_of_lt ha]
  · intro a _
    rw [primePeriodicTerm, primePeriodicTerm, if_pos hr, if_pos hr, Nat.mod_mod_of_dvd _ dvd_rfl]

/-- **The pair difference has exactly zero drift over a full period.**  Contrast
`sum_primePeriodicTerm_period`, where the single tail's period mean is `1/(r(b−1))` and summing
over `r ≤ P` gives the divergent Mertens drift `≍ (log log P)/(b−1)` recorded in
`OBSTRUCTION-2026-09-24-periodic-approximant.md`.  For the DIFFERENCE the drift cancels exactly,
for every `r` and hence for every cut `P`. -/
theorem sum_pairTerm_period (b : ℕ) (hb : 2 ≤ b) (r p q : ℕ) (hr : r.Prime)
    (hp : ¬ (r ∣ p)) (hq : ¬ (r ∣ q)) :
    ∑ s ∈ range r, (primePeriodicTerm b r (p * s) - primePeriodicTerm b r (q * s)) = 0 := by
  rw [Finset.sum_sub_distrib, sum_primePeriodicTerm_mul_period b hb r p hr hp,
    sum_primePeriodicTerm_mul_period b hb r q hr hq, sub_self]

/-! ### Geometry and residue selection for the separation bound -/

lemma phase_im (x : ℝ) : (phase x).im = Real.sin (2 * Real.pi * x) := by
  have hx : phase x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    unfold phase; congr 1; push_cast; ring
  rw [hx, Complex.exp_ofReal_mul_I_im]

lemma abs_sin_le_norm_phase_sub_one (x : ℝ) :
    |Real.sin (2 * Real.pi * x)| ≤ ‖phase x - 1‖ := by
  have := Complex.abs_im_le_norm (phase x - 1)
  simpa [phase_im] using this

lemma sin_le_abs_sin_of_le_abs {A y : ℝ} (hA : 0 ≤ A) (h1 : A ≤ |y|)
    (h2 : |y| ≤ Real.pi / 2) : Real.sin A ≤ |Real.sin y| := by
  have hstep : Real.sin |y| ≤ |Real.sin y| := by
    rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; exact le_abs_self _
    · rw [h, Real.sin_neg]; exact neg_le_abs _
  have hmono : Real.sin A ≤ Real.sin |y| :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) h2 h1
  linarith

/-- The separation used for the pair factor: a single nonzero residue `s` whose phase is a fixed
distance from `1` forces `‖(1/r) Σ_s z_s‖ ≤ 1 - δ²/(4r)`. -/
lemma norm_pairLocalFactor_le_of_sep (b : ℕ) (t : ℝ) (r p q : ℕ) (hr : 0 < r)
    {s : ℕ} (hs : s < r) (hs0 : s ≠ 0) (hp0 : p * 0 = 0) (hq0 : q * 0 = 0)
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hsep : δ ≤ ‖phase (t * (primePeriodicTerm b r (p * s) - primePeriodicTerm b r (q * s)))
        - 1‖) :
    ‖pairLocalFactor b t r p q‖ ≤ 1 - (δ ^ 2 / 4) / r := by
  classical
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  set g : ℕ → ℂ := fun s =>
    phase (t * (primePeriodicTerm b r (p * s) - primePeriodicTerm b r (q * s))) with hg
  have hz0 : g 0 = 1 := by
    simp [hg, hp0, hq0, phase]
  have hpair : ‖g 0 + g s‖ ≤ 2 - δ ^ 2 / 4 := by
    have := norm_add_le_of_norm_sub_ge (z := g s) (w := g 0) (norm_phase _) (norm_phase _)
      hδ0 (by rw [hz0]; exact hsep)
    rw [add_comm]; exact this
  have hsub : ({0, s} : Finset ℕ) ⊆ range r := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_range.mpr hr
    · exact Finset.mem_range.mpr hs
  have hne : (0 : ℕ) ≠ s := fun h => hs0 h.symm
  have hcard : (range r \ ({0, s} : Finset ℕ)).card = r - 2 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_range,
      Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  have hr2 : 2 ≤ r := by omega
  have hrest : ‖∑ x ∈ range r \ ({0, s} : Finset ℕ), g x‖ ≤ ((r:ℝ) - 2) := by
    calc ‖∑ x ∈ range r \ ({0, s} : Finset ℕ), g x‖
        ≤ ∑ x ∈ range r \ ({0, s} : Finset ℕ), ‖g x‖ := norm_sum_le _ _
      _ = ((r - 2 : ℕ) : ℝ) := by simp [hcard, hg]
      _ = ((r:ℝ) - 2) := by rw [Nat.cast_sub hr2]; norm_num
  have hsum : ‖∑ x ∈ range r, g x‖ ≤ (r:ℝ) - δ ^ 2 / 4 := by
    rw [← Finset.sum_sdiff hsub, Finset.sum_pair hne]
    calc ‖(∑ x ∈ range r \ ({0, s} : Finset ℕ), g x) + (g 0 + g s)‖
        ≤ ‖∑ x ∈ range r \ ({0, s} : Finset ℕ), g x‖ + ‖g 0 + g s‖ := norm_add_le _ _
      _ ≤ ((r:ℝ) - 2) + (2 - δ ^ 2 / 4) := by linarith
      _ = (r:ℝ) - δ ^ 2 / 4 := by ring
  rw [pairLocalFactor, norm_div, Complex.norm_natCast, div_le_iff₀ hrR]
  have he : (1 - δ ^ 2 / 4 / (r:ℝ)) * (r:ℝ) = (r:ℝ) - δ ^ 2 / 4 := by field_simp
  rw [he]
  exact hsum



/-- The residue-selection pigeonhole.  For `r` prime large, there is `s ≢ 0` with
`p*s ≡ r-1-j` for some `j ∈ [i, 2i+2]` and `q*s ≡ c` with `c ≤ r-1-i` and `c ≠ r-1-j`. -/
lemma exists_pair_residue (p q i r : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hr : r.Prime) (hrb : p + q + (2*i+2) + 10 ≤ r) :
    ∃ s j : ℕ, s < r ∧ s ≠ 0 ∧ i ≤ j ∧ j ≤ 2*i+2 ∧
      (p * s) % r = r - 1 - j ∧ (q * s) % r ≤ r - 1 - i ∧ (q * s) % r ≠ r - 1 - j := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : NeZero r := ⟨hr.pos.ne'⟩
  set J := 2*i+2 with hJ
  have hpr : p < r := by omega
  have hqr : q < r := by omega
  have hpne : (p : ZMod r) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff p r).mp h
    have := Nat.le_of_dvd hp.pos this
    omega
  set x : ℕ → ZMod r := fun j => ((r - 1 - j : ℕ) : ZMod r) with hx
  set y : ℕ → ZMod r := fun j => (q : ZMod r) * (p : ZMod r)⁻¹ * x j with hy
  set s : ℕ → ℕ := fun j => ((p : ZMod r)⁻¹ * x j).val with hs
  -- basic facts
  have hxval : ∀ j ≤ J, (x j).val = r - 1 - j := by
    intro j hj; rw [hx]; exact ZMod.val_cast_of_lt (by omega)
  have hxne : ∀ j ≤ J, x j ≠ 0 := by
    intro j hj h
    have : (x j).val = 0 := by rw [h]; simp
    rw [hxval j hj] at this; omega
  have hps : ∀ j ≤ J, (p * s j) % r = r - 1 - j := by
    intro j hj
    have hcast : ((p * s j : ℕ) : ZMod r) = x j := by
      push_cast
      rw [hs, ZMod.natCast_val, ZMod.cast_id]
      field_simp
    have : (p * s j) % r = ((p * s j : ℕ) : ZMod r).val := (ZMod.val_natCast r _).symm
    rw [this, hcast, hxval j hj]
  have hqs : ∀ j ≤ J, (q * s j) % r = (y j).val := by
    intro j hj
    have hcast : ((q * s j : ℕ) : ZMod r) = y j := by
      push_cast
      rw [hs, ZMod.natCast_val, ZMod.cast_id, hy]
      ring
    have : (q * s j) % r = ((q * s j : ℕ) : ZMod r).val := (ZMod.val_natCast r _).symm
    rw [this, hcast]
  have hqpne : (q : ZMod r) * (p : ZMod r)⁻¹ ≠ 0 := by
    have hqne : (q : ZMod r) ≠ 0 := by
      intro h
      have := (ZMod.natCast_eq_zero_iff q r).mp h
      have := Nat.le_of_dvd hq.pos this
      omega
    exact mul_ne_zero hqne (inv_ne_zero hpne)
  have hqp1 : (q : ZMod r) * (p : ZMod r)⁻¹ ≠ 1 := by
    intro h
    have : (q : ZMod r) = (p : ZMod r) := by
      field_simp at h; exact h
    have := (ZMod.natCast_eq_natCast_iff q p r).mp this
    unfold Nat.ModEq at this
    rw [Nat.mod_eq_of_lt hqr, Nat.mod_eq_of_lt hpr] at this
    exact hpq this.symm
  -- y j ≠ x j
  have hyx : ∀ j ≤ J, y j ≠ x j := by
    intro j hj h
    apply hqp1
    rw [hy] at h
    have h2 : (q : ZMod r) * (p : ZMod r)⁻¹ * x j = 1 * x j := by rw [one_mul]; exact h
    exact mul_right_cancel₀ (hxne j hj) h2
  -- injectivity of j ↦ (y j).val on [0, J]
  have hinj : ∀ j ≤ J, ∀ k ≤ J, (y j).val = (y k).val → j = k := by
    intro j hj k hk hval
    have hyy : y j = y k := by
      have := congrArg (fun n : ℕ => ((n : ℕ) : ZMod r)) hval
      simpa [ZMod.natCast_val, ZMod.cast_id] using this
    have hxx : x j = x k := by
      rw [hy] at hyy
      exact mul_left_cancel₀ hqpne hyy
    have := congrArg ZMod.val hxx
    rw [hxval j hj, hxval k hk] at this
    omega
  -- pigeonhole
  by_cases hall : ∀ j ∈ Finset.Icc i J, r - i ≤ (y j).val
  · exfalso
    have hmap : ∀ j ∈ Finset.Icc i J, (y j).val ∈ Finset.Icc (r - i) (r - 1) := by
      intro j hj
      refine Finset.mem_Icc.mpr ⟨hall j hj, ?_⟩
      have := ZMod.val_lt (y j); omega
    have hcard := Finset.card_le_card_of_injOn (fun j => (y j).val) hmap
      (by
        intro j hj k hk hjk
        simp only [Finset.coe_Icc, Set.mem_Icc] at hj hk
        exact hinj j hj.2 k hk.2 hjk)
    rw [Nat.card_Icc, Nat.card_Icc] at hcard
    omega
  · push_neg at hall
    obtain ⟨j, hjmem, hjlt⟩ := hall
    rw [Finset.mem_Icc] at hjmem
    obtain ⟨hij, hjJ⟩ := hjmem
    refine ⟨s j, j, ZMod.val_lt _, ?_, hij, hjJ, hps j hjJ, ?_, ?_⟩
    · intro h
      have := hps j hjJ
      rw [h, Nat.mul_zero, Nat.zero_mod] at this
      omega
    · rw [hqs j hjJ]; omega
    · rw [hqs j hjJ]
      intro hcon
      exact hyx j hjJ (by
        have : (y j).val = (x j).val := by rw [hcon, hxval j hjJ]
        exact ZMod.val_injective r this)

/-! ### The pair separation bound -/

set_option maxHeartbeats 1000000 in
/-- **The pair separation bound — PROVED.**

Fix `r` prime with `r ≥ p + q + (2i+2) + 10`.  Since `r` is prime, `p` and `q` are invertible
mod `r` and `q p⁻¹ ≠ 1` (that would force `r ∣ q − p`).  For `j` in the window `[i, 2i+2]` put
`s_j := p⁻¹(r−1−j) mod r`, so the FIRST exponent is `a_j = p s_j mod r = r−1−j` and the second is
`c_j = q s_j mod r = (q p⁻¹ (r−1−j)).val`.

*Pigeonhole* (`exists_pair_residue`): `j ↦ c_j` is injective on the window (multiplication by the
unit `q p⁻¹` is injective and `j ↦ r−1−j` is injective below `r`), and at most `i` residues lie in
the top block `[r−i, r−1]`, while the window has `i + 3` elements.  So some `j` has
`c_j ≤ r−1−i`; and `c_j ≠ a_j` always, since `q p⁻¹ ≠ 1`.

*Analysis*: with `m = max a_j c_j`, `n = min a_j c_j` (so `n < m`, `m + 1 + i ≤ r ≤ m + 1 + 2i+2`),
`|b^{a} − b^{c}|/(b^r − 1) ∈ [R/2, 2R]` where `R = b^m/b^r ∈ [b^{−1−J}, b^{−1−i}]`, `J = 2i+2`.
Hence the `s_j`-summand's argument has `|arg| ∈ [A, B]` with the FIXED constants
`A = |t|/(2b^{1+J}) > 0` and `B = 2|t|/b^{1+i} ≤ 1/4` (choose `i` with `8|t| ≤ b^{1+i}`).

*Separation*: `‖e(x) − 1‖ ≥ |Im e(x)| = |sin 2πx|`, and `sin` is monotone on `[0, π/2]`, so
`‖e(arg) − 1‖ ≥ sin(2πA) =: δ > 0`, uniformly in `r`.  The `s = 0` summand is exactly `1`, so two
of the `r` unit vectors are `δ` apart and `norm_pairLocalFactor_le_of_sep` (the parallelogram
bound) gives `‖pairLocalFactor‖ ≤ 1 − (δ²/4)/r`. -/
theorem norm_pairLocalFactor_le (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (ht : t ≠ 0) (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℕ in atTop,
      r.Prime → ‖pairLocalFactor b t r p q‖ ≤ 1 - c / r := by
  classical
  have hb1 : (1:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hb2R : (2:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
  have hbpos : (0:ℝ) < (b:ℝ) := by linarith
  have htpos : 0 < |t| := abs_pos.mpr ht
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (8 * |t|) hb1
  set J : ℕ := 2*i+2 with hJdef
  have hpowmono : ∀ u v : ℕ, u ≤ v → (b:ℝ)^u ≤ (b:ℝ)^v := fun u v h =>
    pow_le_pow_right₀ hb1.le h
  have hbi : 8 * |t| ≤ (b:ℝ)^(1+i) := le_of_lt (lt_of_lt_of_le hi (hpowmono _ _ (by omega)))
  have hbiPos : (0:ℝ) < (b:ℝ)^(1+i) := by positivity
  have hbJPos : (0:ℝ) < (b:ℝ)^(1+J) := by positivity
  set A : ℝ := |t| / (2 * (b:ℝ)^(1+J)) with hAdef
  set B : ℝ := 2 * |t| / (b:ℝ)^(1+i) with hBdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hB4 : B ≤ 1/4 := by
    rw [hBdef, div_le_div_iff₀ hbiPos (by norm_num : (0:ℝ) < 4)]; linarith
  have hAB : A ≤ B := by
    rw [hAdef, hBdef, div_le_div_iff₀ (by positivity) hbiPos]
    have : (b:ℝ)^(1+i) ≤ (b:ℝ)^(1+J) := hpowmono _ _ (by omega)
    nlinarith
  set δ : ℝ := Real.sin (2 * Real.pi * A) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    have : 2 * Real.pi * A ≤ 2 * Real.pi * (1/4) := by nlinarith [hAB, hB4]
    linarith
  refine ⟨δ^2/4, by positivity, ?_⟩
  refine Filter.eventually_atTop.mpr ⟨p + q + J + 10, fun r hrb hr => ?_⟩
  obtain ⟨s, j, hslt, hs0, hij, hjJ, hpsa, hqcle, hqcne⟩ :=
    exists_pair_residue p q i r hp hq hpq hr (by omega)
  set a : ℕ := r - 1 - j with hadef
  set cc : ℕ := (q * s) % r with hccdef
  have hrpos : 0 < r := hr.pos
  have hcclt : cc < r := Nat.mod_lt _ hrpos
  have halt : a < r := by omega
  have hane : a ≠ cc := fun h => hqcne h.symm
  set m : ℕ := max a cc with hmdef
  set n : ℕ := min a cc with hndef
  have hnm : n < m := by
    rw [hmdef, hndef]; omega
  have hm1 : 1 ≤ m := by omega
  have hmi : m + 1 + i ≤ r := by
    rw [hmdef]; omega
  have hmJ : r ≤ m + 1 + J := by
    rw [hmdef]; omega
  -- the real estimates
  have hbr2 : (2:ℝ) ≤ (b:ℝ)^r := by
    calc (2:ℝ) = (2:ℝ)^1 := by norm_num
      _ ≤ (b:ℝ)^1 := by
          apply pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hb)
      _ ≤ (b:ℝ)^r := hpowmono _ _ (by omega)
  have hden : (0:ℝ) < (b:ℝ)^r - 1 := by linarith
  have hbrpos : (0:ℝ) < (b:ℝ)^r := by positivity
  have hbmpos : (0:ℝ) < (b:ℝ)^m := by positivity
  set R : ℝ := (b:ℝ)^m / (b:ℝ)^r with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hR1 : R ≤ 1/(b:ℝ)^(1+i) := by
    rw [hRdef, div_le_div_iff₀ hbrpos hbiPos]
    have : (b:ℝ)^m * (b:ℝ)^(1+i) = (b:ℝ)^(m+1+i) := by rw [← pow_add]; ring_nf
    rw [this, one_mul]
    exact hpowmono _ _ hmi
  have hR2 : 1/(b:ℝ)^(1+J) ≤ R := by
    rw [hRdef, div_le_div_iff₀ hbJPos hbrpos]
    have : (b:ℝ)^m * (b:ℝ)^(1+J) = (b:ℝ)^(m+1+J) := by rw [← pow_add]; ring_nf
    rw [one_mul, this]
    exact hpowmono _ _ hmJ
  set value : ℝ := ((b:ℝ)^a - (b:ℝ)^cc)/((b:ℝ)^r - 1) with hvdef
  have habs : |(b:ℝ)^a - (b:ℝ)^cc| = (b:ℝ)^m - (b:ℝ)^n := by
    rcases lt_or_gt_of_ne hane with h | h
    · have hmax : m = cc := by rw [hmdef]; omega
      have hmin : n = a := by rw [hndef]; omega
      rw [hmax, hmin, abs_of_neg (by
        have := pow_lt_pow_right₀ hb1 h; linarith)]
      ring
    · have hmax : m = a := by rw [hmdef]; omega
      have hmin : n = cc := by rw [hndef]; omega
      rw [hmax, hmin, abs_of_pos (by
        have := pow_lt_pow_right₀ hb1 h; linarith)]
  have hbn : (b:ℝ)^n ≤ (b:ℝ)^m / 2 := by
    have h1 : (b:ℝ)^n ≤ (b:ℝ)^(m-1) := hpowmono _ _ (by omega)
    have h2 : (2:ℝ) * (b:ℝ)^(m-1) ≤ (b:ℝ) * (b:ℝ)^(m-1) := by nlinarith [pow_pos hbpos (m-1), hb2R]
    have h3 : (b:ℝ) * (b:ℝ)^(m-1) = (b:ℝ)^m := by
      rw [← pow_succ']; congr 1; omega
    linarith
  have hvabs : |value| = ((b:ℝ)^m - (b:ℝ)^n)/((b:ℝ)^r - 1) := by
    rw [hvdef, abs_div, habs, abs_of_pos hden]
  have hvlow : R/2 ≤ |value| := by
    rw [hvabs, hRdef]
    rw [div_div, div_le_div_iff₀ (by positivity) hden]
    nlinarith [hbn, hbmpos, hbrpos, hbr2]
  have hvhigh : |value| ≤ 2*R := by
    rw [hvabs, hRdef]
    have hpn : (0:ℝ) < (b:ℝ)^n := by positivity
    rw [div_le_iff₀ hden]
    have key : 2*((b:ℝ)^m/(b:ℝ)^r)*((b:ℝ)^r-1) = 2*(b:ℝ)^m*((b:ℝ)^r-1)/(b:ℝ)^r := by
      field_simp
    rw [key, le_div_iff₀ hbrpos]
    nlinarith [hbmpos, hbrpos, hpn, hbr2]
  -- the argument of the `s`-th summand
  set arg : ℝ := t * value with hargdef
  have hargabs : |arg| = |t| * |value| := by rw [hargdef, abs_mul]
  have hA' : A ≤ |t| * R / 2 := by
    rw [hAdef, div_le_iff₀ (by positivity : (0:ℝ) < 2*(b:ℝ)^(1+J))]
    have h := hR2
    rw [div_le_iff₀ hbJPos] at h
    nlinarith [htpos, hbJPos, hRpos]
  have hB' : |t| * (2*R) ≤ B := by
    rw [hBdef, le_div_iff₀ hbiPos]
    have h := hR1
    rw [le_div_iff₀ hbiPos] at h
    nlinarith [htpos, hbiPos, hRpos]
  have hAarg : A ≤ |arg| := by
    rw [hargabs]
    nlinarith [hvlow, htpos, hA']
  have hargB : |arg| ≤ B := by
    rw [hargabs]
    nlinarith [hvhigh, htpos, hB']
  -- the separation
  have hyabs : |2 * Real.pi * arg| = 2 * Real.pi * |arg| := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  have hsep : δ ≤ ‖phase arg - 1‖ := by
    refine le_trans ?_ (abs_sin_le_norm_phase_sub_one arg)
    rw [hδdef]
    refine sin_le_abs_sin_of_le_abs (by positivity) ?_ ?_
    · rw [hyabs]; nlinarith [hAarg]
    · rw [hyabs]; nlinarith [hargB, hB4]
  -- identify the argument
  have hid : t * (primePeriodicTerm b r (p * s) - primePeriodicTerm b r (q * s)) = arg := by
    rw [primePeriodicTerm, primePeriodicTerm, if_pos hr, if_pos hr, hpsa, ← hccdef,
      div_sub_div_same, hargdef, hvdef]
  refine norm_pairLocalFactor_le_of_sep b t r p q hrpos hslt hs0 (mul_zero p) (mul_zero q)
    hδpos.le ?_
  rw [hid]; exact hsep


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
