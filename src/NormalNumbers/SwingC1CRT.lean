import NormalNumbers.SwingC1Periodic

/-!
# Model × decoupling: a finite splitting of a mean along a periodic factor

`SwingC1Periodic.lean` shows the `×b`-orbit of `G₄_b` is an explicit sum of `p`-periodic
functions of `n`.  Fixing a cut `P` and putting `Q = Π_{p ≤ P} p`, the orbit splits as a
`Q`-periodic part plus a large-prime remainder, and the character of a sum is a product:

`e(h θ_n) = A n · B n`,  `A` exactly `Q`-periodic,  `B` carried by the primes `> P`.

This file is the purely finite half of that decomposition.  For ANY `Q`-periodic `A` and any
bounded `B`,

`‖mean_{m < QR} A(m)B(m)‖ ≤ ‖mean of A over one period‖ + mean_c ‖(mean of B on c mod Q) − (mean of B)‖`

(`norm_fullMean_mul_le_periodMean_add_defect`).  So a mean of this shape vanishes as soon as

* **(M)** the *model* term `periodMean A Q → 0` — for the orbit this is a CRT product over the
  primes `≤ P` and is elementary (Mertens); and
* **(D)** the *decoupling* term — the large-prime part `B` is equidistributed in progressions to
  the small-prime modulus `Q`.

The point of the split is that (M) carries all of the randomness and is a theorem, while (D)
asks only that the large primes do not see the small-prime residues — a different statement from
the natural-density Elliott correlations that the `ω`-side localisation
(`corrSum_eq_elliott`) runs into.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-! ### Splitting a range into residue classes -/

/-- `range (Q*R)` is the disjoint union of the `Q` progressions `c + r·Q`, `r < R`. -/
theorem sum_range_mul_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) (Q R : ℕ) :
    ∑ m ∈ range (Q * R), f m = ∑ c ∈ range Q, ∑ r ∈ range R, f (c + r * Q) := by
  induction R with
  | zero => simp
  | succ R ih =>
      have hsplit : Q * (R + 1) = Q * R + Q := by ring
      have hIco : ∑ m ∈ Finset.Ico (Q * R) (Q * R + Q), f m = ∑ c ∈ range Q, f (c + R * Q) := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel_left]
        exact Finset.sum_congr rfl fun c _ => by rw [show Q * R + c = c + R * Q by ring]
      rw [hsplit, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive _ (Nat.zero_le (Q * R)) (Nat.le_add_right (Q * R) Q),
        ← Finset.range_eq_Ico, ih, hIco, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => (Finset.sum_range_succ _ R).symm

/-! ### The three means -/

/-- `mean_{m < n} f m`. -/
noncomputable def fullMean (f : ℕ → ℂ) (n : ℕ) : ℂ := (∑ m ∈ range n, f m) / n

/-- `Â₀`: the mean of a `Q`-periodic function over one period. -/
noncomputable def periodMean (A : ℕ → ℂ) (Q : ℕ) : ℂ := (∑ c ∈ range Q, A c) / Q

/-- `γ(c)`: the mean of `B` along the progression `c mod Q`, `R` terms. -/
noncomputable def progMean (B : ℕ → ℂ) (Q R c : ℕ) : ℂ := (∑ r ∈ range R, B (c + r * Q)) / R

lemma norm_fullMean_le_one (f : ℕ → ℂ) (n : ℕ) (hf : ∀ m, ‖f m‖ ≤ 1) :
    ‖fullMean f n‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [fullMean, h]
  · have hn : (0 : ℝ) < n := by exact_mod_cast h
    rw [fullMean, norm_div, Complex.norm_natCast, div_le_one hn]
    calc ‖∑ m ∈ range n, f m‖ ≤ ∑ m ∈ range n, ‖f m‖ := norm_sum_le _ _
      _ ≤ ∑ _m ∈ range n, (1 : ℝ) := Finset.sum_le_sum fun m _ => hf m
      _ = n := by simp

lemma norm_progMean_le_one (B : ℕ → ℂ) (Q R c : ℕ) (hB : ∀ m, ‖B m‖ ≤ 1) :
    ‖progMean B Q R c‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos R with h | h
  · simp [progMean, h]
  · have hR : (0 : ℝ) < R := by exact_mod_cast h
    rw [progMean, norm_div, Complex.norm_natCast, div_le_one hR]
    calc ‖∑ r ∈ range R, B (c + r * Q)‖ ≤ ∑ r ∈ range R, ‖B (c + r * Q)‖ := norm_sum_le _ _
      _ ≤ ∑ _r ∈ range R, (1 : ℝ) := Finset.sum_le_sum fun r _ => hB _
      _ = R := by simp

/-- The mean of `B` over `[0, QR)` is the mean over `c` of its progression means. -/
theorem fullMean_eq_periodMean_progMean (B : ℕ → ℂ) (Q R : ℕ) (hQ : 0 < Q) (hR : 0 < R) :
    fullMean B (Q * R) = periodMean (fun c => progMean B Q R c) Q := by
  have hQc : ((Q : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hRc : ((R : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [fullMean, periodMean, sum_range_mul_split B Q R]
  simp only [progMean]
  rw [← Finset.sum_div]
  push_cast
  field_simp

/-- With `A` periodic, the mean of `A·B` over `[0, QR)` is the period-mean of `A · γ`. -/
theorem fullMean_mul_eq_periodMean (A B : ℕ → ℂ) (Q R : ℕ) (hQ : 0 < Q) (hR : 0 < R)
    (hper : ∀ c r : ℕ, A (c + r * Q) = A c) :
    fullMean (fun m => A m * B m) (Q * R)
      = periodMean (fun c => A c * progMean B Q R c) Q := by
  have hQc : ((Q : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hRc : ((R : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [fullMean, periodMean, sum_range_mul_split (fun m => A m * B m) Q R]
  have hinner : ∀ c ∈ range Q, ∑ r ∈ range R, A (c + r * Q) * B (c + r * Q)
      = A c * ∑ r ∈ range R, B (c + r * Q) := by
    intro c _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [hper c r]
  rw [Finset.sum_congr rfl hinner]
  simp only [progMean]
  have hdiv : ∀ c ∈ range Q, A c * ((∑ r ∈ range R, B (c + r * Q)) / (R : ℂ))
      = (A c * ∑ r ∈ range R, B (c + r * Q)) / (R : ℂ) := fun c _ => by ring
  rw [Finset.sum_congr rfl hdiv, ← Finset.sum_div, div_div]
  push_cast
  ring

/-! ### The bound -/

/-- **Model × decoupling.**  For a `Q`-periodic `A` of modulus `≤ 1` and any `B` of modulus `≤ 1`,
the mean of `A·B` is controlled by the *model* term (the period mean of `A`) plus the
*decoupling defect* (the mean over residue classes of the deviation of `B`'s progression mean
from its overall mean).  Purely finite: no analysis, no arithmetic. -/
theorem norm_fullMean_mul_le_periodMean_add_defect
    (A B : ℕ → ℂ) (Q R : ℕ) (hQ : 0 < Q) (hR : 0 < R)
    (hper : ∀ c r : ℕ, A (c + r * Q) = A c)
    (hA : ∀ m, ‖A m‖ ≤ 1) (hB : ∀ m, ‖B m‖ ≤ 1) :
    ‖fullMean (fun m => A m * B m) (Q * R)‖
      ≤ ‖periodMean A Q‖
        + (∑ c ∈ range Q, ‖progMean B Q R c - fullMean B (Q * R)‖) / Q := by
  have hQc : ((Q : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  set β : ℂ := fullMean B (Q * R) with hβ
  have hβ1 : ‖β‖ ≤ 1 := norm_fullMean_le_one B _ hB
  -- the exact identity
  have hid : fullMean (fun m => A m * B m) (Q * R)
      = β * periodMean A Q + (∑ c ∈ range Q, A c * (progMean B Q R c - β)) / Q := by
    rw [fullMean_mul_eq_periodMean A B Q R hQ hR hper, periodMean, periodMean]
    have : ∀ c ∈ range Q, A c * progMean B Q R c = β * A c + A c * (progMean B Q R c - β) := by
      intro c _; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, add_div,
      mul_div_assoc]
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖β * periodMean A Q‖ ≤ ‖periodMean A Q‖ := by
    rw [norm_mul]
    nlinarith [norm_nonneg (periodMean A Q), norm_nonneg β]
  have h2 : ‖(∑ c ∈ range Q, A c * (progMean B Q R c - β)) / Q‖
      ≤ (∑ c ∈ range Q, ‖progMean B Q R c - β‖) / Q := by
    rw [norm_div, Complex.norm_natCast, div_le_div_iff_of_pos_right hQr]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [norm_mul]
    nlinarith [norm_nonneg (progMean B Q R c - β), hA c, norm_nonneg (A c)]
  linarith

/-! ### The CRT factorisation of a period mean

A function of `n` that is a product of factors each depending only on `n mod p`, `p` running
over pairwise-coprime moduli, has a period mean that FACTORISES.  This is the mechanism behind
leaf (M): over one full period the residues `(n mod p)_p` are jointly uniform.
-/

/-- **Two coprime moduli.**  `∑_{c < qQ} g(c mod q) h(c mod Q) = (∑_{a<q} g a)(∑_{b<Q} h b)`. -/
theorem sum_range_mul_mod_mul (q Q : ℕ) (hq : 0 < q) (hQ : 0 < Q) (hcop : Nat.Coprime q Q)
    (g h : ℕ → ℂ) :
    ∑ c ∈ range (q * Q), g (c % q) * h (c % Q)
      = (∑ a ∈ range q, g a) * (∑ b ∈ range Q, h b) := by
  have hqQ : 0 < q * Q := Nat.mul_pos hq hQ
  have hstep : ∑ c ∈ range (q * Q), g (c % q) * h (c % Q)
      = ∑ x ∈ (range q) ×ˢ (range Q), g x.1 * h x.2 := by
    refine Finset.sum_bij (fun c _ => (c % q, c % Q)) ?_ ?_ ?_ ?_
    · intro c _
      exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.mod_lt _ hq), Finset.mem_range.mpr (Nat.mod_lt _ hQ)⟩
    · intro c₁ h₁ c₂ h₂ heq
      rw [Finset.mem_range] at h₁ h₂
      have e1 : c₁ % q = c₂ % q := congrArg Prod.fst heq
      have e2 : c₁ % Q = c₂ % Q := congrArg Prod.snd heq
      have : c₁ % (q * Q) = c₂ % (q * Q) :=
        (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨e1, e2⟩
      rwa [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at this
    · intro x hx
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx
      obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop x.1 x.2
      refine ⟨k % (q * Q), Finset.mem_range.mpr (Nat.mod_lt _ hqQ), ?_⟩
      have d1 : k % (q * Q) % q = k % q := Nat.mod_mod_of_dvd k (Dvd.intro Q rfl)
      have d2 : k % (q * Q) % Q = k % Q := Nat.mod_mod_of_dvd k (Dvd.intro_left q rfl)
      have e1 : k % (q * Q) % q = x.1 := by
        rw [d1, hk1, Nat.mod_eq_of_lt hx.1]
      have e2 : k % (q * Q) % Q = x.2 := by
        rw [d2, hk2, Nat.mod_eq_of_lt hx.2]
      exact Prod.ext e1 e2
    · intro c _; rfl
  rw [hstep, Finset.sum_product, Finset.sum_mul_sum]

/-- **The CRT factorisation.**  For pairwise-coprime moduli `S`, a product of residue-functions
sums over one full period `∏_{p∈S} p` to the product of the individual residue sums. -/
theorem sum_range_prod_mod (f : ℕ → ℕ → ℂ) :
    ∀ (S : Finset ℕ), (∀ p ∈ S, 0 < p) → (S : Set ℕ).Pairwise Nat.Coprime →
      ∑ c ∈ range (∏ p ∈ S, p), ∏ p ∈ S, f p (c % p)
        = ∏ p ∈ S, ∑ s ∈ range p, f p s := by
  classical
  refine Finset.induction ?_ ?_
  · intro _ _; simp
  · intro q T hqT ih hpos hcop
    have hposT : ∀ p ∈ T, 0 < p := fun p hp => hpos p (Finset.mem_insert_of_mem hp)
    have hcopT : (T : Set ℕ).Pairwise Nat.Coprime :=
      Set.Pairwise.mono (by exact_mod_cast Finset.coe_subset.mpr (Finset.subset_insert q T)) hcop
    have hq : 0 < q := hpos q (Finset.mem_insert_self q T)
    set Q : ℕ := ∏ p ∈ T, p with hQdef
    have hQ : 0 < Q := Finset.prod_pos hposT
    have hqQ : Nat.Coprime q Q := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      exact hcop (Finset.mem_insert_self q T) (Finset.mem_insert_of_mem hp)
        (fun hEq => hqT (hEq ▸ hp))
    have hprod : ∏ p ∈ insert q T, p = q * Q := Finset.prod_insert hqT
    have hmod : ∀ c : ℕ, ∏ p ∈ insert q T, f p (c % p)
        = f q (c % q) * ∏ p ∈ T, f p ((c % Q) % p) := by
      intro c
      rw [Finset.prod_insert hqT]
      congr 1
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Nat.mod_mod_of_dvd c (Finset.dvd_prod_of_mem _ hp)]
    rw [hprod, Finset.sum_congr rfl (fun c _ => hmod c),
      sum_range_mul_mod_mul q Q hq hQ hqQ (fun a => f q a) (fun b => ∏ p ∈ T, f p (b % p)),
      ih hposT hcopT, Finset.prod_insert hqT]

end NormalNumbers.CastingOut
