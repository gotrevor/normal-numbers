/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3Split

/-!
# `G_b` as a rational plus the large-prime Lambert number

The small/large split of `ω` is a split of the *number*:

`G_b = S_P + L_P`,  `S_P = ∑_n ω_{≤P}(n) b^{−n}`,  `L_P = ∑_n ω_{>P}(n) b^{−n}`.

The point of this file is the pair of identities

* `fract_tailSmall_eq_orbit` : `fract (tailSmall P b n) = orbit b (smallLambert P b) n`
* `fract_tailLarge_eq_orbit` : `fract (tailLarge P b n) = orbit b (largeLambert P b) n`

so the "tails" of `SwingC3Split` are literally the `×b`-orbits of two real numbers, and

* `orbit_primeLambert_eq_fract_add` :
  `orbit b G_b n = fract (orbit b S_P n + orbit b L_P n)`.

`orbit b S_P` is `Q`-periodic (`SwingC3Split.tailSmall_congr`), and indeed `S_P` is **rational**:
`smallLambert_rat` exhibits `(b^Q − 1)·S_P` as an integer.  So the orbit of `G_b` is the orbit of
`L_P` rotated by one of `Q` constants, the constant depending only on `n mod Q`.

Two consequences that re-site the crux of `SwingC3Rotation.lean`:

* `orbit_largeLambert_succ` : `orbit b L_P (n+1) = fract (b · orbit b L_P n)` — the residue class
  `r+1` is the `×b` image of the class `r`.  So `TailLargeDecouple` (all classes carry the same
  empirical law) is *equivalent* to the statement that every weak limit of the `×b^Q`-empirical
  measures of `L_P` is `×b`-invariant.  It is a statement about one real number's orbit, and not
  about `ω mod b` (Selberg–Delange) or about `ω(n), ω(n+1)` jointly (Chowla).
* the prime-side form (recorded in `PENDING_WORK.md`, not yet formalised):
  `tailLarge P b n = ∑_{p > P} b^{−j₀(n,p)}/(1 − b^{−p})` with `j₀(n,p)` the least `j ≥ 1` with
  `p ∣ n+j`.  Each summand depends only on `n mod p`, and every such `p` is coprime to `Q`; that
  is why the finite-dimensional decoupling is exactly free.
-/

open Finset

namespace NormalNumbers

open PrimeLambert

/-! ### A generic Lambert number and its tails -/

/-- The Lambert-type number `∑_{n ≥ 0} f(n)·b^{−n}` for a digit source `f` dominated by `ω`. -/
noncomputable def lambertOf (b : ℕ) (f : ℕ → ℕ) : ℝ := ∑' n : ℕ, (f n : ℝ) / (b : ℝ) ^ n

/-- Its tail at `k`: `∑_{j ≥ 1} f(k+j)·b^{−j}`. -/
noncomputable def tailOf (b : ℕ) (f : ℕ → ℕ) (k : ℕ) : ℝ :=
  ∑' i : ℕ, (f (k + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)

/-- The integer head `∑_{m ≤ k} b^{k−m} f(m)`. -/
def tailIntOf (b : ℕ) (f : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ m ∈ range (k + 1), b ^ (k - m) * f m

variable {b : ℕ}

lemma summable_lambertOf (hb : 2 ≤ b) {f : ℕ → ℕ} (hf : ∀ n, (f n : ℝ) ≤ omegaR n) :
    Summable (fun n : ℕ => (f n : ℝ) / (b : ℝ) ^ n) := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by positivity
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_omegaR_div_pow hb)
  have : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  gcongr
  exact hf n

lemma summable_tailOf (hb : 2 ≤ b) {f : ℕ → ℕ} (hf : ∀ n, (f n : ℝ) ≤ omegaR n) (k : ℕ) :
    Summable (fun i : ℕ => (f (k + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (G4.summable_tailB hb k)
  have : (0 : ℝ) < (b : ℝ) ^ (i + 1) := by positivity
  gcongr
  exact hf _

/-- **`T_f(k) = b^k · L_f − (integer)`.**  Same computation as `G4Transport.tailB_eq`. -/
theorem tailOf_eq (hb : 2 ≤ b) {f : ℕ → ℕ} (hf : ∀ n, (f n : ℝ) ≤ omegaR n) (k : ℕ) :
    tailOf b f k = (b : ℝ) ^ k * lambertOf b f - tailIntOf b f k := by
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  have hs : Summable (fun n : ℕ => (b : ℝ) ^ k * ((f n : ℝ) / (b : ℝ) ^ n)) :=
    (summable_lambertOf hb hf).mul_left _
  have h := hs.sum_add_tsum_nat_add (k + 1)
  have hfin : ∑ i ∈ range (k + 1), (b : ℝ) ^ k * ((f i : ℝ) / (b : ℝ) ^ i)
      = tailIntOf b f k := by
    rw [tailIntOf]; push_cast
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hm' : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [pow_sub₀ (b : ℝ) hb0 hm']
    field_simp
  have htail : ∑' i : ℕ, (b : ℝ) ^ k * ((f (i + (k + 1)) : ℝ) / (b : ℝ) ^ (i + (k + 1)))
      = tailOf b f k := by
    rw [tailOf]
    refine tsum_congr (fun i => ?_)
    rw [show i + (k + 1) = k + i + 1 by ring, pow_add, pow_add]
    field_simp
    ring
  rw [lambertOf, ← tsum_mul_left, ← h, hfin, htail]
  ring

/-- **The tail is the orbit.** -/
theorem fract_tailOf (hb : 2 ≤ b) {f : ℕ → ℕ} (hf : ∀ n, (f n : ℝ) ≤ omegaR n) (k : ℕ) :
    Int.fract (tailOf b f k) = orbit b (lambertOf b f) k := by
  rw [tailOf_eq hb hf k, orbit, mul_comm]
  exact Int.fract_sub_natCast _ _

/-! ### The two halves -/

/-- `S_P = ∑_n ω_{≤P}(n) b^{−n}`, the small-prime Lambert number. -/
noncomputable def smallLambert (P b : ℕ) : ℝ := lambertOf b (omegaSmall P)

/-- `L_P = ∑_n ω_{>P}(n) b^{−n}`, the large-prime Lambert number. -/
noncomputable def largeLambert (P b : ℕ) : ℝ := lambertOf b (omegaLarge P)

lemma omegaSmall_le_omegaR (P n : ℕ) : (omegaSmall P n : ℝ) ≤ omegaR n := by
  have := omegaSmall_add_omegaLarge P n
  rw [omegaR]
  exact_mod_cast Nat.le.intro this

lemma omegaLarge_le_omegaR (P n : ℕ) : (omegaLarge P n : ℝ) ≤ omegaR n := by
  have := omegaSmall_add_omegaLarge P n
  rw [omegaR]
  refine Nat.cast_le.2 ?_
  omega

@[simp] lemma tailOf_omegaSmall (P k : ℕ) : tailOf b (omegaSmall P) k = tailSmall P b k := rfl

@[simp] lemma tailOf_omegaLarge (P k : ℕ) : tailOf b (omegaLarge P) k = tailLarge P b k := rfl

/-- **`fract (tailSmall) = orbit of `S_P`**. -/
theorem fract_tailSmall_eq_orbit (hb : 2 ≤ b) (P k : ℕ) :
    Int.fract (tailSmall P b k) = orbit b (smallLambert P b) k :=
  fract_tailOf hb (omegaSmall_le_omegaR P) k

/-- **`fract (tailLarge) = orbit of `L_P`** — the identity that re-sites the crux. -/
theorem fract_tailLarge_eq_orbit (hb : 2 ≤ b) (P k : ℕ) :
    Int.fract (tailLarge P b k) = orbit b (largeLambert P b) k :=
  fract_tailOf hb (omegaLarge_le_omegaR P) k

/-- **The number splits**: `G_b = S_P + L_P`. -/
theorem primeLambertAtBase_eq_add (hb : 2 ≤ b) (P : ℕ) :
    primeLambertAtBase b = smallLambert P b + largeLambert P b := by
  rw [smallLambert, largeLambert, lambertOf, lambertOf,
    ← Summable.tsum_add (summable_lambertOf hb (omegaSmall_le_omegaR P))
      (summable_lambertOf hb (omegaLarge_le_omegaR P)), primeLambertAtBase]
  refine tsum_congr fun n => ?_
  have hsum := omegaSmall_add_omegaLarge P n
  have : omegaR n = (omegaSmall P n : ℝ) + (omegaLarge P n : ℝ) := by
    rw [omegaR, ← Nat.cast_add, hsum]
  rw [this, add_div]

/-- `fract` of a sum of fractional parts. -/
lemma fract_add_fract (x y : ℝ) :
    Int.fract (Int.fract x + Int.fract y) = Int.fract (x + y) := by
  have h : Int.fract x + Int.fract y = (x + y) - ((⌊x⌋ + ⌊y⌋ : ℤ) : ℝ) := by
    rw [Int.fract, Int.fract]; push_cast; ring
  rw [h, Int.fract_sub_intCast]

/-- Rotating by a real and then taking `fract` sees only the fractional part. -/
lemma fract_add_fract_right (θ x : ℝ) : Int.fract (θ + Int.fract x) = Int.fract (θ + x) := by
  have h : θ + Int.fract x = (θ + x) - ((⌊x⌋ : ℤ) : ℝ) := by rw [Int.fract]; push_cast; ring
  rw [h, Int.fract_sub_intCast]

/-- **The orbit of `G_b` is a rotation of the orbit of `L_P`.** -/
theorem orbit_primeLambert_eq_fract_add (hb : 2 ≤ b) (P n : ℕ) :
    orbit b (primeLambertAtBase b) n
      = Int.fract (orbit b (smallLambert P b) n + orbit b (largeLambert P b) n) := by
  rw [← fract_tailSmall_eq_orbit hb, ← fract_tailLarge_eq_orbit hb, fract_add_fract,
    ← tailB_eq_small_add_large hb P n, ← orbit_eq_fract_tailB hb n]

/-- One step of the `×b` orbit: the residue class `r+1` is the `×b` image of the class `r`. -/
theorem orbit_succ_eq (b : ℕ) (x : ℝ) (n : ℕ) :
    orbit b x (n + 1) = Int.fract ((b : ℝ) * orbit b x n) := by
  unfold orbit
  have h : (b : ℝ) * Int.fract (x * (b : ℝ) ^ n)
      = x * (b : ℝ) ^ (n + 1) - ((b * ⌊x * (b : ℝ) ^ n⌋ : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [h, Int.fract_sub_intCast]


/-! ### `S_P` is rational, and its orbit is `Q`-periodic -/

/-- The orbit of `S_P` depends only on the class mod `Q`. -/
theorem orbit_smallLambert_congr (hb : 2 ≤ b) {P Q : ℕ} (hQ : ∀ p ≤ P, p.Prime → p ∣ Q)
    {n n' : ℕ} (h : n ≡ n' [MOD Q]) :
    orbit b (smallLambert P b) n = orbit b (smallLambert P b) n' := by
  rw [← fract_tailSmall_eq_orbit hb, ← fract_tailSmall_eq_orbit hb,
    tailSmall_congr (b := b) hQ h]

/-- **`S_P` is rational**: `(b^Q − 1)·S_P` is the natural number `∑_{m ≤ Q} b^{Q−m} ω_{≤P}(m)`.
The small-prime digit stream is purely periodic with period `Q`, so the number it defines has
denominator dividing `b^Q − 1`. -/
theorem smallLambert_rat (hb : 2 ≤ b) {P Q : ℕ} (hQ0 : 0 < Q) (hQ : ∀ p ≤ P, p.Prime → p ∣ Q) :
    ((b : ℝ) ^ Q - 1) * smallLambert P b = (tailIntOf b (omegaSmall P) Q : ℕ) := by
  have hzero : omegaSmall P 0 = 0 := by simp [omegaSmall]
  -- `tailOf … 0 = lambertOf …` because the `n = 0` digit vanishes
  have h0 : tailOf b (omegaSmall P) 0 = smallLambert P b := by
    rw [smallLambert, lambertOf, tailOf]
    rw [(summable_lambertOf hb (omegaSmall_le_omegaR P)).tsum_eq_zero_add]
    rw [hzero]
    simp
  -- periodicity: the tail at `Q` is the tail at `0`
  have hper : tailOf b (omegaSmall P) Q = tailOf b (omegaSmall P) 0 := by
    rw [tailOf, tailOf]
    refine tsum_congr fun i => ?_
    congr 2
    refine omegaSmall_congr_of_modEq (by omega) (by omega) hQ ?_
    have h1 : Q ≡ 0 [MOD Q] := (Nat.modEq_zero_iff_dvd).2 dvd_rfl
    simpa [Nat.add_assoc] using h1.add_right (i + 1)
  have hsm : smallLambert P b = lambertOf b (omegaSmall P) := rfl
  have heq := tailOf_eq hb (omegaSmall_le_omegaR P) (b := b) Q
  rw [hper, h0, ← hsm] at heq
  linear_combination -heq

end NormalNumbers
