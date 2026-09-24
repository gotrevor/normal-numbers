/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3AddChar

/-!
# The closed form of the large-prime tail

The crux of the swing is `AddCharTail b`: for `0 < j < Q` and `h ≠ 0`,

`(1/N) ∑_{n<N} e(jn/Q) · e(h · tailLarge P b n) → 0`.

`tailLarge P b n = ∑_{i≥0} ω_{>P}(n+i+1) b^{−(i+1)}` is defined by a *vertical* sum over the
window slots.  Counting the pairs `(i, p)` with `p > P` prime and `p ∣ n+i+1` in the other
order collapses the inner sum to a geometric series and gives the **closed form**

    tailLarge P b n  =  ∑_{p > P prime}  b^{n mod p} / (b^p − 1).

This is the structural fact the crux needs: the large-prime tail is a sum of functions each of
which is **periodic with a prime period `p > P`**, while the twisting character `e(jn/Q)` has
period `Q` built only from primes `≤ P`.  Every period in sight is coprime to `Q`; the
correlation the crux asserts to vanish is therefore a genuinely "independent" one, and no
single term can conspire with the character.

(Sanity: at `n = 0` this is the classical Lambert identity `∑_m ω(m) b^{−m} = ∑_p 1/(b^p − 1)`
restricted to `p > P`.)
-/

open Finset

namespace NormalNumbers

open PrimeLambert

/-- The `p`-th term of the closed form: `b^{n mod p}/(b^p − 1)`.  Manifestly periodic in `n`
with period `p`. -/
noncomputable def tailPrimeTerm (b p n : ℕ) : ℝ := (b : ℝ) ^ (n % p) / ((b : ℝ) ^ p - 1)

/-- **The term is `p`-periodic in `n`.** -/
theorem tailPrimeTerm_congr {b p n n' : ℕ} (h : n ≡ n' [MOD p]) :
    tailPrimeTerm b p n = tailPrimeTerm b p n' := by
  rw [tailPrimeTerm, tailPrimeTerm, h]

/-- The double family counting the pairs `(i, p)` with `p > P` prime dividing `n + i + 1`. -/
private noncomputable def cellTail (b P n : ℕ) (i p : ℕ) : ℝ :=
  if P < p ∧ p.Prime ∧ p ∣ (n + i + 1) then ((b : ℝ) ^ (i + 1))⁻¹ else 0

/-- **The closed form of the large-prime tail.** -/
theorem tailLarge_eq_tsum {b : ℕ} (hb : 2 ≤ b) (P n : ℕ) :
    tailLarge P b n = ∑' p : ℕ, (if P < p ∧ p.Prime then tailPrimeTerm b p n else 0) := by
  classical
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  set f : ℕ → ℕ → ℝ := cellTail b P n with hf
  have hf0 : ∀ i p, 0 ≤ f i p := by
    intro i p; rw [hf, cellTail]; split_ifs
    · positivity
    · exact le_rfl
  -- rows: finitely supported on the large prime factors of `n + i + 1`
  have hrowsupp : ∀ i : ℕ, ∀ p ∉ (n + i + 1).primeFactors.filter (fun p => ¬ p ≤ P), f i p = 0 := by
    intro i p hp
    have hc : ¬ (P < p ∧ p.Prime ∧ p ∣ (n + i + 1)) := by
      rintro ⟨h1, h2, h3⟩
      exact hp (Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨h2, h3, by omega⟩, by omega⟩)
    simp only [hf, cellTail]; exact if_neg hc
  have hrowS : ∀ i, Summable (f i) := fun i => summable_of_ne_finset_zero (hrowsupp i)
  have hrow : ∀ i, ∑' p, f i p = (omegaLarge P (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1) := by
    intro i
    rw [tsum_eq_sum (hrowsupp i)]
    have hval : ∀ p ∈ (n + i + 1).primeFactors.filter (fun p => ¬ p ≤ P),
        f i p = ((b : ℝ) ^ (i + 1))⁻¹ := by
      intro p hp
      simp only [Finset.mem_filter, Nat.mem_primeFactors] at hp
      simp only [hf, cellTail]
      exact if_pos ⟨by omega, hp.1.1, hp.1.2.1⟩
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul, ← omegaLarge, div_eq_mul_inv]
  -- columns: a geometric series in the residue class `i + 1 ≡ −n (mod p)`
  have hcolS : ∀ p, Summable (fun i => f i p) := by
    intro p
    refine Summable.of_nonneg_of_le (fun i => hf0 i p) (fun i => ?_)
      (((summable_geometric_of_lt_one (r := (b : ℝ)⁻¹) (by positivity)
        (by rw [inv_lt_one_iff₀]; right; linarith)).mul_left ((b : ℝ)⁻¹)).congr
        (fun i => by rw [← pow_succ']))
    simp only [hf, cellTail]
    split_ifs
    · rw [← inv_pow]
    · positivity
  have hcol : ∀ p : ℕ, ∑' i, f i p = if P < p ∧ p.Prime then tailPrimeTerm b p n else 0 := by
    intro p
    by_cases hp : P < p ∧ p.Prime
    · rw [if_pos hp]
      obtain ⟨hPp, hpp⟩ := hp
      have hp0 : 0 < p := hpp.pos
      set d : ℕ := p - n % p with hd
      have hmod : n % p < p := Nat.mod_lt _ hp0
      have hdvdn : n - n % p = p * (n / p) := by
        have := Nat.div_add_mod n p; omega
      have hd1 : 1 ≤ d := by omega
      have hdp : d + n % p = p := by omega
      have hbp : (1 : ℝ) < (b : ℝ) ^ p := one_lt_pow₀ (by linarith) (by omega)
      set r : ℝ := ((b : ℝ) ^ p)⁻¹ with hrdef
      have hr0 : 0 < r := by rw [hrdef]; positivity
      have hr1 : r < 1 := by rw [hrdef, inv_lt_one_iff₀]; right; exact hbp
      have hgeo0 : HasSum (fun k : ℕ => r ^ k) (1 - r)⁻¹ := hasSum_geometric_of_lt_one hr0.le hr1
      have hval : ((b : ℝ) ^ d)⁻¹ * (1 - r)⁻¹ = tailPrimeTerm b p n := by
        have hne : ((b : ℝ) ^ p - 1) ≠ 0 := by intro hc; rw [sub_eq_zero] at hc; linarith
        have hbd : (0 : ℝ) < (b : ℝ) ^ d := by positivity
        have hsplit : (b : ℝ) ^ d * (b : ℝ) ^ (n % p) = (b : ℝ) ^ p := by
          rw [← pow_add, hdp]
        rw [tailPrimeTerm, hrdef]
        field_simp
        nlinarith [hsplit, hbd]
      have hgeo : HasSum (fun k : ℕ => ((b : ℝ) ^ d)⁻¹ * r ^ k) (tailPrimeTerm b p n) := by
        rw [← hval]; exact hgeo0.mul_left _
      have hinj : Function.Injective (fun k : ℕ => d - 1 + k * p) := by
        intro k1 k2 hk
        simp only [add_right_inj] at hk
        exact Nat.eq_of_mul_eq_mul_right hp0 hk
      have hzero : ∀ i ∉ Set.range (fun k : ℕ => d - 1 + k * p), f i p = 0 := by
        intro i hi
        have hc : ¬ (P < p ∧ p.Prime ∧ p ∣ (n + i + 1)) := by
          rintro ⟨-, -, hdvd⟩
          obtain ⟨c, hc⟩ := hdvd
          refine hi ⟨c - (n / p) - 1, ?_⟩
          simp only
          have h1 := Nat.div_add_mod n p
          have h2 : p * (n / p) < p * c := by omega
          have h3 : n / p < c := lt_of_mul_lt_mul_left h2 (Nat.zero_le p)
          have h4 : (c - (n / p) - 1) * p + (n / p + 1) * p = c * p := by
            rw [← add_mul]; congr 1; omega
          have h5 : (n / p + 1) * p = p * (n / p) + p := by ring
          have h6 : c * p = p * c := mul_comm c p
          omega
        simp only [hf, cellTail]; exact if_neg hc
      have hcomp : ∀ k : ℕ, f (d - 1 + k * p) p = ((b : ℝ) ^ d)⁻¹ * r ^ k := by
        intro k
        have hdvd : p ∣ (n + (d - 1 + k * p) + 1) := by
          have h1 := Nat.div_add_mod n p
          refine ⟨n / p + 1 + k, ?_⟩
          have h2 : p * (n / p + 1 + k) = p * (n / p) + p + p * k := by ring
          have h3 : k * p = p * k := mul_comm k p
          omega
        simp only [hf, cellTail]
        rw [if_pos ⟨hPp, hpp, hdvd⟩, hrdef, inv_pow, ← pow_mul, ← mul_inv, ← pow_add]
        have h3 : k * p = p * k := mul_comm k p
        congr 2
        omega
      have hHS : HasSum (fun i => f i p) (tailPrimeTerm b p n) :=
        (Function.Injective.hasSum_iff (f := fun i => f i p) hinj hzero).1
          (hgeo.congr_fun (fun k => hcomp k))
      exact hHS.tsum_eq
    · rw [if_neg hp]
      have hz : ∀ i, f i p = 0 := by
        intro i
        simp only [hf, cellTail]
        exact if_neg (fun hc => hp ⟨hc.1, hc.2.1⟩)
      simp [hz]
  have huncurry : Summable (Function.uncurry f) := by
    have huc : Function.uncurry f = fun x : ℕ × ℕ => f x.1 x.2 := rfl
    rw [huc, summable_prod_of_nonneg (fun x => hf0 x.1 x.2)]
    exact ⟨fun i => hrowS i, Summable.congr (summable_tailLarge hb P n) (fun i => (hrow i).symm)⟩
  calc tailLarge P b n = ∑' i, ∑' p, f i p := by
        rw [tailLarge]; exact tsum_congr fun i => (hrow i).symm
    _ = ∑' p, ∑' i, f i p := (huncurry.tsum_comm' hrowS hcolS).symm
    _ = _ := tsum_congr hcol

/-! ### Free truncation: the tail beyond `K` is exponentially small once `K > n`

The `loglog` obstruction (`DIRECTION.md`: `E[∑_{p>K} c_p] ≍ loglog N − loglog K`) is a statement
about the *mean over `n < N`* of the discarded mass, and it bites only for `K ≤ N`.  Pointwise
the closed form gives something much stronger: `n mod p = n` as soon as `p > n`, so the `p`-term
is `≤ 2 b^{n−p}` and the whole tail beyond `K` is `≤ 2 b^{n−K}`.  So for a sum over `n < N`,
truncating at `K = 2N` is FREE — the price of the truncation is not accuracy but the *period*
`∏_{P<p≤2N} p` of the truncated function.  This pins exactly where the difficulty lives. -/

/-- The summand of the closed form, as a function of `p` alone. -/
noncomputable def tailPrimeSummand (b P n p : ℕ) : ℝ :=
  if P < p ∧ p.Prime then tailPrimeTerm b p n else 0

theorem tailPrimeSummand_nonneg {b : ℕ} (hb : 2 ≤ b) (P n p : ℕ) :
    0 ≤ tailPrimeSummand b P n p := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  rw [tailPrimeSummand]
  split_ifs with hp
  · have hp2 : 2 ≤ p := hp.2.two_le
    have : (1 : ℝ) < (b : ℝ) ^ p := one_lt_pow₀ (by linarith) (by omega)
    rw [tailPrimeTerm]
    positivity
  · exact le_rfl

/-- **The geometric majorant.**  `b^{n mod p}/(b^p − 1) ≤ 2 b^n (1/b)^p`. -/
theorem tailPrimeSummand_le {b : ℕ} (hb : 2 ≤ b) (P n p : ℕ) :
    tailPrimeSummand b P n p ≤ 2 * (b : ℝ) ^ n * ((b : ℝ)⁻¹) ^ p := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  rw [tailPrimeSummand]
  split_ifs with hp
  · have hp2 : 2 ≤ p := hp.2.two_le
    have hbp : (2 : ℝ) ≤ (b : ℝ) ^ p := by
      calc (2:ℝ) ≤ (b:ℝ) ^ 1 := by simpa using hbR
        _ ≤ (b:ℝ) ^ p := pow_le_pow_right₀ (by linarith) (by omega)
    have hnum : (b : ℝ) ^ (n % p) ≤ (b : ℝ) ^ n :=
      pow_le_pow_right₀ (by linarith) (Nat.mod_le n p)
    have hden : (0:ℝ) < (b : ℝ) ^ p - 1 := by linarith
    have hhalf : (b : ℝ) ^ p / 2 ≤ (b : ℝ) ^ p - 1 := by linarith
    have hpos : (0:ℝ) < (b : ℝ) ^ p / 2 := by linarith
    rw [tailPrimeTerm, inv_pow]
    calc (b : ℝ) ^ (n % p) / ((b : ℝ) ^ p - 1)
        ≤ (b : ℝ) ^ n / ((b : ℝ) ^ p / 2) := by gcongr
      _ = 2 * (b : ℝ) ^ n * ((b : ℝ) ^ p)⁻¹ := by field_simp
  · positivity

theorem summable_tailPrimeSummand {b : ℕ} (hb : 2 ≤ b) (P n : ℕ) :
    Summable (tailPrimeSummand b P n) := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  refine Summable.of_nonneg_of_le (fun p => tailPrimeSummand_nonneg hb P n p)
    (fun p => tailPrimeSummand_le hb P n p) ?_
  exact ((summable_geometric_of_lt_one (r := (b : ℝ)⁻¹) (by positivity)
    (by rw [inv_lt_one_iff₀]; right; linarith)).mul_left _)

theorem tailLarge_eq_tsum' {b : ℕ} (hb : 2 ≤ b) (P n : ℕ) :
    tailLarge P b n = ∑' p : ℕ, tailPrimeSummand b P n p :=
  tailLarge_eq_tsum hb P n

/-- **Free truncation.**  Cutting the closed form off at `K` loses a nonnegative amount that is
at most `2 b^{n−K}` — exponentially small as soon as `K` exceeds `n`.  (The `loglog N` tail
obstruction is about the MEAN over `n < N` with `K ≤ N`; pointwise there is no obstruction.) -/
theorem tailLarge_sub_truncate_mem_Icc {b : ℕ} (hb : 2 ≤ b) (P n K : ℕ) :
    tailLarge P b n - ∑ p ∈ Finset.range (K + 1), tailPrimeSummand b P n p
      ∈ Set.Icc (0 : ℝ) (2 * (b : ℝ) ^ n / (b : ℝ) ^ K) := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hS := summable_tailPrimeSummand hb P n
  have hsplit := hS.sum_add_tsum_nat_add (K + 1)
  have hkey : tailLarge P b n - ∑ p ∈ Finset.range (K + 1), tailPrimeSummand b P n p
      = ∑' i : ℕ, tailPrimeSummand b P n (i + (K + 1)) := by
    rw [tailLarge_eq_tsum' hb P n, ← hsplit]; ring
  rw [hkey]
  constructor
  · exact tsum_nonneg (fun i => tailPrimeSummand_nonneg hb P n _)
  · have hgeo : Summable (fun i : ℕ => 2 * (b : ℝ) ^ n * ((b : ℝ)⁻¹) ^ (i + (K + 1))) := by
      refine ((summable_geometric_of_lt_one (r := (b : ℝ)⁻¹) (by positivity)
        (by rw [inv_lt_one_iff₀]; right; linarith)).mul_left
          (2 * (b : ℝ) ^ n * ((b : ℝ)⁻¹) ^ (K + 1))).congr (fun i => ?_)
      rw [pow_add]; ring
    have hle : ∑' i : ℕ, tailPrimeSummand b P n (i + (K + 1))
        ≤ ∑' i : ℕ, 2 * (b : ℝ) ^ n * ((b : ℝ)⁻¹) ^ (i + (K + 1)) :=
      Summable.tsum_le_tsum (fun i => tailPrimeSummand_le hb P n _)
        (hS.comp_injective (add_left_injective (K + 1))) hgeo
    refine hle.trans ?_
    have hval : ∑' i : ℕ, 2 * (b : ℝ) ^ n * ((b : ℝ)⁻¹) ^ (i + (K + 1))
        = 2 * (b : ℝ) ^ n * ((b : ℝ)⁻¹) ^ (K + 1) * (1 - (b : ℝ)⁻¹)⁻¹ := by
      rw [show (fun i : ℕ => 2 * (b : ℝ) ^ n * ((b : ℝ)⁻¹) ^ (i + (K + 1)))
          = fun i : ℕ => (2 * (b : ℝ) ^ n * ((b : ℝ)⁻¹) ^ (K + 1)) * ((b : ℝ)⁻¹) ^ i from
        funext fun i => by rw [pow_add]; ring]
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity)
        (by rw [inv_lt_one_iff₀]; right; linarith)]
    rw [hval]
    have hb1 : (1:ℝ) ≤ (b : ℝ) - 1 := by linarith
    have hLHS : 2 * (b : ℝ) ^ n * ((b : ℝ)⁻¹) ^ (K + 1) * (1 - (b : ℝ)⁻¹)⁻¹
        = 2 * (b : ℝ) ^ n / ((b : ℝ) ^ K * ((b : ℝ) - 1)) := by
      rw [inv_pow, pow_succ]
      have hbne : (b : ℝ) ≠ 0 := by linarith
      have hbne1 : (b : ℝ) - 1 ≠ 0 := by linarith
      have hbK : ((b : ℝ) ^ K) ≠ 0 := by positivity
      field_simp
    rw [hLHS, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (pow_pos hb0 n) (pow_pos hb0 K), pow_pos hb0 n, pow_pos hb0 K]

/-- The truncation, written as a sum over the primes in `(P, K]`. -/
theorem sum_tailPrimeSummand_range (b P n K : ℕ) :
    ∑ p ∈ Finset.range (K + 1), tailPrimeSummand b P n p
      = ∑ p ∈ (Finset.Ioc P K).filter Nat.Prime, tailPrimeTerm b p n := by
  classical
  have hsub : Finset.Ioc P K ⊆ Finset.range (K + 1) := by
    intro p hp
    simp only [Finset.mem_Ioc] at hp
    simp only [Finset.mem_range]
    omega
  rw [← Finset.sum_subset hsub, Finset.sum_filter]
  · exact Finset.sum_congr rfl fun p hp => by
      simp only [Finset.mem_Ioc] at hp
      rw [tailPrimeSummand]
      by_cases hpp : p.Prime
      · rw [if_pos ⟨hp.1, hpp⟩, if_pos hpp]
      · rw [if_neg (fun hc => hpp hc.2), if_neg hpp]
  · intro p hp hnot
    simp only [Finset.mem_range] at hp
    simp only [Finset.mem_Ioc] at hnot
    rw [tailPrimeSummand, if_neg]
    rintro ⟨h1, -⟩
    exact hnot ⟨h1, by omega⟩

end NormalNumbers
