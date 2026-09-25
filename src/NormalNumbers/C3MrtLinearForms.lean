/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtPowerfulSum

/-!
# From `ζ^ω` along a shift to `ζ^Ω` along linear forms

`C3MrtOmegaBridge` gives `z^{ω} = z^{Ω} ⋆ g` with `g = sqfW z` supported on the powerful
numbers, and `C3MrtPowerfulSum` shows `∑_d ‖g(d)‖/d < ∞`.  This file performs the actual
**substitution**: it rewrites a shifted `ζ^ω` average as a sum, over powerful moduli `d`, of
`ζ^Ω` averages along the **linear form** `k ↦ d k`.

The single-shift statement (`sum_pow_omega_shift_eq`) is

    ∑_{n < N} F(n) · z^{ω(n+1)}
      =  ∑_{d ≤ N}  g(d) · ∑_{1 ≤ k ≤ N/d}  F(dk − 1) · z^{Ω(k)} ,

with `g(d) = (z − z²)^{ω(d)}` on powerful `d` and `0` elsewhere.  The inner sum is a correlation
of the **completely multiplicative** `z^{Ω}` against the weight `F` restricted to the arithmetic
progression `n ≡ −1 (mod d)` — exactly the shape `Erdos67b.NonasymptoticLogElliott` is stated
for.  Taking `F(n) = e(jn/Q) ∏_{i≥1} ζ_i^{ω(n+1+i)}` and iterating over the `D` shifts turns the
`D`-point correlation into a `D`-fold tuple sum of `ζ^Ω` correlations along `D` linear forms;
`C3MrtPowerfulSum.summable_norm_sqfW_div` makes that tuple sum absolutely convergent, hence
truncatable at `d ≤ Y` uniformly in `N`.

The `g`-side is the transpose of the bridge (`pow_omegaNat_eq_sum_divisors'`): it is `g` that
carries the divisor, and `z^{Ω}` that carries the quotient — which is what puts the *linear
form* on the completely multiplicative factor.
-/

open Finset

namespace NormalNumbers

namespace CastingOut

/-- **Transposed bridge.**  `z^{ω(m)} = ∑_{d ∣ m} g(d) · z^{Ω(m/d)}` with `g = sqfW z`.
The transpose of `pow_omegaNat_eq_sum_divisors`; this is the orientation in which the
*completely multiplicative* factor receives the quotient `m/d`. -/
theorem pow_omegaNat_eq_sum_divisors' (z : ℂ) {m : ℕ} (hm : m ≠ 0) :
    z ^ omegaNat m = ∑ d ∈ m.divisors, sqfW z d * z ^ ArithmeticFunction.cardFactors (m / d) := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f m) (mul_comm (zOm z) (sqfW z) ▸
    zOm_mul_sqfW z)
  simp only [ArithmeticFunction.mul_apply] at h
  rw [Nat.sum_divisorsAntidiagonal (f := fun x y => sqfW z x * zOm z y)] at h
  rw [zom_apply hm] at h
  rw [← h]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdm := Nat.mem_divisors.1 hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hm (Nat.eq_zero_of_zero_dvd hdm.1)
  have hq0 : m / d ≠ 0 := Nat.div_ne_zero_iff.2 ⟨hd0, Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdm.1⟩
  rw [zOm_apply hq0]

/-- The divisors of `m` with `0 < m ≤ N` all lie in `range (N+1)`. -/
private lemma divisors_subset_range {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    m.divisors ⊆ range (N + 1) := by
  intro d hd
  have := Nat.le_of_dvd hm (Nat.mem_divisors.1 hd).1
  exact Finset.mem_range.2 (by omega)

/-- **Reindexing along the linear form.**  For `d ≥ 1`, the `n < N` with `d ∣ n+1` are exactly
`n = dk − 1` for `1 ≤ k ≤ N/d`. -/
theorem sum_over_progression_eq {d N : ℕ} (hd : 0 < d) (G : ℕ → ℂ) :
    ∑ n ∈ (range N).filter (fun n => d ∣ n + 1), G n
      = ∑ k ∈ Icc 1 (N / d), G (d * k - 1) := by
  refine Finset.sum_nbij' (i := fun n => (n + 1) / d) (j := fun k => d * k - 1) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, hdvd⟩ := hn
    have hk : 1 ≤ (n + 1) / d := Nat.one_le_div_iff hd |>.2 (Nat.le_of_dvd (by omega) hdvd)
    have hk2 : (n + 1) / d ≤ N / d := Nat.div_le_div_right (by omega)
    exact Finset.mem_Icc.2 ⟨hk, hk2⟩
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have hkN : d * k ≤ N := by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hd).1 hk.2
    have hpos : 1 ≤ d * k := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hd.ne' (by omega))
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have : d * k - 1 + 1 = d * k := by omega
    rw [this]
    exact Dvd.intro k rfl
  · intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨k, hk⟩ := hn.2
    rw [hk, Nat.mul_div_cancel_left _ hd]
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have hpos : 1 ≤ d * k := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hd.ne' (by omega))
    have : d * k - 1 + 1 = d * k := by omega
    rw [this, Nat.mul_div_cancel_left _ hd]
  · intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨k, hk⟩ := hn.2
    have : d * ((n + 1) / d) = n + 1 := by rw [hk, Nat.mul_div_cancel_left _ hd]
    rw [this, Nat.add_sub_cancel]

/-- **The substitution lemma.**  A shifted `z^{ω}` average is a sum, over powerful moduli `d`,
of `z^{Ω}` averages along the linear forms `k ↦ dk`. -/
theorem sum_pow_omega_shift_eq (z : ℂ) (F : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ range N, F n * z ^ omegaNat (n + 1)
      = ∑ d ∈ range (N + 1),
          sqfW z d * ∑ k ∈ Icc 1 (N / d), F (d * k - 1) * z ^ ArithmeticFunction.cardFactors k := by
  have step1 : ∀ n ∈ range N, F n * z ^ omegaNat (n + 1)
      = ∑ d ∈ range (N + 1),
          (if d ∣ n + 1 then sqfW z d * z ^ ArithmeticFunction.cardFactors ((n + 1) / d) else 0)
            * F n := by
    intro n hn
    rw [Finset.mem_range] at hn
    have hm : (n + 1) ≠ 0 := by omega
    have hsub : (n + 1).divisors ⊆ range (N + 1) :=
      divisors_subset_range (by omega) (by omega)
    have hfilter : (range (N + 1)).filter (fun d => d ∣ n + 1) = (n + 1).divisors := by
      ext d
      constructor
      · intro hd
        rw [Finset.mem_filter] at hd
        exact Nat.mem_divisors.2 ⟨hd.2, hm⟩
      · intro hd
        have hdvd := (Nat.mem_divisors.1 hd).1
        have : d ≤ n + 1 := Nat.le_of_dvd (by omega) hdvd
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hdvd⟩
    rw [← Finset.sum_mul, ← Finset.sum_filter, hfilter,
      pow_omegaNat_eq_sum_divisors' z hm, mul_comm]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · simp [sqfW]
  · rw [← Finset.sum_filter_add_sum_filter_not (range N) (fun n => d ∣ n + 1)]
    have hzero : ∑ n ∈ (range N).filter (fun n => ¬ d ∣ n + 1),
        (if d ∣ n + 1 then sqfW z d * z ^ ArithmeticFunction.cardFactors ((n + 1) / d) else 0)
          * F n = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      rw [Finset.mem_filter] at hn
      rw [if_neg hn.2, zero_mul]
    rw [hzero, add_zero]
    have hcongr : ∑ n ∈ (range N).filter (fun n => d ∣ n + 1),
        (if d ∣ n + 1 then sqfW z d * z ^ ArithmeticFunction.cardFactors ((n + 1) / d) else 0)
          * F n
        = ∑ n ∈ (range N).filter (fun n => d ∣ n + 1),
            sqfW z d * (F n * z ^ ArithmeticFunction.cardFactors ((n + 1) / d)) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_filter] at hn
      rw [if_pos hn.2]; ring
    rw [hcongr, ← Finset.mul_sum]
    congr 1
    rw [sum_over_progression_eq hdpos (fun n => F n * z ^ ArithmeticFunction.cardFactors ((n + 1) / d))]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    have hpos : 1 ≤ d * k := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hdpos.ne' (by omega))
    have hk1 : d * k - 1 + 1 = d * k := by omega
    rw [hk1, Nat.mul_div_cancel_left _ hdpos]

/-! ### The general form: arbitrary offset, arbitrary index set

For the `D`-point correlation each of the `D` shifts `n+1+i` must be expanded in turn, and the
`i`-th expansion happens *inside* the congruence conditions already imposed by the previous
ones.  So the general statement ranges `n` over an arbitrary `Finset` and the shift over an
arbitrary positive offset.
-/

/-- **Substitution, general form.**  For any finite index set `S` of `n`'s with `n + c ≤ B`,

    ∑_{n ∈ S} F(n) z^{ω(n+c)} = ∑_{d ≤ B} g(d) ∑_{n ∈ S, d ∣ n+c} F(n) z^{Ω((n+c)/d)} .

Since `S` is arbitrary, this may be applied repeatedly: the `i`-th application runs inside the
congruence conditions already imposed by the previous ones. -/
theorem sum_pow_omega_offset_eq (z : ℂ) (F : ℕ → ℂ) (S : Finset ℕ) (c B : ℕ) (hc : 0 < c)
    (hB : ∀ n ∈ S, n + c ≤ B) :
    ∑ n ∈ S, F n * z ^ omegaNat (n + c)
      = ∑ d ∈ range (B + 1),
          sqfW z d * ∑ n ∈ S.filter (fun n => d ∣ n + c),
            F n * z ^ ArithmeticFunction.cardFactors ((n + c) / d) := by
  have step1 : ∀ n ∈ S, F n * z ^ omegaNat (n + c)
      = ∑ d ∈ range (B + 1),
          (if d ∣ n + c then sqfW z d * z ^ ArithmeticFunction.cardFactors ((n + c) / d) else 0)
            * F n := by
    intro n hn
    have hm : (n + c) ≠ 0 := by omega
    have hfilter : (range (B + 1)).filter (fun d => d ∣ n + c) = (n + c).divisors := by
      ext d
      constructor
      · intro hd
        rw [Finset.mem_filter] at hd
        exact Nat.mem_divisors.2 ⟨hd.2, hm⟩
      · intro hd
        have hdvd := (Nat.mem_divisors.1 hd).1
        have hle : d ≤ n + c := Nat.le_of_dvd (by omega) hdvd
        have := hB n hn
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hdvd⟩
    rw [← Finset.sum_mul, ← Finset.sum_filter, hfilter,
      pow_omegaNat_eq_sum_divisors' z hm, mul_comm]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [← Finset.sum_filter_add_sum_filter_not S (fun n => d ∣ n + c)]
  have hzero : ∑ n ∈ S.filter (fun n => ¬ d ∣ n + c),
      (if d ∣ n + c then sqfW z d * z ^ ArithmeticFunction.cardFactors ((n + c) / d) else 0)
        * F n = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [Finset.mem_filter] at hn
    rw [if_neg hn.2, zero_mul]
  rw [hzero, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_filter] at hn
  rw [if_pos hn.2]
  ring

/-- **The `D = 2` substitution.**  Both shifts expanded: the double sum over the powerful
moduli `(d, e)` of a correlation of the completely multiplicative `z₀^{Ω}`, `z₁^{Ω}` restricted
to the joint progression `n ≡ −1 (mod d)`, `n ≡ −2 (mod e)` — which, after CRT on `lcm d e`,
is a two-point correlation along two linear forms.  This is the shape required by
`Erdos67b.NonasymptoticLogElliott` at two points. -/
theorem sum_pow_omega_two_shift_eq (z₀ z₁ : ℂ) (F : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ range N, F n * (z₀ ^ omegaNat (n + 1) * z₁ ^ omegaNat (n + 2))
      = ∑ d ∈ range (N + 2), ∑ e ∈ range (N + 3),
          sqfW z₀ d * sqfW z₁ e *
            ∑ n ∈ ((range N).filter (fun n => d ∣ n + 1)).filter (fun n => e ∣ n + 2),
              F n * (z₀ ^ ArithmeticFunction.cardFactors ((n + 1) / d) *
                z₁ ^ ArithmeticFunction.cardFactors ((n + 2) / e)) := by
  have hstep : ∑ n ∈ range N, (fun n => F n * z₁ ^ omegaNat (n + 2)) n * z₀ ^ omegaNat (n + 1)
      = ∑ d ∈ range (N + 2),
          sqfW z₀ d * ∑ n ∈ (range N).filter (fun n => d ∣ n + 1),
            (F n * z₁ ^ omegaNat (n + 2)) *
              z₀ ^ ArithmeticFunction.cardFactors ((n + 1) / d) :=
    sum_pow_omega_offset_eq z₀ (fun n => F n * z₁ ^ omegaNat (n + 2)) (range N) 1 (N + 1)
      one_pos (fun n hn => by rw [Finset.mem_range] at hn; omega)
  have hL : ∑ n ∈ range N, F n * (z₀ ^ omegaNat (n + 1) * z₁ ^ omegaNat (n + 2))
      = ∑ n ∈ range N, (fun n => F n * z₁ ^ omegaNat (n + 2)) n * z₀ ^ omegaNat (n + 1) := by
    refine Finset.sum_congr rfl fun n _ => by ring
  rw [hL, hstep]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hinner := sum_pow_omega_offset_eq z₁
    (fun n => F n * z₀ ^ ArithmeticFunction.cardFactors ((n + 1) / d))
    ((range N).filter (fun n => d ∣ n + 1)) 2 (N + 2) (by norm_num)
    (fun n hn => by rw [Finset.mem_filter, Finset.mem_range] at hn; omega)
  have hrw : ∑ n ∈ (range N).filter (fun n => d ∣ n + 1),
      (F n * z₁ ^ omegaNat (n + 2)) * z₀ ^ ArithmeticFunction.cardFactors ((n + 1) / d)
      = ∑ n ∈ (range N).filter (fun n => d ∣ n + 1),
        (fun n => F n * z₀ ^ ArithmeticFunction.cardFactors ((n + 1) / d)) n *
          z₁ ^ omegaNat (n + 2) := by
    refine Finset.sum_congr rfl fun n _ => by ring
  rw [hrw, hinner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mul_assoc, Finset.mul_sum]
  congr 1
  rw [← Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun n _ => by ring

/-! ### Only COPRIME tuples survive

A structural constraint that the `D = 1` case cannot see: the joint system `d ∣ n+1`,
`e ∣ n+2` forces `gcd(d, e) ∣ 1`.  So the double sum over powerful moduli is really a sum over
*coprime* powerful pairs — and for coprime `d, e` the joint condition is a single residue class
mod `d e`, which is what makes the CRT reindexing to two linear forms available.
-/

/-- The joint progression forces coprimality: `gcd(d,e) ∣ (n+2) − (n+1) = 1`. -/
theorem coprime_of_joint_progression {d e n : ℕ} (h1 : d ∣ n + 1) (h2 : e ∣ n + 2) :
    Nat.Coprime d e := by
  have hg1 : Nat.gcd d e ∣ n + 1 := (Nat.gcd_dvd_left d e).trans h1
  have hg2 : Nat.gcd d e ∣ n + 2 := (Nat.gcd_dvd_right d e).trans h2
  have hsub : Nat.gcd d e ∣ (n + 2) - (n + 1) := Nat.dvd_sub hg2 hg1
  have : Nat.gcd d e ∣ 1 := by simpa using hsub
  exact Nat.eq_one_of_dvd_one this

/-- Hence non-coprime pairs contribute nothing. -/
theorem joint_progression_eq_empty_of_not_coprime {d e N : ℕ} (h : ¬ Nat.Coprime d e) :
    ((range N).filter (fun n => d ∣ n + 1)).filter (fun n => e ∣ n + 2) = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun n hn => ?_
  rw [Finset.mem_filter, Finset.mem_filter] at hn
  exact h (coprime_of_joint_progression hn.1.2 hn.2)

/-- **The `D = 2` substitution, restricted to coprime moduli.**  The clean form: the correlation
is a sum over *coprime* powerful pairs `(d, e)`, for each of which the surviving `n` form a
single residue class mod `d e`. -/
theorem sum_pow_omega_two_shift_eq_coprime (z₀ z₁ : ℂ) (F : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ range N, F n * (z₀ ^ omegaNat (n + 1) * z₁ ^ omegaNat (n + 2))
      = ∑ d ∈ range (N + 2), ∑ e ∈ (range (N + 3)).filter (fun e => Nat.Coprime d e),
          sqfW z₀ d * sqfW z₁ e *
            ∑ n ∈ ((range N).filter (fun n => d ∣ n + 1)).filter (fun n => e ∣ n + 2),
              F n * (z₀ ^ ArithmeticFunction.cardFactors ((n + 1) / d) *
                z₁ ^ ArithmeticFunction.cardFactors ((n + 2) / e)) := by
  rw [sum_pow_omega_two_shift_eq z₀ z₁ F N]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_filter_add_sum_filter_not (range (N + 3)) (fun e => Nat.Coprime d e)]
  have hzero : ∑ e ∈ (range (N + 3)).filter (fun e => ¬ Nat.Coprime d e),
      sqfW z₀ d * sqfW z₁ e *
        ∑ n ∈ ((range N).filter (fun n => d ∣ n + 1)).filter (fun n => e ∣ n + 2),
          F n * (z₀ ^ ArithmeticFunction.cardFactors ((n + 1) / d) *
            z₁ ^ ArithmeticFunction.cardFactors ((n + 2) / e)) = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    rw [Finset.mem_filter] at he
    rw [joint_progression_eq_empty_of_not_coprime he.2, Finset.sum_empty, mul_zero]
  rw [hzero, add_zero]

/-! ### CRT: the joint progression is a single class, and the shifts become linear forms -/

/-- `d ∣ n + c` is a congruence condition on `n`, with representative `M − c` for any multiple
`M ≥ c` of `d`.  (Stated this way to avoid negative residues in `ℕ`.) -/
theorem dvd_add_iff_modEq {d n c M : ℕ} (hdM : d ∣ M) (hcM : c ≤ M) :
    d ∣ n + c ↔ n ≡ M - c [MOD d] := by
  have hMc : M - c + c = M := by omega
  constructor
  · intro h
    refine Nat.ModEq.add_right_cancel' c ?_
    rw [hMc]
    calc n + c ≡ 0 [MOD d] := (Nat.modEq_zero_iff_dvd).2 h
      _ ≡ M [MOD d] := ((Nat.modEq_zero_iff_dvd).2 hdM).symm
  · intro h
    have h' : n + c ≡ M - c + c [MOD d] := Nat.ModEq.add_right c h
    rw [hMc] at h'
    refine (Nat.modEq_zero_iff_dvd).1 ?_
    exact h'.trans ((Nat.modEq_zero_iff_dvd).2 hdM)

/-- **The joint progression is a single residue class.**  For coprime `d, e > 0` there is a
single `a < de` with `(d ∣ n+1 ∧ e ∣ n+2) ↔ n ≡ a (mod de)`, and `a` itself satisfies the two
divisibilities.  Coprimality is necessary as well as sufficient
(`coprime_of_joint_progression`). -/
theorem exists_joint_class {d e : ℕ} (hd : 0 < d) (he : 0 < e) (hco : Nat.Coprime d e) :
    ∃ a : ℕ, a < d * e ∧ d ∣ a + 1 ∧ e ∣ a + 2 ∧
      ∀ n : ℕ, (d ∣ n + 1 ∧ e ∣ n + 2) ↔ n % (d * e) = a := by
  set M := 2 * (d * e) with hM
  have hde : 0 < d * e := Nat.mul_pos hd he
  have hdM : d ∣ M := Dvd.dvd.mul_left (Dvd.intro e rfl) 2
  have heM : e ∣ M := Dvd.dvd.mul_left (Dvd.intro_left d rfl) 2
  have hM2 : 2 ≤ M := by omega
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hco (M - 1) (M - 2)
  set a := k % (d * e) with ha
  have hak : a ≡ k [MOD d * e] := Nat.mod_modEq k (d * e)
  have hakd : a ≡ k [MOD d] := hak.of_dvd (Dvd.intro e rfl)
  have hake : a ≡ k [MOD e] := hak.of_dvd (Dvd.intro_left d rfl)
  have hjoint : ∀ n : ℕ, (d ∣ n + 1 ∧ e ∣ n + 2) ↔ n ≡ a [MOD d * e] := by
    intro n
    constructor
    · rintro ⟨h1, h2⟩
      rw [dvd_add_iff_modEq hdM (by omega)] at h1
      rw [dvd_add_iff_modEq heM (by omega)] at h2
      exact (Nat.modEq_and_modEq_iff_modEq_mul hco).1
        ⟨(h1.trans hk1.symm).trans hakd.symm, (h2.trans hk2.symm).trans hake.symm⟩
    · intro h
      obtain ⟨hd', he'⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hco).2 h
      exact ⟨(dvd_add_iff_modEq hdM (by omega)).2 ((hd'.trans hakd).trans hk1),
        (dvd_add_iff_modEq heM (by omega)).2 ((he'.trans hake).trans hk2)⟩
  have hamod : a % (d * e) = a := Nat.mod_eq_of_lt (Nat.mod_lt _ hde)
  refine ⟨a, Nat.mod_lt _ hde, ?_, ?_, fun n => ?_⟩
  · exact ((hjoint a).2 (by rfl)).1
  · exact ((hjoint a).2 (by rfl)).2
  · rw [hjoint n]
    unfold Nat.ModEq
    rw [hamod]

/-- Reindexing a residue class by its progression variable. -/
theorem sum_over_class_eq {L a N : ℕ} (hL : 0 < L) (haL : a < L) (G : ℕ → ℂ) :
    ∑ n ∈ (range N).filter (fun n => n % L = a), G n
      = ∑ j ∈ (range N).filter (fun j => L * j + a < N), G (L * j + a) := by
  refine Finset.sum_nbij' (i := fun n => (n - a) / L) (j := fun j => L * j + a) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, hmod⟩ := hn
    have hage : a ≤ n := hmod ▸ Nat.mod_le n L
    have hdvd : L ∣ n - a := by
      have : n % L = a % L := by rw [hmod, Nat.mod_eq_of_lt haL]
      exact (Nat.modEq_iff_dvd' hage).1 this.symm
    have hrec : L * ((n - a) / L) + a = n := by
      rw [Nat.mul_div_cancel' hdvd]; omega
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · have : (n - a) / L ≤ n - a := Nat.div_le_self _ _
      omega
    · omega
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hj.2, ?_⟩
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt haL
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, hmod⟩ := hn
    have hage : a ≤ n := hmod ▸ Nat.mod_le n L
    have hdvd : L ∣ n - a := by
      have : n % L = a % L := by rw [hmod, Nat.mod_eq_of_lt haL]
      exact (Nat.modEq_iff_dvd' hage).1 this.symm
    rw [Nat.mul_div_cancel' hdvd]
    omega
  · intro j hj
    rw [Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hL]
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, hmod⟩ := hn
    have hage : a ≤ n := hmod ▸ Nat.mod_le n L
    have hdvd : L ∣ n - a := by
      have : n % L = a % L := by rw [hmod, Nat.mod_eq_of_lt haL]
      exact (Nat.modEq_iff_dvd' hage).1 this.symm
    have : L * ((n - a) / L) + a = n := by rw [Nat.mul_div_cancel' hdvd]; omega
    rw [this]

/-- **The shifts become linear forms.**  On the class `n = (de)j + a`, the argument of the
completely multiplicative factor is an honest linear form in the progression variable `j`:
`(n+1)/d = e j + (a+1)/d`. -/
theorem shift_div_eq_linear (d e a j : ℕ) (hd : 0 < d) :
    (d * e * j + a + 1) / d = e * j + (a + 1) / d := by
  have : d * e * j + a + 1 = (a + 1) + d * (e * j) := by ring
  rw [this, Nat.add_mul_div_left _ _ hd, Nat.add_comm]

/-- Its companion for the second shift: `(n+2)/e = d j + (a+2)/e`. -/
theorem shift_div_eq_linear' (d e a j : ℕ) (he : 0 < e) :
    (d * e * j + a + 2) / e = d * j + (a + 2) / e := by
  have : d * e * j + a + 2 = (a + 2) + e * (d * j) := by ring
  rw [this, Nat.add_mul_div_left _ _ he, Nat.add_comm]

/-- **The `D = 2` inner sum, as a two-point correlation along two linear forms.**

For coprime `d, e > 0` the joint progression collapses to `n = (de)j + a`, and on it the two
completely multiplicative factors are evaluated at the **linear forms** `e j + (a+1)/d` and
`d j + (a+2)/e`.  This is precisely the hypothesis shape of `Erdos67b.NonasymptoticLogElliott`
at two points: two completely multiplicative unimodular functions along two linear forms in a
single progression variable. -/
theorem inner_sum_linear_forms {d e : ℕ} (hd : 0 < d) (he : 0 < e) (hco : Nat.Coprime d e)
    (z₀ z₁ : ℂ) (F : ℕ → ℂ) (N : ℕ) :
    ∃ a : ℕ, a < d * e ∧ d ∣ a + 1 ∧ e ∣ a + 2 ∧
      ∑ n ∈ ((range N).filter (fun n => d ∣ n + 1)).filter (fun n => e ∣ n + 2),
          F n * (z₀ ^ ArithmeticFunction.cardFactors ((n + 1) / d) *
            z₁ ^ ArithmeticFunction.cardFactors ((n + 2) / e))
        = ∑ j ∈ (range N).filter (fun j => d * e * j + a < N),
            F (d * e * j + a) *
              (z₀ ^ ArithmeticFunction.cardFactors (e * j + (a + 1) / d) *
                z₁ ^ ArithmeticFunction.cardFactors (d * j + (a + 2) / e)) := by
  obtain ⟨a, haL, hda, hea, hclass⟩ := exists_joint_class hd he hco
  refine ⟨a, haL, hda, hea, ?_⟩
  have hfil : ((range N).filter (fun n => d ∣ n + 1)).filter (fun n => e ∣ n + 2)
      = (range N).filter (fun n => n % (d * e) = a) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, and_assoc]
    constructor
    · rintro ⟨hn, h1, h2⟩
      exact ⟨hn, (hclass n).1 ⟨h1, h2⟩⟩
    · rintro ⟨hn, h⟩
      obtain ⟨h1, h2⟩ := (hclass n).2 h
      exact ⟨hn, h1, h2⟩
  rw [hfil, sum_over_class_eq (Nat.mul_pos hd he) haL]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [shift_div_eq_linear d e a j hd, shift_div_eq_linear' d e a j he]

/-! ### Truncating the modulus at `d ≤ Y`, uniformly in `N` -/

/-- The tail of the bridge weight beyond `Y`. -/
noncomputable def bridgeTail (z : ℂ) (Y : ℕ) : ℝ :=
  ∑' d : {d : ℕ // d ∉ range (Y + 1)}, ‖sqfW z d.val‖ / (d.val : ℝ)

lemma bridgeTail_nonneg (z : ℂ) (Y : ℕ) : 0 ≤ bridgeTail z Y :=
  tsum_nonneg fun _ => by positivity

/-- The tail vanishes as `Y → ∞` (this is where `summable_norm_sqfW_div` is spent). -/
theorem bridgeTail_tendsto (z : ℂ) :
    Filter.Tendsto (bridgeTail z) Filter.atTop (nhds 0) := by
  have hcomp := tendsto_tsum_compl_atTop_zero (fun d : ℕ => ‖sqfW z d‖ / (d : ℝ))
  exact hcomp.comp (Filter.tendsto_finset_range.comp (Filter.tendsto_add_atTop_nat 1))

/-- **Uniform truncation.**  Cutting the modulus at `d ≤ Y` costs at most `N · (tail beyond Y)`,
with a tail independent of `N`.  Together with `bridgeTail_tendsto` this makes the
`ζ^ω → ζ^Ω`-along-linear-forms substitution usable inside a density statement: pick `Y` from
`ε`, then let `N → ∞`. -/
theorem bridge_truncation_bound (z : ℂ) (hz : ‖z‖ = 1) (F : ℕ → ℂ) (hF : ∀ n, ‖F n‖ ≤ 1)
    (Y N : ℕ) :
    ‖(∑ n ∈ range N, F n * z ^ omegaNat (n + 1))
        - ∑ d ∈ range (Y + 1),
            sqfW z d * ∑ k ∈ Icc 1 (N / d), F (d * k - 1) * z ^ ArithmeticFunction.cardFactors k‖
      ≤ (N : ℝ) * bridgeTail z Y := by
  set T : ℕ → ℂ := fun d =>
    sqfW z d * ∑ k ∈ Icc 1 (N / d), F (d * k - 1) * z ^ ArithmeticFunction.cardFactors k with hT
  set M := max N Y with hM
  rw [sum_pow_omega_shift_eq z F N]
  -- extend the first sum to `range (M+1)`: the new terms vanish
  have hext : ∑ d ∈ range (N + 1), T d = ∑ d ∈ range (M + 1), T d := by
    refine Finset.sum_subset (by
      intro d hd
      rw [Finset.mem_range] at hd ⊢
      omega) ?_
    intro d hd hd'
    rw [Finset.mem_range] at hd hd'
    have hdN : N < d := by omega
    have : N / d = 0 := Nat.div_eq_of_lt hdN
    simp [hT, this]
  have hsubY : range (Y + 1) ⊆ range (M + 1) := by
    intro d hd; rw [Finset.mem_range] at hd ⊢; omega
  have hdiff : (∑ d ∈ range (N + 1), T d) - ∑ d ∈ range (Y + 1), T d
      = ∑ d ∈ range (M + 1) \ range (Y + 1), T d := by
    rw [hext, ← Finset.sum_sdiff hsubY]
    ring
  rw [hdiff]
  -- termwise bound
  have hterm : ∀ d ∈ range (M + 1) \ range (Y + 1),
      ‖T d‖ ≤ (N : ℝ) * (‖sqfW z d‖ / (d : ℝ)) := by
    intro d hd
    rw [Finset.mem_sdiff, Finset.mem_range] at hd
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · exact absurd (Finset.mem_range.2 (by omega)) hd.2
      · exact h
    have hinner : ‖∑ k ∈ Icc 1 (N / d), F (d * k - 1) * z ^ ArithmeticFunction.cardFactors k‖
        ≤ ((N / d : ℕ) : ℝ) := by
      refine le_trans (norm_sum_le _ _) ?_
      have hle : ∀ k ∈ Icc 1 (N / d),
          ‖F (d * k - 1) * z ^ ArithmeticFunction.cardFactors k‖ ≤ 1 := by
        intro k _
        rw [norm_mul, norm_pow, hz, one_pow, mul_one]
        exact hF _
      calc ∑ k ∈ Icc 1 (N / d), ‖F (d * k - 1) * z ^ ArithmeticFunction.cardFactors k‖
          ≤ ∑ _k ∈ Icc 1 (N / d), (1 : ℝ) := Finset.sum_le_sum hle
        _ = ((N / d : ℕ) : ℝ) := by
            rw [Finset.sum_const, Nat.card_Icc]
            simp
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    have hdiv : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
    calc ‖T d‖ = ‖sqfW z d‖ *
          ‖∑ k ∈ Icc 1 (N / d), F (d * k - 1) * z ^ ArithmeticFunction.cardFactors k‖ := by
          rw [hT, norm_mul]
      _ ≤ ‖sqfW z d‖ * ((N : ℝ) / (d : ℝ)) := by
          refine mul_le_mul_of_nonneg_left (hinner.trans hdiv) (norm_nonneg _)
      _ = (N : ℝ) * (‖sqfW z d‖ / (d : ℝ)) := by ring
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N)
  -- compare the finite sum with the tail tsum
  have hsummable : Summable fun d : {d : ℕ // d ∉ range (Y + 1)} => ‖sqfW z d.val‖ / (d.val : ℝ) :=
    (summable_norm_sqfW_div z hz).subtype _
  classical
  have hfilter : (range (M + 1) \ range (Y + 1)).filter (fun d => d ∉ range (Y + 1))
      = range (M + 1) \ range (Y + 1) :=
    Finset.filter_true_of_mem (fun d hd => (Finset.mem_sdiff.1 hd).2)
  have hsub := Finset.sum_subtype_eq_sum_filter (s := range (M + 1) \ range (Y + 1))
      (p := fun d : ℕ => d ∉ range (Y + 1)) (f := fun d : ℕ => ‖sqfW z d‖ / (d : ℝ))
  rw [hfilter] at hsub
  rw [← hsub]
  exact hsummable.sum_le_tsum _ (fun _ _ => by positivity)

/-! ### The harmonic-weighted truncation bound

`bridge_truncation_bound` costs `N · bridgeTail(Y)`, which is useless against a *log-averaged*
main term of size `log N`.  The fix is to make the cost proportional to the **mass the weight
puts on the progression**: for a weight `u` with `∑_{k ≤ N/d} u(dk−1) ≤ B/d` the truncation
error is `B · bridgeTail(Y)`.  The flat weight gives `B = N`; the harmonic weight `1/n` gives
`B = 1 + log N`, which is the right size against a log-averaged main term.

The `1/d` in the mass hypothesis is not an extra assumption but the automatic gain of summing a
weight along a progression of modulus `d` — and it is exactly the `1/d` that `bridgeTail`
already carries.
-/

/-- **Truncation bound, weighted form.**  If the weight puts mass at most `B/d` on the
progression of modulus `d`, then cutting the modulus at `d ≤ Y` costs at most
`B · bridgeTail(Y)`. -/
theorem bridge_truncation_bound_of_mass (z : ℂ) (hz : ‖z‖ = 1) (F : ℕ → ℂ) (Y N : ℕ) (B : ℝ)
    (hmass : ∀ d : ℕ, 0 < d → ∑ k ∈ Icc 1 (N / d), ‖F (d * k - 1)‖ ≤ B / (d : ℝ)) :
    ‖(∑ n ∈ range N, F n * z ^ omegaNat (n + 1))
        - ∑ d ∈ range (Y + 1),
            sqfW z d * ∑ k ∈ Icc 1 (N / d), F (d * k - 1) * z ^ ArithmeticFunction.cardFactors k‖
      ≤ B * bridgeTail z Y := by
  have hB : 0 ≤ B := by
    have h := hmass 1 one_pos
    have h0 : (0 : ℝ) ≤ ∑ k ∈ Icc 1 (N / 1), ‖F (1 * k - 1)‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    simpa using h0.trans h
  set T : ℕ → ℂ := fun d =>
    sqfW z d * ∑ k ∈ Icc 1 (N / d), F (d * k - 1) * z ^ ArithmeticFunction.cardFactors k with hT
  set M := max N Y with hM
  rw [sum_pow_omega_shift_eq z F N]
  have hext : ∑ d ∈ range (N + 1), T d = ∑ d ∈ range (M + 1), T d := by
    refine Finset.sum_subset (by intro d hd; rw [Finset.mem_range] at hd ⊢; omega) ?_
    intro d hd hd'
    rw [Finset.mem_range] at hd hd'
    have : N / d = 0 := Nat.div_eq_of_lt (by omega)
    simp [hT, this]
  have hsubY : range (Y + 1) ⊆ range (M + 1) := by
    intro d hd; rw [Finset.mem_range] at hd ⊢; omega
  have hdiff : (∑ d ∈ range (N + 1), T d) - ∑ d ∈ range (Y + 1), T d
      = ∑ d ∈ range (M + 1) \ range (Y + 1), T d := by
    rw [hext, ← Finset.sum_sdiff hsubY]; ring
  rw [hdiff]
  have hterm : ∀ d ∈ range (M + 1) \ range (Y + 1),
      ‖T d‖ ≤ B * (‖sqfW z d‖ / (d : ℝ)) := by
    intro d hd
    rw [Finset.mem_sdiff, Finset.mem_range] at hd
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · exact absurd (Finset.mem_range.2 (by omega)) hd.2
      · exact h
    have hinner : ‖∑ k ∈ Icc 1 (N / d), F (d * k - 1) * z ^ ArithmeticFunction.cardFactors k‖
        ≤ B / (d : ℝ) := by
      refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum ?_) (hmass d hd0))
      intro k _
      rw [norm_mul, norm_pow, hz, one_pow, mul_one]
    calc ‖T d‖ = ‖sqfW z d‖ *
          ‖∑ k ∈ Icc 1 (N / d), F (d * k - 1) * z ^ ArithmeticFunction.cardFactors k‖ := by
          rw [hT, norm_mul]
      _ ≤ ‖sqfW z d‖ * (B / (d : ℝ)) := mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
      _ = B * (‖sqfW z d‖ / (d : ℝ)) := by ring
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hB
  have hsummable : Summable fun d : {d : ℕ // d ∉ range (Y + 1)} => ‖sqfW z d.val‖ / (d.val : ℝ) :=
    (summable_norm_sqfW_div z hz).subtype _
  classical
  have hfilter : (range (M + 1) \ range (Y + 1)).filter (fun d => d ∉ range (Y + 1))
      = range (M + 1) \ range (Y + 1) :=
    Finset.filter_true_of_mem (fun d hd => (Finset.mem_sdiff.1 hd).2)
  have hsub := Finset.sum_subtype_eq_sum_filter (s := range (M + 1) \ range (Y + 1))
      (p := fun d : ℕ => d ∉ range (Y + 1)) (f := fun d : ℕ => ‖sqfW z d‖ / (d : ℝ))
  rw [hfilter] at hsub
  rw [← hsub]
  exact hsummable.sum_le_tsum _ (fun _ _ => by positivity)

/-- **The harmonic weight satisfies the mass hypothesis with `B = 1 + log N`.**
`∑_{k ≤ N/d} 1/(dk) = H_{⌊N/d⌋}/d ≤ (1 + log N)/d`. -/
theorem harmonic_mass_bound {F : ℕ → ℂ} (hF : ∀ n : ℕ, ‖F n‖ ≤ ((n : ℝ) + 1)⁻¹) (N : ℕ) :
    ∀ d : ℕ, 0 < d → ∑ k ∈ Icc 1 (N / d), ‖F (d * k - 1)‖ ≤ (1 + Real.log N) / (d : ℝ) := by
  intro d hd
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hstep : ∀ k ∈ Icc 1 (N / d), ‖F (d * k - 1)‖ ≤ (1 / (d : ℝ)) * ((k : ℝ))⁻¹ := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk1 : 1 ≤ k := hk.1
    have hdk : 1 ≤ d * k := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hd.ne' (by omega))
    have hcast : ((d * k - 1 : ℕ) : ℝ) + 1 = (d : ℝ) * (k : ℝ) := by
      have : (d * k - 1 : ℕ) + 1 = d * k := by omega
      have h2 : (((d * k - 1 : ℕ) + 1 : ℕ) : ℝ) = ((d * k : ℕ) : ℝ) := by rw [this]
      push_cast at h2 ⊢
      linarith [h2]
    refine (hF _).trans ?_
    rw [hcast]
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    rw [one_div, ← mul_inv]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  have hharm : ∑ k ∈ Icc 1 (N / d), ((k : ℝ))⁻¹ ≤ 1 + Real.log N := by
    have h1 : ∑ k ∈ Icc 1 (N / d), ((k : ℝ))⁻¹ = ((harmonic (N / d) : ℚ) : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rfl
    rw [h1]
    refine (harmonic_le_one_add_log (N / d)).trans ?_
    have hle : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.div_le_self N d
    rcases Nat.eq_zero_or_pos (N / d) with h0 | h0
    · rw [h0]
      simp [hlogN]
    · have : Real.log ((N / d : ℕ) : ℝ) ≤ Real.log N :=
        Real.log_le_log (by exact_mod_cast h0) hle
      linarith
  calc (1 / (d : ℝ)) * ∑ k ∈ Icc 1 (N / d), ((k : ℝ))⁻¹
      ≤ (1 / (d : ℝ)) * (1 + Real.log N) := by
        refine mul_le_mul_of_nonneg_left hharm (by positivity)
    _ = (1 + Real.log N) / (d : ℝ) := by ring

end CastingOut

end NormalNumbers

-- axiom audit
#print axioms NormalNumbers.CastingOut.sum_pow_omega_shift_eq
#print axioms NormalNumbers.CastingOut.bridge_truncation_bound
#print axioms NormalNumbers.CastingOut.bridgeTail_tendsto
#print axioms NormalNumbers.CastingOut.sum_pow_omega_offset_eq
#print axioms NormalNumbers.CastingOut.sum_pow_omega_two_shift_eq_coprime
#print axioms NormalNumbers.CastingOut.exists_joint_class
#print axioms NormalNumbers.CastingOut.inner_sum_linear_forms
#print axioms NormalNumbers.CastingOut.bridge_truncation_bound_of_mass
#print axioms NormalNumbers.CastingOut.harmonic_mass_bound
