/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtRungTwo

/-!
# The two-shift truncation: cutting BOTH moduli

`C3MrtLinearForms` proves the truncation bound `bridge_truncation_bound_of_mass` for the
*one-shift* expansion: cutting the modulus at `d ≤ Y` costs `B · bridgeTail(Y)` when the weight
puts mass `≤ B/d` on each progression.  The `D = 2` rung expands twice, so it needs the same
bound in the generality of `sum_pow_omega_offset_eq`: an arbitrary finite index set `S` and an
arbitrary offset `c`.  That generality is what makes the bound *iterable*, because the second
expansion runs inside the congruence condition the first one imposed.

* `offset_truncation_bound_of_mass` — the general-`S`, general-`c` truncation bound.
* `two_shift_truncation_bound` — both moduli cut, by applying it twice.  The cost is
  `B · (bridgeTail z₀ Y + bridgeTail z₁ Y)`, with `B` the same harmonic mass `1 + log N` in
  both applications: the inner sums inherit the `1/(n+1)` weight of the original variable, so
  no mass is lost between the two expansions.

Both `bridgeTail`s tend to `0` (`bridgeTail_tendsto`) **independently of `N`**, which is the
whole point: `Y` is chosen from `ε` before `N → ∞`.
-/

open Finset

namespace NormalNumbers

namespace CastingOut

open scoped Classical in
/-- **Truncation bound, general index set and offset.**  The `S = range N`, `c = 1` case is
`bridge_truncation_bound_of_mass`; the generality is what lets the bound be applied a second
time inside the congruence condition the first expansion imposed. -/
theorem offset_truncation_bound_of_mass (z : ℂ) (hz : ‖z‖ = 1) (F : ℕ → ℂ)
    (S : Finset ℕ) (c : ℕ) (hc : 0 < c) (D : ℕ) (hD : ∀ n ∈ S, n + c ≤ D)
    (Y : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hmass : ∀ d : ℕ, 0 < d →
      ∑ n ∈ S.filter (fun n => d ∣ n + c), ‖F n‖ ≤ B / (d : ℝ)) :
    ‖(∑ n ∈ S, F n * z ^ omegaNat (n + c))
        - ∑ d ∈ range (Y + 1), sqfW z d *
            ∑ n ∈ S.filter (fun n => d ∣ n + c),
              F n * z ^ ArithmeticFunction.cardFactors ((n + c) / d)‖
      ≤ B * bridgeTail z Y := by
  classical
  set T : ℕ → ℂ := fun d => sqfW z d *
    ∑ n ∈ S.filter (fun n => d ∣ n + c),
      F n * z ^ ArithmeticFunction.cardFactors ((n + c) / d) with hT
  set M := max D Y with hM
  rw [sum_pow_omega_offset_eq z F S c D hc hD]
  -- extend to `range (M+1)`: for `d > D` the progression is empty
  have hext : ∑ d ∈ range (D + 1), T d = ∑ d ∈ range (M + 1), T d := by
    refine Finset.sum_subset (by intro d hd; rw [Finset.mem_range] at hd ⊢; omega) ?_
    intro d hd hd'
    rw [Finset.mem_range] at hd hd'
    have hempty : S.filter (fun n => d ∣ n + c) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun n hn => ?_
      obtain ⟨hnS, hdvd⟩ := Finset.mem_filter.1 hn
      have h1 : d ≤ n + c := Nat.le_of_dvd (by omega) hdvd
      have h2 : n + c ≤ D := hD n hnS
      omega
    simp [hT, hempty]
  have hsubY : range (Y + 1) ⊆ range (M + 1) := by
    intro d hd; rw [Finset.mem_range] at hd ⊢; omega
  have hdiff : (∑ d ∈ range (D + 1), T d) - ∑ d ∈ range (Y + 1), T d
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
    have hinner : ‖∑ n ∈ S.filter (fun n => d ∣ n + c),
        F n * z ^ ArithmeticFunction.cardFactors ((n + c) / d)‖ ≤ B / (d : ℝ) := by
      refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum ?_) (hmass d hd0))
      intro n _
      rw [norm_mul, norm_pow, hz, one_pow, mul_one]
    calc ‖T d‖ = ‖sqfW z d‖ * ‖∑ n ∈ S.filter (fun n => d ∣ n + c),
          F n * z ^ ArithmeticFunction.cardFactors ((n + c) / d)‖ := by rw [hT, norm_mul]
      _ ≤ ‖sqfW z d‖ * (B / (d : ℝ)) := mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
      _ = B * (‖sqfW z d‖ / (d : ℝ)) := by ring
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hB
  have hsummable : Summable fun d : {d : ℕ // d ∉ range (Y + 1)} => ‖sqfW z d.val‖ / (d.val : ℝ) :=
    (summable_norm_sqfW_div z hz).subtype _
  have hfilter : (range (M + 1) \ range (Y + 1)).filter (fun d => d ∉ range (Y + 1))
      = range (M + 1) \ range (Y + 1) :=
    Finset.filter_true_of_mem (fun d hd => (Finset.mem_sdiff.1 hd).2)
  have hsub := Finset.sum_subtype_eq_sum_filter (s := range (M + 1) \ range (Y + 1))
      (p := fun d : ℕ => d ∉ range (Y + 1)) (f := fun d : ℕ => ‖sqfW z d‖ / (d : ℝ))
  rw [hfilter] at hsub
  rw [← hsub]
  exact hsummable.sum_le_tsum _ (fun _ _ => by positivity)


/-! ## The harmonic mass on an arbitrary progression

`harmonic_mass_bound` (`C3MrtLinearForms`) computes the mass on the progression `n + 1 ≡ 0
(mod d)` by reindexing to `n = dk − 1`.  The second expansion needs the same estimate for the
offset `c = 2` and, crucially, for an *arbitrary* subset of `range N` — the set the first
expansion left behind.  Injecting `n ↦ (n + c)/e` into `Icc 1 ((M + c)/e)` does it, at the cost
of the harmless factor `c` coming from `(n+1)⁻¹ ≤ c·(n+c)⁻¹`.
-/

open scoped Classical in
/-- **Harmonic mass on a progression, in the generality the second expansion needs.**  Any
subset of `range M`, any offset `c ≥ 1`, any modulus `e ≥ 1`. -/
theorem progression_harmonic_mass {F : ℕ → ℂ} (hF : ∀ n : ℕ, ‖F n‖ ≤ ((n : ℝ) + 1)⁻¹)
    {S : Finset ℕ} {M : ℕ} (hS : ∀ n ∈ S, n < M) {c : ℕ} (hc : 0 < c) {e : ℕ} (he : 0 < e) :
    ∑ n ∈ S.filter (fun n => e ∣ n + c), ‖F n‖
      ≤ (c : ℝ) * (1 + Real.log (M + c)) / (e : ℝ) := by
  classical
  set T := S.filter (fun n => e ∣ n + c) with hTdef
  set K := (M + c) / e with hK
  set φ : ℕ → ℕ := fun n => (n + c) / e with hφ
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  -- each element of `T` has `n + c = e · φ n` with `1 ≤ φ n ≤ K`
  have hmul : ∀ n ∈ T, e * φ n = n + c := by
    intro n hn
    exact Nat.mul_div_cancel' (Finset.mem_filter.1 hn).2
  have hmem : ∀ n ∈ T, φ n ∈ Finset.Icc 1 K := by
    intro n hn
    obtain ⟨hnS, _⟩ := Finset.mem_filter.1 hn
    have h1 : 1 ≤ φ n := by
      rcases Nat.eq_zero_or_pos (φ n) with h | h
      · have := hmul n hn; rw [h, mul_zero] at this; omega
      · exact h
    have h2 : φ n ≤ K := by
      rw [hφ, hK]
      exact Nat.div_le_div_right (by have := hS n hnS; omega)
    exact Finset.mem_Icc.2 ⟨h1, h2⟩
  have hinj : Set.InjOn φ (T : Set ℕ) := by
    intro m hm n hn hmn
    have h1 := hmul m (Finset.mem_coe.1 hm)
    have h2 := hmul n (Finset.mem_coe.1 hn)
    rw [hmn] at h1
    omega
  -- termwise: `‖F n‖ ≤ (c/e) · (φ n)⁻¹`
  have hstep : ∀ n ∈ T, ‖F n‖ ≤ ((c : ℝ) / (e : ℝ)) * ((φ n : ℝ))⁻¹ := by
    intro n hn
    have hpos : (0 : ℝ) < (φ n : ℝ) := by
      have := (Finset.mem_Icc.1 (hmem n hn)).1
      exact_mod_cast this
    have hcast : (e : ℝ) * (φ n : ℝ) = (n : ℝ) + c := by
      have h := hmul n hn
      have h2 : ((e * φ n : ℕ) : ℝ) = ((n + c : ℕ) : ℝ) := by rw [h]
      push_cast at h2 ⊢
      linarith
    have hkey : ((n : ℝ) + 1)⁻¹ ≤ (c : ℝ) / ((n : ℝ) + c) := by
      have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have heq : ((c : ℝ) / (e : ℝ)) * ((φ n : ℝ))⁻¹ = (c : ℝ) / ((e : ℝ) * (φ n : ℝ)) := by
      field_simp
    rw [heq, hcast]
    exact (hF n).trans hkey
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  have himg : ∑ n ∈ T, ((φ n : ℝ))⁻¹ = ∑ m ∈ T.image φ, ((m : ℝ))⁻¹ :=
    (Finset.sum_image (f := fun m : ℕ => ((m : ℝ))⁻¹) hinj).symm
  rw [himg]
  have hsub : T.image φ ⊆ Finset.Icc 1 K := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hm
    exact hmem n hn
  have hharm : ∑ m ∈ T.image φ, ((m : ℝ))⁻¹ ≤ 1 + Real.log (M + c) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun m _ _ => by positivity)) ?_
    have h1 : ∑ m ∈ Finset.Icc 1 K, ((m : ℝ))⁻¹ = ((harmonic K : ℚ) : ℝ) := by
      rw [harmonic_eq_sum_Icc]; push_cast; rfl
    rw [h1]
    refine (harmonic_le_one_add_log K).trans ?_
    have hle : ((K : ℕ) : ℝ) ≤ ((M + c : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_le_self (M + c) e
    have hlog : (0 : ℝ) ≤ Real.log ((M + c : ℕ) : ℝ) := Real.log_natCast_nonneg _
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · rw [show ((K : ℕ) : ℝ) = 0 by rw [h0]; norm_num, Real.log_zero]
      push_cast at hlog ⊢
      linarith
    · have : Real.log ((K : ℕ) : ℝ) ≤ Real.log ((M + c : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast h0) hle
      push_cast at this ⊢
      linarith
  calc ((c : ℝ) / (e : ℝ)) * ∑ m ∈ T.image φ, ((m : ℝ))⁻¹
      ≤ ((c : ℝ) / (e : ℝ)) * (1 + Real.log (M + c)) :=
        mul_le_mul_of_nonneg_left hharm (by positivity)
    _ = (c : ℝ) * (1 + Real.log (M + c)) / (e : ℝ) := by ring


/-! ## The harmonic mass on a residue class, with the FULL modulus gain

`progression_harmonic_mass` gives the gain `1/e` of one divisibility condition.  The two-shift
error needs the gain of BOTH conditions at once, `1/(de)`, because the outer sum over `d ≤ Y`
carries no decay of its own: `∑_{d ≤ Y} ‖sqfW z₀ d‖ ≍ Y^{1/2}` while `bridgeTail z₁ Y ≍
Y^{-1/2}`, so their product is `O(1)` — not `o(1)`.  Only the weighted sum
`∑_d ‖sqfW z₀ d‖/d`, which converges, is small enough.

The joint condition `d ∣ n+1 ∧ e ∣ n+2` is a single class `a (mod de)` (`exists_joint_class`),
so the mass is `(a+1)⁻¹ + (1 + log M)/(de)`: the `j = 0` term of the class, plus the harmonic
tail with the full modulus.  The head is NOT `O(1/(de))` — `a` can be as small as `≍ d` — but
`a + 2 ≥ e` bounds it by `2/e`, and `2/e` summed against `‖sqfW z₁ e‖` over `e > Y` is an
`N`-independent constant, which the quantifier order `ε → Y → A → i₀ → N → ∞` absorbs.
-/

open scoped Classical in
/-- **Harmonic mass on a residue class.**  Any subset of `range M` lying in one class
`a (mod L)` has harmonic mass at most `(a+1)⁻¹ + (1 + log M)/L`: the class's first element, plus
the harmonic tail at the full modulus. -/
theorem class_harmonic_mass {F : ℕ → ℂ} (hF : ∀ n : ℕ, ‖F n‖ ≤ ((n : ℝ) + 1)⁻¹)
    {S : Finset ℕ} {M : ℕ} (hS : ∀ n ∈ S, n < M) {L a : ℕ} (hL : 0 < L)
    (hcl : ∀ n ∈ S, n % L = a) :
    ∑ n ∈ S, ‖F n‖ ≤ ((a : ℝ) + 1)⁻¹ + (1 + Real.log M) / (L : ℝ) := by
  classical
  set ψ : ℕ → ℕ := fun n => n / L with hψ
  set S0 := S.filter (fun n => ψ n = 0) with hS0
  set S1 := S.filter (fun n => ψ n ≠ 0) with hS1
  have hrec : ∀ n ∈ S, L * ψ n + a = n := by
    intro n hn
    have := hcl n hn
    rw [hψ]
    simpa [this] using (Nat.div_add_mod n L)
  have hsplit : ∑ n ∈ S0, ‖F n‖ + ∑ n ∈ S1, ‖F n‖ = ∑ n ∈ S, ‖F n‖ :=
    Finset.sum_filter_add_sum_filter_not S _ _
  -- the head: `S0 ⊆ {a}`
  have hhead : ∑ n ∈ S0, ‖F n‖ ≤ ((a : ℝ) + 1)⁻¹ := by
    have hsub : S0 ⊆ {a} := by
      intro n hn
      obtain ⟨hnS, hz⟩ := Finset.mem_filter.1 hn
      have := hrec n hnS
      rw [hz, mul_zero, zero_add] at this
      simp [this]
    calc ∑ n ∈ S0, ‖F n‖ ≤ ∑ n ∈ S0, ((n : ℝ) + 1)⁻¹ := Finset.sum_le_sum fun n _ => hF n
      _ ≤ ∑ n ∈ ({a} : Finset ℕ), ((n : ℝ) + 1)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
      _ = ((a : ℝ) + 1)⁻¹ := by simp
  -- the tail: inject `ψ` into `Icc 1 (M/L)`
  have htail : ∑ n ∈ S1, ‖F n‖ ≤ (1 + Real.log M) / (L : ℝ) := by
    have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    have hmem : ∀ n ∈ S1, ψ n ∈ Finset.Icc 1 (M / L) := by
      intro n hn
      obtain ⟨hnS, hz⟩ := Finset.mem_filter.1 hn
      refine Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 hz, ?_⟩
      exact Nat.div_le_div_right (hS n hnS).le
    have hinj : Set.InjOn ψ (S1 : Set ℕ) := by
      intro m hm n hn hmn
      have h1 := hrec m (Finset.mem_filter.1 (Finset.mem_coe.1 hm)).1
      have h2 := hrec n (Finset.mem_filter.1 (Finset.mem_coe.1 hn)).1
      rw [hmn] at h1
      omega
    have hstep : ∀ n ∈ S1, ‖F n‖ ≤ (1 / (L : ℝ)) * ((ψ n : ℝ))⁻¹ := by
      intro n hn
      obtain ⟨hnS, hz⟩ := Finset.mem_filter.1 hn
      have hpos : (0 : ℝ) < (ψ n : ℝ) := by
        have := (Finset.mem_Icc.1 (hmem n hn)).1
        exact_mod_cast this
      have hge : (L : ℝ) * (ψ n : ℝ) ≤ (n : ℝ) + 1 := by
        have h := hrec n hnS
        have h2 : ((L * ψ n : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by
          exact_mod_cast Nat.le.intro h
        push_cast at h2 ⊢
        linarith
      refine (hF n).trans ?_
      rw [one_div, ← mul_inv]
      exact inv_anti₀ (by positivity) hge
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.mul_sum]
    have himg : ∑ n ∈ S1, ((ψ n : ℝ))⁻¹ = ∑ m ∈ S1.image ψ, ((m : ℝ))⁻¹ :=
      (Finset.sum_image (f := fun m : ℕ => ((m : ℝ))⁻¹) hinj).symm
    rw [himg]
    have hsub : S1.image ψ ⊆ Finset.Icc 1 (M / L) := by
      intro m hm
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hm
      exact hmem n hn
    have hharm : ∑ m ∈ S1.image ψ, ((m : ℝ))⁻¹ ≤ 1 + Real.log M := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun m _ _ => by positivity)) ?_
      have h1 : ∑ m ∈ Finset.Icc 1 (M / L), ((m : ℝ))⁻¹ = ((harmonic (M / L) : ℚ) : ℝ) := by
        rw [harmonic_eq_sum_Icc]; push_cast; rfl
      rw [h1]
      refine (harmonic_le_one_add_log (M / L)).trans ?_
      have hle : ((M / L : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.div_le_self M L
      have hlog : (0 : ℝ) ≤ Real.log M := Real.log_natCast_nonneg M
      rcases Nat.eq_zero_or_pos (M / L) with h0 | h0
      · rw [show ((M / L : ℕ) : ℝ) = 0 by rw [h0]; norm_num, Real.log_zero]
        linarith
      · have : Real.log ((M / L : ℕ) : ℝ) ≤ Real.log M :=
          Real.log_le_log (by exact_mod_cast h0) hle
        linarith
    calc (1 / (L : ℝ)) * ∑ m ∈ S1.image ψ, ((m : ℝ))⁻¹
        ≤ (1 / (L : ℝ)) * (1 + Real.log M) :=
          mul_le_mul_of_nonneg_left hharm (by positivity)
      _ = (1 + Real.log M) / (L : ℝ) := by ring
  linarith [hsplit, hhead, htail]


open scoped Classical in
/-- **The joint mass, with both gains.**  For the joint progression `d ∣ n+1`, `e ∣ n+2` the
harmonic mass is at most `2/e + (1 + log N)/(d·e)`.  The `1/(de)` in the main term is what the
outer `d`-sum needs (`∑_d ‖sqfW z₀ d‖/d` converges, `∑_d ‖sqfW z₀ d‖` does not); the head `2/e`
carries no `log N`, so it contributes only an `N`-independent constant. -/
theorem joint_progression_harmonic_mass {F : ℕ → ℂ} (hF : ∀ n : ℕ, ‖F n‖ ≤ ((n : ℝ) + 1)⁻¹)
    (N : ℕ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    ∑ n ∈ ((Finset.range N).filter (fun n => d ∣ n + 1)).filter (fun n => e ∣ n + 2), ‖F n‖
      ≤ 2 / (e : ℝ) + (1 + Real.log N) / ((d : ℝ) * (e : ℝ)) := by
  classical
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlog : (0 : ℝ) ≤ Real.log N := Real.log_natCast_nonneg N
  by_cases hco : Nat.Coprime d e
  · obtain ⟨a, haL, hda, hea, hclass⟩ := exists_joint_class hd he hco
    set T := ((Finset.range N).filter (fun n => d ∣ n + 1)).filter (fun n => e ∣ n + 2) with hT
    have hSlt : ∀ n ∈ T, n < N := by
      intro n hn
      exact Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hn).1).1
    have hcl : ∀ n ∈ T, n % (d * e) = a := by
      intro n hn
      exact (hclass n).1 ⟨(Finset.mem_filter.1 (Finset.mem_filter.1 hn).1).2,
        (Finset.mem_filter.1 hn).2⟩
    have hmass := class_harmonic_mass hF hSlt (Nat.mul_pos hd he) hcl
    -- the head `(a+1)⁻¹ ≤ 2/e`, because `e ∣ a + 2`
    have hhead : ((a : ℝ) + 1)⁻¹ ≤ 2 / (e : ℝ) := by
      have hae : e ≤ a + 2 := Nat.le_of_dvd (by omega) hea
      have haeR : (e : ℝ) ≤ (a : ℝ) + 2 := by exact_mod_cast hae
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) heR]
      have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
      nlinarith
    have hcast : ((d * e : ℕ) : ℝ) = (d : ℝ) * (e : ℝ) := by push_cast; ring
    rw [hcast] at hmass
    linarith
  · rw [joint_progression_eq_empty_of_not_coprime hco, Finset.sum_empty]
    positivity


/-! ## The two-shift truncation bound

Both moduli cut at `Y`.  The outer expansion pays `(1 + log(N+1))·bridgeTail z₀ Y`; the inner
one pays, for each `d ≤ Y`, `(2 + (1 + log N)/d)·bridgeTail z₁ Y`, weighted by `‖sqfW z₀ d‖`.
Summing the `d`-weights gives the two shapes that appear in the statement: the `2` against the
partial sum `sqfWPartial` (an `N`-independent constant, absorbed), and the `(1 + log N)/d`
against the *convergent* weighted mass `sqfWMass` (the term of the right order).
-/

/-- `∑_{d ≤ Y} ‖sqfW z d‖`, an `N`-independent constant (it grows with `Y`, like `Y^{1/2}`). -/
noncomputable def sqfWPartial (z : ℂ) (Y : ℕ) : ℝ := ∑ d ∈ Finset.range (Y + 1), ‖sqfW z d‖

/-- `∑_d ‖sqfW z d‖/d`, finite by `summable_norm_sqfW_div`. -/
noncomputable def sqfWMass (z : ℂ) : ℝ := ∑' d : ℕ, ‖sqfW z d‖ / (d : ℝ)

lemma sqfWPartial_nonneg (z : ℂ) (Y : ℕ) : 0 ≤ sqfWPartial z Y :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma sum_norm_sqfW_div_le_mass {z : ℂ} (hz : ‖z‖ = 1) (Y : ℕ) :
    ∑ d ∈ Finset.range (Y + 1), ‖sqfW z d‖ / (d : ℝ) ≤ sqfWMass z :=
  (summable_norm_sqfW_div z hz).sum_le_tsum _ (fun _ _ => by positivity)

open scoped Classical in
/-- **The two-shift truncation bound.**  Cutting BOTH moduli at `Y` costs
`(1 + log(N+1))·bridgeTail z₀ Y + (2·sqfWPartial z₀ Y + (1 + log N)·sqfWMass z₀)·bridgeTail z₁ Y`.
Both `bridgeTail`s tend to `0` as `Y → ∞` independently of `N`, and `sqfWMass z₀ < ∞`, so
choosing `Y` from `ε` first makes the second summand `≤ ε·log N` plus an `N`-independent
constant — the shape the rung needs. -/
theorem two_shift_truncation_bound {z₀ z₁ : ℂ} (hz₀ : ‖z₀‖ = 1) (hz₁ : ‖z₁‖ = 1)
    {F : ℕ → ℂ} (hF : ∀ n : ℕ, ‖F n‖ ≤ ((n : ℝ) + 1)⁻¹) (Y N : ℕ) :
    ‖(∑ n ∈ Finset.range N, F n * (z₀ ^ omegaNat (n + 1) * z₁ ^ omegaNat (n + 2)))
        - ∑ d ∈ Finset.range (Y + 1), ∑ e ∈ Finset.range (Y + 1),
            sqfW z₀ d * sqfW z₁ e *
              ∑ n ∈ ((Finset.range N).filter (fun n => d ∣ n + 1)).filter (fun n => e ∣ n + 2),
                F n * (z₀ ^ ArithmeticFunction.cardFactors ((n + 1) / d) *
                  z₁ ^ ArithmeticFunction.cardFactors ((n + 2) / e))‖
      ≤ (1 + Real.log (N + 1)) * bridgeTail z₀ Y
        + (2 * sqfWPartial z₀ Y + (1 + Real.log N) * sqfWMass z₀) * bridgeTail z₁ Y := by
  classical
  set S : ℕ → Finset ℕ := fun d => (Finset.range N).filter (fun n => d ∣ n + 1) with hS
  set F₁ : ℕ → ℂ := fun n => F n * z₁ ^ omegaNat (n + 2) with hF₁
  have hF₁norm : ∀ n, ‖F₁ n‖ = ‖F n‖ := by
    intro n; rw [hF₁, norm_mul, norm_pow, hz₁, one_pow, mul_one]
  have hF₁le : ∀ n : ℕ, ‖F₁ n‖ ≤ ((n : ℝ) + 1)⁻¹ := fun n => by rw [hF₁norm]; exact hF n
  set Mid := ∑ d ∈ Finset.range (Y + 1), sqfW z₀ d *
    ∑ n ∈ S d, F₁ n * z₀ ^ ArithmeticFunction.cardFactors ((n + 1) / d) with hMid
  -- Step 1: the outer truncation
  have hstep1 : ‖(∑ n ∈ Finset.range N, F n * (z₀ ^ omegaNat (n + 1) * z₁ ^ omegaNat (n + 2)))
      - Mid‖ ≤ (1 + Real.log (N + 1)) * bridgeTail z₀ Y := by
    have hrw : (∑ n ∈ Finset.range N, F n * (z₀ ^ omegaNat (n + 1) * z₁ ^ omegaNat (n + 2)))
        = ∑ n ∈ Finset.range N, F₁ n * z₀ ^ omegaNat (n + 1) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hF₁]; ring
    rw [hrw, hMid]
    refine offset_truncation_bound_of_mass z₀ hz₀ F₁ (Finset.range N) 1 one_pos (N + 1)
      (fun n hn => by rw [Finset.mem_range] at hn; omega) Y (1 + Real.log (N + 1))
      (by have h1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by
            have := Nat.cast_nonneg (α := ℝ) N; linarith
          have := Real.log_nonneg h1
          push_cast
          linarith) ?_
    intro d hd
    have := progression_harmonic_mass hF₁le (S := Finset.range N) (M := N)
      (fun n hn => Finset.mem_range.1 hn) one_pos hd
    push_cast at this ⊢
    simpa using this
  -- Step 2: the inner truncation, for each `d`
  have hstep2 : ∀ d ∈ Finset.range (Y + 1),
      ‖(∑ n ∈ S d, F₁ n * z₀ ^ ArithmeticFunction.cardFactors ((n + 1) / d))
        - ∑ e ∈ Finset.range (Y + 1), sqfW z₁ e *
            ∑ n ∈ (S d).filter (fun n => e ∣ n + 2),
              (F n * z₀ ^ ArithmeticFunction.cardFactors ((n + 1) / d)) *
                z₁ ^ ArithmeticFunction.cardFactors ((n + 2) / e)‖
        ≤ (2 + (1 + Real.log N) / (d : ℝ)) * bridgeTail z₁ Y := by
    intro d _
    set G : ℕ → ℂ := fun n => F n * z₀ ^ ArithmeticFunction.cardFactors ((n + 1) / d) with hG
    have hGnorm : ∀ n, ‖G n‖ = ‖F n‖ := by
      intro n; rw [hG, norm_mul, norm_pow, hz₀, one_pow, mul_one]
    have hGle : ∀ n : ℕ, ‖G n‖ ≤ ((n : ℝ) + 1)⁻¹ := fun n => by rw [hGnorm]; exact hF n
    have hrw : (∑ n ∈ S d, F₁ n * z₀ ^ ArithmeticFunction.cardFactors ((n + 1) / d))
        = ∑ n ∈ S d, G n * z₁ ^ omegaNat (n + 2) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hF₁, hG]; ring
    rw [hrw]
    refine offset_truncation_bound_of_mass z₁ hz₁ G (S d) 2 (by norm_num) (N + 2)
      (fun n hn => by
        have := Finset.mem_range.1 (Finset.mem_filter.1 hn).1
        omega) Y (2 + (1 + Real.log N) / (d : ℝ))
      (by have := Real.log_natCast_nonneg N
          have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
          positivity) ?_
    intro e he
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · have hempty : (S 0).filter (fun n => e ∣ n + 2) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun n hn => ?_
        have := (Finset.mem_filter.1 (Finset.mem_filter.1 hn).1).2
        simp at this
      rw [hempty, Finset.sum_empty]
      have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
      have : (0 : ℝ) ≤ (2 + (1 + Real.log N) / ((0 : ℕ) : ℝ)) / (e : ℝ) := by
        rw [Nat.cast_zero, div_zero]; positivity
      linarith
    · have hjoint := joint_progression_harmonic_mass hGle N hd0 he
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
      have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
      have heq : (2 + (1 + Real.log N) / (d : ℝ)) / (e : ℝ)
          = 2 / (e : ℝ) + (1 + Real.log N) / ((d : ℝ) * (e : ℝ)) := by
        field_simp
      rw [heq]
      exact hjoint
  -- assemble
  set Full := ∑ d ∈ Finset.range (Y + 1), ∑ e ∈ Finset.range (Y + 1),
    sqfW z₀ d * sqfW z₁ e *
      ∑ n ∈ (S d).filter (fun n => e ∣ n + 2),
        F n * (z₀ ^ ArithmeticFunction.cardFactors ((n + 1) / d) *
          z₁ ^ ArithmeticFunction.cardFactors ((n + 2) / e)) with hFull
  have hMidFull : ‖Mid - Full‖
      ≤ (2 * sqfWPartial z₀ Y + (1 + Real.log N) * sqfWMass z₀) * bridgeTail z₁ Y := by
    have hdiff : Mid - Full = ∑ d ∈ Finset.range (Y + 1), sqfW z₀ d *
        ((∑ n ∈ S d, F₁ n * z₀ ^ ArithmeticFunction.cardFactors ((n + 1) / d))
          - ∑ e ∈ Finset.range (Y + 1), sqfW z₁ e *
              ∑ n ∈ (S d).filter (fun n => e ∣ n + 2),
                (F n * z₀ ^ ArithmeticFunction.cardFactors ((n + 1) / d)) *
                  z₁ ^ ArithmeticFunction.cardFactors ((n + 2) / e)) := by
      rw [hMid, hFull, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      have hinner : ∀ e ∈ Finset.range (Y + 1),
        sqfW z₀ d * sqfW z₁ e *
          ∑ n ∈ (S d).filter (fun n => e ∣ n + 2),
            F n * (z₀ ^ ArithmeticFunction.cardFactors ((n + 1) / d) *
              z₁ ^ ArithmeticFunction.cardFactors ((n + 2) / e))
        = sqfW z₀ d * (sqfW z₁ e *
            ∑ n ∈ (S d).filter (fun n => e ∣ n + 2),
              (F n * z₀ ^ ArithmeticFunction.cardFactors ((n + 1) / d)) *
                z₁ ^ ArithmeticFunction.cardFactors ((n + 2) / e)) := by
        intro e _
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by ring
      rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, ← mul_sub]
    rw [hdiff]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ d ∈ Finset.range (Y + 1),
        ‖sqfW z₀ d * ((∑ n ∈ S d, F₁ n * z₀ ^ ArithmeticFunction.cardFactors ((n + 1) / d))
          - ∑ e ∈ Finset.range (Y + 1), sqfW z₁ e *
              ∑ n ∈ (S d).filter (fun n => e ∣ n + 2),
                (F n * z₀ ^ ArithmeticFunction.cardFactors ((n + 1) / d)) *
                  z₁ ^ ArithmeticFunction.cardFactors ((n + 2) / e))‖
          ≤ (2 * ‖sqfW z₀ d‖ + (1 + Real.log N) * (‖sqfW z₀ d‖ / (d : ℝ)))
              * bridgeTail z₁ Y := by
      intro d hd
      rw [norm_mul]
      refine le_trans (mul_le_mul_of_nonneg_left (hstep2 d hd) (norm_nonneg _)) ?_
      have hT : 0 ≤ bridgeTail z₁ Y := bridgeTail_nonneg z₁ Y
      have : ‖sqfW z₀ d‖ * ((2 + (1 + Real.log N) / (d : ℝ)) * bridgeTail z₁ Y)
          = (2 * ‖sqfW z₀ d‖ + (1 + Real.log N) * (‖sqfW z₀ d‖ / (d : ℝ)))
              * bridgeTail z₁ Y := by ring
      rw [this]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (bridgeTail_nonneg z₁ Y)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hlog : (0 : ℝ) ≤ 1 + Real.log N := by
      have := Real.log_natCast_nonneg N; linarith
    have h2 := sum_norm_sqfW_div_le_mass hz₀ Y
    have : (2 : ℝ) * ∑ d ∈ Finset.range (Y + 1), ‖sqfW z₀ d‖ = 2 * sqfWPartial z₀ Y := by
      rw [sqfWPartial]
    rw [this]
    have := mul_le_mul_of_nonneg_left h2 hlog
    linarith
  calc ‖(∑ n ∈ Finset.range N, F n * (z₀ ^ omegaNat (n + 1) * z₁ ^ omegaNat (n + 2))) - Full‖
      = ‖((∑ n ∈ Finset.range N, F n * (z₀ ^ omegaNat (n + 1) * z₁ ^ omegaNat (n + 2))) - Mid)
          + (Mid - Full)‖ := by congr 1; ring
    _ ≤ _ := le_trans (norm_add_le _ _) (add_le_add hstep1 hMidFull)


/-! ## From the joint progression to the rung's window

`inner_sum_linear_forms` turns the joint inner sum into a sum over the progression variable `j`,
still carrying the harmonic weight of the ORIGINAL variable `n = de·j + a`.  Two elementary
steps bring it to the shape `rung_two_of_named_inputs` consumes:

* the cutoff `{j : de·j + a < N}` is an initial segment `range (J+1)` (`filter_linear_lt_eq_range`);
* peeling `j = 0` and applying `weight_transfer` replaces the weight by `(de)⁻¹ · j⁻¹`
  (`joint_inner_harmonic_le`), at a cost `((a+1)⁻¹ + 2/(de))` that is bounded by `1 + 2/(de)`
  and carries no `log N`.

Summed over the `(d,e)` with `d, e ≤ Y` both costs are `N`-independent constants, which the
quantifier order `ε → Y → A → i₀ → N → ∞` absorbs.
-/

open scoped Classical in
/-- The cutoff `{j : L·j + a < N}` is the initial segment `range ((N−1−a)/L + 1)`. -/
theorem filter_linear_lt_eq_range {L a N : ℕ} (hL : 0 < L) (haN : a < N) :
    (Finset.range N).filter (fun j => L * j + a < N) = Finset.range ((N - 1 - a) / L + 1) := by
  classical
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, hlt⟩
    have h1 : j * L ≤ N - 1 - a := by rw [mul_comm]; omega
    have := (Nat.le_div_iff_mul_le hL).2 h1
    omega
  · intro hj
    have h1 : j ≤ (N - 1 - a) / L := Nat.lt_succ_iff.1 hj
    have h2 : L * j ≤ N - 1 - a := by
      have := Nat.mul_le_mul_left L h1
      exact le_trans this (by rw [mul_comm]; exact Nat.div_mul_le_self _ _)
    have h3 : L * j + a < N := by omega
    have h4 : j ≤ L * j := Nat.le_mul_of_pos_left j hL
    exact ⟨by omega, h3⟩

/-- **Peel `j = 0`, transfer the weight.**  The harmonically weighted sum over the progression
variable is `(de)⁻¹` times the rung's sum, up to `(a+1)⁻¹ + 2/(de)` — an `N`-independent cost. -/
theorem joint_inner_harmonic_le {z₀ z₁ : ℂ} (hz₀ : ‖z₀‖ = 1) (hz₁ : ‖z₁‖ = 1)
    {L a b₀ b₁ d e : ℕ} (hL : 0 < L) (haL : a + 1 ≤ L) (J : ℕ) :
    ‖∑ j ∈ Finset.range (J + 1), ((((L * j + a : ℕ) : ℝ) + 1)⁻¹ : ℝ) •
        (z₀ ^ ArithmeticFunction.cardFactors (e * j + b₀) *
          z₁ ^ ArithmeticFunction.cardFactors (d * j + b₁))‖
      ≤ (((a : ℝ) + 1)⁻¹ + 2 / (L : ℝ))
        + (L : ℝ)⁻¹ * ‖∑ j ∈ Finset.Icc 1 J, (((j : ℝ))⁻¹ : ℝ) •
            (z₀ ^ ArithmeticFunction.cardFactors (e * j + b₀) *
              z₁ ^ ArithmeticFunction.cardFactors (d * j + b₁))‖ := by
  classical
  set G : ℕ → ℂ := fun j => z₀ ^ ArithmeticFunction.cardFactors (e * j + b₀) *
    z₁ ^ ArithmeticFunction.cardFactors (d * j + b₁) with hG
  have hGnorm : ∀ j, ‖G j‖ ≤ 1 := by
    intro j; rw [hG, norm_mul, norm_pow, norm_pow, hz₀, hz₁, one_pow, one_pow, mul_one]
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  -- split off `j = 0`
  have hsplit : Finset.range (J + 1) = insert 0 (Finset.Icc 1 J) := by
    ext j; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have h0 : (0 : ℕ) ∉ Finset.Icc 1 J := by simp
  rw [hsplit, Finset.sum_insert h0]
  -- the weight is the one `weight_transfer` expects, with offset `a + 1`
  have hwt : ∀ j : ℕ, (((L * j + a : ℕ) : ℝ) + 1)⁻¹ = (((L * j + (a + 1) : ℕ) : ℝ))⁻¹ := by
    intro j; push_cast; ring
  have hrw : ∑ j ∈ Finset.Icc 1 J, ((((L * j + a : ℕ) : ℝ) + 1)⁻¹ : ℝ) • G j
      = ∑ j ∈ Finset.Icc 1 J, ((((L * j + (a + 1) : ℕ) : ℝ))⁻¹ : ℝ) • G j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hwt j]
  have htrans := weight_transfer (L := L) (a := a + 1) hL haL J G hGnorm
  have hhead : ‖((((L * 0 + a : ℕ) : ℝ) + 1)⁻¹ : ℝ) • G 0‖ ≤ ((a : ℝ) + 1)⁻¹ := by
    rw [norm_smul, Real.norm_eq_abs]
    have hcast : (((L * 0 + a : ℕ) : ℝ) + 1)⁻¹ = ((a : ℝ) + 1)⁻¹ := by norm_num
    rw [hcast, abs_of_nonneg (by positivity)]
    calc ((a : ℝ) + 1)⁻¹ * ‖G 0‖ ≤ ((a : ℝ) + 1)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (hGnorm 0) (by positivity)
      _ = ((a : ℝ) + 1)⁻¹ := mul_one _
  have htail : ‖∑ j ∈ Finset.Icc 1 J, ((((L * j + a : ℕ) : ℝ) + 1)⁻¹ : ℝ) • G j‖
      ≤ 2 / (L : ℝ) + (L : ℝ)⁻¹ * ‖∑ j ∈ Finset.Icc 1 J, (((j : ℝ))⁻¹ : ℝ) • G j‖ := by
    rw [hrw]
    have hsub := norm_sub_norm_le
      (∑ j ∈ Finset.Icc 1 J, ((((L * j + (a + 1) : ℕ) : ℝ))⁻¹ : ℝ) • G j)
      ((L : ℝ)⁻¹ • ∑ j ∈ Finset.Icc 1 J, (((j : ℝ))⁻¹ : ℝ) • G j)
    have hnsm : ‖(L : ℝ)⁻¹ • ∑ j ∈ Finset.Icc 1 J, (((j : ℝ))⁻¹ : ℝ) • G j‖
        = (L : ℝ)⁻¹ * ‖∑ j ∈ Finset.Icc 1 J, (((j : ℝ))⁻¹ : ℝ) • G j‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hnsm] at hsub
    have := le_trans hsub htrans
    linarith
  refine le_trans (norm_add_le _ _) ?_
  linarith [hhead, htail]

end CastingOut

end NormalNumbers

-- axiom audit
#print axioms NormalNumbers.CastingOut.offset_truncation_bound_of_mass
#print axioms NormalNumbers.CastingOut.progression_harmonic_mass
#print axioms NormalNumbers.CastingOut.class_harmonic_mass
#print axioms NormalNumbers.CastingOut.joint_progression_harmonic_mass
#print axioms NormalNumbers.CastingOut.two_shift_truncation_bound
#print axioms NormalNumbers.CastingOut.filter_linear_lt_eq_range
#print axioms NormalNumbers.CastingOut.joint_inner_harmonic_le
