/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtLinearForms

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

end CastingOut

end NormalNumbers

-- axiom audit
#print axioms NormalNumbers.CastingOut.offset_truncation_bound_of_mass
#print axioms NormalNumbers.CastingOut.progression_harmonic_mass
#print axioms NormalNumbers.CastingOut.class_harmonic_mass
#print axioms NormalNumbers.CastingOut.joint_progression_harmonic_mass
