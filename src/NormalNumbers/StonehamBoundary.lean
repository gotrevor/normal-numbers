import NormalNumbers.StonehamBase6
import NormalNumbers.Disjunctive
import NormalNumbers.StonehamBoundaryLemmas

/-!
# Fixed-boundary-offset proof of base-6 Stoneham disjunctivity

Attended statement freeze: Ren / Astra, 2026-09-13.
These are proof obligations, not claims of completed formalization.
See BRIEF-stoneham-boundary-2026-09-13.md for the full elementary route.

The headline says every real subinterval is visited arbitrarily late.  It
does not assert normality, a frequency bound, or any statement about log 2.
The boundary map is `k ↦ 3^k - k`, with INTEGER subtraction for congruences.
-/

namespace NormalNumbers

/-- The block-exponent map hits every residue at every binary precision.
Frozen statement: do not weaken, re-hypothesize, rename, or delete. -/
theorem stoneham_exponent_residue_surjective (r a : ℕ) :
    ∃ k : ℕ, k < 2 ^ r ∧
      ((3 : ℤ) ^ k - (k : ℤ)) % (2 ^ r : ℤ) = (a : ℤ) % (2 ^ r : ℤ) := by
  obtain ⟨k, hk, hmod⟩ := exponent_residue_aux r (a : ℤ)
  exact ⟨k, hk, hmod⟩

/-- A fine grid is supplied by the powers of 3.  Only the residues 1 mod 8
are needed, so full classification of the generated subgroup is optional.
Frozen statement. -/
theorem stoneham_three_pow_grid (c a : ℕ) (hc : 3 ≤ c)
    (ha : a < 2 ^ c) (hgrid : a % 8 = 1) :
    ∃ e : ℕ, 3 ^ e % 2 ^ c = a := by
  obtain ⟨e, he⟩ := three_pow_grid_aux c hc (a : ℤ) (by omega)
  refine ⟨e, ?_⟩
  have h1 : ((3 ^ e % 2 ^ c : ℕ) : ℤ) = ((a : ℕ) : ℤ) := by
    push_cast
    rw [he]
    exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast ha)
  exact_mod_cast h1

/-- Every point on that grid is the exact readout at arbitrarily late
block boundaries.  Natural subtraction is safe once the returned block
conditions are established.  Frozen statement. -/
theorem stoneham_boundary_readout_recurrence (c a K : ℕ) (hc : 3 ≤ c)
    (ha : a < 2 ^ c) (hgrid : a % 8 = 1) :
    ∃ k : ℕ, K ≤ k ∧ 3 ≤ 3 ^ k - c ∧
      sC (3 ^ k - c) = c ∧ readout (3 ^ k - c) = a := by
  obtain ⟨e, he⟩ := stoneham_three_pow_grid c a hc ha hgrid
  have hr : 1 ≤ c - 2 := by omega
  obtain ⟨k0, _, hk0⟩ := exponent_residue_aux (c - 2) ((e + c : ℕ) : ℤ)
  -- the block index
  set k : ℕ := k0 + (K + c + 3) * 2 ^ (c - 2) with hkdef
  have hP : 1 ≤ 2 ^ (c - 2) := Nat.one_le_two_pow
  have hkK : K + c + 3 ≤ k := by
    have : K + c + 3 ≤ (K + c + 3) * 2 ^ (c - 2) := Nat.le_mul_of_pos_right _ hP
    omega
  have hk1 : 1 ≤ k := by omega
  -- power bounds
  have hc3 : c < 3 ^ (k - 1) := by
    calc c < 3 ^ c := Nat.lt_pow_self (by norm_num)
      _ ≤ 3 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hkk : k ≤ 3 ^ (k - 1) := by
    have := Nat.lt_pow_self (n := k - 1) (a := 3) (by norm_num); omega
  have h3k : 3 ^ k = 3 * 3 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hn3 : 3 ≤ 3 ^ k - c := by omega
  have hjstar : jstar (3 ^ k - c) = k - 1 := by
    rw [jstar, Nat.find_eq_iff]
    refine ⟨by rw [show k - 1 + 1 = k by omega]; omega, ?_⟩
    intro i hi
    push Not
    calc 3 ^ (i + 1) ≤ 3 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 3 ^ k - c := by omega
  have hsC : sC (3 ^ k - c) = c := by
    unfold sC; rw [hjstar, show k - 1 + 1 = k by omega]; omega
  have hsA : sA (3 ^ k - c) = 3 ^ k - c - k := by
    unfold sA; rw [hjstar, show k - 1 + 1 = k by omega]
  refine ⟨k, by omega, hn3, hsC, ?_⟩
  -- the exponent congruence, integer form
  have hper := stoneham_f_periodic (c - 2) hr k0 (K + c + 3)
  have hfk : (3 : ℤ) ^ k - (k : ℤ) ≡ ((e + c : ℕ) : ℤ) [ZMOD 2 ^ (c - 2)] := hper.trans hk0
  have hd : ((3 ^ k - c - k : ℕ) : ℤ) ≡ (e : ℤ) [ZMOD 2 ^ (c - 2)] := by
    have hsub : ((3 ^ k - c - k : ℕ) : ℤ) = (3 : ℤ) ^ k - (k : ℤ) - (c : ℤ) := by
      have : c + k ≤ 3 ^ k := by omega
      push_cast [Nat.sub_sub, Nat.cast_sub this]; ring
    rw [hsub]
    have := hfk.sub_right (c : ℤ)
    push_cast at this
    simpa using this
  have hdN : 3 ^ k - c - k ≡ e [MOD 2 ^ (c - 2)] := Int.natCast_modEq_iff.mp hd
  -- 3^P ≡ 1 mod 2^c, natural form
  have hP1 : 3 ^ (2 ^ (c - 2)) ≡ 1 [MOD 2 ^ c] := by
    have := three_pow_two_pow_modEq_one (c - 2) hr
    rw [show c - 2 + 2 = c by omega] at this
    exact Int.natCast_modEq_iff.mp (by exact_mod_cast this)
  -- 3^x mod 2^c depends only on x mod P
  have hred : ∀ x : ℕ, 3 ^ x ≡ 3 ^ (x % 2 ^ (c - 2)) [MOD 2 ^ c] := by
    intro x
    conv_lhs => rw [← Nat.div_add_mod x (2 ^ (c - 2)), pow_add, pow_mul]
    calc (3 ^ 2 ^ (c - 2)) ^ (x / 2 ^ (c - 2)) * 3 ^ (x % 2 ^ (c - 2))
        ≡ 1 ^ (x / 2 ^ (c - 2)) * 3 ^ (x % 2 ^ (c - 2)) [MOD 2 ^ c] :=
          (hP1.pow _).mul_right _
      _ = 3 ^ (x % 2 ^ (c - 2)) := by rw [one_pow, one_mul]
  have hfinal : 3 ^ (3 ^ k - c - k) ≡ 3 ^ e [MOD 2 ^ c] := by
    refine (hred _).trans ?_
    rw [hdN]
    exact (hred e).symm
  unfold readout
  rw [hsC, hsA]
  rw [← he]
  exact hfinal

/-- A uniform one-cell bound, strengthening the public readout interface
using the bound already proved internally in StonehamBase6.  Frozen statement. -/
theorem stoneham_orbit_readout_cell (n : ℕ) (hn : 3 ≤ n) :
    (readout n : ℝ) / (2 : ℝ) ^ sC n < orbit 6 stoneham23 n ∧
      orbit 6 stoneham23 n < ((readout n : ℝ) + 1) / (2 : ℝ) ^ sC n := by
  obtain ⟨hlo, hhi⟩ := stoneham_base6_readout n hn
  refine ⟨hlo, ?_⟩
  set J := jstar n with hJ
  have hJ1 : 1 ≤ J := one_le_jstar hn
  have hJn : J + 2 ≤ n := jstar_add_two_le hn
  have hn3J : n < 3 ^ (J + 1) := lt_three_pow_jstar n
  -- the tail is strictly below one cell
  have hT_lt : 2 * (3 : ℝ) ^ (sA n - 1) / 2 ^ (3 ^ (J + 2) - n) < 1 / (2 : ℝ) ^ sC n := by
    have hsplit : 3 ^ (J + 2) - n = 2 * 3 ^ (J + 1) + sC n := by
      unfold sC; rw [← hJ]
      have : 3 ^ (J + 2) = 3 * 3 ^ (J + 1) := by rw [pow_succ]; ring
      omega
    have hnat : 2 * 3 ^ (sA n - 1) < 4 ^ (3 ^ (J + 1)) := by
      have ha : sA n - 1 < 3 ^ (J + 1) := by unfold sA; rw [← hJ]; omega
      have h9 : 3 ≤ 3 ^ (J + 1) := by
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ (J + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc 2 * 3 ^ (sA n - 1) < 2 * 3 ^ (3 ^ (J + 1)) := by
            have := Nat.pow_lt_pow_right (by norm_num : 1 < 3) ha
            omega
        _ ≤ 4 ^ (3 ^ (J + 1)) := two_mul_three_pow_le_four_pow h9
    have hreal : (2 : ℝ) * 3 ^ (sA n - 1) < 4 ^ (3 ^ (J + 1)) := by exact_mod_cast hnat
    have h4 : (4 : ℝ) ^ (3 ^ (J + 1)) = 2 ^ (2 * 3 ^ (J + 1)) := by
      rw [pow_mul]; norm_num
    rw [hsplit, pow_add, ← h4]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have h2c : (0 : ℝ) < 2 ^ sC n := by positivity
    nlinarith [h2c, hreal]
  have hcell : ((readout n : ℝ) + 1) / (2 : ℝ) ^ sC n
      = (readout n : ℝ) / 2 ^ sC n + 1 / 2 ^ sC n := by ring
  rw [hcell]
  linarith

/-- The sparse boundary subsequence visits every interval arbitrarily late.
This is the mathematical campaign endpoint.  Frozen statement. -/
theorem stoneham_base6_interval_recurrence (u v : ℝ)
    (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ orbit 6 stoneham23 n ∈ Set.Ico u v := by
  -- choose the precision `c` with `16 < (v - u) 2^c`
  have hvu : 0 < v - u := by linarith
  obtain ⟨M, hM⟩ := exists_nat_gt (16 / (v - u))
  set c : ℕ := M + 3 with hc
  have hc3 : 3 ≤ c := by omega
  have hcM : (M : ℝ) < (2 : ℝ) ^ c := by
    have h1 : c < 2 ^ c := Nat.lt_two_pow_self
    have h2 : (M : ℝ) < (c : ℝ) := by exact_mod_cast (show M < c by omega)
    have h3 : (c : ℝ) < (2 : ℝ) ^ c := by exact_mod_cast h1
    linarith
  have h2c : (0 : ℝ) < (2 : ℝ) ^ c := by positivity
  have h16 : 16 < (v - u) * 2 ^ c := by
    have := (div_lt_iff₀ hvu).1 hM
    nlinarith
  -- choose the grid point `a = 8m + 9` just above `u 2^c`
  set m : ℕ := ⌊u * 2 ^ c / 8⌋₊ with hm
  have hm_nonneg : 0 ≤ u * 2 ^ c / 8 := by positivity
  have hm1 : (m : ℝ) ≤ u * 2 ^ c / 8 := Nat.floor_le hm_nonneg
  have hm2 : u * 2 ^ c / 8 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  set a : ℕ := 8 * m + 9 with hadef
  have hgrid : a % 8 = 1 := by omega
  have ha_real : (a : ℝ) = 8 * (m : ℝ) + 9 := by rw [hadef]; push_cast; ring
  have hua : u * 2 ^ c < (a : ℝ) := by rw [ha_real]; linarith
  have hav : (a : ℝ) + 1 < v * 2 ^ c := by rw [ha_real]; linarith
  have ha_lt : a < 2 ^ c := by
    have h1 : (a : ℝ) + 1 < (2 : ℝ) ^ c := by
      have : v * 2 ^ c ≤ 1 * 2 ^ c := by gcongr
      linarith
    have h2 : ((a : ℕ) : ℝ) < ((2 ^ c : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h2
  -- the late boundary visit
  obtain ⟨k, hk, hn3, hsC, hread⟩ :=
    stoneham_boundary_readout_recurrence c a (N + c) hc3 ha_lt hgrid
  refine ⟨3 ^ k - c, ?_, ?_⟩
  · have : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
    omega
  · obtain ⟨hlo, hhi⟩ := stoneham_orbit_readout_cell (3 ^ k - c) hn3
    rw [hsC, hread] at hlo hhi
    constructor
    · have : u ≤ (a : ℝ) / 2 ^ c := by rw [le_div_iff₀ h2c]; linarith
      linarith
    · have : ((a : ℝ) + 1) / 2 ^ c < v := by rw [div_lt_iff₀ h2c]; linarith
      linarith

/-- Every finite base-6 word occurs in the Stoneham constant alpha_(2,3).
Frozen headline.  This is weaker than normality, which is false in base 6. -/
theorem isDisjunctive_six_stoneham23 : IsDisjunctive 6 stoneham23 := by
  intro u v hu huv hv
  obtain ⟨n, _, hn⟩ := stoneham_base6_interval_recurrence u v hu huv hv 0
  exact ⟨n, hn⟩

end NormalNumbers
