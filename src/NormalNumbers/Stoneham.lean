/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.HotSpot
import NormalNumbers.StonehamArith

/-!
# Stoneham's theorem

R. Stoneham (1973): `α₂,₃ = Σ_{m≥1} 1/(3ᵐ·2^(3ᵐ))` is normal in base 2 —
the only known normality proof for a number defined by an honest analytic
series rather than through its own digits.  (Contrast: Bailey–Borwein 2012
showed `α₂,₃` is *not* normal in base 6 — normality is a property of the
pair (number, base).)

## Proof plan (the self-similar cascade)

Write `W_M = [3^M, 3^(M+1))` for the `M`-th window of orbit times.  For
`n ∈ W_M`, the orbit point `2^n·α mod 1` equals `c_M(n)/3^M + ε_n` with
`0 < ε_n < 2/3^(M+1)` (`stonehamState_approx`), where the integer state
`c_M(n)` (`stonehamState`) doubles mod `3^M` at each step
(`stonehamState_succ`) from a *unit* seed (`stonehamState_unit`).

By `StonehamArith`, 2 generates the full unit group mod `3^M`, of order
`2·3^(M-1)`.  Since `|W_M| = 2·3^M` is exactly three periods, each window
traverses the unit cycle exactly three times: window visit counts to any
interval reduce to counting *units of `ℤ/3^M` in integer intervals*, which
is uniform to `±2` (`card_units_Ico`).

Partial windows (the frontier of the count) are partial cycles, and the
distribution of a partial doubling-cycle is exactly the incomplete-
exponential-sum wall.  The route around it (Bailey–Borwein 2013, via
Bailey–Misiurewicz 2006) is one-sided: a partial cycle's visits are a
*subset* of a full cycle's, so **upper** visit bounds survive with no
cancellation needed (`segment_visit_upper`), and the **strong hot spot
lemma** says one-sided bounds suffice: a non-normal number must have an
interval family visited with frequency exceeding any constant multiple of
its length, which the window counting rules out with an absolute constant.
The hot-spot lemma (`isNormal_of_visit_upper_bound`, statement pinned
2026-08-23 against Bailey–Misiurewicz — see
`papers/bailey-misiurewicz-2006-hot-spot.md`) is the one
piece of real analysis; everything else is exact counting in `(ℤ/3^M)ˣ`.
No character sums and no Erdős–Turán inequality anywhere.
-/

namespace NormalNumbers

/-- The Stoneham constant `α₂,₃ = Σ_{m≥1} 1/(3ᵐ·2^(3ᵐ))`. -/
noncomputable def stoneham23 : ℝ :=
  ∑' n : ℕ, 1 / ((3 : ℝ) ^ (n + 1) * 2 ^ (3 ^ (n + 1)))

/-- Head of the Stoneham series: terms `m = 1 … M`. -/
noncomputable def stonehamPartial (M : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M, 1 / ((3 : ℝ) ^ m * 2 ^ (3 ^ m))

/-- The integer orbit state at time `n` in window `M`:
`c_M(n) = (Σ_{m=1}^{M} 3^(M-m)·2^(n-3^m)) mod 3^M`.  Meaningful for
`n ≥ 3^M` (natural subtraction truncates earlier terms harmlessly only
when every `3^m ≤ n`). -/
def stonehamState (M n : ℕ) : ℕ :=
  (∑ m ∈ Finset.Icc 1 M, 3 ^ (M - m) * 2 ^ (n - 3 ^ m)) % 3 ^ M

/-- The state doubles mod `3^M` at each step (once `n ≥ 3^M`). -/
theorem stonehamState_succ (M n : ℕ) (hM : 1 ≤ M) (hn : 3 ^ M ≤ n) :
    stonehamState M (n + 1) = 2 * stonehamState M n % 3 ^ M := by
  unfold stonehamState
  have hsum : ∑ m ∈ Finset.Icc 1 M, 3 ^ (M - m) * 2 ^ (n + 1 - 3 ^ m)
      = 2 * ∑ m ∈ Finset.Icc 1 M, 3 ^ (M - m) * 2 ^ (n - 3 ^ m) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : m ≤ M := (Finset.mem_Icc.mp hm).2
    have h3m : 3 ^ m ≤ n :=
      le_trans (Nat.pow_le_pow_right (by norm_num) hm') hn
    have : n + 1 - 3 ^ m = (n - 3 ^ m) + 1 := by omega
    rw [this, pow_succ]
    ring
  rw [hsum, Nat.mul_mod, Nat.mul_mod 2 (_ % 3 ^ M), Nat.mod_mod_of_dvd _ dvd_rfl]

/-- The seed of window `M` is a unit mod `3^M`: only the `m = M` term is
prime to 3. -/
theorem stonehamState_unit (M : ℕ) (hM : 1 ≤ M) :
    ¬ 3 ∣ stonehamState M (3 ^ M) := by
  unfold stonehamState
  rw [Nat.dvd_mod_iff (dvd_pow_self 3 (by omega : M ≠ 0))]
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have hins : Finset.Icc 1 (M' + 1) = insert (M' + 1) (Finset.Icc 1 M') := by
    ext u; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hins, Finset.sum_insert (by simp [Finset.mem_Icc])]
  simp only [Nat.sub_self, pow_zero, mul_one]
  intro hdvd
  have hdvd_sum : 3 ∣ ∑ m ∈ Finset.Icc 1 M',
      3 ^ (M' + 1 - m) * 2 ^ (3 ^ (M' + 1) - 3 ^ m) := by
    refine Finset.dvd_sum fun m hm => ?_
    have hm' : m ≤ M' := (Finset.mem_Icc.mp hm).2
    exact Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) _
  omega

/-- The Stoneham series' terms. -/
noncomputable def sterm (j : ℕ) : ℝ := 1 / ((3 : ℝ) ^ (j + 1) * 2 ^ (3 ^ (j + 1)))

theorem sterm_pos (j : ℕ) : 0 < sterm j := by unfold sterm; positivity

theorem sterm_le (j : ℕ) : sterm j ≤ (1 / 2) ^ j := by
  unfold sterm
  rw [div_pow, one_pow]
  apply div_le_div_of_nonneg_left one_pos.le (by positivity)
  calc (2 : ℝ) ^ j ≤ 2 ^ (3 ^ (j + 1)) := by
        apply pow_le_pow_right₀ one_le_two
        calc j ≤ 3 ^ j := (Nat.lt_pow_self (by norm_num)).le
          _ ≤ 3 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ 3 ^ (j + 1) * 2 ^ (3 ^ (j + 1)) := by
        nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3) (n := j + 1),
          pow_pos (by norm_num : (0:ℝ) < 2) (3 ^ (j + 1))]

theorem summable_sterm : Summable sterm :=
  Summable.of_nonneg_of_le (fun j => (sterm_pos j).le) sterm_le
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

/-- Orbit points in window `M` are the rational state plus a positive
error under `2/3^(M+1)`: for `3^M ≤ n < 3^(M+1)`,
`c_M(n)/3^M < 2^n·α mod 1 < c_M(n)/3^M + 2/3^(M+1)`. -/
theorem stonehamState_approx (M n : ℕ) (hM : 1 ≤ M)
    (hn : 3 ^ M ≤ n) (hn' : n < 3 ^ (M + 1)) :
    (stonehamState M n : ℝ) / 3 ^ M < orbit 2 stoneham23 n ∧
      orbit 2 stoneham23 n
        < (stonehamState M n : ℝ) / 3 ^ M + 2 / 3 ^ (M + 1) := by
  have h3M : (0 : ℝ) < 3 ^ M := by positivity
  have h3M1 : (0 : ℝ) < 3 ^ (M + 1) := by positivity
  -- the scaled series
  set g : ℕ → ℝ := fun j => (2 : ℝ) ^ n * sterm j with hg
  have hg_sum : Summable g := summable_sterm.mul_left _
  have hg_pos : ∀ j, 0 < g j := fun j => by
    have := sterm_pos j
    simp only [hg]; positivity
  have hmul : stoneham23 * (2 : ℝ) ^ n = ∑' j, g j := by
    rw [tsum_mul_left, mul_comm]; rfl
  have hshift_sum : Summable fun j => g (j + M) :=
    (summable_nat_add_iff M).2 hg_sum
  -- split at M
  have hsplit : ∑' j, g j
      = (∑ j ∈ Finset.range M, g j) + ∑' j, g (j + M) :=
    (hg_sum.sum_add_tsum_nat_add M).symm
  set T : ℝ := ∑' j, g (j + M) with hT
  -- the raw head sum (pre-mod)
  set S : ℕ := ∑ m ∈ Finset.Icc 1 M, 3 ^ (M - m) * 2 ^ (n - 3 ^ m) with hS
  -- head = S / 3^M
  have hHead : (∑ j ∈ Finset.range M, g j) = (S : ℝ) / 3 ^ M := by
    rw [hS]
    push_cast
    rw [Finset.sum_div,
      show Finset.Icc 1 M = Finset.Ico 1 (M + 1) from by
        ext u; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjM : j < M := Finset.mem_range.mp hj
    have h3le : 3 ^ (1 + j) ≤ n :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hn
    have h2 : (2 : ℝ) ^ (n - 3 ^ (1 + j)) * 2 ^ (3 ^ (1 + j)) = 2 ^ n := by
      rw [← pow_add]; congr 1; omega
    have h3 : (3 : ℝ) ^ (M - (1 + j)) * 3 ^ (1 + j) = 3 ^ M := by
      rw [← pow_add]; congr 1; omega
    simp only [hg, sterm]
    rw [mul_one_div, div_eq_div_iff (by positivity) h3M.ne']
    rw [← h2, ← h3]; ring
  -- tail bounds
  have hT_pos : 0 < T := by
    rw [hT]
    exact Summable.tsum_pos hshift_sum (fun j => (hg_pos _).le) 0 (hg_pos _)
  have hT_le : T ≤ 1 / 3 ^ (M + 1) := by
    set c : ℝ := (2 : ℝ) ^ n / (3 ^ (M + 1) * 2 ^ (3 ^ (M + 1))) with hc
    have hterm : ∀ j, g (j + M) ≤ c * (1 / 2) ^ j := by
      intro j
      have hexp : 3 ^ (M + 1) + j ≤ 3 ^ (j + M + 1) := by
        have hj3 : j + 1 ≤ 3 ^ j := Nat.lt_pow_self (by norm_num)
        have hP : 1 ≤ 3 ^ (M + 1) := Nat.one_le_pow _ _ (by norm_num)
        calc 3 ^ (M + 1) + j ≤ 3 ^ (M + 1) * (j + 1) := by nlinarith
          _ ≤ 3 ^ (M + 1) * 3 ^ j := Nat.mul_le_mul_left _ hj3
          _ = 3 ^ (j + M + 1) := by rw [← pow_add]; congr 1; omega
      have hkey : (3 : ℝ) ^ (M + 1) * 2 ^ (3 ^ (M + 1)) * 2 ^ j
          ≤ 3 ^ (j + M + 1) * 2 ^ (3 ^ (j + M + 1)) := by
        have h3 : (3 : ℝ) ^ (M + 1) ≤ 3 ^ (j + M + 1) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have h2 : (2 : ℝ) ^ (3 ^ (M + 1)) * 2 ^ j ≤ 2 ^ (3 ^ (j + M + 1)) := by
          rw [← pow_add]
          exact pow_le_pow_right₀ one_le_two hexp
        calc (3 : ℝ) ^ (M + 1) * 2 ^ (3 ^ (M + 1)) * 2 ^ j
            = 3 ^ (M + 1) * (2 ^ (3 ^ (M + 1)) * 2 ^ j) := by ring
          _ ≤ 3 ^ (j + M + 1) * 2 ^ (3 ^ (j + M + 1)) :=
              mul_le_mul h3 h2 (by positivity) (by positivity)
      simp only [hg, sterm, hc]
      rw [mul_one_div, div_pow, one_pow, div_mul_div_comm, mul_one]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hkey
    have hgeom : Summable fun j : ℕ => c * (1 / 2) ^ j :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left c
    have hle := hshift_sum.tsum_le_tsum hterm hgeom
    rw [hT]
    refine le_trans hle ?_
    rw [tsum_mul_left, tsum_geometric_two, hc]
    have h2n : (2 : ℝ) ^ n * 2 ≤ 2 ^ (3 ^ (M + 1)) := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ one_le_two (by omega)
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    calc (2:ℝ) ^ n * 2 ≤ 2 ^ (3 ^ (M + 1)) := h2n
      _ = 1 / 3 ^ (M + 1) * (3 ^ (M + 1) * 2 ^ (3 ^ (M + 1))) := by
          field_simp
  -- peel the integer part
  have hstate : stonehamState M n = S % 3 ^ M := rfl
  have hstate_lt : stonehamState M n < 3 ^ M := by
    rw [hstate]; exact Nat.mod_lt _ (pow_pos (by norm_num) M)
  have hcast : (S : ℝ) / 3 ^ M
      = ((S / 3 ^ M : ℕ) : ℝ) + (stonehamState M n : ℝ) / 3 ^ M := by
    have h := Nat.div_add_mod S (3 ^ M)
    rw [hstate]
    have hSr : (S : ℝ) = (3:ℝ) ^ M * ((S / 3 ^ M : ℕ) : ℝ) + ((S % 3 ^ M : ℕ) : ℝ) := by
      exact_mod_cast h.symm
    rw [hSr]
    field_simp
  have hy_nonneg : 0 ≤ (stonehamState M n : ℝ) / 3 ^ M + T := by positivity
  have hy_lt : (stonehamState M n : ℝ) / 3 ^ M + T < 1 := by
    have h1 : (stonehamState M n : ℝ) ≤ (3:ℝ) ^ M - 1 := by
      have : (stonehamState M n : ℕ) + 1 ≤ 3 ^ M := hstate_lt
      have := (Nat.cast_le (α := ℝ)).2 this
      push_cast at this
      linarith
    have h3 : (1:ℝ) / 3 ^ (M + 1) < 1 / 3 ^ M := by
      apply div_lt_div_of_pos_left one_pos h3M
      exact pow_lt_pow_right₀ (by norm_num) (by omega)
    have hsplit1 : ((3:ℝ) ^ M - 1) / 3 ^ M + 1 / 3 ^ M = 1 := by
      field_simp
      ring
    have hdiv : (stonehamState M n : ℝ) / 3 ^ M ≤ ((3:ℝ) ^ M - 1) / 3 ^ M := by
      gcongr
    linarith
  have horb : orbit 2 stoneham23 n = (stonehamState M n : ℝ) / 3 ^ M + T := by
    unfold orbit
    have hb2 : ((2:ℕ) : ℝ) = (2:ℝ) := by norm_num
    rw [hb2, hmul, hsplit, hHead, hcast, add_assoc, Int.fract_natCast_add]
    exact Int.fract_eq_self.mpr ⟨hy_nonneg, hy_lt⟩
  refine ⟨?_, ?_⟩
  · rw [horb]; linarith
  · rw [horb]
    have h2x : (2:ℝ) / 3 ^ (M + 1) = 2 * (1 / 3 ^ (M + 1)) := by ring
    have hxpos : (0:ℝ) < 1 / 3 ^ (M + 1) := by positivity
    rw [h2x]
    linarith

/-- Units of `ℤ/3^M` in an integer interval are uniform to `±2`:
`(q-p)·2/3 - 2 ≤ #{u ∈ [p,q) : ¬3∣u} ≤ (q-p)·2/3 + 2` (stated with
`3·card` to stay in `ℕ`). -/
theorem card_units_Ico (p q : ℕ) (hpq : p ≤ q) :
    2 * (q - p) - 6 ≤ 3 * ((Finset.Ico p q).filter fun u => ¬ 3 ∣ u).card ∧
      3 * ((Finset.Ico p q).filter fun u => ¬ 3 ∣ u).card ≤ 2 * (q - p) + 6 := by
  suffices h : ((Finset.Ico p q).filter fun u => ¬ 3 ∣ u).card
      = (q - (q + 2) / 3) - (p - (p + 2) / 3) by
    rw [h]; omega
  clear hpq
  induction q with
  | zero =>
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · rw [Finset.Ico_eq_empty (by omega)]; simp
  | succ q ih =>
    rcases Nat.lt_or_ge q p with hq | hq
    · rcases Nat.lt_or_ge (q + 1) p with hq1 | hq1
      · rw [Finset.Ico_eq_empty (by omega)]; simp; omega
      · have : p = q + 1 := by omega
        subst this; simp
    · rw [Nat.Ico_succ_right_eq_insert_Ico hq, Finset.filter_insert]
      have hmem : q ∉ (Finset.Ico p q).filter fun u => ¬ 3 ∣ u := by
        simp [Finset.mem_Ico]
      by_cases h3 : 3 ∣ q
      · rw [if_neg (by simpa using h3), ih]
        omega
      · rw [if_pos h3, Finset.card_insert_of_notMem hmem, ih]
        omega

/-- Counting a predicate of the residue: `#{q < B·T : p (q % T)} = B · #{r < T : p r}`. -/
theorem card_filter_mod_pred (B T : ℕ) (hT : 0 < T) (p : ℕ → Prop) [DecidablePred p] :
    ((Finset.range (B * T)).filter fun q => p (q % T)).card
      = B * ((Finset.range T).filter p).card := by
  classical
  have key : ((Finset.range (B * T)).filter fun q => p (q % T)).card
      = (Finset.range B ×ˢ ((Finset.range T).filter p)).card := by
    refine Finset.card_nbij' (fun q => (q / T, q % T)) (fun r => r.1 * T + r.2)
      ?_ ?_ ?_ ?_
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range,
        Finset.mem_product] at hq ⊢
      exact ⟨Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hq.1),
        Nat.mod_lt _ hT, hq.2⟩
    · intro r hr
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range,
        Finset.mem_product] at hr ⊢
      obtain ⟨h1, h2, hp⟩ := hr
      have hmod : (r.1 * T + r.2) % T = r.2 := by
        rw [mul_comm r.1 T, Nat.mul_add_mod, Nat.mod_eq_of_lt h2]
      constructor
      · calc r.1 * T + r.2 < r.1 * T + T := by omega
          _ = (r.1 + 1) * T := by ring
          _ ≤ B * T := Nat.mul_le_mul_right T h1
      · rw [hmod]; exact hp
    · intro q _
      show q / T * T + q % T = q
      rw [mul_comm (q / T) T, Nat.div_add_mod]
    · intro r hr
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range,
        Finset.mem_product] at hr
      have hdiv : (r.1 * T + r.2) / T = r.1 := by
        rw [mul_comm r.1 T, Nat.mul_add_div hT, Nat.div_eq_of_lt hr.2.1, add_zero]
      have hmod : (r.1 * T + r.2) % T = r.2 := by
        rw [mul_comm r.1 T, Nat.mul_add_mod, Nat.mod_eq_of_lt hr.2.1]
      rw [Prod.ext_iff]
      exact ⟨hdiv, hmod⟩
  rw [key, Finset.card_product, Finset.card_range]

/-- **One-sided segment bound**: a doubling-orbit segment of any length
`ℓ` visits an interval at most as often as `⌈ℓ/ord⌉` full unit cycles do —
a partial cycle is a subset of a full one, so no cancellation is needed.
With `ord = 2·3^(M-1)` and the unit-counting bound, the visits to
`[a, c)` are at most `(⌊ℓ/ord⌋ + 1)·((c-a)·2·3^(M-1) + 4)`. -/
theorem segment_visit_upper (M : ℕ) (hM : 1 ≤ M) (u : ℕ)
    (hu : ¬ 3 ∣ u) (a c : ℝ) (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1)
    (ℓ : ℕ) :
    (((Finset.range ℓ).filter fun j =>
        ((u * 2 ^ j % 3 ^ M : ℕ) : ℝ) / 3 ^ M ∈ Set.Ico a c).card : ℝ)
      ≤ (ℓ / (2 * 3 ^ (M - 1)) + 1) * ((c - a) * (2 * 3 ^ (M - 1)) + 4) := by
  classical
  set ord : ℕ := 2 * 3 ^ (M - 1) with horddef
  have hordpos : 0 < ord := by positivity
  have hPpos : 0 < (3:ℕ) ^ M := pow_pos (by norm_num) M
  have h3P : (3:ℕ) ∣ 3 ^ M := dvd_pow_self 3 (by omega : M ≠ 0)
  -- the mod-P residues along the doubling orbit
  set f : ℕ → ℕ := fun r => u * 2 ^ r % 3 ^ M with hf
  -- period ord
  have h2ord : 2 ^ ord ≡ 1 [MOD 3 ^ M] := by
    have h := two_pow_modEq_one (M - 1)
    have hM' : M - 1 + 1 = M := by omega
    rw [hM'] at h
    rw [horddef]
    exact h
  have hper : ∀ j : ℕ, f j = f (j % ord) := by
    intro j
    show u * 2 ^ j % 3 ^ M = u * 2 ^ (j % ord) % 3 ^ M
    conv_lhs => rw [← Nat.div_add_mod j ord]
    rw [pow_add, pow_mul]
    have step : (2 ^ ord) ^ (j / ord) * 2 ^ (j % ord)
        ≡ 1 ^ (j / ord) * 2 ^ (j % ord) [MOD 3 ^ M] :=
      Nat.ModEq.mul_right _ (h2ord.pow _)
    have hfin := step.mul_left u
    simp only [one_pow, one_mul] at hfin
    exact hfin
  -- the interval membership predicate on residues
  set p : ℕ → Prop := fun r => ((f r : ℕ) : ℝ) / 3 ^ M ∈ Set.Ico a c with hp
  -- the count factors through j % ord
  have hcongr : ((Finset.range ℓ).filter fun j =>
        ((u * 2 ^ j % 3 ^ M : ℕ) : ℝ) / 3 ^ M ∈ Set.Ico a c)
      = (Finset.range ℓ).filter fun j => p (j % ord) := by
    refine Finset.filter_congr fun j _ => ?_
    have hj := hper j
    simp only [hf] at hj
    simp only [hp, hf, ← hj]
  rw [hcongr]
  -- inflate to full blocks
  have hlift : ℓ ≤ (ℓ / ord + 1) * ord := by
    calc ℓ = ord * (ℓ / ord) + ℓ % ord := (Nat.div_add_mod ℓ ord).symm
      _ ≤ ord * (ℓ / ord) + ord :=
          Nat.add_le_add_left (Nat.mod_lt ℓ hordpos).le _
      _ = (ℓ / ord + 1) * ord := by ring
  have hcard1 : ((Finset.range ℓ).filter fun j => p (j % ord)).card
      ≤ (ℓ / ord + 1) * ((Finset.range ord).filter p).card := by
    calc ((Finset.range ℓ).filter fun j => p (j % ord)).card
        ≤ (((Finset.range ((ℓ / ord + 1) * ord)).filter
            fun j => p (j % ord))).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (by
            intro x hx
            exact Finset.mem_range.mpr
              (lt_of_lt_of_le (Finset.mem_range.mp hx) hlift)))
      _ = (ℓ / ord + 1) * ((Finset.range ord).filter p).card :=
          card_filter_mod_pred _ _ hordpos p
  -- per-period bound via injectivity into units of an integer interval
  set pl : ℕ := ⌈a * 3 ^ M⌉₊ with hpl
  set qu : ℕ := ⌈c * 3 ^ M⌉₊ with hqu
  have h3MR : (0:ℝ) < 3 ^ M := by positivity
  have hplqu : pl ≤ qu := Nat.ceil_le_ceil (by nlinarith)
  have hucop : Nat.Coprime u (3 ^ M) := by
    exact Nat.Coprime.pow_right _
      (Nat.coprime_comm.mp ((Nat.prime_three.coprime_iff_not_dvd).mpr hu))
  have hmaps : ∀ r ∈ (Finset.range ord).filter p,
      f r ∈ (Finset.Ico pl qu).filter fun v => ¬ 3 ∣ v := by
    intro r hr
    obtain ⟨-, hpr⟩ := Finset.mem_filter.mp hr
    obtain ⟨hlo, hhi⟩ := hpr
    have hfrP : (0:ℝ) ≤ (f r : ℝ) := by positivity
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · -- pl ≤ f r
      rw [hpl]
      apply Nat.ceil_le.mpr
      rw [le_div_iff₀ h3MR] at hlo
      linarith [hlo]
    · -- f r < qu
      have h1 : ((f r : ℕ) : ℝ) < c * 3 ^ M := by
        rw [div_lt_iff₀ h3MR] at hhi
        linarith [hhi]
      have h2 : ((f r : ℕ) : ℝ) < (qu : ℝ) :=
        lt_of_lt_of_le h1 (Nat.le_ceil _)
      exact_mod_cast h2
    · -- ¬ 3 ∣ f r
      intro hdvd
      have hmod : f r % 3 = u * 2 ^ r % 3 := Nat.mod_mod_of_dvd _ h3P
      have h3ur : 3 ∣ u * 2 ^ r := by omega
      rcases (Nat.prime_three.dvd_mul).mp h3ur with h | h
      · exact hu h
      · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
        norm_num at this
  have hinj : Set.InjOn f ((Finset.range ord).filter p) := by
    intro r hr s hs hrs
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hr hs
    -- move to ZMod P
    have hz : ((u * 2 ^ r : ℕ) : ZMod (3 ^ M)) = ((u * 2 ^ s : ℕ) : ZMod (3 ^ M)) := by
      rw [ZMod.natCast_eq_natCast_iff]
      show u * 2 ^ r % 3 ^ M = u * 2 ^ s % 3 ^ M
      exact hrs
    push_cast at hz
    -- cancel the unit u
    set U : (ZMod (3 ^ M))ˣ := ZMod.unitOfCoprime u hucop with hU
    have hUcoe : (U : ZMod (3 ^ M)) = (u : ℕ) := ZMod.coe_unitOfCoprime _ _
    have h2eq : ((2 : ZMod (3 ^ M))) ^ r = (2 : ZMod (3 ^ M)) ^ s := by
      have hcg := congrArg
        (fun x => ((U⁻¹ : (ZMod (3 ^ M))ˣ) : ZMod (3 ^ M)) * x) hz
      simpa [← hUcoe, ← mul_assoc, Units.inv_mul] using hcg
    -- transfer to the unit group and use injectivity below the order
    have hunit : twoUnit M ^ r = twoUnit M ^ s := by
      apply Units.ext
      push_cast [twoUnit, ZMod.coe_unitOfCoprime]
      exact_mod_cast h2eq
    have hordM : orderOf (twoUnit M) = ord := by
      rw [horddef]; exact orderOf_twoUnit M hM
    have := pow_injOn_Iio_orderOf (x := twoUnit M)
      (by rw [hordM]; exact hr.1 : r ∈ Set.Iio (orderOf (twoUnit M)))
      (by rw [hordM]; exact hs.1 : s ∈ Set.Iio (orderOf (twoUnit M))) hunit
    exact this
  have hcard2 : ((Finset.range ord).filter p).card
      ≤ ((Finset.Ico pl qu).filter fun v => ¬ 3 ∣ v).card :=
    Finset.card_le_card_of_injOn f hmaps hinj
  -- unit counting
  have hcount : 3 * ((Finset.Ico pl qu).filter fun v => ¬ 3 ∣ v).card
      ≤ 2 * (qu - pl) + 6 := (card_units_Ico pl qu hplqu).2
  -- put it together over ℝ
  have hquR : (qu : ℝ) < c * 3 ^ M + 1 := by
    rw [hqu]; exact Nat.ceil_lt_add_one (by nlinarith)
  have hplR : a * 3 ^ M ≤ (pl : ℝ) := by rw [hpl]; exact Nat.le_ceil _
  have hsubR : ((qu - pl : ℕ) : ℝ) ≤ (c - a) * 3 ^ M + 1 := by
    rw [Nat.cast_sub hplqu]
    nlinarith
  have hordR : ((ord : ℕ) : ℝ) = 2 * 3 ^ (M - 1) := by
    rw [horddef]; push_cast; ring
  have h3M_split : (3:ℝ) ^ M = 3 * 3 ^ (M - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hperR : (((Finset.range ord).filter p).card : ℝ)
      ≤ (c - a) * (2 * 3 ^ (M - 1)) + 4 := by
    have hcast : (3:ℝ) * (((Finset.Ico pl qu).filter fun v => ¬ 3 ∣ v).card : ℝ)
        ≤ 2 * ((qu - pl : ℕ) : ℝ) + 6 := by exact_mod_cast hcount
    have hc2 : (((Finset.range ord).filter p).card : ℝ)
        ≤ (((Finset.Ico pl qu).filter fun v => ¬ 3 ∣ v).card : ℝ) := by
      exact_mod_cast hcard2
    have hchain : (3:ℝ) * (((Finset.range ord).filter p).card : ℝ)
        ≤ 2 * ((c - a) * 3 ^ M + 1) + 6 := by nlinarith
    have hsub2 : (c - a) * (3:ℝ) ^ M = (c - a) * (3 * 3 ^ (M - 1)) := by
      rw [← h3M_split]
    nlinarith [hchain, hsub2]
  -- final assembly
  have hcard1R : (((Finset.range ℓ).filter fun j => p (j % ord)).card : ℝ)
      ≤ ((ℓ / ord + 1 : ℕ) : ℝ) * (((Finset.range ord).filter p).card : ℝ) := by
    exact_mod_cast hcard1
  have hdivR : ((ℓ / ord : ℕ) : ℝ) + 1 ≤ (ℓ : ℝ) / (2 * 3 ^ (M - 1)) + 1 := by
    have := Nat.cast_div_le (m := ℓ) (n := ord) (α := ℝ)
    rw [hordR] at this
    linarith
  have hpernn : (0:ℝ) ≤ (c - a) * (2 * 3 ^ (M - 1)) + 4 := by nlinarith
  calc (((Finset.range ℓ).filter fun j => p (j % ord)).card : ℝ)
      ≤ ((ℓ / ord + 1 : ℕ) : ℝ) * (((Finset.range ord).filter p).card : ℝ) :=
        hcard1R
    _ ≤ ((ℓ / ord + 1 : ℕ) : ℝ) * ((c - a) * (2 * 3 ^ (M - 1)) + 4) := by
        apply mul_le_mul_of_nonneg_left hperR (by positivity)
    _ ≤ ((ℓ : ℝ) / (2 * 3 ^ (M - 1)) + 1) * ((c - a) * (2 * 3 ^ (M - 1)) + 4) := by
        apply mul_le_mul_of_nonneg_right _ hpernn
        push_cast
        exact hdivR

/-- **Strong hot spot lemma** (Bailey–Misiurewicz 2006), contrapositive
form: if there is a constant `C` such that every b-adic interval's visit
frequency is eventually `≤ C·(its length)`, then `x` is normal.
✅ Statement PINNED 2026-08-23 against the paper — see
`papers/bailey-misiurewicz-2006-hot-spot.md`: this is a faithful corollary
of its Theorem 1.1 (weak hot spot theorem: `α` is b-normal iff visit
frequencies are uniformly `O(length)` over all intervals) via a finite
covering argument — any `[c,d)` meets at most `b+2` scale-`k` b-adic
intervals for `b⁻ᵏ ≤ d−c < b⁻ᵏ⁺¹`, so the uniform b-adic bound extends to
all intervals with `B = (b+2)·C`.  The statement is fixed; the proof route
is free — ergodic or elementary block counting both qualify. -/
theorem isNormal_of_visit_upper_bound (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (C : ℝ)
    (h : ∀ k m : ℕ, m < b ^ k → ∀ᶠ n in Filter.atTop,
      (visitCount (orbit b (Int.fract x)) ((m : ℝ) / (b : ℝ) ^ k)
          ((m + 1 : ℝ) / (b : ℝ) ^ k) n : ℝ) / n ≤ C / (b : ℝ) ^ k) :
    IsNormal b x := by
  rw [isNormal_iff_equidistributed_orbit b hb x, ← funext (orbit_fract b x)]
  exact equidistributed_orbit_of_visit_upper b hb (Int.fract x) C h

/-- `α₂,₃` lies in `[0, 1)` (in fact in `(0, 1/12]`). -/
theorem stoneham23_mem_Ico : stoneham23 ∈ Set.Ico (0 : ℝ) 1 := by
  have hsum : Summable sterm := summable_sterm
  have hgeom : Summable fun j : ℕ => (1 / 24 : ℝ) * (1 / 2) ^ j :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hle : ∀ j, sterm j ≤ (1 / 24 : ℝ) * (1 / 2) ^ j := by
    intro j
    unfold sterm
    rw [div_pow, one_pow, mul_one_div, div_div]
    apply div_le_div_of_nonneg_left one_pos.le (by positivity)
    have h3 : (3 : ℝ) ≤ 3 ^ (j + 1) :=
      le_self_pow₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (j + 3) ≤ 2 ^ (3 ^ (j + 1)) := by
      apply pow_le_pow_right₀ one_le_two
      calc j + 3 ≤ 3 * (j + 1) := by omega
        _ ≤ 3 ^ (j + 1) := by
            calc 3 * (j + 1) ≤ 3 * 3 ^ j := by
                  have : j + 1 ≤ 3 ^ j := Nat.lt_pow_self (by norm_num)
                  omega
              _ = 3 ^ (j + 1) := (pow_succ' 3 j).symm
    calc (24 : ℝ) * 2 ^ j = 3 * 2 ^ (j + 3) := by ring
      _ ≤ 3 ^ (j + 1) * 2 ^ (3 ^ (j + 1)) := by
          apply mul_le_mul h3 h2 (by positivity) (by positivity)
  constructor
  · unfold stoneham23
    have : ∀ j : ℕ, (0:ℝ) ≤ 1 / ((3 : ℝ) ^ (j + 1) * 2 ^ (3 ^ (j + 1))) := by
      intro j; positivity
    exact tsum_nonneg this
  · have h1 : stoneham23 ≤ ∑' j : ℕ, (1 / 24 : ℝ) * (1 / 2) ^ j :=
      hsum.tsum_le_tsum hle hgeom
    rw [tsum_mul_left, tsum_geometric_two] at h1
    linarith

/-- Orbit states across window `M`: the seed doubles, so
`c_M(3^M + j) = c_M(3^M)·2^j mod 3^M`. -/
theorem stonehamState_window (M : ℕ) (hM : 1 ≤ M) (j : ℕ) :
    stonehamState M (3 ^ M + j) = stonehamState M (3 ^ M) * 2 ^ j % 3 ^ M := by
  have hPpos : 0 < 3 ^ M := pow_pos (by norm_num) M
  induction j with
  | zero =>
    rw [add_zero, pow_zero, mul_one]
    exact (Nat.mod_eq_of_lt (Nat.mod_lt _ hPpos)).symm
  | succ j ih =>
    have hstep : 3 ^ M + (j + 1) = (3 ^ M + j) + 1 := by omega
    rw [hstep, stonehamState_succ M _ hM (by omega), ih]
    have hcong := (Nat.mod_modEq (stonehamState M (3 ^ M) * 2 ^ j) (3 ^ M)).mul_left 2
    calc 2 * (stonehamState M (3 ^ M) * 2 ^ j % 3 ^ M) % 3 ^ M
        = 2 * (stonehamState M (3 ^ M) * 2 ^ j) % 3 ^ M := hcong
      _ = stonehamState M (3 ^ M) * 2 ^ (j + 1) % 3 ^ M := by
          rw [pow_succ]; ring_nf

/-- Shift a filtered-interval count to a filtered-range count. -/
theorem card_filter_Ico_shift (s t : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    ((Finset.Ico s t).filter Q).card
      = ((Finset.range (t - s)).filter fun j => Q (s + j)).card := by
  classical
  refine Finset.card_nbij' (fun n => n - s) (fun j => s + j) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico,
      Finset.mem_range] at hn ⊢
    obtain ⟨⟨h1, h2⟩, hq⟩ := hn
    refine ⟨by omega, ?_⟩
    rwa [show s + (n - s) = n by omega]
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range,
      Finset.mem_Ico] at hj ⊢
    exact ⟨⟨by omega, by omega⟩, hj.2⟩
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hn
    show s + (n - s) = n
    omega
  · intro j _
    show s + j - s = j
    omega

/-- Visits of an initial segment of window `M` to `[a, c)`, in terms of the
window length: the interval widens by the approximation error `2/3^(M+1)`. -/
theorem window_visit_bound (M : ℕ) (hM : 1 ≤ M) (a c : ℝ)
    (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1) (ℓ : ℕ) (hℓ : ℓ ≤ 2 * 3 ^ M) :
    (((Finset.range ℓ).filter fun j =>
        orbit 2 stoneham23 (3 ^ M + j) ∈ Set.Ico a c).card : ℝ)
      ≤ ((ℓ : ℝ) / (2 * 3 ^ (M - 1)) + 1)
          * ((c - a + 2 / 3 ^ (M + 1)) * (2 * 3 ^ (M - 1)) + 4) := by
  classical
  set u : ℕ := stonehamState M (3 ^ M) with hu
  have huu : ¬ 3 ∣ u := stonehamState_unit M hM
  have h3M1 : (0:ℝ) < 3 ^ (M + 1) := by positivity
  set a' : ℝ := max 0 (a - 2 / 3 ^ (M + 1)) with ha'
  have ha'0 : 0 ≤ a' := le_max_left _ _
  have ha'c : a' ≤ c := by
    apply max_le (le_trans ha hac)
    have : (0:ℝ) < 2 / 3 ^ (M + 1) := by positivity
    linarith
  -- each orbit visit forces a state visit to the widened interval
  have hsub : ((Finset.range ℓ).filter fun j =>
        orbit 2 stoneham23 (3 ^ M + j) ∈ Set.Ico a c)
      ⊆ (Finset.range ℓ).filter fun j =>
        ((u * 2 ^ j % 3 ^ M : ℕ) : ℝ) / 3 ^ M ∈ Set.Ico a' c := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ico] at hj ⊢
    obtain ⟨hjℓ, hlo, hhi⟩ := hj
    have hn : 3 ^ M ≤ 3 ^ M + j := by omega
    have hn' : 3 ^ M + j < 3 ^ (M + 1) := by
      have : (3:ℕ) ^ (M + 1) = 3 * 3 ^ M := by rw [pow_succ]; ring
      omega
    obtain ⟨happ1, happ2⟩ := stonehamState_approx M (3 ^ M + j) hM hn hn'
    rw [stonehamState_window M hM j, ← hu] at happ1 happ2
    refine ⟨hjℓ, ?_, ?_⟩
    · apply max_le
      · positivity
      · linarith
    · linarith
  calc (((Finset.range ℓ).filter fun j =>
        orbit 2 stoneham23 (3 ^ M + j) ∈ Set.Ico a c).card : ℝ)
      ≤ (((Finset.range ℓ).filter fun j =>
          ((u * 2 ^ j % 3 ^ M : ℕ) : ℝ) / 3 ^ M ∈ Set.Ico a' c).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((ℓ : ℝ) / (2 * 3 ^ (M - 1)) + 1) * ((c - a') * (2 * 3 ^ (M - 1)) + 4) :=
        segment_visit_upper M hM u huu a' c ha'0 ha'c hc ℓ
    _ ≤ ((ℓ : ℝ) / (2 * 3 ^ (M - 1)) + 1)
          * ((c - a + 2 / 3 ^ (M + 1)) * (2 * 3 ^ (M - 1)) + 4) := by
        have hwid : c - a' ≤ c - a + 2 / 3 ^ (M + 1) := by
          have : a - 2 / 3 ^ (M + 1) ≤ a' := le_max_right _ _
          linarith
        have hordnn : (0:ℝ) ≤ 2 * 3 ^ (M - 1) := by positivity
        have h1 : (0:ℝ) ≤ (ℓ : ℝ) / (2 * 3 ^ (M - 1)) + 1 := by positivity
        apply mul_le_mul_of_nonneg_left _ h1
        nlinarith [hwid, hordnn]

/-- The window bound, simplified for a dyadic interval of length `1/2^k`
in the regime `M ≥ 2k+3`: at most `2λ·ℓ + 3λ·ord` visits, `λ = 1/2^k`,
`ord = 2·3^(M-1)`. -/
theorem per_window_bound (k M ℓ : ℕ) (hMk : 2 * k + 3 ≤ M)
    (hℓ : ℓ ≤ 2 * 3 ^ M) (a c : ℝ) (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1)
    (hca : c - a = 1 / 2 ^ k) :
    (((Finset.range ℓ).filter fun j =>
        orbit 2 stoneham23 (3 ^ M + j) ∈ Set.Ico a c).card : ℝ)
      ≤ 2 * (1 / 2 ^ k) * ℓ + 3 * (1 / 2 ^ k) * (2 * 3 ^ (M - 1)) := by
  have hM : 1 ≤ M := by omega
  have hord : (0:ℝ) < 2 * 3 ^ (M - 1) := by positivity
  have h2k : (0:ℝ) < 2 ^ k := by positivity
  have hlam : (0:ℝ) < 1 / 2 ^ k := by positivity
  -- error term is at most λ
  have herr : (2:ℝ) / 3 ^ (M + 1) ≤ 1 / 2 ^ k := by
    rw [div_le_div_iff₀ (by positivity) h2k]
    calc (2:ℝ) * 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
      _ ≤ 3 ^ (k + 1) := by
          apply pow_le_pow_left₀ (by norm_num) (by norm_num)
      _ ≤ 3 ^ (M + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 1 * 3 ^ (M + 1) := (one_mul _).symm
  -- the additive constant is at most λ·ord
  have h16 : (16:ℝ) ≤ 1 / 2 ^ k * (2 * 3 ^ (M - 1)) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ h2k]
    have h9 : (3:ℝ) ^ (2 * k + 2) = 9 * 9 ^ k := by
      rw [pow_add, pow_mul]
      norm_num
      ring
    calc (16:ℝ) * 2 ^ k = 2 * (8 * 2 ^ k) := by ring
      _ ≤ 2 * (9 * 9 ^ k) := by
          have : (2:ℝ) ^ k ≤ 9 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
          nlinarith
      _ = 2 * 3 ^ (2 * k + 2) := by rw [h9]
      _ ≤ 2 * 3 ^ (M - 1) := by
          have : (3:ℝ) ^ (2 * k + 2) ≤ 3 ^ (M - 1) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          linarith
  -- ℓ is at most three periods
  have hlo : (ℓ:ℝ) / (2 * 3 ^ (M - 1)) ≤ 3 := by
    rw [div_le_iff₀ hord]
    have hcast : ((2 * 3 ^ M : ℕ) : ℝ) = 2 * 3 ^ M := by push_cast; ring
    have h1 : (ℓ:ℝ) ≤ 2 * 3 ^ M := by
      calc (ℓ:ℝ) ≤ ((2 * 3 ^ M : ℕ) : ℝ) := by exact_mod_cast hℓ
        _ = 2 * 3 ^ M := hcast
    have h3M : (3:ℝ) ^ M = 3 * 3 ^ (M - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    nlinarith
  have hbase := window_visit_bound M hM a c ha hac hc ℓ hℓ
  rw [hca] at hbase
  refine le_trans hbase ?_
  set w : ℝ := 1 / 2 ^ k + 2 / 3 ^ (M + 1) with hw
  set ord : ℝ := 2 * 3 ^ (M - 1) with hodef
  set L : ℝ := (ℓ:ℝ) / ord with hL
  have hLnn : 0 ≤ L := by positivity
  have hw2 : w ≤ 2 * (1 / 2 ^ k) := by rw [hw]; linarith
  have hwnn : 0 ≤ w := by rw [hw]; positivity
  have hexp : (L + 1) * (w * ord + 4) = w * (L * ord) + 4 * L + w * ord + 4 := by
    ring
  have hLord : L * ord = (ℓ:ℝ) := by
    rw [hL]
    field_simp
  rw [hexp, hLord]
  have t1 : w * (ℓ:ℝ) ≤ 2 * (1 / 2 ^ k) * ℓ :=
    mul_le_mul_of_nonneg_right hw2 (by positivity)
  have t2 : 4 * L ≤ 12 := by linarith
  have t3 : w * ord ≤ 2 * (1 / 2 ^ k) * ord :=
    mul_le_mul_of_nonneg_right hw2 hord.le
  have hfin : 2 * (1 / 2 ^ k) * ord + (1 / 2 ^ k) * ord
      = 3 * (1 / 2 ^ k) * ord := by ring
  linarith

/-- Telescoping bound for total window lengths inside `[0, N)`. -/
theorem sum_window_len_le (N M0 Mmax : ℕ)
    (h : ∀ M ∈ Finset.Icc M0 Mmax, 3 ^ M ≤ N) :
    ∑ M ∈ Finset.Icc M0 Mmax, ((min N (3 ^ (M + 1)) - 3 ^ M : ℕ) : ℝ)
      ≤ N := by
  rcases Nat.lt_or_ge Mmax M0 with hlt | hge
  · rw [Finset.Icc_eq_empty (by omega)]
    simp
  · set fR : ℕ → ℝ := fun X => ((min N (3 ^ X) : ℕ) : ℝ) with hfR
    have hstep : ∀ M ∈ Finset.Icc M0 Mmax,
        ((min N (3 ^ (M + 1)) - 3 ^ M : ℕ) : ℝ) = fR (M + 1) - fR M := by
      intro M hM
      have h3M : 3 ^ M ≤ N := h M hM
      have hminM : min N (3 ^ M) = 3 ^ M := min_eq_right h3M
      have hle : (3:ℕ) ^ M ≤ min N (3 ^ (M + 1)) :=
        le_min h3M (Nat.pow_le_pow_right (by norm_num) (by omega))
      simp only [hfR]
      push_cast [Nat.cast_sub hle, hminM]
      ring
    rw [Finset.sum_congr rfl hstep,
      show Finset.Icc M0 Mmax = Finset.Ico M0 (Mmax + 1) from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
      Finset.sum_Ico_eq_sum_range]
    have htel := Finset.sum_range_sub (fun i => fR (M0 + i)) (Mmax + 1 - M0)
    calc ∑ i ∈ Finset.range (Mmax + 1 - M0), (fR (M0 + i + 1) - fR (M0 + i))
        = fR (M0 + (Mmax + 1 - M0)) - fR (M0 + 0) := by
          rw [← htel]
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 1
      _ ≤ (N:ℝ) - 0 := by
          apply sub_le_sub
          · simp only [hfR]
            exact_mod_cast Nat.cast_le.mpr (min_le_left _ _)
          · simp only [hfR]; positivity
      _ = N := by ring

/-- Telescoping bound for total period lengths. -/
theorem sum_ord_le (M0 Mmax : ℕ) (hM0 : 1 ≤ M0) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : (3:ℝ) ^ Mmax ≤ B) :
    ∑ M ∈ Finset.Icc M0 Mmax, (2 * (3:ℝ) ^ (M - 1)) ≤ B := by
  rcases Nat.lt_or_ge Mmax M0 with hlt | hge
  · rw [Finset.Icc_eq_empty (by omega)]
    simpa using hB0
  · set gR : ℕ → ℝ := fun i => (3:ℝ) ^ (M0 - 1 + i) with hgR
    have hstep : ∀ M ∈ Finset.Icc M0 Mmax,
        (2 * (3:ℝ) ^ (M - 1)) = gR (M - M0 + 1) - gR (M - M0) := by
      intro M hM
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hM
      have e1 : M0 - 1 + (M - M0 + 1) = M := by omega
      have e2 : M0 - 1 + (M - M0) = M - 1 := by omega
      simp only [hgR]
      rw [e1, e2]
      have h3M : (3:ℝ) ^ M = 3 * 3 ^ (M - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h3M]
      ring
    rw [Finset.sum_congr rfl hstep,
      show Finset.Icc M0 Mmax = Finset.Ico M0 (Mmax + 1) from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
      Finset.sum_Ico_eq_sum_range]
    have htel := Finset.sum_range_sub (fun i => gR i) (Mmax + 1 - M0)
    calc ∑ i ∈ Finset.range (Mmax + 1 - M0),
          (gR (M0 + i - M0 + 1) - gR (M0 + i - M0))
        = ∑ i ∈ Finset.range (Mmax + 1 - M0), (gR (i + 1) - gR i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 2
          all_goals omega
      _ = gR (Mmax + 1 - M0) - gR 0 := htel
      _ ≤ gR (Mmax + 1 - M0) := by
          have : (0:ℝ) ≤ gR 0 := by simp only [hgR]; positivity
          linarith
      _ = (3:ℝ) ^ Mmax := by
          simp only [hgR]
          congr 1
          omega
      _ ≤ B := hB

/-- **Stoneham's theorem** (1973): `α₂,₃` is normal in base 2. -/
theorem isNormal_two_stoneham23 : IsNormal 2 stoneham23 := by
  classical
  apply isNormal_of_visit_upper_bound 2 (by norm_num) stoneham23 6
  intro k m hm
  have hfr : Int.fract stoneham23 = stoneham23 :=
    Int.fract_eq_self.mpr ⟨stoneham23_mem_Ico.1, stoneham23_mem_Ico.2⟩
  have hb2 : ((2:ℕ):ℝ) = (2:ℝ) := by norm_num
  rw [hfr, hb2]
  set a : ℝ := (m:ℝ) / 2 ^ k with hadef
  set c : ℝ := ((m:ℝ) + 1) / 2 ^ k with hcdef
  have h2k : (0:ℝ) < 2 ^ k := by positivity
  have hm' : (m:ℝ) + 1 ≤ 2 ^ k := by
    have : (m + 1 : ℕ) ≤ 2 ^ k := hm
    exact_mod_cast this
  have ha : 0 ≤ a := by rw [hadef]; positivity
  have hac : a ≤ c := by
    rw [hadef, hcdef]
    gcongr
    linarith
  have hc1 : c ≤ 1 := by rw [hcdef, div_le_one h2k]; exact hm'
  have hca : c - a = 1 / 2 ^ k := by rw [hadef, hcdef]; ring
  set M0 : ℕ := 2 * k + 3 with hM0def
  refine Filter.eventually_atTop.mpr ⟨3 ^ M0 * 2 ^ k + 1, fun N hN => ?_⟩
  have h3M0 : 27 ≤ 3 ^ M0 := by
    calc (27:ℕ) = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ M0 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2k1 : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have hN2 : 2 ≤ N := by
    have := Nat.mul_le_mul h3M0 h2k1
    omega
  set Mmax : ℕ := Nat.log 3 (N - 1) with hMdef
  set P : ℕ → Prop := fun n => orbit 2 stoneham23 n ∈ Set.Ico a c with hP
  -- decomposition of the count into windows
  have hsplit : (Finset.range N).filter P ⊆
      ((Finset.range (3 ^ M0)).filter P) ∪
        (Finset.Icc M0 Mmax).biUnion
          (fun M => (Finset.Ico (3 ^ M) (min N (3 ^ (M + 1)))).filter P) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, hPn⟩ := hn
    rcases Nat.lt_or_ge n (3 ^ M0) with hsmall | hbig
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hsmall, hPn⟩)
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨Nat.log 3 n, ?_, ?_⟩)
      · rw [Finset.mem_Icc]
        constructor
        · calc M0 = Nat.log 3 (3 ^ M0) := (Nat.log_pow (by norm_num) M0).symm
            _ ≤ Nat.log 3 n := Nat.log_mono_right hbig
        · rw [hMdef]
          exact Nat.log_mono_right (by omega)
      · rw [Finset.mem_filter, Finset.mem_Ico]
        have hn0 : n ≠ 0 := by
          have h1 : 1 ≤ 3 ^ M0 := Nat.one_le_pow _ _ (by norm_num)
          omega
        exact ⟨⟨Nat.pow_log_le_self 3 hn0,
          lt_min hnN (Nat.lt_pow_succ_log_self (by norm_num) n)⟩, hPn⟩
  have hcards : ((Finset.range N).filter P).card
      ≤ 3 ^ M0 + ∑ M ∈ Finset.Icc M0 Mmax,
          ((Finset.Ico (3 ^ M) (min N (3 ^ (M + 1)))).filter P).card := by
    calc ((Finset.range N).filter P).card
        ≤ (((Finset.range (3 ^ M0)).filter P) ∪
            (Finset.Icc M0 Mmax).biUnion
              (fun M => (Finset.Ico (3 ^ M) (min N (3 ^ (M + 1)))).filter P)).card :=
          Finset.card_le_card hsplit
      _ ≤ ((Finset.range (3 ^ M0)).filter P).card
            + ((Finset.Icc M0 Mmax).biUnion
              (fun M => (Finset.Ico (3 ^ M) (min N (3 ^ (M + 1)))).filter P)).card :=
          Finset.card_union_le _ _
      _ ≤ 3 ^ M0 + ∑ M ∈ Finset.Icc M0 Mmax,
            ((Finset.Ico (3 ^ M) (min N (3 ^ (M + 1)))).filter P).card :=
          add_le_add ((Finset.card_filter_le _ _).trans (Finset.card_range _).le)
            Finset.card_biUnion_le
  -- window bounds, over ℝ
  have hwin : ∀ M ∈ Finset.Icc M0 Mmax,
      (((Finset.Ico (3 ^ M) (min N (3 ^ (M + 1)))).filter P).card : ℝ)
        ≤ 2 * (1 / 2 ^ k) * ((min N (3 ^ (M + 1)) - 3 ^ M : ℕ) : ℝ)
          + 3 * (1 / 2 ^ k) * (2 * 3 ^ (M - 1)) := by
    intro M hMmem
    obtain ⟨hMlo, hMhi⟩ := Finset.mem_Icc.mp hMmem
    have hℓ : min N (3 ^ (M + 1)) - 3 ^ M ≤ 2 * 3 ^ M := by
      have hmr : min N (3 ^ (M + 1)) ≤ 3 ^ (M + 1) := min_le_right _ _
      have h3 : (3:ℕ) ^ (M + 1) = 3 * 3 ^ M := by rw [pow_succ]; ring
      omega
    rw [card_filter_Ico_shift]
    have := per_window_bound k M (min N (3 ^ (M + 1)) - 3 ^ M)
      (by omega) hℓ a c ha hac hc1 hca
    simpa [hP] using this
  -- window-length and period sums
  have hlog : (3:ℕ) ^ Mmax ≤ N - 1 := by
    rw [hMdef]
    exact Nat.pow_log_le_self 3 (by omega)
  have hsum1 : ∑ M ∈ Finset.Icc M0 Mmax,
      ((min N (3 ^ (M + 1)) - 3 ^ M : ℕ) : ℝ) ≤ N :=
    sum_window_len_le N M0 Mmax (fun M hMm => by
      obtain ⟨-, h2⟩ := Finset.mem_Icc.mp hMm
      calc (3:ℕ) ^ M ≤ 3 ^ Mmax := Nat.pow_le_pow_right (by norm_num) h2
        _ ≤ N - 1 := hlog
        _ ≤ N := by omega)
  have hsum2 : ∑ M ∈ Finset.Icc M0 Mmax, (2 * (3:ℝ) ^ (M - 1)) ≤ (N:ℝ) :=
    sum_ord_le M0 Mmax (by omega) N (by positivity) (by
      have h1 : (3:ℕ) ^ Mmax ≤ N := le_trans hlog (by omega)
      exact_mod_cast h1)
  -- combine
  have hcardsR : (((Finset.range N).filter P).card : ℝ)
      ≤ 3 ^ M0 + ∑ M ∈ Finset.Icc M0 Mmax,
          (((Finset.Ico (3 ^ M) (min N (3 ^ (M + 1)))).filter P).card : ℝ) := by
    exact_mod_cast hcards
  have hchain : (((Finset.range N).filter P).card : ℝ)
      ≤ 3 ^ M0 + 5 * (1 / 2 ^ k) * N := by
    have hs := Finset.sum_le_sum hwin
    have hexp : ∑ M ∈ Finset.Icc M0 Mmax,
        (2 * (1 / 2 ^ k) * ((min N (3 ^ (M + 1)) - 3 ^ M : ℕ) : ℝ)
          + 3 * (1 / 2 ^ k) * (2 * 3 ^ (M - 1)))
        = 2 * (1 / 2 ^ k) * (∑ M ∈ Finset.Icc M0 Mmax,
            ((min N (3 ^ (M + 1)) - 3 ^ M : ℕ) : ℝ))
          + 3 * (1 / 2 ^ k) * (∑ M ∈ Finset.Icc M0 Mmax, (2 * (3:ℝ) ^ (M - 1))) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hl : (0:ℝ) ≤ 1 / 2 ^ k := by positivity
    have b1 : 2 * (1 / 2 ^ k) * (∑ M ∈ Finset.Icc M0 Mmax,
        ((min N (3 ^ (M + 1)) - 3 ^ M : ℕ) : ℝ)) ≤ 2 * (1 / 2 ^ k) * N := by
      apply mul_le_mul_of_nonneg_left hsum1 (by positivity)
    have b2 : 3 * (1 / 2 ^ k) * (∑ M ∈ Finset.Icc M0 Mmax,
        (2 * (3:ℝ) ^ (M - 1))) ≤ 3 * (1 / 2 ^ k) * N := by
      apply mul_le_mul_of_nonneg_left hsum2 (by positivity)
    calc (((Finset.range N).filter P).card : ℝ)
        ≤ 3 ^ M0 + ∑ M ∈ Finset.Icc M0 Mmax,
            (((Finset.Ico (3 ^ M) (min N (3 ^ (M + 1)))).filter P).card : ℝ) :=
          hcardsR
      _ ≤ 3 ^ M0 + (2 * (1 / 2 ^ k) * N + 3 * (1 / 2 ^ k) * N) := by
          have hs2 := le_trans hs (le_of_eq hexp)
          linarith [hs2, b1, b2]
      _ = 3 ^ M0 + 5 * (1 / 2 ^ k) * N := by ring
  -- divide by N
  have hNpos : (0:ℝ) < N := by
    have : (0:ℕ) < N := by omega
    exact_mod_cast this
  have hvc : (visitCount (orbit 2 stoneham23) a c N : ℝ)
      = (((Finset.range N).filter P).card : ℝ) := rfl
  rw [div_le_iff₀ hNpos, hvc]
  have hNb : (3:ℝ) ^ M0 ≤ 1 / 2 ^ k * N := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ h2k]
    have h1 : (3 ^ M0 * 2 ^ k : ℕ) ≤ N := by omega
    calc (3:ℝ) ^ M0 * 2 ^ k = ((3 ^ M0 * 2 ^ k : ℕ) : ℝ) := by push_cast; ring
      _ ≤ N := by exact_mod_cast h1
  calc (((Finset.range N).filter P).card : ℝ)
      ≤ 3 ^ M0 + 5 * (1 / 2 ^ k) * N := hchain
    _ ≤ 1 / 2 ^ k * N + 5 * (1 / 2 ^ k) * N := by linarith
    _ = 6 / 2 ^ k * N := by ring
end NormalNumbers
