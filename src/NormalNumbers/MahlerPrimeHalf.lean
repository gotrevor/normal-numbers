/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerPrimeUpper

/-!
# The prime-base upper bound, halved: `M(g,1) ≤ g(g+1)/2` 🧮

`MahlerMultiplier.lean` gives `M(g,k) ≤ g^(k+1)` and `MahlerPrimeUpper.lean`
shaves `2g − 3` off it for prime `g` by excluding the shadow denominator
`q = 1`.  That exclusion looked like the end of the line: `PENDING_WORK.md`
records that *excluding* a denominator `q ≥ 2` is unavailable (the coprimality
that drives the `q = 1` argument fails once `gcd(A, q gᵏ) ≥ gᵏ`), and that even
a perfect exclusion would stop at `≈ g²/2`.

This file reaches that `g²/2` — not by excluding small denominators but by
**converting** them.  The observation:

> if `x_n` is within `g^(−k)/q` of `p/q`, then `q x_n` is within `g^(−k)` of an
> integer, i.e. the orbit of `q·α` has a run of `k` zeros (or of `k` digits
> `g − 1`) at time `n`.

`MahlerRunBranch` settles that branch for `q·α` at multiplier `m' ≤ gᵏ`, and
`m'·(q α) = (m' q)·α`, so a small denominator `q` costs a multiplier of only
`q gᵏ` — no exclusion needed, and no coprimality (`mahler_multiplier_near_grid`).

So for any threshold `q₀`, every orbit point either sits near a grid of
denominator `< q₀` — costing `≤ (q₀−1) gᵏ` — or all its rational shadows have
denominator `≥ q₀`, and the covering sweep then only needs

    M ≥ g^(k+1) − q₀(g − 2) − 1

(`mahler_multiplier_prime_param`).  Balancing the two at `k = 1` with
`q₀ = (g+1)/2` gives both sides equal to `g(g+1)/2`:

    **`M(g,1) ≤ g(g+1)/2`   for every odd prime `g`**

(`mahler_multiplier_prime_half`) — a factor `2 − o(1)` off the `g²` headline,
and the first bound at a prime base with the right order of magnitude
(`MahlerPrimeLowerBound.lean` gives `Θ(g²)` from below; the exact values
`M(5,1) = 6`, `M(7,1) = 9` sit near `g²/4`, so what remains is a factor `2`).
-/

namespace NormalNumbers.Mahler

open NormalNumbers

/-- **The small-denominator branch.**  If the orbit of `q·α` comes within
`g^(−k)` of an integer infinitely often — which is what "`α` is repeatedly
within `g^(−k)/q` of the `q`-grid" means — then some multiplier `m ≤ q·gᵏ`
already produces every `k`-block infinitely often in `m·α`. -/
theorem mahler_multiplier_near_grid (g : ℕ) (hgp : g.Prime) (α : ℝ) (hα : Irrational α)
    (w : List ℕ) (hwd : ∀ d ∈ w, d < g) (hk : 1 ≤ w.length) (q : ℕ) (hq : 1 ≤ q)
    (hnear : ∀ N, ∃ n, N ≤ n ∧ ∃ p : ℤ,
      |orbit g ((q : ℝ) * α) n - p| < 1 / (g : ℝ) ^ w.length) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ q * g ^ w.length ∧
      ∀ N, ∃ n, N ≤ n ∧ OccursAt g ((m : ℝ) * α) w n := by
  have hg : 2 ≤ g := hgp.two_le
  set k := w.length with hkdef
  have hqα : Irrational ((q : ℝ) * α) := hα.natCast_mul (by omega)
  -- the runs, in one of the two flavours
  have hrun : (∀ N, ∃ n, N ≤ n ∧ OccursAt g ((q : ℝ) * α) (List.replicate k 0) n) ∨
      (∀ N, ∃ n, N ≤ n ∧ OccursAt g ((q : ℝ) * α) (List.replicate k (g - 1)) n) := by
    by_cases hz : ∀ N, ∃ n, N ≤ n ∧ OccursAt g ((q : ℝ) * α) (List.replicate k 0) n
    · exact Or.inl hz
    · right
      push Not at hz
      obtain ⟨N₀, hN₀⟩ := hz
      intro N
      obtain ⟨n, hn, p, hp⟩ := hnear (max N N₀)
      refine ⟨n, le_trans (le_max_left _ _) hn, ?_⟩
      rcases orbit_run_of_den_one g k hg hk ((q : ℝ) * α) n p hp with h | h
      · exact absurd h (hN₀ n (le_trans (le_max_right _ _) hn))
      · exact h
  -- feed the run branch, then fold the `q` into the multiplier
  have hmul : ∀ (m : ℕ) (N : ℕ), (∃ n, N ≤ n ∧ OccursAt g ((m : ℝ) * ((q : ℝ) * α)) w n) →
      ∃ n, N ≤ n ∧ OccursAt g (((m * q : ℕ) : ℝ) * α) w n := by
    intro m N h
    obtain ⟨n, hn, hocc⟩ := h
    refine ⟨n, hn, ?_⟩
    rwa [show (((m * q : ℕ) : ℝ) * α) = (m : ℝ) * ((q : ℝ) * α) by push_cast; ring]
  rcases hrun with h | h
  · obtain ⟨m, hm1, hm2, hm3⟩ :=
      mahler_multiplier_of_zero_runs g hgp ((q : ℝ) * α) hqα w hwd hk h
    exact ⟨m * q, Nat.mul_pos hm1 hq, by
      rw [mul_comm]; exact Nat.mul_le_mul_left q hm2, fun N => hmul m N (hm3 N)⟩
  · obtain ⟨m, hm1, hm2, hm3⟩ :=
      mahler_multiplier_of_pred_runs g hgp ((q : ℝ) * α) hqα w hwd hk h
    exact ⟨m * q, Nat.mul_pos hm1 hq, by
      rw [mul_comm]; exact Nat.mul_le_mul_left q hm2, fun N => hmul m N (hm3 N)⟩

/-- **The covering contraction above a denominator threshold.**  If the
multiples `m x`, `1 ≤ m ≤ M`, all miss the cell of `W` and
`g^(k+1) ≤ q₀(g−2) + M + 1`, then every rational `ρ` with
`q₀ ≤ ρ.den ≤ gᵏ` and defect `< g^(−k)` has defect `< g^(−k)/g`. -/
theorem defect_contracts_of_bad_ge (g k W q₀ M : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k)
    (hW : W < g ^ k) (hM : g ^ (k + 1) ≤ q₀ * (g - 2) + M + 1)
    (x : ℝ) (hx : Irrational x)
    (hbad : ∀ m : ℕ, 1 ≤ m → m ≤ M →
      Int.fract ((m : ℝ) * x) ∉
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k))
    (ρ : ℚ) (hden0 : q₀ ≤ ρ.den) (hden : ρ.den ≤ g ^ k)
    (hη : |(ρ.den : ℝ) * x - ρ.num| < 1 / (g : ℝ) ^ k) :
    (g : ℝ) * |(ρ.den : ℝ) * x - ρ.num| < 1 / (g : ℝ) ^ k := by
  have hcop : IsCoprime ρ.num (ρ.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact ρ.reduced
  have h := defect_bound_of_bad g k W hg hW M x hx hbad ρ.num ρ.den ρ.pos hden hcop hη
  set E : ℝ := |(ρ.den : ℝ) * x - ρ.num| with hEdef
  set Q : ℝ := (g : ℝ) ^ k with hQdef
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hQ2 : (2 : ℝ) ≤ Q := by
    rw [hQdef]
    have h1 : (2 : ℝ) ≤ (2 : ℝ) ^ k := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
        _ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
    have h2 : (2 : ℝ) ^ k ≤ (g : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) hgR k
    linarith
  have hQ0 : 0 < Q := by linarith
  have hg0 : (0 : ℝ) < g := by linarith
  have hqQ : (ρ.den : ℝ) ≤ Q := by rw [hQdef]; exact_mod_cast hden
  have hq0R : (q₀ : ℝ) ≤ ρ.den := by exact_mod_cast hden0
  -- the hypothesis `hM`, cast to `ℝ` without truncated subtraction
  have hgsub : ((g - 2 : ℕ) : ℝ) = (g : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hMR : (g : ℝ) * Q ≤ (q₀ : ℝ) * ((g : ℝ) - 2) + M + 1 := by
    have := (Nat.cast_le (α := ℝ)).2 hM
    push_cast [hgsub] at this
    calc (g : ℝ) * Q = ((g : ℝ) ^ (k + 1)) := by rw [hQdef, pow_succ]; ring
      _ ≤ (q₀ : ℝ) * ((g : ℝ) - 2) + M + 1 := this
  by_contra hcon
  push Not at hcon
  have hEge : 1 / ((g : ℝ) * Q) ≤ E := by
    have h1 : 1 ≤ (g : ℝ) * E * Q := by
      have h2 := mul_le_mul_of_nonneg_right hcon hQ0.le
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hQ0)] at h2
      linarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith [h1]
  -- `M + 1 − 2q ≥ g(Q − q)` because `q ≥ q₀` and `g ≥ 2`
  have hcoef : (g : ℝ) * (Q - ρ.den) ≤ (M : ℝ) + 1 - 2 * ρ.den := by
    nlinarith [mul_le_mul_of_nonneg_right hq0R (by linarith : (0 : ℝ) ≤ (g : ℝ) - 2)]
  have hcoef0 : 0 ≤ (g : ℝ) * (Q - ρ.den) := by nlinarith
  have hfin : 1 - (ρ.den : ℝ) / Q ≤ ((M : ℝ) + 1 - 2 * ρ.den) * E := by
    calc 1 - (ρ.den : ℝ) / Q = ((g : ℝ) * (Q - ρ.den)) * (1 / ((g : ℝ) * Q)) := by
          field_simp
      _ ≤ ((g : ℝ) * (Q - ρ.den)) * E := mul_le_mul_of_nonneg_left hEge hcoef0
      _ ≤ ((M : ℝ) + 1 - 2 * ρ.den) * E := by
          apply mul_le_mul_of_nonneg_right hcoef
          rw [hEdef]; positivity
  linarith

/-- **The parameterized prime upper bound.**  Fix a denominator threshold
`q₀ ≤ gᵏ`.  If the budget `M` covers both the small-denominator branch
(`(q₀−1)gᵏ ≤ M`) and the covering sweep above the threshold
(`g^(k+1) ≤ q₀(g−2) + M + 1`), then `M` multipliers suffice. -/
theorem mahler_multiplier_prime_param (g : ℕ) (hgp : g.Prime) (q₀ M : ℕ) (hq₀ : 1 ≤ q₀)
    (α : ℝ) (hα : Irrational α) (w : List ℕ) (hwd : ∀ d ∈ w, d < g) (hk : 1 ≤ w.length)
    (hq₀Q : q₀ ≤ g ^ w.length)
    (hMrun : (q₀ - 1) * g ^ w.length ≤ M)
    (hMcov : g ^ (w.length + 1) ≤ q₀ * (g - 2) + M + 1) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ M ∧ ∀ N, ∃ n, N ≤ n ∧ OccursAt g ((m : ℝ) * α) w n := by
  have hg : 2 ≤ g := hgp.two_le
  set k := w.length with hkdef
  set W := blockNatVal g w with hWdef
  have hW : W < g ^ k := blockNatVal_lt g w hwd
  -- Branch A: some `q < q₀` has the orbit of `q·α` near an integer infinitely often
  by_cases hgrid : ∃ q : ℕ, 1 ≤ q ∧ q < q₀ ∧ ∀ N, ∃ n, N ≤ n ∧ ∃ p : ℤ,
      |orbit g ((q : ℝ) * α) n - p| < 1 / (g : ℝ) ^ k
  · obtain ⟨q, hq1, hqlt, hnear⟩ := hgrid
    obtain ⟨m, hm1, hm2, hm3⟩ :=
      mahler_multiplier_near_grid g hgp α hα w hwd hk q hq1 hnear
    refine ⟨m, hm1, le_trans hm2 (le_trans ?_ hMrun), hm3⟩
    exact Nat.mul_le_mul_right _ (by omega)
  -- Branch B: every shadow denominator is eventually `≥ q₀`
  push Not at hgrid
  choose! Nq hNq using hgrid
  set N₁ := (Finset.range q₀).sup Nq with hN₁def
  by_contra hcon
  push Not at hcon
  choose! Nf hNf using hcon
  set N₀ := max N₁ ((Finset.range (M + 1)).sup Nf) with hN₀def
  have hN₀ : ∀ m, m ≤ M → Nf m ≤ N₀ := fun m hm =>
    le_trans (Finset.le_sup (f := Nf) (Finset.mem_range.2 (by omega))) (le_max_right _ _)
  have hbad : ∀ n, N₀ ≤ n → ∀ m : ℕ, 1 ≤ m → m ≤ M →
      Int.fract ((m : ℝ) * orbit g α n) ∉
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k) := by
    intro n hn m hm1 hmM hmem
    apply hNf m hm1 hmM n (le_trans (hN₀ m hmM) hn)
    rw [occursAt_iff_orbit_mem g hg _ w hwd n, orbit_nat_mul]
    exact hmem
  have hgk1 : 1 ≤ g ^ k := Nat.one_le_pow _ _ (by omega)
  apply orbit_escapes g hg α hα (g ^ k) hgk1 N₀
  intro n hn ρ hden hsmall
  have hcastQ : ((g ^ k : ℕ) : ℝ) = (g : ℝ) ^ k := by push_cast; ring
  rw [hcastQ] at hsmall ⊢
  -- the denominator is at least `q₀`
  have hden0 : q₀ ≤ ρ.den := by
    by_contra hc
    push Not at hc
    have hq1 : 1 ≤ ρ.den := ρ.pos
    have hNle : Nq ρ.den ≤ n := by
      refine le_trans (Finset.le_sup (f := Nq) (Finset.mem_range.2 hc)) ?_
      exact le_trans (le_max_left _ _) hn
    have hfr : orbit g ((ρ.den : ℝ) * α) n = Int.fract ((ρ.den : ℝ) * orbit g α n) :=
      orbit_nat_mul g α ρ.den n
    have heq : Int.fract ((ρ.den : ℝ) * orbit g α n)
        - ((ρ.num - ⌊(ρ.den : ℝ) * orbit g α n⌋ : ℤ) : ℝ)
        = (ρ.den : ℝ) * orbit g α n - ρ.num := by
      rw [Int.fract]; push_cast; ring
    have hbig := hNq ρ.den hq1 hc n hNle (ρ.num - ⌊(ρ.den : ℝ) * orbit g α n⌋)
    rw [hfr, heq] at hbig
    linarith
  exact defect_contracts_of_bad_ge g k W q₀ M hg hk hW hMcov (orbit g α n)
    (orbit_irrational g hg α hα n) (hbad n hn) ρ hden0 hden hsmall


/-- **`M(g,k) ≤ g^(k+1) − (g−1)²` for prime `g` and `k ≥ 2`.**  The threshold
`q₀ = g` instance of `mahler_multiplier_prime_param`: the small-denominator
branch costs `(g−1)gᵏ = g^(k+1) − gᵏ`, the covering sweep above the threshold
costs `g^(k+1) − g(g−2) − 1`, and for `k ≥ 2` the second dominates.  The saving
over `mahler_multiplier` is `(g−1)² − ...`, i.e. `g² − 2g + 1`; the `k = 1` case
is much better served by `mahler_multiplier_prime_half`. -/
theorem mahler_multiplier_prime_gen (g : ℕ) (hgp : g.Prime)
    (α : ℝ) (hα : Irrational α) (w : List ℕ) (hwd : ∀ d ∈ w, d < g) (hk : 2 ≤ w.length) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ g ^ (w.length + 1) - (g * (g - 2) + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ OccursAt g ((m : ℝ) * α) w n := by
  have hg : 2 ≤ g := hgp.two_le
  have hgk : g ≤ g ^ w.length := Nat.le_self_pow (by omega) g
  have hg2k : g * g ≤ g ^ w.length := by
    have : g ^ 2 ≤ g ^ w.length := Nat.pow_le_pow_right (by omega) hk
    calc g * g = g ^ 2 := by ring
      _ ≤ g ^ w.length := this
  have hpow : g ^ (w.length + 1) = g ^ w.length * g := by ring
  have hmul2 : g ^ w.length * 2 ≤ g ^ w.length * g := Nat.mul_le_mul_left _ hg
  have hgg : g * (g - 2) + g ≤ g * g := by
    obtain ⟨j, hj⟩ : ∃ j, g = j + 2 := ⟨g - 2, by omega⟩
    subst hj
    have hs : j + 2 - 2 = j := by omega
    rw [hs]; ring_nf; omega
  have hpeel : (g - 1) * g ^ w.length + g ^ w.length = g ^ w.length * g := by
    obtain ⟨j, hj⟩ : ∃ j, g = j + 2 := ⟨g - 2, by omega⟩
    subst hj
    have hs : j + 2 - 1 = j + 1 := by omega
    rw [hs]; ring
  refine mahler_multiplier_prime_param g hgp g
    (g ^ (w.length + 1) - (g * (g - 2) + 1)) (by omega) α hα w hwd (by omega) hgk ?_ ?_ <;> omega

/-- **`M(g,1) ≤ g(g+1)/2` for every odd prime `g`.**  Half the `g²` headline of
`mahler_multiplier`, and the first prime-base upper bound of the right order of
magnitude: `MahlerPrimeLowerBound.lean` gives `Θ(g²)` from below, and the exact
values `M(5,1) = 6`, `M(7,1) = 9` sit near `g²/4`. -/
theorem mahler_multiplier_prime_half (g : ℕ) (hgp : g.Prime) (hodd : g % 2 = 1)
    (α : ℝ) (hα : Irrational α) (w : List ℕ) (hwd : ∀ d ∈ w, d < g) (hk : w.length = 1) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ g * (g + 1) / 2 ∧
      ∀ N, ∃ n, N ≤ n ∧ OccursAt g ((m : ℝ) * α) w n := by
  have hg : 2 ≤ g := hgp.two_le
  have hg3 : 3 ≤ g := by omega
  set q₀ := (g + 1) / 2 with hq₀def
  have hq₀2 : 2 * q₀ = g + 1 := by omega
  have hM2 : 2 * (g * (g + 1) / 2) = g * (g + 1) := by
    have : 2 ∣ g * (g + 1) := by
      rcases Nat.even_or_odd g with he | ho
      · exact Dvd.dvd.mul_right he.two_dvd _
      · exact Dvd.dvd.mul_left (by omega : 2 ∣ g + 1) _
    omega
  refine mahler_multiplier_prime_param g hgp q₀ (g * (g + 1) / 2) (by omega) α hα w hwd
    (by omega) ?_ ?_ ?_
  · rw [hk, pow_one]; omega
  · rw [hk, pow_one]
    have h1 : (q₀ - 1) * g * 2 = (g - 1) * g := by
      have : 2 * (q₀ - 1) = g - 1 := by omega
      calc (q₀ - 1) * g * 2 = (2 * (q₀ - 1)) * g := by ring
        _ = (g - 1) * g := by rw [this]
    have h2 : (g - 1) * g + 2 * g = g * (g + 1) := by
      obtain ⟨j, rfl⟩ : ∃ j, g = j + 3 := ⟨g - 3, by omega⟩
      have hs : j + 3 - 1 = j + 2 := by omega
      rw [hs]; ring
    omega
  · rw [hk, pow_succ, pow_one]
    have hgs : g - 2 + 2 = g := by omega
    have key : 2 * (q₀ * (g - 2)) = (g + 1) * (g - 2) := by
      calc 2 * (q₀ * (g - 2)) = (2 * q₀) * (g - 2) := by ring
        _ = (g + 1) * (g - 2) := by rw [hq₀2]
    have hexp : (g + 1) * (g - 2) + (g * (g + 1)) + 2 = 2 * (g * g) := by
      obtain ⟨j, rfl⟩ : ∃ j, g = j + 3 := ⟨g - 3, by omega⟩
      have hs : j + 3 - 2 = j + 1 := by omega
      rw [hs]; ring
    omega

end NormalNumbers.Mahler
