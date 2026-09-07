/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerFarey

/-!
# The multi-scale bound: `M(g,1) ≤ (g² + 6g + 1)/4` for odd primes `g` 🧮

The denominator-jump engine of `MahlerFarey.lean`, run to its conclusion.
Fix `Q = gᵏ`, a budget `M` with `μ = M + 1`, and suppose every orbit point
`x_n`, `n ≥ N₀`, is bad (no `m ≤ M` puts `m x_n` in the cell of `W`).

* At every time there is a **canonical shadow**: a rational `σ` with
  `σ.den ≤ Q` and defect `|σ.den·x_n − σ.num| < 1/(2Q)` (`canonical_exists`:
  Dirichlet gives defect `< 1/Q`, the covering lemma then squeezes it below
  `1/(2Q)` as soon as `μ > 2Q`).  By `orbit_approx_unique` it is unique, so
  its denominator `D(n)` is a genuine function of time.
* **One stage** (`stage_jump`).  Follow the shadow chain from `σ` at time `n`
  (`shadow_chain`: when `g` is coprime to `σ.den` the denominator never
  changes and the normalized defect is exactly `gⁱ·|x_n − σ|`).  Let `j+1` be
  the first time the defect reaches `1/(2Q)`.  At `n+j` the shadow is still
  canonical, so the covering lemma bounds its defect `E` by
  `(1 − d/Q)/(μ − 2d)`; at `n+j+1` it is no longer canonical, so Farey
  separation against the canonical `τ` there gives
  `τ.den · gE + d·(defect τ) ≥ 1`, and `d·(defect τ) ≤ d/μ` (the `O(1/g)`
  loss).  Hence `τ.den > (μ − d)(μ − 2d)·Q / (μ g (Q − d))`, and the
  one-variable inequality

      `d · μ g (Q − d) ≤ (μ − d)(μ − 2d) · Q`        (`jump_condition`)

  makes that `τ.den > d`: **the canonical denominator strictly increases at
  every stage**.
* **Iteration** (`den_grows`).  No exit-time count is needed: each stage
  raises the canonical denominator by at least `1`, so after `Q` stages it
  exceeds `Q` — contradiction (`no_bad_orbit`).
* **The constant.**  At `k = 1`, `Q = g`, the jump condition is the quadratic
  `(μ+2)d² − μ(g+3)d + μ² ≥ 0`, whose discriminant at `μ = (g+1)(g+5)/4` is
  exactly `−4μ²`: it holds for every real `d`.  So `M = (g² + 6g + 1)/4`
  works for every odd prime `g` (`mahler_multiplier_quarter`), i.e.

      **`M(g,1) ≤ g²/4 + O(g)`**,

  the constant the exact census `docs/mahler-exact-values-2026-09-07.md`
  sits at (`M(p,1) ≈ ⌊p/2⌋²`).  For `g ≥ 5` this retires
  `mahler_multiplier_prime_half` (`g(g+1)/2`) to a corollary.

⚠️ **Where `k = 1` enters** (found while formalizing; the paper argument in
`PENDING_WORK.md` glossed it).  The shadow `ρ' = gρ − ⌊g x_n⌋` keeps the
denominator of `ρ` only when `g ∤ ρ.den`; if `g ∣ ρ.den` the denominator DROPS
by a factor `g` and the defect is unchanged, and the jump estimate then only
returns the canonical denominator to `≈ μ/g` rather than above the previous
one.  At `k = 1` every canonical denominator is `< Q = g` (`canonical_den_lt`),
so for prime `g` it is coprime to `g` and no drop can occur.  For `k ≥ 2` the
hypothesis `hcop` below is genuinely needed and is *false* in general; the
bound `g^(k+1)/4` for `k ≥ 2` needs an additional idea and is NOT claimed here.
-/

namespace NormalNumbers.Mahler

open NormalNumbers

/-- The defect of `ρ` at `y` is `ρ.den · |y − ρ|`, sign included. -/
theorem den_mul_sub_num (ρ : ℚ) (y : ℝ) :
    (ρ.den : ℝ) * y - ρ.num = ρ.den * (y - ρ) := by
  have hd : (ρ.den : ℝ) ≠ 0 := by exact_mod_cast ρ.pos.ne'
  rw [Rat.cast_def]; field_simp

/-- **The shadow chain keeps its denominator.**  If `g` is coprime to `σ.den`,
then at every later time `n + i` there is a rational `ρ` with the SAME
denominator whose normalized defect is exactly `gⁱ` times that of `σ`:
`x_{n+i} − ρ = gⁱ (x_n − σ)`. -/
theorem shadow_chain (g : ℕ) (α : ℝ) (n : ℕ) (σ : ℚ) (hcop : Nat.Coprime g σ.den) :
    ∀ i, ∃ ρ : ℚ, ρ.den = σ.den ∧
      orbit g α (n + i) - ρ = (g : ℝ) ^ i * (orbit g α n - σ) := by
  intro i
  induction i with
  | zero => exact ⟨σ, rfl, by simp⟩
  | succ i ih =>
      obtain ⟨ρ, hden, hdef⟩ := ih
      set z : ℤ := ⌊(g : ℝ) * orbit g α (n + i)⌋ with hzdef
      -- the shadow, written as `(g ρ.num − z ρ.den) / ρ.den`
      set P : ℤ := (g : ℤ) * ρ.num - z * (ρ.den : ℤ) with hPdef
      refine ⟨(P : ℚ) / (ρ.den : ℚ), ?_, ?_⟩
      · -- denominator: `P` is coprime to `ρ.den`
        have hcopP : IsCoprime P (ρ.den : ℤ) := by
          rw [hPdef]
          rw [IsCoprime.sub_mul_right_left_iff]
          apply IsCoprime.mul_left
          · rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
            rw [hden]; exact hcop
          · rw [Int.isCoprime_iff_gcd_eq_one]; exact ρ.reduced
        have h := Rat.den_div_eq_of_coprime (a := P) (b := (ρ.den : ℤ))
          (by exact_mod_cast ρ.pos) (by
            rw [Nat.coprime_iff_gcd_eq_one, ← Int.gcd_eq_natAbs,
              ← Int.isCoprime_iff_gcd_eq_one]
            exact hcopP)
        have h' : ((P : ℚ) / (ρ.den : ℚ)).den = ρ.den := by
          have : (((P : ℚ) / ((ρ.den : ℤ) : ℚ)).den : ℤ) = (ρ.den : ℤ) := h
          exact_mod_cast this
        rw [h', hden]
      · -- defect: `x_{n+i+1} − ρ' = g (x_{n+i} − ρ)`
        have hstep : orbit g α (n + (i + 1)) = (g : ℝ) * orbit g α (n + i) - z := by
          rw [show n + (i + 1) = n + i + 1 from rfl, orbit_succ]; rfl
        have hρ'R : (((P : ℚ) / (ρ.den : ℚ) : ℚ) : ℝ) = (g : ℝ) * ρ - z := by
          have hd : (ρ.den : ℝ) ≠ 0 := by exact_mod_cast ρ.pos.ne'
          have hρ : (ρ : ℝ) = (ρ.num : ℝ) / ρ.den := by rw [Rat.cast_def]
          rw [hρ]; push_cast [hPdef]; field_simp
        rw [hstep, hρ'R, pow_succ]
        linear_combination (g : ℝ) * hdef

/-! ### The canonical shadow -/

/-- `σ` is the **canonical shadow** of `x` at scale `Q = gᵏ`: denominator
`≤ Q` and defect below `1/(2Q)`.  By `approx_unique` there is at most one. -/
def Canonical (g k : ℕ) (x : ℝ) (σ : ℚ) : Prop :=
  σ.den ≤ g ^ k ∧ |(σ.den : ℝ) * x - σ.num| < 1 / (2 * (g : ℝ) ^ k)

/-- The covering lemma, for a rational (automatically reduced) with defect
below `1/gᵏ`. -/
theorem covering_rat (g k W M : ℕ) (hg : 2 ≤ g) (hW : W < g ^ k) (x : ℝ) (hx : Irrational x)
    (hbad : ∀ m : ℕ, 1 ≤ m → m ≤ M →
      Int.fract ((m : ℝ) * x) ∉
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k))
    (σ : ℚ) (hden : σ.den ≤ g ^ k)
    (hη : |(σ.den : ℝ) * x - σ.num| < 1 / (g : ℝ) ^ k) :
    ((M : ℝ) + 1 - 2 * σ.den) * |(σ.den : ℝ) * x - σ.num| < 1 - (σ.den : ℝ) / (g : ℝ) ^ k := by
  have hcop : IsCoprime σ.num (σ.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact σ.reduced
  exact defect_bound_of_bad g k W hg hW M x hx hbad σ.num σ.den σ.pos hden hcop hη

/-- The covering lemma for a canonical shadow, denominators cleared:
`(μ − 2d)·E·Q < Q − d` with `μ = M + 1`, `d = σ.den`, `Q = gᵏ`. -/
theorem covering_canonical (g k W M : ℕ) (hg : 2 ≤ g) (hW : W < g ^ k) (x : ℝ)
    (hx : Irrational x)
    (hbad : ∀ m : ℕ, 1 ≤ m → m ≤ M →
      Int.fract ((m : ℝ) * x) ∉
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k))
    (σ : ℚ) (hσ : Canonical g k x σ) :
    ((M : ℝ) + 1 - 2 * σ.den) * |(σ.den : ℝ) * x - σ.num| * (g : ℝ) ^ k
      < (g : ℝ) ^ k - σ.den := by
  have hQ0 : (0 : ℝ) < (g : ℝ) ^ k := by
    have : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
    positivity
  have hη : |(σ.den : ℝ) * x - σ.num| < 1 / (g : ℝ) ^ k := by
    refine lt_of_lt_of_le hσ.2 ?_
    apply one_div_le_one_div_of_le hQ0; linarith
  have h := covering_rat g k W M hg hW x hx hbad σ hσ.1 hη
  have h2 := mul_lt_mul_of_pos_right h hQ0
  have e : (1 - (σ.den : ℝ) / (g : ℝ) ^ k) * (g : ℝ) ^ k = (g : ℝ) ^ k - σ.den := by
    field_simp
  rw [e] at h2; exact h2

/-- **A canonical shadow exists at every bad point** (for `M ≥ 2gᵏ`).
Dirichlet gives a rational of denominator `≤ gᵏ` with defect `< 1/gᵏ`; the
covering lemma then squeezes the defect below `1/(2gᵏ)`. -/
theorem canonical_exists (g k W M : ℕ) (hg : 2 ≤ g) (hW : W < g ^ k) (hM : 2 * g ^ k ≤ M)
    (x : ℝ) (hx : Irrational x)
    (hbad : ∀ m : ℕ, 1 ≤ m → m ≤ M →
      Int.fract ((m : ℝ) * x) ∉
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k)) :
    ∃ σ : ℚ, Canonical g k x σ := by
  have hQnat : 0 < g ^ k := by positivity
  obtain ⟨σ, hσ, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le x hQnat
  have hQR : ((g ^ k : ℕ) : ℝ) = (g : ℝ) ^ k := by push_cast; ring
  set Q : ℝ := (g : ℝ) ^ k with hQdef
  have hQ0 : 0 < Q := by
    have : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
    positivity
  have hdpos : (0 : ℝ) < σ.den := by exact_mod_cast σ.pos
  have hdQ : (σ.den : ℝ) ≤ Q := by rw [← hQR]; exact_mod_cast hden
  have hMR : 2 * Q ≤ M := by
    have := (Nat.cast_le (α := ℝ)).2 hM
    rwa [Nat.cast_mul, Nat.cast_ofNat, hQR] at this
  -- Dirichlet: defect `≤ 1/(Q+1) < 1/Q`
  rw [hQR] at hσ
  have hE : |(σ.den : ℝ) * x - σ.num| < 1 / Q := by
    rw [den_mul_sub_num, abs_mul, abs_of_pos hdpos]
    calc (σ.den : ℝ) * |x - σ| ≤ σ.den * (1 / ((Q + 1) * σ.den)) :=
          mul_le_mul_of_nonneg_left hσ hdpos.le
      _ = 1 / (Q + 1) := by field_simp
      _ < 1 / Q := by apply one_div_lt_one_div_of_lt hQ0; linarith
  refine ⟨σ, hden, ?_⟩
  by_contra hcon
  push Not at hcon
  have hcov := covering_rat g k W M hg hW x hx hbad σ hden hE
  have hcoef : 0 < (M : ℝ) + 1 - 2 * σ.den := by linarith
  have h1 : ((M : ℝ) + 1 - 2 * σ.den) * (1 / (2 * Q))
      ≤ ((M : ℝ) + 1 - 2 * σ.den) * |(σ.den : ℝ) * x - σ.num| :=
    mul_le_mul_of_nonneg_left hcon hcoef.le
  have h2 : 1 - (σ.den : ℝ) / Q ≤ ((M : ℝ) + 1 - 2 * σ.den) * (1 / (2 * Q)) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    have : (1 - (σ.den : ℝ) / Q) * (2 * Q) = 2 * Q - 2 * σ.den := by field_simp
    rw [this]; linarith
  linarith

/-- **A canonical shadow has denominator `< gᵏ`** (for `M ≥ 2gᵏ`): at
`d = gᵏ` the covering lemma's right-hand side vanishes. -/
theorem canonical_den_lt (g k W M : ℕ) (hg : 2 ≤ g) (hW : W < g ^ k) (hM : 2 * g ^ k ≤ M)
    (x : ℝ) (hx : Irrational x)
    (hbad : ∀ m : ℕ, 1 ≤ m → m ≤ M →
      Int.fract ((m : ℝ) * x) ∉
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k))
    (σ : ℚ) (hσ : Canonical g k x σ) : σ.den < g ^ k := by
  rcases lt_or_eq_of_le hσ.1 with h | h
  · exact h
  exfalso
  have hcov := covering_canonical g k W M hg hW x hx hbad σ hσ
  have hQR : ((g ^ k : ℕ) : ℝ) = (g : ℝ) ^ k := by push_cast; ring
  have hdR : (σ.den : ℝ) = (g : ℝ) ^ k := by rw [← hQR]; exact_mod_cast h
  have hMR : 2 * (g : ℝ) ^ k ≤ M := by
    have := (Nat.cast_le (α := ℝ)).2 hM
    rwa [Nat.cast_mul, Nat.cast_ofNat, hQR] at this
  rw [hdR] at hcov
  have hcoef : 0 ≤ (M : ℝ) + 1 - 2 * (g : ℝ) ^ k := by linarith
  have : 0 ≤ ((M : ℝ) + 1 - 2 * (g : ℝ) ^ k) * |(g : ℝ) ^ k * x - σ.num| * (g : ℝ) ^ k := by
    positivity
  linarith

/-! ### One stage: the canonical denominator strictly increases -/

/-- The real-number core of a stage.  With `μ = M+1`, `d` the old canonical
denominator, `t` the new one, `E` the defect of the old shadow one step before
exit and `F` the defect of the new canonical shadow:

* covering at the old shadow:  `(μ − 2d)·E·Q < Q − d`;
* covering at the new shadow:  `(μ − 2t)·F·Q < Q − t`, and `F < 1/(2Q)`;
* Farey separation at the exit time: `1 ≤ t·(gE) + d·F`;
* the jump condition:  `d·μ·g·(Q − d) ≤ (μ − d)(μ − 2d)·Q`.

Then `d < t`. -/
theorem stage_arith (μ Q g d t E F : ℝ) (hQ0 : 0 < Q) (hg0 : 0 < g)
    (hd1 : 1 ≤ d) (hdQ : d < Q) (ht1 : 1 ≤ t) (hμ : 2 * Q + 1 ≤ μ)
    (hE0 : 0 ≤ E) (hF0 : 0 ≤ F)
    (hE : (μ - 2 * d) * E * Q < Q - d)
    (hF : (μ - 2 * t) * F * Q < Q - t) (hFhalf : F < 1 / (2 * Q))
    (hFar : 1 ≤ t * (g * E) + d * F)
    (hjump : d * μ * g * (Q - d) ≤ (μ - d) * (μ - 2 * d) * Q) :
    d < t := by
  by_contra hcon
  push Not at hcon
  -- Step A: `μ F < 1`
  have hFQ : 2 * Q * F < 1 := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Q)).1 hFhalf
    linarith
  have hA : μ * F < 1 := by
    have h1 : μ * F * Q = (μ - 2 * t) * F * Q + t * (2 * Q * F) := by ring
    have h2 : t * (2 * Q * F) ≤ t := by
      have := mul_le_mul_of_nonneg_left hFQ.le (by linarith : (0 : ℝ) ≤ t)
      linarith
    have h3 : μ * F * Q < Q := by linarith
    by_contra h4
    push Not at h4
    have : Q ≤ μ * F * Q := by nlinarith
    linarith
  -- Step B: `μ − d < t g E μ`
  have hB : μ - d < t * (g * E) * μ := by
    have h1 : μ ≤ t * (g * E) * μ + d * F * μ := by
      have := mul_le_mul_of_nonneg_right hFar (by linarith : (0 : ℝ) ≤ μ)
      linarith
    have h2 : d * F * μ < d := by
      have := mul_lt_mul_of_pos_left hA (by linarith : (0 : ℝ) < d)
      linarith
    linarith
  -- Step C: `t ≤ d`
  have hC : μ - d < d * (g * E) * μ := by
    have : t * (g * E) * μ ≤ d * (g * E) * μ := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_right hcon (by positivity)
    linarith
  -- Step D: multiply by `Q (μ − 2d) > 0` and compare with the covering bound
  have hcoef : 0 < μ - 2 * d := by linarith
  have hD : (μ - d) * (μ - 2 * d) * Q < d * μ * g * (Q - d) := by
    have h1 : (μ - d) * ((μ - 2 * d) * Q) < d * (g * E) * μ * ((μ - 2 * d) * Q) :=
      mul_lt_mul_of_pos_right hC (by positivity)
    have h2 : d * (g * E) * μ * ((μ - 2 * d) * Q) = d * g * μ * ((μ - 2 * d) * E * Q) := by ring
    have h3 : d * g * μ * ((μ - 2 * d) * E * Q) < d * g * μ * (Q - d) :=
      mul_lt_mul_of_pos_left hE (by
        have : 0 < μ := by linarith
        positivity)
    calc (μ - d) * (μ - 2 * d) * Q = (μ - d) * ((μ - 2 * d) * Q) := by ring
      _ < d * (g * E) * μ * ((μ - 2 * d) * Q) := h1
      _ = d * g * μ * ((μ - 2 * d) * E * Q) := h2
      _ < d * g * μ * (Q - d) := h3
      _ = d * μ * g * (Q - d) := by ring
  linarith

/-- **The stage lemma.**  From a canonical shadow `σ` at time `n ≥ N₀` there
is a later time `m` whose canonical shadow `τ` has a strictly LARGER
denominator.  Needs: every orbit point from `N₀` on is bad, `g` is coprime to
every possible canonical denominator (`hcop`), and the jump condition
(`hjump`) at every possible canonical denominator. -/
theorem stage_jump (g k W M : ℕ) (hg : 2 ≤ g) (hW : W < g ^ k) (hM : 2 * g ^ k ≤ M)
    (α : ℝ) (hα : Irrational α) (N₀ : ℕ)
    (hbad : ∀ n, N₀ ≤ n → ∀ m : ℕ, 1 ≤ m → m ≤ M →
      Int.fract ((m : ℝ) * orbit g α n) ∉
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k))
    (hcop : ∀ d : ℕ, 1 ≤ d → d < g ^ k → Nat.Coprime g d)
    (hjump : ∀ d : ℕ, 1 ≤ d → d < g ^ k →
      (d : ℝ) * ((M : ℝ) + 1) * g * ((g : ℝ) ^ k - d)
        ≤ ((M : ℝ) + 1 - d) * ((M : ℝ) + 1 - 2 * d) * (g : ℝ) ^ k)
    (n : ℕ) (hn : N₀ ≤ n) (σ : ℚ) (hσ : Canonical g k (orbit g α n) σ) :
    ∃ m, n ≤ m ∧ ∃ τ : ℚ, Canonical g k (orbit g α m) τ ∧ σ.den < τ.den := by
  set x : ℕ → ℝ := orbit g α with hxdef
  set Q : ℝ := (g : ℝ) ^ k with hQdef
  have hQR : ((g ^ k : ℕ) : ℝ) = Q := by rw [hQdef]; push_cast; ring
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hg1 : (1 : ℝ) < g := by exact_mod_cast (by omega : 1 < g)
  have hQ0 : 0 < Q := by rw [hQdef]; positivity
  have hMR : 2 * Q ≤ M := by
    have := (Nat.cast_le (α := ℝ)).2 hM
    rwa [Nat.cast_mul, Nat.cast_ofNat, hQR] at this
  -- the old denominator
  set d : ℕ := σ.den with hddef
  have hd1 : 1 ≤ d := σ.pos
  have hdQ : d < g ^ k :=
    canonical_den_lt g k W M hg hW hM (x n) (orbit_irrational g hg α hα n) (hbad n hn) σ hσ
  have hcopd : Nat.Coprime g d := hcop d hd1 hdQ
  have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hdQR : (d : ℝ) < Q := by rw [← hQR]; exact_mod_cast hdQ
  -- the normalized defect
  set δ : ℝ := |x n - σ| with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; apply abs_pos.2; intro h0
    exact (orbit_irrational g hg α hα n).ne_rat σ (by linarith)
  -- the exit time: first `i` with `d gⁱ δ ≥ 1/(2Q)`
  have hex : ∃ i : ℕ, 1 / (2 * Q) ≤ (d : ℝ) * (g : ℝ) ^ i * δ := by
    obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (1 / (2 * Q) / ((d : ℝ) * δ)) hg1
    refine ⟨i, ?_⟩
    rw [div_lt_iff₀ (by positivity)] at hi
    linarith
  classical
  set i₀ := Nat.find hex with hi₀def
  have hP : 1 / (2 * Q) ≤ (d : ℝ) * (g : ℝ) ^ i₀ * δ := Nat.find_spec hex
  have hi₀ : i₀ ≠ 0 := by
    intro h0
    rw [h0] at hP
    simp only [pow_zero, mul_one] at hP
    have := hσ.2
    rw [den_mul_sub_num, abs_mul, abs_of_pos (by exact_mod_cast σ.pos : (0 : ℝ) < σ.den)] at this
    rw [← hQdef] at this
    linarith
  obtain ⟨j, hj⟩ : ∃ j, i₀ = j + 1 := ⟨i₀ - 1, by omega⟩
  have hnotP : (d : ℝ) * (g : ℝ) ^ j * δ < 1 / (2 * Q) := by
    have := Nat.find_min hex (show j < i₀ by omega)
    push Not at this; exact this
  rw [hj] at hP
  -- the shadow at `n + j`, still canonical
  obtain ⟨ρ, hρden, hρdef⟩ := shadow_chain g α n σ hcopd j
  have hρE : |(ρ.den : ℝ) * x (n + j) - ρ.num| = (d : ℝ) * (g : ℝ) ^ j * δ := by
    rw [den_mul_sub_num, abs_mul, abs_of_pos (by exact_mod_cast ρ.pos : (0 : ℝ) < ρ.den),
      hρdef, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (g : ℝ) ^ j), hρden]
    ring
  have hρcan : Canonical g k (x (n + j)) ρ := by
    refine ⟨by rw [hρden]; exact hσ.1, ?_⟩
    rw [hρE, ← hQdef]; exact hnotP
  have hcovρ := covering_canonical g k W M hg hW (x (n + j))
    (orbit_irrational g hg α hα (n + j)) (hbad (n + j) (by omega)) ρ hρcan
  rw [hρE, hρden, ← hQdef] at hcovρ
  -- the shadow at `m = n + j + 1`, no longer canonical
  set m := n + (j + 1) with hmdef
  obtain ⟨ρ', hρ'den, hρ'def⟩ := shadow_chain g α n σ hcopd (j + 1)
  have hρ'E : |(d : ℝ) * x m - ρ'.num| = (d : ℝ) * (g : ℝ) ^ (j + 1) * δ := by
    have := den_mul_sub_num ρ' (x m)
    rw [hρ'den] at this
    rw [this, abs_mul, abs_of_pos (by exact_mod_cast hd1 : (0 : ℝ) < d), hρ'def, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < (g : ℝ) ^ (j + 1))]
    ring
  -- the canonical shadow at `m`
  have hxm : Irrational (x m) := orbit_irrational g hg α hα m
  obtain ⟨τ, hτ⟩ := canonical_exists g k W M hg hW hM (x m) hxm (hbad m (by omega))
  have hcovτ := covering_canonical g k W M hg hW (x m) hxm (hbad m (by omega)) τ hτ
  rw [← hQdef] at hcovτ
  have ht1 : 1 ≤ τ.den := τ.pos
  -- `ρ' ≠ τ`, since `ρ'` has defect `≥ 1/(2Q)` and `τ` has defect `< 1/(2Q)`
  have hne : ρ'.num * (τ.den : ℤ) ≠ τ.num * (d : ℤ) := by
    intro heq
    have hEq : ρ' = τ := by
      rw [Rat.eq_iff_mul_eq_mul, hρ'den]; exact heq
    have h1 := hτ.2
    rw [← hEq, hρ'den, hρ'E, ← hQdef] at h1
    linarith
  have hFar := defect_pair_ge (x m) ρ'.num τ.num d τ.den hd1 ht1 hne
  rw [hρ'E] at hFar
  refine ⟨m, by omega, τ, hτ, ?_⟩
  -- assemble the real inequality
  have hE0 : 0 ≤ (d : ℝ) * (g : ℝ) ^ j * δ := by positivity
  have hpow : (d : ℝ) * (g : ℝ) ^ (j + 1) * δ = (g : ℝ) * ((d : ℝ) * (g : ℝ) ^ j * δ) := by ring
  rw [hpow] at hFar
  have hτhalf := hτ.2
  rw [← hQdef] at hτhalf
  have hjd := hjump d hd1 hdQ
  have hμ : 2 * Q + 1 ≤ (M : ℝ) + 1 := by linarith
  have key := stage_arith ((M : ℝ) + 1) Q g d τ.den ((d : ℝ) * (g : ℝ) ^ j * δ)
    |(τ.den : ℝ) * x m - τ.num| hQ0 hg0 hd1R hdQR (by exact_mod_cast ht1) hμ hE0
    (abs_nonneg _) hcovρ hcovτ hτhalf hFar hjd
  exact_mod_cast key

/-! ### Iteration and the contradiction -/

/-- **Denominators grow without bound.**  `j` stages raise the canonical
denominator by at least `j`. -/
theorem den_grows (g k W M : ℕ) (hg : 2 ≤ g) (hW : W < g ^ k) (hM : 2 * g ^ k ≤ M)
    (α : ℝ) (hα : Irrational α) (N₀ : ℕ)
    (hbad : ∀ n, N₀ ≤ n → ∀ m : ℕ, 1 ≤ m → m ≤ M →
      Int.fract ((m : ℝ) * orbit g α n) ∉
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k))
    (hcop : ∀ d : ℕ, 1 ≤ d → d < g ^ k → Nat.Coprime g d)
    (hjump : ∀ d : ℕ, 1 ≤ d → d < g ^ k →
      (d : ℝ) * ((M : ℝ) + 1) * g * ((g : ℝ) ^ k - d)
        ≤ ((M : ℝ) + 1 - d) * ((M : ℝ) + 1 - 2 * d) * (g : ℝ) ^ k)
    (j : ℕ) :
    ∀ n, N₀ ≤ n → ∀ σ : ℚ, Canonical g k (orbit g α n) σ →
      ∃ m, n ≤ m ∧ ∃ τ : ℚ, Canonical g k (orbit g α m) τ ∧ σ.den + j ≤ τ.den := by
  induction j with
  | zero => intro n hn σ hσ; exact ⟨n, le_rfl, σ, hσ, by omega⟩
  | succ j ih =>
      intro n hn σ hσ
      obtain ⟨m, hnm, τ, hτ, hlt⟩ :=
        stage_jump g k W M hg hW hM α hα N₀ hbad hcop hjump n hn σ hσ
      obtain ⟨m', hmm', τ', hτ', hle⟩ := ih m (le_trans hn hnm) τ hτ
      exact ⟨m', le_trans hnm hmm', τ', hτ', by omega⟩

/-- **No orbit is bad forever.**  Under the coprimality and jump hypotheses,
the orbit of an irrational cannot be bad from some time on: after `gᵏ` stages
the canonical denominator would exceed `gᵏ`. -/
theorem no_bad_orbit (g k W M : ℕ) (hg : 2 ≤ g) (hW : W < g ^ k) (hM : 2 * g ^ k ≤ M)
    (α : ℝ) (hα : Irrational α) (N₀ : ℕ)
    (hbad : ∀ n, N₀ ≤ n → ∀ m : ℕ, 1 ≤ m → m ≤ M →
      Int.fract ((m : ℝ) * orbit g α n) ∉
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k))
    (hcop : ∀ d : ℕ, 1 ≤ d → d < g ^ k → Nat.Coprime g d)
    (hjump : ∀ d : ℕ, 1 ≤ d → d < g ^ k →
      (d : ℝ) * ((M : ℝ) + 1) * g * ((g : ℝ) ^ k - d)
        ≤ ((M : ℝ) + 1 - d) * ((M : ℝ) + 1 - 2 * d) * (g : ℝ) ^ k) : False := by
  obtain ⟨σ, hσ⟩ := canonical_exists g k W M hg hW hM (orbit g α N₀)
    (orbit_irrational g hg α hα N₀) (hbad N₀ le_rfl)
  obtain ⟨m, _, τ, hτ, hle⟩ :=
    den_grows g k W M hg hW hM α hα N₀ hbad hcop hjump (g ^ k) N₀ le_rfl σ hσ
  have h1 := σ.pos
  have h2 := hτ.1
  omega

/-- **The multi-scale multiplier theorem, parameterized.**  If `M ≥ 2gᵏ`, `g`
is coprime to every `d < gᵏ`, and the jump condition holds at every `d < gᵏ`,
then some multiplier `m ≤ M` makes every `k`-block occur infinitely often. -/
theorem mahler_multiplier_quarter_param (g : ℕ) (hg : 2 ≤ g) (M : ℕ)
    (α : ℝ) (hα : Irrational α) (w : List ℕ) (hwd : ∀ d ∈ w, d < g)
    (hM : 2 * g ^ w.length ≤ M)
    (hcop : ∀ d : ℕ, 1 ≤ d → d < g ^ w.length → Nat.Coprime g d)
    (hjump : ∀ d : ℕ, 1 ≤ d → d < g ^ w.length →
      (d : ℝ) * ((M : ℝ) + 1) * g * ((g : ℝ) ^ w.length - d)
        ≤ ((M : ℝ) + 1 - d) * ((M : ℝ) + 1 - 2 * d) * (g : ℝ) ^ w.length) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ M ∧ ∀ N, ∃ n, N ≤ n ∧ OccursAt g ((m : ℝ) * α) w n := by
  set k := w.length with hkdef
  set W := blockNatVal g w with hWdef
  have hW : W < g ^ k := blockNatVal_lt g w hwd
  by_contra hcon
  push Not at hcon
  choose! Nf hNf using hcon
  set N₀ := (Finset.range (M + 1)).sup Nf with hN₀def
  have hN₀ : ∀ m, m ≤ M → Nf m ≤ N₀ := fun m hm =>
    Finset.le_sup (f := Nf) (Finset.mem_range.2 (by omega))
  have hbad : ∀ n, N₀ ≤ n → ∀ m : ℕ, 1 ≤ m → m ≤ M →
      Int.fract ((m : ℝ) * orbit g α n) ∉
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k) := by
    intro n hn m hm1 hmM hmem
    apply hNf m hm1 hmM n (le_trans (hN₀ m hmM) hn)
    rw [occursAt_iff_orbit_mem g hg _ w hwd n, orbit_nat_mul]
    exact hmem
  exact no_bad_orbit g k W M hg hW hM α hα N₀ hbad hcop hjump

/-! ### The instance `k = 1`: `M(g,1) ≤ (g² + 6g + 1)/4` -/

/-- **The jump condition at `k = 1`, `μ = (g+1)(g+5)/4`, for every real `d`.**
`(μ − d)(μ − 2d) − dμ(g − d) = (μ+2)d² − μ(g+3)d + μ²`, and
`4(μ+2)·(that) = (2(μ+2)d − μ(g+3))² + 4μ²` — the discriminant is `−4μ²`. -/
theorem jump_condition_k1 (g d : ℝ) (hg : 0 ≤ g) :
    d * ((g + 1) * (g + 5) / 4) * (g - d)
      ≤ ((g + 1) * (g + 5) / 4 - d) * ((g + 1) * (g + 5) / 4 - 2 * d) := by
  set μ : ℝ := (g + 1) * (g + 5) / 4 with hμdef
  have hμpos : 0 < μ + 2 := by rw [hμdef]; positivity
  have hid : 4 * (μ + 2) * ((μ - d) * (μ - 2 * d) - d * μ * (g - d))
      = (2 * (μ + 2) * d - μ * (g + 3)) ^ 2 + 4 * μ ^ 2 := by
    rw [hμdef]; ring
  have h0 : 0 ≤ 4 * (μ + 2) * ((μ - d) * (μ - 2 * d) - d * μ * (g - d)) := by
    rw [hid]; positivity
  have h1 : 0 ≤ (μ - d) * (μ - 2 * d) - d * μ * (g - d) :=
    nonneg_of_mul_nonneg_right (by linarith [h0]) (by linarith : (0 : ℝ) < 4 * (μ + 2))
  linarith

/-- **`M(g,1) ≤ (g² + 6g + 1)/4` for every odd prime `g`.**  The constant
`1/4` of the exact census (`M(p,1) ≈ ⌊p/2⌋²`), reached from above; for `g ≥ 5`
this beats `mahler_multiplier_prime_half`'s `g(g+1)/2`. -/
theorem mahler_multiplier_quarter (g : ℕ) (hgp : g.Prime) (hodd : g % 2 = 1)
    (α : ℝ) (hα : Irrational α) (w : List ℕ) (hwd : ∀ d ∈ w, d < g) (hk : w.length = 1) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ (g ^ 2 + 6 * g + 1) / 4 ∧
      ∀ N, ∃ n, N ≤ n ∧ OccursAt g ((m : ℝ) * α) w n := by
  have hg : 2 ≤ g := hgp.two_le
  obtain ⟨j, hj⟩ : ∃ j, g = 2 * j + 1 := ⟨g / 2, by omega⟩
  set M := (g ^ 2 + 6 * g + 1) / 4 with hMdef
  have hM4 : 4 * M = g ^ 2 + 6 * g + 1 := by
    have : g ^ 2 + 6 * g + 1 = 4 * (j ^ 2 + 4 * j + 2) := by rw [hj]; ring
    rw [hMdef, this, Nat.mul_div_cancel_left _ (by norm_num)]
  have hMR : (M : ℝ) + 1 = ((g : ℝ) + 1) * ((g : ℝ) + 5) / 4 := by
    have h := (Nat.cast_inj (R := ℝ)).2 hM4
    push_cast at h
    linarith
  refine mahler_multiplier_quarter_param g hg M α hα w hwd ?_ ?_ ?_
  · rw [hk, pow_one]; nlinarith [hM4]
  · intro d hd1 hdlt
    rw [hk, pow_one] at hdlt
    exact (Nat.Prime.coprime_iff_not_dvd hgp).2 (Nat.not_dvd_of_pos_of_lt (by omega) hdlt)
  · intro d _ _
    rw [hk, pow_one, hMR]
    have hg0 : (0 : ℝ) ≤ g := by positivity
    have h := jump_condition_k1 (g : ℝ) (d : ℝ) hg0
    have := mul_le_mul_of_nonneg_right h hg0
    calc (d : ℝ) * (((g : ℝ) + 1) * ((g : ℝ) + 5) / 4) * g * ((g : ℝ) - d)
        = d * (((g : ℝ) + 1) * ((g : ℝ) + 5) / 4) * ((g : ℝ) - d) * g := by ring
      _ ≤ _ := this

/-- **`mahler_multiplier_prime_half` retired to a corollary** (for `g ≥ 5`):
`(g² + 6g + 1)/4 ≤ g(g+1)/2` once `g² ≥ 4g + 1`.  (At `g = 3` the quarter bound
`7` exceeds `g(g+1)/2 = 6`; that base is covered by the original proof — and by
the exact value `M(3,1) = 2`.) -/
theorem mahler_multiplier_prime_half_of_quarter (g : ℕ) (hgp : g.Prime) (hodd : g % 2 = 1)
    (hg5 : 5 ≤ g)
    (α : ℝ) (hα : Irrational α) (w : List ℕ) (hwd : ∀ d ∈ w, d < g) (hk : w.length = 1) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ g * (g + 1) / 2 ∧
      ∀ N, ∃ n, N ≤ n ∧ OccursAt g ((m : ℝ) * α) w n := by
  obtain ⟨m, hm1, hm2, hm3⟩ := mahler_multiplier_quarter g hgp hodd α hα w hwd hk
  refine ⟨m, hm1, le_trans hm2 ?_, hm3⟩
  have h2 : 2 * (g * (g + 1) / 2) = g * (g + 1) := by
    have : 2 ∣ g * (g + 1) := by
      rcases Nat.even_or_odd g with he | ho
      · exact Dvd.dvd.mul_right he.two_dvd _
      · exact Dvd.dvd.mul_left (by omega : 2 ∣ g + 1) _
    omega
  apply Nat.div_le_of_le_mul
  have : 4 * (g * (g + 1) / 2) = 2 * (g * (g + 1)) := by omega
  rw [this]
  nlinarith

end NormalNumbers.Mahler
