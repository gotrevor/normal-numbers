/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4ScheduleBig

/-!
# Entropy expedition, objective A0: **the outer scale `X` is capped at fixed `K`**

The A0 probe asks whether the `E0` chain (`G4EntropyBudget.entropy_E0`) survives raising the
outer scale `X` at a *fixed* `K`.  The audit of `entropy_gt_of_budget`'s cone shows `X` enters
the frame in exactly one place — the field `P := apSample X G.P₀ G.b₀` of `gridFrame` — and so
reaches the schedule inequalities through exactly four terms:

| where | term | monotone in `X`? |
|---|---|---|
| `hne`/`hX` | `b₀ < X` | ✅ |
| `PropC` (`δ₃ = smallPrimeBound … Psz`) | `2R^{Mc}/Psz`, `2(2e/Mc)^{Mc}(#sm)^{Mc}·2R^{Mc}/Psz` | ✅ (`Psz = |P| ≥ X/2P₀` grows) |
| `hbig` | `2Y²·rowL2²/|P|` | ✅ |
| `hbig` | **`(log Mx / log Y)·rowL1`** | ❌ — `hMx` forces `Mx ≥ X − P₀` |
| `hfar` | `farC G X Dm = log((X+Dm)/|P|) + log(log(X+Dm)+1)` | ❌ but with `4^{−(K+N)}` slack |

This module proves the ❌ in row 4 outright: **every** `ScheduleWitness` obeys

    `Mx ≤ Y ^ (3·2^K·δbig·ε·η)`   (`ScheduleWitness.Mx_le_rpow`)

and hence `X ≤ Y ^ (3·2^K·δbig·ε·η) + P₀` (`ScheduleWitness.X_le_rpow`).  The cap is a *theorem
about the witness interface*, not about the particular numerals of the base-four schedule: the
`log Mx / log Y` summand of `hbig` is the count of prime factors of a sample point exceeding the
medium cutoff `Y`, and a larger sample simply has more of them.

At the implemented parameters (`δbig = 1/8`, `ε = 1/K`, `η = 2^{−k₄}`, `K = 4k₄`) the exponent is
`(3/(8K))·2^{3k₄}`, so `X ≲ Y^{2^{3K/4}}`, i.e. `log₂ X ≲ 2^{m(K) + 3K/4}`; the *next* rung of the
ladder needs `log₂ X = 100·2^{m(K+4)}` with `m(K+4) ≫ m(K) + 3K/4`.  So A0's verdict is **NO**,
and the gap is not closable by also raising `Y`: raising `Y` at fixed `K` is itself capped by
`hbig`'s dyadic term `√(4(1 + log log₂ Y − log log₂ R)·rowL2²)`, which allows only
`m − m₁ ≲ 2^{5K/2}`, whereas `m₁(K+4) − m₁(K) ≥ 4095·m₁(K)`.
-/

open Finset Real
open scoped BigOperators Nat

namespace NormalNumbers.G4

namespace ScheduleWitness

variable {ℓ w : ℕ}

/-- The exponent of the `X`-ceiling: `3·2^K·δbig·ε·η`. -/
noncomputable def bigExp (W : ScheduleWitness ℓ w) : ℝ :=
  3 * 2 ^ W.G.K * (W.δbig * (W.ε * W.η))

/-- **The `hbig` field caps `log Mx / log Y`.** -/
theorem log_Mx_div_log_Y_le (W : ScheduleWitness ℓ w) :
    Real.log W.Mx / Real.log W.Y ≤ W.bigExp := by
  have hb := W.hbig
  have hsq : 0 ≤ Real.sqrt (4 * (1 + Real.log (Nat.log 2 W.Y) - Real.log (Nat.log 2 W.R))
          * ((1 / 8 : ℝ) ^ W.G.K / 15)
        + 2 * (W.Y : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ W.G.K / 3) ^ 2
            / (apSample W.X W.G.P₀ W.G.b₀).card) := Real.sqrt_nonneg _
  have hkey : (Real.log W.Mx / Real.log W.Y) * (1 / 2 : ℝ) ^ W.G.K / 3
      ≤ W.δbig * (W.ε * W.η) := by linarith
  have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ W.G.K := by positivity
  rw [bigExp]
  have h3 : (Real.log W.Mx / Real.log W.Y) * (1 / 2 : ℝ) ^ W.G.K
      ≤ 3 * (W.δbig * (W.ε * W.η)) := by linarith
  have hmul : (Real.log W.Mx / Real.log W.Y)
      ≤ 3 * (W.δbig * (W.ε * W.η)) / (1 / 2 : ℝ) ^ W.G.K := by
    rw [le_div_iff₀ hpow]; exact h3
  refine hmul.trans (le_of_eq ?_)
  rw [div_pow, one_pow]
  field_simp

/-- **The ceiling on `Mx`**: `Mx ≤ Y ^ bigExp`. -/
theorem Mx_le_rpow (W : ScheduleWitness ℓ w) (hY : 1 < W.Y) :
    W.Mx ≤ (W.Y : ℝ) ^ W.bigExp := by
  have hY1 : (1 : ℝ) < (W.Y : ℝ) := by exact_mod_cast hY
  have hlogY : 0 < Real.log W.Y := Real.log_pos hY1
  have h := W.log_Mx_div_log_Y_le
  rw [div_le_iff₀ hlogY] at h
  have hMx0 : (0 : ℝ) < W.Mx := lt_of_lt_of_le zero_lt_one W.hMx1
  rw [← Real.log_le_log_iff hMx0 (by positivity), Real.log_rpow (by linarith)]
  exact h

/-- The largest element of a nonempty `apSample` is within `P₀` of `X`. -/
lemma exists_mem_apSample_ge {X P₀ a : ℕ} (hP₀ : 0 < P₀) (ha : a < P₀) (haX : a < X) :
    ∃ n ∈ apSample X P₀ a, X ≤ n + P₀ := by
  obtain ⟨q, r, hr, hqr⟩ : ∃ q r, r < P₀ ∧ X - 1 - a = P₀ * q + r :=
    ⟨(X - 1 - a) / P₀, (X - 1 - a) % P₀, Nat.mod_lt _ hP₀,
      (Nat.div_add_mod (X - 1 - a) P₀).symm⟩
  refine ⟨a + P₀ * q, ?_, ?_⟩
  · unfold apSample
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  · omega

/-- **The ceiling on `X`**: every witness has `X ≤ Y ^ bigExp + P₀`. -/
theorem X_le_rpow (W : ScheduleWitness ℓ w) (hY : 1 < W.Y) (i : W.G.Idx) :
    (W.X : ℝ) ≤ (W.Y : ℝ) ^ W.bigExp + W.G.P₀ := by
  have hb₀ : W.G.b₀ < W.G.P₀ := W.G.b₀_lt_P₀
  have hP₀ : 0 < W.G.P₀ := by omega
  have hb₀X : W.G.b₀ < W.X := by
    obtain ⟨n, hn⟩ := W.hne
    unfold apSample at hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    have : n % W.G.P₀ = W.G.b₀ := hn.2
    have : W.G.b₀ ≤ n := this ▸ Nat.mod_le _ _
    omega
  obtain ⟨n, hn, hnX⟩ := exists_mem_apSample_ge hP₀ hb₀ hb₀X
  have hle : ((n : ℝ)) ≤ W.Mx := by
    have := W.hMx n hn i
    have hcast : ((n : ℝ)) ≤ ((n + shiftAL W.G.B W.G.Q W.G.D₀ i : ℕ) : ℝ) := by
      push_cast; linarith [Nat.cast_nonneg (α := ℝ) (shiftAL W.G.B W.G.Q W.G.D₀ i)]
    linarith
  have hX : ((W.X : ℝ)) ≤ (n : ℝ) + W.G.P₀ := by exact_mod_cast hnX
  have := W.Mx_le_rpow hY
  linarith
end ScheduleWitness

/-! ### The ceiling at the implemented parameters, against the next rung of the ladder -/

namespace Sched

/-- `m₁` jumps by a factor `≥ 4096` in one rung. -/
lemma m₁_step (K : ℕ) : 4096 * m₁ K ≤ m₁ (K + 4) := by
  unfold m₁
  have h8 : (8 : ℕ) ^ (K + 4) = 4096 * 8 ^ K := by ring
  have hp : K ^ (2 * K + 1) ≤ (K + 4) ^ (2 * (K + 4) + 1) :=
    le_trans (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_right (by omega) (by omega))
  calc 4096 * (1000 * 8 ^ K * K ^ (2 * K + 1))
      = 1000 * (4096 * 8 ^ K) * K ^ (2 * K + 1) := by ring
    _ ≤ 1000 * (4096 * 8 ^ K) * (K + 4) ^ (2 * (K + 4) + 1) := by
        exact Nat.mul_le_mul_left _ hp
    _ = 1000 * 8 ^ (K + 4) * (K + 4) ^ (2 * (K + 4) + 1) := by rw [h8]

/-- The headroom `3k₄` that `hbig` allows at scale `K` does not reach the next rung. -/
lemma m_add_lt {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K) : m K + 3 * k₄ < m (K + 4) := by
  have h1 := m₁_step K
  have h2 : m₂ K ≤ m₂ (K + 4) := by
    unfold m₂; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hK1 : K ≤ m₁ K := by
    unfold m₁
    calc K ≤ 1000 * K := by omega
      _ ≤ 1000 * 8 ^ K * K ^ (2 * K + 1) := by
          have hb : 1 ≤ 8 ^ K := Nat.one_le_pow _ _ (by norm_num)
          have hc : K ≤ K ^ (2 * K + 1) := Nat.le_self_pow (by omega) K
          calc 1000 * K ≤ 1000 * K ^ (2 * K + 1) := Nat.mul_le_mul_left _ hc
            _ ≤ 1000 * 8 ^ K * K ^ (2 * K + 1) := by
                exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by positivity))
  unfold m
  omega

/-- **The arithmetic core of the A0 obstruction**, in ℕ: the largest outer scale `hbig` permits
at scale `K` — `2^{2^{m K + 3k₄}}`, together with the whole of `X K` — is still strictly below
`X (K+4)`. -/
lemma pow_add_X_lt_X_step {K k₄ : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K) :
    2 ^ 2 ^ (m K + 3 * k₄) + X K < X (K + 4) := by
  have hk : 25 ≤ k₄ := by omega
  have hmlt := m_add_lt hK4 hK
  set a := m K + 3 * k₄ with ha
  set b := m (K + 4) with hb
  -- `100·2^{m K} ≤ 2^a`
  have h100 : 100 * 2 ^ m K ≤ 2 ^ a := by
    have : (100 : ℕ) ≤ 2 ^ (3 * k₄) := by
      calc (100 : ℕ) ≤ 2 ^ 7 := by norm_num
        _ ≤ 2 ^ (3 * k₄) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 100 * 2 ^ m K ≤ 2 ^ (3 * k₄) * 2 ^ m K := Nat.mul_le_mul_right _ this
      _ = 2 ^ a := by rw [ha, pow_add]; ring
  have hXK : X K ≤ 2 ^ 2 ^ a := by
    unfold X
    exact Nat.pow_le_pow_right (by norm_num) h100
  have hsum : 2 ^ 2 ^ a + X K ≤ 2 ^ (2 ^ a + 1) := by
    have : 2 ^ (2 ^ a + 1) = 2 ^ 2 ^ a + 2 ^ 2 ^ a := by rw [pow_succ]; ring
    omega
  have hab : 2 ^ a + 1 ≤ 2 ^ b := by
    have h1 : 2 ^ (a + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (a + 1) = 2 ^ a + 2 ^ a := by rw [pow_succ]; ring
    have h3 : 1 ≤ 2 ^ a := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hlt : 2 ^ b < 100 * 2 ^ b := by
    have h0 : 0 < 2 ^ b := Nat.two_pow_pos b
    nlinarith
  have hfin : 2 ^ (2 ^ a + 1) < X (K + 4) := by
    unfold X
    rw [← hb]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

end Sched

/-- **A0's verdict, as a theorem.**  Any schedule witness whose medium cutoff is the schedule's
`Y K` and whose allowances are at most the implemented `δbig = 1/8`, `ε = 1/K`, `η = 2^{−k₄}`
has outer scale **strictly below the next rung `X (K+4)`** of the ladder.

So `entropy_E0` does **not** generalize to `∀ X ≥ X K`: the `hbig` field of `ScheduleWitness`
(its `(log Mx / log Y)·rowL1 4 K` summand, fed by `hMx`) caps `X` at `Y^{(3/8K)·2^{3k₄}}`, and
that cap is below the scale at which the *next* band of the concatenated read begins.  This is
the named obstruction that stops objective A. -/
theorem ScheduleWitness.X_lt_X_step {ℓ w K k₄ : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K)
    (W : ScheduleWitness ℓ w) (hWK : W.G.K = K) (hWY : W.Y = Sched.Y K)
    (hδ0 : 0 ≤ W.δbig) (hδ : W.δbig ≤ 1 / 8) (hε : W.ε ≤ 1 / (K : ℝ))
    (hη : W.η ≤ (1 / 2 : ℝ) ^ k₄) (hP₀ : 2 * W.G.P₀ ≤ Sched.X K) (i : W.G.Idx) :
    W.X < Sched.X (K + 4) := by
  have hk : 25 ≤ k₄ := by omega
  have hKr : (100 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  -- `bigExp ≤ 2^{3k₄}`
  have hA : (0 : ℝ) < (2 : ℝ) ^ (3 * k₄) := by positivity
  have hB : (0 : ℝ) < (2 : ℝ) ^ k₄ := by positivity
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
  have hbe : W.bigExp ≤ (2 : ℝ) ^ (3 * k₄) := by
    have hεη : W.ε * W.η ≤ (1 / (K : ℝ)) * (1 / 2 : ℝ) ^ k₄ :=
      mul_le_mul hε hη W.hη.le (by positivity)
    have hεη0 : (0 : ℝ) ≤ W.ε * W.η := mul_nonneg W.hε.le W.hη.le
    have hprod : W.δbig * (W.ε * W.η) ≤ (1 / 8 : ℝ) * ((1 / (K : ℝ)) * (1 / 2 : ℝ) ^ k₄) :=
      mul_le_mul hδ hεη hεη0 (by norm_num)
    have he : (2 : ℝ) ^ K = (2 : ℝ) ^ (3 * k₄) * (2 : ℝ) ^ k₄ := by
      rw [← pow_add]; congr 1; omega
    have h2 : ((1 : ℝ) / 2) ^ k₄ = 1 / (2 : ℝ) ^ k₄ := by rw [div_pow, one_pow]
    have h38 : (3 : ℝ) / (8 * (K : ℝ)) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    rw [ScheduleWitness.bigExp, hWK]
    calc 3 * (2 : ℝ) ^ K * (W.δbig * (W.ε * W.η))
        ≤ 3 * (2 : ℝ) ^ K * ((1 / 8 : ℝ) * ((1 / (K : ℝ)) * (1 / 2 : ℝ) ^ k₄)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = 3 / (8 * (K : ℝ)) * (2 : ℝ) ^ (3 * k₄) := by
          rw [he, h2]; field_simp
      _ ≤ 1 * (2 : ℝ) ^ (3 * k₄) := mul_le_mul_of_nonneg_right h38 hA.le
      _ = (2 : ℝ) ^ (3 * k₄) := one_mul _
  -- the ceiling, transported to the ladder
  have hY2 : Sched.Y K = 2 ^ 2 ^ Sched.m K := rfl
  have hYgt : 1 < W.Y := by
    rw [hWY, hY2]
    exact Nat.one_lt_two_pow (by positivity)
  have hXle := W.X_le_rpow hYgt i
  have hYcast : ((W.Y : ℕ) : ℝ) = (2 : ℝ) ^ ((2 ^ Sched.m K : ℕ) : ℝ) := by
    rw [hWY, hY2, Real.rpow_natCast]
    push_cast
    ring
  have hmul : ((2 ^ Sched.m K : ℕ) : ℝ) * W.bigExp ≤ ((2 ^ (Sched.m K + 3 * k₄) : ℕ) : ℝ) := by
    have hp : (0 : ℝ) < ((2 ^ Sched.m K : ℕ) : ℝ) := by positivity
    calc ((2 ^ Sched.m K : ℕ) : ℝ) * W.bigExp
        ≤ ((2 ^ Sched.m K : ℕ) : ℝ) * (2 : ℝ) ^ (3 * k₄) :=
          mul_le_mul_of_nonneg_left hbe hp.le
      _ = ((2 ^ (Sched.m K + 3 * k₄) : ℕ) : ℝ) := by push_cast [pow_add]; ring
  have hrpow : (W.Y : ℝ) ^ W.bigExp ≤ ((2 ^ 2 ^ (Sched.m K + 3 * k₄) : ℕ) : ℝ) := by
    rw [hYcast, ← Real.rpow_mul (by norm_num)]
    have : ((2 ^ 2 ^ (Sched.m K + 3 * k₄) : ℕ) : ℝ)
        = (2 : ℝ) ^ ((2 ^ (Sched.m K + 3 * k₄) : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]; push_cast; ring
    rw [this]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hmul
  have hP₀r : ((W.G.P₀ : ℕ) : ℝ) ≤ ((Sched.X K : ℕ) : ℝ) := by
    have : W.G.P₀ ≤ Sched.X K := by omega
    exact_mod_cast this
  have hfinal : ((W.X : ℕ) : ℝ) ≤ ((2 ^ 2 ^ (Sched.m K + 3 * k₄) + Sched.X K : ℕ) : ℝ) := by
    push_cast
    push_cast at hXle hrpow hP₀r
    linarith
  have hnat : W.X ≤ 2 ^ 2 ^ (Sched.m K + 3 * k₄) + Sched.X K := by exact_mod_cast hfinal
  exact lt_of_le_of_lt hnat (Sched.pow_add_X_lt_X_step hK4 hK)

end NormalNumbers.G4
