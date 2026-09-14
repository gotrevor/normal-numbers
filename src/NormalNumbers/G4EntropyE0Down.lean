/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyBudget

/-!
# **E0 downward**: the entropy bound survives *shrinking* the outer scale

`G4EntropyXCeiling` settled objective A0: the E0 chain does **not** survive raising `X` past
`Y^{3·2^K δbig ε η}` at fixed `K`, because `hbig`'s `log Mx / log Y` summand counts prime
factors above the medium cutoff.  That closed the design which wanted `X` *larger*.

The design that prefix control actually needs wants `X` **smaller**, and there the four
`X`-sensitive terms line up the other way:

| term | as `X` shrinks |
|---|---|
| `hbig`, `(log Mx / log Y)` | **improves** (`Mx ≤ 2X' ≤ 2X K`) |
| `hfar`, `farC G X' Dm` | **improves** (`log((X'+Dm)/|P'|) ≈ log 2P₀`, `log log(X'+Dm)` shrinks) |
| `hbig`, `2Y²·rowL2²/|P'|` | degrades — needs `|P'| ≳ Y²8^K` |
| `smallPrimeBound` terms (a),(d), `2R^{Mc}/Psz` | degrades — needs `Psz ≳ Λ·R^{Mc}` |

Both degrading terms are *powers of `Y`*, and `X K = Y^{100}`, so there is a wide window:
everything still holds down to `Xlo K := Y K ^ 50 = √(X K)`.

**Why this is the on-path direction.**  A window start of band `i` sits at `2·kIdx(n,α)`, which
is increasing in `n` at fixed `α`.  So a *position cutoff* `c` inside band `i` selects, atom by
atom, the sub-sample `n ≲ d_α·c/2` — a **truncation of `X`**, not an extension.  Prefix control
for `fullPos` therefore asks for E0 at all `X' ≤ X K`, which is what this module supplies down to
`√(X K)`; below that, the read has produced fewer digits than `fT i`, where the trivial bound
`fT_kk_le` already suffices.  The two regimes overlap by a factor `≫ 1` because
`X/(dmin·kk) ≫ √X`.

Two leaves remain open (`sorry`), each the `X'`-version of an existing `X K` lemma whose proof
goes through `card_apSample_ge_half`:

* `hbig_holds_down`   — `G4ScheduleBig.hbig_holds` at `X'`
* `smallPrime_term_le_down` — `G4EntropyBudget.smallPrime_term_le` at `X'`

**Done**: `hfar_holds_down`, via `farC_le_down` (`farC G X' Dm ≤ logP₀Nat K + m K + 10` for
every `Xlo K ≤ X' ≤ X K`) together with `two_mul_exp_le_Xlo` and `gridDm_le_Xlo`.

The assembly `entropy_E0_down` is complete and consumes exactly those three.
-/

open Finset Real MeasureTheory
open scoped BigOperators Nat

namespace NormalNumbers.G4

namespace Sched

open NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-- The downward threshold `Xlo K = Y K ^ 50 = √(X K)`. -/
def Xlo (K : ℕ) : ℕ := Y K ^ 50

lemma Xlo_pos (K : ℕ) : 0 < Xlo K := by
  unfold Xlo Y; positivity

lemma Xlo_le_X (K : ℕ) : Xlo K ≤ X K := by
  unfold Xlo X Y
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `2P₀ ≤ Xlo K`: the same computation as `two_mul_P₀_le_X`, with `50` in place of `100`. -/
lemma two_mul_P₀_le_Xlo {K : ℕ} (hK : 100 ≤ K) :
    2 * (gridOf K (N K) (by omega)).P₀ ≤ Xlo K := by
  have h1 := P₀_le_exp (K := K) (by omega)
  have h2 : 2 * Real.exp (logP₀Nat K) ≤ (Xlo K : ℝ) := by
    have he := exp_nat_le_two_pow (logP₀Nat K)
    have hm : 2 * logP₀Nat K + 1 ≤ 50 * 2 ^ m K := by
      have := logP₀Nat_le_two_pow_m hK
      have : 1 ≤ 2 ^ m K := Nat.one_le_two_pow
      omega
    have h3 : (2 : ℝ) ^ (2 * logP₀Nat K + 1) ≤ (2 : ℝ) ^ (50 * 2 ^ m K) :=
      pow_le_pow_right₀ (by norm_num) hm
    have hXlo : ((Xlo K : ℕ) : ℝ) = (2 : ℝ) ^ (50 * 2 ^ m K) := by
      unfold Xlo Y
      push_cast
      rw [← pow_mul]
      ring_nf
    rw [hXlo]
    calc 2 * Real.exp (logP₀Nat K) ≤ 2 * (2 : ℝ) ^ (2 * logP₀Nat K) := by linarith
      _ = (2 : ℝ) ^ (2 * logP₀Nat K + 1) := by ring
      _ ≤ _ := h3
  exact_mod_cast (by linarith : (2 * (gridOf K (N K) (by omega)).P₀ : ℝ) ≤ (Xlo K : ℝ))

lemma b₀_lt_of_Xlo_le {K X' : ℕ} (hK : 100 ≤ K) (h : Xlo K ≤ X') :
    (gridOf K (N K) (by omega)).b₀ < X' := by
  have h1 := (gridOf K (N K) (by omega : 1 ≤ K)).b₀_lt_P₀
  have h2 := two_mul_P₀_le_Xlo hK
  omega

/-! ### The three open leaves

Each is the `X'`-version of an `X K` lemma.  The `X K` proof bounds
`|apSample (X K) P₀ b₀| ≥ X K/(2P₀) = Y^{100}/(2P₀)` and compares against a fixed power of `Y`;
the `X'` version has `≥ Y^{50}/(2P₀)` instead, and every comparison in those proofs has slack
far exceeding a factor `Y^{50}`.  `Mx' = X' + J·Dm ≤ X K + J·Dm`, so the `log Mx/log Y` summand
and `farC`'s `log log` term only improve. -/

/-- **Leaf 1** — `G4ScheduleBig.hbig_holds`, at any `X'` with `Xlo K ≤ X' ≤ X K`. -/
theorem hbig_holds_down {K k₄ X' : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K)
    (hlo : Xlo K ≤ X') (hhi : X' ≤ X K) :
    Real.sqrt (4 * (1 + Real.log (Nat.log 2 (Y K)) - Real.log (Nat.log 2 (R K)))
          * ((1 / 8 : ℝ) ^ K / 15)
        + 2 * (Y K : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ K / 3) ^ 2
          / ((apSample X' (gridOf K (N K) (by omega)).P₀
              (gridOf K (N K) (by omega)).b₀).card : ℝ))
      + (Real.log ((X' + J K * gridDm K (N K) : ℕ) : ℝ) / Real.log (Y K)) * (1 / 2 : ℝ) ^ K / 3
      ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  sorry

/-- `2·exp(logP₀Nat K) ≤ Xlo K`. -/
lemma two_mul_exp_le_Xlo {K : ℕ} (hK : 100 ≤ K) :
    2 * Real.exp (logP₀Nat K) ≤ (Xlo K : ℝ) := by
  have h1 := exp_nat_le_two_pow (logP₀Nat K)
  have hm : 2 * logP₀Nat K + 1 ≤ 50 * 2 ^ m K := by
    have := logP₀Nat_le_two_pow_m hK
    have : 1 ≤ 2 ^ m K := Nat.one_le_two_pow
    omega
  have h3 : (2 : ℝ) ^ (2 * logP₀Nat K + 1) ≤ (2 : ℝ) ^ (50 * 2 ^ m K) :=
    pow_le_pow_right₀ (by norm_num) hm
  have hXlo : ((Xlo K : ℕ) : ℝ) = (2 : ℝ) ^ (50 * 2 ^ m K) := by
    unfold Xlo Y; push_cast; rw [← pow_mul]; ring_nf
  rw [hXlo]
  calc 2 * Real.exp (logP₀Nat K) ≤ 2 * (2 : ℝ) ^ (2 * logP₀Nat K) := by linarith
    _ = (2 : ℝ) ^ (2 * logP₀Nat K + 1) := by ring
    _ ≤ _ := h3

lemma gridDm_le_Xlo {K : ℕ} (hK : 100 ≤ K) : gridDm K (N K) ≤ Xlo K := by
  have h1 := gridDm_le_gridP₀Bound K (N K) (by omega)
  have h2 : (gridP₀Bound K (N K) : ℝ) ≤ Real.exp (logP₀Nat K) := by
    have hpos : (0 : ℝ) < gridP₀Bound K (N K) := by
      have := gridDm_pos K (N K)
      exact_mod_cast (by omega : 0 < gridP₀Bound K (N K))
    calc (gridP₀Bound K (N K) : ℝ) = Real.exp (Real.log (gridP₀Bound K (N K))) :=
          (Real.exp_log hpos).symm
      _ ≤ _ := Real.exp_le_exp.2 (log_gridP₀Bound_le (by omega))
  have h3 := two_mul_exp_le_Xlo hK
  have h4 : (gridDm K (N K) : ℝ) ≤ gridP₀Bound K (N K) := by exact_mod_cast h1
  have : (gridDm K (N K) : ℝ) ≤ (Xlo K : ℝ) := by
    have := Real.exp_pos (logP₀Nat K : ℝ)
    linarith
  exact_mod_cast this

theorem farC_le_down {K X' : ℕ} (hK : 100 ≤ K) (hlo : Xlo K ≤ X') (hhi : X' ≤ X K) :
    farC (gridOf K (N K) (by omega)) X' (gridDm K (N K)) ≤ logP₀Nat K + m K + 10 := by
  set G := gridOf K (N K) (by omega : 1 ≤ K) with hG
  have hP₀ : (0 : ℝ) < G.P₀ := by exact_mod_cast G.P₀_pos
  have hXlo := Xlo_pos K
  have hX'pos : 0 < X' := by omega
  have hXr : (0 : ℝ) < X' := by exact_mod_cast hX'pos
  have hhiR : ((X' : ℕ) : ℝ) ≤ ((X K : ℕ) : ℝ) := by exact_mod_cast hhi
  have hcard := card_apSample_ge_half X' G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀
    (le_trans (two_mul_P₀_le_Xlo hK) hlo)
  have hcard0 : (0 : ℝ) < (apSample X' G.P₀ G.b₀).card := by
    have : (0 : ℝ) < (X' : ℝ) / (2 * G.P₀) := by positivity
    linarith
  have hDmX : (gridDm K (N K) : ℝ) ≤ X' := by
    exact_mod_cast le_trans (gridDm_le_Xlo hK) hlo
  have hP₀exp := P₀_le_exp (K := K) (by omega)
  unfold farC
  -- first term: `(X+Dm)/|P| ≤ 4P₀`
  have h1 : (((X' + gridDm K (N K) : ℕ) : ℝ) / (apSample X' G.P₀ G.b₀).card)
      ≤ 4 * G.P₀ := by
    push_cast
    rw [div_le_iff₀ hcard0]
    calc (X' : ℝ) + gridDm K (N K) ≤ 2 * (X' : ℝ) := by linarith
      _ = 4 * G.P₀ * ((X' : ℝ) / (2 * G.P₀)) := by field_simp; ring
      _ ≤ 4 * G.P₀ * (apSample X' G.P₀ G.b₀).card := by gcongr
  have h1' : Real.log (((X' + gridDm K (N K) : ℕ) : ℝ) / (apSample X' G.P₀ G.b₀).card)
      ≤ 2 + logP₀Nat K := by
    have hpos : (0 : ℝ) < ((X' + gridDm K (N K) : ℕ) : ℝ) / (apSample X' G.P₀ G.b₀).card := by
      push_cast; positivity
    calc Real.log (((X' + gridDm K (N K) : ℕ) : ℝ) / (apSample X' G.P₀ G.b₀).card)
        ≤ Real.log (4 * G.P₀) := Real.log_le_log hpos h1
      _ = Real.log 4 + Real.log G.P₀ := Real.log_mul (by norm_num) hP₀.ne'
      _ ≤ 2 + logP₀Nat K := by
          have ha : Real.log 4 ≤ 2 := by
            have : (4 : ℝ) ≤ Real.exp 2 := by
              have := Real.add_one_le_exp (1 : ℝ)
              have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
              rw [h2]; nlinarith [Real.exp_pos 1]
            calc Real.log 4 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) this
              _ = 2 := Real.log_exp 2
          have hb : Real.log G.P₀ ≤ logP₀Nat K := by
            calc Real.log G.P₀ ≤ Real.log (Real.exp (logP₀Nat K)) := Real.log_le_log hP₀ hP₀exp
              _ = logP₀Nat K := Real.log_exp _
          linarith
  -- second term: `log(log(X+Dm)+1) ≤ m + 8`
  have h2 : Real.log (Real.log ((X' + gridDm K (N K) : ℕ) : ℝ) + 1) ≤ m K + 8 := by
    have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogX : Real.log ((X' + gridDm K (N K) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m K + 7) := by
      have hle : ((X' + gridDm K (N K) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (100 * 2 ^ m K + 1) := by
        push_cast
        have hXK : ((X K : ℕ) : ℝ) = (2 : ℝ) ^ (100 * 2 ^ m K) := by unfold X; push_cast; rfl
        have hDmXK : ((gridDm K (N K) : ℕ) : ℝ) ≤ ((X K : ℕ) : ℝ) := by
          exact_mod_cast gridDm_le_X hK
        rw [pow_succ]
        push_cast at hXK hDmXK hhiR
        linarith
      calc Real.log ((X' + gridDm K (N K) : ℕ) : ℝ)
          ≤ Real.log ((2 : ℝ) ^ (100 * 2 ^ m K + 1)) :=
            Real.log_le_log (by push_cast; positivity) hle
        _ = (100 * 2 ^ m K + 1 : ℕ) * Real.log 2 := by rw [Real.log_pow]
        _ ≤ (100 * 2 ^ m K + 1 : ℕ) := by
            have : (0 : ℝ) ≤ (100 * 2 ^ m K + 1 : ℕ) := by positivity
            nlinarith
        _ ≤ (2 : ℝ) ^ (m K + 7) := by
            have : 100 * 2 ^ m K + 1 ≤ 2 ^ (m K + 7) := by
              rw [pow_add]
              have : 1 ≤ 2 ^ m K := Nat.one_le_two_pow
              omega
            exact_mod_cast this
    have hpos : (0 : ℝ) < Real.log ((X' + gridDm K (N K) : ℕ) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ Real.log ((X' + gridDm K (N K) : ℕ) : ℝ) :=
        Real.log_nonneg (by
          push_cast
          have h1 : (1 : ℝ) ≤ (X' : ℝ) := by exact_mod_cast hX'pos
          linarith [(Nat.cast_nonneg (gridDm K (N K)) : (0:ℝ) ≤ ((gridDm K (N K) : ℕ) : ℝ))])
      linarith
    calc Real.log (Real.log ((X' + gridDm K (N K) : ℕ) : ℝ) + 1)
        ≤ Real.log ((2 : ℝ) ^ (m K + 8)) := by
          apply Real.log_le_log hpos
          have : (1 : ℝ) ≤ (2 : ℝ) ^ (m K + 7) := one_le_pow₀ (by norm_num)
          rw [pow_succ]
          linarith
      _ = (m K + 8 : ℕ) * Real.log 2 := by rw [Real.log_pow]
      _ ≤ (m K + 8 : ℕ) := by
          have : (0 : ℝ) ≤ (m K + 8 : ℕ) := by positivity
          nlinarith
      _ = m K + 8 := by push_cast; ring
  linarith


/-- **Leaf 2** — `G4ScheduleFar.hfar_holds`, at any `X'` with `Xlo K ≤ X' ≤ X K`. -/
theorem hfar_holds_down {K X' : ℕ} (hK : 100 ≤ K) (hlo : Xlo K ≤ X') (hhi : X' ≤ X K) :
    (2 : ℝ) ^ K / Real.log 2
      * ((1 / 4 : ℝ) ^ (K + N K)
        * ((farC (gridOf K (N K) (by omega)) X' (gridDm K (N K)) + 2 * (K + N K : ℕ) + 2) / 3
          + 2 / 9))
      ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ K) := by
  have hfarC := farC_le_down hK hlo hhi
  have hne' : (apSample X' (gridOf K (N K) (by omega)).P₀
      (gridOf K (N K) (by omega)).b₀).Nonempty :=
    apSample_nonempty_of_le _ _ _ (gridOf K (N K) (by omega)).P₀_pos
      (gridOf K (N K) (by omega)).b₀_lt_P₀ (le_trans (two_mul_P₀_le_Xlo hK) hlo)
  have hfar0 := farC_nonneg (gridOf K (N K) (by omega)) X' hne' (gridDm K (N K))
  set C := farC (gridOf K (N K) (by omega)) X' (gridDm K (N K)) with hC
  have hl2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  -- the bracket is at most `A/3` with `A = logP₀Nat + m + 2J + 13`
  set A : ℕ := logP₀Nat K + m K + 2 * J K + 13 with hA
  have hbr : (C + 2 * (K + N K : ℕ) + 2) / 3 + 2 / 9 ≤ (A : ℝ) / 3 := by
    have hJ : (J K : ℝ) = K + N K := by unfold J; push_cast; ring
    rw [hA]; push_cast; rw [hJ]
    linarith
  have hbr0 : 0 ≤ (C + 2 * (K + N K : ℕ) + 2) / 3 + 2 / 9 := by positivity
  -- the ℕ inequality
  have hN := four_mul_le_four_pow_N hK
  have hNr : (4 : ℝ) * K * A ≤ (4 : ℝ) ^ N K := by exact_mod_cast hN
  -- assemble
  have e1 : (1 / 4 : ℝ) ^ (K + N K) = (1 / 4 : ℝ) ^ K * (1 / 4 : ℝ) ^ N K := pow_add _ _ _
  have e2 : (2 : ℝ) ^ K * (1 / 4 : ℝ) ^ K = (1 / 2 : ℝ) ^ K := by
    rw [← mul_pow]; norm_num
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ N K := by positivity
  have hq : (1 / 4 : ℝ) ^ N K * (A : ℝ) ≤ 1 / (4 * K) := by
    rw [one_div_pow, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ h4pos (by positivity)]
    linarith
  have hη : (0 : ℝ) < (1 / 2 : ℝ) ^ K := by positivity
  calc (2 : ℝ) ^ K / Real.log 2
        * ((1 / 4 : ℝ) ^ (K + N K) * ((C + 2 * (K + N K : ℕ) + 2) / 3 + 2 / 9))
      ≤ (2 : ℝ) ^ K / Real.log 2 * ((1 / 4 : ℝ) ^ (K + N K) * ((A : ℝ) / 3)) := by gcongr
    _ = (1 / 2 : ℝ) ^ K * ((1 / 4 : ℝ) ^ N K * A) / (3 * Real.log 2) := by
        rw [e1, ← e2]; field_simp
    _ ≤ (1 / 2 : ℝ) ^ K * (1 / (4 * K)) / 2 := by
        gcongr
        linarith
    _ = (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ K) := by field_simp; ring

/-- **Leaf 3** — `G4EntropyBudget.smallPrime_term_le`, at any `X'` with `Xlo K ≤ X' ≤ X K`. -/
theorem smallPrime_term_le_down {K k₄ X' : ℕ} (hK4 : K = 4 * k₄) (hK : 100 ≤ K)
    (hlo : Xlo K ≤ X') (hhi : X' ≤ X K) :
    (((2 * Dj K k₄ + 1) ^ ((K ^ 2) ^ K) : ℕ) : ℝ)
      * smallPrimeBound (smallPrimes (R K) (gridOf K (N K) (by omega)).P₀)
          (T K) (R K) (Mc K)
          (apSample X' (gridOf K (N K) (by omega)).P₀ (gridOf K (N K) (by omega)).b₀).card
          (Real.exp 1) (13 / 2) (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K)
      ≤ 3 * Real.exp (-4) + 1 / 32 := by
  sorry

/-! ### The assembly -/

/-- **E0 at every outer scale between `√(X K)` and `X K`.**  Verbatim the proof of
`entropy_E0`, with `X'` in place of `X K`; the only inputs that noticed the change are the three
leaves above. -/
theorem entropy_E0_down {K k₄ X' : ℕ} (hK4 : K = 4 * k₄) (hK : 33856 ≤ K)
    (hlo : Xlo K ≤ X') (hhi : X' ≤ X K) :
    (1 / 5 : ℝ) * ((k₄ : ℝ) * (((K ^ 2 + 1) ^ K : ℕ) : ℝ))
      < (NormalNumbers.G4Entropy.jointLaw (gridOf K (N K) (by omega))
          (b₀_lt_of_Xlo_le (show 100 ≤ K by omega) hlo) k₄ (primeLambertAtBase 4)).H₂ := by
  have hK100 : 100 ≤ K := by omega
  have hK1 : 1 ≤ K := by omega
  have hk : 25 ≤ k₄ := by omega
  have hKr : (100 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK100
  set G := gridOf K (N K) hK1 with hGdef
  set hX := b₀_lt_of_Xlo_le (show 100 ≤ K by omega) hlo with hXdef
  set η : ℝ := (1 / 2 : ℝ) ^ k₄ with hηdef
  have hη : (0 : ℝ) < η := by rw [hηdef]; positivity
  set ε : ℝ := 1 / (K : ℝ) with hεdef
  have hε : (0 : ℝ) < ε := by rw [hεdef]; positivity
  set hne := NormalNumbers.G4Entropy.apSample_nonempty G hX with hnedef
  set fr := gridFrame 4 (by norm_num) G X' hne (smallPrimes (R K) G.P₀)
    (frozenGamma 4 G) hη hε (Dj K k₄) with hfrdef
  -- real lifts of `θ` and `γ`
  choose θr hθr using fun ν => QuotientAddGroup.mk_surjective (fr.θ ν)
  choose γr hγr using fun ν => QuotientAddGroup.mk_surjective (fr.γ ν)
  set M : ℝ := (k₄ : ℝ) * (((K ^ 2 + 1) ^ K : ℕ) : ℝ) with hMdef
  have hMpos : (0 : ℝ) < M := by
    rw [hMdef]
    have : (0 : ℝ) < (k₄ : ℝ) := by exact_mod_cast (show 0 < k₄ by omega)
    have h2 : (0 : ℝ) < (((K ^ 2 + 1) ^ K : ℕ) : ℝ) := by
      have : 0 < (K ^ 2 + 1) ^ K := Nat.pow_pos (by positivity)
      exact_mod_cast this
    positivity
  -- ### the four terms
  -- (1) the cover term
  have hcover : (2 : ℝ) ^ ((1 - (4 / 5 : ℝ) / 2) * M)
      * (∑ G' ∈ fr.goodSets, η ^ G'.card * (volume (fr.pieceCube G')).toReal)
      ≤ (1 / 8 : ℝ) / 2 ^ K := by
    refine entropy_cover_sum_le 4 (by norm_num) G X' hne _ _ hη hε (Dj K k₄)
      (Lg := (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K))
      (by rw [hεdef, div_lt_one (by linarith)]; linarith)
      (Nat.one_le_pow _ _ (show 0 < K ^ 2 by positivity)) ?_ (by positivity) (by positivity) ?_
    · have h := log_det_one_add_tensorGram_le' (K := K) hK1
      show Real.log (1 + tensorGram G.K G.s).det
        ≤ (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K)
      push_cast
      exact h
    · intro g hglo hghi
      have := entropy_cover_bound (K := K) (m := k₄) (g := g) (η := η)
        (Lg := (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K)) (δ := 4 / 5)
        hK ?_ (by norm_num) (by norm_num) ?_ hη ?_ le_rfl ?_ ?_
      · refine this.trans_eq ?_
        show (1 / 8 : ℝ) / 2 ^ (K + (K ^ 2) ^ K) = (1 / 8 : ℝ) / 2 ^ K / 2 ^ G.rDim
        rw [show G.rDim = (K ^ 2) ^ K from rfl, pow_add]
        field_simp
      · rw [hK4]; push_cast; ring_nf; rfl
      · -- `92√K + 46 ≤ (4/5)·K·log 2`
        have hs : (184 : ℝ) * Real.sqrt K ≤ (K : ℝ) := by
          have h1 : (184 : ℝ) ≤ Real.sqrt K := by
            have h : Real.sqrt (33856 : ℝ) ≤ Real.sqrt K :=
              Real.sqrt_le_sqrt (by exact_mod_cast hK)
            have he : Real.sqrt (33856 : ℝ) = 184 := by
              rw [show (33856 : ℝ) = 184 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
            linarith [he ▸ h]
          have h2 : Real.sqrt K * Real.sqrt K = (K : ℝ) := Real.mul_self_sqrt (by positivity)
          nlinarith [Real.sqrt_nonneg (K : ℝ)]
        have hKb : (33856 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
        have hl2 : (0.6931 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
        nlinarith [hs, hKb, hl2]
      · rw [hηdef, ← pow_mul, hK4, mul_comm]
      · exact hglo
      · exact hghi
  -- (2) the Jackson term
  have hjack : 2 * (1 / (fr.res * Real.sqrt ((Dj K k₄ : ℕ) + 1))) ≤ 1 / 8 := by
    have h := Sched.jackson_term_le (K := K) (k₄ := k₄) hK1
    have hres : fr.res = (1 / (K : ℝ)) * (1 / 2 : ℝ) ^ k₄ := by
      rw [hfrdef]; rfl
    rw [hres]
    exact h
  -- (3) `PropD`
  have hD : fr.PropD ((1 / 8 : ℝ) + (1 / 8 : ℝ)) := by
    refine gridFrame_propD_of_bounds 4 (by norm_num) G X' (R K) (Y K) hne
      (show 0 < K from hK1) (R_ge_two K) (R_le_Y K)
      (Mx := ((X' + J K * gridDm K (N K) : ℕ) : ℝ)) ?_ ?_
      (Dm := gridDm K (N K)) (gridOf.d_le hK1) hη hε (Dj K k₄) ?_ ?_
    · have : 1 ≤ X' := by have := Xlo_pos K; omega
      exact_mod_cast le_add_right this
    · exact fun n hn i => by exact_mod_cast gridOf.add_shiftAL_le hK1 hn i
    · have h := hbig_holds_down hK4 hK100 hlo hhi
      simp only [Nat.cast_ofNat, rowL1_four, rowL2_four, hεdef, hηdef,
        show G.K = K from rfl, show G.P₀ = (gridOf K (N K) hK1).P₀ from rfl,
        show G.b₀ = (gridOf K (N K) hK1).b₀ from rfl]
      ring_nf
      ring_nf at h
      linarith
    · have h := hfar_holds_down hK100 hlo hhi
      simp only [Nat.cast_ofNat, farBound_four, hεdef, hηdef,
        show G.K = K from rfl, show G.N = N K from rfl,
        show G.P₀ = (gridOf K (N K) hK1).P₀ from rfl,
        show G.b₀ = (gridOf K (N K) hK1).b₀ from rfl]
      have hkK : (1 / 2 : ℝ) ^ K ≤ (1 / 2 : ℝ) ^ k₄ :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have hKpos : (0 : ℝ) < K := by linarith
      calc _ ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ K) := h
        _ ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by gcongr
  -- (4) `PropC` and the small-prime term
  set δ₃ : ℝ := smallPrimeBound (smallPrimes (R K) G.P₀) (Fintype.card G.Idx) (R K) (Mc K)
    (apSample X' G.P₀ G.b₀).card (Real.exp 1) (13 / 2)
    (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ G.K) with hδ₃def
  have hC : fr.PropC δ₃ :=
    gridFrame_propC_four G X' hne _ _ hη hε (R := R K)
      (fun p hp => (mem_smallPrimes.1 hp).1) (fun p hp => (mem_smallPrimes.1 hp).2.2)
      (by have := R_ge_two K; omega) (fun p hp => (mem_smallPrimes.1 hp).2.1)
      (by
        show 1 + Nat.clog 4 (2 ^ K * Dj K k₄) ≤ N K
        have h := (Nat.clog_le_iff_le_pow (by norm_num)).2 (two_pow_mul_Dj_le hK4 hK100)
        have hN : 1 ≤ N K := N_pos hK1
        omega)
      (Mc_pos hK1) (Real.one_le_exp zero_le_one) (by norm_num)
  have hδ₃nn : (0 : ℝ) ≤ δ₃ :=
    smallPrimeBound_nonneg _ _ _ _ _ (by positivity) (by norm_num)
  have hsmall : (((2 * Dj K k₄ + 1) ^ G.rDim : ℕ) : ℝ) * δ₃ ≤ 3 * Real.exp (-4) + 1 / 32 := by
    have h := smallPrime_term_le_down hK4 hK100 hlo hhi
    have hcard : Fintype.card G.Idx = T K := gridOf.card_Idx hK1
    rw [hδ₃def, hcard]
    exact h
  -- ### E0
  have hmη : ((2 : ℝ)⁻¹) ^ k₄ ≤ η := by rw [hηdef]; norm_num
  have hmain := NormalNumbers.G4Entropy.entropy_gt_of_budget G X' hX (by norm_num)
    (smallPrimes (R K) G.P₀) (frozenGamma 4 G) hη hε (Dj K k₄) k₄ θr γr hθr hγr hmη
    (δ := 4 / 5) (M := M) (by norm_num) (by norm_num) hMpos hD hC hδ₃nn ?_
  · have he : (1 : ℝ) - 4 / 5 = 1 / 5 := by norm_num
    rw [he] at hmain
    exact hmain
  · have he4 := Sched.exp_neg_four_le
    have hR : (4 / 5 : ℝ) / (2 - 4 / 5) = 2 / 3 := by norm_num
    have hc8 : (1 / 8 : ℝ) / 2 ^ K ≤ 1 / 8 := by
      have : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    rw [hR]
    linarith [hcover, hjack, hsmall]

end Sched

end NormalNumbers.G4
