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

Three leaves are open (`sorry`), each the `X'`-version of an existing `X K` lemma whose proof
goes through `card_apSample_ge_half`:

* `hbig_holds_down`   — `G4ScheduleBig.hbig_holds` at `X'`
* `hfar_holds_down`   — `G4ScheduleFar.hfar_holds` at `X'`
* `smallPrime_term_le_down` — `G4EntropyBudget.smallPrime_term_le` at `X'`

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

/-- **Leaf 2** — `G4ScheduleFar.hfar_holds`, at any `X'` with `Xlo K ≤ X' ≤ X K`. -/
theorem hfar_holds_down {K X' : ℕ} (hK : 100 ≤ K) (hlo : Xlo K ≤ X') (hhi : X' ≤ X K) :
    (2 : ℝ) ^ K / Real.log 2
      * ((1 / 4 : ℝ) ^ (K + N K)
        * ((farC (gridOf K (N K) (by omega)) X' (gridDm K (N K)) + 2 * (K + N K : ℕ) + 2) / 3
          + 2 / 9))
      ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ K) := by
  sorry

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
