/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorSelfSimilar
import NormalNumbers.Derandomize

/-!
# Exact arithmetic for the `Ω_k` lower approximations

Helpers for `ExplicitOmegaK.approx_Gfam`: a coin prefix of length `D` pins `cantorReal ω` to
`[Y/2^{2D+1}, Y/2^{2D+1} + 4^{-D}/6]` with `Y = yN p` primitive recursive; a primitive recursive
integer `k`-th root; integer sign parts through the `ℤ` encoding.
-/

open MeasureTheory

namespace NormalNumbers.OmegaKApprox

open ExplicitSquare CantorSelfSimilar Derandomize

/-! ## The prefix point -/

/-- Numerator of the left end of the prefix cylinder, over `2^{2|p|+1}`. -/
def yN : List Bool → ℕ
  | [] => 1
  | c :: q => (3 + c.toNat) * 4 ^ q.length + yN q

theorem primrec_yN : Primrec yN := by
  have h : Primrec₂ fun (_ : List Bool) (x : Bool × List Bool × ℕ) =>
      (3 + x.1.toNat) * 4 ^ x.2.1.length + x.2.2 := by
    have hb : Primrec fun b : Bool => b.toNat :=
      (Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)).of_eq fun b => by
        cases b <;> rfl
    exact (Primrec.nat_add.comp (Primrec.nat_mul.comp
      (Primrec.nat_add.comp (Primrec.const 3) (hb.comp (Primrec.fst.comp Primrec.snd)))
      (ComputableNormal.primrec_pow.comp (Primrec.const 4)
        (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂
  refine (Primrec.list_rec Primrec.id (Primrec.const 1) h).of_eq fun p => ?_
  induction p with
  | nil => rfl
  | cons c q ih => show _ = _ + yN q; rw [← ih]; rfl

theorem cantorReal_le_two_thirds (ω : ℕ → Bool) : cantorReal ω ≤ 2 / 3 := by
  have hbdd : BddAbove (Set.range cantorReal) :=
    ⟨1, by rintro _ ⟨ω, rfl⟩; exact (cantorReal_mem_Ico ω).2.le⟩
  set S := ⨆ ω, cantorReal ω
  have hstep : ∀ ω, cantorReal ω ≤ 5 / 8 + (S - 1 / 2) / 4 := by
    intro ω
    have hω : ω = consB (ω 0) (fun n => ω (n + 1)) := by
      funext n; cases n <;> rfl
    rw [hω, cantorReal_consB]
    have := le_ciSup hbdd (fun n => ω (n + 1))
    unfold psi; split_ifs <;> linarith
  have hS : S ≤ 5 / 8 + (S - 1 / 2) / 4 := ciSup_le hstep
  have := hstep ω
  linarith

theorem one_half_le_cantorReal (ω : ℕ → Bool) : 1 / 2 ≤ cantorReal ω := by
  have hsum : Summable fun i => (cantorDigits ω i : ℝ) / ((2 : ℕ) : ℝ) ^ (i + 1) := by
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      ((summable_geometric_two).mul_left (1 / 2))
    have : (cantorDigits ω i : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 (cantorDigits_lt ω i)
    rw [Nat.cast_ofNat, pow_succ]
    calc (cantorDigits ω i : ℝ) / (2 ^ i * 2) ≤ 1 / (2 ^ i * 2) := by gcongr
      _ = 1 / 2 * (1 / 2) ^ i := by rw [div_pow, one_pow]; field_simp
  have := hsum.le_tsum 0 (fun j _ => by positivity)
  unfold cantorReal realOfDigits
  simpa [cantorDigits] using this

theorem pre_succ (ω : ℕ → Bool) (D : ℕ) : pre ω (D + 1) = ω 0 :: pre (fun n => ω (n + 1)) D := by
  simp [pre, List.range_succ_eq_map, Function.comp_def]

/-- **A prefix pins the Cantor point.** -/
theorem cantorReal_mem_prefix (D : ℕ) : ∀ ω : ℕ → Bool,
    (yN (pre ω D) : ℝ) / 2 ^ (2 * D + 1) ≤ cantorReal ω ∧
      cantorReal ω ≤ (yN (pre ω D) : ℝ) / 2 ^ (2 * D + 1) + (1 / 4 : ℝ) ^ D / 6 := by
  induction D with
  | zero =>
    intro ω
    simp only [pre, List.range_zero, List.map_nil, yN]
    norm_num
    exact ⟨one_half_le_cantorReal ω, by linarith [cantorReal_le_two_thirds ω]⟩
  | succ D ih =>
    intro ω
    have hω : ω = consB (ω 0) (fun n => ω (n + 1)) := by funext n; cases n <;> rfl
    obtain ⟨h1, h2⟩ := ih (fun n => ω (n + 1))
    rw [pre_succ, yN, length_pre]
    conv => enter [1, 2]; rw [hω]
    conv => enter [2, 1]; rw [hω]
    rw [cantorReal_consB]
    set t := cantorReal (fun n => ω (n + 1))
    set Y : ℝ := (yN (pre (fun n => ω (n + 1)) D) : ℝ)
    have e : (((3 + (ω 0).toNat) * 4 ^ D + yN (pre (fun n => ω (n + 1)) D) : ℕ) : ℝ) /
        2 ^ (2 * (D + 1) + 1) = (3 + ((ω 0).toNat : ℝ)) / 8 + Y / 2 ^ (2 * D + 1) / 4 := by
      push_cast
      rw [show 2 * (D + 1) + 1 = (2 * D + 1) + 2 by ring, pow_add,
        show (2 : ℝ) ^ (2 * D + 1) = 2 * 4 ^ D by rw [pow_succ, pow_mul]; norm_num; ring]
      field_simp; ring
    rw [e]
    have ep : psi (ω 0) t = (3 + ((ω 0).toNat : ℝ)) / 8 + t / 4 := by
      unfold psi; cases ω 0 <;> simp <;> ring
    rw [ep, pow_succ (1 / 4 : ℝ) D]
    constructor <;> linarith

/-! ## Integer `k`-th root -/

/-- `⌊Z^{1/k}⌋` by bounded search. -/
def iroot (k Z : ℕ) : ℕ := Nat.findGreatest (fun x => x ^ k ≤ Z) Z

theorem primrec_iroot : Primrec₂ iroot := by
  have hp : PrimrecRel fun (y : ℕ × ℕ) (x : ℕ) => x ^ y.1 ≤ y.2 :=
    Primrec.nat_le.comp (ComputableNormal.primrec_pow.comp Primrec.snd
      (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst)
  exact (Primrec.nat_findGreatest Primrec.snd hp).to₂

theorem iroot_pow_le {k : ℕ} (hk : 1 ≤ k) (Z : ℕ) : iroot k Z ^ k ≤ Z :=
  Nat.findGreatest_spec (P := fun x => x ^ k ≤ Z) (Nat.zero_le Z)
    (by rw [zero_pow (by omega)]; exact Nat.zero_le _)

theorem lt_iroot_succ_pow {k : ℕ} (hk : 1 ≤ k) (Z : ℕ) : Z < (iroot k Z + 1) ^ k := by
  by_cases h : iroot k Z + 1 ≤ Z
  · have := Nat.findGreatest_is_greatest (P := fun x => x ^ k ≤ Z) (Nat.lt_succ_self _) h
    exact not_le.1 this
  · have hz : Z < iroot k Z + 1 := by omega
    calc Z < iroot k Z + 1 := hz
      _ ≤ (iroot k Z + 1) ^ k := Nat.le_self_pow (by omega) _

/-! ## Integer sign parts -/

theorem encode_ofNat (n : ℕ) : Encodable.encode (Int.ofNat n) = 2 * n := by
  change Equiv.natSumNatEquivNat (Sum.inl n) = _; simp

theorem encode_negSucc (n : ℕ) : Encodable.encode (Int.negSucc n) = 2 * n + 1 := by
  change Equiv.natSumNatEquivNat (Sum.inr n) = _; simp

theorem primrec_toNat : Primrec fun z : ℤ => z.toNat := by
  have h : Primrec fun e : ℕ => (1 - e % 2) * (e / 2) :=
    Primrec.nat_mul.comp (Primrec.nat_sub.comp (Primrec.const 1)
      (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)))
      (Primrec.nat_div.comp Primrec.id (Primrec.const 2))
  refine (h.comp Primrec.encode).of_eq fun z => ?_
  rcases z with n | n
  · rw [encode_ofNat]; simp
  · rw [encode_negSucc]; simp

theorem primrec_negPart : Primrec fun z : ℤ => (-z).toNat := by
  have h : Primrec fun e : ℕ => (e % 2) * (e / 2 + 1) :=
    Primrec.nat_mul.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.succ.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2)))
  refine (h.comp Primrec.encode).of_eq fun z => ?_
  rcases z with n | n
  · rw [encode_ofNat]; simp
  · rw [encode_negSucc]; simp [Int.negSucc_eq]; try omega

theorem primrec_natAbs : Primrec fun z : ℤ => z.natAbs :=
  (Primrec.nat_add.comp primrec_toNat primrec_negPart).of_eq fun z => by omega

end NormalNumbers.OmegaKApprox
