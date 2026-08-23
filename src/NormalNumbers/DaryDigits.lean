/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.TBrickDefs
import NormalNumbers.RealDefs

/-!
# W5 — d-ary digit extraction

The Lemma-13 payload locates every point of a refined cylinder in a definite
order-`(m+k)` cell `J·d^k + blockNatVal β` inside its order-`m` cell `J`.
This file converts that cell membership into **digits**: the base-`d` digits
of `x` at positions `m, …, m+k−1` are exactly `β`.

* `blockNatVal_digit` — digit `l` of a big-endian block value is
  `V / d^(len−1−l) % d`;
* `floor_pow_of_mem_daryCell` — coarsening a cell membership to a floor at
  any lower order (integer division);
* `digitOf_eq_of_cells` / `digit_window_eq` — the extraction.
-/

namespace NormalNumbers

/-- Digit `l` (big-endian) of a block value: `blockNatVal / b^(len−1−l) % b`. -/
theorem blockNatVal_digit (b : ℕ) :
    ∀ (w : List ℕ), (∀ a ∈ w, a < b) → ∀ l, l < w.length →
      blockNatVal b w / b ^ (w.length - 1 - l) % b = w.getD l 0 := by
  intro w
  induction w with
  | nil => intro _ l hl; simp at hl
  | cons a w ih =>
    intro hw l hl
    have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le _) (hw a List.mem_cons_self)
    have hV : blockNatVal b w < b ^ w.length :=
      blockNatVal_lt b w (fun e he => hw e (List.mem_cons_of_mem a he))
    rw [blockNatVal_cons]
    cases l with
    | zero =>
      have he : (a :: w).length - 1 - 0 = w.length := by
        simp
      rw [he, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
        Nat.div_eq_of_lt hV]
      simp [Nat.mod_eq_of_lt (hw a List.mem_cons_self)]
    | succ l =>
      have hlw : l < w.length := by
        simpa [Nat.succ_lt_succ_iff] using hl
      have he : (a :: w).length - 1 - (l + 1) = w.length - 1 - l := by
        simp only [List.length_cons]
        omega
      rw [he]
      have hsplit : w.length = (l + 1) + (w.length - 1 - l) := by omega
      have hpow : b ^ w.length = b ^ (l + 1) * b ^ (w.length - 1 - l) := by
        rw [← pow_add]
        congr 1
      rw [hpow, ← Nat.mul_assoc, Nat.add_comm,
        Nat.add_mul_div_right _ _ (by positivity)]
      have hmod : (blockNatVal b w / b ^ (w.length - 1 - l)
          + a * b ^ (l + 1)) % b
          = blockNatVal b w / b ^ (w.length - 1 - l) % b := by
        have h2 : a * b ^ (l + 1) = a * b ^ l * b := by ring
        rw [h2, Nat.add_mul_mod_self_right]
      rw [hmod, ih (fun e he => hw e (List.mem_cons_of_mem a he)) l hlw]
      simp

/-- Coarsening a definite cell to a floor at a lower order: if
`x ∈ daryCell d M F 1` then `⌊x·d^(M−q)⌋ = F / d^q`. -/
theorem floor_pow_of_mem_daryCell {d M : ℕ} (hd : 1 ≤ d) {F : ℤ} {x : ℝ}
    (hx : x ∈ daryCell d M F 1) (q : ℕ) (hq : q ≤ M) :
    ⌊x * (d : ℝ) ^ (M - q)⌋ = F / (d : ℤ) ^ q := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hpowM : (0 : ℝ) < (d : ℝ) ^ M := by positivity
  have hpowq : (0 : ℝ) < (d : ℝ) ^ q := by positivity
  have hpowqZ : (0 : ℤ) < (d : ℤ) ^ q := by positivity
  obtain ⟨hl, hr⟩ := hx
  set E : ℤ := F / (d : ℤ) ^ q with hE
  have h1 : E * (d : ℤ) ^ q ≤ F := Int.ediv_mul_le F hpowqZ.ne'
  have h2 : F < (E + 1) * (d : ℤ) ^ q := Int.lt_ediv_add_one_mul_self F hpowqZ
  have hsplit : (d : ℝ) ^ M = (d : ℝ) ^ (M - q) * (d : ℝ) ^ q := by
    rw [← pow_add]
    congr 1
    omega
  rw [Int.floor_eq_iff]
  constructor
  · -- E ≤ x·d^(M−q)
    have h1R : (E : ℝ) * (d : ℝ) ^ q ≤ F := by exact_mod_cast h1
    have hxl : (F : ℝ) / (d : ℝ) ^ M ≤ x := hl
    rw [div_le_iff₀ hpowM] at hxl
    rw [hsplit] at hxl
    nlinarith
  · -- x·d^(M−q) < E + 1
    have h2R : (F : ℝ) + 1 ≤ ((E : ℝ) + 1) * (d : ℝ) ^ q := by
      have : F + 1 ≤ (E + 1) * (d : ℤ) ^ q := h2
      exact_mod_cast this
    have hxr : x < ((F : ℝ) + 1) / (d : ℝ) ^ M := by
      exact_mod_cast hr
    rw [lt_div_iff₀ hpowM] at hxr
    rw [hsplit] at hxr
    have hq1 : (1 : ℝ) ≤ (d : ℝ) ^ q := one_le_pow₀ (by exact_mod_cast hd)
    nlinarith

/-- **Digit extraction**: if `x` sits in the order-`m` cell `J ≥ 0` and in
the order-`(m+k)` sub-cell `J·d^k + blockNatVal β`, then its base-`d` digits
at positions `m, …, m+k−1` are exactly `β`. -/
theorem digitOf_eq_of_cells {d m k : ℕ} (hd : 1 ≤ d) {J : ℤ} (hJ : 0 ≤ J)
    {x : ℝ} {β : Fin k → Fin d}
    (hx2 : x ∈ daryCell d (m + k)
      (J * d ^ k + blockNatVal d (List.ofFn fun i => (β i : ℕ))) 1)
    (l : Fin k) :
    digitOf d x (m + l) = β l := by
  set V : ℕ := blockNatVal d (List.ofFn fun i => (β i : ℕ)) with hV
  -- the floor at order `m + l + 1`
  have hq : k - 1 - (l : ℕ) ≤ m + k := by omega
  have hfloor := floor_pow_of_mem_daryCell hd hx2 (k - 1 - (l : ℕ)) hq
  have hMq : m + k - (k - 1 - (l : ℕ)) = m + (l : ℕ) + 1 := by
    have := l.isLt
    omega
  rw [hMq] at hfloor
  -- integer division: the `J`-part contributes a multiple of `d`
  set e : ℕ := k - 1 - (l : ℕ) with he
  have hsplitk : k = ((l : ℕ) + 1) + e := by
    have := l.isLt
    omega
  clear_value e
  have hdvd : (J * (d : ℤ) ^ k + V) / (d : ℤ) ^ e
      = (V : ℤ) / (d : ℤ) ^ e + J * (d : ℤ) ^ ((l : ℕ) + 1) := by
    have hpow : (d : ℤ) ^ k = (d : ℤ) ^ ((l : ℕ) + 1) * (d : ℤ) ^ e := by
      rw [← pow_add]
      congr 1
    rw [hpow, ← mul_assoc, add_comm,
      Int.add_mul_ediv_right _ _ (by positivity : (0 : ℤ) < (d : ℤ) ^ e).ne']
  rw [hdvd] at hfloor
  -- convert to ℕ
  have hVdiv : ((V / d ^ e : ℕ) : ℤ) = (V : ℤ) / (d : ℤ) ^ e := by
    rw [Int.natCast_div]
    push_cast
    rfl
  obtain ⟨Jn, rfl⟩ := Int.eq_ofNat_of_zero_le hJ
  have hcast : (V : ℤ) / (d : ℤ) ^ e + (Jn : ℤ) * (d : ℤ) ^ ((l : ℕ) + 1)
      = ((V / d ^ e + Jn * d ^ ((l : ℕ) + 1) : ℕ) : ℤ) := by
    push_cast
    rfl
  rw [hcast] at hfloor
  rw [digitOf, hfloor, Int.toNat_natCast]
  -- ℕ arithmetic: kill the `Jn` term mod `d`, read the digit
  have hmod : (V / d ^ e + Jn * d ^ ((l : ℕ) + 1)) % d = V / d ^ e % d := by
    have h2 : Jn * d ^ ((l : ℕ) + 1) = Jn * d ^ (l : ℕ) * d := by ring
    rw [h2, Nat.add_mul_mod_self_right]
  rw [hmod]
  have hdig := blockNatVal_digit d (List.ofFn fun i => (β i : ℕ))
    (by
      intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
      exact (β i).isLt)
    (l : ℕ) (by simp [l.isLt])
  rw [List.length_ofFn, ← he, ← hV] at hdig
  rw [hdig, List.getD_eq_getElem _ 0 (by simp [l.isLt]), List.getElem_ofFn]

/-- The digit **window**: the positions `m, …, m+k−1` of `x` read exactly
the block `β`, as lists. -/
theorem digit_window_eq {d m k : ℕ} (hd : 1 ≤ d) {J : ℤ} (hJ : 0 ≤ J)
    {x : ℝ} {β : Fin k → Fin d}
    (hx2 : x ∈ daryCell d (m + k)
      (J * d ^ k + blockNatVal d (List.ofFn fun i => (β i : ℕ))) 1) :
    (List.range k).map (fun l => digitOf d x (m + l))
      = List.ofFn (fun i => (β i : ℕ)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    have hik : i < k := by simpa using h1
    exact digitOf_eq_of_cells hd hJ hx2 ⟨i, hik⟩

end NormalNumbers
