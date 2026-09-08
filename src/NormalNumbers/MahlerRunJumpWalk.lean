/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerRunJump

/-!
# The run+jump chain: the data, the walk and the theorem 🧮

`MahlerRunJump.lean` proves the certificate valid for any `Data` satisfying `Hyp`.
This file constructs the data from the arithmetic hypotheses, builds the two closed
walks, and states `mahler_lower_bound_runjump`.

## The data

Let `T ≥ 1` be a common exponent with `p^T ≡ 1 (mod Dh j)` for every background
(`T = φ((b+L)!)` works).  Along the run (`i ≥ 1`) everything is forced and free:

    al i = p^{T−1} mod Dh i  (= p⁻¹),   cj i = p^{2T−2} mod Dh i  (= p⁻²),   ap i = 1.

At the closing jump (`i = 0`, `Dh 0 = b`, `Dn 0 = b + L ≡ p (mod b)`) the departure
condition is `p² · al 0 ≡ −1 (mod b)`, which `p^f ≡ −1 (mod b)` solves by
`al 0 = p^{3f−2}`; the landing condition `ap 0 · b ≡ 1 (mod b+L)` is solved by
`ap 0 = p^{T−1}` because `p ≡ b (mod b+L)`.

The junction digit `dj i` is then forced by the exact identity `key`, which holds
because `Dh i` and `Dn i` are coprime (`key_of_congr`).
-/

namespace NormalNumbers.Adder.RunJump

open NormalNumbers NormalNumbers.Mahler

/-! ### The exact-landing identity from the two congruences -/

/-- If the departure congruence holds mod `D`, the landing congruence holds mod `n`,
and `D`, `n` are coprime, the exact identity `key` holds with the forced digit. -/
theorem key_of_congr {p D n al ap : ℕ} (hD : 0 < D) (hn : 0 < n) (hcop : Nat.Coprime D n)
    (hdep : (p * al * n + 1) % D = 0) (hland : ap * D % n = 1)
    (hle : ap * D ≤ p * al * n + 1) :
    p * al * n + 1 = ap * D + ((p * al * n + 1 - ap * D) / (D * n)) * (D * n) := by
  have h1 : D ∣ p * al * n + 1 - ap * D :=
    Nat.dvd_sub (Nat.dvd_of_mod_eq_zero hdep) (Dvd.intro_left _ rfl)
  have h2 : n ∣ p * al * n + 1 - ap * D := by
    have hm : ap * D ≡ p * al * n + 1 [MOD n] := by
      unfold Nat.ModEq
      rw [hland, show p * al * n + 1 = 1 + n * (p * al) by ring, Nat.add_mul_mod_self_left]
      rcases Nat.lt_or_ge 1 n with h | h
      · exact (Nat.mod_eq_of_lt h).symm
      · have : n = 1 := by omega
        subst this; omega
    exact (Nat.modEq_iff_dvd' hle).1 hm
  have h3 := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h1 h2
  rw [Nat.div_mul_cancel h3]
  omega

/-! ### The data -/

variable (p b L f T : ℕ)

/-- Departure residues. -/
def alF (i : ℕ) : ℕ := if i = 0 then p ^ (3 * f - 2) % b else p ^ (T - 1) % Dh b i

/-- Injection sources. -/
def cjF (i : ℕ) : ℕ := if i = 0 then p ^ (3 * f - 3 + T) % b else p ^ (2 * T - 2) % Dh b i

/-- Landing residues. -/
def apF (i : ℕ) : ℕ := if i = 0 then p ^ (T - 1) % Dn b L 0 else 1

/-- Junction digits (forced by `key`). -/
def djF (i : ℕ) : ℕ :=
  (p * alF p b f T i * Dn b L i + 1 - apF p b L T i * Dh b i) / (Dh b i * Dn b L i)

/-- The run+jump data. -/
def mk : Data p b L := ⟨alF p b f T, cjF p b f T, apF p b L T, djF p b L f T⟩

/-- The arithmetic hypotheses of the chain. -/
structure Arith : Prop where
  hb : 3 ≤ b
  hL : 1 ≤ L
  hp : p = 2 * b + L
  hf : 1 ≤ f
  hpow : p ^ f % b = b - 1
  hT : 1 ≤ T
  hT1 : ∀ j, j ≤ L → p ^ T % Dh b j = 1
  hcop : Nat.Coprime b (b + L)

variable {p b L f T}

section arith

variable (A : Arith p b L f T)
include A

theorem A_hp0 : 0 < p := by have := A.hb; have := A.hp; omega

/-- `p^(T−1) · p ≡ 1` mod every background. -/
theorem pow_pred_mul {j : ℕ} (hj : j ≤ L) : p ^ (T - 1) % Dh b j * p % Dh b j = 1 := by
  rw [Nat.mod_mul_mod, ← pow_succ, Nat.sub_add_cancel A.hT]; exact A.hT1 j hj

omit A in
theorem Dh0 : Dh b 0 = b := by unfold Dh; rfl
omit A in
theorem Dn0 : Dn b L 0 = b + L := by unfold Dn nx Dh; simp

omit A in
theorem Dh_succ (i : ℕ) : Dh b (i + 1) = Dn b L (i + 1) + 1 := by
  unfold Dn nx Dh; simp; omega

theorem mk_al_lt (i : ℕ) (hi : i ≤ L) : (mk p b L f T).al i < Dh b i := by
  have := A.hb
  show alF p b f T i < Dh b i
  unfold alF; split_ifs with h0
  · subst h0; rw [Dh0]; exact Nat.mod_lt _ (by omega)
  · exact Nat.mod_lt _ (Dh_pos (by omega) _)

theorem mk_cj_lt (i : ℕ) (hi : i ≤ L) : (mk p b L f T).cj i < Dh b i := by
  have := A.hb
  show cjF p b f T i < Dh b i
  unfold cjF; split_ifs with h0
  · subst h0; rw [Dh0]; exact Nat.mod_lt _ (by omega)
  · exact Nat.mod_lt _ (Dh_pos (by omega) _)

theorem mk_ap_lt (i : ℕ) (hi : i ≤ L) : (mk p b L f T).ap i < Dn b L i := by
  have := A.hb
  show apF p b L T i < Dn b L i
  unfold apF; split_ifs with h0
  · subst h0; exact Nat.mod_lt _ (Dn_pos (by omega) _ _)
  · have := Dn_bounds (b := b) (L := L) i hi; omega

theorem mk_inj (i : ℕ) (hi : i ≤ L) :
    (mk p b L f T).cj i * p % Dh b i = (mk p b L f T).al i := by
  show cjF p b f T i * p % Dh b i = alF p b f T i
  have hT := A.hT
  unfold cjF alF; split_ifs with h0
  · subst h0
    rw [Dh0, Nat.mod_mul_mod, ← pow_succ, show 3 * f - 3 + T + 1 = (3 * f - 2) + T by have := A.hf; omega,
      pow_add, Nat.mul_mod, ← Dh0 (b := b), A.hT1 0 (by omega), mul_one, Nat.mod_mod]
  · rw [Nat.mod_mul_mod, ← pow_succ, show 2 * T - 2 + 1 = (T - 1) + T by omega, pow_add,
      Nat.mul_mod, A.hT1 i hi, mul_one, Nat.mod_mod]

/-- The departure congruence at every junction. -/
theorem mk_dep (i : ℕ) (hi : i ≤ L) :
    (p * (mk p b L f T).al i * Dn b L i + 1) % Dh b i = 0 := by
  show (p * alF p b f T i * Dn b L i + 1) % Dh b i = 0
  have hb := A.hb
  have hpe := A.hp
  unfold alF; split_ifs with h0
  · -- the jump: `p · p^{3f−2} · (b+L) + 1 ≡ p^{3f} + 1 ≡ 0 (mod b)`
    subst h0
    rw [Dh0, Dn0]
    have hb0 : 0 < b := by omega
    rw [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [ZMod.natCast_mod]
    push_cast
    have hpb : (p : ZMod b) = (L : ZMod b) := by
      rw [hpe]; push_cast; rw [ZMod.natCast_self]; ring
    have hpf : ((p : ZMod b)) ^ f = -1 := by
      have h1 : ((p ^ f % b : ℕ) : ZMod b) = ((b - 1 : ℕ) : ZMod b) := by rw [A.hpow]
      rw [ZMod.natCast_mod, Nat.cast_sub (by omega), ZMod.natCast_self] at h1
      push_cast at h1
      rw [h1]; ring
    have e : (p : ZMod b) * (p : ZMod b) ^ (3 * f - 2) * ((b : ZMod b) + (L : ZMod b)) + 1
        = (p : ZMod b) ^ (3 * f) + 1 := by
      rw [ZMod.natCast_self, zero_add, ← hpb, ← pow_succ', ← pow_succ,
        show 3 * f - 2 + 1 + 1 = 3 * f by have := A.hf; omega]
    rw [e, pow_mul', hpf]; ring
  · -- the run: `p · p⁻¹ · (D − 1) + 1 ≡ 0 (mod D)`
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [Dh_succ] at *
    set n := Dn b L (i + 1)
    have hmul := pow_pred_mul A (j := i + 1) hi
    rw [Dh_succ] at hmul
    have hdm := Nat.div_add_mod (p ^ (T - 1) % (n + 1) * p) (n + 1)
    rw [hmul] at hdm
    set t := p ^ (T - 1) % (n + 1) * p / (n + 1)
    apply Nat.mod_eq_zero_of_dvd
    refine ⟨t * n + 1, ?_⟩
    linear_combination n * hdm.symm

/-- The landing congruence at every junction. -/
theorem mk_land (i : ℕ) (hi : i ≤ L) :
    (mk p b L f T).ap i * Dh b i % Dn b L i = 1 := by
  show apF p b L T i * Dh b i % Dn b L i = 1
  have hb := A.hb
  have hpe := A.hp
  unfold apF; split_ifs with h0
  · subst h0
    rw [Dh0, Dn0]
    have hT := A.hT1 L le_rfl
    rw [show Dh b L = b + L from rfl] at hT
    have hn : 1 < b + L := by omega
    have hpb : (b : ZMod (b + L)) = (p : ZMod (b + L)) := by
      rw [hpe]; push_cast
      have : ((b : ZMod (b + L)) + (L : ZMod (b + L))) = 0 := by
        rw [← Nat.cast_add, ZMod.natCast_self]
      linear_combination (-1 : ZMod (b + L)) * this
    have hZ : ((p ^ (T - 1) % (b + L) * b : ℕ) : ZMod (b + L)) = ((1 : ℕ) : ZMod (b + L)) := by
      push_cast
      rw [ZMod.natCast_mod]
      push_cast
      rw [hpb, ← pow_succ, Nat.sub_add_cancel A.hT]
      have := (ZMod.natCast_eq_natCast_iff' (p ^ T) 1 (b + L)).2
        (by rw [hT]; exact (Nat.mod_eq_of_lt hn).symm)
      push_cast at this
      exact this
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hZ
    rwa [Nat.mod_eq_of_lt hn] at this
  · obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [Dh_succ, one_mul, Nat.add_mod_left]
    have := Dn_bounds (b := b) (L := L) (i + 1) hi
    exact Nat.mod_eq_of_lt (by omega)

theorem mk_coprime (i : ℕ) (hi : i ≤ L) : Nat.Coprime (Dh b i) (Dn b L i) := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [Dh0, Dn0]; exact A.hcop
  · obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [Dh_succ]
    exact (Nat.coprime_self_add_left.2 (Nat.coprime_one_left _))

theorem mk_key (i : ℕ) (hi : i ≤ L) :
    p * (mk p b L f T).al i * Dn b L i + 1
      = (mk p b L f T).ap i * Dh b i + (mk p b L f T).dj i * (Dh b i * Dn b L i) := by
  have hb := A.hb
  have hpe := A.hp
  have hD := Dh_pos (b := b) (by omega) i
  have hn := Dn_pos (b := b) (by omega) L i
  have hdep := mk_dep A i hi
  have hland := mk_land A i hi
  have hal := mk_al_lt A i hi
  have hap := mk_ap_lt A i hi
  have hDp := Dh_lt_p (b := b) (L := L) (by omega) hpe hi
  have hal1 : 1 ≤ (mk p b L f T).al i := by
    by_contra hc
    have : (mk p b L f T).al i = 0 := by omega
    rw [this] at hdep
    simp at hdep
    have := Dh_bounds (b := b) (L := L) i hi; omega
  have hle : (mk p b L f T).ap i * Dh b i ≤ p * (mk p b L f T).al i * Dn b L i + 1 := by
    have h1 : (mk p b L f T).ap i * Dh b i ≤ Dn b L i * Dh b i := Nat.mul_le_mul_right _ hap.le
    have h2 : Dn b L i * Dh b i ≤ Dn b L i * p := Nat.mul_le_mul_left _ hDp.le
    have h3 : Dn b L i * p ≤ Dn b L i * (p * (mk p b L f T).al i) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hal1)
    have h4 : Dn b L i * (p * (mk p b L f T).al i) = p * (mk p b L f T).al i * Dn b L i := by ring
    omega
  exact key_of_congr hD hn (mk_coprime A i hi) hdep hland hle

theorem mk_dj_lt (i : ℕ) (hi : i ≤ L) : (mk p b L f T).dj i < p := by
  have hb := A.hb
  have hpe := A.hp
  have hD := Dh_pos (b := b) (by omega) i
  have hn := Dn_pos (b := b) (by omega) L i
  have hal := mk_al_lt A i hi
  show djF p b L f T i < p
  unfold djF
  rw [Nat.div_lt_iff_lt_mul (Nat.mul_pos hD hn)]
  have h1 : p * alF p b f T i * Dn b L i + 1 ≤ p * (Dh b i - 1) * Dn b L i + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by
      show (mk p b L f T).al i ≤ Dh b i - 1; omega))) 1
  have h2 : p * (Dh b i - 1) * Dn b L i + p * Dn b L i = p * Dh b i * Dn b L i := by
    obtain ⟨d, hd⟩ : ∃ d, Dh b i = d + 1 := ⟨Dh b i - 1, by omega⟩
    rw [hd, Nat.add_sub_cancel]; ring
  have h3 : 2 ≤ p * Dn b L i := by nlinarith
  have h4 : p * (Dh b i * Dn b L i) = p * Dh b i * Dn b L i := by ring
  omega

/-- **The constructed data satisfies `Hyp`.** -/
theorem mk_hyp : Hyp p b L (mk p b L f T) where
  hb := A.hb
  hL := A.hL
  hp := A.hp
  al_lt := mk_al_lt A
  cj_lt := mk_cj_lt A
  ap_lt := mk_ap_lt A
  dj_lt := mk_dj_lt A
  inj := mk_inj A
  key := mk_key A

end arith

/-! ### Edge steps of the certificate -/

section steps

variable (A : Arith p b L f T)
include A

omit A in
theorem far_congr {i a a' : ℕ} (hi : i ≤ L) (h : a % Dh b i = a' % Dh b i) :
    far p b L i a = far p b L i a' := by
  have hmod : i % (L + 1) = i := Nat.mod_eq_of_lt (by omega)
  unfold far; congr 1; rw [hmod, h]

omit A in
theorem far_mod {i a : ℕ} (hi : i ≤ L) : far p b L i (a % Dh b i) = far p b L i a :=
  far_congr hi (Nat.mod_mod _ _)

/-- A far step: `F_j(p^e) → F_j(p^{e+1})`. -/
theorem far_step {j e : ℕ} (hj : j ≤ L) :
    far p b L j (p ^ (e + 1)) ∈ nxt (mk p b L f T) (far p b L j (p ^ e)) := by
  have hb := A.hb
  have hpe := A.hp
  unfold nxt
  rw [if_pos (by rw [ix_far hb hpe hj]; exact hj), ix_far hb hpe hj, rs_far hb hpe hj]
  simp only [List.singleton_append, List.mem_cons]
  left
  apply far_congr hj
  rw [pow_succ, Nat.mod_mod, Nat.mod_mul_mod]

/-- An injection: `F_j(p^e) → J_j` when `p^e ≡ cj j`. -/
theorem inj_step {j e : ℕ} (hj : j ≤ L) (hcj : p ^ e % Dh b j = (mk p b L f T).cj j) :
    jn p b L j ∈ nxt (mk p b L f T) (far p b L j (p ^ e)) := by
  have hb := A.hb
  have hpe := A.hp
  unfold nxt
  rw [if_pos (by rw [ix_far hb hpe hj]; exact hj), ix_far hb hpe hj, rs_far hb hpe hj,
    Nat.mod_mod, if_pos hcj]
  simp

/-- A landing: `J_j → F_{nx j}(ap j)`. -/
theorem jn_step {j : ℕ} (hj : j ≤ L) :
    far p b L (nx L j) ((mk p b L f T).ap j) ∈ nxt (mk p b L f T) (jn p b L j) := by
  have hb := A.hb
  have hpe := A.hp
  unfold nxt
  rw [if_neg (by rw [ix_jn hb hpe hj]; omega), rs_jn hb hpe hj]
  simp

theorem cj_run {j : ℕ} (hj : j ≤ L) (h0 : j ≠ 0) :
    p ^ (2 * T - 2) % Dh b j = (mk p b L f T).cj j := by
  show _ = cjF p b f T j
  unfold cjF; rw [if_neg h0]

theorem cj_zero : p ^ (3 * f - 3 + T) % Dh b 0 = (mk p b L f T).cj 0 := by
  show _ = cjF p b f T 0
  unfold cjF; rw [if_pos rfl, Dh0]

theorem ap_run {j : ℕ} (h0 : j ≠ 0) : (mk p b L f T).ap j = 1 := by
  show apF p b L T j = 1
  unfold apF; rw [if_neg h0]

theorem ap_zero : (mk p b L f T).ap 0 = p ^ (T - 1) % Dh b L := by
  show apF p b L T 0 = _
  unfold apF; rw [if_pos rfl]; rfl

omit A in
theorem nx_run {j : ℕ} (h0 : j ≠ 0) : nx L j = j - 1 := by unfold nx; rw [if_neg h0]

omit A in
theorem nx_zero : nx L 0 = L := by unfold nx; rw [if_pos rfl]

/-- `F_L(p^T) = F_L(1)`. -/
theorem far_pow_T (j : ℕ) (hj : j ≤ L) : far p b L j (p ^ T) = far p b L j 1 := by
  apply far_congr hj
  rw [A.hT1 j hj]
  exact (Nat.mod_eq_of_lt (by have := Dh_bounds (b := b) (L := L) j hj; have := A.hb; omega)).symm

end steps

/-! ### The walks -/

section walks

variable (p b L f T)

/-- A block: `F_j(p^{e₀}), …, F_j(p^{e₀+len}), J_j`. -/
def blk (j e₀ len r : ℕ) : Fin (S p b L) :=
  if r ≤ len then far p b L j (p ^ (e₀ + r)) else jn p b L j

/-- Length of the closing segment in background `b`. -/
def t₀ : ℕ := 3 * f - 3 + T

/-- Period of walk A. -/
def PA : ℕ := T + 1 + (L - 1) * (2 * T) + (t₀ f T + 2)

/-- Walk A: block `L` (from `p^{T−1}`, `T` far states), the middle blocks `L−1, …, 1`
(each `2T − 1` far states), and block `0` (`t₀ + 1` far states). -/
def walkA (n : ℕ) : Fin (S p b L) :=
  if n ≤ T then blk p b L L (T - 1) (T - 1) n
  else if n < T + 1 + (L - 1) * (2 * T) then
    blk p b L (L - 1 - (n - (T + 1)) / (2 * T)) 0 (2 * T - 2) ((n - (T + 1)) % (2 * T))
  else blk p b L 0 0 (t₀ f T) (n - (T + 1) - (L - 1) * (2 * T))

/-- Walk B: the far cycle in background `L` from `p^{T−1}`, period `T`. -/
def walkB (n : ℕ) : Fin (S p b L) := far p b L L (p ^ (T - 1 + n))

variable {p b L f T}

theorem blk_far {j e₀ len r : ℕ} (hr : r ≤ len) :
    blk p b L j e₀ len r = far p b L j (p ^ (e₀ + r)) := by
  unfold blk; rw [if_pos hr]

theorem blk_jn {j e₀ len r : ℕ} (hr : ¬ r ≤ len) : blk p b L j e₀ len r = jn p b L j := by
  unfold blk; rw [if_neg hr]

theorem walkA_L {n : ℕ} (hn : n ≤ T) : walkA p b L f T n = blk p b L L (T - 1) (T - 1) n := by
  unfold walkA; rw [if_pos hn]

theorem walkA_mid (hT : 0 < T) {k r : ℕ} (hk : k < L - 1) (hr : r < 2 * T) :
    walkA p b L f T (T + 1 + k * (2 * T) + r) = blk p b L (L - 1 - k) 0 (2 * T - 2) r := by
  have h2T : 0 < 2 * T := by omega
  have hlt : T + 1 + k * (2 * T) + r < T + 1 + (L - 1) * (2 * T) := by
    have : (k + 1) * (2 * T) ≤ (L - 1) * (2 * T) := Nat.mul_le_mul_right _ hk
    rw [Nat.add_mul, one_mul] at this
    omega
  unfold walkA
  rw [if_neg (by omega), if_pos hlt, show T + 1 + k * (2 * T) + r - (T + 1) = k * (2 * T) + r by omega,
    (dm h2T hr).1, (dm h2T hr).2]

theorem walkA_zero' {m : ℕ} :
    walkA p b L f T (T + 1 + (L - 1) * (2 * T) + m) = blk p b L 0 0 (t₀ f T) m := by
  unfold walkA
  rw [if_neg (by omega), if_neg (by omega),
    show T + 1 + (L - 1) * (2 * T) + m - (T + 1) - (L - 1) * (2 * T) = m by omega]

/-- Every position of walk A lies in block `L`, a middle block, or block `0`. -/
theorem pos_cases (hT : 0 < T) (n : ℕ) (hn : n < PA L f T) :
    n ≤ T ∨ (∃ k r, k < L - 1 ∧ r < 2 * T ∧ n = T + 1 + k * (2 * T) + r) ∨
    (∃ m, m ≤ t₀ f T + 1 ∧ n = T + 1 + (L - 1) * (2 * T) + m) := by
  have h2T : 0 < 2 * T := by omega
  rcases Nat.lt_or_ge T n with h | h
  · rcases Nat.lt_or_ge n (T + 1 + (L - 1) * (2 * T)) with h' | h'
    · right; left
      refine ⟨(n - (T + 1)) / (2 * T), (n - (T + 1)) % (2 * T), ?_, Nat.mod_lt _ h2T, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul h2T]; omega
      · have := Nat.div_add_mod' (n - (T + 1)) (2 * T)
        omega
    · right; right
      refine ⟨n - (T + 1) - (L - 1) * (2 * T), ?_, by omega⟩
      unfold PA at hn; omega
  · left; exact h

section closed

variable (A : Arith p b L f T)
include A

theorem walkA_step (n : ℕ) (hn : n + 1 < PA L f T) :
    walkA p b L f T (n + 1) ∈ nxt (mk p b L f T) (walkA p b L f T n) := by
  have hb := A.hb
  have hL := A.hL
  have hT := A.hT
  have hT0 : 0 < T := hT
  rcases pos_cases (L := L) (f := f) hT0 n (by omega) with h | ⟨k, r, hk, hr, rfl⟩ | ⟨m, hm, rfl⟩
  · -- block `L`
    rcases Nat.lt_or_ge (n + 1) T with h1 | h1
    · rw [walkA_L h, walkA_L h1.le, blk_far (by omega), blk_far (by omega),
        show T - 1 + (n + 1) = (T - 1 + n) + 1 by omega]
      exact far_step A le_rfl
    · rcases Nat.lt_or_ge n T with h2 | h2
      · have hnT : n + 1 = T := by omega
        rw [walkA_L h, walkA_L (n := n + 1) (by omega), blk_far (by omega), blk_jn (by omega)]
        apply inj_step A le_rfl
        rw [show T - 1 + n = 2 * T - 2 by omega]
        exact cj_run A le_rfl (by omega)
      have hnT : n = T := by omega
      rw [hnT, walkA_L le_rfl, blk_jn (by omega)]
      have hstart : walkA p b L f T (T + 1) = far p b L (L - 1) (p ^ 0) := by
        rcases Nat.lt_or_ge 1 L with hL2 | hL2
        · have := walkA_mid (p := p) (b := b) (f := f) (L := L) (T := T) hT0 (k := 0) (r := 0) (by omega) (by omega)
          rw [zero_mul, add_zero, add_zero] at this
          rw [this, blk_far (by omega), Nat.sub_zero]
        · have hL1 : L = 1 := by omega
          have := walkA_zero' (p := p) (b := b) (f := f) (T := T) (L := L) (m := 0)
          rw [hL1, Nat.sub_self, zero_mul, add_zero, add_zero] at this
          rw [hL1, this, blk_far (by omega), Nat.sub_self]
      rw [hstart, pow_zero]
      have := jn_step A (j := L) le_rfl
      rw [ap_run A (by omega), nx_run (by omega)] at this
      exact this
  · -- a middle block, background `j = L − 1 − k ≥ 1`
    have hj : L - 1 - k ≤ L := by omega
    have hj0 : L - 1 - k ≠ 0 := by omega
    rcases Nat.lt_or_ge (r + 1) (2 * T) with h1 | h1
    · rw [walkA_mid hT0 hk hr, show T + 1 + k * (2 * T) + r + 1 = T + 1 + k * (2 * T) + (r + 1) by omega,
        walkA_mid hT0 hk h1]
      rcases Nat.lt_or_ge (r + 1) (2 * T - 1) with h2 | h2
      · rw [blk_far (by omega), blk_far (by omega), zero_add, zero_add]
        exact far_step A hj
      · rw [blk_far (by omega), blk_jn (by omega), zero_add]
        apply inj_step A hj
        rw [show r = 2 * T - 2 by omega]
        exact cj_run A hj hj0
    · have hr' : r = 2 * T - 1 := by omega
      subst hr'
      rw [walkA_mid hT0 hk hr, blk_jn (by omega)]
      have hnext : walkA p b L f T (T + 1 + k * (2 * T) + (2 * T - 1) + 1)
          = far p b L (L - 1 - k - 1) (p ^ 0) := by
        have e : T + 1 + k * (2 * T) + (2 * T - 1) + 1 = T + 1 + (k + 1) * (2 * T) + 0 := by
          rw [Nat.add_mul, one_mul]; omega
        rw [e]
        rcases Nat.lt_or_ge (k + 1) (L - 1) with h3 | h3
        · rw [walkA_mid hT0 h3 (by omega), blk_far (by omega)]
          congr 1 <;> omega
        · have hk1 : k + 1 = L - 1 := by omega
          rw [hk1, walkA_zero', blk_far (by omega)]
          congr 1 <;> omega
      rw [hnext, pow_zero]
      have := jn_step A hj
      rw [ap_run A hj0, nx_run hj0] at this
      exact this
  · -- block `0`
    have hlt : m + 1 ≤ t₀ f T + 1 := by unfold PA at hn; omega
    rw [walkA_zero', show T + 1 + (L - 1) * (2 * T) + m + 1 = T + 1 + (L - 1) * (2 * T) + (m + 1) by omega,
      walkA_zero']
    rcases Nat.lt_or_ge (m + 1) (t₀ f T + 1) with h2 | h2
    · rw [blk_far (by omega), blk_far (by omega), zero_add, zero_add]
      exact far_step A (by omega)
    · rw [blk_far (by omega), blk_jn (by omega), zero_add]
      apply inj_step A (by omega)
      rw [show m = t₀ f T by omega]
      exact cj_zero A

omit A in
theorem walkA_start : walkA p b L f T 0 = far p b L L (p ^ (T - 1)) := by
  rw [walkA_L (Nat.zero_le _), blk_far (Nat.zero_le _), add_zero]

theorem walkA_closed :
    far p b L L (p ^ (T - 1)) ∈ nxt (mk p b L f T) (walkA p b L f T (PA L f T - 1)) := by
  have e : PA L f T - 1 = T + 1 + (L - 1) * (2 * T) + (t₀ f T + 1) := by unfold PA; omega
  rw [e, walkA_zero', blk_jn (by omega)]
  have := jn_step A (j := 0) (Nat.zero_le _)
  rw [nx_zero, ap_zero A, far_mod le_rfl] at this
  exact this

theorem walkB_step (n : ℕ) (hn : n + 1 < T) :
    walkB p b L T (n + 1) ∈ nxt (mk p b L f T) (walkB p b L T n) := by
  unfold walkB
  rw [show T - 1 + (n + 1) = (T - 1 + n) + 1 by omega]
  exact far_step A le_rfl

theorem walkB_closed :
    far p b L L (p ^ (T - 1)) ∈ nxt (mk p b L f T) (walkB p b L T (T - 1)) := by
  have hT := A.hT
  unfold walkB
  have := far_step A (j := L) (e := T - 1 + (T - 1)) le_rfl
  have h2 : far p b L L (p ^ (T - 1 + (T - 1) + 1)) = far p b L L (p ^ (T - 1)) := by
    apply far_congr le_rfl
    rw [show T - 1 + (T - 1) + 1 = (T - 1) + T by omega, pow_add, Nat.mul_mod, A.hT1 L le_rfl,
      mul_one, Nat.mod_mod]
  rw [h2] at this
  exact this

end closed

end walks

/-! ### The witness pair -/

section witness

variable (A : Arith p b L f T)
include A

/-- A far→far edge is never `hi`-extremal: the width shrinks by `p`. -/
theorem not_hiMax_far {j e : ℕ} (hj : j ≤ L) :
    ¬ (cert (mk p b L f T)).HiMax (far p b L j (p ^ e)) (far p b L j (p ^ (e + 1))) := by
  have hb := A.hb
  have hpe := A.hp
  have hp0 : 0 < p := by omega
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp0
  intro hmax
  unfold EscapeCert.HiMax at hmax
  simp only [cert] at hmax
  have hs : ix (far p b L j (p ^ e)) ≤ L := by rw [ix_far hb hpe hj]; exact hj
  have hs' : ix (far p b L j (p ^ (e + 1))) ≤ L := by rw [ix_far hb hpe hj]; exact hj
  rw [hip_eq, hip_eq, lop_eq, lop_eq, wd_far hs, wd_far hs', En_far hs, En_far hs', Nn_far hs,
    Nn_far hs', ix_far hb hpe hj, ix_far hb hpe hj, rs_far hb hpe hj, rs_far hb hpe hj, dig_far hs,
    ix_far hb hpe hj, rs_far hb hpe hj] at hmax
  simp only [Nat.mod_mod] at hmax
  set D := Dh b j
  set r := p ^ e % D
  have hD : 0 < D := Dh_pos (by omega) j
  have hDQ : (0 : ℚ) < D := by exact_mod_cast hD
  have hw : (0 : ℚ) < wid p b L j := by
    unfold wid
    have : (0 : ℚ) < Dn b L j := by exact_mod_cast Dn_pos (show 0 < b by omega) L j
    positivity
  -- the far edge is exact on the left
  have hexact : ((r * p / D : ℕ) : ℚ) + ((p ^ (e + 1) % D : ℕ) : ℚ) / D = p * ((r : ℚ) / D) := by
    have hdm := Nat.div_add_mod (r * p) D
    have hmod : p ^ (e + 1) % D = r * p % D := by
      rw [pow_succ, Nat.mod_mul_mod]
    rw [hmod]
    field_simp
    have := congrArg (fun x : ℕ => (x : ℚ)) hdm
    push_cast at this
    linear_combination this
  rw [← add_assoc, hexact] at hmax
  have : (p : ℚ) * ((r : ℚ) / D) + wid p b L j = p * ((r : ℚ) / D + wid p b L j) := by
    rw [div_eq_iff hpQ.ne'] at hmax; linarith
  have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast (show 2 ≤ p by omega)
  nlinarith

/-- `dig F_j(1) = ⌊p / Dh j⌋`. -/
theorem dig_far_one {j : ℕ} (hj : j ≤ L) :
    dig (mk p b L f T) (far p b L j 1) = p / Dh b j := by
  have hb := A.hb
  have hpe := A.hp
  have hs : ix (far p b L j 1) ≤ L := by rw [ix_far hb hpe hj]; exact hj
  rw [dig_far hs, ix_far hb hpe hj, rs_far hb hpe hj]
  have hD := Dh_bounds (b := b) (L := L) j hj
  rw [Nat.mod_eq_of_lt (show 1 < Dh b j by omega), Nat.mod_eq_of_lt (show 1 < Dh b j by omega),
    one_mul]

theorem dig_top : dig (mk p b L f T) (far p b L L 1) = 1 := by
  have hb := A.hb
  have hpe := A.hp
  have hL := A.hL
  rw [dig_far_one A le_rfl, show Dh b L = b + L from rfl]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

theorem dig_bot : 2 ≤ dig (mk p b L f T) (far p b L 0 1) := by
  have hb := A.hb
  have hpe := A.hp
  rw [dig_far_one A (Nat.zero_le _), Dh0, Nat.le_div_iff_mul_le (by omega)]
  omega

theorem T_two (hT2 : 2 ≤ T) : walkA p b L f T 1 = far p b L L 1 := by
  rw [walkA_L (by omega), blk_far (by omega), show T - 1 + 1 = T by omega, far_pow_T A L le_rfl]

theorem walkB_one (hT2 : 2 ≤ T) : walkB p b L T (1 % T) = far p b L L 1 := by
  unfold walkB
  rw [Nat.mod_eq_of_lt (by omega), show T - 1 + 1 = T by omega, far_pow_T A L le_rfl]

omit A in
theorem PA_pos : 0 < PA L f T := by unfold PA; omega

/-- **The witness pair**: walk A and walk B, common length `PA · T`, from `F_L(p^{T−1})`. -/
theorem witness (hT2 : 2 ≤ T) (Lc : ℕ) (hLc : Lc = PA L f T * T) (hL0 : 0 < Lc) :
    (cert (mk p b L f T)).WitnessPair Lc
      (fun i : Fin Lc => walkA p b L f T (i.1 % PA L f T))
      (fun i : Fin Lc => walkB p b L T (i.1 % T)) hL0 (far p b L L (p ^ (T - 1))) := by
  have hb := A.hb
  have hpe := A.hp
  have hL := A.hL
  have hT := A.hT
  have hPA := PA_pos (L := L) (f := f) (T := T)
  have hPA2 : T + 1 + (L - 1) * (2 * T) < PA L f T := by unfold PA; omega
  have hLc2 : PA L f T ≤ Lc := by rw [hLc]; exact Nat.le_mul_of_pos_right _ (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact EscapeCert.isClosedWalk_periodic (C := cert (mk p b L f T)) (walkA p b L f T) (PA L f T)
      hPA _ (walkA_start) (walkA_step A) (walkA_closed A) Lc T (by rw [hLc, mul_comm]) (by omega) hL0
  · exact EscapeCert.isClosedWalk_periodic (C := cert (mk p b L f T)) (walkB p b L T) T
      (by omega) _ (by unfold walkB; rw [add_zero]) (walkB_step A) (walkB_closed A) Lc (PA L f T)
      hLc hPA hL0
  · refine ⟨⟨1, by omega⟩, ?_⟩
    show dig (mk p b L f T) (walkA p b L f T (1 % PA L f T)) ≠ p - 1
    rw [Nat.mod_eq_of_lt (by omega), T_two A hT2, dig_top A]; omega
  · refine ⟨⟨1, by omega⟩, ?_⟩
    show dig (mk p b L f T) (walkB p b L T (1 % T)) ≠ p - 1
    rw [walkB_one A hT2, dig_top A]; omega
  · refine ⟨⟨0, by omega⟩, show 0 + 1 < Lc by omega, ?_⟩
    show ¬ (cert (mk p b L f T)).HiMax (walkA p b L f T (0 % PA L f T))
      (walkA p b L f T ((0 + 1) % PA L f T))
    rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega), walkA_start, walkA_L (by omega),
      blk_far (by omega), zero_add]
    exact not_hiMax_far A le_rfl
  · refine ⟨⟨0, by omega⟩, show 0 + 1 < Lc by omega, ?_⟩
    show ¬ (cert (mk p b L f T)).HiMax (walkB p b L T (0 % T)) (walkB p b L T ((0 + 1) % T))
    rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)]
    unfold walkB
    rw [add_zero]
    exact not_hiMax_far A le_rfl
  · refine ⟨⟨T + 1 + (L - 1) * (2 * T), by omega⟩, ?_⟩
    show dig (mk p b L f T) (walkA p b L f T ((T + 1 + (L - 1) * (2 * T)) % PA L f T))
      ≠ dig (mk p b L f T) (walkB p b L T ((T + 1 + (L - 1) * (2 * T)) % T))
    have e1 : (T + 1 + (L - 1) * (2 * T)) % T = 1 % T := by
      rw [show T + 1 + (L - 1) * (2 * T) = 1 + T * (1 + (L - 1) * 2) by ring,
        Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt hPA2, e1, walkB_one A hT2, dig_top A]
    have := walkA_zero' (p := p) (b := b) (f := f) (T := T) (L := L) (m := 0)
    rw [add_zero] at this
    rw [this, blk_far (Nat.zero_le _), add_zero, pow_zero]
    have := dig_bot A
    omega

end witness

/-! ### The theorem -/

/-- The arithmetic hypotheses from primality: `T = 2 φ((p−b)!)`. -/
theorem arith_of_prime (p b f : ℕ) (hp : p.Prime) (hb : 3 ≤ b) (h2b : 2 * b < p)
    (hf : 1 ≤ f) (hpow : p ^ f % b = b - 1) :
    Arith p b (p - 2 * b) f (2 * Nat.totient ((p - b).factorial)) := by
  have hcopf : Nat.Coprime p (p - b).factorial :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (by rw [Nat.Prime.dvd_factorial hp]; omega)
  have hφ : 0 < Nat.totient ((p - b).factorial) := Nat.totient_pos.2 (Nat.factorial_pos _)
  refine ⟨hb, by omega, by omega, hf, hpow, by omega, ?_, ?_⟩
  · intro j hj
    have hD : Dh b j ∣ (p - b).factorial := Nat.dvd_factorial (Dh_pos (by omega) j) (by unfold Dh; omega)
    have h1 : p ^ (2 * Nat.totient ((p - b).factorial)) ≡ 1 [MOD Dh b j] := by
      have := (Nat.ModEq.pow_totient hcopf).of_dvd hD
      rw [pow_mul']
      simpa using this.pow 2
    unfold Nat.ModEq at h1
    rw [h1]
    exact Nat.mod_eq_of_lt (by unfold Dh; omega)
  · rw [Nat.coprime_self_add_right]
    have : Nat.Coprime b p := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 (by
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega))))
    have e : p = (p - 2 * b) + 2 * b := by omega
    rw [e, Nat.coprime_add_mul_right_right] at this
    exact this

/-- **The run+jump theorem.**  For every prime `p`, every `3 ≤ b < p/2` with
`−1 ∈ ⟨p⟩ (mod b)` (`p^f ≡ −1`, `f ≥ 1`), every channel `m ≤ b(p − b − 1) − 1` is
digit-`(p−1)`-free for a common irrational: `M(p,1) > b(p − b − 1) − 1`. -/
theorem mahler_lower_bound_runjump (p b f : ℕ) (hp : p.Prime) (hb : 3 ≤ b) (h2b : 2 * b < p)
    (hf : 1 ≤ f) (hpow : p ^ f % b = b - 1) :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ b * (p - b - 1) - 1 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt p ((m : ℝ) * α) [p - 1] n := by
  have A := arith_of_prime p b f hp hb h2b hf hpow
  set L := p - 2 * b with hL
  set T := 2 * Nat.totient ((p - b).factorial) with hT
  have hφ : 0 < Nat.totient ((p - b).factorial) := Nat.totient_pos.2 (Nat.factorial_pos _)
  have hT2 : 2 ≤ T := by omega
  have hMlt : b * (p - b - 1) - 1 < b * (b + L - 1) := by
    have : p - b - 1 = b + L - 1 := by omega
    rw [this]
    have : 1 ≤ b * (b + L - 1) := Nat.mul_pos (by omega) (by omega)
    omega
  have hPA := PA_pos (L := L) (f := f) (T := T)
  have hL0 : 0 < PA L f T * T := Nat.mul_pos hPA (by omega)
  exact (cert (mk p b L f T)).escape_mahler_lower_bound (by omega) _ [p - 1] (valid (mk_hyp A) hMlt)
    _ _ _ hL0 _ (witness A hT2 _ rfl hL0)

/-- `p ≡ −1 (mod b)` is the case `f = 1`. -/
theorem mahler_lower_bound_runjump_of_dvd (p b : ℕ) (hp : p.Prime) (hb : 3 ≤ b) (h2b : 2 * b < p)
    (hdvd : b ∣ p + 1) :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ b * (p - b - 1) - 1 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt p ((m : ℝ) * α) [p - 1] n := by
  refine mahler_lower_bound_runjump p b 1 hp hb h2b le_rfl ?_
  obtain ⟨q, hq⟩ := hdvd
  rw [pow_one, show p = (b - 1) + b * (q - 1) by
    have : 1 ≤ q := by nlinarith
    rw [Nat.mul_sub_one]; omega, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- **`3 ∣ p + 1`**: `b = (p+1)/3` gives `M(p,1) > 2(p+1)(p−2)/9 − 1`  (constant `2/9`). -/
theorem mahler_lower_bound_runjump_three (p : ℕ) (hp : p.Prime) (hp11 : 11 ≤ p)
    (h3 : 3 ∣ p + 1) :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 2 * (p + 1) * (p - 2) / 9 - 1 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt p ((m : ℝ) * α) [p - 1] n := by
  obtain ⟨b, hb⟩ := h3
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have hpc : p = 3 * c + 2 := by omega
  subst hpc
  have e : (c + 1) * (3 * c + 2 - (c + 1) - 1) = 2 * (3 * c + 2 + 1) * (3 * c + 2 - 2) / 9 := by
    rw [show 3 * c + 2 - (c + 1) - 1 = 2 * c by omega, show 3 * c + 2 + 1 = 3 * (c + 1) by ring,
      show 3 * c + 2 - 2 = 3 * c by omega, show 2 * (3 * (c + 1)) * (3 * c) = (2 * c * (c + 1)) * 9 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
    ring
  rw [← e]
  exact mahler_lower_bound_runjump_of_dvd _ (c + 1) hp (by omega) (by omega) ⟨3, by omega⟩

/-- **`4 ∣ p + 1`**: `b = (p+1)/4` gives `M(p,1) > (p+1)(3p−5)/16 − 1`  (constant `3/16`). -/
theorem mahler_lower_bound_runjump_four (p : ℕ) (hp : p.Prime) (hp11 : 11 ≤ p)
    (h4 : 4 ∣ p + 1) :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ (p + 1) * (3 * p - 5) / 16 - 1 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt p ((m : ℝ) * α) [p - 1] n := by
  obtain ⟨b, hb⟩ := h4
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have hpc : p = 4 * c + 3 := by omega
  subst hpc
  have e : (c + 1) * (4 * c + 3 - (c + 1) - 1) = (4 * c + 3 + 1) * (3 * (4 * c + 3) - 5) / 16 := by
    rw [show 4 * c + 3 - (c + 1) - 1 = 3 * c + 1 by omega, show 4 * c + 3 + 1 = 4 * (c + 1) by ring,
      show 3 * (4 * c + 3) - 5 = 4 * (3 * c + 1) by omega,
      show 4 * (c + 1) * (4 * (3 * c + 1)) = ((c + 1) * (3 * c + 1)) * 16 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  rw [← e]
  exact mahler_lower_bound_runjump_of_dvd _ (c + 1) hp (by omega) (by omega) ⟨4, by omega⟩

/-- Numeric anchors against the exact census (`docs/mahler-exact-values-2026-09-07.md`):
`(p, b) = (13, 5)`, `(23, 10)`, `(31, 14)` give `M ≥ 35, 120, 224`, all EXACT. -/
theorem mahler_lower_bound_base13_runjump :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 34 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt 13 ((m : ℝ) * α) [12] n :=
  mahler_lower_bound_runjump 13 5 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem mahler_lower_bound_base31_runjump :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 223 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt 31 ((m : ℝ) * α) [30] n :=
  mahler_lower_bound_runjump 31 14 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The conditional `1/4`** (directive trigger T3): if some `b` within `j` of `p/2`
(`p = 2b + j`) has `−1 ∈ ⟨p⟩ (mod b)`, then `M(p,1) > (p−j)(p+j−2)/4 − 1`.
Measured (`experiments/mahler_runjump_admissible.py`): for every prime `p < 2000` the
best admissible `b` has `j ≤ 33` (`j = 33` only at `p = 853`), so the constant is `1/4 − O(1/p)` there. -/
theorem mahler_lower_bound_runjump_near_half (p b j f : ℕ) (hp : p.Prime) (hb : 3 ≤ b)
    (hj : 1 ≤ j) (hpj : p = 2 * b + j) (hf : 1 ≤ f) (hpow : p ^ f % b = b - 1) :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ (p - j) * (p + j - 2) / 4 - 1 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt p ((m : ℝ) * α) [p - 1] n := by
  have e : b * (p - b - 1) = (p - j) * (p + j - 2) / 4 := by
    subst hpj
    rw [show 2 * b + j - b - 1 = b + j - 1 by omega, show 2 * b + j - j = 2 * b by omega,
      show 2 * b + j + j - 2 = 2 * (b + j - 1) by omega,
      show 2 * b * (2 * (b + j - 1)) = (b * (b + j - 1)) * 4 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  rw [← e]
  exact mahler_lower_bound_runjump p b f hp hb (by omega) hf hpow

end NormalNumbers.Adder.RunJump
