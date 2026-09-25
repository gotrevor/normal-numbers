/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AbelianWindowMulti
import NormalNumbers.AbelianWindowPerturb

/-!
# Item 4: nested layers of gadgets

`AbelianWindowMulti` settles the law of ONE block width `q`: a block carrying any list of
pairwise-disjoint gadgets gives a sequence abelian at exactly the lengths that are not arms
(`multi_isAbelianAt_of_notMem`, `multi_not_isAbelianAt'`), and `c4_realizable_of_finite_compl`
is the finite-complement case.  A single block width can never do better: its exact abelian set
is eventually `q`-periodic.

The way out is to let the block width grow.  The structural fact that makes this work is
`bitw_blockOf` below: the block digit's bits ARE the original sequence's bits, so a gadget placed
at absolute positions `{p, p+1, p+a, p+a+1}` reads and writes only those four bits of the
underlying binary sequence `x` — *independently of the block width `q` used to compute the law*.
Hence the same perturbation of `x` is simultaneously
* a `blockSeq` of width `q_n` (so the engine of `AbelianWindowMulti` computes its law exactly), and
* within density `O(∑_{m>n} 1/Q_m)` of the next stage,
and `AbelianWindowPerturb.tendsto_onesFreq_of_linear_diff` transfers the limits.
-/

open Finset Polynomial

namespace NormalNumbers.Abelian

open NormalNumbers.PowerBase

/-! ## The block digit's bits are the original bits -/

/-- **The bits of a block digit are the bits of the sequence.** -/
theorem bitw_blockOf (q : ℕ) (x : ℕ → ℕ) (hx : ∀ m, x m < 2) (j r : ℕ) (hr : r < q) :
    bitw q (blockOf 2 q x j) r = x (q * j + r) := by
  set w : List ℕ := (List.range q).map (fun t => x (q * j + t)) with hwdef
  have hlen : w.length = q := by rw [hwdef]; simp
  have hlt : ∀ e ∈ w, e < 2 := by
    intro e he
    rw [hwdef, List.mem_map] at he
    obtain ⟨t, -, rfl⟩ := he
    exact hx _
  have hword : wordOf 2 q (valOf 2 w) = w := by
    have := wordOf_valOf (B := 2) (by norm_num) w hlt
    rwa [hlen] at this
  rw [blockOf, ← hwdef, bitw, hword, hwdef, getD_map_range q r _ hr]

/-- Off every gadget's quadruple, the gadget-driven block sequence IS the original sequence. -/
theorem blockSeq_multiG_eq_of_notMem (q : ℕ) (hq0 : 0 < q) (gs : List (ℕ × ℕ)) (x : ℕ → ℕ)
    (hx : ∀ m, x m < 2) (m : ℕ) (h : ∀ pa ∈ gs, m % q ∉ quadSet pa.1 pa.2) :
    blockSeq (multiG q gs) (blockOf 2 q x) q m = x m := by
  rw [blockSeq, multiG_of_notMem q gs (m % q) _ h,
    bitw_blockOf q x hx (m / q) (m % q) (Nat.mod_lt _ hq0)]
  congr 1
  exact Nat.div_add_mod m q

/-! ## The gadget action is intrinsic: independent of the block width -/

/-- The trigger of a gadget at ABSOLUTE position `P` with arm `a`, read off the sequence `x`. -/
def absTrig (x : ℕ → ℕ) (P a : ℕ) : Prop :=
  x P ≠ x (P + 1) ∧ x (P + a) = x (P + 1) ∧ x (P + a + 1) = x P

instance (x : ℕ → ℕ) (P a : ℕ) : Decidable (absTrig x P a) := by unfold absTrig; infer_instance

/-- The value at `m` of `x` with the single gadget at absolute position `P`, arm `a`, applied. -/
def absGad (x : ℕ → ℕ) (P a : ℕ) (m : ℕ) : ℕ :=
  if absTrig x P a then
    (if m = P + a then x (P + a + 1) else if m = P + a + 1 then x (P + a) else x m)
  else x m

/-- **The key `q`-independence lemma.**  On a gadget's quadruple the block sequence's value is the
ABSOLUTE gadget action on `x` — it does not mention the block width at all.  Hence the very same
perturbation of `x` is a `blockSeq` for every width `q` that the layout fits in. -/
theorem blockSeq_multiG_eq_absGad (q : ℕ) (hq0 : 0 < q) (gs : List (ℕ × ℕ)) (hgs : GadSep gs)
    (hnd : gs.Nodup) (x : ℕ → ℕ) (hx : ∀ m, x m < 2) (p a : ℕ) (hpa : (p, a) ∈ gs)
    (hq : p + a + 1 < q) (m : ℕ) (hr : m % q ∈ quadSet p a) :
    blockSeq (multiG q gs) (blockOf 2 q x) q m = absGad x (q * (m / q) + p) a m := by
  set j := m / q with hjdef
  set r := m % q with hrdef
  have hm : q * j + r = m := Nat.div_add_mod m q
  have hrq : r < q := Nat.mod_lt _ hq0
  set P := q * j + p with hPdef
  have hb : ∀ u, u < q → bitw q (blockOf 2 q x j) u = x (q * j + u) :=
    fun u hu => bitw_blockOf q x hx j u hu
  have htrig : gadTrig q p a (blockOf 2 q x j) ↔ absTrig x P a := by
    unfold gadTrig absTrig
    rw [hb p (by omega), hb (p + 1) (by omega), hb (p + a) (by omega), hb (p + a + 1) (by omega),
      show q * j + (p + 1) = P + 1 from by rw [hPdef]; omega,
      show q * j + (p + a) = P + a from by rw [hPdef]; omega,
      show q * j + (p + a + 1) = P + a + 1 from by rw [hPdef]; omega]
  rw [blockSeq, multiG_mem_eq q gs hgs hnd r _ (p, a) hpa hr, gadBit, absGad]
  by_cases ht : absTrig x P a
  · rw [if_pos (htrig.mpr ht), if_pos ht]
    have e1 : (r = p + a) ↔ (m = P + a) := by rw [hPdef]; omega
    have e2 : (r = p + a + 1) ↔ (m = P + a + 1) := by rw [hPdef]; omega
    by_cases h1 : r = p + a
    · rw [if_pos h1, if_pos (e1.mp h1), hb (p + a + 1) (by omega),
        show q * j + (p + a + 1) = P + a + 1 from by rw [hPdef]; omega]
    · rw [if_neg h1, if_neg (fun hc => h1 (e1.mpr hc))]
      by_cases h2 : r = p + a + 1
      · rw [if_pos h2, if_pos (e2.mp h2), hb (p + a) (by omega),
          show q * j + (p + a) = P + a from by rw [hPdef]; omega]
      · rw [if_neg h2, if_neg (fun hc => h2 (e2.mpr hc)), hb r hrq, hm]
  · rw [if_neg (fun hc => ht (htrig.mp hc)), if_neg ht, hb r hrq, hm]

/-! ## The offset pigeonhole

Layer `n` occupies exactly FOUR residues modulo its period `Q_n` (the quadruple
`{o_n, o_n+1, o_n+a_n, o_n+a_n+1}`), hence exactly four residues modulo every divisor of `Q_n`.
So keeping layer `n` disjoint from layers `m < n` forbids at most `16` residue classes modulo
each `Q_m`, i.e. at most `16 * (Q_n / Q_m)` values of `o_n` in `range Q_n`.  With periods growing
at least geometrically from `Q_1 ≥ 64` the total is `< Q_n`, so a good offset always exists.
-/

/-- A residue class modulo a divisor `d` of `Q` meets `range Q` in at most `Q / d` points. -/
theorem card_filter_mod_le (Q d c : ℕ) (hd : 0 < d) (hdvd : d ∣ Q) :
    ((range Q).filter (fun o => o % d = c)).card ≤ Q / d := by
  classical
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simp
  have hQd : (Q - 1) / d + 1 = Q / d := by
    obtain ⟨k, rfl⟩ := hdvd
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at hQ
      · exact hk
    rw [Nat.mul_div_cancel_left _ hd]
    obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
    have hmul : d * (t + 1) = d * t + d := by ring
    have h1 : d * (t + 1) - 1 = d * t + (d - 1) := by omega
    rw [h1, Nat.mul_add_div hd, Nat.div_eq_of_lt (by omega)]
  rw [← Finset.card_range (Q / d)]
  refine Finset.card_le_card_of_injOn (fun o => o / d) (fun o ho => ?_) (fun o ho o' ho' he => ?_)
  · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ho
    obtain ⟨ho1, ho2⟩ := ho
    simp only [Finset.mem_coe, Finset.mem_range]
    rw [← hQd]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (show o ≤ Q - 1 by omega))
  · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ho ho'
    have h1 : d * (o / d) + o % d = o := Nat.div_add_mod o d
    have h2 : d * (o' / d) + o' % d = o' := Nat.div_add_mod o' d
    rw [ho.2] at h1
    rw [ho'.2] at h2
    simp only at he
    rw [← h1, ← h2, he]

/-- **The offset pigeonhole.**  If the forbidden residue classes are few, a good offset exists. -/
theorem exists_avoiding_offset (N Q : ℕ) (hQ : 0 < Q) (d : ℕ → ℕ) (S : ℕ → Finset ℕ)
    (hd : ∀ m < N, 0 < d m ∧ d m ∣ Q)
    (hsum : ∑ m ∈ range N, (S m).card * (Q / d m) < Q) :
    ∃ o, o < Q ∧ ∀ m < N, o % d m ∉ S m := by
  classical
  set B := (range Q).filter (fun o => ∃ m ∈ range N, o % d m ∈ S m) with hBdef
  have hcov : B ⊆ (range N).biUnion
      (fun m => (S m).biUnion (fun c => (range Q).filter (fun o => o % d m = c))) := by
    intro o ho
    rw [hBdef, Finset.mem_filter] at ho
    obtain ⟨hoQ, m, hm, hmem⟩ := ho
    exact Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_biUnion.mpr
      ⟨o % d m, hmem, Finset.mem_filter.mpr ⟨hoQ, rfl⟩⟩⟩
  have hcard : B.card < Q := by
    refine lt_of_le_of_lt (le_trans (Finset.card_le_card hcov) ?_) hsum
    refine le_trans (Finset.card_biUnion_le) (Finset.sum_le_sum (fun m hm => ?_))
    obtain ⟨hdm, hdvd⟩ := hd m (Finset.mem_range.mp hm)
    refine le_trans (Finset.card_biUnion_le) ?_
    refine le_trans (Finset.sum_le_sum (fun c _ => card_filter_mod_le Q (d m) c hdm hdvd)) ?_
    rw [Finset.sum_const, smul_eq_mul]
  have hns : ¬ (range Q ⊆ B) := by
    intro hs
    have := Finset.card_le_card hs
    rw [Finset.card_range] at this
    omega
  obtain ⟨o, hoQ, hoB⟩ := Finset.not_subset.mp hns
  refine ⟨o, Finset.mem_range.mp hoQ, fun m hm hmem => ?_⟩
  exact hoB (by
    rw [hBdef, Finset.mem_filter]
    exact ⟨hoQ, m, Finset.mem_range.mpr hm, hmem⟩)

/-! ## The exact window law of a stage

`multi_not_isAbelianAt'` only needs an inequality, but the limit transfer
(`tendsto_onesFreq_of_linear_diff`) needs every stage to attain the SAME value `v`.  So for the
excluded lengths we need the stage law exactly, not just a bound.  The computation is:
the constant term of the window polynomial at a residue `r` is `(3/4)^{k(r)}` times the Binomial
value, where `k(r)` counts the blocks whose trace separates a gadget of arm `L`.
-/

/-- **The exact constant term** of a window polynomial, given the set of defective blocks. -/
theorem winGf_coeff_eq (q : ℕ) (hq0 : 0 < q) (gs : List (ℕ × ℕ))
    (hok : ∀ pa ∈ gs, GadOk q pa) (hgs : GadSep gs) (hnd : gs.Nodup) (S L r : ℕ)
    (hS : ∀ t < L, (r + t) / q < S) (D : Finset ℕ) (hD : D ⊆ range S)
    (hdef : ∀ b ∈ D, (∑ d ∈ range (2 ^ q), (X : ℝ[X]) ^ segOnes (multiG q gs) q L r b d).coeff 0
      = 3 / 4 * ((2 : ℝ) ^ q / 2 ^ segLen q L r b))
    (hcln : ∀ b ∈ (range S) \ D,
      (∑ d ∈ range (2 ^ q), (X : ℝ[X]) ^ segOnes (multiG q gs) q L r b d).coeff 0
        = (2 : ℝ) ^ q / 2 ^ segLen q L r b) :
    (winGf (multiG q gs) q (2 ^ q) S L r).coeff 0
      = (3 / 4) ^ D.card * (((2 ^ q : ℕ) : ℝ) ^ S / 2 ^ L) := by
  classical
  have hB0 : 0 < 2 ^ q := by positivity
  have hcast : ((2 ^ q : ℕ) : ℝ) = (2 : ℝ) ^ q := by push_cast; ring
  have hcoeff : (winGf (multiG q gs) q (2 ^ q) S L r).coeff 0
      = ∏ b ∈ range S,
        (∑ d ∈ range (2 ^ q), (X : ℝ[X]) ^ segOnes (multiG q gs) q L r b d).coeff 0 := by
    rw [winGf_eq_prod (multiG q gs) hB0 q S L r hS, ← Polynomial.constantCoeff_apply, map_prod]
    rfl
  have hprodv : ∏ b ∈ range S, ((2 : ℝ) ^ q / 2 ^ segLen q L r b)
      = ((2 ^ q : ℕ) : ℝ) ^ S / 2 ^ L := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range,
      Finset.prod_pow_eq_pow_sum, segLen_sum q L r S hS, hcast]
  rw [hcoeff, ← Finset.prod_sdiff hD, Finset.prod_congr rfl hdef,
    Finset.prod_congr rfl hcln, Finset.prod_mul_distrib, Finset.prod_const,
    ← hprodv, ← Finset.prod_sdiff hD]
  ring

/-! ## The layer system -/

/-- The data of a nested layer system.  Layer `n` puts an `arm n`-gadget at every position
`≡ off n (mod Q n)`.  The periods are nested and grow geometrically; `hbig` (the offset is at
least half the period) is what makes the tail density bound `O(M / Q m)` instead of `O(M / Q m)
+ 1` per layer, and `hdisj` is the conclusion of `exists_avoiding_offset`. -/
structure LayerSys where
  Q : ℕ → ℕ
  off : ℕ → ℕ
  arm : ℕ → ℕ
  hQ64 : 64 ≤ Q 0
  hQdouble : ∀ n, 2 * Q n ≤ Q (n + 1)
  hQdvd : ∀ n, Q n ∣ Q (n + 1)
  harm : ∀ n, 2 ≤ arm n
  hfit : ∀ n, off n + arm n + 1 < Q n
  hbig : ∀ n, Q n ≤ 2 * off n
  hdisj : ∀ m n, m < n → ∀ δ ∈ ({0, 1, arm m, arm m + 1} : Finset ℕ),
            ∀ δ' ∈ ({0, 1, arm n, arm n + 1} : Finset ℕ),
            (off n + δ') % Q m ≠ (off m + δ) % Q m

namespace LayerSys

variable (Ls : LayerSys)

theorem Qpos (n : ℕ) : 0 < Ls.Q n := by
  induction n with
  | zero => have := Ls.hQ64; omega
  | succ n ih => have := Ls.hQdouble n; omega

theorem dvd_of_le {m n : ℕ} (h : m ≤ n) : Ls.Q m ∣ Ls.Q n := by
  induction n with
  | zero => rw [Nat.le_zero] at h; rw [h]
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with h1 | h1
      · exact dvd_trans (ih (by omega)) (Ls.hQdvd n)
      · rw [show m = n + 1 from by omega]

/-- The gadgets of layer `m` inside one block of width `Ls.Q n`. -/
def layerRow (m N : ℕ) : List (ℕ × ℕ) :=
  (List.range N).map (fun k => (k * Ls.Q m + Ls.off m, Ls.arm m))

/-- All gadgets of layers `0..n`, inside one block of width `Ls.Q n`. -/
def layerGads (n : ℕ) : List (ℕ × ℕ) :=
  (List.range (n + 1)).flatMap (fun m => Ls.layerRow m (Ls.Q n / Ls.Q m))

theorem mem_layerGads {n : ℕ} {x : ℕ × ℕ} : x ∈ Ls.layerGads n ↔
    ∃ m, m ≤ n ∧ ∃ k, k < Ls.Q n / Ls.Q m ∧ x = (k * Ls.Q m + Ls.off m, Ls.arm m) := by
  simp only [layerGads, layerRow, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · intro ⟨m, hm, k, hk, hxk⟩
    exact ⟨m, by omega, k, hk, hxk.symm⟩
  · intro ⟨m, hm, k, hk, hxk⟩
    exact ⟨m, by omega, k, hk, hxk.symm⟩

theorem layerGads_ok (n : ℕ) : ∀ x ∈ Ls.layerGads n, GadOk (Ls.Q n) x := by
  intro x hx
  rw [Ls.mem_layerGads] at hx
  obtain ⟨m, hm, k, hk, rfl⟩ := hx
  refine ⟨Ls.harm m, ?_⟩
  simp only
  -- `k * Q m + off m + arm m + 1 < Q n` because `k + 1 ≤ Q n / Q m` and `off m + arm m + 1 < Q m`
  have hQm := Ls.Qpos m
  have hfit := Ls.hfit m
  have hdvd : Ls.Q m ∣ Ls.Q n := Ls.dvd_of_le hm
  obtain ⟨t, ht⟩ := hdvd
  have hkt : k < t := by rwa [ht, Nat.mul_div_cancel_left _ hQm] at hk
  calc k * Ls.Q m + Ls.off m + Ls.arm m + 1 < k * Ls.Q m + Ls.Q m := by omega
    _ = (k + 1) * Ls.Q m := by ring
    _ ≤ t * Ls.Q m := Nat.mul_le_mul_right _ (by omega)
    _ = Ls.Q n := by rw [ht]; ring

/-- A convenient sufficient condition for two gadgets' quadruples to be disjoint. -/
theorem gadDisj_of_forall {p a p' a' : ℕ}
    (h : ∀ δ δ' : ℕ, (δ = 0 ∨ δ = 1 ∨ δ = a ∨ δ = a + 1) →
      (δ' = 0 ∨ δ' = 1 ∨ δ' = a' ∨ δ' = a' + 1) → p + δ ≠ p' + δ') :
    GadDisj (p, a) (p', a') := by
  intro u hu hc
  rw [mem_quadSet] at hu hc
  obtain ⟨δ, hδ, rfl⟩ : ∃ δ, (δ = 0 ∨ δ = 1 ∨ δ = a ∨ δ = a + 1) ∧ u = p + δ := by
    rcases hc with h1 | h1 | h1 | h1
    exacts [⟨0, by tauto, by omega⟩, ⟨1, by tauto, by omega⟩, ⟨a, by tauto, by omega⟩,
      ⟨a + 1, by tauto, by omega⟩]
  obtain ⟨δ', hδ', he⟩ : ∃ δ', (δ' = 0 ∨ δ' = 1 ∨ δ' = a' ∨ δ' = a' + 1) ∧ p + δ = p' + δ' := by
    rcases hu with h1 | h1 | h1 | h1
    exacts [⟨0, by tauto, by omega⟩, ⟨1, by tauto, by omega⟩, ⟨a', by tauto, by omega⟩,
      ⟨a' + 1, by tauto, by omega⟩]
  exact h δ δ' hδ hδ' he

/-- Layer `m'`'s positions, read modulo an earlier layer's period, are `off m' + δ'`. -/
theorem base_mod {m m' : ℕ} (h : m ≤ m') (k δ : ℕ) :
    (k * Ls.Q m' + Ls.off m' + δ) % Ls.Q m = (Ls.off m' + δ) % Ls.Q m := by
  obtain ⟨t, ht⟩ := Ls.dvd_of_le h
  rw [show k * Ls.Q m' + Ls.off m' + δ = (Ls.off m' + δ) + Ls.Q m * (k * t) from by
    rw [ht]; ring]
  exact Nat.add_mul_mod_self_left _ _ _

theorem layerGads_sep (n : ℕ) : GadSep (Ls.layerGads n) := by
  intro x hx y hy
  rw [Ls.mem_layerGads] at hx hy
  obtain ⟨m, hm, k, hk, rfl⟩ := hx
  obtain ⟨m', hm', k', hk', rfl⟩ := hy
  have hQm := Ls.Qpos m
  by_cases hmm : m = m'
  · subst hmm
    by_cases hkk : k = k'
    · left; rw [hkk]
    · right
      refine gadDisj_of_forall (fun δ δ' hδ hδ' he => ?_)
      have hfit := Ls.hfit m
      set A := k * Ls.Q m with hA
      set B := k' * Ls.Q m with hB
      have hstep : A + Ls.Q m ≤ B ∨ B + Ls.Q m ≤ A := by
        rcases Nat.lt_or_ge k k' with h1 | h1
        · left
          calc A + Ls.Q m = (k + 1) * Ls.Q m := by rw [hA]; ring
            _ ≤ k' * Ls.Q m := Nat.mul_le_mul_right _ (by omega)
        · right
          have hk1 : k' + 1 ≤ k := by omega
          calc B + Ls.Q m = (k' + 1) * Ls.Q m := by rw [hB]; ring
            _ ≤ k * Ls.Q m := Nat.mul_le_mul_right _ hk1
      omega
  · right
    -- distinct layers: compare modulo the smaller period
    refine gadDisj_of_forall (fun δ δ' hδ hδ' he => ?_)
    rcases Nat.lt_or_ge m m' with hlt | hge
    · have e1 : (k * Ls.Q m + Ls.off m + δ) % Ls.Q m = (Ls.off m + δ) % Ls.Q m :=
        Ls.base_mod (le_refl m) k δ
      have e2 : (k' * Ls.Q m' + Ls.off m' + δ') % Ls.Q m = (Ls.off m' + δ') % Ls.Q m :=
        Ls.base_mod (le_of_lt hlt) k' δ'
      refine Ls.hdisj m m' hlt δ (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
        δ' (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) ?_
      rw [← e2, ← e1, he]
    · have hlt' : m' < m := by omega
      have e1 : (k * Ls.Q m + Ls.off m + δ) % Ls.Q m' = (Ls.off m + δ) % Ls.Q m' :=
        Ls.base_mod (le_of_lt hlt') k δ
      have e2 : (k' * Ls.Q m' + Ls.off m' + δ') % Ls.Q m' = (Ls.off m' + δ') % Ls.Q m' :=
        Ls.base_mod (le_refl m') k' δ'
      refine Ls.hdisj m' m hlt' δ' (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
        δ (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) ?_
      rw [← e1, ← e2, he]

theorem layerRow_nodup (m N : ℕ) : (Ls.layerRow m N).Nodup := by
  refine List.Nodup.map (fun k k' he => ?_) (List.nodup_range)
  have hQm := Ls.Qpos m
  simp only [Prod.mk.injEq] at he
  exact Nat.eq_of_mul_eq_mul_right hQm (by omega)

theorem layerGads_nodup (n : ℕ) : (Ls.layerGads n).Nodup := by
  rw [layerGads, List.nodup_flatMap]
  refine ⟨fun m _ => Ls.layerRow_nodup m _, ?_⟩
  rw [List.pairwise_iff_forall_sublist]
  intro m m' hsub
  -- `m` comes before `m'` in `range (n+1)`, so `m < m'`
  have hmm : m < m' := by
    have := List.Sublist.subset hsub
    have h1 : m ∈ List.range (n + 1) := this (by simp)
    have h2 : m' ∈ List.range (n + 1) := this (by simp)
    exact (List.pairwise_iff_forall_sublist.mp
      (List.pairwise_lt_range (n := n + 1))) hsub
  intro x hx hx'
  simp only [layerRow, List.mem_map, List.mem_range] at hx hx'
  obtain ⟨k, -, rfl⟩ := hx
  obtain ⟨k', -, he⟩ := hx'
  simp only [Prod.mk.injEq] at he
  have e1 : (k * Ls.Q m + Ls.off m + 0) % Ls.Q m = (Ls.off m + 0) % Ls.Q m :=
    Ls.base_mod (le_refl m) k 0
  have e2 : (k' * Ls.Q m' + Ls.off m' + 0) % Ls.Q m = (Ls.off m' + 0) % Ls.Q m :=
    Ls.base_mod (le_of_lt hmm) k' 0
  refine Ls.hdisj m m' hmm 0 (by simp) 0 (by simp) ?_
  rw [← e2, ← e1, he.1]

/-! ## The stages and their common limit

`stage x n` is the sequence obtained by driving the width-`Ls.Q n` block engine with the digits of
`x`.  By `blockSeq_multiG_eq_absGad` the perturbation it applies is INTRINSIC: at a position
covered by layer `i` the value is `absGad x (base) (arm i)`, where `base` is the unique multiple of
`Ls.Q i` shifted by `Ls.off i` that covers the position.  Neither the base nor the value mentions
`n`, so the stages agree wherever the later layers do not reach — and `hbig` says layer `i` reaches
no position below `Ls.Q i / 2`.  Hence `stage x n m` is eventually constant in `n`, position by
position, and `limSeq x m := stage x m m` is the limit. -/

/-- Periods grow at least like `64 * 2 ^ n`. -/
theorem Qgrow (n : ℕ) : 64 * 2 ^ n ≤ Ls.Q n := by
  induction n with
  | zero => simpa using Ls.hQ64
  | succ n ih =>
      have := Ls.hQdouble n
      calc 64 * 2 ^ (n + 1) = 2 * (64 * 2 ^ n) := by ring
        _ ≤ 2 * Ls.Q n := by omega
        _ ≤ Ls.Q (n + 1) := this

/-- A late layer reaches no early position. -/
theorem notMem_quad_of_lt {i m : ℕ} (h : m < i) :
    m % Ls.Q i ∉ quadSet (Ls.off i) (Ls.arm i) := by
  have h2 : i + 1 ≤ 2 ^ i := Nat.succ_le_of_lt (Nat.lt_two_pow_self)
  have hg := Ls.Qgrow i
  have hb := Ls.hbig i
  have hmQ : m < Ls.Q i := by nlinarith
  have hmo : m < Ls.off i := by nlinarith
  rw [Nat.mod_eq_of_lt hmQ, mem_quadSet]
  omega

/-- Reading a layer-`i` gadget of the width-`Ls.Q n` block engine modulo `Ls.Q i`. -/
theorem quad_of_row {i n k m : ℕ} (hi : i ≤ n) (hk : k < Ls.Q n / Ls.Q i)
    (h : m % Ls.Q n ∈ quadSet (k * Ls.Q i + Ls.off i) (Ls.arm i)) :
    m % Ls.Q i ∈ quadSet (Ls.off i) (Ls.arm i) ∧ k = (m % Ls.Q n) / Ls.Q i := by
  have hQi := Ls.Qpos i
  have hfit := Ls.hfit i
  have hdvd : Ls.Q i ∣ Ls.Q n := Ls.dvd_of_le hi
  rw [mem_quadSet] at h
  obtain ⟨δ, hδ, hr⟩ : ∃ δ, (δ = 0 ∨ δ = 1 ∨ δ = Ls.arm i ∨ δ = Ls.arm i + 1) ∧
      m % Ls.Q n = k * Ls.Q i + (Ls.off i + δ) := by
    rcases h with h | h | h | h
    exacts [⟨0, by tauto, by omega⟩, ⟨1, by tauto, by omega⟩,
      ⟨Ls.arm i, by tauto, by omega⟩, ⟨Ls.arm i + 1, by tauto, by omega⟩]
  have hlt : Ls.off i + δ < Ls.Q i := by omega
  have hmod : (m % Ls.Q n) % Ls.Q i = Ls.off i + δ := by
    rw [hr, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  have hdiv : (m % Ls.Q n) / Ls.Q i = k := by
    rw [hr, Nat.mul_comm, Nat.mul_add_div hQi, Nat.div_eq_of_lt hlt]; omega
  refine ⟨?_, hdiv.symm⟩
  rw [Nat.mod_mod_of_dvd m hdvd] at hmod
  rw [hmod, mem_quadSet]
  omega

/-- The width-`Ls.Q n` stage of the layer system, driven by the binary sequence `x`. -/
def stage (x : ℕ → ℕ) (n : ℕ) : ℕ → ℕ :=
  blockSeq (multiG (Ls.Q n) (Ls.layerGads n)) (blockOf 2 (Ls.Q n) x) (Ls.Q n)

/-- Off every layer, the stage is `x` itself. -/
theorem stage_eq_self {x : ℕ → ℕ} (hx : ∀ m, x m < 2) {n m : ℕ}
    (h : ∀ i ≤ n, m % Ls.Q i ∉ quadSet (Ls.off i) (Ls.arm i)) : Ls.stage x n m = x m := by
  refine blockSeq_multiG_eq_of_notMem _ (Ls.Qpos n) _ x hx m (fun pa hpa hmem => ?_)
  rw [Ls.mem_layerGads] at hpa
  obtain ⟨i, hi, k, hk, rfl⟩ := hpa
  exact h i hi (Ls.quad_of_row hi hk hmem).1

/-- **The intrinsic stage law.**  On a layer-`i` position the stage applies the absolute gadget
action at the base `Ls.Q i * (m / Ls.Q i) + Ls.off i` — no mention of the stage index `n`. -/
theorem stage_eq_absGad {x : ℕ → ℕ} (hx : ∀ m, x m < 2) {n i m : ℕ} (hi : i ≤ n)
    (h : m % Ls.Q i ∈ quadSet (Ls.off i) (Ls.arm i)) :
    Ls.stage x n m = absGad x (Ls.Q i * (m / Ls.Q i) + Ls.off i) (Ls.arm i) m := by
  have hQi := Ls.Qpos i
  have hQn := Ls.Qpos n
  have hfit := Ls.hfit i
  have hdvd : Ls.Q i ∣ Ls.Q n := Ls.dvd_of_le hi
  set k := (m % Ls.Q n) / Ls.Q i with hkdef
  rw [mem_quadSet] at h
  obtain ⟨δ, hδ, hr⟩ : ∃ δ, (δ = 0 ∨ δ = 1 ∨ δ = Ls.arm i ∨ δ = Ls.arm i + 1) ∧
      m % Ls.Q i = Ls.off i + δ := by
    rcases h with h | h | h | h
    exacts [⟨0, by tauto, by omega⟩, ⟨1, by tauto, by omega⟩,
      ⟨Ls.arm i, by tauto, by omega⟩, ⟨Ls.arm i + 1, by tauto, by omega⟩]
  have hmod : (m % Ls.Q n) % Ls.Q i = Ls.off i + δ := by rw [Nat.mod_mod_of_dvd m hdvd, hr]
  have hsplit : Ls.Q i * k + (Ls.off i + δ) = m % Ls.Q n := by
    rw [hkdef, ← hmod]; exact Nat.div_add_mod _ _
  have hk : k < Ls.Q n / Ls.Q i :=
    Nat.div_lt_div_of_lt_of_dvd hdvd (Nat.mod_lt _ hQn)
  have hmemq : m % Ls.Q n ∈ quadSet (k * Ls.Q i + Ls.off i) (Ls.arm i) := by
    rw [mem_quadSet]; rw [Nat.mul_comm k]; omega
  have hmem : (k * Ls.Q i + Ls.off i, Ls.arm i) ∈ Ls.layerGads n :=
    Ls.mem_layerGads.mpr ⟨i, hi, k, hk, rfl⟩
  have hbase : Ls.Q n * (m / Ls.Q n) + (k * Ls.Q i + Ls.off i) = Ls.Q i * (m / Ls.Q i) + Ls.off i := by
    have e1 : Ls.Q n * (m / Ls.Q n) + m % Ls.Q n = m := Nat.div_add_mod _ _
    have e2 : Ls.Q i * (m / Ls.Q i) + m % Ls.Q i = m := Nat.div_add_mod _ _
    rw [Nat.mul_comm k] at *
    omega
  rw [stage, blockSeq_multiG_eq_absGad _ hQn _ (Ls.layerGads_sep n) (Ls.layerGads_nodup n) x hx
    _ _ hmem ((Ls.layerGads_ok n _ hmem).2) m hmemq, hbase]

/-- **The stages stabilize.**  Position `m` is settled from stage `m` on. -/
theorem stage_eq_of_ge {x : ℕ → ℕ} (hx : ∀ m, x m < 2) {n m : ℕ} (hnm : m ≤ n) :
    Ls.stage x n m = Ls.stage x m m := by
  classical
  by_cases h : ∃ i ≤ m, m % Ls.Q i ∈ quadSet (Ls.off i) (Ls.arm i)
  · obtain ⟨i, hi, hmem⟩ := h
    rw [Ls.stage_eq_absGad hx (le_trans hi hnm) hmem, Ls.stage_eq_absGad hx hi hmem]
  · push_neg at h
    have hall : ∀ i ≤ n, m % Ls.Q i ∉ quadSet (Ls.off i) (Ls.arm i) := by
      intro i _
      rcases Nat.lt_or_ge m i with h1 | h1
      · exact Ls.notMem_quad_of_lt h1
      · exact h i h1
    rw [Ls.stage_eq_self hx hall, Ls.stage_eq_self hx h]

/-- The limit sequence of the layer system. -/
def limSeq (x : ℕ → ℕ) (m : ℕ) : ℕ := Ls.stage x m m

theorem stage_eq_limSeq {x : ℕ → ℕ} (hx : ∀ m, x m < 2) {n m : ℕ} (hnm : m ≤ n) :
    Ls.stage x n m = Ls.limSeq x m := Ls.stage_eq_of_ge hx hnm

/-! ## The difference density of a stage

Stage `n` and the limit differ only at positions covered by a layer `i > n`.  Layer `i` occupies
four residues modulo `Ls.Q i`, so it covers at most `4 * (M / Ls.Q i + 1)` positions below `M`;
and by `hbig` it covers NONE when `Ls.Q i > 2 * M`.  Both cases are dominated by `12 * M / Ls.Q i`,
and `Ls.Q i ≥ 64 * 2 ^ i` sums the tail to `12 * M / (64 * 2 ^ n)`.
-/

/-- Residues modulo `q` are sparse in `range M` — the non-divisor version of
`card_filter_mod_le`. -/
theorem card_filter_mod_le' (M q c : ℕ) (hq : 0 < q) :
    ((range M).filter (fun m => m % q = c)).card ≤ M / q + 1 := by
  classical
  rw [← Finset.card_range (M / q + 1)]
  refine Finset.card_le_card_of_injOn (fun m => m / q) (fun m hm => ?_) (fun m hm m' hm' he => ?_)
  · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hm
    simp only [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
  · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hm hm'
    have h1 : q * (m / q) + m % q = m := Nat.div_add_mod m q
    have h2 : q * (m' / q) + m' % q = m' := Nat.div_add_mod m' q
    rw [hm.2] at h1
    rw [hm'.2] at h2
    simp only at he
    rw [← h1, ← h2, he]

theorem card_quadSet_le (p a : ℕ) : (quadSet p a).card ≤ 4 := by
  rw [quadSet]
  refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
  refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
  refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
  simp

/-- A layer covers at most `4 * (M / Q + 1)` positions below `M`. -/
theorem card_cover_le (i M : ℕ) :
    ((range M).filter (fun m => m % Ls.Q i ∈ quadSet (Ls.off i) (Ls.arm i))).card
      ≤ 4 * (M / Ls.Q i + 1) := by
  classical
  have hq := Ls.Qpos i
  have hsub : (range M).filter (fun m => m % Ls.Q i ∈ quadSet (Ls.off i) (Ls.arm i))
      ⊆ (quadSet (Ls.off i) (Ls.arm i)).biUnion
        (fun c => (range M).filter (fun m => m % Ls.Q i = c)) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    exact Finset.mem_biUnion.mpr ⟨_, hm.2, Finset.mem_filter.mpr ⟨hm.1, rfl⟩⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans Finset.card_biUnion_le ?_
  refine le_trans (Finset.sum_le_sum (fun c _ => card_filter_mod_le' M (Ls.Q i) c hq)) ?_
  rw [Finset.sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (card_quadSet_le _ _)

/-- The real-valued uniform cover bound. -/
theorem card_cover_real_le (i M : ℕ) :
    (((range M).filter (fun m => m % Ls.Q i ∈ quadSet (Ls.off i) (Ls.arm i))).card : ℝ)
      ≤ 12 * M / Ls.Q i := by
  classical
  have hq := Ls.Qpos i
  have hqR : (0 : ℝ) < Ls.Q i := by exact_mod_cast hq
  rcases Nat.lt_or_ge (2 * M) (Ls.Q i) with hbig | hsmall
  · -- the layer reaches no position below `M` at all
    have hempty : (range M).filter (fun m => m % Ls.Q i ∈ quadSet (Ls.off i) (Ls.arm i)) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr (fun m hm hmem => ?_)
      rw [Finset.mem_range] at hm
      have hb := Ls.hbig i
      have hfit := Ls.hfit i
      rw [Nat.mod_eq_of_lt (by omega), mem_quadSet] at hmem
      omega
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have hM : 0 < M := by
      rcases Nat.eq_zero_or_pos M with rfl | h
      · omega
      · exact h
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    have h1 : (((range M).filter (fun m => m % Ls.Q i ∈ quadSet (Ls.off i) (Ls.arm i))).card : ℝ)
        ≤ 4 * ((M / Ls.Q i : ℕ) + 1) := by
      have := Ls.card_cover_le i M
      exact_mod_cast this
    have h2 : (((M / Ls.Q i : ℕ) : ℝ)) ≤ (M : ℝ) / Ls.Q i := Nat.cast_div_le
    have hdQ : ((M / Ls.Q i : ℕ) : ℝ) * Ls.Q i ≤ M := by
      rw [← le_div_iff₀ hqR]; exact h2
    have hQ2 : (Ls.Q i : ℝ) ≤ 2 * M := by exact_mod_cast hsmall
    rw [le_div_iff₀ hqR]
    nlinarith [h1, hdQ, hQ2, hqR]

/-- The positions where stage `n` differs from the limit are covered by the later layers. -/
theorem diff_subset {x : ℕ → ℕ} (hx : ∀ m, x m < 2) (n M : ℕ) :
    (range M).filter (fun m => Ls.limSeq x m ≠ Ls.stage x n m)
      ⊆ (Finset.Ico (n + 1) (n + 1 + M)).biUnion
        (fun i => (range M).filter (fun m => m % Ls.Q i ∈ quadSet (Ls.off i) (Ls.arm i))) := by
  classical
  intro m hm
  rw [Finset.mem_filter, Finset.mem_range] at hm
  obtain ⟨hmM, hne⟩ := hm
  -- some layer `i` with `n < i ≤ m` covers `m`
  have hex : ∃ i, n < i ∧ i ≤ m ∧ m % Ls.Q i ∈ quadSet (Ls.off i) (Ls.arm i) := by
    by_contra hc
    push_neg at hc
    refine hne ?_
    by_cases h : ∃ i ≤ m, m % Ls.Q i ∈ quadSet (Ls.off i) (Ls.arm i)
    · obtain ⟨i, hi, hmem⟩ := h
      have hin : i ≤ n := by
        by_contra hgt
        exact absurd hmem (hc i (by omega) hi)
      rw [limSeq, Ls.stage_eq_absGad hx hi hmem, Ls.stage_eq_absGad hx hin hmem]
    · push_neg at h
      have hall : ∀ i ≤ n, m % Ls.Q i ∉ quadSet (Ls.off i) (Ls.arm i) := by
        intro i _
        rcases Nat.lt_or_ge m i with h1 | h1
        · exact Ls.notMem_quad_of_lt h1
        · exact h i h1
      rw [limSeq, Ls.stage_eq_self hx hall, Ls.stage_eq_self hx (fun i hi => h i hi)]
  obtain ⟨i, hni, him, hmem⟩ := hex
  refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmM, hmem⟩

/-- **The difference density bound.**  `diffCount (limSeq) (stage n) M ≤ (3 / (16 * 2 ^ n)) * M`. -/
theorem diffCount_stage_le {x : ℕ → ℕ} (hx : ∀ m, x m < 2) (n M : ℕ) :
    (diffCount (Ls.limSeq x) (Ls.stage x n) M : ℝ) ≤ 3 / (16 * 2 ^ n) * M := by
  classical
  have hcard : (diffCount (Ls.limSeq x) (Ls.stage x n) M : ℝ)
      ≤ ∑ i ∈ Finset.Ico (n + 1) (n + 1 + M),
          (((range M).filter (fun m => m % Ls.Q i ∈ quadSet (Ls.off i) (Ls.arm i))).card : ℝ) := by
    have h1 := Finset.card_le_card (Ls.diff_subset hx n M)
    have h2 := Finset.card_biUnion_le (s := Finset.Ico (n + 1) (n + 1 + M))
      (t := fun i => (range M).filter (fun m => m % Ls.Q i ∈ quadSet (Ls.off i) (Ls.arm i)))
    have : diffCount (Ls.limSeq x) (Ls.stage x n) M
        ≤ ∑ i ∈ Finset.Ico (n + 1) (n + 1 + M),
            ((range M).filter (fun m => m % Ls.Q i ∈ quadSet (Ls.off i) (Ls.arm i))).card := by
      rw [diffCount]; omega
    exact_mod_cast this
  have hterm : ∀ i ∈ Finset.Ico (n + 1) (n + 1 + M),
      (((range M).filter (fun m => m % Ls.Q i ∈ quadSet (Ls.off i) (Ls.arm i))).card : ℝ)
        ≤ 12 * M * (1 / 64) * (1 / 2 : ℝ) ^ i := by
    intro i _
    refine le_trans (Ls.card_cover_real_le i M) ?_
    have hQ : (64 : ℝ) * 2 ^ i ≤ Ls.Q i := by exact_mod_cast Ls.Qgrow i
    have hqR : (0 : ℝ) < Ls.Q i := by exact_mod_cast Ls.Qpos i
    have hMR : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hpow : (0 : ℝ) < 2 ^ i := by positivity
    rw [div_le_iff₀ hqR]
    have hc : ((1 : ℝ) / 2) ^ i * 2 ^ i = 1 := by rw [← mul_pow]; norm_num
    have hcpos : (0 : ℝ) < ((1 : ℝ) / 2) ^ i := by positivity
    have hcQ : (64 : ℝ) ≤ ((1 : ℝ) / 2) ^ i * Ls.Q i := by nlinarith [hc, hQ, hcpos]
    nlinarith [hcQ, hMR]
  refine le_trans (le_trans hcard (Finset.sum_le_sum hterm)) ?_
  rw [← Finset.mul_sum]
  have hgeom : ∑ i ∈ Finset.Ico (n + 1) (n + 1 + M), (1 / 2 : ℝ) ^ i
      ≤ (1 / 2 : ℝ) ^ n * 2 * (1 / 2) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [pow_add]
    rw [← Finset.mul_sum]
    have := sum_geometric_two_le M
    have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ 1 := by positivity
    calc (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ 1 * ∑ i ∈ range (n + 1 + M - (n + 1)), (1 / 2 : ℝ) ^ i
        ≤ (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ 1 * 2 := by
          refine mul_le_mul_of_nonneg_left ?_ hp.le
          simpa using sum_geometric_two_le (n + 1 + M - (n + 1))
      _ = (1 / 2 : ℝ) ^ n * 2 * (1 / 2) := by ring
  have hMR : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have he : (3 : ℝ) / (16 * 2 ^ n) * M = 12 * M * (1 / 64) * ((1 / 2 : ℝ) ^ n * 2 * (1 / 2)) := by
    have h2n : ((1 : ℝ) / 2) ^ n = 1 / 2 ^ n := by rw [div_pow, one_pow]
    rw [h2n]
    field_simp
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hgeom (by positivity)

end LayerSys

/-! ## The exact window law at a repeated arm

`multi_not_isAbelianAt'` only needs the inequality `coeff < Binomial`.  The limit transfer needs
the exact common value, so here is the exact constant term at every residue, with NO injectivity
hypothesis on the arms: a length-`L` window separates the gadget `(p', a')` only from block `b = 0`
at residue `r = p' + 1` and only when `a' = L`.  Hence at a residue that is not `p' + 1` for any
`L`-armed gadget the law is exactly Binomial, and at such a residue exactly ONE block (`b = 0`) is
defective, contributing exactly the factor `3 / 4`.
-/

/-- A length-`L` window separates a gadget only from block `0`, at residue `p' + 1`, arm `L`. -/
theorem segSet_unsep_gen (q L r b p' a' : ℕ) (ha' : 2 ≤ a') (hq' : p' + a' + 1 < q) (hr : r < q)
    (hne : ¬ (b = 0 ∧ r = p' + 1 ∧ a' = L)) : Unsep (segSet q L r b) (p', a') := by
  rw [segSet_eq_Ico_gen]
  refine sep_of_ne ha' ?_
  rintro ⟨h1, h2⟩
  rcases Nat.eq_zero_or_pos b with rfl | hb1
  · simp only [Nat.zero_mul, Nat.sub_zero] at h1 h2
    exact hne ⟨rfl, by omega, by omega⟩
  · have hbq : q ≤ b * q := Nat.le_mul_of_pos_left q hb1
    omega

/-- The plain (Binomial) constant term of a segment factor. -/
theorem segGf_coeff_plain (q : ℕ) (gs : List (ℕ × ℕ)) (hq0 : 0 < q)
    (hok : ∀ pa ∈ gs, GadOk q pa) (hgs : GadSep gs) (hnd : gs.Nodup) (L r b : ℕ)
    (hsep : ∀ pa ∈ gs, Unsep (segSet q L r b) pa) :
    (∑ d ∈ range (2 ^ q), (X : ℝ[X]) ^ segOnes (multiG q gs) q L r b d).coeff 0
      = (2 : ℝ) ^ q / 2 ^ segLen q L r b := by
  rw [multi_segGf_plain q gs hq0 hok hgs hnd L r b hsep, Polynomial.coeff_C_mul]
  have hb : ((1 + X : ℝ[X]) ^ segLen q L r b).coeff 0 = 1 := by
    rw [add_comm, Polynomial.coeff_X_add_one_pow]
    simp
  rw [hb, mul_one]
  push_cast
  ring

/-- **The exact defective factor.**  At `r = p + 1`, block `0`, an `a`-armed gadget contributes
exactly `3 / 4` — the dichotomy allows only two values and the defect is strict. -/
theorem segGf_coeff_defect (q : ℕ) (gs : List (ℕ × ℕ)) (hq0 : 0 < q) (p a : ℕ)
    (hmem : (p, a) ∈ gs) (hok : ∀ pa ∈ gs, GadOk q pa) (hgs : GadSep gs) (hnd : gs.Nodup) :
    (∑ d ∈ range (2 ^ q), (X : ℝ[X]) ^ segOnes (multiG q gs) q a (p + 1) 0 d).coeff 0
      = 3 / 4 * ((2 : ℝ) ^ q / 2 ^ segLen q a (p + 1) 0) := by
  obtain ⟨ha, hq⟩ := hok (p, a) hmem
  simp only at ha hq
  have hseg0 : segLen q a (p + 1) 0 = a := by
    rw [segLen_eq_card q a (p + 1) 0 hq0, segSet_defect q p a hq, Nat.card_Ico]
    omega
  have hlt : (∑ d ∈ range (2 ^ q), (X : ℝ[X]) ^ segOnes (multiG q gs) q a (p + 1) 0 d).coeff 0
      < (2 : ℝ) ^ q / 2 ^ a := by
    rw [segGf_eq_blockGf q hq0 _ a (p + 1) 0, segSet_defect q p a hq]
    exact blockGf_defect_coeff q gs p a hmem hok hgs hnd
  rcases segGf_coeff_dichotomy q hq0 gs hok hgs hnd a (p + 1) 0 with h | h
  · rw [hseg0] at h
    rw [h] at hlt
    exact absurd hlt (lt_irrefl _)
  · exact h

/-- **Exact law at a clean residue.**  If `r` is not `p' + 1` for any `L`-armed gadget, the
length-`L` window law at `r` is exactly Binomial. -/
theorem winGf_coeff_plain_res (q : ℕ) (hq0 : 0 < q) (gs : List (ℕ × ℕ))
    (hok : ∀ pa ∈ gs, GadOk q pa) (hgs : GadSep gs) (hnd : gs.Nodup) (S L r : ℕ) (hr : r < q)
    (hS : ∀ t < L, (r + t) / q < S)
    (hclean : ∀ pa ∈ gs, ¬ (r = pa.1 + 1 ∧ pa.2 = L)) :
    (winGf (multiG q gs) q (2 ^ q) S L r).coeff 0 = ((2 ^ q : ℕ) : ℝ) ^ S / 2 ^ L := by
  classical
  have h := winGf_coeff_eq q hq0 gs hok hgs hnd S L r hS ∅ (by simp)
    (by simp) (fun b _ => ?_)
  · simpa using h
  · refine segGf_coeff_plain q gs hq0 hok hgs hnd L r b (fun pa hpa => ?_)
    obtain ⟨p', a'⟩ := pa
    obtain ⟨ha', hq'⟩ := hok (p', a') hpa
    refine segSet_unsep_gen q L r b p' a' ha' hq' hr (fun hc => ?_)
    exact hclean (p', a') hpa ⟨hc.2.1, hc.2.2⟩

/-- **Exact law at a defective residue.**  At `r = p + 1` for an `L`-armed gadget `(p, L)` exactly
one block is defective, so the window law is exactly `3 / 4` of Binomial. -/
theorem winGf_coeff_defect_res (q : ℕ) (hq0 : 0 < q) (gs : List (ℕ × ℕ))
    (hok : ∀ pa ∈ gs, GadOk q pa) (hgs : GadSep gs) (hnd : gs.Nodup) (S L p : ℕ)
    (hmem : (p, L) ∈ gs) (hSpos : 0 < S) (hr : p + 1 < q)
    (hS : ∀ t < L, (p + 1 + t) / q < S) :
    (winGf (multiG q gs) q (2 ^ q) S L (p + 1)).coeff 0
      = 3 / 4 * (((2 ^ q : ℕ) : ℝ) ^ S / 2 ^ L) := by
  classical
  have h := winGf_coeff_eq q hq0 gs hok hgs hnd S L (p + 1) hS {0}
    (by simpa using Finset.mem_range.mpr hSpos)
    (fun b hb => ?_) (fun b hb => ?_)
  · simpa using h
  · rw [Finset.mem_singleton] at hb
    subst hb
    exact segGf_coeff_defect q gs hq0 p L hmem hok hgs hnd
  · rw [Finset.mem_sdiff, Finset.mem_singleton] at hb
    refine segGf_coeff_plain q gs hq0 hok hgs hnd L (p + 1) b (fun pa hpa => ?_)
    obtain ⟨p', a'⟩ := pa
    obtain ⟨ha', hq'⟩ := hok (p', a') hpa
    exact segSet_unsep_gen q L (p + 1) b p' a' ha' hq' hr (fun hc => hb.2 hc.1)
