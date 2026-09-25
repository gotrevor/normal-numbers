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
