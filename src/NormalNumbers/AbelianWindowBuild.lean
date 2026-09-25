/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AbelianWindowLayers

/-!
# Building the layer system

`AbelianWindowLayers` reduces C4's hard branch to producing, for any injective arm sequence
`arm : ℕ → ℕ` with `2 ≤ arm n`, a `LayerSys` with those arms.  This file does that by recursion.

The periods are forced: `Q 0 = 4 * (arm 0 + 64)` and `Q (n+1) = 2 * Q n * (arm (n+1) + 2)`, so
nestedness, doubling and the geometric growth `64 * 2 ^ n ≤ Q n` hold with NO reference to the
offsets.  That is what makes the recursion non-mutual: the offset pigeonhole
(`exists_avoiding_offset`) needs only the periods, so the offset at stage `n + 1` can be chosen
after the fact, and the remaining `LayerSys` fields (`hfit`, `hbig`, `hdisj`) follow from that
one choice.

The offset is taken in `range (Q n)` — the PREVIOUS period — and then translated by
`Q n * (arm (n+1) + 2)` into the top half of `Q (n+1)`.  Translation by a multiple of `Q n`
changes no residue modulo any `Q m`, `m ≤ n`, so disjointness survives, while `hbig` becomes
automatic.
-/

open Finset

namespace NormalNumbers.Abelian

/-- The disjointness demand on a candidate offset for layer `n + 1`. -/
def GoodOff (arm : ℕ → ℕ) (Qf offf : ℕ → ℕ) (n o : ℕ) : Prop :=
  ∀ m ≤ n, ∀ δ ∈ ({0, 1, arm m, arm m + 1} : Finset ℕ),
    ∀ δ' ∈ ({0, 1, arm (n + 1), arm (n + 1) + 1} : Finset ℕ),
      (o + δ') % Qf m ≠ (offf m + δ) % Qf m

open Classical in
/-- The periods and offsets of the first `n + 1` layers (constant beyond `n`). -/
noncomputable def bld (arm : ℕ → ℕ) : ℕ → (ℕ → ℕ) × (ℕ → ℕ)
  | 0 => (fun _ => 4 * (arm 0 + 64), fun _ => 2 * (arm 0 + 64))
  | n + 1 =>
      let P := bld arm n
      let Qn := P.1 n
      let o : ℕ := if h : ∃ o, o < Qn ∧ GoodOff arm P.1 P.2 n o then h.choose else 0
      (fun i => if i ≤ n then P.1 i else 2 * Qn * (arm (n + 1) + 2),
       fun i => if i ≤ n then P.2 i else o + Qn * (arm (n + 1) + 2))

/-- The period of layer `n`. -/
noncomputable def bQ (arm : ℕ → ℕ) (n : ℕ) : ℕ := (bld arm n).1 n

/-- The offset of layer `n`. -/
noncomputable def bOff (arm : ℕ → ℕ) (n : ℕ) : ℕ := (bld arm n).2 n

variable (arm : ℕ → ℕ)

theorem bld_stable : ∀ n i, i ≤ n → (bld arm n).1 i = bQ arm i ∧ (bld arm n).2 i = bOff arm i := by
  intro n
  induction n with
  | zero =>
      intro i hi
      rw [Nat.le_zero] at hi
      subst hi
      exact ⟨rfl, rfl⟩
  | succ n ih =>
      intro i hi
      rcases Nat.lt_or_ge n i with h1 | h1
      · have : i = n + 1 := by omega
        subst this
        exact ⟨rfl, rfl⟩
      · have h2 : (bld arm (n + 1)).1 i = (bld arm n).1 i := by
          show (if i ≤ n then (bld arm n).1 i else _) = _
          rw [if_pos h1]
        have h3 : (bld arm (n + 1)).2 i = (bld arm n).2 i := by
          show (if i ≤ n then (bld arm n).2 i else _) = _
          rw [if_pos h1]
        rw [h2, h3]
        exact ih i h1

theorem bQ_zero : bQ arm 0 = 4 * (arm 0 + 64) := rfl

theorem bOff_zero : bOff arm 0 = 2 * (arm 0 + 64) := rfl

theorem bQ_succ (n : ℕ) : bQ arm (n + 1) = 2 * bQ arm n * (arm (n + 1) + 2) := by
  show (if n + 1 ≤ n then _ else 2 * (bld arm n).1 n * (arm (n + 1) + 2)) = _
  rw [if_neg (by omega)]
  rfl

theorem bQ_pos (n : ℕ) : 0 < bQ arm n := by
  induction n with
  | zero => rw [bQ_zero]; omega
  | succ n ih => rw [bQ_succ]; positivity

theorem bQ_double (n : ℕ) : 2 * bQ arm n ≤ bQ arm (n + 1) := by
  rw [bQ_succ]
  nlinarith [bQ_pos arm n]

theorem bQ_dvd (n : ℕ) : bQ arm n ∣ bQ arm (n + 1) := ⟨2 * (arm (n + 1) + 2), by rw [bQ_succ]; ring⟩

theorem bQ_dvd_le {m n : ℕ} (h : m ≤ n) : bQ arm m ∣ bQ arm n := by
  induction n with
  | zero => rw [Nat.le_zero] at h; rw [h]
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with h1 | h1
      · exact dvd_trans (ih (by omega)) (bQ_dvd arm n)
      · rw [show m = n + 1 from by omega]

theorem bQ_grow (n : ℕ) : 64 * 2 ^ n ≤ bQ arm n := by
  induction n with
  | zero => rw [bQ_zero]; omega
  | succ n ih =>
      have := bQ_double arm n
      calc 64 * 2 ^ (n + 1) = 2 * (64 * 2 ^ n) := by ring
        _ ≤ 2 * bQ arm n := by omega
        _ ≤ bQ arm (n + 1) := this

/-! ## The offset exists -/

open Classical in
/-- The residues modulo `bQ arm m` that a layer-`(n+1)` offset must avoid. -/
noncomputable def badRes (n m : ℕ) : Finset ℕ :=
  ((({0, 1, arm m, arm m + 1} : Finset ℕ) ×ˢ
      ({0, 1, arm (n + 1), arm (n + 1) + 1} : Finset ℕ))).image
    (fun pr => (bOff arm m + pr.1 + (bQ arm m - pr.2 % bQ arm m)) % bQ arm m)

theorem card_badRes (n m : ℕ) : (badRes arm n m).card ≤ 16 := by
  classical
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_product]
  have h1 : (({0, 1, arm m, arm m + 1} : Finset ℕ)).card ≤ 4 := by
    refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
    refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
    refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
    simp
  have h2 : (({0, 1, arm (n + 1), arm (n + 1) + 1} : Finset ℕ)).card ≤ 4 := by
    refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
    refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
    refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
    simp
  calc _ ≤ 4 * 4 := Nat.mul_le_mul h1 h2
    _ = 16 := by norm_num

/-- Avoiding `badRes` is exactly the disjointness demand. -/
theorem goodOff_of_notMem {n o : ℕ} (h : ∀ m ≤ n, o % bQ arm m ∉ badRes arm n m) :
    GoodOff arm (bQ arm) (bOff arm) n o := by
  classical
  intro m hm δ hδ δ' hδ' hc
  refine h m hm ?_
  rw [badRes, Finset.mem_image]
  refine ⟨(δ, δ'), Finset.mem_product.mpr ⟨hδ, hδ'⟩, ?_⟩
  set Q := bQ arm m with hQdef
  have hQ : 0 < Q := bQ_pos arm m
  -- `δ' + (Q - δ' % Q) = Q * (δ' / Q + 1)`
  have hsplit : δ' + (Q - δ' % Q) = Q * (δ' / Q + 1) := by
    have h1 : Q * (δ' / Q) + δ' % Q = δ' := Nat.div_add_mod δ' Q
    have h2 : δ' % Q < Q := Nat.mod_lt _ hQ
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hmod : (o + δ' + (Q - δ' % Q)) % Q = o % Q := by
    rw [Nat.add_assoc, hsplit, Nat.add_mul_mod_self_left]
  calc (bOff arm m + δ + (Q - δ' % Q)) % Q
      = ((bOff arm m + δ) % Q + (Q - δ' % Q)) % Q := (Nat.mod_add_mod _ _ _).symm
    _ = ((o + δ') % Q + (Q - δ' % Q)) % Q := by rw [hc]
    _ = (o + δ' + (Q - δ' % Q)) % Q := Nat.mod_add_mod _ _ _
    _ = o % Q := hmod

/-- **The offset always exists.**  Each earlier layer forbids at most `16` residue classes, and
the periods grow geometrically from `64`, so the forbidden set misses `range (bQ arm n)`. -/
theorem exists_goodOff (n : ℕ) : ∃ o, o < bQ arm n ∧ GoodOff arm (bQ arm) (bOff arm) n o := by
  classical
  have hQn : 0 < bQ arm n := bQ_pos arm n
  have hsum : ∑ m ∈ range (n + 1), (badRes arm n m).card * (bQ arm n / bQ arm m) < bQ arm n := by
    have hQnR : (0 : ℝ) < bQ arm n := by exact_mod_cast hQn
    have hreal : ((∑ m ∈ range (n + 1), (badRes arm n m).card * (bQ arm n / bQ arm m) : ℕ) : ℝ)
        ≤ (bQ arm n : ℝ) / 2 := by
      have hterm : ∀ m ∈ range (n + 1),
          (((badRes arm n m).card * (bQ arm n / bQ arm m) : ℕ) : ℝ)
            ≤ 16 * (bQ arm n : ℝ) * (1 / 64) * (1 / 2 : ℝ) ^ m := by
        intro m _
        have hQm : 0 < bQ arm m := bQ_pos arm m
        have hQmR : (0 : ℝ) < bQ arm m := by exact_mod_cast hQm
        have hg : (64 : ℝ) * 2 ^ m ≤ bQ arm m := by exact_mod_cast bQ_grow arm m
        have hc : (((badRes arm n m).card : ℕ) : ℝ) ≤ 16 := by
          exact_mod_cast card_badRes arm n m
        have hd : (((bQ arm n / bQ arm m : ℕ)) : ℝ) ≤ (bQ arm n : ℝ) / bQ arm m := Nat.cast_div_le
        have hdnn : (0 : ℝ) ≤ (((bQ arm n / bQ arm m : ℕ)) : ℝ) := Nat.cast_nonneg _
        have hcnn : (0 : ℝ) ≤ (((badRes arm n m).card : ℕ) : ℝ) := Nat.cast_nonneg _
        have hstep : (((badRes arm n m).card : ℕ) : ℝ) * (((bQ arm n / bQ arm m : ℕ)) : ℝ)
            ≤ 16 * ((bQ arm n : ℝ) / bQ arm m) := by
          calc (((badRes arm n m).card : ℕ) : ℝ) * (((bQ arm n / bQ arm m : ℕ)) : ℝ)
              ≤ 16 * (((bQ arm n / bQ arm m : ℕ)) : ℝ) := by nlinarith
            _ ≤ 16 * ((bQ arm n : ℝ) / bQ arm m) := by nlinarith
        rw [Nat.cast_mul]
        refine le_trans hstep ?_
        have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ m := by positivity
        have hcm : ((1 : ℝ) / 2) ^ m * 2 ^ m = 1 := by rw [← mul_pow]; norm_num
        have hcQ : (64 : ℝ) ≤ ((1 : ℝ) / 2) ^ m * bQ arm m := by nlinarith
        have hrw : (16 : ℝ) * ((bQ arm n : ℝ) / bQ arm m) = 16 * (bQ arm n : ℝ) / bQ arm m := by
          ring
        rw [hrw, div_le_iff₀ hQmR]
        nlinarith [hQnR.le]
      rw [Nat.cast_sum]
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.mul_sum]
      have hgeom : ∑ m ∈ range (n + 1), (1 / 2 : ℝ) ^ m ≤ 2 := by
        simpa using sum_geometric_two_le (n + 1)
      nlinarith [hQnR.le]
    have : ((∑ m ∈ range (n + 1), (badRes arm n m).card * (bQ arm n / bQ arm m) : ℕ) : ℝ)
        < (bQ arm n : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨o, hoQ, hob⟩ := exists_avoiding_offset (n + 1) (bQ arm n) hQn (fun m => bQ arm m)
    (fun m => badRes arm n m) (fun m hm => ⟨bQ_pos arm m, bQ_dvd_le arm (by omega)⟩) hsum
  exact ⟨o, hoQ, goodOff_of_notMem arm (fun m hm => hob m (by omega))⟩

/-! ## Reading off the chosen offset -/

theorem goodOff_iff (n o : ℕ) :
    GoodOff arm (bld arm n).1 (bld arm n).2 n o ↔ GoodOff arm (bQ arm) (bOff arm) n o := by
  unfold GoodOff
  constructor
  · intro h m hm δ hδ δ' hδ'
    rw [← (bld_stable arm n m hm).1, ← (bld_stable arm n m hm).2]
    exact h m hm δ hδ δ' hδ'
  · intro h m hm δ hδ δ' hδ'
    rw [(bld_stable arm n m hm).1, (bld_stable arm n m hm).2]
    exact h m hm δ hδ δ' hδ'

/-- **The chosen offset.**  `bOff arm (n+1)` is a good offset translated into the top half. -/
theorem bOff_succ_spec (n : ℕ) : ∃ o, o < bQ arm n ∧ GoodOff arm (bQ arm) (bOff arm) n o ∧
    bOff arm (n + 1) = o + bQ arm n * (arm (n + 1) + 2) := by
  classical
  have hcond : ∃ o, o < (bld arm n).1 n ∧ GoodOff arm (bld arm n).1 (bld arm n).2 n o := by
    obtain ⟨o, ho, hg⟩ := exists_goodOff arm n
    exact ⟨o, ho, (goodOff_iff arm n o).mpr hg⟩
  obtain ⟨ho, hg⟩ := hcond.choose_spec
  refine ⟨hcond.choose, ho, (goodOff_iff arm n _).mp hg, ?_⟩
  show (if n + 1 ≤ n then (bld arm n).2 (n + 1)
    else (if h : ∃ o, o < (bld arm n).1 n ∧ GoodOff arm (bld arm n).1 (bld arm n).2 n o
      then h.choose else 0) + (bld arm n).1 n * (arm (n + 1) + 2)) = _
  rw [if_neg (by omega), dif_pos hcond]
  rfl

/-! ## The layer system -/

theorem bfit : ∀ n, bOff arm n + arm n + 1 < bQ arm n := by
  intro n
  cases n with
  | zero => rw [bQ_zero, bOff_zero]; omega
  | succ n =>
      obtain ⟨o, ho, -, hoff⟩ := bOff_succ_spec arm n
      have hQn : 0 < bQ arm n := bQ_pos arm n
      have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have hgr := bQ_grow arm n
      have hQ2 : 2 ≤ bQ arm n := by nlinarith
      rw [hoff, bQ_succ]
      have h1 : arm (n + 1) + 1 ≤ bQ arm n * (arm (n + 1) + 1) :=
        Nat.le_mul_of_pos_left _ hQn
      nlinarith

theorem bbig : ∀ n, bQ arm n ≤ 2 * bOff arm n := by
  intro n
  cases n with
  | zero => rw [bQ_zero, bOff_zero]; omega
  | succ n =>
      obtain ⟨o, -, -, hoff⟩ := bOff_succ_spec arm n
      rw [hoff, bQ_succ,
        show 2 * bQ arm n * (arm (n + 1) + 2) = 2 * (bQ arm n * (arm (n + 1) + 2)) from by ring]
      omega

theorem bdisj : ∀ m n, m < n → ∀ δ ∈ ({0, 1, arm m, arm m + 1} : Finset ℕ),
    ∀ δ' ∈ ({0, 1, arm n, arm n + 1} : Finset ℕ),
      (bOff arm n + δ') % bQ arm m ≠ (bOff arm m + δ) % bQ arm m := by
  intro m n hmn δ hδ δ' hδ'
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨o, -, hg, hoff⟩ := bOff_succ_spec arm k
  obtain ⟨t, ht⟩ : bQ arm m ∣ bQ arm k * (arm (k + 1) + 2) :=
    Dvd.dvd.mul_right (bQ_dvd_le arm (by omega)) _
  have hmod : (bOff arm (k + 1) + δ') % bQ arm m = (o + δ') % bQ arm m := by
    rw [hoff, show o + bQ arm k * (arm (k + 1) + 2) + δ' = (o + δ') + bQ arm m * t from by
      rw [ht]; ring, Nat.add_mul_mod_self_left]
  rw [hmod]
  exact hg m (by omega) δ hδ δ' hδ'

/-- **The layer system with prescribed arms.** -/
noncomputable def bLayerSys (harm : ∀ n, 2 ≤ arm n) (hinj : ∀ i j, arm i = arm j → i = j) :
    LayerSys where
  Q := bQ arm
  off := bOff arm
  arm := arm
  hQ64 := by rw [bQ_zero]; omega
  hQdouble := bQ_double arm
  hQdvd := bQ_dvd arm
  harm := harm
  hfit := bfit arm
  hbig := bbig arm
  harminj := hinj
  hdisj := bdisj arm

@[simp] theorem bLayerSys_arm (harm : ∀ n, 2 ≤ arm n) (hinj : ∀ i j, arm i = arm j → i = j)
    (n : ℕ) : (bLayerSys arm harm hinj).arm n = arm n := rfl

/-! ## The assembly -/

/-- A concrete binary normal sequence. -/
noncomputable def binNormal : ℕ → ℕ := digitOf 2 (Int.fract NormalNumbers.G4.Sched.fullRealW)

theorem binNormal_lt_two (m : ℕ) : binNormal m < 2 := digitOf_lt 2 (by norm_num) _ m

theorem binNormal_normal : IsNormalSequence 2 binNormal := by
  have h := NormalNumbers.G4.Sched.isNormal_two_pow_fullRealW 1 (by norm_num)
  norm_num [IsNormal] at h
  exact h

/-- **C4 for any prescribed infinite arm family.** -/
theorem c4_realizable_of_arms (h2 : ∀ n, 2 ≤ arm n) (hinj : ∀ i j, arm i = arm j → i = j) :
    ∃ s : ℕ → ℕ, (∀ m, s m < 2) ∧ ∀ L : ℕ, 1 ≤ L → (IsAbelianAt s L ↔ ∀ i, L ≠ arm i) := by
  set Ls := bLayerSys arm h2 hinj with hLs
  refine ⟨Ls.limSeq binNormal, Ls.limSeq_lt_two binNormal, fun L hL => ?_⟩
  constructor
  · intro habs i hLi
    refine Ls.limSeq_not_isAbelianAt binNormal_lt_two binNormal_normal i ?_
    rw [bLayerSys_arm, ← hLi]
    exact habs
  · intro hne
    refine Ls.limSeq_isAbelianAt binNormal_lt_two binNormal_normal L (fun i => ?_)
    rw [bLayerSys_arm]
    exact hne i

/-- **C4, hard branch.**  Every set of window lengths containing `1` is realized exactly.
(Moved here from `AbelianWindowSets.lean`, which cannot see the construction.) -/
theorem c4_realizable_of_mem_one (S : Set ℕ) (hS : ∀ L ∈ S, 1 ≤ L) (h1 : 1 ∈ S) :
    ∃ s : ℕ → ℕ, (∀ m, s m < 2) ∧ ∀ L : ℕ, 1 ≤ L → (IsAbelianAt s L ↔ L ∈ S) := by
  classical
  set p : ℕ → Prop := fun L => 2 ≤ L ∧ L ∉ S with hp
  have hkey : ∀ L, 1 ≤ L → (¬ p L ↔ L ∈ S) := by
    intro L hL
    constructor
    · intro h
      by_contra hns
      refine h ⟨?_, hns⟩
      rcases Nat.lt_or_ge L 2 with h2 | h2
      · exact absurd (show L ∈ S from by rw [show L = 1 from by omega]; exact h1) hns
      · exact h2
    · intro hmem hc
      exact hc.2 hmem
  rcases Set.finite_or_infinite (Set.ofPred p) with hfin | hinf
  · obtain ⟨s, hs2, hs⟩ := c4_realizable_of_finite_compl hfin.toFinset (fun a ha => by
      rw [Set.Finite.mem_toFinset] at ha
      exact ha.1)
    refine ⟨s, hs2, fun L hL => ?_⟩
    rw [hs L hL, Set.Finite.mem_toFinset]
    exact hkey L hL
  · set arm : ℕ → ℕ := Nat.nth p with harmdef
    have h2 : ∀ n, 2 ≤ arm n := fun n => (Nat.nth_mem_of_infinite hinf n).1
    have hinj : ∀ i j, arm i = arm j → i = j := fun i j h => Nat.nth_injective hinf h
    obtain ⟨s, hs2, hs⟩ := c4_realizable_of_arms arm h2 hinj
    refine ⟨s, hs2, fun L hL => ?_⟩
    rw [hs L hL]
    constructor
    · intro hne
      refine (hkey L hL).mp (fun hpL => ?_)
      obtain ⟨i, hi⟩ := Nat.subset_range_nth (p := p) hpL
      exact hne i hi.symm
    · intro hmem i hLi
      have hmm : p (arm i) := Nat.nth_mem_of_infinite hinf i
      rw [← hLi] at hmm
      exact hmm.2 hmem

/-- **C4 (ratified headline).**  Every admissible set of window lengths is realized exactly. -/
theorem c4_realizable (S : Set ℕ) (hS : ∀ L ∈ S, 1 ≤ L) (hadm : S = ∅ ∨ 1 ∈ S) :
    ∃ s : ℕ → ℕ, (∀ m, s m < 2) ∧ ∀ L : ℕ, 1 ≤ L → (IsAbelianAt s L ↔ L ∈ S) := by
  rcases hadm with rfl | h1
  · refine ⟨fun _ => 0, fun m => by norm_num, fun L hL => ?_⟩
    simp only [Set.mem_empty_iff_false, iff_false]
    exact not_isAbelianAt_zero_fun L hL
  · exact c4_realizable_of_mem_one S hS h1
