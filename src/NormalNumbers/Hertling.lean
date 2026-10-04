/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBad
import NormalNumbers.NormalMeager
import NormalNumbers.ReciprocalNormal

/-!
# Bugeaud 10.31 (Hertling): rich exactly on a dependence-closed set of bases — audit

**Source.**  Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, Cambridge
Tracts in Math. 193 (2012), p. 220, verbatim:

> Hertling [342] asked whether Schmidt's Theorem 6.3 has an analogue with normality replaced by
> richness.
> **Problem 10.31.** Let R ∪ S be a partition of the set of integers greater than or equal to 2
> into two classes such that any two multiplicatively dependent integers fall in the same class.
> There are real numbers which are rich to every base from R but not rich to every base from S.

"Not rich to every base from S" means rich to *no* base of `S` (the same idiom as Theorem 6.3,
"normal to every base from R but not normal to every base from S").  Hertling's original
question (P. Hertling, *Disjunctive ω-words and real numbers*, Informatik-Berichte 180,
FernUni Hagen 1995, §2; J.UCS 2 (1996) 549–568): "Let A, B be two disjoint classes of possible
bases with {2, 3, …} = A ∪ B such that equivalent bases lie in the same class.  Then the set of
real numbers that are normal to all bases in A and not normal to all bases in B has the
cardinality of the continuum.  The author does not know whether a similar result is true for
disjunctive numbers."

Lean form: `bugeaud_10_31` (`∃ x, RichExactly R x` for every `DepClosed R`).

## Audit verdict (2026-10-03): below the 40% bar; recorded here, not run

* **Truth of 10.31**: likely (≈ 85%).  **This repo proving it in 2–4 laps: ≈ 12%.**
* **What is in the kernel** (no `sorry`):
  - the known-false sibling: a non-closed `R` has no witness
    (`not_exists_richExactly_of_not_depClosed`, concretely `not_exists_richExactly_two`:
    rich in 2 ⟺ rich in 4);
  - the corners `R = ∅` (`richExactly_empty`, from the 10.36 engine) and `R = all`
    (`richExactly_univ`, Calude–Zamfirescu residuality);
  - the **reduction** `richExactly_of_blockForcing`: the whole problem follows from one
    block-forcing statement `BlockForcing` about the 10.36 engine's tree of good windows,
    restricted to the obstacles of the bases in `S`;
  - `depClosed_of_blockForcing`: `BlockForcing` itself refutes on non-closed `R`, so the
    hypothesis is not decorative.
* **The single open node** is `blockForcing` (`sorry`).  `bugeaud_10_31` is proved from it.

## Why `blockForcing` is the crux, and why it is not elementary

A good window `W` (potential `< θ` for the `S`-obstacles of radius `s^{−n−24}`) must have a
good descendant inside an `r`-adic cylinder `[u D]_r` for a prescribed block `D` of length `L`.
* **Free steps are cheap**: at most `≈ 22` of the 64 children of a good window are bad
  (`Σ_j old_j ≤ 2√K Φ`, bad means `old_j ≥ θ − A`), so the good tree branches ≥ 41/64.
* **Forcing is not**: inside `D` there are `≈ L log r / log s − 24` base-`s` levels whose
  obstacles are *larger* than the target cylinder (fatal if met), for every active `s`.
  - Union bound over placements `u`: fatal fraction `≈ 2 s^{−24} · L log_s r` per base, which
    exceeds 1 once `L ≳ s^{24}`.  Since `L → ∞` and the constant `24` (or any per-base `c_s`,
    fixed once `s` is active) cannot grow, the union bound fails for every `s` eventually.
  - The true survival fraction should be `≈ ∏_s (1 − 2s^{−24})^{L log_s r}`, but that needs the
    base-`s` digit strings of the placements `x_u = (u r^L + D)/r^{m+L}` to be *jointly*
    equidistributed at resolution `≈ r^{−L}` while `u` ranges over a window, not over all
    residues mod `r^m`.  By Erdős–Turán this asks `‖h sⁿ / r^{m}‖ ≫ r^{−p}` for all `h ≲ r^L`,
    a statement about the low `r`-adic digits of `sⁿ`.  That is a Schmidt-lemma-type
    (`×r` vs `×s`) independence input, needed at every scale and uniformly over infinitely
    many `s`.  Nothing in this repo supplies it (`CantorLiouville` handles base 3 only).
  - Pure counting cannot replace it: the good tree may have Lebesgue-density
    `(41/64)^{depth}`, far below the `r^{−L}` density of the `D`-cylinders, so pigeonhole
    gives nothing.
* **Dead ends checked**: Baire inside the good-window Cantor set reduces to the same lemma;
  Hertling/Bugeaud Liouville-type sums `Σ c_j/b^{n_j}` make every base independent of `b`
  rich, so they cannot separate two infinite classes; measures on `⋂_{s∈S} Bad_s` with Fourier
  decay along `r^m` are the open `×s₁ ×s₂` Fourier problem (and full decay is impossible:
  Davenport–Erdős–LeVeque would make `S`-points normal in `S`).

## Prior art (searched 2026-10-03)

* `R = ∅`: Bugeaud, Rev. Mat. Iberoam. 28 (2012), Thm 2.1 (entropy `< log b` for every `b`,
  via Schmidt games); also the repo's 10.36 engine.  `R = all`: Calude–Zamfirescu 1999;
  Bugeaud 2012 Thm 2.2 (explicit).
* `S` = one class: Hertling 1996, `Σ_{j≥1} r^{−j!−j}` (`Literature.hertling1996_factorial`).
* Two bases only: El-Zanati–Transue; Bergelson–Einsiedler–Tseng (arXiv 1309.4823, commuting
  toral maps, full dimension).
* Normality analogues: Schmidt 1961/62 (`Literature.schmidt1961_partition`), Brown–Moran–Pearce,
  Pollington (full dimension), **Becher–Slaman, J. London Math. Soc. 2014 (arXiv 1311.0333),
  Thm 5** (`Literature.becherSlaman2014_thm5`): normal to `R`, not *simply* normal to any base
  of `S`.  Their `S`-module visits each `s` infinitely often and omits the digit `s − 1` only
  during the stages devoted to `s`.  Between those stages the base-`s` digits are
  unconstrained, so the construction does not prevent richness in `S`.  Not normal does not
  imply not rich: `exists_rich_and_not_normal_everywhere`.
* Not addressing richness: Becher–Bugeaud–Slaman, *The irrationality exponents of computable
  numbers* (arXiv 1410.1017); Bugeaud–Moshchevitin (arXiv 0905.0830); Temur, arXiv 2609.16362
  (Problem 10.53).
* Instruments: the book's text, the RMI paper, Hertling's 1995 report and Becher–Slaman,
  read in full; arXiv API; about six web searches.  No paper claiming 10.31 was found.
  Forward citations of Hertling 1996 were not enumerated.
-/

open scoped ENNReal

namespace NormalNumbers.Hertling

open NormalNumbers NormalNumbers.UniformBad

/-! ## Statement -/

/-- Multiplicative dependence of two bases: `a^m = b^n` for some `m, n ≥ 1`. -/
def MulDep (a b : ℕ) : Prop := ∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧ a ^ m = b ^ n

/-- Hertling's hypothesis: any two multiplicatively dependent bases lie on the same side. -/
def DepClosed (R : Set ℕ) : Prop :=
  ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → MulDep a b → (a ∈ R ↔ b ∈ R)

/-- `x` is rich (disjunctive) to exactly the bases `b ≥ 2` lying in `R`. -/
def RichExactly (R : Set ℕ) (x : ℝ) : Prop :=
  ∀ b : ℕ, 2 ≤ b → (IsDisjunctive b x ↔ b ∈ R)

/-! ## Guards and corners (proved) -/

/-- Richness is invariant along multiplicative dependence (`isDisjunctive_pow_iff` twice). -/
theorem isDisjunctive_iff_of_mulDep {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (h : MulDep a b)
    (x : ℝ) : IsDisjunctive a x ↔ IsDisjunctive b x := by
  obtain ⟨m, n, hm, hn, he⟩ := h
  rw [isDisjunctive_pow_iff a m ha hm x, he, ← isDisjunctive_pow_iff b n hb hn x]

/-- A witness forces Hertling's hypothesis. -/
theorem depClosed_of_richExactly {R : Set ℕ} {x : ℝ} (h : RichExactly R x) : DepClosed R := by
  intro a b ha hb hab
  rw [← h a ha, ← h b hb]
  exact isDisjunctive_iff_of_mulDep ha hb hab x

/-- **Known-false sibling.**  A partition splitting a dependence class has no witness. -/
theorem not_exists_richExactly_of_not_depClosed {R : Set ℕ} (hR : ¬ DepClosed R) :
    ¬ ∃ x, RichExactly R x := fun ⟨_, hx⟩ => hR (depClosed_of_richExactly hx)

/-- Concretely: no real is rich in base 2 and in no other base (rich in 2 ⟺ rich in 4). -/
theorem not_exists_richExactly_two : ¬ ∃ x, RichExactly {2} x := by
  refine not_exists_richExactly_of_not_depClosed fun h => ?_
  have := h 2 4 le_rfl (by norm_num) ⟨2, 1, by norm_num, le_rfl, by norm_num⟩
  simp at this

/-- Corner `R = ∅`: rich to no base (the 10.36 engine, `exists_irrational_not_isDisjunctive`;
also Bugeaud, RMI 2012, Thm 2.1). -/
theorem richExactly_empty : ∃ x, RichExactly ∅ x := by
  obtain ⟨ξ, -, h⟩ := exists_irrational_not_isDisjunctive
  refine ⟨ξ, fun b hb => ?_⟩
  simp only [Set.mem_empty_iff_false, iff_false]
  exact h b hb

/-- Corner `R = all bases`: rich to every base (Calude–Zamfirescu residuality). -/
theorem richExactly_univ : ∃ x, RichExactly Set.univ x := by
  obtain ⟨x, hx, -⟩ := exists_absolutelyDisjunctive_forall_not_isNormal
  exact ⟨x, fun b hb => by simp only [Set.mem_univ, iff_true]; exact hx b hb⟩

/-- **Why the normality literature does not answer 10.31**: failing normality does not prevent
richness.  One real is rich to every base and normal to none. -/
theorem exists_rich_and_not_normal_everywhere :
    ∃ x : ℝ, ∀ b : ℕ, 2 ≤ b → IsDisjunctive b x ∧ ¬ IsNormal b x := by
  obtain ⟨x, hx, hn⟩ := exists_absolutelyDisjunctive_forall_not_isNormal
  exact ⟨x, fun b hb => ⟨hx b hb, hn b hb⟩⟩

/-! ## The `S`-restricted 10.36 obstacle family -/

/-- Obstacle indices `(b, n, a)` of the 10.36 family whose base lies in `S`. -/
abbrev IdxOn (S : Set ℕ) := {p : Idx // p.1.1 ∈ S}

/-- Centre of an `S`-obstacle. -/
noncomputable def ctrOn (S : Set ℕ) (p : IdxOn S) : ℝ := ctr p.1

/-- Radius `b^{−(n+24)}` of an `S`-obstacle. -/
noncomputable def radOn (S : Set ℕ) (p : IdxOn S) : ℝ := rad p.1

/-- Early-charging stage of an `S`-obstacle. -/
def stageOn (S : Set ℕ) (p : IdxOn S) : ℕ := stage p.1

/-- The engine potential (`ℓ₀ = 1/2`, `K = 64`) of the `S`-obstacles. -/
noncomputable def potOn (S : Set ℕ) (P : ℕ → Prop) (k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  potential (ctrOn S) (radOn S) (stageOn S) (1 / 2) 64 P k x

/-- Restricting to `S` lowers the potential. -/
theorem potOn_le (S : Set ℕ) (P : ℕ → Prop) (k : ℕ) (x : ℝ) :
    potOn S P k x ≤ potential ctr rad stage (1 / 2) 64 P k x :=
  ENNReal.tsum_comp_le_tsum_of_injective
    (f := fun i : {i : IdxOn S // P (stageOn S i) ∧
        (obstacle (ctrOn S) (radOn S) i ∩ window (1 / 2) 64 k x).Nonempty} =>
      (⟨i.1.1, i.2.1, i.2.2⟩ :
        {i : Idx // P (stage i) ∧ (obstacle ctr rad i ∩ window (1 / 2) 64 k x).Nonempty}))
    (fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z => z.1) h :)))
    (fun i => ENNReal.ofReal (Real.sqrt (rad i / (1 / 2 / ((64 : ℕ) : ℝ) ^ k))))

theorem newPotOn_le (S : Set ℕ) (k : ℕ) (x : ℝ) :
    potOn S (· = k) k x ≤ ENNReal.ofReal (1 / 40) :=
  (potOn_le S _ k x).trans (newPotential_le k x)

theorem radOn_pos (S : Set ℕ) (p : IdxOn S) : 0 < radOn S p := rad_pos p.1

/-! ## The open node: block forcing -/

/-- **Block forcing** for the partition `(R, S)`.  Below every good window of the `S`-restricted
10.36 engine (carried potential `< θ`) there is a strictly deeper good window all of whose
points contain a prescribed base-`r` block, for every `r ∈ R`.

Windows need not be children: one forcing may jump many stages.  The engine only needs good
windows at a cofinal set of stages (`richExactly_of_blockForcing`). -/
def BlockForcing (S R : Set ℕ) : Prop :=
  ∀ (k : ℕ) (x : ℝ), potOn S (· ≤ k) k x < theta 64 →
    ∀ r ∈ R, 2 ≤ r → ∀ D : List ℕ, (∀ d ∈ D, d < r) →
      ∃ k' x', k < k' ∧ window (1 / 2) 64 k' x' ⊆ window (1 / 2) 64 k x ∧
        potOn S (· ≤ k') k' x' < theta 64 ∧
        ∀ y ∈ window (1 / 2) 64 k' x', ∃ n, OccursAt r y D n

/-- **The crux (open).**  Block forcing holds for every dependence-closed partition.

Confidence that it is true as stated (fixed `C = 24`, `K = 64`): 65%.  Confidence that this
repo proves it in 2–4 laps: 12%.

English sketch, with the gap marked.  Given a good window `W` of length `ℓ`, descend freely
(`potential_step`) into an `r`-adic cylinder `[w]` of level `m₀`.  Consider the placements
`C_u = [w u D]` for `u` ranging over the `r^p` words of length `p ≥ 2L`.  Their positions are
`r^{−m₀−p}`-spaced, so an obstacle of radius `ρ` kills at most `2ρ r^{m₀+p} + 2` placements.
(i) Old obstacles (carried in `Φ(W) < θ`) kill a fraction `≤ 2Σ t_i² + 2θ r^{(L−p)/2} < 1/4`.
Their small members add `≤ 2θ r^{(L−p)/2}` to the expected potential.
(ii) Obstacles at base-`s` levels with `s^{−n} ∈ [λ s^{24}, ℓ]`, where `λ = r^{−m₀−p−L}`, are
fatal.  At free levels (`s^{−n} ≥ r^{−m₀−p}`) they kill a measure-proportional fraction
`≈ 2s^{−24}` per level.  **GAP**: at the `≈ L log_s r − 24` levels inside `D`, the fraction of
placements killed is `2s^{−24}` per level only if `{u sⁿ/r^{m₀+p}}` is equidistributed.  Even
then the union bound over levels exceeds 1 once `L ≳ s^{24}`.  One needs either joint
equidistribution of the base-`s` digit strings of the `x_u` at resolution `r^{−L}`, which is a
Schmidt-lemma-type `×r ×s` input, or a different obstacle shape for `S`. -/
theorem blockForcing (R : Set ℕ) (hR : DepClosed R) : BlockForcing {b | b ∉ R} R := by
  sorry

/-! ## The reduction (proved): block forcing ⟹ 10.31 -/

/-- One construction step: a strictly deeper good sub-window, which also meets the requirement
`q = (r, D)` when that requirement is valid. -/
theorem exists_next {R : Set ℕ} (hF : BlockForcing {b | b ∉ R} R) {k : ℕ} {x : ℝ}
    (hk : potOn {b | b ∉ R} (· ≤ k) k x < theta 64) (q : ℕ × List ℕ) :
    ∃ k' x', k < k' ∧ window (1 / 2) 64 k' x' ⊆ window (1 / 2) 64 k x ∧
      potOn {b | b ∉ R} (· ≤ k') k' x' < theta 64 ∧
      ((q.1 ∈ R ∧ 2 ≤ q.1 ∧ ∀ d ∈ q.2, d < q.1) →
        ∀ y ∈ window (1 / 2) 64 k' x', ∃ n, OccursAt q.1 y q.2 n) := by
  by_cases hq : q.1 ∈ R ∧ 2 ≤ q.1 ∧ ∀ d ∈ q.2, d < q.1
  · obtain ⟨k', x', hkk, hsub, hgood, hocc⟩ := hF k x hk q.1 hq.1 hq.2.1 q.2 hq.2.2
    exact ⟨k', x', hkk, hsub, hgood, fun _ => hocc⟩
  · obtain ⟨j, hj, hgood⟩ := potential_step (ctrOn {b | b ∉ R}) (radOn {b | b ∉ R})
      (stageOn {b | b ∉ R}) (K := 64) (by norm_num) (ℓ₀ := 1 / 2) (A := 1 / 40) (by norm_num)
      one_fortieth_le_threshold (newPotOn_le _) hk
    refine ⟨k + 1, x + j * (1 / 2 / ((64 : ℕ) : ℝ) ^ (k + 1)), Nat.lt_succ_self k, ?_, hgood,
      fun h => absurd h hq⟩
    intro y hy
    simp only [window, Set.mem_Icc] at hy ⊢
    have hℓ : (0 : ℝ) < 1 / 2 / ((64 : ℕ) : ℝ) ^ (k + 1) := by positivity
    have hj' : (j : ℝ) + 1 ≤ 64 := by exact_mod_cast hj
    have hsplit : (1 / 2 : ℝ) / ((64 : ℕ) : ℝ) ^ k = 64 * (1 / 2 / ((64 : ℕ) : ℝ) ^ (k + 1)) := by
      rw [pow_succ]; push_cast; field_simp
    constructor
    · nlinarith [mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) hℓ.le]
    · rw [hsplit]; nlinarith

/-- A point in a good window deep enough, at a stage after the obstacle's own, is not in the
obstacle.  (The tail of `exists_avoid_of_stagePotential`, factored out.) -/
theorem not_mem_obstacle_of_good {ι : Type*} (c r : ι → ℝ) (st : ι → ℕ) {K : ℕ} (hK : 5 ≤ K)
    {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (i : ι) {k : ℕ} (hk : st i ≤ k)
    (hbig : ℓ₀ < 2 * K * r i * (K : ℝ) ^ k) {x ξ : ℝ} (hξ : ξ ∈ window ℓ₀ K k x)
    (hgood : potential c r st ℓ₀ K (· ≤ k) k x < theta K) : ξ ∉ obstacle c r i := by
  intro hi
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hθpos : (0 : ℝ) < 1 / Real.sqrt (2 * K) := by positivity
  have hterm := term_le_potential c r st ℓ₀ K (P := (· ≤ k)) i hk hi hξ
  have hlt := lt_of_le_of_lt hterm hgood
  rw [theta, ENNReal.ofReal_lt_ofReal_iff hθpos] at hlt
  have hbig' : 1 / (2 * K) < r i / (ℓ₀ / (K : ℝ) ^ k) := by
    rw [lt_div_iff₀ (div_pos hℓ₀ (pow_pos hKpos k)), div_mul_div_comm, one_mul,
      div_lt_iff₀ (by positivity)]
    nlinarith
  have hsq : Real.sqrt (1 / (2 * K)) < Real.sqrt (r i / (ℓ₀ / (K : ℝ) ^ k)) :=
    Real.sqrt_lt_sqrt (by positivity) hbig'
  rw [Real.sqrt_div zero_le_one, Real.sqrt_one] at hsq
  linarith

/-- Avoiding the obstacle at `a = round(bⁿξ)` is the inequality `‖bⁿξ‖ > b^{−24}`.  (The
wiring step of `exists_uniformBad_allBases_24`, factored out.) -/
theorem dnear_gt_of_not_mem {ξ : ℝ} {b n : ℕ} (hb : 2 ≤ b)
    (h : ξ ∉ obstacle ctr rad (⟨(b, n, round ((b : ℝ) ^ n * ξ)), hb⟩ : Idx)) :
    (b : ℝ) ^ (-(24 : ℝ)) < dnear ((b : ℝ) ^ n * ξ) := by
  have hbpos : (0 : ℝ) < b := by positivity
  have hbn : (0 : ℝ) < (b : ℝ) ^ n := pow_pos hbpos n
  simp only [obstacle, ctr, rad, Set.mem_Icc, not_and_or, not_le] at h
  have hrpow : (b : ℝ) ^ (-(24 : ℝ)) = ((b : ℝ) ^ 24)⁻¹ := by
    rw [Real.rpow_neg hbpos.le]; norm_cast
  rw [hrpow, dnear]
  have hpow : ((b : ℝ) ^ (n + 24))⁻¹ * (b : ℝ) ^ n = ((b : ℝ) ^ 24)⁻¹ := by
    rw [pow_add]; field_simp
  set m : ℝ := (round ((b : ℝ) ^ n * ξ) : ℝ)
  have e1 : (b : ℝ) ^ n * (m / (b : ℝ) ^ n) = m := by field_simp
  have e2 : (b : ℝ) ^ n * ((b : ℝ) ^ (n + 24))⁻¹ = ((b : ℝ) ^ 24)⁻¹ := by
    rw [mul_comm]; exact hpow
  have hinv : 0 < ((b : ℝ) ^ 24)⁻¹ := by positivity
  rcases h with h | h
  · have := mul_lt_mul_of_pos_left h hbn
    rw [mul_sub, e1, e2] at this
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  · have := mul_lt_mul_of_pos_left h hbn
    rw [mul_add, e1, e2] at this
    rw [abs_of_pos (by linarith)]
    linarith

/-- **Reduction (proved).**  Block forcing for `(R, complement)` gives a real rich to exactly
the bases of `R`.

Proof: enumerate the requirements `q = (r, D)` (`Denumerable (ℕ × List ℕ)`).  Starting from the
engine's root window `[1/4, 3/4]`, apply `exists_next` once per requirement.  This gives nested
good windows at strictly increasing stages; their left ends increase to a point `ξ` in every
window.  Every `S`-obstacle misses `ξ` (`not_mem_obstacle_of_good` at a deep enough window),
so `‖sⁿξ‖ > s^{−24}` for every `s ∉ R` and `ξ` is not rich there.  Every valid `(r, D)` with
`r ∈ R` was forced at its step, so `ξ` is rich to every base of `R`. -/
theorem richExactly_of_blockForcing {R : Set ℕ} (hF : BlockForcing {b | b ∉ R} R) :
    ∃ x, RichExactly R x := by
  classical
  set S : Set ℕ := {b | b ∉ R} with hSdef
  set ℓ : ℕ → ℝ := fun k => 1 / 2 / ((64 : ℕ) : ℝ) ^ k with hℓdef
  have hℓpos : ∀ k, 0 < ℓ k := fun k => by simp only [hℓdef]; positivity
  have h0 : potOn S (· ≤ 0) 0 (1 / 4) < theta 64 := by
    have hθ : ENNReal.ofReal (1 / 40) < theta 64 := by
      rw [theta, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      have h1 := one_fortieth_le_threshold
      have h2 : (1 - 2 / Real.sqrt ((64 : ℕ) : ℝ)) / Real.sqrt (2 * ((64 : ℕ) : ℝ)) <
          1 / Real.sqrt (2 * ((64 : ℕ) : ℝ)) :=
        div_lt_div_of_pos_right (by have : 0 < 2 / Real.sqrt ((64 : ℕ) : ℝ) := by positivity
                                    linarith) (by positivity)
      linarith
    calc potOn S (· ≤ 0) 0 (1 / 4) ≤ potOn S (· = 0) 0 (1 / 4) :=
          potential_mono _ _ _ _ _ (fun n hn => Nat.le_zero.mp hn) 0 _
      _ ≤ ENNReal.ofReal (1 / 40) := newPotOn_le S 0 _
      _ < theta 64 := hθ
  -- the construction
  let St := {p : ℕ × ℝ // potOn S (· ≤ p.1) p.1 p.2 < theta 64}
  let seq : ℕ → St := fun j => Nat.rec (motive := fun _ => St) ⟨(0, 1 / 4), h0⟩
    (fun j s => ⟨(Classical.choose (exists_next hF s.2 (Denumerable.ofNat (ℕ × List ℕ) j)),
        Classical.choose (Classical.choose_spec
          (exists_next hF s.2 (Denumerable.ofNat (ℕ × List ℕ) j)))),
      (Classical.choose_spec (Classical.choose_spec
          (exists_next hF s.2 (Denumerable.ofNat (ℕ × List ℕ) j)))).2.2.1⟩) j
  set k : ℕ → ℕ := fun j => (seq j).1.1 with hkdef
  set x : ℕ → ℝ := fun j => (seq j).1.2 with hxdef
  have hgood : ∀ j, potOn S (· ≤ k j) (k j) (x j) < theta 64 := fun j => (seq j).2
  have hspec : ∀ j, k j < k (j + 1) ∧
      window (1 / 2) 64 (k (j + 1)) (x (j + 1)) ⊆ window (1 / 2) 64 (k j) (x j) ∧
      ((let q := Denumerable.ofNat (ℕ × List ℕ) j
        (q.1 ∈ R ∧ 2 ≤ q.1 ∧ ∀ d ∈ q.2, d < q.1) →
        ∀ y ∈ window (1 / 2) 64 (k (j + 1)) (x (j + 1)), ∃ n, OccursAt q.1 y q.2 n)) := by
    intro j
    have := Classical.choose_spec (Classical.choose_spec
      (exists_next hF (seq j).2 (Denumerable.ofNat (ℕ × List ℕ) j)))
    exact ⟨this.1, this.2.1, this.2.2.2⟩
  have hkmono : StrictMono k := strictMono_nat_of_lt_succ fun j => (hspec j).1
  have hnest : ∀ j m, j ≤ m →
      window (1 / 2) 64 (k m) (x m) ⊆ window (1 / 2) 64 (k j) (x j) := by
    intro j m hjm
    induction m, hjm using Nat.le_induction with
    | base => exact le_rfl
    | succ m _ ih => exact (hspec m).2.1.trans ih
  have hxwin : ∀ j, x j ∈ window (1 / 2) 64 (k j) (x j) := fun j =>
    ⟨le_rfl, by have := hℓpos (k j); simp only [hℓdef] at this; linarith⟩
  -- the limit point
  have hbdd : BddAbove (Set.range x) := by
    refine ⟨x 0 + ℓ (k 0), ?_⟩
    rintro _ ⟨j, rfl⟩
    exact (hnest 0 j (Nat.zero_le j) (hxwin j)).2
  set ξ := ⨆ j, x j with hξ
  have hξwin : ∀ j, ξ ∈ window (1 / 2) 64 (k j) (x j) := by
    intro j
    refine ⟨le_ciSup hbdd j, ciSup_le fun m => ?_⟩
    rcases le_total j m with hjm | hmj
    · exact (hnest j m hjm (hxwin m)).2
    · have := (hnest m j hmj (hxwin j)).1
      have := hℓpos (k j); simp only [hℓdef] at this
      linarith
  refine ⟨ξ, fun b hb => ⟨fun hrich => ?_, fun hbR => ?_⟩⟩
  · -- not rich off `R`
    by_contra hbR
    apply not_isDisjunctive_of_uniformBad (c := 24) hb _ hrich
    intro n
    apply dnear_gt_of_not_mem hb
    set i : IdxOn S := ⟨⟨(b, n, round ((b : ℝ) ^ n * ξ)), hb⟩, hbR⟩
    have hri : 0 < radOn S i := radOn_pos S i
    obtain ⟨k₁, hk₁⟩ := pow_unbounded_of_one_lt ((1 / 2 : ℝ) / (2 * (64 : ℕ) * radOn S i))
      (by norm_num : (1 : ℝ) < ((64 : ℕ) : ℝ))
    set j := max k₁ (stageOn S i)
    have hkj : j ≤ k j := hkmono.id_le j
    have hK : ((64 : ℕ) : ℝ) ^ k₁ ≤ ((64 : ℕ) : ℝ) ^ k j :=
      pow_le_pow_right₀ (by norm_num) ((le_max_left _ _).trans hkj)
    have hbig : (1 / 2 : ℝ) < 2 * (64 : ℕ) * radOn S i * ((64 : ℕ) : ℝ) ^ k j := by
      rw [div_lt_iff₀ (by positivity)] at hk₁
      have h2Kr : (0 : ℝ) ≤ 2 * (64 : ℕ) * radOn S i := mul_nonneg (by norm_num) hri.le
      have hm := mul_le_mul_of_nonneg_left hK h2Kr
      rw [mul_comm] at hk₁
      exact hk₁.trans_le hm
    exact not_mem_obstacle_of_good (ctrOn S) (radOn S) (stageOn S) (K := 64) (by norm_num)
      (by norm_num) i ((le_max_right _ _).trans hkj) hbig (hξwin j) (hgood j)
  · -- rich on `R`
    rw [isDisjunctive_iff_forall_occursAt b hb]
    intro D hD
    set j := Encodable.encode (b, D)
    have hq : Denumerable.ofNat (ℕ × List ℕ) j = (b, D) := Denumerable.ofNat_encode _
    have := (hspec j).2.2
    simp only [hq] at this
    exact this ⟨hbR, hb, hD⟩ ξ (hξwin (j + 1))

/-- **`BlockForcing` refutes on a non-closed `R`** (through the reduction and the guard), so
`blockForcing`'s hypothesis carries weight. -/
theorem depClosed_of_blockForcing {R : Set ℕ} (hF : BlockForcing {b | b ∉ R} R) :
    DepClosed R := by
  obtain ⟨x, hx⟩ := richExactly_of_blockForcing hF
  exact depClosed_of_richExactly hx

/-- **Bugeaud 2012, Problem 10.31 (Hertling).**  For every partition of the bases closed under
multiplicative dependence, some real is rich to every base of `R` and to no base outside it.

Proved from the open node `blockForcing` by `richExactly_of_blockForcing`.  Confidence that the
statement is true: 85%. -/
theorem bugeaud_10_31 (R : Set ℕ) (hR : DepClosed R) : ∃ x : ℝ, RichExactly R x :=
  richExactly_of_blockForcing (blockForcing R hR)

end NormalNumbers.Hertling

/-! ## Literature inputs (cited, not used by any proof above) -/

namespace NormalNumbers.Literature

open NormalNumbers NormalNumbers.Hertling

/-- **Schmidt 1961/62** (Bugeaud 2012, Theorem 6.3): for a dependence-closed partition, some
real is normal to every base of `R` and to no base outside it.  (The book states that the set
of such reals is uncountable; this is the weaker existence form.) -/
def schmidt1961_partition : Prop :=
  ∀ R : Set ℕ, DepClosed R → ∃ x : ℝ, ∀ b : ℕ, 2 ≤ b → (IsNormal b x ↔ b ∈ R)

/-- **Becher–Slaman, J. London Math. Soc. 2014 (arXiv 1311.0333), Theorem 5**: for `R` closed
under multiplicative dependence, some real is normal to every base of `R` and not simply
normal to any base in its complement. -/
def becherSlaman2014_thm5 : Prop :=
  ∀ R : Set ℕ, DepClosed R → ∃ x : ℝ, ∀ b : ℕ, 2 ≤ b →
    (b ∈ R → IsNormal b x) ∧ (b ∉ R → ¬ ReciprocalNormal.IsSimplyNormal b x)

/-- **Hertling 1996** (J.UCS 2; Bugeaud 2012, Notes 5.6, p. 117): for `r ≥ 2` the real
`Σ_{j≥1} r^{−j!−j}` is not rich to base `r` but is rich to every base multiplicatively
independent of `r`.  This is 10.31 when `S` is a single dependence class. -/
def hertling1996_factorial : Prop :=
  ∀ r : ℕ, 2 ≤ r →
    let x : ℝ := ∑' j : ℕ, ((r : ℝ) ^ ((j + 1).factorial + (j + 1)))⁻¹
    ¬ IsDisjunctive r x ∧ ∀ s : ℕ, 2 ≤ s → ¬ MulDep s r → IsDisjunctive s x

/-- **Wired edge**: Hertling's single-class theorem is the case `S = [r]` of 10.31. -/
theorem richExactly_singleClass_of_hertling (h : hertling1996_factorial) {r : ℕ} (hr : 2 ≤ r) :
    ∃ x : ℝ, RichExactly {b | ¬ MulDep b r} x := by
  obtain ⟨hnot, hrich⟩ := h r hr
  refine ⟨_, fun b hb => ⟨fun hbx hdep => hnot ?_, fun hind => hrich b hb hind⟩⟩
  exact (isDisjunctive_iff_of_mulDep hb hr hdep _).1 hbx

end NormalNumbers.Literature
