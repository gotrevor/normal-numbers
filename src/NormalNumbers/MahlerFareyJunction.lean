/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerNumCert

/-!
# The Farey junction: two backgrounds `(p+1)/2` and `(p+3)/2` 🧮

Every junction certificate so far (`MahlerBackgroundCert.lean`, `MahlerTwoJunction.lean`)
lives over ONE background `1/D` and re-enters the orbit with an offset `b/(pD)`; the
offset is what the drift analysis charges, and it caps the constant at `1/5` for two
junctions and `D/(2p) ≤ 1/4` for one (with the Linnik-strength orbit condition on `D`).

The exact census (`docs/mahler-exact-values-2026-09-07.md`) shows `M(p,1) = ⌊p/2⌋² − {0,1,2,4}`,
and the trimmed-product SCC at `p = 19` (`experiments/mahler_exact_M.py`) reveals the
construction: TWO backgrounds `D₁ = (p+1)/2` and `D₂ = (p+3)/2`, Farey neighbours, and
junctions that land EXACTLY on the other background — the perturbation `1/(p D₁ D₂)` is
injected one step before the junction, never an offset `b/(pD)`.  The first failing channel
is then `m = D₁ (p − D₂) = (p+1)(p−3)/4 = ⌊p/2⌋² − 1`.

Writing `p = 2k − 1`, `D₁ = k`, `D₂ = k + 1`, `E = p k (k+1)`, slack `σ = 1`:

* far states `F₁(a) = a/k` (`a < k`) and `F₂(a) = a/(k+1)` (`a ≤ k`), digit `⌊ap/D⌋`,
  successor `F(pa mod D)`;
* `J₁ = 1/k + 1/E` (numerator `p(k+1) + 1`), digit `1`, successor `F₂(k) = −1/(k+1)`;
* `J₂ = a₂/(k+1) + 1/E` (numerator `a₂ p k + 1`) with `a₂ p ≡ 1 (mod k+1)`, digit
  `⌊a₂ p/(k+1)⌋`, successor `F₁(1)`;
* the injections `F₁(k−1) → J₁` (digit `p − 2`) and `F₂(a) → J₂` for `pa ≡ a₂`.

`p ≡ −1 (mod k)` closes the `F₁` side for free (`1 → −1 → 1`).  The `F₂` side lands at
`−1` and must reach `a₂ = p⁻¹`: with `p^s ≡ −1 (mod k+1)` the walk is
`−1 = p^s → p^{s+1} → … → p^{2s−2} → J₂`.

**Relation to family I.**  `MahlerFamilyI.lean` proves the same bound `⌊p/2⌋² − 2` under
the same hypothesis: its near state `N₀ = 1/D + 2/(pD)` IS `J₁ = 1/k + 1/E` (Farey:
`1/k = 1/(k+1) + 1/(k(k+1))`), so family I is secretly this two-background certificate
with `D₁ = (p+1)/2` hidden.  This file makes both backgrounds explicit, which is the form
that generalises: the **general junction rule** is that any two coprime backgrounds
`D → D'` are joined by an exact landing from `−1/(pD') (mod D)` onto `1/D (mod D')`, at
cost `m < D'(p − D)`, and the orbit condition at a background with neighbours
`D_prev, D_next` is `p^e ≡ −D_prev/D_next (mod D)`.  For a chain `k, k+1, …, k+t`
(up and back down) every condition is trivial except `−1 ∈ ⟨p⟩ (mod k+t)` at the top,
with bound `k² − 2k − t²`; see `PENDING_WORK.md` §top.  Hypotheses here are weaker than
family I's (`p ≥ 5`, any `s ≥ 1`, no primality).

Main theorem: `mahler_lower_bound_farey`: for every odd `p = 2k − 1 ≥ 5` with
`p^s ≡ −1 (mod k+1)`, `M(p,1) > k² − 2k − 1 = ⌊p/2⌋² − 2`.
-/

namespace NormalNumbers.Adder.Farey

open NormalNumbers NormalNumbers.Mahler

/-! ### States -/

section states

variable (p k a₂ : ℕ)

/-- `F₁(a) = a/k`, index `a mod k`. -/
def f1 (a : ℕ) : Fin (2 * k + 3) := ⟨a % k % (2 * k + 3), Nat.mod_lt _ (by omega)⟩
/-- `F₂(a) = a/(k+1)`, index `k + (a mod (k+1))`. -/
def f2 (a : ℕ) : Fin (2 * k + 3) := ⟨(k + a % (k + 1)) % (2 * k + 3), Nat.mod_lt _ (by omega)⟩
def j1 : Fin (2 * k + 3) := ⟨2 * k + 1, by omega⟩
def j2 : Fin (2 * k + 3) := ⟨2 * k + 2, by omega⟩

/-- The common denominator `E = p k (k+1)`. -/
def E : ℕ := p * k * (k + 1)

variable {k}

theorem f1_val (a : ℕ) (hk : 0 < k) : (f1 k a).1 = a % k := by
  unfold f1; simp only; exact Nat.mod_eq_of_lt (by have := Nat.mod_lt a hk; omega)

theorem f2_val (a : ℕ) : (f2 k a).1 = k + a % (k + 1) := by
  unfold f2; simp only; exact Nat.mod_eq_of_lt (by have := Nat.mod_lt a (show 0 < k + 1 by omega); omega)

theorem f1_congr {a a' : ℕ} (h : a % k = a' % k) : f1 k a = f1 k a' := by
  unfold f1; simp only [Fin.mk.injEq]; rw [h]

theorem f2_congr {a a' : ℕ} (h : a % (k + 1) = a' % (k + 1)) : f2 k a = f2 k a' := by
  unfold f2; simp only [Fin.mk.injEq]; rw [h]

theorem f1_mod (a : ℕ) : f1 k (a % k) = f1 k a := f1_congr (Nat.mod_mod _ _)
theorem f2_mod (a : ℕ) : f2 k (a % (k + 1)) = f2 k a := f2_congr (Nat.mod_mod _ _)

variable (k)

/-- Tail numerators over `E`. -/
def num (s : Fin (2 * k + 3)) : ℕ :=
  if s.1 < k then s.1 * p * (k + 1)
  else if s.1 ≤ 2 * k then (s.1 - k) * p * k
  else if s.1 = 2 * k + 1 then p * (k + 1) + 1
  else a₂ * p * k + 1

/-- The emitted digits. -/
def dig (s : Fin (2 * k + 3)) : ℕ :=
  if s.1 < k then s.1 * p / k
  else if s.1 ≤ 2 * k then (s.1 - k) * p / (k + 1)
  else if s.1 = 2 * k + 1 then 1
  else a₂ * p / (k + 1)

/-- Successors: the two far cycles, the two injections, the two landings. -/
def nxt (s : Fin (2 * k + 3)) : List (Fin (2 * k + 3)) :=
  if s.1 < k then [f1 k (s.1 * p)] ++ (if s.1 * p % k = 1 then [j1 k] else [])
  else if s.1 ≤ 2 * k then
    [f2 k ((s.1 - k) * p)] ++ (if (s.1 - k) * p % (k + 1) = a₂ then [j2 k] else [])
  else if s.1 = 2 * k + 1 then [f2 k k]
  else [f1 k 1]

/-- The Farey-junction numerator certificate, slack `σ = 1`. -/
def cert : NumCert p where
  n := 2 * k + 3
  num := num p k a₂
  dig := dig p k a₂
  nxt := nxt p k a₂
  E := E p k
  σ := 1

variable {p k a₂}

theorem num_f1 (a : ℕ) (hk : 0 < k) : num p k a₂ (f1 k a) = (a % k) * p * (k + 1) := by
  unfold num; rw [f1_val a hk, if_pos (Nat.mod_lt _ hk)]
theorem dig_f1 (a : ℕ) (hk : 0 < k) : dig p k a₂ (f1 k a) = (a % k) * p / k := by
  unfold dig; rw [f1_val a hk, if_pos (Nat.mod_lt _ hk)]
theorem nxt_f1 (a : ℕ) (hk : 0 < k) : nxt p k a₂ (f1 k a) =
    [f1 k ((a % k) * p)] ++ (if (a % k) * p % k = 1 then [j1 k] else []) := by
  unfold nxt; rw [f1_val a hk, if_pos (Nat.mod_lt _ hk)]

theorem num_f2 (a : ℕ) : num p k a₂ (f2 k a) = (a % (k + 1)) * p * k := by
  unfold num; rw [f2_val a]
  have := Nat.mod_lt a (show 0 < k + 1 by omega)
  rw [if_neg (by omega), if_pos (by omega)]; simp
theorem dig_f2 (a : ℕ) : dig p k a₂ (f2 k a) = (a % (k + 1)) * p / (k + 1) := by
  unfold dig; rw [f2_val a]
  have := Nat.mod_lt a (show 0 < k + 1 by omega)
  rw [if_neg (by omega), if_pos (by omega)]; simp
theorem nxt_f2 (a : ℕ) : nxt p k a₂ (f2 k a) =
    [f2 k ((a % (k + 1)) * p)] ++ (if (a % (k + 1)) * p % (k + 1) = a₂ then [j2 k] else []) := by
  unfold nxt; rw [f2_val a]
  have := Nat.mod_lt a (show 0 < k + 1 by omega)
  rw [if_neg (by omega), if_pos (by omega)]; simp

theorem num_j1 : num p k a₂ (j1 k) = p * (k + 1) + 1 := by
  unfold num j1; simp only; rw [if_neg (by omega), if_neg (by omega)]; simp
theorem dig_j1 : dig p k a₂ (j1 k) = 1 := by
  unfold dig j1; simp only; rw [if_neg (by omega), if_neg (by omega)]; simp
theorem nxt_j1 : nxt p k a₂ (j1 k) = [f2 k k] := by
  unfold nxt j1; simp only; rw [if_neg (by omega), if_neg (by omega)]; simp
theorem num_j2 : num p k a₂ (j2 k) = a₂ * p * k + 1 := by
  unfold num j2; simp only; rw [if_neg (by omega), if_neg (by omega)]; simp
theorem dig_j2 : dig p k a₂ (j2 k) = a₂ * p / (k + 1) := by
  unfold dig j2; simp only; rw [if_neg (by omega), if_neg (by omega)]; simp
theorem nxt_j2 : nxt p k a₂ (j2 k) = [f1 k 1] := by
  unfold nxt j2; simp only; rw [if_neg (by omega), if_neg (by omega)]; simp

/-- Every state is `F₁(a)` (`a < k`), `F₂(a)` (`a ≤ k`), `J₁` or `J₂`. -/
theorem state_cases (hk : 0 < k) (s : Fin (2 * k + 3)) :
    (∃ a, a < k ∧ s = f1 k a) ∨ (∃ a, a ≤ k ∧ s = f2 k a) ∨ s = j1 k ∨ s = j2 k := by
  have hs := s.2
  rcases Nat.lt_or_ge s.1 k with h1 | h1
  · left; exact ⟨s.1, h1, Fin.ext (by rw [f1_val _ hk, Nat.mod_eq_of_lt h1])⟩
  · right
    rcases Nat.lt_or_ge s.1 (2 * k + 1) with h2 | h2
    · left
      refine ⟨s.1 - k, by omega, Fin.ext ?_⟩
      rw [f2_val, Nat.mod_eq_of_lt (by omega)]; omega
    · right
      rcases (show s.1 = 2 * k + 1 ∨ s.1 = 2 * k + 2 by omega) with h | h
      · left; exact Fin.ext (by unfold j1; simp; omega)
      · right; exact Fin.ext (by unfold j2; simp; omega)

/-- The six edge types. -/
theorem mem_nxt (hk : 0 < k) {s s' : Fin (2 * k + 3)} (hs' : s' ∈ nxt p k a₂ s) :
    (∃ a, a < k ∧ s = f1 k a ∧ s' = f1 k (a * p)) ∨
    (∃ a, a < k ∧ a * p % k = 1 ∧ s = f1 k a ∧ s' = j1 k) ∨
    (∃ a, a ≤ k ∧ s = f2 k a ∧ s' = f2 k (a * p)) ∨
    (∃ a, a ≤ k ∧ a * p % (k + 1) = a₂ ∧ s = f2 k a ∧ s' = j2 k) ∨
    (s = j1 k ∧ s' = f2 k k) ∨ (s = j2 k ∧ s' = f1 k 1) := by
  rcases state_cases hk s with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ | rfl | rfl
  · rw [nxt_f1 a hk, Nat.mod_eq_of_lt ha] at hs'
    simp only [List.mem_append, List.mem_singleton] at hs'
    rcases hs' with rfl | hs'
    · left; exact ⟨a, ha, rfl, rfl⟩
    · split_ifs at hs' with hj
      · simp only [List.mem_singleton] at hs'
        right; left
        exact ⟨a, ha, hj, rfl, hs'⟩
      · simp at hs'
  · rw [nxt_f2 a, Nat.mod_eq_of_lt (by omega)] at hs'
    simp only [List.mem_append, List.mem_singleton] at hs'
    rcases hs' with rfl | hs'
    · right; right; left; exact ⟨a, ha, rfl, rfl⟩
    · split_ifs at hs' with hj
      · simp only [List.mem_singleton] at hs'
        right; right; right; left
        exact ⟨a, ha, hj, rfl, hs'⟩
      · simp at hs'
  · rw [nxt_j1, List.mem_singleton] at hs'
    right; right; right; right; left; exact ⟨rfl, hs'⟩
  · rw [nxt_j2, List.mem_singleton] at hs'
    right; right; right; right; right; exact ⟨rfl, hs'⟩

end states

/-! ### Validity -/

section good

variable {p k a₂ M : ℕ}

/-- The hypotheses: `p = 2k − 1 ≥ 5` and `a₂ = p⁻¹ (mod k+1)`. -/
structure Hyp (p k a₂ : ℕ) : Prop where
  hk : 3 ≤ k
  hp : p + 1 = 2 * k
  ha₂ : a₂ < k + 1
  ha₂p : a₂ * p % (k + 1) = 1

theorem lift {X A B : ℕ} (hX : 0 < X) (h : A < B) : X * A < X * B :=
  Nat.mul_lt_mul_of_pos_left h hX

theorem lift_le {X A B : ℕ} (h : A ≤ B) : X * A ≤ X * B := Nat.mul_le_mul_left X h

/-- `(m·(p(k+1)+1)) mod E = p(k+1)(m mod k) + m` for `m < p(k+1)`. -/
theorem mod_j1 (hk : 0 < k) (m : ℕ) (hm : m < p * (k + 1)) :
    m * (p * (k + 1) + 1) % E p k = p * (k + 1) * (m % k) + m := by
  have hdm := Nat.div_add_mod m k
  have e : m * (p * (k + 1) + 1) = E p k * (m / k) + (p * (k + 1) * (m % k) + m) := by
    unfold E
    calc m * (p * (k + 1) + 1) = p * (k + 1) * (k * (m / k) + m % k) + m := by rw [hdm]; ring
      _ = _ := by ring
  rw [e, Nat.mul_add_mod]
  apply Nat.mod_eq_of_lt
  have h1 : p * (k + 1) * (m % k) + p * (k + 1) ≤ p * (k + 1) * k := by
    have := lift_le (X := p * (k + 1)) (show m % k + 1 ≤ k from Nat.mod_lt _ hk)
    rw [Nat.mul_add, mul_one] at this; exact this
  unfold E; nlinarith

/-- `(m·(a₂pk+1)) mod E = pk((m a₂) mod (k+1)) + m` for `m < pk`. -/
theorem mod_j2 (m : ℕ) (hm : m < p * k) :
    m * (a₂ * p * k + 1) % E p k = p * k * (m * a₂ % (k + 1)) + m := by
  have hdm := Nat.div_add_mod (m * a₂) (k + 1)
  have e : m * (a₂ * p * k + 1) = E p k * (m * a₂ / (k + 1)) + (p * k * (m * a₂ % (k + 1)) + m) := by
    unfold E
    calc m * (a₂ * p * k + 1) = p * k * ((k + 1) * (m * a₂ / (k + 1)) + m * a₂ % (k + 1)) + m := by
          rw [hdm]; ring
      _ = _ := by ring
  rw [e, Nat.mul_add_mod]
  apply Nat.mod_eq_of_lt
  have h1 : p * k * (m * a₂ % (k + 1)) + p * k ≤ p * k * (k + 1) := by
    have := lift_le (X := p * k) (show m * a₂ % (k + 1) + 1 ≤ k + 1 from Nat.mod_lt _ (by omega))
    rw [Nat.mul_add, mul_one] at this; exact this
  unfold E; omega

theorem mod_f1 (a m : ℕ) : m * (a * p * (k + 1)) % E p k = p * (k + 1) * (m * a % k) := by
  unfold E
  rw [show m * (a * p * (k + 1)) = p * (k + 1) * (m * a) by ring,
    show p * k * (k + 1) = p * (k + 1) * k by ring, Nat.mul_mod_mul_left]

theorem mod_f2 (a m : ℕ) : m * (a * p * k) % E p k = p * k * (m * a % (k + 1)) := by
  unfold E
  rw [show m * (a * p * k) = p * k * (m * a) by ring, Nat.mul_mod_mul_left]

theorem good (h : Hyp p k a₂) (hM : M + 2 * k + 1 ≤ k * k) : (cert p k a₂).Good M := by
  obtain ⟨hk, hp, ha₂, ha₂p⟩ := h
  have hk0 : 0 < k := by omega
  have hp1 : p - 1 + 1 = p := by omega
  have hMpk1 : ∀ m, m ≤ M → m < p * (k + 1) := fun m hm => by nlinarith
  have hMpk : ∀ m, m ≤ M → m < p * k := fun m hm => by nlinarith
  have hE : E p k = p * (k + 1) * k := by unfold E; ring
  have hE' : E p k = p * k * (k + 1) := rfl
  have hp0 : 0 < p := by omega
  refine ⟨by unfold cert E; positivity, by unfold cert; norm_num, ?_, ?_, ?_, ?_⟩
  · -- digits below `p`
    intro s
    show dig p k a₂ s < p
    rcases state_cases hk0 s with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ | rfl | rfl
    · rw [dig_f1 a hk0, Nat.mod_eq_of_lt ha, Nat.div_lt_iff_lt_mul hk0, mul_comm p k]
      exact Nat.mul_lt_mul_of_pos_right ha (by omega)
    · rw [dig_f2 a, Nat.mod_eq_of_lt (by omega), Nat.div_lt_iff_lt_mul (by omega), mul_comm p]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    · rw [dig_j1]; omega
    · rw [dig_j2, Nat.div_lt_iff_lt_mul (by omega), mul_comm p]
      exact Nat.mul_lt_mul_of_pos_right ha₂ (by omega)
  · -- `num + 1 ≤ E`
    intro s
    show num p k a₂ s + 1 ≤ E p k
    rcases state_cases hk0 s with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ | rfl | rfl
    · rw [num_f1 a hk0, Nat.mod_eq_of_lt ha, hE]
      have := lift_le (X := p * (k + 1)) (show a + 1 ≤ k by omega)
      rw [Nat.mul_add, mul_one] at this
      have e : a * p * (k + 1) = p * (k + 1) * a := by ring
      nlinarith
    · rw [num_f2 a, Nat.mod_eq_of_lt (by omega), hE']
      have := lift_le (X := p * k) (show a + 1 ≤ k + 1 by omega)
      rw [Nat.mul_add, mul_one] at this
      have e : a * p * k = p * k * a := by ring
      nlinarith
    · rw [num_j1, hE]
      have := lift_le (X := p * (k + 1)) (show 2 ≤ k by omega)
      nlinarith
    · rw [num_j2, hE']
      have := lift_le (X := p * k) (show a₂ + 1 ≤ k + 1 by omega)
      rw [Nat.mul_add, mul_one] at this
      have e : a₂ * p * k = p * k * a₂ := by ring
      nlinarith
  · -- edges
    intro s s' hs'
    show ∃ δ, δ + 1 < 1 * p ∧ dig p k a₂ s * E p k + num p k a₂ s' = p * num p k a₂ s + δ ∧
      ∀ m, m ≤ M → p * (m * num p k a₂ s % E p k) + m * δ < (p - 1) * E p k
    rcases mem_nxt hk0 hs' with ⟨a, ha, rfl, rfl⟩ | ⟨a, ha, hj, rfl, rfl⟩ | ⟨a, ha, rfl, rfl⟩ |
      ⟨a, ha, hj, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- `F₁(a) → F₁(ap)`
      refine ⟨0, by omega, ?_, ?_⟩
      · rw [dig_f1 a hk0, num_f1 a hk0, num_f1 (a * p) hk0, Nat.mod_eq_of_lt ha, add_zero, hE]
        have hdm := Nat.div_add_mod (a * p) k
        calc a * p / k * (p * (k + 1) * k) + a * p % k * p * (k + 1)
            = p * (k + 1) * (k * (a * p / k) + a * p % k) := by ring
          _ = p * (k + 1) * (a * p) := by rw [hdm]
          _ = p * (a * p * (k + 1)) := by ring
      · intro m hm
        rw [num_f1 a hk0, Nat.mod_eq_of_lt ha, mod_f1, mul_zero, add_zero, hE]
        have hr : m * a % k < k := Nat.mod_lt _ hk0
        have core : p * (m * a % k) < (p - 1) * k := by
          have h1 : p * (m * a % k) + p ≤ p * k := by
            have := lift_le (X := p) (show m * a % k + 1 ≤ k by omega)
            rw [Nat.mul_add, mul_one] at this; exact this
          have h2 : (p - 1) * k + k = p * k := by
            rw [Nat.sub_one_mul]; have : k ≤ p * k := Nat.le_mul_of_pos_left _ (by omega); omega
          omega
        calc p * (p * (k + 1) * (m * a % k)) = p * (k + 1) * (p * (m * a % k)) := by ring
          _ < p * (k + 1) * ((p - 1) * k) := lift (Nat.mul_pos hp0 (by omega)) core
          _ = (p - 1) * (p * (k + 1) * k) := by ring
    · -- `F₁(a) → J₁`, the injection
      refine ⟨1, by omega, ?_, ?_⟩
      · rw [dig_f1 a hk0, num_f1 a hk0, num_j1, Nat.mod_eq_of_lt ha, hE]
        have hdm := Nat.div_add_mod (a * p) k
        rw [hj] at hdm
        calc a * p / k * (p * (k + 1) * k) + (p * (k + 1) + 1)
            = p * (k + 1) * (k * (a * p / k) + 1) + 1 := by ring
          _ = p * (k + 1) * (a * p) + 1 := by rw [hdm]
          _ = p * (a * p * (k + 1)) + 1 := by ring
      · intro m hm
        rw [num_f1 a hk0, Nat.mod_eq_of_lt ha, mod_f1, mul_one, hE]
        have hr : m * a % k < k := Nat.mod_lt _ hk0
        have core : p * (m * a % k) + 1 ≤ (p - 1) * k := by
          have h1 : p * (m * a % k) + p ≤ p * k := by
            have := lift_le (X := p) (show m * a % k + 1 ≤ k by omega)
            rw [Nat.mul_add, mul_one] at this; exact this
          have h2 : (p - 1) * k + k = p * k := by
            rw [Nat.sub_one_mul]; have : k ≤ p * k := Nat.le_mul_of_pos_left _ (by omega); omega
          omega
        have hm' := hMpk1 m hm
        calc p * (p * (k + 1) * (m * a % k)) + m
            < p * (k + 1) * (p * (m * a % k)) + p * (k + 1) := by
              rw [show p * (p * (k + 1) * (m * a % k)) = p * (k + 1) * (p * (m * a % k)) by ring]
              omega
          _ = p * (k + 1) * (p * (m * a % k) + 1) := by ring
          _ ≤ p * (k + 1) * ((p - 1) * k) := lift_le core
          _ = (p - 1) * (p * (k + 1) * k) := by ring
    · -- `F₂(a) → F₂(ap)`
      refine ⟨0, by omega, ?_, ?_⟩
      · rw [dig_f2 a, num_f2 a, num_f2 (a * p), Nat.mod_eq_of_lt (show a < k + 1 by omega),
          add_zero, hE']
        have hdm := Nat.div_add_mod (a * p) (k + 1)
        calc a * p / (k + 1) * (p * k * (k + 1)) + a * p % (k + 1) * p * k
            = p * k * ((k + 1) * (a * p / (k + 1)) + a * p % (k + 1)) := by ring
          _ = p * k * (a * p) := by rw [hdm]
          _ = p * (a * p * k) := by ring
      · intro m hm
        rw [num_f2 a, Nat.mod_eq_of_lt (show a < k + 1 by omega), mod_f2, mul_zero, add_zero, hE']
        have hr : m * a % (k + 1) < k + 1 := Nat.mod_lt _ (by omega)
        have core : p * (m * a % (k + 1)) < (p - 1) * (k + 1) := by
          have h1 : p * (m * a % (k + 1)) ≤ p * k := lift_le (by omega)
          have h2 : (p - 1) * (k + 1) + (k + 1) = p * (k + 1) := by
            rw [Nat.sub_one_mul]
            have : k + 1 ≤ p * (k + 1) := Nat.le_mul_of_pos_left _ (by omega); omega
          have h3 : p * (k + 1) = p * k + p := by ring
          omega
        calc p * (p * k * (m * a % (k + 1))) = p * k * (p * (m * a % (k + 1))) := by ring
          _ < p * k * ((p - 1) * (k + 1)) := lift (Nat.mul_pos hp0 (by omega)) core
          _ = (p - 1) * (p * k * (k + 1)) := by ring
    · -- `F₂(a) → J₂`, the injection
      refine ⟨1, by omega, ?_, ?_⟩
      · rw [dig_f2 a, num_f2 a, num_j2, Nat.mod_eq_of_lt (show a < k + 1 by omega), hE']
        have hdm := Nat.div_add_mod (a * p) (k + 1)
        rw [hj] at hdm
        calc a * p / (k + 1) * (p * k * (k + 1)) + (a₂ * p * k + 1)
            = p * k * ((k + 1) * (a * p / (k + 1)) + a₂) + 1 := by ring
          _ = p * k * (a * p) + 1 := by rw [hdm]
          _ = p * (a * p * k) + 1 := by ring
      · intro m hm
        rw [num_f2 a, Nat.mod_eq_of_lt (show a < k + 1 by omega), mod_f2, mul_one, hE']
        have hr : m * a % (k + 1) < k + 1 := Nat.mod_lt _ (by omega)
        have core : p * (m * a % (k + 1)) + 1 ≤ (p - 1) * (k + 1) := by
          have h1 : p * (m * a % (k + 1)) ≤ p * k := lift_le (by omega)
          have h2 : (p - 1) * (k + 1) + (k + 1) = p * (k + 1) := by
            rw [Nat.sub_one_mul]
            have : k + 1 ≤ p * (k + 1) := Nat.le_mul_of_pos_left _ (by omega); omega
          have h3 : p * (k + 1) = p * k + p := by ring
          omega
        have hm' := hMpk m hm
        calc p * (p * k * (m * a % (k + 1))) + m
            < p * k * (p * (m * a % (k + 1))) + p * k := by
              rw [show p * (p * k * (m * a % (k + 1))) = p * k * (p * (m * a % (k + 1))) by ring]
              omega
          _ = p * k * (p * (m * a % (k + 1)) + 1) := by ring
          _ ≤ p * k * ((p - 1) * (k + 1)) := lift_le core
          _ = (p - 1) * (p * k * (k + 1)) := by ring
    · -- `J₁ → F₂(k)`, the landing on `−1/(k+1)`
      refine ⟨0, by omega, ?_, ?_⟩
      · rw [dig_j1, num_j1, num_f2 k, Nat.mod_eq_of_lt (show k < k + 1 by omega), add_zero, hE']
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
        obtain rfl : p = 2 * j + 5 := by omega
        ring
      · intro m hm
        rw [num_j1, mod_j1 hk0 m (hMpk1 m hm), mul_zero, add_zero, hE]
        have hr : m % k < k := Nat.mod_lt _ hk0
        -- `p(k+1)(m mod k) + m < (p−1)(k+1)k`, sharp at `m = k² − 1`
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
        obtain rfl : p = 2 * j + 5 := by omega
        rw [show 2 * j + 5 - 1 = 2 * j + 4 by omega]
        have core : (2 * j + 5) * (j + 4) * (m % (j + 3)) + m < (2 * j + 4) * (j + 4) * (j + 3) := by
          have h1 : (2 * j + 5) * (j + 4) * (m % (j + 3)) ≤ (2 * j + 5) * (j + 4) * (j + 2) :=
            lift_le (by omega)
          nlinarith
        calc (2 * j + 5) * ((2 * j + 5) * (j + 4) * (m % (j + 3)) + m)
            < (2 * j + 5) * ((2 * j + 4) * (j + 4) * (j + 3)) := lift (by omega) core
          _ = (2 * j + 4) * ((2 * j + 5) * (j + 3 + 1) * (j + 3)) := by ring
    · -- `J₂ → F₁(1)`, the landing on `1/k`
      refine ⟨0, by omega, ?_, ?_⟩
      · rw [dig_j2, num_j2, num_f1 1 hk0, Nat.mod_eq_of_lt (show 1 < k by omega), add_zero, hE']
        have hdm := Nat.div_add_mod (a₂ * p) (k + 1)
        rw [ha₂p] at hdm
        calc a₂ * p / (k + 1) * (p * k * (k + 1)) + 1 * p * (k + 1)
            = p * (k * ((k + 1) * (a₂ * p / (k + 1)) + 1) + 1) := by ring
          _ = p * (k * (a₂ * p) + 1) := by rw [hdm]
          _ = p * (a₂ * p * k + 1) := by ring
      · intro m hm
        rw [num_j2, mod_j2 m (hMpk m hm), mul_zero, add_zero, hE']
        have hr : m * a₂ % (k + 1) < k + 1 := Nat.mod_lt _ (by omega)
        -- `pk r + m < (p−1)k(k+1)`, sharp at `m = k² − 2k`
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
        obtain rfl : p = 2 * j + 5 := by omega
        rw [show 2 * j + 5 - 1 = 2 * j + 4 by omega]
        have core : (2 * j + 5) * (j + 3) * (m * a₂ % (j + 3 + 1)) + m
            < (2 * j + 4) * (j + 3) * (j + 4) := by
          have h1 : (2 * j + 5) * (j + 3) * (m * a₂ % (j + 3 + 1)) ≤ (2 * j + 5) * (j + 3) * (j + 3) :=
            lift_le (by omega)
          nlinarith
        calc (2 * j + 5) * ((2 * j + 5) * (j + 3) * (m * a₂ % (j + 3 + 1)) + m)
            < (2 * j + 5) * ((2 * j + 4) * (j + 3) * (j + 4)) := lift (by omega) core
          _ = (2 * j + 4) * ((2 * j + 5) * (j + 3) * (j + 3 + 1)) := by ring
  · -- carries: `(m·num) mod E + m < E`
    intro s m hm
    show m * num p k a₂ s % E p k + 1 * m < E p k
    rw [one_mul]
    have hm1 := hMpk1 m hm
    have hm2 := hMpk m hm
    rcases state_cases hk0 s with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ | rfl | rfl
    · rw [num_f1 a hk0, Nat.mod_eq_of_lt ha, mod_f1, hE]
      have h1 : p * (k + 1) * (m * a % k) + p * (k + 1) ≤ p * (k + 1) * k := by
        have := lift_le (X := p * (k + 1)) (show m * a % k + 1 ≤ k from Nat.mod_lt _ hk0)
        rw [Nat.mul_add, mul_one] at this; exact this
      omega
    · rw [num_f2 a, Nat.mod_eq_of_lt (show a < k + 1 by omega), mod_f2, hE']
      have h1 : p * k * (m * a % (k + 1)) + p * k ≤ p * k * (k + 1) := by
        have := lift_le (X := p * k) (show m * a % (k + 1) + 1 ≤ k + 1 from Nat.mod_lt _ (by omega))
        rw [Nat.mul_add, mul_one] at this; exact this
      omega
    · rw [num_j1, mod_j1 hk0 m hm1, hE]
      have h1 : p * (k + 1) * (m % k) + p * (k + 1) ≤ p * (k + 1) * k := by
        have := lift_le (X := p * (k + 1)) (show m % k + 1 ≤ k from Nat.mod_lt _ hk0)
        rw [Nat.mul_add, mul_one] at this; exact this
      -- `2m < p(k+1)`
      have h2 : 2 * m < p * (k + 1) := by nlinarith
      omega
    · rw [num_j2, mod_j2 m hm2, hE']
      have h1 : p * k * (m * a₂ % (k + 1)) + p * k ≤ p * k * (k + 1) := by
        have := lift_le (X := p * k) (show m * a₂ % (k + 1) + 1 ≤ k + 1 from Nat.mod_lt _ (by omega))
        rw [Nat.mul_add, mul_one] at this; exact this
      have h2 : 2 * m < p * k := by nlinarith
      omega

theorem valid (h : Hyp p k a₂) (hM : M + 2 * k + 1 ≤ k * k) :
    (cert p k a₂).toCert.Valid M [p - 1] :=
  NumCert.valid (by have := h.hk; have := h.hp; omega) (good h hM)

theorem not_hiMax_of_edge (h : Hyp p k a₂) (hM : M + 2 * k + 1 ≤ k * k)
    {s s' : Fin (2 * k + 3)} (hs' : s' ∈ nxt p k a₂ s) :
    ¬ (cert p k a₂).toCert.HiMax s s' :=
  NumCert.not_hiMax_of_edge (by have := h.hk; have := h.hp; omega) (good h hM) hs'

end good

/-! ### The walks -/

section walks

variable (p k s : ℕ)

/-- Walk A, period `s + 3`: `F₁(1), F₁(−1), J₁, F₂(k p^0), …, F₂(k p^{s−2}), J₂`. -/
def walkA (i : ℕ) : Fin (2 * k + 3) :=
  if i = 0 then f1 k 1 else if i = 1 then f1 k (k - 1) else if i = 2 then j1 k
  else if i ≤ s + 1 then f2 k (k * p ^ (i - 3)) else j2 k

/-- Walk B, period `2`: the oscillation `F₁(1), F₁(−1)`. -/
def walkB (i : ℕ) : Fin (2 * k + 3) := if i % 2 = 0 then f1 k 1 else f1 k (k - 1)

variable {p k s}
variable {a₂ M : ℕ}

theorem walkA_zero : walkA p k s 0 = f1 k 1 := by simp [walkA]
theorem walkA_one : walkA p k s 1 = f1 k (k - 1) := by simp [walkA]
theorem walkA_two : walkA p k s 2 = j1 k := by simp [walkA]
theorem walkA_mid (i : ℕ) (hi : 3 ≤ i) (hi' : i ≤ s + 1) :
    walkA p k s i = f2 k (k * p ^ (i - 3)) := by
  unfold walkA
  rw [if_neg (show ¬ i = 0 by omega), if_neg (show ¬ i = 1 by omega), if_neg (show ¬ i = 2 by omega),
    if_pos hi']
theorem walkA_last (hs : 1 ≤ s) : walkA p k s (s + 2) = j2 k := by
  unfold walkA
  rw [if_neg (show ¬ s + 2 = 0 by omega), if_neg (show ¬ s + 2 = 1 by omega),
    if_neg (show ¬ s + 2 = 2 by omega), if_neg (show ¬ s + 2 ≤ s + 1 by omega)]

theorem walkB_even (i : ℕ) (hi : i % 2 = 0) : walkB k i = f1 k 1 := by simp [walkB, hi]
theorem walkB_odd (i : ℕ) (hi : i % 2 = 1) : walkB k i = f1 k (k - 1) := by simp [walkB, hi]

/-- `p ≡ −1 (mod k)`: `1 ↦ k − 1`. -/
theorem f1_one_step (hk : 2 ≤ k) (hp : p + 1 = 2 * k) : f1 k (1 % k * p) = f1 k (k - 1) := by
  apply f1_congr
  rw [Nat.mod_eq_of_lt (show 1 < k by omega), one_mul, show p = (k - 1) + k * 1 by omega,
    Nat.add_mul_mod_self_left]

/-- `p ≡ −1 (mod k)`: `(k − 1) p ≡ 1`. -/
theorem f1_neg_one_mul (hk : 2 ≤ k) (hp : p + 1 = 2 * k) : (k - 1) % k * p % k = 1 := by
  rw [Nat.mod_eq_of_lt (show k - 1 < k by omega)]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  obtain rfl : p = 2 * j + 3 := by omega
  rw [show j + 2 - 1 = j + 1 by omega,
    show (j + 1) * (2 * j + 3) = 1 + (j + 2) * (2 * j + 1) by ring, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

theorem f1_neg_one_step (hk : 2 ≤ k) (hp : p + 1 = 2 * k) : f1 k ((k - 1) % k * p) = f1 k 1 := by
  apply f1_congr
  rw [f1_neg_one_mul hk hp, Nat.mod_eq_of_lt (show 1 < k by omega)]

theorem walkA_closed (hk : 3 ≤ k) (hp : p + 1 = 2 * k) (hs : 3 ≤ s)
    (ha₂ : a₂ = k * p ^ (s - 1) % (k + 1)) :
    walkA p k s 0 = f1 k 1 ∧
    (∀ i, i + 1 < s + 3 → walkA p k s (i + 1) ∈ nxt p k a₂ (walkA p k s i)) ∧
    f1 k 1 ∈ nxt p k a₂ (walkA p k s (s + 3 - 1)) := by
  have hk0 : 0 < k := by omega
  refine ⟨walkA_zero, ?_, ?_⟩
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ (3 ≤ i ∧ i + 1 ≤ s + 1) ∨ i = s + 1 by omega) with
      rfl | rfl | rfl | ⟨h3, h4⟩ | rfl
    · rw [walkA_zero, walkA_one, nxt_f1 1 hk0, f1_one_step (by omega) hp]
      simp
    · rw [walkA_one, walkA_two, nxt_f1 (k - 1) hk0, f1_neg_one_mul (by omega) hp]
      simp
    · rw [walkA_two, walkA_mid 3 le_rfl (by omega), nxt_j1]
      simp
    · rw [walkA_mid i h3 (by omega), walkA_mid (i + 1) (by omega) h4, nxt_f2]
      simp only [List.mem_append, List.mem_singleton]
      left
      apply f2_congr
      rw [Nat.mod_mul_mod, show i + 1 - 3 = (i - 3) + 1 by omega, pow_succ, mul_assoc]
    · have hs' : 3 ≤ s := hs
      rw [walkA_mid (s + 1) (by omega) le_rfl, walkA_last (by omega), nxt_f2]
      simp only [List.mem_append, List.mem_singleton]
      right
      rw [if_pos]
      · simp
      · have e1 : s + 1 - 3 = s - 2 := by omega
        have e2 : s - 1 = (s - 2) + 1 := by omega
        rw [Nat.mod_mul_mod, ha₂, e1, e2, pow_succ, mul_assoc]
  · rw [show s + 3 - 1 = s + 2 by omega, walkA_last (by omega), nxt_j2]
    simp

theorem walkB_closed (hk : 3 ≤ k) (hp : p + 1 = 2 * k) :
    walkB k 0 = f1 k 1 ∧
    (∀ i, i + 1 < 2 → walkB k (i + 1) ∈ nxt p k a₂ (walkB k i)) ∧
    f1 k 1 ∈ nxt p k a₂ (walkB k (2 - 1)) := by
  have hk0 : 0 < k := by omega
  refine ⟨walkB_even 0 rfl, ?_, ?_⟩
  · intro i hi
    obtain rfl : i = 0 := by omega
    rw [walkB_even 0 rfl, walkB_odd 1 rfl, nxt_f1 1 hk0, f1_one_step (by omega) hp]
    simp
  · rw [walkB_odd 1 rfl, nxt_f1 (k - 1) hk0, f1_neg_one_step (by omega) hp]
    simp

/-- `dig F₁(1) = 1`. -/
theorem dig_f1_one (hk : 3 ≤ k) (hp : p + 1 = 2 * k) : dig p k a₂ (f1 k 1) = 1 := by
  rw [dig_f1 1 (by omega), Nat.mod_eq_of_lt (by omega), one_mul]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- `dig F₂(kp) = ⌊3p/(k+1)⌋ ≥ 3`. -/
theorem dig_f2_kp (hk : 3 ≤ k) (hp : p + 1 = 2 * k) : 3 ≤ dig p k a₂ (f2 k (k * p ^ 1)) := by
  rw [dig_f2, pow_one]
  have e : k * p % (k + 1) = 3 := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    obtain rfl : p = 2 * j + 5 := by omega
    rw [show (j + 3) * (2 * j + 5) = 3 + (j + 3 + 1) * (2 * j + 3) by ring,
      Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  rw [e, Nat.le_div_iff_mul_le (by omega)]
  omega

theorem witness (h : Hyp p k a₂) (hM : M + 2 * k + 1 ≤ k * k) (hs : 3 ≤ s)
    (ha₂ : a₂ = k * p ^ (s - 1) % (k + 1)) (L : ℕ) (hL : L = 2 * (s + 3)) (hL0 : 0 < L) :
    (cert p k a₂).toCert.WitnessPair L
      (fun i : Fin L => walkA p k s (i.1 % (s + 3)))
      (fun i : Fin L => walkB k i.1) hL0 (f1 k 1) := by
  have hk := h.hk
  have hp := h.hp
  have hL6 : 6 ≤ L := by omega
  obtain ⟨hA0, hAstep, hAclose⟩ := walkA_closed (a₂ := a₂) hk hp hs ha₂
  obtain ⟨hB0, hBstep, hBclose⟩ := walkB_closed (p := p) (a₂ := a₂) hk hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact EscapeCert.isClosedWalk_periodic (C := (cert p k a₂).toCert) (walkA p k s) (s + 3)
      (by omega) _ hA0 hAstep hAclose L 2 hL (by omega) hL0
  · have := EscapeCert.isClosedWalk_periodic (C := (cert p k a₂).toCert) (walkB k) 2
      (by omega) _ hB0 hBstep hBclose L (s + 3) (by omega) (by omega) hL0
    convert this using 2 with i
    simp only [walkB, Nat.mod_mod_of_dvd _ (dvd_refl 2)]
  · refine ⟨⟨0, by omega⟩, ?_⟩
    show dig p k a₂ (walkA p k s (0 % (s + 3))) ≠ p - 1
    rw [Nat.zero_mod, walkA_zero, dig_f1_one hk hp]; omega
  · refine ⟨⟨0, by omega⟩, ?_⟩
    show dig p k a₂ (walkB k 0) ≠ p - 1
    rw [walkB_even 0 rfl, dig_f1_one hk hp]; omega
  · refine ⟨⟨0, by omega⟩, show 0 + 1 < L by omega, ?_⟩
    simp only [Nat.zero_mod, Nat.mod_eq_of_lt (show 0 + 1 < s + 3 by omega)]
    exact not_hiMax_of_edge h hM (hAstep 0 (by omega))
  · refine ⟨⟨0, by omega⟩, show 0 + 1 < L by omega, ?_⟩
    exact not_hiMax_of_edge h hM (hBstep 0 (by omega))
  · refine ⟨⟨4, by omega⟩, ?_⟩
    show dig p k a₂ (walkA p k s (4 % (s + 3))) ≠ dig p k a₂ (walkB k 4)
    rw [Nat.mod_eq_of_lt (by omega), walkA_mid 4 (by omega) (by omega), walkB_even 4 rfl,
      dig_f1_one hk hp, show (4 : ℕ) - 3 = 1 from rfl]
    have := dig_f2_kp (a₂ := a₂) hk hp
    omega

end walks

/-! ### The theorem -/

/-- `a₂ = k p^{s−1} mod (k+1)` inverts `p` when `p^s ≡ −1 ≡ k`. -/
theorem a₂_inv {p k s : ℕ} (hk : 1 ≤ k) (hs : 1 ≤ s) (hpow : p ^ s % (k + 1) = k) :
    k * p ^ (s - 1) % (k + 1) * p % (k + 1) = 1 := by
  rw [Nat.mod_mul_mod, mul_assoc, ← pow_succ, show s - 1 + 1 = s by omega,
    Nat.mul_mod, hpow, Nat.mod_mul_mod,
    show k * k = 1 + (k + 1) * (k - 1) by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [Nat.add_sub_cancel]; ring,
    Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- **The Farey-junction theorem.**  For every odd `p = 2k − 1 ≥ 5` with `p^s ≡ −1 (mod k+1)`
(`s ≥ 3`; any `s ≥ 1` via `mahler_lower_bound_farey'`), every channel `m ≤ k² − 2k − 1 = ⌊p/2⌋² − 2`
is digit-`(p−1)`-free for a common irrational: `M(p,1) > ⌊p/2⌋² − 2`.  No primality is used. -/
theorem mahler_lower_bound_farey (p k s : ℕ) (hk : 3 ≤ k) (hp : p + 1 = 2 * k) (hs : 3 ≤ s)
    (hpow : p ^ s % (k + 1) = k) :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ k * k - 2 * k - 1 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt p ((m : ℝ) * α) [p - 1] n := by
  set a₂ := k * p ^ (s - 1) % (k + 1) with ha₂
  have h : Hyp p k a₂ := ⟨hk, hp, Nat.mod_lt _ (by omega), a₂_inv (by omega) (by omega) hpow⟩
  have hM : k * k - 2 * k - 1 + 2 * k + 1 ≤ k * k := by
    have : 2 * k + 1 ≤ k * k := by nlinarith
    omega
  have hL0 : 0 < 2 * (s + 3) := by omega
  exact (cert p k a₂).toCert.escape_mahler_lower_bound (by omega) _ [p - 1] (valid h hM) _ _ _ hL0 _
    (witness h hM hs ha₂ _ rfl hL0)

/-- `p^s ≡ −1` for some `s ≥ 1` suffices: `p^{3s} ≡ (−1)³ = −1`. -/
theorem mahler_lower_bound_farey' (p k s : ℕ) (hk : 3 ≤ k) (hp : p + 1 = 2 * k) (hs : 1 ≤ s)
    (hpow : p ^ s % (k + 1) = k) :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ k * k - 2 * k - 1 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt p ((m : ℝ) * α) [p - 1] n := by
  refine mahler_lower_bound_farey p k (3 * s) hk hp (by omega) ?_
  rw [pow_mul', Nat.pow_mod, hpow]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  rw [show (j + 3) ^ 3 = (j + 3) + (j + 3 + 1) * ((j + 3) * (j + 2)) by ring,
    Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- `M(19,1) ≥ 79 = ⌊19/2⌋² − 2` (census: `80`). -/
theorem mahler_lower_bound_base19_farey :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 79 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt 19 ((m : ℝ) * α) [18] n :=
  mahler_lower_bound_farey' 19 10 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `M(23,1) ≥ 119 = ⌊23/2⌋² − 2` (census: `120`). -/
theorem mahler_lower_bound_base23_farey :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 119 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt 23 ((m : ℝ) * α) [22] n :=
  mahler_lower_bound_farey' 23 12 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `M(31,1) ≥ 223 = ⌊31/2⌋² − 2` (census: `224`). -/
theorem mahler_lower_bound_base31_farey :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 223 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt 31 ((m : ℝ) * α) [30] n :=
  mahler_lower_bound_farey' 31 16 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end NormalNumbers.Adder.Farey
