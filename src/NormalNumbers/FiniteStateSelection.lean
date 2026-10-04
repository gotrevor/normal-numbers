/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Bridge
import NormalNumbers.G4EntropyOcc

/-!
# Finite-state relabelings, pushdown relabelings and `f`-normality (lane E3)

Audit: `docs/FINITE-STATE-AUDIT-2026-10-04.md`.  Direction: `docs/ENGINE-PROPOSALS-2026-10-04.md` §E3.

**The questions.**  Pulari, *On Normality and Equidistribution for Separator Enumerators*,
arXiv:2602.01199v2 (3 Feb 2026), §5 "Discussion and open questions", asks two things about
Mayordomo's relativized normality (`f`-normality, `dim^f_FS(x) = 1`, Mayordomo arXiv:2208.00157):

* **(Q-DPDT)** "One concrete setting is when the naming map is computable by a deterministic
  pushdown transducer.  In particular, does there exist such a separator enumerator `f` and a point
  `x ∈ [0,1)` for which the integer sequence `(k^n a_n^f(x))_{n ≥ 1}` is `k`-adically
  equidistributed while `dim^f_FS(x) < 1`?"
* **(Q-weak)** "It would be interesting to determine whether some weaker condition (e.g. levelwise
  surjectivity or bounded-to-one behavior on each `Σ^n`) suffices for the same equidistribution
  characterization, or whether non-invertible finite-state relabelings can already break it."

**The answers frozen here.**

* `pulariDPDTQuestion_of_lit` — **yes** to Q-DPDT for every base `k ≥ 5`, with a REAL-TIME
  (letter-to-letter, no ε-moves, no end marker) deterministic pushdown relabeling: the decoder
  `decRun` of the free-reduction coder `encRun`, applied to the Carton–Perifel normal sequence
  `w₁ w̃₁ w₂ w̃₂ ⋯`.  The relabeling is a bijection on every level `Σ^n`, so Pulari's
  finite-state-coherent characterization fails as soon as the finite control gets one stack.
* `pulariWeakening_of_lit` — Q-weak collapses for synchronous relabelings: a synchronous Mealy
  relabeling whose image is dense is automatically levelwise surjective, hence levelwise bijective,
  hence agrees with an invertible Mealy machine, so the characterization holds for EVERY synchronous
  finite-state relabeling that is a separator enumerator.  Levelwise surjectivity is not weaker than
  invertibility, and a non-injective (e.g. bounded-to-one) synchronous relabeling is never a
  separator enumerator at all.

Both are proved here from elementary leaves (all proved; see `## Leaves`) and three cited
hypotheses in `NormalNumbers.Literature` (Carton–Perifel normality, "FS-dimension one ⇒ normal",
Pulari's Theorem 3).

**Guard (known-false sibling).**  `mirror_not_mealy`: the stack is load-bearing — the mirror
relabeling is not computed by any synchronous Mealy machine, because Pulari's theorem would then
force `dim^f = 1` at the same point.  The mechanism therefore separates the pushdown class from the
finite-state class, as a difficulty check requires.

Conventions follow Pulari §2: `grid u = val(u)/k^{|u|}`; an FST `T` has outputs in `Σ*`;
`K^T(w) = min{|π| : T(π) = w}`; `K^{T,f}_δ(x) = min{K^T(w) : |f(w) − x| < δ}`;
`dim^f_FS(x) = inf_T liminf_{δ→0⁺} K^{T,f}_δ(x) / log_k(1/δ)`;
`a_n^f(x) = max{f(w) : |w| ≤ n, f(w) ≤ x}`.  FST states are `Fin (m+1)` with start state `0`.
-/

noncomputable section

open Filter Topology
open scoped ENNReal

namespace NormalNumbers.FiniteState

variable {k : ℕ}

/-! ## Separator enumerators and relativized finite-state dimension (Mayordomo, Pulari §2) -/

/-- The level-`|u|` grid point named by `u`: `val(u)/k^{|u|} = Σ uᵢ k^{-(i+1)}`. -/
def grid (k : ℕ) (u : List (Fin k)) : ℝ :=
  ∑ i : Fin u.length, ((u.get i : ℕ) : ℝ) / (k : ℝ) ^ ((i : ℕ) + 1)

theorem grid_nil : grid k [] = 0 := by simp [grid]

/-- A **separator enumerator** (Mayordomo; Pulari Def. 2): values in `[0,1)` and dense image in
`[0,1)` (countability is automatic for a function on `Σ*`). -/
def IsSepEnum (f : List (Fin k) → ℝ) : Prop :=
  (∀ w, f w ∈ Set.Ico (0 : ℝ) 1) ∧
    ∀ a c : ℝ, 0 ≤ a → a < c → c ≤ 1 → ∃ w, f w ∈ Set.Ioo a c

/-- A `Σ`-finite-state transducer (Pulari Def. 1): states `Fin (m+1)`, start state `0`,
transition `δ`, output `ν` with values in `Σ*`. -/
structure FST (k : ℕ) where
  m : ℕ
  δ : Fin (m + 1) → Fin k → Fin (m + 1)
  ν : Fin (m + 1) → Fin k → List (Fin k)

/-- Output of an FST from a given state. -/
def FST.runFrom (T : FST k) : Fin (T.m + 1) → List (Fin k) → List (Fin k)
  | _, [] => []
  | q, a :: w => T.ν q a ++ T.runFrom (T.δ q a) w

/-- `T(w) = ν(q₀, w)`. -/
def FST.run (T : FST k) (w : List (Fin k)) : List (Fin k) := T.runFrom 0 w

/-- `T`-information content `K^T(w)` (Pulari Def. 1, after Mayordomo); `⊤` off the range. -/
def infoK (T : FST k) (w : List (Fin k)) : ℕ∞ :=
  ⨅ (π : List (Fin k)) (_ : T.run π = w), (π.length : ℕ∞)

/-- Relativized approximation complexity `K^{T,f}_δ(x)` (Pulari Def. 3). -/
def approxK (T : FST k) (f : List (Fin k) → ℝ) (δ x : ℝ) : ℕ∞ :=
  ⨅ (w : List (Fin k)) (_ : |f w - x| < δ), infoK T w

/-- Relativized finite-state dimension `dim^f_FS(x)` (Pulari Def. 4). -/
def fDim (f : List (Fin k) → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ⨅ T : FST k, liminf (fun δ : ℝ =>
    ((approxK T f δ x : ℕ∞) : ℝ≥0∞) / ENNReal.ofReal (Real.logb k (1 / δ))) (𝓝[>] 0)

/-- `f`-normality: `dim^f_FS(x) = 1` (Pulari Def. 4). -/
def IsFNormal (f : List (Fin k) → ℝ) (x : ℝ) : Prop := fDim f x = 1

/-- Length-`n` prefix of a sequence. -/
def pre (S : ℕ → Fin k) (n : ℕ) : List (Fin k) := List.ofFn fun i : Fin n => S i

/-- Finite-state dimension of a sequence in its decompression form
`inf_T liminf_n K^T(S↾n)/n` (Doty–Moser 2006 Thm 3.11, as used in Pulari Lemma 1). -/
def fsDim (S : ℕ → Fin k) : ℝ≥0∞ :=
  ⨅ T : FST k, liminf (fun n : ℕ => ((infoK T (pre S n) : ℕ∞) : ℝ≥0∞) / (n : ℝ≥0∞)) atTop

/-- Best approximation from below `a_n^f(x)` (Pulari Def. 5). -/
def bestBelow (f : List (Fin k) → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  sSup {y | ∃ w : List (Fin k), w.length ≤ n ∧ f w = y ∧ y ≤ x}

/-- The scaled best-from-below sequence `k^n a_n^f(x)`, read through `⌊·⌋` (it is an integer in
every case considered here; the integrality is stated separately where it is used). -/
def scaled (f : List (Fin k) → ℝ) (x : ℝ) (n : ℕ) : ℤ := ⌊(k : ℝ) ^ n * bestBelow f x n⌋

open Classical in
/-- `k`-adic equidistribution of an integer sequence (Pulari Def. 6): for every `m ≥ 1` and every
residue `r < k^m`, the frequency of `n ∈ [1, N]` with `bₙ ≡ r (mod k^m)` tends to `k^{-m}`. -/
def KAdicEquidist (k : ℕ) (b : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ r : ℕ, r < k ^ m →
    Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N).filter fun n => b n ≡ (r : ℤ) [ZMOD (k : ℤ) ^ m]).card : ℝ) / N)
      atTop (𝓝 (1 / (k : ℝ) ^ m))

/-! ## Synchronous Mealy relabelings (Pulari §4) -/

/-- A synchronous (letter-to-letter) Mealy machine, with NO permutation requirement. -/
structure Mealy (k : ℕ) where
  Q : Type
  [fintype : Fintype Q]
  q0 : Q
  δ : Q → Fin k → Q
  out : Q → Fin k → Fin k

/-- Mealy output from a given state. -/
def Mealy.runFrom (M : Mealy k) : M.Q → List (Fin k) → List (Fin k)
  | _, [] => []
  | q, a :: w => M.out q a :: M.runFrom (M.δ q a) w

/-- Mealy output from the start state. -/
def Mealy.run (M : Mealy k) (w : List (Fin k)) : List (Fin k) := M.runFrom M.q0 w

/-- Pulari Def. 7: every per-state output map is a permutation of `Σ`. -/
def Mealy.IsInvertible (M : Mealy k) : Prop := ∀ q, Function.Bijective (M.out q)

/-- The relabeled enumerator `f(w) = grid(M(w))` (Pulari Def. 8; `f(λ) = 0` by `grid_nil`). -/
def mealyEnum (M : Mealy k) (w : List (Fin k)) : ℝ := grid k (M.run w)

/-! ## Real-time deterministic pushdown transducers -/

/-- A real-time deterministic pushdown transducer (Carton–Perifel 2024 §2 model, without
ε-transitions) with state type `Q` and stack alphabet `Z`: in state `q` with stack top `top?`,
reading `a`, it pops the top (if any), pushes the returned list (head = new top), and emits the
returned word.  Finiteness of `Q` and `Z` is required where the class is used (`IsDPDTEnum`). -/
structure RTDPDT (k : ℕ) (Q Z : Type) where
  q0 : Q
  step : Q → Option Z → Fin k → Q × List Z × List (Fin k)

/-- DPDT output from a configuration (stack listed top first). -/
def RTDPDT.runFrom {Q Z : Type} (P : RTDPDT k Q Z) : Q → List Z → List (Fin k) → List (Fin k)
  | _, _, [] => []
  | q, s, a :: w =>
    (P.step q s.head? a).2.2 ++
      P.runFrom (P.step q s.head? a).1 ((P.step q s.head? a).2.1 ++ s.tail) w

/-- DPDT output from the start configuration (empty stack). -/
def RTDPDT.run {Q Z : Type} (P : RTDPDT k Q Z) (w : List (Fin k)) : List (Fin k) :=
  P.runFrom P.q0 [] w

/-- `f` is computed by a real-time deterministic pushdown transducer with finitely many states and
a finite stack alphabet: `f(w) = grid(P(w))`. -/
def IsDPDTEnum (f : List (Fin k) → ℝ) : Prop :=
  ∃ (Q Z : Type) (_ : Fintype Q) (_ : Fintype Z) (P : RTDPDT k Q Z),
    ∀ w, f w = grid k (P.run w)

/-! ## The free-reduction coder and its pushdown decoder -/

section Mirror

variable [NeZero k]

/-- Coder step (stack top first): a letter equal to the top cancels it and emits `0`; any other
letter is pushed and emits its difference from the old top. -/
def encStep : List (Fin k) → Fin k → List (Fin k) × Fin k
  | [], a => ([a], a)
  | t :: s, a => if a = t then (s, 0) else (a :: t :: s, a - t)

/-- The coder: the stack after reading `p` is the free reduction of `p` under `aa → ε`. -/
def encRun : List (Fin k) → List (Fin k) → List (Fin k)
  | _, [] => []
  | s, a :: w => (encStep s a).2 :: encRun (encStep s a).1 w

/-- Decoder step: `0` pops and emits the top; `o ≠ 0` pushes and emits `o + top`.  For each stack
this is a permutation of the input letter. -/
def decStep : List (Fin k) → Fin k → List (Fin k) × Fin k
  | [], o => ([o], o)
  | t :: s, o => if o = 0 then (s, t) else ((o + t) :: t :: s, o + t)

/-- The decoder: the naming map of the mirror enumerator. -/
def decRun : List (Fin k) → List (Fin k) → List (Fin k)
  | _, [] => []
  | s, o :: w => (decStep s o).2 :: decRun (decStep s o).1 w

theorem decStep_encStep (s : List (Fin k)) (a : Fin k) :
    decStep s (encStep s a).2 = ((encStep s a).1, a) := by
  cases s with
  | nil => rfl
  | cons t s =>
    by_cases h : a = t
    · subst h; simp [encStep, decStep]
    · have h' : a - t ≠ 0 := sub_ne_zero.mpr h
      simp [encStep, decStep, h, h']

theorem encStep_decStep (s : List (Fin k)) (o : Fin k) :
    encStep s (decStep s o).2 = ((decStep s o).1, o) := by
  cases s with
  | nil => rfl
  | cons t s =>
    by_cases h : o = 0
    · subst h; simp [encStep, decStep]
    · have h' : o + t ≠ t := fun e => h (by simpa using e)
      simp [encStep, decStep, h, h']

theorem decRun_encRun (s w : List (Fin k)) : decRun s (encRun s w) = w := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => simp [encRun, decRun, decStep_encStep, ih]

theorem encRun_decRun (s w : List (Fin k)) : encRun s (decRun s w) = w := by
  induction w generalizing s with
  | nil => rfl
  | cons o w ih => simp [encRun, decRun, encStep_decStep, ih]

theorem length_encRun (s w : List (Fin k)) : (encRun s w).length = w.length := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => simp [encRun, ih]

theorem length_decRun (s w : List (Fin k)) : (decRun s w).length = w.length := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => simp [decRun, ih]

/-- The decoder is a bijection on every level `Σ^n` (inverse `encRun []`). -/
theorem decRun_levelSurj (u : List (Fin k)) :
    ∃ w, w.length = u.length ∧ decRun [] w = u :=
  ⟨encRun [] u, length_encRun [] u, decRun_encRun [] u⟩

/-- The mirror enumerator `f(w) = grid(decRun(w))`. -/
def mirrorEnum (k : ℕ) [NeZero k] (w : List (Fin k)) : ℝ := grid k (decRun [] w)

/-- The decoder as a one-state real-time DPDT with stack alphabet `Σ`. -/
def mirrorDPDT : RTDPDT k Unit (Fin k) where
  q0 := ()
  step := fun _ top o => match top with
    | none => ((), [o], [o])
    | some t => if o = 0 then ((), [], [t]) else ((), [o + t, t], [o + t])

theorem mirrorDPDT_step_none (o : Fin k) :
    (mirrorDPDT (k := k)).step () none o = ((), [o], [o]) := rfl

theorem mirrorDPDT_step_some (t o : Fin k) :
    (mirrorDPDT (k := k)).step () (some t) o
      = if o = 0 then ((), [], [t]) else ((), [o + t, t], [o + t]) := rfl

theorem mirrorDPDT_runFrom (s w : List (Fin k)) :
    (mirrorDPDT (k := k)).runFrom () s w = decRun s w := by
  induction w generalizing s with
  | nil => rfl
  | cons o w ih =>
    cases s with
    | nil =>
      simp only [RTDPDT.runFrom, List.head?_nil, mirrorDPDT_step_none, List.tail_nil,
        List.append_nil, ih, decRun, decStep, List.singleton_append]
    | cons t s =>
      by_cases h : o = 0
      · subst h
        simp only [RTDPDT.runFrom, List.head?_cons, mirrorDPDT_step_some, if_true,
          List.tail_cons, List.nil_append, ih, decRun, decStep, List.singleton_append]
      · simp only [RTDPDT.runFrom, List.head?_cons, mirrorDPDT_step_some, h, if_false,
          List.tail_cons, ih, decRun, decStep, List.cons_append, List.nil_append]

/-- The mirror enumerator is computed by a real-time deterministic pushdown transducer. -/
theorem isDPDTEnum_mirror : IsDPDTEnum (mirrorEnum k) :=
  ⟨Unit, Fin k, inferInstance, inferInstance, mirrorDPDT, fun w => by
    show grid k (decRun [] w) = grid k ((mirrorDPDT (k := k)).runFrom () [] w)
    rw [mirrorDPDT_runFrom]⟩

/-- Names of a whole sequence under the coder: `encSeq S i` is the `i`-th letter of `encRun [] S`. -/
def encSeq (S : ℕ → Fin k) (i : ℕ) : Fin k := (encRun [] (pre S (i + 1))).getD i 0

/-! ### The Carton–Perifel sequence `w₁ w̃₁ w₂ w̃₂ ⋯` -/

/-- The `j`-th length-`n` word in lexicographic order (most significant digit first). -/
def lexWord (k : ℕ) [NeZero k] (n j : ℕ) : List (Fin k) :=
  (List.range n).map fun i => (⟨(j / k ^ (n - 1 - i)) % k, Nat.mod_lt _ (Nat.pos_of_neZero k)⟩ : Fin k)

/-- `wₙ`: all length-`n` words concatenated in lexicographic order. -/
def champBlock (k : ℕ) [NeZero k] (n : ℕ) : List (Fin k) :=
  (List.range (k ^ n)).flatMap (lexWord k n)

/-- `wₙ w̃ₙ`. -/
def cpBlock (k : ℕ) [NeZero k] (n : ℕ) : List (Fin k) := champBlock k n ++ (champBlock k n).reverse

/-- `w₁ w̃₁ ⋯ w_N w̃_N`. -/
def cpPrefix (k : ℕ) [NeZero k] (N : ℕ) : List (Fin k) :=
  (List.range N).flatMap fun n => cpBlock k (n + 1)

/-- The Carton–Perifel sequence `x = w₁ w̃₁ w₂ w̃₂ ⋯` (Carton–Perifel 2024, Prop. 2.1). -/
def cpSeq (k : ℕ) [NeZero k] (i : ℕ) : Fin k := (cpPrefix k (i + 1)).getD i 0

/-- The real number with digit sequence `cpSeq k`. -/
def cpReal (k : ℕ) [NeZero k] : ℝ := realOfDigits k fun i => (cpSeq k i : ℕ)

/-- Non-vacuity anchor: on `w₁ w̃₁ = 0 1 2 3 4 4 3 2 1 0` (base 5) the coder emits six zeros
(the leading `0` read on an empty stack, then five cancellations). -/
theorem encRun_cpPrefix_five_one_anchor :
    ((encRun [] (cpPrefix 5 1)).count 0, (cpPrefix 5 1).length) = (6, 10) := by
  decide

end Mirror

end NormalNumbers.FiniteState

/-! ## Cited hypotheses -/

namespace NormalNumbers.Literature

open NormalNumbers NormalNumbers.FiniteState

/-- **Carton–Perifel 2024**, *Deterministic pushdown automata can compress some normal
sequences*, Log. Methods Comput. Sci. 20(3) (2024) 15:1–15:8, arXiv:2205.00734, **Proposition 2.1**
(`pro:formal`): the sequence `x = w₁ w̃₁ w₂ w̃₂ ⋯`, `wₙ` the lexicographic concatenation of all
length-`n` words, is normal ("The proof that the sequence `x` is normal is an easy adaptation that
the Champernowne sequence is normal [Becher–Carton 2018, Thm 7.7.1]").  Their proposition is stated
"for some large enough integer `k`", and the paper notes that `k ⩾ 7` is sufficient; the `k ⩾ 5`
remark there concerns compression experiments, not normality.  So we transcribe it for `k ≥ 7`
only (referee, docs/FINITE-STATE-REFEREE-2026-10-04.md); smaller `k` is the believed leaf
`FiniteState.isNormal_cpSeq`. -/
def cartonPerifel_normal : Prop :=
  ∀ (k : ℕ) [NeZero k], 7 ≤ k → IsNormalSequence k fun i => (cpSeq k i : ℕ)

/-- **Finite-state dimension one implies normal**, in decompression form: Bourke–Hitchcock–
Vinodchandran, *Entropy rates and finite-state dimension*, Theoret. Comput. Sci. 349 (2005)
(a sequence is normal iff its finite-state dimension is `1`), composed with Doty–Moser,
*Finite-state dimension and lossy decompressors*, arXiv:cs/0609096, Theorem 3.12 (the direction `fsDim ≤ dim_FS`; Thm 3.11 is the converse per-prefix form;
Mayordomo arXiv:2208.00157 Thm 3.2 states the fixed-transducer form directly)
(`dim_FS(S) = inf_T liminf K^T(S↾n)/n`), exactly as Pulari 2602.01199 Lemma 1 combines them.
Only the direction "dimension one ⇒ normal" (Schnorr–Stimm's direction) is transcribed.
Referee: that the `FST` model here (outputs in `Σ*`, no injectivity) is the Doty–Moser
decompressor model. -/
def fsDim_one_isNormal : Prop :=
  ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ S : ℕ → Fin k,
    fsDim S = 1 → IsNormalSequence k fun i => (S i : ℕ)

/-- **Pulari 2026, Theorem 3** (`thm:fscoherent-eqchar`, arXiv:2602.01199v2 §4.1): for a
finite-state coherent enumerator `f = grid ∘ M` (`M` an invertible synchronous Mealy machine) and
`x ∈ [0,1)`, `x` is `f`-normal iff `(k^n a_n^f(x))_{n≥1}` is `k`-adically equidistributed.  That
sequence is `⌊k^n x⌋` (his Lemma 6), so reading it through `⌊·⌋` is faithful. -/
def pulari_coherent_eqchar : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ M : Mealy k, M.IsInvertible → ∀ x ∈ Set.Ico (0 : ℝ) 1,
    (IsFNormal (mealyEnum M) x ↔ KAdicEquidist k (scaled (mealyEnum M) x))

end NormalNumbers.Literature

namespace NormalNumbers.FiniteState

variable {k : ℕ}

/-! ## The two questions as Props -/

/-- **Pulari 2602.01199v2 §5, Q-DPDT**: a separator enumerator computed by a deterministic pushdown
transducer and a point `x ∈ [0,1)` with `(k^n a_n^f(x))` integral and `k`-adically
equidistributed while `dim^f_FS(x) < 1`. -/
def PulariDPDTQuestion (k : ℕ) : Prop :=
  ∃ f : List (Fin k) → ℝ, IsSepEnum f ∧ IsDPDTEnum f ∧ ∃ x ∈ Set.Ico (0 : ℝ) 1,
    (∀ n, ((scaled f x n : ℤ) : ℝ) = (k : ℝ) ^ n * bestBelow f x n) ∧
      KAdicEquidist k (scaled f x) ∧ fDim f x < 1

/-- **Pulari 2602.01199v2 §5, Q-weak**, positive form for synchronous finite-state relabelings:
the equidistribution characterization holds for EVERY synchronous Mealy relabeling (no
invertibility assumed) that is a separator enumerator. -/
def PulariWeakening (k : ℕ) : Prop :=
  ∀ M : Mealy k, IsSepEnum (mealyEnum M) → ∀ x ∈ Set.Ico (0 : ℝ) 1,
    (IsFNormal (mealyEnum M) x ↔ KAdicEquidist k (scaled (mealyEnum M) x))

/-! ## Coder combinatorics (free reduction, mirror return, zero count) -/

section Coder

variable [NeZero k]

def encStk : List (Fin k) → List (Fin k) → List (Fin k)
  | s, [] => s
  | s, a :: w => encStk (encStep s a).1 w

theorem encRun_append (s p q : List (Fin k)) :
    encRun s (p ++ q) = encRun s p ++ encRun (encStk s p) q := by
  induction p generalizing s with
  | nil => rfl
  | cons a p ih => simp [encRun, encStk, ih]

theorem encStk_append (s p q : List (Fin k)) :
    encStk s (p ++ q) = encStk (encStk s p) q := by
  induction p generalizing s with
  | nil => rfl
  | cons a p ih => simp [encStk, ih]

theorem count_inv (s w : List (Fin k)) :
    s.length + w.length ≤ 2 * (encRun s w).count 0 + (encStk s w).length := by
  induction w generalizing s with
  | nil => simp [encStk, encRun]
  | cons a w ih =>
    have h1 := ih (encStep s a).1
    have h2 : (encRun (encStep s a).1 w).count 0 ≤ (encRun s (a :: w)).count 0 := by
      simp only [encRun]; exact List.count_le_count_cons ..
    cases s with
    | nil => simp [encStk, encStep] at h1 h2 ⊢; omega
    | cons t s =>
      by_cases h : a = t
      · subst h; simp [encRun, encStk, encStep] at h1 ⊢; omega
      · simp [encStk, encStep, h] at h1 h2 ⊢; omega

/-- Reduced stacks: no two adjacent equal letters. -/
def Red : List (Fin k) → Prop
  | [] => True
  | [_] => True
  | a :: b :: s => a ≠ b ∧ Red (b :: s)

theorem red_tail {t : Fin k} {s : List (Fin k)} (h : Red (t :: s)) : Red s := by
  match s, h with
  | [], _ => trivial
  | _ :: _, h => exact h.2

theorem red_encStep (s : List (Fin k)) (a : Fin k) (h : Red s) : Red (encStep s a).1 := by
  cases s with
  | nil => trivial
  | cons t s =>
    by_cases ha : a = t
    · simp [encStep, ha]; exact red_tail h
    · simp [encStep, ha]; exact ⟨ha, h⟩

theorem encStep_encStep (s : List (Fin k)) (a : Fin k) (h : Red s) :
    (encStep (encStep s a).1 a).1 = s := by
  cases s with
  | nil => simp [encStep]
  | cons t s =>
    by_cases ha : a = t
    · subst ha
      cases s with
      | nil => simp [encStep]
      | cons u s =>
        simp [encStep, h.1]
    · simp [encStep, ha]

theorem red_encStk (s w : List (Fin k)) (h : Red s) : Red (encStk s w) := by
  induction w generalizing s with
  | nil => exact h
  | cons a w ih => exact ih _ (red_encStep s a h)

theorem encStk_reverse (s w : List (Fin k)) (h : Red s) :
    encStk (encStk s w) w.reverse = s := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
    simp only [encStk, List.reverse_cons, encStk_append]
    rw [ih _ (red_encStep s a h)]
    exact encStep_encStep s a h

theorem block_count (w : List (Fin k)) :
    w.length ≤ (encRun [] (w ++ w.reverse)).count 0 ∧ encStk [] (w ++ w.reverse) = [] := by
  have hr := encStk_reverse ([] : List (Fin k)) w trivial
  refine ⟨?_, by rw [encStk_append, hr]⟩
  have h1 := count_inv ([] : List (Fin k)) w
  have h2 := count_inv (encStk [] w) w.reverse
  rw [hr] at h2
  rw [encRun_append, List.count_append]
  simp at h1 h2
  omega

theorem cpPrefix_succ (N : ℕ) : cpPrefix k (N + 1) = cpPrefix k N ++ cpBlock k (N + 1) := by
  simp [cpPrefix, List.range_succ, List.flatMap_append]

theorem cpPrefix_count (N : ℕ) :
    (cpPrefix k N).length ≤ 2 * (encRun [] (cpPrefix k N)).count 0 ∧
      encStk [] (cpPrefix k N) = [] := by
  induction N with
  | zero => simp [cpPrefix, encRun, encStk]
  | succ N ih =>
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := block_count (champBlock k (N + 1))
    rw [cpPrefix_succ, encRun_append, encStk_append, h2, List.count_append, List.length_append]
    refine ⟨?_, h4⟩
    have : (cpBlock k (N+1)).length = 2 * (champBlock k (N+1)).length := by
      simp [cpBlock]; ring
    unfold cpBlock at this ⊢
    omega


theorem pre_succ (S : ℕ → Fin k) (n : ℕ) : pre S (n + 1) = pre S n ++ [S n] := by
  simp only [pre]; rw [List.ofFn_succ_last]; simp

theorem length_pre (S : ℕ → Fin k) (n : ℕ) : (pre S n).length = n := by simp [pre]


theorem cpPrefix_add (N M : ℕ) : ∃ t, cpPrefix k (N + M) = cpPrefix k N ++ t := by
  induction M with
  | zero => exact ⟨[], by simp⟩
  | succ M ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨t ++ cpBlock k (N + M + 1), by rw [← add_assoc, cpPrefix_succ, ht, List.append_assoc]⟩

theorem le_length_cpPrefix (N : ℕ) : N ≤ (cpPrefix k N).length := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [cpPrefix_succ, List.length_append]
    have : 1 ≤ (cpBlock k (N + 1)).length := by
      simp [cpBlock, champBlock, lexWord]
      have : 0 < k ^ (N + 1) := pow_pos (Nat.pos_of_neZero k) _
      nlinarith
    omega

theorem cpSeq_eq (N i : ℕ) (hi : i < (cpPrefix k N).length) :
    cpSeq k i = (cpPrefix k N).getD i 0 := by
  unfold cpSeq
  have h1 := le_length_cpPrefix (k := k) (i + 1)
  rcases le_total N (i + 1) with h | h
  · obtain ⟨t, ht⟩ := cpPrefix_add (k := k) N (i + 1 - N)
    rw [show N + (i + 1 - N) = i + 1 by omega] at ht
    rw [ht, List.getD_append _ _ _ _ hi]
  · obtain ⟨t, ht⟩ := cpPrefix_add (k := k) (i + 1) (N - (i + 1))
    rw [show i + 1 + (N - (i + 1)) = N by omega] at ht
    rw [ht, List.getD_append _ _ _ _ (by omega)]

theorem pre_cpSeq (N : ℕ) : pre (cpSeq k) (cpPrefix k N).length = cpPrefix k N := by
  apply List.ext_getElem (by simp [pre])
  intro i h1 h2
  simp only [pre, List.getElem_ofFn]
  rw [cpSeq_eq N i h2, List.getD_eq_getElem]


theorem countOcc_single (a : ℕ) (l : List ℕ) : countOccurrences [a] l = l.count a := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [countOccurrences, List.tails, List.countP_cons] at ih ⊢
    rw [ih, List.count_cons]
    by_cases h : b = a <;> simp [List.isPrefixOf, h, Ne.symm]

end Coder

/-! ## Grid toolkit, Mealy runs, prefixes of digit expansions -/

/-- The integer value of a word, most significant letter first. -/
def wval : List (Fin k) → ℕ
  | [] => 0
  | a :: u => (a : ℕ) * k ^ u.length + wval u

theorem wval_append (u v : List (Fin k)) : wval (u ++ v) = wval u * k ^ v.length + wval v := by
  induction u with
  | nil => simp [wval]
  | cons a u ih => simp only [List.cons_append, wval, ih, List.length_append, pow_add]; ring

theorem wval_lt (hk : 0 < k) (u : List (Fin k)) : wval u < k ^ u.length := by
  induction u with
  | nil => simp [wval]
  | cons a u ih =>
    simp only [wval, List.length_cons, pow_succ]
    have : (a : ℕ) + 1 ≤ k := a.isLt
    nlinarith

theorem grid_cons (hk : 0 < k) (a : Fin k) (u : List (Fin k)) :
    grid k (a :: u) = ((a : ℝ) + grid k u) / k := by
  simp only [grid, List.length_cons, Fin.sum_univ_succ]
  simp [List.get, pow_succ, Finset.sum_div, div_div, add_div]

theorem grid_eq (hk : 0 < k) (u : List (Fin k)) : grid k u = (wval u : ℝ) / (k : ℝ) ^ u.length := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  induction u with
  | nil => simp [grid, wval]
  | cons a u ih =>
    rw [grid_cons hk, ih]
    simp only [wval, List.length_cons, pow_succ]
    push_cast
    field_simp

theorem grid_mul_pow (hk : 0 < k) (u : List (Fin k)) :
    grid k u * (k : ℝ) ^ u.length = wval u := by
  have : (0 : ℝ) < (k : ℝ) ^ u.length := by positivity
  rw [grid_eq hk]; field_simp

theorem wval_inj (hk : 0 < k) : ∀ (u v : List (Fin k)), u.length = v.length → wval u = wval v → u = v
  | [], [], _, _ => rfl
  | a :: u, b :: v, hl, he => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [wval, hl] at he
    have hu := wval_lt hk u
    have hv := wval_lt hk v
    rw [hl] at hu
    have hab : (a : ℕ) = b := by
      have h1 : ((a : ℕ) * k ^ v.length + wval u) / k ^ v.length = a := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hu, zero_add]
      have h2 : ((b : ℕ) * k ^ v.length + wval v) / k ^ v.length = b := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hv, zero_add]
      rw [← h1, ← h2, he]
    rw [Fin.ext hab, wval_inj hk u v hl (by rw [hab] at he; omega)]

/-- The length-`n` word of value `j mod k^n`. -/
def toWord (hk : 0 < k) : ℕ → ℕ → List (Fin k)
  | 0, _ => []
  | n + 1, j => ⟨j / k ^ n % k, Nat.mod_lt _ hk⟩ :: toWord hk n j

theorem length_toWord (hk : 0 < k) (n j : ℕ) : (toWord hk n j).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [toWord, ih]

theorem wval_toWord (hk : 0 < k) (n j : ℕ) : wval (toWord hk n j) = j % k ^ n := by
  induction n with
  | zero => simp [toWord, wval, Nat.mod_one]
  | succ n ih =>
    simp only [toWord, wval, length_toWord, ih]
    rw [Nat.mod_pow_succ]; ring

/-- Every level grid point `j/k^n`, `j < k^n`, is the grid value of a length-`n` word. -/
theorem exists_grid_eq (hk : 0 < k) (n j : ℕ) (hj : j < k ^ n) :
    ∃ u : List (Fin k), u.length = n ∧ grid k u = (j : ℝ) / (k : ℝ) ^ n :=
  ⟨toWord hk n j, length_toWord hk n j, by
    rw [grid_eq hk, wval_toWord, Nat.mod_eq_of_lt hj, length_toWord]⟩

theorem grid_mem_Ico (hk : 0 < k) (u : List (Fin k)) : grid k u ∈ Set.Ico (0 : ℝ) 1 := by
  rw [grid_eq hk]
  have hp : (0 : ℝ) < (k : ℝ) ^ u.length := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hp]
  exact_mod_cast wval_lt hk u


def copyFST (k : ℕ) : FST k where
  m := 0
  δ := fun _ _ => 0
  ν := fun _ a => [a]

theorem copyFST_run (w : List (Fin k)) : (copyFST k).run w = w := by
  unfold FST.run
  induction w with
  | nil => rfl
  | cons a w ih => simp [FST.runFrom, copyFST] at ih ⊢; exact ih


/-- State reached after reading `w`. -/
def Mealy.stateFrom (M : Mealy k) : M.Q → List (Fin k) → M.Q
  | q, [] => q
  | q, a :: w => M.stateFrom (M.δ q a) w

theorem Mealy.runFrom_append (M : Mealy k) (q : M.Q) (u v : List (Fin k)) :
    M.runFrom q (u ++ v) = M.runFrom q u ++ M.runFrom (M.stateFrom q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih => simp [Mealy.runFrom, Mealy.stateFrom, ih]

theorem Mealy.stateFrom_append (M : Mealy k) (q : M.Q) (u v : List (Fin k)) :
    M.stateFrom q (u ++ v) = M.stateFrom (M.stateFrom q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih => simp [Mealy.stateFrom, ih]

theorem Mealy.length_runFrom (M : Mealy k) (q : M.Q) (u : List (Fin k)) :
    (M.runFrom q u).length = u.length := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih => simp [Mealy.runFrom, ih]


theorem grid_append (hk : 0 < k) (u v : List (Fin k)) :
    grid k (u ++ v) = grid k u + grid k v / (k : ℝ) ^ u.length := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [grid_eq hk, grid_eq hk, grid_eq hk, wval_append, List.length_append, pow_add]
  push_cast
  field_simp

theorem grid_mul_pow_le (hk : 0 < k) (u : List (Fin k)) (n : ℕ) (hu : u.length ≤ n) :
    grid k u * (k : ℝ) ^ n = ((wval u * k ^ (n - u.length) : ℕ) : ℝ) := by
  have : (k : ℝ) ^ n = (k : ℝ) ^ u.length * (k : ℝ) ^ (n - u.length) := by
    rw [← pow_add]; congr 1; omega
  rw [this, ← mul_assoc, grid_mul_pow hk]; push_cast; ring



theorem pre_succ' (S : ℕ → Fin k) (n : ℕ) : pre S (n + 1) = pre S n ++ [S n] := by
  simp only [pre]; rw [List.ofFn_succ_last]; simp

theorem wval_pre_succ (S : ℕ → Fin k) (i : ℕ) :
    wval (pre S (i + 1)) = ∑ t ∈ Finset.range (i + 1), (S t : ℕ) * k ^ (i - t) := by
  induction i with
  | zero => simp [pre, wval]
  | succ i ih =>
    rw [pre_succ', wval_append, ih, Finset.sum_range_succ (n := i + 1)]
    simp only [List.length_singleton, pow_one, wval, List.length_nil, pow_zero, mul_one, add_zero,
      Nat.sub_self]
    rw [Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_range] at ht
    rw [mul_assoc, ← pow_succ]; congr 2; omega

/-- With proper digits, `⌊x k^n⌋` is the value of the length-`n` prefix. -/
theorem floor_mul_pow_eq_wval (hk : 2 ≤ k) (S : ℕ → Fin k)
    (hp : ProperDigits k fun i => (S i : ℕ)) (n : ℕ) :
    ⌊realOfDigits k (fun i => (S i : ℕ)) * (k : ℝ) ^ n⌋ = (wval (pre S n) : ℤ) := by
  cases n with
  | zero =>
    have hx := realOfDigits_mem_Ico k hk _ (fun i => (S i).isLt) hp
    simp only [pow_zero, mul_one, pre, List.ofFn_zero, wval, Nat.cast_zero]
    exact Int.floor_eq_zero_iff.mpr hx
  | succ i =>
    rw [floor_realOfDigits_mul_pow k hk _ (fun i => (S i).isLt) hp i, wval_pre_succ]

theorem abs_grid_pre_sub_lt (hk : 2 ≤ k) (S : ℕ → Fin k)
    (hp : ProperDigits k fun i => (S i : ℕ)) (n : ℕ) :
    |grid k (pre S n) - realOfDigits k (fun i => (S i : ℕ))| < ((k : ℝ) ^ n)⁻¹ := by
  have hk0 : 0 < k := by omega
  set x := realOfDigits k (fun i => (S i : ℕ))
  have hp' : (0 : ℝ) < (k : ℝ) ^ n := by positivity
  have hF := floor_mul_pow_eq_wval hk S hp n
  have h1 := Int.floor_le (x * (k : ℝ) ^ n)
  have h2 := Int.lt_floor_add_one (x * (k : ℝ) ^ n)
  rw [hF] at h1 h2
  push_cast at h1 h2
  have hg : grid k (pre S n) * (k : ℝ) ^ n = wval (pre S n) := by
    have := grid_mul_pow hk0 (pre S n); rwa [show (pre S n).length = n by simp [pre]] at this
  rw [abs_lt]
  constructor
  · rw [neg_lt_sub_iff_lt_add, ← sub_lt_iff_lt_add']
    rw [← mul_lt_mul_iff_of_pos_right hp', sub_mul, inv_mul_cancel₀ hp'.ne', hg]; linarith
  · have : (grid k (pre S n) - x) * (k : ℝ) ^ n ≤ 0 := by rw [sub_mul, hg]; linarith
    have h3 : grid k (pre S n) - x ≤ 0 := by
      by_contra hc; push_neg at hc; nlinarith
    have : (0 : ℝ) < ((k : ℝ) ^ n)⁻¹ := by positivity
    linarith


theorem tendsto_div_of_two_sided {A B : ℕ → ℕ} {C : ℕ} {L : ℝ}
    (hAB : ∀ n, A n ≤ B n + C) (hBA : ∀ n, B n ≤ A n + C)
    (h : Tendsto (fun n => (A n : ℝ) / n) atTop (𝓝 L)) :
    Tendsto (fun n => (B n : ℝ) / n) atTop (𝓝 L) := by
  have hC : Tendsto (fun n : ℕ => (C : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using h.sub hC)
    (by simpa using h.add hC) (fun n => ?_) (fun n => ?_)
  · dsimp only; rw [← sub_div]
    have : (A n : ℝ) ≤ B n + C := by exact_mod_cast hAB n
    gcongr; linarith
  · dsimp only; rw [← add_div]
    have : (B n : ℝ) ≤ A n + C := by exact_mod_cast hBA n
    gcongr

theorem pre_split (S : ℕ → Fin k) (n m : ℕ) (h : m ≤ n) :
    pre S n = pre S (n - m) ++ List.ofFn fun j : Fin m => S (n - m + j) := by
  apply List.ext_getElem (by simp [pre]; omega)
  intro i h1 h2
  simp only [pre, List.getElem_ofFn]
  rw [List.getElem_append]
  split_ifs with hi
  · simp
  · simp only [List.getElem_ofFn]; congr 1; simp only [List.length_ofFn] at hi ⊢; omega

/-! ## Leaves (frozen statements; all proved — the percentages are the pre-proof confidences) -/

/-- **Leaf (92%).**  A length-preserving naming map that is surjective on every level gives a
separator enumerator.  Proof: `grid` maps `Σ^n` onto `{j/k^n}`, which lies in `[0,1)`, and the
union over `n` is dense. -/
theorem isSepEnum_grid_of_levelSurj (hk : 2 ≤ k) (g : List (Fin k) → List (Fin k))
    (hlen : ∀ w, (g w).length = w.length)
    (hsurj : ∀ u : List (Fin k), ∃ w, w.length = u.length ∧ g w = u) :
    IsSepEnum fun w => grid k (g w) := by
  have hk0 : 0 < k := by omega
  refine ⟨fun w => grid_mem_Ico hk0 _, fun a c ha hac hc => ?_⟩
  have hk1 : (1 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hac) (inv_lt_one_of_one_lt₀ hk1)
  rw [inv_pow] at hn
  have hp : (0 : ℝ) < (k : ℝ) ^ n := by positivity
  set j : ℕ := ⌊a * (k : ℝ) ^ n⌋.toNat + 1
  have hj1 : a * (k : ℝ) ^ n < j := by
    have := Int.lt_floor_add_one (a * (k : ℝ) ^ n)
    have h0 : (0 : ℤ) ≤ ⌊a * (k : ℝ) ^ n⌋ := Int.floor_nonneg.mpr (by positivity)
    simp only [j]; push_cast
    rw [show ((⌊a * (k : ℝ) ^ n⌋.toNat : ℕ) : ℝ) = ((⌊a * (k : ℝ) ^ n⌋ : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg h0]
    linarith
  have hj2 : (j : ℝ) ≤ a * (k : ℝ) ^ n + 1 := by
    have := Int.floor_le (a * (k : ℝ) ^ n)
    have h0 : (0 : ℤ) ≤ ⌊a * (k : ℝ) ^ n⌋ := Int.floor_nonneg.mpr (by positivity)
    simp only [j]; push_cast
    rw [show ((⌊a * (k : ℝ) ^ n⌋.toNat : ℕ) : ℝ) = ((⌊a * (k : ℝ) ^ n⌋ : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg h0]
    linarith
  have hlt : (j : ℝ) / (k : ℝ) ^ n < c := by
    rw [div_lt_iff₀ hp]
    have : 1 < (c - a) * (k : ℝ) ^ n := by rwa [← div_lt_iff₀ hp, one_div]
    linarith
  have hjk : j < k ^ n := by
    have : (j : ℝ) < (k : ℝ) ^ n := by
      have := (div_lt_iff₀ hp).mp (lt_of_lt_of_le hlt hc); linarith
    exact_mod_cast this
  obtain ⟨u, hu, hgu⟩ := exists_grid_eq hk0 n j hjk
  obtain ⟨w, -, hw⟩ := hsurj u
  refine ⟨w, ?_, ?_⟩
  · show a < grid k (g w)
    rw [hw, hgu, lt_div_iff₀ hp]; exact hj1
  · show grid k (g w) < c
    rw [hw, hgu]; exact hlt

/-- **Leaf (92%).**  Pulari Lemma 6 for any levelwise-surjective length-preserving relabeling:
`k^n a_n^f(x) = ⌊k^n x⌋`.  Proof: the values at lengths `≤ n` are exactly the grid points of
denominator dividing `k^n`, and the largest one `≤ x` is `⌊k^n x⌋/k^n`. -/
theorem bestBelow_grid_of_levelSurj (hk : 2 ≤ k) (g : List (Fin k) → List (Fin k))
    (hlen : ∀ w, (g w).length = w.length)
    (hsurj : ∀ u : List (Fin k), ∃ w, w.length = u.length ∧ g w = u)
    (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) (n : ℕ) :
    (k : ℝ) ^ n * bestBelow (fun w => grid k (g w)) x n = ⌊(k : ℝ) ^ n * x⌋ := by
  have hk0 : 0 < k := by omega
  have hp : (0 : ℝ) < (k : ℝ) ^ n := by positivity
  set F := ⌊(k : ℝ) ^ n * x⌋ with hFdef
  have hF0 : 0 ≤ F := Int.floor_nonneg.mpr (mul_nonneg hp.le hx.1)
  have hFlt : F < ((k ^ n : ℕ) : ℤ) := by
    rw [Int.floor_lt]; push_cast
    have := mul_lt_mul_of_pos_left hx.2 hp; linarith
  have hG : IsGreatest {y | ∃ w : List (Fin k), w.length ≤ n ∧ grid k (g w) = y ∧ y ≤ x}
      ((F : ℝ) / (k : ℝ) ^ n) := by
    constructor
    · obtain ⟨u, hu, hgu⟩ := exists_grid_eq hk0 n F.toNat (by omega)
      obtain ⟨w, hw, hgw⟩ := hsurj u
      have hc : ((F.toNat : ℕ) : ℝ) = (F : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hF0
      refine ⟨w, by omega, by rw [hgw, hgu, hc], ?_⟩
      rw [div_le_iff₀ hp, mul_comm]; exact Int.floor_le _
    · rintro y ⟨w, hw, rfl, hy⟩
      have h := grid_mul_pow_le hk0 (g w) n (by rw [hlen]; exact hw)
      have hN : (((wval (g w) * k ^ (n - (g w).length) : ℕ) : ℤ)) ≤ F := by
        rw [Int.le_floor]; push_cast
        have := mul_le_mul_of_nonneg_right hy hp.le
        push_cast at h; linarith
      rw [le_div_iff₀ hp, h]; exact_mod_cast hN
  have : bestBelow (fun w => grid k (g w)) x n = (F : ℝ) / (k : ℝ) ^ n := hG.csSup_eq
  rw [this]; field_simp

/-- **Leaf (92%).**  Normal digits give `k`-adically equidistributed `⌊k^n x⌋` (Pulari Thm 2,
Kuipers–Niederreiter).  Proof: for `n ≥ m`, `⌊k^n x⌋ mod k^m` is the value of the digit block
`x_{n-m+1} ⋯ x_n`, so the count of `n ≤ N` with residue `r` is the occurrence count of the length-`m`
word of `r` in the first `N` digits, up to `m`. -/
theorem kAdicEquidist_floor_of_normal (hk : 2 ≤ k) (S : ℕ → Fin k)
    (hn : IsNormalSequence k fun i => (S i : ℕ)) :
    KAdicEquidist k fun n => ⌊(k : ℝ) ^ n * realOfDigits k (fun i => (S i : ℕ))⌋ := by
  classical
  have hk0 : 0 < k := by omega
  have hp := properDigits_of_isNormalSequence hk hn
  set s : ℕ → ℕ := fun i => (S i : ℕ) with hs
  intro m hm r hr
  set w : List ℕ := (toWord hk0 m r).map Fin.val with hwdef
  have hwlen : w.length = m := by simp [w, length_toWord]
  have hw0 : w ≠ [] := by intro h; rw [h] at hwlen; simp at hwlen; omega
  have hwd : ∀ d ∈ w, d < k := by
    intro d hd; simp only [w, List.mem_map] at hd; obtain ⟨a, -, rfl⟩ := hd; exact a.isLt
  have hA := tendsto_div_of_bounded_diff (C := w.length)
    (fun n => (card_filter_matchesAt_le s w hw0 n).1)
    (fun n => (card_filter_matchesAt_le s w hw0 n).2) (hn w hw0 hwd)
  rw [hwlen] at hA
  have hkm : (0 : ℤ) < (k : ℤ) ^ m := by positivity
  have key : ∀ n, m ≤ n → ((⌊(k : ℝ) ^ n * realOfDigits k s⌋ ≡ (r : ℤ) [ZMOD (k : ℤ) ^ m]) ↔
      MatchesAt s w (n - m)) := by
    intro n hmn
    set L : List (Fin k) := List.ofFn fun j : Fin m => S (n - m + j) with hL
    have hLlen : L.length = m := by simp [L]
    rw [mul_comm, floor_mul_pow_eq_wval hk S hp n, pre_split S n m hmn, wval_append, hLlen]
    have hLlt := wval_lt hk0 L
    rw [hLlen] at hLlt
    have e1 : Int.ModEq ((k : ℤ) ^ m) (((wval (pre S (n - m)) * k ^ m + wval L : ℕ) : ℤ)) (r : ℤ)
        ↔ wval L = r := by
      unfold Int.ModEq
      push_cast
      rw [add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by positivity)
        (by exact_mod_cast hLlt), Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hr)]
      exact_mod_cast Iff.rfl
    rw [e1]
    have e2 : wval L = r ↔ L = toWord hk0 m r := by
      constructor
      · intro h
        exact wval_inj hk0 _ _ (by rw [hLlen, length_toWord])
          (by rw [h, wval_toWord, Nat.mod_eq_of_lt hr])
      · intro h; rw [h, wval_toWord, Nat.mod_eq_of_lt hr]
    rw [e2]
    constructor
    · intro h j hj
      rw [hwlen] at hj
      have : L[j]'(by omega) = (toWord hk0 m r)[j]'(by rw [length_toWord]; omega) := by
        simp only [h]
      simp only [L, List.getElem_ofFn] at this
      simp only [s, w, List.getD_eq_getElem?_getD, List.getElem?_map]
      rw [List.getElem?_eq_getElem (by rw [length_toWord]; omega)]
      simp [this]
    · intro h
      apply List.ext_getElem (by rw [hLlen, length_toWord])
      intro j h1 h2
      have := h j (by omega)
      simp only [s, w, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem h2] at this
      simp only [L, List.getElem_ofFn]
      exact Fin.ext (by simpa using this)
  rw [one_div]
  refine tendsto_div_of_two_sided (C := m) (fun N => ?_) (fun N => ?_) hA
  · beta_reduce
    calc ((Finset.range N).filter (MatchesAt s w)).card
        ≤ ((((Finset.Icc 1 N).filter fun n =>
              ⌊(k : ℝ) ^ n * realOfDigits k s⌋ ≡ (r : ℤ) [ZMOD (k : ℤ) ^ m]).image
              (· - m)) ∪ Finset.Ico (N - m) N).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_range] at hi
          simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_Icc,
            Finset.mem_Ico]
          by_cases hfit : i + m ≤ N
          · left
            refine ⟨i + m, ⟨⟨by omega, hfit⟩, ?_⟩, by omega⟩
            rw [key (i + m) (by omega), show i + m - m = i by omega]; exact hi.2
          · right; omega
      _ ≤ _ := by
          refine le_trans (Finset.card_union_le _ _) ?_
          rw [Nat.card_Ico]
          have := Finset.card_image_le (s := (Finset.Icc 1 N).filter fun n =>
              ⌊(k : ℝ) ^ n * realOfDigits k s⌋ ≡ (r : ℤ) [ZMOD (k : ℤ) ^ m]) (f := (· - m))
          omega
  · beta_reduce
    calc ((Finset.Icc 1 N).filter fun n =>
            ⌊(k : ℝ) ^ n * realOfDigits k s⌋ ≡ (r : ℤ) [ZMOD (k : ℤ) ^ m]).card
        ≤ ((((Finset.range N).filter (MatchesAt s w)).image (· + m)) ∪ Finset.range m).card := by
          apply Finset.card_le_card
          intro n hn'
          simp only [Finset.mem_filter, Finset.mem_Icc] at hn'
          simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
          by_cases hmn : m ≤ n
          · left
            exact ⟨n - m, ⟨by omega, (key n hmn).mp hn'.2⟩, by omega⟩
          · right; omega
      _ ≤ _ := by
          refine le_trans (Finset.card_union_le _ _) ?_
          rw [Finset.card_range]
          have := Finset.card_image_le (s := (Finset.range N).filter (MatchesAt s w)) (f := (· + m))
          omega

/-- **Leaf (88%).**  A synchronous decoder `g` that maps the prefixes of a name sequence `N` to the
prefixes of `S` transfers compression: `dim^g(x) ≤ dim_FS(N)` at `x = 0.S`.  Proof: at `δ = k^{-n}`
the name `N↾n` has `|grid(S↾n) − x| < k^{-n}` (proper digits), so
`K^{T,f}_{k^{-n}}(x) ≤ K^T(N↾n)`; take `liminf` along `δ = k^{-n}` and `inf_T`. -/
theorem fDim_le_fsDim_of_decode (hk : 2 ≤ k) (g : List (Fin k) → List (Fin k))
    (N S : ℕ → Fin k) (hg : ∀ n, g (pre N n) = pre S n)
    (hp : ProperDigits k fun i => (S i : ℕ)) :
    fDim (fun w => grid k (g w)) (realOfDigits k fun i => (S i : ℕ)) ≤ fsDim N := by
  set x := realOfDigits k fun i => (S i : ℕ)
  have hk1 : (1 : ℝ) < k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  refine iInf_mono fun T => ?_
  set δ : ℕ → ℝ := fun n => ((k : ℝ) ^ n)⁻¹
  have hδ : Tendsto δ atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · simp only [δ, ← inv_pow]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hk1)
    · show 0 < δ n; positivity
  refine le_trans (hδ.liminf_le_liminf_comp) (liminf_le_liminf ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Function.comp]
  have hlog : Real.logb k (1 / δ n) = n := by
    simp only [δ, one_div, inv_inv, Real.logb_pow, Real.logb_self_eq_one hk1, mul_one]
  rw [hlog, ENNReal.ofReal_natCast]
  gcongr
  have : approxK T (fun w => grid k (g w)) (δ n) x ≤ infoK T (pre N n) := by
    refine iInf_le_of_le (pre N n) (iInf_le_of_le ?_ le_rfl)
    simp only [hg]; exact abs_grid_pre_sub_lt hk S hp n
  exact_mod_cast this

/-- **Leaf (95%).**  The one-state copying FST gives `K^T(S↾n) ≤ n`. -/
theorem fsDim_le_one (hk : 2 ≤ k) (S : ℕ → Fin k) : fsDim S ≤ 1 := by
  refine le_trans (iInf_le _ (copyFST k)) ?_
  refine le_trans (liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)) ?_
  refine limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun n => ?_)
  have h : infoK (copyFST k) (pre S n) ≤ n := by
    unfold infoK
    exact iInf_le_of_le (pre S n) (iInf_le_of_le (copyFST_run _) (by simp [pre]))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : infoK (copyFST k) (pre S 0) = 0 := by simpa using h
    simp [h0]
  · refine ENNReal.div_le_of_le_mul ?_
    rw [one_mul]
    exact_mod_cast h

/-- **Leaf (97%).**  The coder is online: the names of `S↾n` are the prefix of `encSeq S`. -/
theorem pre_encSeq [NeZero k] (S : ℕ → Fin k) (n : ℕ) :
    pre (encSeq S) n = encRun [] (pre S n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hl : (encRun [] (pre S n)).length = n := by rw [length_encRun, length_pre]
    rw [pre_succ, ih, pre_succ, encRun_append]
    congr 1
    simp only [encSeq, pre_succ, encRun_append, encRun]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hl]

/-- **Leaf (92%), the counting core.**  On `w₁ w̃₁ ⋯ w_N w̃_N` the coder emits at least a quarter
zeros.  Proof: the coder's stack after a prefix `p` is the free reduction `red(p)` under `aa → ε`,
and `red(w w̃) = ε`, so every block `wₙ w̃ₙ` starts on an empty stack.  Reading `w̃ₙ` takes the
stack from `red(wₙ)` (length `r`) back to empty, so its pops `C` and pushes `P` satisfy
`C + P = |wₙ|`, `C − P = r`, i.e. `C ≥ |wₙ|/2`; each pop emits `0`.  Summing,
`#0 ≥ Σ|wₙ|/2 = |prefix|/4`.  (Numerics, `probe` in the audit doc: the true frequency is ≈ 1/2.) -/
theorem length_le_four_mul_count_zero [NeZero k] (N : ℕ) :
    (cpPrefix k N).length ≤ 4 * (encRun [] (cpPrefix k N)).count 0 := by
  have := (cpPrefix_count (k := k) N).1; omega

/-- **Leaf (90%).**  For `k ≥ 5` the names of the Carton–Perifel sequence are not normal: the digit
`0` has frequency `≥ 1/4 > 1/k` along the block ends `|cpPrefix k N|` (from
`length_le_four_mul_count_zero` and `pre_encSeq`). -/
theorem not_isNormal_encSeq_cpSeq [NeZero k] (hk : 5 ≤ k) :
    ¬ IsNormalSequence k fun i => (encSeq (cpSeq k) i : ℕ) := by
  intro hn
  have h := hn [0] (by simp) (by simp; omega)
  set L : ℕ → ℕ := fun N => (cpPrefix k (N + 1)).length
  have hL : Tendsto L atTop atTop :=
    tendsto_atTop_mono (fun N => le_trans (Nat.le_succ N) (le_length_cpPrefix (N + 1)))
      tendsto_id
  have h2 := h.comp hL
  have hbound : ∀ N, (1 : ℝ) / 4 ≤ ((fun n => (countOccurrences [0]
      ((List.range n).map fun i => (encSeq (cpSeq k) i : ℕ)) : ℝ) / n) ∘ L) N := by
    intro N
    simp only [Function.comp, countOcc_single]
    have hmap : (List.range (L N)).map (fun i => (encSeq (cpSeq k) i : ℕ))
        = (pre (encSeq (cpSeq k)) (L N)).map (fun a : Fin k => (a : ℕ)) := by
      apply List.ext_getElem (by simp [pre])
      intro i h1 h2
      simp [pre]
    have hcm := List.count_map_of_injective (pre (encSeq (cpSeq k)) (L N)) Fin.val
      Fin.val_injective (0 : Fin k)
    simp only [Fin.val_zero] at hcm
    rw [hmap, hcm, pre_encSeq]
    have hc := length_le_four_mul_count_zero (k := k) (N + 1)
    have hpos : 0 < L N := lt_of_lt_of_le (Nat.succ_pos N) (le_length_cpPrefix (N + 1))
    simp only [L, pre_cpSeq] at hc hpos ⊢
    rw [div_le_div_iff₀ (by norm_num) (by exact_mod_cast hpos)]
    have : ((cpPrefix k (N + 1)).length : ℝ) ≤ 4 * ((encRun [] (cpPrefix k (N + 1))).count 0 : ℝ) := by
      exact_mod_cast hc
    simpa [Fin.val_zero] using (by linarith : (1:ℝ) * ((cpPrefix k (N + 1)).length : ℝ) ≤ ((encRun [] (cpPrefix k (N + 1))).count 0 : ℝ) * 4)
  have hle := ge_of_tendsto h2 (Eventually.of_forall hbound)
  have hk' : (5 : ℝ) ≤ k := by exact_mod_cast hk
  simp at hle
  have : (k : ℝ)⁻¹ ≤ 1 / 5 := by rw [one_div]; exact inv_anti₀ (by norm_num) hk'
  linarith


/-- **New (proved): base `≥ 3`.**  The block bound `cpPrefix_count` (`#0 ≥ |prefix|/2` at every
block end, sharper than the frozen `1/4` leaf) separates from `1/k` already for `k ≥ 3`, so the
names of the Carton–Perifel sequence are not normal for every `k ≥ 3`.  This settles the
`ZeroFreqHalf` route of `FiniteStateSelectionStretch` without needing the exact frequency. -/
theorem not_isNormal_encSeq_cpSeq_of_three [NeZero k] (hk : 3 ≤ k) :
    ¬ IsNormalSequence k fun i => (encSeq (cpSeq k) i : ℕ) := by
  intro hn
  have h := hn [0] (by simp) (by simp; omega)
  set L : ℕ → ℕ := fun N => (cpPrefix k (N + 1)).length
  have hL : Tendsto L atTop atTop :=
    tendsto_atTop_mono (fun N => le_trans (Nat.le_succ N) (le_length_cpPrefix (N + 1)))
      tendsto_id
  have h2 := h.comp hL
  have hbound : ∀ N, (1 : ℝ) / 2 ≤ ((fun n => (countOccurrences [0]
      ((List.range n).map fun i => (encSeq (cpSeq k) i : ℕ)) : ℝ) / n) ∘ L) N := by
    intro N
    simp only [Function.comp, countOcc_single]
    have hmap : (List.range (L N)).map (fun i => (encSeq (cpSeq k) i : ℕ))
        = (pre (encSeq (cpSeq k)) (L N)).map (fun a : Fin k => (a : ℕ)) := by
      apply List.ext_getElem (by simp [pre])
      intro i h1 h2
      simp [pre]
    have hcm := List.count_map_of_injective (pre (encSeq (cpSeq k)) (L N)) Fin.val
      Fin.val_injective (0 : Fin k)
    simp only [Fin.val_zero] at hcm
    rw [hmap, hcm, pre_encSeq]
    have hc := (cpPrefix_count (k := k) (N + 1)).1
    have hpos : 0 < L N := lt_of_lt_of_le (Nat.succ_pos N) (le_length_cpPrefix (N + 1))
    simp only [L, pre_cpSeq] at hc hpos ⊢
    rw [div_le_div_iff₀ (by norm_num) (by exact_mod_cast hpos)]
    have : ((cpPrefix k (N + 1)).length : ℝ) ≤ 2 * ((encRun [] (cpPrefix k (N + 1))).count 0 : ℝ) := by
      exact_mod_cast hc
    simpa [Fin.val_zero] using (by linarith : (1:ℝ) * ((cpPrefix k (N + 1)).length : ℝ) ≤ ((encRun [] (cpPrefix k (N + 1))).count 0 : ℝ) * 2)
  have hle := ge_of_tendsto h2 (Eventually.of_forall hbound)
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  simp at hle
  have : (k : ℝ)⁻¹ ≤ 1 / 3 := by rw [one_div]; exact inv_anti₀ (by norm_num) hk'
  linarith

/-- **Leaf (95%).**  A synchronous Mealy relabeling that is a separator enumerator is surjective
on every level.  Proof: if `u ∈ Σ^n` is missed, the open interval `(grid u, grid u + k^{-n})`
contains no value — a value from a word of length `≤ n` is a multiple of `k^{-n}`, and a value from
a longer word `w` lies in it only if `M(w)↾n = M(w↾n) = u` (synchronicity). -/
theorem mealy_levelSurj_of_isSepEnum (hk : 2 ≤ k) (M : Mealy k)
    (hM : IsSepEnum (mealyEnum M)) :
    ∀ u : List (Fin k), ∃ w, w.length = u.length ∧ M.run w = u := by
  have hk0 : 0 < k := by omega
  intro u
  by_contra hne
  push_neg at hne
  set n := u.length with hn
  have hp : (0 : ℝ) < (k : ℝ) ^ n := by positivity
  have hU := wval_lt hk0 u
  have hgu := grid_mul_pow hk0 u
  rw [← hn] at hgu
  have hle : grid k u + 1 / (k : ℝ) ^ n ≤ 1 := by
    rw [grid_eq hk0, ← hn, ← add_div, div_le_one hp]
    exact_mod_cast hU
  obtain ⟨w, hw1, hw2⟩ := hM.2 (grid k u) (grid k u + 1 / (k : ℝ) ^ n) (grid_mem_Ico hk0 u).1
    (by have : 0 < 1 / (k : ℝ) ^ n := by positivity
        linarith) hle
  simp only [mealyEnum] at hw1 hw2
  have hlo : (wval u : ℝ) < grid k (M.run w) * (k : ℝ) ^ n := by
    rw [← hgu]; exact mul_lt_mul_of_pos_right hw1 hp
  have hhi : grid k (M.run w) * (k : ℝ) ^ n < (wval u : ℝ) + 1 := by
    have := mul_lt_mul_of_pos_right hw2 hp
    rw [add_mul, hgu, one_div, inv_mul_cancel₀ hp.ne'] at this; exact this
  have hlenw : (M.run w).length = w.length := Mealy.length_runFrom M _ w
  rcases le_or_gt w.length n with hm | hm
  · rw [grid_mul_pow_le hk0 _ n (by omega)] at hlo hhi
    have h1 : wval u < wval (M.run w) * k ^ (n - (M.run w).length) := by exact_mod_cast hlo
    have h2 : wval (M.run w) * k ^ (n - (M.run w).length) < wval u + 1 := by exact_mod_cast hhi
    omega
  · have hsplit : M.run w = M.run (w.take n) ++ M.runFrom (M.stateFrom M.q0 (w.take n)) (w.drop n) := by
      conv_lhs => rw [← List.take_append_drop n w]
      exact Mealy.runFrom_append M _ _ _
    have hl1 : (M.run (w.take n)).length = n := by
      rw [Mealy.run, Mealy.length_runFrom, List.length_take]; omega
    set v1 := M.run (w.take n)
    set v2 := M.runFrom (M.stateFrom M.q0 (w.take n)) (w.drop n)
    have hg : grid k (M.run w) * (k : ℝ) ^ n = wval v1 + grid k v2 := by
      rw [hsplit, grid_append hk0, hl1, add_mul, ← hl1, grid_mul_pow hk0, hl1,
        div_mul_cancel₀ _ hp.ne']
    rw [hg] at hlo hhi
    have h2 := grid_mem_Ico hk0 v2
    have e1 : wval u < wval v1 + 1 := by
      have : (wval u : ℝ) < wval v1 + 1 := by linarith [h2.2]
      exact_mod_cast this
    have e2 : wval v1 < wval u + 1 := by
      have : (wval v1 : ℝ) < wval u + 1 := by linarith [h2.1]
      exact_mod_cast this
    have : v1 = u := wval_inj hk0 _ _ (by rw [hl1]) (by omega)
    exact hne (w.take n) (by rw [List.length_take]; omega) this

/-- **Leaf (93%).**  A levelwise-surjective synchronous Mealy machine agrees with an invertible
one.  Proof: surjectivity on `Σ^{n+1}` forces `out q` to be a permutation at every state `q`
reached by a length-`n` word (else two one-letter extensions collide and `|Σ^{n+1}|` is missed);
replace `out` by the identity at unreachable states. -/
theorem exists_invertible_of_levelSurj (M : Mealy k)
    (hM : ∀ u : List (Fin k), ∃ w, w.length = u.length ∧ M.run w = u) :
    ∃ M' : Mealy k, M'.IsInvertible ∧ ∀ w, M'.run w = M.run w := by
  classical
  -- injectivity of `M.run` on each level
  have hinj : ∀ n (w₁ w₂ : List (Fin k)), w₁.length = n → w₂.length = n →
      M.run w₁ = M.run w₂ → w₁ = w₂ := by
    intro n
    let F : List.Vector (Fin k) n → List.Vector (Fin k) n := fun v =>
      ⟨M.run v.1, by rw [Mealy.run, Mealy.length_runFrom, v.2]⟩
    have hs : Function.Surjective F := by
      intro v
      obtain ⟨w, hw, hw'⟩ := hM v.1
      exact ⟨⟨w, hw.trans v.2⟩, Subtype.ext hw'⟩
    have hi := Finite.injective_iff_surjective.mpr hs
    intro w₁ w₂ h₁ h₂ he
    have := @hi ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ (Subtype.ext he)
    exact congrArg Subtype.val this
  let R : M.Q → Prop := fun q => ∃ w, M.stateFrom M.q0 w = q
  have hbij : ∀ q, R q → Function.Bijective (M.out q) := by
    rintro q ⟨w, rfl⟩
    rw [← Finite.injective_iff_bijective]
    intro a b hab
    have := hinj (w.length + 1) (w ++ [a]) (w ++ [b]) (by simp) (by simp)
      (by simp [Mealy.run, Mealy.runFrom_append, Mealy.runFrom, hab])
    simpa using this
  let M' : Mealy k :=
    { Q := M.Q, fintype := M.fintype, q0 := M.q0, δ := M.δ,
      out := fun q => if R q then M.out q else id }
  refine ⟨M', fun q => ?_, fun w => ?_⟩
  · show Function.Bijective (if R q then M.out q else id)
    split_ifs with h
    · exact hbij q h
    · exact Function.bijective_id
  · have key : ∀ (u w : List (Fin k)),
        M'.runFrom (M.stateFrom M.q0 u) w = M.runFrom (M.stateFrom M.q0 u) w := by
      intro u w
      induction w generalizing u with
      | nil => rfl
      | cons a w ih =>
        have hR : R (M.stateFrom M.q0 u) := ⟨u, rfl⟩
        have := ih (u ++ [a])
        simp only [Mealy.stateFrom_append, Mealy.stateFrom] at this
        simp only [Mealy.runFrom]
        exact congrArg₂ _ (by simp [M', hR]) this
    exact key [] w

/-! ## Wiring (proved) -/

/-- Not normal ⇒ finite-state dimension `< 1`, from the cited direction and `fsDim_le_one`. -/
theorem fsDim_lt_one_of_not_normal (hFS : Literature.fsDim_one_isNormal) [NeZero k]
    (hk : 2 ≤ k) (S : ℕ → Fin k) (h : ¬ IsNormalSequence k fun i => (S i : ℕ)) :
    fsDim S < 1 :=
  lt_of_le_of_ne (fsDim_le_one hk S) fun h1 => h (hFS k hk S h1)

/-- All the facts about the mirror enumerator at the Carton–Perifel point, for any base in which
the coder's names of `cpSeq k` are not normal. -/
theorem mirrorEnum_cpReal_facts_of_not_normal [NeZero k] (hk2 : 2 ≤ k)
    (hnn : ¬ IsNormalSequence k fun i => (encSeq (cpSeq k) i : ℕ))
    (hn : IsNormalSequence k fun i => (cpSeq k i : ℕ)) (hFS : Literature.fsDim_one_isNormal) :
    IsSepEnum (mirrorEnum k) ∧ cpReal k ∈ Set.Ico (0 : ℝ) 1 ∧
      (∀ n, ((scaled (mirrorEnum k) (cpReal k) n : ℤ) : ℝ)
        = (k : ℝ) ^ n * bestBelow (mirrorEnum k) (cpReal k) n) ∧
      KAdicEquidist k (scaled (mirrorEnum k) (cpReal k)) ∧
      fDim (mirrorEnum k) (cpReal k) < 1 := by
  have hp : ProperDigits k fun i => (cpSeq k i : ℕ) := properDigits_of_isNormalSequence hk2 hn
  have hs : ∀ i, (cpSeq k i : ℕ) < k := fun i => (cpSeq k i).isLt
  have hx : cpReal k ∈ Set.Ico (0 : ℝ) 1 := realOfDigits_mem_Ico k hk2 _ hs hp
  have hlen : ∀ w : List (Fin k), (decRun [] w).length = w.length :=
    fun w => length_decRun [] w
  have hfloor := bestBelow_grid_of_levelSurj hk2 (decRun (k := k) []) hlen decRun_levelSurj (cpReal k) hx
  have hsc : ∀ n, scaled (mirrorEnum k) (cpReal k) n = ⌊(k : ℝ) ^ n * cpReal k⌋ := fun n => by
    show ⌊(k : ℝ) ^ n * bestBelow (fun w => grid k (decRun [] w)) (cpReal k) n⌋ = _
    rw [hfloor n, Int.floor_intCast]
  refine ⟨isSepEnum_grid_of_levelSurj hk2 _ hlen decRun_levelSurj, hx, fun n => ?_, ?_, ?_⟩
  · rw [hsc n]; exact (hfloor n).symm
  · have he : scaled (mirrorEnum k) (cpReal k) = fun n => ⌊(k : ℝ) ^ n * cpReal k⌋ := funext hsc
    rw [he]; exact kAdicEquidist_floor_of_normal hk2 (cpSeq k) hn
  · have hg : ∀ n, decRun [] (pre (encSeq (cpSeq k)) n) = pre (cpSeq k) n := fun n => by
      rw [pre_encSeq, decRun_encRun]
    exact lt_of_le_of_lt (fDim_le_fsDim_of_decode hk2 (decRun (k := k) []) _ _ hg hp)
      (fsDim_lt_one_of_not_normal hFS hk2 _ hnn)

/-- **Believed leaf (90%): the Carton–Perifel sequence is normal in every base `k ≥ 2`.**
Carton–Perifel cite only `k ⩾ 7` (`Literature.cartonPerifel_normal`); their normality proof is a
one-line pointer to the Champernowne argument [Becher–Carton 2018, Thm 7.7.1], which does not use
the size of `k`: the block `wₙ w̃ₙ` is the lexicographic list of all length-`n` words followed by its
mirror, and both halves have the Champernowne word counts up to `O(n kⁿ)` boundary terms.  Numeric
probe `probes/finite_state_cp_normality_probe.py` (k = 2, 3, 5 against a normal and a non-normal
control) agrees.  Needed only for `k ∈ {2, …, 6}`. -/
theorem isNormal_cpSeq [NeZero k] (hk : 2 ≤ k) : IsNormalSequence k fun i => (cpSeq k i : ℕ) := by
  sorry

/-- **HEADLINE (answer to Pulari's Q-DPDT, conditional on two cited inputs; confidence 85%).**

Problem (Pulari, arXiv:2602.01199v2, §5 "Discussion and open questions"): "One concrete setting is
when the naming map is computable by a deterministic pushdown transducer.  In particular, does there
exist such a separator enumerator `f` and a point `x ∈ [0,1)` for which the integer sequence
`(k^n a_n^f(x))_{n≥1}` is `k`-adically equidistributed while `dim^f_FS(x) < 1`?"

Answer: **yes**, for every base `k ≥ 7` on the cited inputs alone (bases `3 ≤ k ≤ 6`:
`pulariDPDTQuestion_three`, via the believed leaf `isNormal_cpSeq`), and with a real-time (letter-to-letter) DPDT.  `f` is the
mirror enumerator `grid ∘ decRun`, `x` is the Carton–Perifel normal number `0.w₁w̃₁w₂w̃₂⋯`.

English proof.  The decoder applies, at each step, a permutation of the input letter depending on
the stack, so it is a bijection on every `Σ^n`; hence `f` hits every grid point of every level,
is a separator enumerator, and `k^n a_n^f(x) = ⌊k^n x⌋`, which is `k`-adically equidistributed
because `x` is normal.  The names of `x↾n` are `encRun(x↾n)`, the free-reduction coder's output,
which emits `0` at every cancellation; each block `w w̃` cancels at least `|w|/2` letters, so `0`
has frequency `≥ 1/4 > 1/k` along the block ends, the name sequence is not normal, its
finite-state dimension is `< 1`, and the decoder transfers that bound to `dim^f(x)`.

Cited inputs: `Literature.cartonPerifel_normal`, `Literature.fsDim_one_isNormal`.
Leaves: the (proved) leaf theorems above.  `k ∈ {2,3,4}` is in
`FiniteStateSelectionStretch` (the `1/4` bound does not separate there). -/
theorem pulariDPDTQuestion_of_lit [NeZero k] (hk : 7 ≤ k)
    (hCP : Literature.cartonPerifel_normal) (hFS : Literature.fsDim_one_isNormal) :
    PulariDPDTQuestion k := by
  obtain ⟨hse, hx, hint, hkad, hdim⟩ :=
    mirrorEnum_cpReal_facts_of_not_normal (by omega) (not_isNormal_encSeq_cpSeq (by omega))
      (hCP k hk) hFS
  exact ⟨mirrorEnum k, hse, isDPDTEnum_mirror, cpReal k, hx, hint, hkad, hdim⟩

/-- **Q-DPDT for every base `k ≥ 3`** (conditional on `fsDim_one_isNormal` and the believed leaf
`isNormal_cpSeq`): the mirror enumerator at the Carton–Perifel point answers Pulari's question
already from base `3`, via `not_isNormal_encSeq_cpSeq_of_three`.  Base `2` remains open
(`PulariDPDTBaseTwo`). -/
theorem pulariDPDTQuestion_three [NeZero k] (hk : 3 ≤ k)
    (hFS : Literature.fsDim_one_isNormal) :
    PulariDPDTQuestion k := by
  obtain ⟨hse, hx, hint, hkad, hdim⟩ :=
    mirrorEnum_cpReal_facts_of_not_normal (by omega) (not_isNormal_encSeq_cpSeq_of_three hk)
      (isNormal_cpSeq (by omega)) hFS
  exact ⟨mirrorEnum k, hse, isDPDTEnum_mirror, cpReal k, hx, hint, hkad, hdim⟩

/-- **HEADLINE (answer to Pulari's Q-weak for synchronous relabelings, conditional on Pulari's
Theorem 3; confidence 93%).**

Problem (Pulari, arXiv:2602.01199v2, §5): "It would be interesting to determine whether some
weaker condition (e.g. levelwise surjectivity or bounded-to-one behavior on each `Σ^n`) suffices
for the same equidistribution characterization, or whether non-invertible finite-state relabelings
can already break it."

Answer for synchronous (letter-to-letter) relabelings: they cannot break it.  A synchronous Mealy
relabeling with dense image is levelwise surjective (`mealy_levelSurj_of_isSepEnum`), levelwise
surjectivity of a synchronous machine is equivalent to invertibility on reachable states
(`exists_invertible_of_levelSurj`), so every such separator enumerator coincides with a finite-state
coherent one and Pulari's Theorem 3 applies.  In particular the "weaker conditions" are not weaker,
and a bounded-to-one non-injective synchronous relabeling is never a separator enumerator.  The
non-synchronous case is where the scaling `k^n` stops matching the output resolution (stretch file). -/
theorem pulariWeakening_of_lit (hk : 2 ≤ k) (hP : Literature.pulari_coherent_eqchar) :
    PulariWeakening k := by
  intro M hM x hx
  obtain ⟨M', hinv, hrun⟩ :=
    exists_invertible_of_levelSurj M (mealy_levelSurj_of_isSepEnum hk M hM)
  have he : mealyEnum M' = mealyEnum M := funext fun w => by simp only [mealyEnum, hrun]
  rw [← he]
  exact hP k hk M' hinv x hx

/-- **Guard: the stack is load-bearing.**  No synchronous Mealy machine computes the mirror
decoder: otherwise the mirror enumerator would be a synchronous finite-state relabeling that is a
separator enumerator, `pulariWeakening_of_lit` would make `cpReal k` mirror-normal (its scaled
sequence is `k`-adically equidistributed), contradicting `dim < 1`.  This is the known-true control
for the mechanism: on the finite-state class the same construction must fail, and it does. -/
theorem mirror_not_mealy [NeZero k] (hk : 7 ≤ k) (hCP : Literature.cartonPerifel_normal)
    (hFS : Literature.fsDim_one_isNormal) (hP : Literature.pulari_coherent_eqchar) :
    ¬ ∃ M : Mealy k, ∀ w, M.run w = decRun [] w := by
  rintro ⟨M, hM⟩
  obtain ⟨hse, hx, -, hkad, hdim⟩ :=
    mirrorEnum_cpReal_facts_of_not_normal (by omega) (not_isNormal_encSeq_cpSeq (by omega))
      (hCP k hk) hFS
  have he : mealyEnum M = mirrorEnum k := funext fun w => by simp only [mealyEnum, mirrorEnum, hM]
  have hW := pulariWeakening_of_lit (by omega) hP M (he ▸ hse) (cpReal k) hx
  rw [he] at hW
  have h1 : fDim (mirrorEnum k) (cpReal k) = 1 := hW.mpr hkad
  exact absurd hdim (by rw [h1]; exact lt_irrefl 1)

end NormalNumbers.FiniteState
