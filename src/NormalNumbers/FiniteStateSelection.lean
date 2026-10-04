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

Both are proved here as WIRING from named leaves (`sorry` with confidence) and three cited
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
for "large enough" alphabets because of the COMPRESSION claim; the normality assertion is made for
the sequence as defined, and we transcribe it for every `k ≥ 2`.  Referee: the base range. -/
def cartonPerifel_normal : Prop :=
  ∀ (k : ℕ) [NeZero k], 2 ≤ k → IsNormalSequence k fun i => (cpSeq k i : ℕ)

/-- **Finite-state dimension one implies normal**, in decompression form: Bourke–Hitchcock–
Vinodchandran, *Entropy rates and finite-state dimension*, Theoret. Comput. Sci. 349 (2005)
(a sequence is normal iff its finite-state dimension is `1`), composed with Doty–Moser,
*Finite-state dimension and lossy decompressors*, arXiv:cs/0609096, Theorem 3.11
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

/-! ## Leaves (frozen, `sorry` with confidence) -/

/-- **Leaf (92%).**  A length-preserving naming map that is surjective on every level gives a
separator enumerator.  Proof: `grid` maps `Σ^n` onto `{j/k^n}`, which lies in `[0,1)`, and the
union over `n` is dense. -/
theorem isSepEnum_grid_of_levelSurj (hk : 2 ≤ k) (g : List (Fin k) → List (Fin k))
    (hlen : ∀ w, (g w).length = w.length)
    (hsurj : ∀ u : List (Fin k), ∃ w, w.length = u.length ∧ g w = u) :
    IsSepEnum fun w => grid k (g w) := by
  sorry

/-- **Leaf (92%).**  Pulari Lemma 6 for any levelwise-surjective length-preserving relabeling:
`k^n a_n^f(x) = ⌊k^n x⌋`.  Proof: the values at lengths `≤ n` are exactly the grid points of
denominator dividing `k^n`, and the largest one `≤ x` is `⌊k^n x⌋/k^n`. -/
theorem bestBelow_grid_of_levelSurj (hk : 2 ≤ k) (g : List (Fin k) → List (Fin k))
    (hlen : ∀ w, (g w).length = w.length)
    (hsurj : ∀ u : List (Fin k), ∃ w, w.length = u.length ∧ g w = u)
    (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) (n : ℕ) :
    (k : ℝ) ^ n * bestBelow (fun w => grid k (g w)) x n = ⌊(k : ℝ) ^ n * x⌋ := by
  sorry

/-- **Leaf (92%).**  Normal digits give `k`-adically equidistributed `⌊k^n x⌋` (Pulari Thm 2,
Kuipers–Niederreiter).  Proof: for `n ≥ m`, `⌊k^n x⌋ mod k^m` is the value of the digit block
`x_{n-m+1} ⋯ x_n`, so the count of `n ≤ N` with residue `r` is the occurrence count of the length-`m`
word of `r` in the first `N` digits, up to `m`. -/
theorem kAdicEquidist_floor_of_normal (hk : 2 ≤ k) (S : ℕ → Fin k)
    (hn : IsNormalSequence k fun i => (S i : ℕ)) :
    KAdicEquidist k fun n => ⌊(k : ℝ) ^ n * realOfDigits k (fun i => (S i : ℕ))⌋ := by
  sorry

/-- **Leaf (88%).**  A synchronous decoder `g` that maps the prefixes of a name sequence `N` to the
prefixes of `S` transfers compression: `dim^g(x) ≤ dim_FS(N)` at `x = 0.S`.  Proof: at `δ = k^{-n}`
the name `N↾n` has `|grid(S↾n) − x| < k^{-n}` (proper digits), so
`K^{T,f}_{k^{-n}}(x) ≤ K^T(N↾n)`; take `liminf` along `δ = k^{-n}` and `inf_T`. -/
theorem fDim_le_fsDim_of_decode (hk : 2 ≤ k) (g : List (Fin k) → List (Fin k))
    (N S : ℕ → Fin k) (hg : ∀ n, g (pre N n) = pre S n)
    (hp : ProperDigits k fun i => (S i : ℕ)) :
    fDim (fun w => grid k (g w)) (realOfDigits k fun i => (S i : ℕ)) ≤ fsDim N := by
  sorry

/-- **Leaf (95%).**  The one-state copying FST gives `K^T(S↾n) ≤ n`. -/
theorem fsDim_le_one (hk : 2 ≤ k) (S : ℕ → Fin k) : fsDim S ≤ 1 := by
  sorry

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

/-- **Leaf (95%).**  A synchronous Mealy relabeling that is a separator enumerator is surjective
on every level.  Proof: if `u ∈ Σ^n` is missed, the open interval `(grid u, grid u + k^{-n})`
contains no value — a value from a word of length `≤ n` is a multiple of `k^{-n}`, and a value from
a longer word `w` lies in it only if `M(w)↾n = M(w↾n) = u` (synchronicity). -/
theorem mealy_levelSurj_of_isSepEnum (hk : 2 ≤ k) (M : Mealy k)
    (hM : IsSepEnum (mealyEnum M)) :
    ∀ u : List (Fin k), ∃ w, w.length = u.length ∧ M.run w = u := by
  sorry

/-- **Leaf (93%).**  A levelwise-surjective synchronous Mealy machine agrees with an invertible
one.  Proof: surjectivity on `Σ^{n+1}` forces `out q` to be a permutation at every state `q`
reached by a length-`n` word (else two one-letter extensions collide and `|Σ^{n+1}|` is missed);
replace `out` by the identity at unreachable states. -/
theorem exists_invertible_of_levelSurj (M : Mealy k)
    (hM : ∀ u : List (Fin k), ∃ w, w.length = u.length ∧ M.run w = u) :
    ∃ M' : Mealy k, M'.IsInvertible ∧ ∀ w, M'.run w = M.run w := by
  sorry

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
    (hCP : Literature.cartonPerifel_normal) (hFS : Literature.fsDim_one_isNormal) :
    IsSepEnum (mirrorEnum k) ∧ cpReal k ∈ Set.Ico (0 : ℝ) 1 ∧
      (∀ n, ((scaled (mirrorEnum k) (cpReal k) n : ℤ) : ℝ)
        = (k : ℝ) ^ n * bestBelow (mirrorEnum k) (cpReal k) n) ∧
      KAdicEquidist k (scaled (mirrorEnum k) (cpReal k)) ∧
      fDim (mirrorEnum k) (cpReal k) < 1 := by
  have hn : IsNormalSequence k fun i => (cpSeq k i : ℕ) := hCP k hk2
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

/-- **HEADLINE (answer to Pulari's Q-DPDT, conditional on two cited inputs; confidence 85%).**

Problem (Pulari, arXiv:2602.01199v2, §5 "Discussion and open questions"): "One concrete setting is
when the naming map is computable by a deterministic pushdown transducer.  In particular, does there
exist such a separator enumerator `f` and a point `x ∈ [0,1)` for which the integer sequence
`(k^n a_n^f(x))_{n≥1}` is `k`-adically equidistributed while `dim^f_FS(x) < 1`?"

Answer: **yes**, for every base `k ≥ 5`, and with a real-time (letter-to-letter) DPDT.  `f` is the
mirror enumerator `grid ∘ decRun`, `x` is the Carton–Perifel normal number `0.w₁w̃₁w₂w̃₂⋯`.

English proof.  The decoder applies, at each step, a permutation of the input letter depending on
the stack, so it is a bijection on every `Σ^n`; hence `f` hits every grid point of every level,
is a separator enumerator, and `k^n a_n^f(x) = ⌊k^n x⌋`, which is `k`-adically equidistributed
because `x` is normal.  The names of `x↾n` are `encRun(x↾n)`, the free-reduction coder's output,
which emits `0` at every cancellation; each block `w w̃` cancels at least `|w|/2` letters, so `0`
has frequency `≥ 1/4 > 1/k` along the block ends, the name sequence is not normal, its
finite-state dimension is `< 1`, and the decoder transfers that bound to `dim^f(x)`.

Cited inputs: `Literature.cartonPerifel_normal`, `Literature.fsDim_one_isNormal`.
Leaves: the `sorry`s above (elementary).  `k ∈ {2,3,4}` is in
`FiniteStateSelectionStretch` (the `1/4` bound does not separate there). -/
theorem pulariDPDTQuestion_of_lit [NeZero k] (hk : 5 ≤ k)
    (hCP : Literature.cartonPerifel_normal) (hFS : Literature.fsDim_one_isNormal) :
    PulariDPDTQuestion k := by
  obtain ⟨hse, hx, hint, hkad, hdim⟩ :=
    mirrorEnum_cpReal_facts_of_not_normal (by omega) (not_isNormal_encSeq_cpSeq hk) hCP hFS
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
theorem mirror_not_mealy [NeZero k] (hk : 5 ≤ k) (hCP : Literature.cartonPerifel_normal)
    (hFS : Literature.fsDim_one_isNormal) (hP : Literature.pulari_coherent_eqchar) :
    ¬ ∃ M : Mealy k, ∀ w, M.run w = decRun [] w := by
  rintro ⟨M, hM⟩
  obtain ⟨hse, hx, -, hkad, hdim⟩ :=
    mirrorEnum_cpReal_facts_of_not_normal (by omega) (not_isNormal_encSeq_cpSeq hk) hCP hFS
  have he : mealyEnum M = mirrorEnum k := funext fun w => by simp only [mealyEnum, mirrorEnum, hM]
  have hW := pulariWeakening_of_lit (by omega) hP M (he ▸ hse) (cpReal k) hx
  rw [he] at hW
  have h1 : fDim (mirrorEnum k) (cpReal k) = 1 := hW.mpr hkad
  exact absurd hdim (by rw [h1]; exact lt_irrefl 1)

end NormalNumbers.FiniteState
