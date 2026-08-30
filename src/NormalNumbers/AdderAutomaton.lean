/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# The adder family automaton (module 2 of the six-fold disjunction)

Brief: `BRIEF-adder-disjunction-formalization.md`; discovery:
`docs/adder-collapse-hunt-2026-08-29.md`; certificate emitter (the Python
mirror of every convention here): `experiments/adder_certificate_emit.py`.

A **channel** is a linear form `z = a·X + b·Y` together with a binary word to
be avoided in the digit stream of `z`.  The **state** of a channel at digit
position `m` holds the carry `T(m) ∈ [0, a+b-1]` of the column addition and
the window of the `ℓ-1` deeper `z`-digits.  The family state is the
mixed-radix packing of the channel states (channel 0 least significant).

`HStep s σ s'` means "`s'` is a legal one-step-deeper state after `s` under
input `σ = x + 2y`".  It is *backward-deterministic*: `s` is computed from
`(σ, s')` by `famPred`, so `HStep s σ s' ↔ famPred … s' = some s`, and the
step is **illegal** exactly when the freshly formed `ℓ`-digit window of some
channel equals that channel's word — i.e. legality encodes "no channel word
occurs at position `m`".

Everything here is `Nat`-valued and computable; the connection to the reals
(true carries, true digits) lives in `AdderCarry.lean` / `AdderShadow.lean`.
-/

namespace NormalNumbers.Adder

/-- A channel of the adder family: the linear form `a·X + b·Y` and the
avoided binary word (`word[0]` shallowest; `word[j]` sits at digit position
`n + j` in an occurrence at position `n`). -/
structure Channel where
  a : ℕ
  b : ℕ
  word : List ℕ
  deriving Repr, DecidableEq

namespace Channel

/-- Word length `ℓ`. -/
def ell (ch : Channel) : ℕ := ch.word.length

/-- Number of carry values: the true carry lies in `[0, a+b-1]` (and `0`
when `a+b = 0`, though no such channel is used). -/
def carrySize (ch : Channel) : ℕ := max (ch.a + ch.b) 1

/-- Number of window values: `2^(ℓ-1)` — the `ℓ-1` deeper digits. -/
def winSize (ch : Channel) : ℕ := 2 ^ (ch.ell - 1)

/-- Channel state count. -/
def size (ch : Channel) : ℕ := ch.carrySize * ch.winSize

/-- The word as a `Nat`, bit `j` = `word[j]` (LSB-first). -/
def wordVal (ch : Channel) : ℕ := ch.word.foldr (fun d acc => d + 2 * acc) 0

/-- Channel-level predecessor: given input bits `(x, y)` and the deeper
channel state `code'`, the unique shallower state — or `none` when the
freshly formed `ℓ`-digit window equals the avoided word. -/
def pred (ch : Channel) (x y : ℕ) (code' : ℕ) : Option ℕ :=
  if (ch.a * x + ch.b * y + code' / ch.winSize) % 2 + 2 * (code' % ch.winSize)
      = ch.wordVal then none
  else some ((ch.a * x + ch.b * y + code' / ch.winSize) / 2 * ch.winSize +
    ((ch.a * x + ch.b * y + code' / ch.winSize) % 2 + 2 * (code' % ch.winSize))
      % ch.winSize)

theorem winSize_pos (ch : Channel) : 0 < ch.winSize := Nat.two_pow_pos _

theorem carrySize_pos (ch : Channel) : 0 < ch.carrySize :=
  lt_of_lt_of_le Nat.one_pos (le_max_right _ _)

theorem size_pos (ch : Channel) : 0 < ch.size :=
  Nat.mul_pos ch.carrySize_pos ch.winSize_pos

theorem pred_lt (ch : Channel) (x y code' : ℕ) (hx : x ≤ 1) (hy : y ≤ 1)
    (hcode : code' < ch.size) {c : ℕ}
    (h : ch.pred x y code' = some c) : c < ch.size := by
  unfold pred at h
  have hw : (0:ℕ) < ch.winSize := ch.winSize_pos
  have hc'lt : code' / ch.winSize < ch.carrySize :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hcode)
  split at h
  · exact absurd h (by simp)
  · have hv : ch.a * x + ch.b * y ≤ ch.a + ch.b := by
      have h1 : ch.a * x ≤ ch.a * 1 := Nat.mul_le_mul_left _ hx
      have h2 : ch.b * y ≤ ch.b * 1 := Nat.mul_le_mul_left _ hy
      omega
    have hcarry : (ch.a * x + ch.b * y + code' / ch.winSize) / 2 < ch.carrySize := by
      have h2 : ch.a + ch.b ≤ ch.carrySize := le_max_left _ _
      omega
    simp only [Option.some.injEq] at h
    subst h
    calc (ch.a * x + ch.b * y + code' / ch.winSize) / 2 * ch.winSize
          + ((ch.a * x + ch.b * y + code' / ch.winSize) % 2
              + 2 * (code' % ch.winSize)) % ch.winSize
        < (ch.a * x + ch.b * y + code' / ch.winSize) / 2 * ch.winSize
            + ch.winSize := Nat.add_lt_add_left (Nat.mod_lt _ hw) _
      _ = ((ch.a * x + ch.b * y + code' / ch.winSize) / 2 + 1) * ch.winSize := by
            ring
      _ ≤ ch.carrySize * ch.winSize := Nat.mul_le_mul_right _ (by omega)

end Channel

/-- The family state count (mixed radix, channel 0 least significant). -/
def famSize : List Channel → ℕ
  | [] => 1
  | ch :: rest => ch.size * famSize rest

/-- Family-level predecessor: componentwise `Channel.pred`; `none` when any
channel's word occurred. -/
def famPred (chs : List Channel) (x y : ℕ) (s' : ℕ) : Option ℕ :=
  match chs with
  | [] => some 0
  | ch :: rest =>
    match ch.pred x y (s' % ch.size), famPred rest x y (s' / ch.size) with
    | some c, some r => some (c + ch.size * r)
    | _, _ => none

theorem famPred_lt (chs : List Channel) (x y : ℕ) (hx : x ≤ 1) (hy : y ≤ 1)
    (s' : ℕ) {s : ℕ}
    (h : famPred chs x y s' = some s) : s < famSize chs := by
  induction chs generalizing s' s with
  | nil =>
    simp only [famPred, Option.some.injEq] at h
    simp [famSize, ← h]
  | cons ch rest ih =>
    simp only [famPred] at h
    have hchsz : 0 < ch.size := ch.size_pos
    rcases hp : ch.pred x y (s' % ch.size) with _ | c <;> rw [hp] at h
    · exact absurd h (by simp)
    rcases hr : famPred rest x y (s' / ch.size) with _ | r <;> rw [hr] at h
    · exact absurd h (by simp)
    simp only [Option.some.injEq] at h
    subst h
    have hc : c < ch.size :=
      ch.pred_lt x y _ hx hy (Nat.mod_lt _ hchsz) hp
    have hrlt : r < famSize rest := ih _ hr
    calc c + ch.size * r < ch.size + ch.size * r := by omega
      _ = ch.size * (r + 1) := by ring
      _ ≤ ch.size * famSize rest := Nat.mul_le_mul_left _ (by omega)
      _ = famSize (ch :: rest) := rfl

/-- `HStep chs s σ s'`: under input `σ = x + 2y ∈ [0,4)`, the deeper state
`s'` legally follows the shallower state `s`, and no channel word occurs at
the position being stepped over. -/
def HStep (chs : List Channel) (s σ s' : ℕ) : Prop :=
  famPred chs (σ % 2) (σ / 2) s' = some s

instance (chs : List Channel) (s σ s' : ℕ) : Decidable (HStep chs s σ s') := by
  unfold HStep; infer_instance

/-! ## The two families -/

/-- The six frozen channels of the main theorem (constants
`ln 2, ln 3, ln 6, ln 18, ln 12, ln 54`; word-to-constant pairing frozen by
the exact collapse computation of 2026-08-29). -/
def mainFamily : List Channel :=
  [⟨1, 0, [0, 0]⟩, ⟨0, 1, [0, 0, 1]⟩, ⟨1, 1, [1, 1]⟩,
   ⟨1, 2, [0, 0, 1]⟩, ⟨2, 1, [0, 1, 0]⟩, ⟨1, 3, [0, 0, 0]⟩]

/-- The vacuous 3-channel dry-run family (`ln 2, ln 3, ln 6` avoiding
`01, 01, 10`) — proves a known-true statement through the same pipeline. -/
def toyFamily : List Channel :=
  [⟨1, 0, [0, 1]⟩, ⟨0, 1, [0, 1]⟩, ⟨1, 1, [1, 0]⟩]

example : famSize mainFamily = 73728 := by decide
example : famSize toyFamily = 16 := by decide

end NormalNumbers.Adder
