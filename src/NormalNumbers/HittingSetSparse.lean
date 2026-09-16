/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderEngineCoreG

/-!
# Sorted-array lookup tables for large hitting-set certificates 🧵

`HittingSetBounds.lean` / `HittingSetBase7.lean` carry their `live` / `rho` /
`omega` / `forced` tables as sparse `List.lookup` association lists.  That is fine
at ambient `9360` (base 7, one digit), but the ambient state space of a
`gfamPred` family is the **product** `∏ᵢ mᵢ · g^(ℓ−1)` over its channels, so the
`(3,2)` family `{1,2,4,5,7,8}` already sits at `1632960` states with `6685`
states carrying a nonzero `omega`.  A linear association-list lookup inside a
sweep of that size is `10^10` comparisons — dead on arrival.

This file gives the same four tables as **sorted `Array ℕ` key/value pairs with
binary search**, so a lookup is `O(log n)` and the sweep is linear in the ambient
size with a small constant.  Nothing here is proved: these are plain definitions
feeding `decide` / `native_decide`, and the certificate theorems state exactly
the same `checkCertA` proposition as the association-list files.
-/

namespace NormalNumbers.Adder

/-- Binary search for `x` in the sorted array `keys`, with explicit fuel
(`64` doublings is past `2^64` keys, so it never runs out in practice). -/
def bfindAux (keys : Array ℕ) (x : ℕ) : ℕ → ℕ → ℕ → Option ℕ
  | 0, _, _ => none
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      let k := keys.getD mid 0
      if x < k then bfindAux keys x fuel lo mid
      else if k < x then bfindAux keys x fuel (mid + 1) hi
      else some mid
    else none

/-- Index of `x` in the sorted array `keys`, if present. -/
def bfind (keys : Array ℕ) (x : ℕ) : Option ℕ := bfindAux keys x 64 0 keys.size

/-- Membership in a sorted key array. -/
def tmem (keys : Array ℕ) (x : ℕ) : Bool := (bfind keys x).isSome

/-- Sparse table lookup: `vals[i]` at the key index, `0` off the key set. -/
def tget (keys vals : Array ℕ) (x : ℕ) : ℕ :=
  match bfind keys x with
  | none => 0
  | some i => vals.getD i 0

/-- Sparse `forced` table: `(sigs[i], dsts[i])` at the key index. -/
def tforced (keys sigs dsts : Array ℕ) (x : ℕ) : Option (ℕ × ℕ) :=
  match bfind keys x with
  | none => none
  | some i => some (sigs.getD i 0, dsts.getD i 0)

end NormalNumbers.Adder
