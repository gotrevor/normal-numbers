/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3Carry

/-!
# Small/large prime splitting of `ω`, and the transitivity route to `OmegaCarryJoint`

The crux `OmegaCarryJoint` (`SwingC3.lean`) asks that one residue class of the carry be
compatible, at positive lower density, with every prescribed residue vector for `ω`.  Attacking
it through equidistribution of `ω mod b` means Selberg–Delange.  There is a softer route, and
this file sets up its algebra.

Split `ω = ω_{≤P} + ω_{>P}` (`omegaSmall`, `omegaLarge`, `omegaSmall_add_omegaLarge`).  The
small part is **periodic**: `omegaSmall P m` depends only on `m` modulo the primes `≤ P`
(`omegaSmall_congr`).  So on an arithmetic progression `n ≡ a (mod Q)`, `Q = ∏_{p ≤ P} p`, the
whole vector `(ω_{≤P}(n+1), …, ω_{≤P}(n+L))` is a CONSTANT determined by `a`, and — choosing `a`
by CRT, with primes `> L` so no prime divides two window entries — that constant vector can be
made **any** vector of counts we like.

By `SwingC3Carry.omegaCarry_succ` the digit window is the base-`b` adder automaton run on
`ω = ω_{≤P} + ω_{>P}`, so moving `a` translates the digit window by an arbitrary amount while
leaving the `ω_{>P}` input alone.  Hence the digit-window law is a mixture, over `a`, of
*shifted copies of a single law*, and every word picks up positive density — **without ever
identifying that law**.  The one thing this needs is

    `OmegaLargeDecouple`: the joint law of `(ω_{>P}(n+1), …, ω_{>P}(n+L))` along
    `n ≡ a (mod Q)` is asymptotically independent of the class `a`,

which is the fundamental lemma of the sieve / Kubilius model territory, not Selberg–Delange.
That is the leaf the next lap should attack.
-/

open Finset

namespace NormalNumbers

open PrimeLambert

/-- `ω_{≤P}(m)`: the number of distinct prime factors of `m` that are `≤ P`. -/
def omegaSmall (P m : ℕ) : ℕ := (m.primeFactors.filter (fun p => p ≤ P)).card

/-- `ω_{>P}(m)`: the number of distinct prime factors of `m` that exceed `P`. -/
def omegaLarge (P m : ℕ) : ℕ := (m.primeFactors.filter (fun p => ¬ p ≤ P)).card

@[simp] theorem omegaSmall_add_omegaLarge (P m : ℕ) :
    omegaSmall P m + omegaLarge P m = ArithmeticFunction.cardDistinctFactors m := by
  rw [omegaSmall, omegaLarge, cardDistinctFactors_eq_card_primeFactors]
  exact Finset.card_filter_add_card_filter_not (fun p => p ≤ P)

/-- **Periodicity of the small part.**  If `m` and `m'` are divisible by exactly the same primes
`≤ P`, their small `ω`-counts agree. -/
theorem omegaSmall_congr {P m m' : ℕ} (hm : m ≠ 0) (hm' : m' ≠ 0)
    (h : ∀ p ≤ P, p.Prime → (p ∣ m ↔ p ∣ m')) : omegaSmall P m = omegaSmall P m' := by
  unfold omegaSmall
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hp, hpm, -⟩, hle⟩
    exact ⟨⟨hp, (h p hle hp).1 hpm, hm'⟩, hle⟩
  · rintro ⟨⟨hp, hpm, -⟩, hle⟩
    exact ⟨⟨hp, (h p hle hp).2 hpm, hm⟩, hle⟩

/-- The congruence hypothesis of `omegaSmall_congr` holds whenever `m ≡ m'` modulo a number `Q`
that every prime `≤ P` divides. -/
theorem omegaSmall_congr_of_modEq {P Q m m' : ℕ} (hm : m ≠ 0) (hm' : m' ≠ 0)
    (hQ : ∀ p ≤ P, p.Prime → p ∣ Q) (h : m ≡ m' [MOD Q]) :
    omegaSmall P m = omegaSmall P m' :=
  omegaSmall_congr hm hm' fun p hp hpp => by
    have hpQ := hQ p hp hpp
    have h' : m ≡ m' [MOD p] := Nat.ModEq.of_dvd hpQ h
    constructor
    · intro hd
      exact (Nat.modEq_zero_iff_dvd).1 (h'.symm.trans ((Nat.modEq_zero_iff_dvd).2 hd))
    · intro hd
      exact (Nat.modEq_zero_iff_dvd).1 (h'.trans ((Nat.modEq_zero_iff_dvd).2 hd))

/-- The digit window of `G_b` at `n` is driven by `ω_{≤P} + ω_{>P}`: restating
`SwingC3Carry.omegaCarry_succ` in the split form, which is where the translation by the
residue class enters. -/
theorem omegaCarry_succ_split {b : ℕ} (hb : 2 ≤ b) (P k : ℕ) :
    omegaCarry b k = (omegaSmall P (k + 1) + omegaLarge P (k + 1) + omegaCarry b (k + 1)) / b := by
  rw [omegaSmall_add_omegaLarge]; exact omegaCarry_succ hb k

end NormalNumbers
