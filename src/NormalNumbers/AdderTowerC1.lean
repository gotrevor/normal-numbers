/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderBaseG

/-!
# Tower claim C1: the ternary digit theorem for {1, 2} (KNOWN RESULT, cited)

Brief: `BRIEF-adder-tower.md` phase C item 1; dossier
`EVIDENCE-2026-08-29-tower-formalization.md` §C1.

⚠️ **Known result — lane 2, cited, never headlined as new.**  This is
**Berend–Boshernitzan 1994's own `M(3,1) = 2`** (reclassified 2026-08-29,
master `c645528`): for every irrational `x` and EVERY digit `d ∈ {0,1,2}`,
`d` occurs infinitely often in the base-3 expansion of `x` or of `2x`.  We
formalize it as an independent machine verification of their statement via
the single-track base-3 engine; per the brief the hand-proof lemma for
`d = 1` is SKIPPED (it presumably re-derives theirs).

The family per digit `d` is two channels `x` and `2x`, each avoiding the
single-digit word `[d]`.  State space: the `x`-channel is stateless (no
carry, trivial window) and the `2x`-channel carries `T ∈ {0,1}` — two family
states, alphabet 3.  The three certificates (`c1Cert0/1/2`) are checked by
`decide` (kernel tier); each survives on forced self-loops or a forced
2-cycle-free descent, exactly the dossier's collapse verdict specialized to
our encoding (live-state COUNT differs from the dossier's 6 — expected,
encodings differ; the collapse VERDICT agrees).
-/

namespace NormalNumbers.Adder

open NormalNumbers

/-- The C1 family for digit `d`: channels `x` and `2x`, both avoiding the
single ternary digit `d`. -/
def c1Chans (d : ℕ) : List ZChannel := [⟨1, 0, [d]⟩, ⟨2, 0, [d]⟩]

/-- All family states are live in every C1 certificate. -/
def c1live : ℕ → Bool := fun _ => true

/-- d = 0: rank increases with the `2x`-carry. -/
def c1rho0 : ℕ → ℕ := fun s => s

def c1forced0 : ℕ → Option (ℕ × ℕ) := fun s =>
  if s = 0 then some (1, 0) else if s = 1 then some (2, 1) else none

/-- d = 1: two forced self-loops, flat rank. -/
def c1rho1 : ℕ → ℕ := fun _ => 0

def c1forced1 : ℕ → Option (ℕ × ℕ) := fun s =>
  if s = 0 then some (0, 0) else if s = 1 then some (2, 1) else none

/-- d = 2: rank decreases with the `2x`-carry. -/
def c1rho2 : ℕ → ℕ := fun s => 1 - s

def c1forced2 : ℕ → Option (ℕ × ℕ) := fun s =>
  if s = 0 then some (0, 0) else if s = 1 then some (1, 1) else none

theorem c1_cert0 : checkCertA (fun σ s' => gfamPred 3 (c1Chans 0) (σ % 3) (σ / 3) s')
    3 2 c1live c1rho0 (fun _ => 0) c1forced0 = true := by decide

theorem c1_cert1 : checkCertA (fun σ s' => gfamPred 3 (c1Chans 1) (σ % 3) (σ / 3) s')
    3 2 c1live c1rho1 (fun _ => 0) c1forced1 = true := by decide

theorem c1_cert2 : checkCertA (fun σ s' => gfamPred 3 (c1Chans 2) (σ % 3) (σ / 3) s')
    3 2 c1live c1rho2 (fun _ => 0) c1forced2 = true := by decide

/-- **C1 (Berend–Boshernitzan 1994, `M(3,1) = 2` — cited, not new)**: for
every irrational `x` and every ternary digit `d`, `d` occurs infinitely
often in the base-3 expansion of `x` or of `2x`. -/
theorem c1_ternary_digit (X : ℝ) (hX : Irrational X) (d : ℕ) (hd : d < 3) :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 X [d] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (2 * X) [d] n) := by
  have key : ∃ ch ∈ c1Chans d, ∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (ch.a * X) ch.word n := by
    interval_cases d
    · exact signed_engine_g_single 3 (by norm_num) (c1Chans 0) rfl c1_cert0 X hX
        (by decide) (by decide) (by decide)
    · exact signed_engine_g_single 3 (by norm_num) (c1Chans 1) rfl c1_cert1 X hX
        (by decide) (by decide) (by decide)
    · exact signed_engine_g_single 3 (by norm_num) (c1Chans 2) rfl c1_cert2 X hX
        (by decide) (by decide) (by decide)
  obtain ⟨ch, hch, hio⟩ := key
  fin_cases hch
  · left
    intro N
    obtain ⟨n, hn, hocc⟩ := hio N
    refine ⟨n, hn, ?_⟩
    rw [show (((1:ℤ):ℝ)) * X = X from by push_cast; ring] at hocc
    exact hocc
  · right
    intro N
    obtain ⟨n, hn, hocc⟩ := hio N
    refine ⟨n, hn, ?_⟩
    rw [show (((2:ℤ):ℝ)) * X = 2 * X from by push_cast; ring] at hocc
    exact hocc

end NormalNumbers.Adder
