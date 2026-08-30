/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderBaseG

/-!
# Tower claim C2: the ternary all-digits product block {2, 11}

Brief: `BRIEF-adder-tower.md` phase C item 2; dossier
`EVIDENCE-2026-08-29-tower-formalization.md` §C2.  **Novelty under check**
(the subsumption sweep is operator-owned): the statement SHAPE — a product
block "some single multiplier's image contains ALL THREE digits i.o." — is
different from the per-digit Berend–Boshernitzan clauses; treat as
candidate-new pending the check, never headline before it clears.

**Statement**: for every irrational `x`, the base-3 expansion of `2x`
contains all three ternary digits infinitely often, or that of `11x` does.

**Proof shape** (exactly the dossier's): NINE certificates — for every
assignment `(d₁, d₂) ∈ {0,1,2}²` the two-channel family "`2x` avoids `d₁`,
`11x` avoids `d₂`" collapses (`c2_clause`) — plus the purely logical
*transversal lemma*: if every clause "`d₁` i.o. in `2x` ∨ `d₂` i.o. in
`11x`" holds, then "all `d` i.o. in `2x` ∨ all `d` i.o. in `11x`"
(contrapositive: were both sides false, some `d₁` fails in `2x` and some
`d₂` fails in `11x`, refuting clause `(d₁, d₂)`; finitely many digits, no
compactness).

Family per `(d₁, d₂)`: `2x` carries `T ∈ [0,1]`, `11x` carries `T ∈ [0,10]`
— 22 family states, alphabet 3.  Certificates emitted and re-verified by
`experiments/adder_baseg_emit.py c2` (the other instrument; live counts
5–10, verdict COLLAPSE on all nine, agreeing with the dossier's
`mahler_minimal_sets.py` run), then checked here independently by kernel
`decide` against our own `gfamPred`.
-/

namespace NormalNumbers.Adder

open NormalNumbers

/-- The C2 family for the avoided-digit assignment `(d₁, d₂)`: channel `2x`
avoiding `d₁` and channel `11x` avoiding `d₂`. -/
def c2Chans (d₁ d₂ : ℕ) : List ZChannel := [⟨2, 0, [d₁]⟩, ⟨11, 0, [d₂]⟩]

/-! ### The nine certificates (data from `adder_baseg_emit.py c2`) -/

def c2mk (live : List ℕ) (rho omega : List (ℕ × ℕ)) (forced : List (ℕ × ℕ × ℕ)) :
    (ℕ → Bool) × (ℕ → ℕ) × (ℕ → ℕ) × (ℕ → Option (ℕ × ℕ)) :=
  (fun s => live.contains s,
   fun s => (rho.lookup s).getD 0,
   fun s => (omega.lookup s).getD 0,
   fun s => forced.lookup s)

def c2c00 := c2mk [4, 6, 8, 10, 17, 21] [(4, 2), (6, 1), (8, 2), (17, 2)]
  [(0, 1), (2, 1), (12, 1), (15, 2), (19, 3)]
  [(4, 0, 17), (8, 1, 4), (10, 1, 10), (17, 2, 8), (21, 2, 21)]
def c2c01 := c2mk [4, 6, 8, 10, 17, 19, 21] [(4, 1), (17, 1), (21, 2)]
  [(0, 1), (2, 1), (12, 2), (14, 1), (15, 2)]
  [(4, 0, 17), (6, 0, 19), (8, 1, 6), (10, 1, 8), (17, 2, 4), (19, 2, 10), (21, 2, 21)]
def c2c02 := c2mk [6, 10, 17, 19, 21] [(6, 2), (17, 2), (19, 1), (21, 2)]
  [(0, 1), (2, 1), (4, 3), (8, 4), (12, 2), (14, 1), (15, 2)]
  [(6, 0, 21), (10, 1, 10), (17, 2, 6), (21, 2, 17)]
def c2c10 := c2mk [0, 2, 6, 8, 10, 11, 13, 19, 21]
  [(0, 1), (2, 1), (6, 1), (8, 1), (11, 1), (21, 1)]
  [(4, 1), (7, 1), (9, 2), (12, 1), (15, 1), (17, 3)]
  [(0, 0, 2), (2, 0, 8), (6, 1, 0), (8, 1, 6), (10, 1, 10), (11, 1, 11),
   (13, 1, 19), (19, 2, 13), (21, 2, 21)]
def c2c11 := c2mk [0, 2, 6, 8, 10, 11, 13, 15, 19, 21]
  [(2, 2), (6, 1), (8, 2), (10, 2), (11, 2), (13, 2), (15, 1), (19, 2)]
  [(4, 3), (7, 1), (9, 2), (12, 2), (14, 1), (17, 3)]
  [(0, 0, 0), (2, 0, 10), (8, 1, 2), (10, 1, 8), (11, 1, 13), (13, 1, 19),
   (19, 2, 11), (21, 2, 21)]
def c2c12 := c2mk [0, 2, 8, 10, 11, 13, 15, 19, 21]
  [(0, 1), (10, 1), (13, 1), (15, 1), (19, 1), (21, 1)]
  [(4, 3), (6, 1), (9, 1), (12, 2), (14, 1), (17, 1)]
  [(0, 0, 0), (2, 0, 8), (8, 1, 2), (10, 1, 10), (11, 1, 11), (13, 1, 15),
   (15, 1, 21), (19, 2, 13), (21, 2, 19)]
def c2c20 := c2mk [0, 2, 4, 11, 15] [(0, 2), (2, 1), (4, 2), (15, 2)]
  [(6, 2), (7, 1), (9, 2), (13, 4), (17, 3), (19, 1), (21, 1)]
  [(0, 0, 4), (4, 0, 15), (11, 1, 11), (15, 2, 0)]
def c2c21 := c2mk [0, 2, 4, 11, 13, 15, 17] [(0, 2), (4, 1), (17, 1)]
  [(6, 2), (7, 1), (9, 2), (19, 1), (21, 1)]
  [(0, 0, 0), (2, 0, 11), (4, 0, 17), (11, 1, 13), (13, 1, 15), (15, 2, 2),
   (17, 2, 4)]
def c2c22 := c2mk [0, 4, 11, 13, 15, 17] [(4, 2), (13, 2), (15, 1), (17, 2)]
  [(2, 3), (6, 2), (9, 1), (19, 1), (21, 1)]
  [(0, 0, 0), (4, 0, 13), (11, 1, 11), (13, 1, 17), (17, 2, 4)]

theorem c2_cert00 : checkCertA (fun σ s' => gfamPred 3 (c2Chans 0 0) (σ % 3) (σ / 3) s')
    3 22 c2c00.1 c2c00.2.1 c2c00.2.2.1 c2c00.2.2.2 = true := by decide
theorem c2_cert01 : checkCertA (fun σ s' => gfamPred 3 (c2Chans 0 1) (σ % 3) (σ / 3) s')
    3 22 c2c01.1 c2c01.2.1 c2c01.2.2.1 c2c01.2.2.2 = true := by decide
theorem c2_cert02 : checkCertA (fun σ s' => gfamPred 3 (c2Chans 0 2) (σ % 3) (σ / 3) s')
    3 22 c2c02.1 c2c02.2.1 c2c02.2.2.1 c2c02.2.2.2 = true := by decide
theorem c2_cert10 : checkCertA (fun σ s' => gfamPred 3 (c2Chans 1 0) (σ % 3) (σ / 3) s')
    3 22 c2c10.1 c2c10.2.1 c2c10.2.2.1 c2c10.2.2.2 = true := by decide
theorem c2_cert11 : checkCertA (fun σ s' => gfamPred 3 (c2Chans 1 1) (σ % 3) (σ / 3) s')
    3 22 c2c11.1 c2c11.2.1 c2c11.2.2.1 c2c11.2.2.2 = true := by decide
theorem c2_cert12 : checkCertA (fun σ s' => gfamPred 3 (c2Chans 1 2) (σ % 3) (σ / 3) s')
    3 22 c2c12.1 c2c12.2.1 c2c12.2.2.1 c2c12.2.2.2 = true := by decide
theorem c2_cert20 : checkCertA (fun σ s' => gfamPred 3 (c2Chans 2 0) (σ % 3) (σ / 3) s')
    3 22 c2c20.1 c2c20.2.1 c2c20.2.2.1 c2c20.2.2.2 = true := by decide
theorem c2_cert21 : checkCertA (fun σ s' => gfamPred 3 (c2Chans 2 1) (σ % 3) (σ / 3) s')
    3 22 c2c21.1 c2c21.2.1 c2c21.2.2.1 c2c21.2.2.2 = true := by decide
theorem c2_cert22 : checkCertA (fun σ s' => gfamPred 3 (c2Chans 2 2) (σ % 3) (σ / 3) s')
    3 22 c2c22.1 c2c22.2.1 c2c22.2.2.1 c2c22.2.2.2 = true := by decide

/-- Clause extraction: a passing `(d₁, d₂)` certificate yields
"`d₁` i.o. in `2x` ∨ `d₂` i.o. in `11x`". -/
theorem c2_of_cert {d₁ d₂ : ℕ} {live : ℕ → Bool} {rho omega : ℕ → ℕ}
    {forced : ℕ → Option (ℕ × ℕ)}
    (hcert : checkCertA (fun σ s' => gfamPred 3 (c2Chans d₁ d₂) (σ % 3) (σ / 3) s')
      3 22 live rho omega forced = true)
    (hw1 : d₁ < 3) (hw2 : d₂ < 3) (X : ℝ) (hX : Irrational X) :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (2 * X) [d₁] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (11 * X) [d₂] n) := by
  have key := signed_engine_g_single 3 (by norm_num) (c2Chans d₁ d₂) rfl hcert X hX
    (by intro ch hch; fin_cases hch <;> norm_num [ZChannel.posSum])
    (by intro ch hch; fin_cases hch <;> norm_num [ZChannel.ell])
    (by intro ch hch; fin_cases hch <;> simpa using by omega)
  obtain ⟨ch, hch, hio⟩ := key
  fin_cases hch
  · left
    intro N
    obtain ⟨n, hn, hocc⟩ := hio N
    refine ⟨n, hn, ?_⟩
    rw [show (((2:ℤ):ℝ)) * X = 2 * X from by push_cast; ring] at hocc
    exact hocc
  · right
    intro N
    obtain ⟨n, hn, hocc⟩ := hio N
    refine ⟨n, hn, ?_⟩
    rw [show (((11:ℤ):ℝ)) * X = 11 * X from by push_cast; ring] at hocc
    exact hocc

/-- All nine clauses. -/
theorem c2_clause (X : ℝ) (hX : Irrational X) (d₁ d₂ : ℕ) (h₁ : d₁ < 3) (h₂ : d₂ < 3) :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (2 * X) [d₁] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (11 * X) [d₂] n) := by
  interval_cases d₁ <;> interval_cases d₂
  · exact c2_of_cert c2_cert00 (by norm_num) (by norm_num) X hX
  · exact c2_of_cert c2_cert01 (by norm_num) (by norm_num) X hX
  · exact c2_of_cert c2_cert02 (by norm_num) (by norm_num) X hX
  · exact c2_of_cert c2_cert10 (by norm_num) (by norm_num) X hX
  · exact c2_of_cert c2_cert11 (by norm_num) (by norm_num) X hX
  · exact c2_of_cert c2_cert12 (by norm_num) (by norm_num) X hX
  · exact c2_of_cert c2_cert20 (by norm_num) (by norm_num) X hX
  · exact c2_of_cert c2_cert21 (by norm_num) (by norm_num) X hX
  · exact c2_of_cert c2_cert22 (by norm_num) (by norm_num) X hX

/-- **C2 (ternary all-digits product block {2, 11}; novelty under check)**:
for every irrational `x`, the base-3 expansion of `2x` contains all three
ternary digits infinitely often, or that of `11x` does.  Transversal lemma
over the nine clause certificates. -/
theorem c2_product_block (X : ℝ) (hX : Irrational X) :
    (∀ d, d < 3 → ∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (2 * X) [d] n) ∨
    (∀ d, d < 3 → ∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (11 * X) [d] n) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨d₁, hd₁, N₁, hN₁⟩, ⟨d₂, hd₂, N₂, hN₂⟩⟩ := hcon
  rcases c2_clause X hX d₁ d₂ hd₁ hd₂ with h | h
  · obtain ⟨n, hn, hocc⟩ := h N₁
    exact hN₁ n hn hocc
  · obtain ⟨n, hn, hocc⟩ := h N₂
    exact hN₂ n hn hocc

end NormalNumbers.Adder
