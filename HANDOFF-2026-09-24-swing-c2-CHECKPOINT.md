# HANDOFF 2026-09-24 — swing at C2, session checkpoint (laps 1–16)

Branch `wip/swing-c2`, HEAD `ef1adb7`, working tree **clean**, `lake build` **green**.
Target file `src/NormalNumbers/SwingC2.lean` — **exactly one `sorry`**: `constructionInputs_hold`.
Full narrative lap-by-lap: `HANDOFF-2026-09-24-swing-c2-lap1.md` (read that for detail).

## The chain, all machine-checked except the last link

    ConjC2                                    (CastingOut.ConjC2, headline, kept as required)
      ⟸ tau_windowPrescribable
      ⟸ WindowPrescribable b tau              windowPrescribable_of_windowShape
      ⟸ WindowShape b                         windowShape_of_subLeafA
      ⟸ SubLeafA b                            subLeafA_of_constructionInputs
      ⟸ ConstructionInputs b                  ← THE ONLY OPEN OBLIGATION

`ConstructionInputs b`: ∀ ℓ ≥ 1, ∀ t < b^ℓ, ∃ n K —
* **(K1)** ∀ j < ℓ+K, j ≠ ℓ−1 → `b^{j+1} ∣ τ(n+1+j)`   (CRT, congruences only)
* **(K2)** `τ(n+ℓ) ≡ t (mod b^ℓ)`                        (ONE Dirichlet prime; odd `b`)
* **(K3)** `carry b τ (n+ℓ+K) < b^K`                     (almost-all divisor bound)

## Verdicts reached (two of them retractions of my own earlier claims)

1. **`τ` is outside the G4/G5 additive class, provably** — `weightN_prime` forces value `1` at a
   prime vs `τ(p)=2`; `tau_not_additive` (`τ(36)=9≠6`).  `G4Transport`'s affine identity does NOT
   port.  *(lap 1, stands)*
2. **Replacement transport** `tau_transport_frozen`: on a valuation-frozen progression `τ(D·m)` is
   a fixed rational multiple of `τ(m)` — multiplication, not translation.  *(lap 1, stands)*
3. **Escape to the additive category**: `τ(p^a·s) = (a+1)·2^{ω(s)}` on the structured locus
   (`tau_primePow_mul_squarefree`), and structured windows are ~60% of all windows and lose no
   targets (probe).  *(laps 5–7, stands)*
4. **RETRACTED (lap 13)**: lap 9–10's "explicit CRT construction is refuted" used the WORST-CASE
   bound `τ ≤ 2√m` where an ALMOST-ALL bound suffices.  With the normal order `τ ≈ (log m)^{log 2}`
   the construction is consistent.  Lap 10's "the crux is irreducibly analytic" is **withdrawn**.
5. **RETRACTED (lap 12)**: `SubLeafA`'s carry hypothesis was stronger than the padding argument
   needs; `WindowShape` is the honest requirement.
6. **No local obstruction**: `structuredTarget_unobstructed` — the residue system is algebraically
   free, so only realisability is at stake.  *(lap 8, stands)*

## Where to resume (ordered)

1. **Finish (K1).**  All pointwise pieces are proved (`succ_factorization_dvd_tau`,
   `factorization_eq_of_modEq`, `pow_dvd_tau_of_factorization`).  Assemble with
   `Nat.chineseRemainderOfFinset` (Mathlib/Data/Nat/ChineseRemainder.lean): `Finset` = slots
   `range (ℓ+K) \ {ℓ−1}`, moduli `s j = q_j^{b^{j+1}}`, `q_j` distinct primes (e.g. `j ↦ nth prime`),
   residues `q_j^{a_j} + s j·(1+j) − (1+j)`.  Coprimality: `Nat.Coprime.pow` of
   `(Nat.coprime_primes _ _).2`.  Target lemma:
   `exists_kill_window : ∃ n, ∀ j < ℓ+K, j ≠ ℓ−1 → (b:ℤ)^(j+1) ∣ (tau (n+1+j) : ℤ)`.
   NOTE: (K1) and (K2) must be solved SIMULTANEOUSLY (same `n`) — fold the (K2) condition into the
   same CRT system by reserving one extra prime `r ∉ {q_j}` and requiring `r^e ‖ n+ℓ`, then take
   the cofactor prime by Dirichlet inside the resulting progression.
2. **(K2)**: needs Dirichlet on primes in APs.  Check `G4MertensAP`, `G4Progression`, and the
   `PrimeNumberTheoremAnd` dependency BEFORE writing one.
3. **(K3)**: leave as a named hypothesis until 1–2 land; then it is the only analytic input.

## Assets

* `probes/swingc2_window.py` — known-answer checked (exact `Fraction` evaluation of `Σ1/(b^n−1)`
  in bases 3 and 10).  Reports target coverage and structured-window density.
* Kernel anchors in `src/`: `subLeafA_three_one`, `subLeafA_three_two` (SubLeafA 3, ℓ ≤ 2, K = 5),
  `subLeafB_three_one_0/1/2` (explicit structured windows with full `q^a·s` data).
* Retained but off the headline path: `SubLeafB`, `subLeafA_of_subLeafB`, `Structured`,
  `tau_of_structured`, `subLeafAAt_mono`, `lt_pow_two_mul_of_pad`, `carry_le_sqrt`,
  `tau_le_two_mul_sqrt` — all proved, none deleted.
