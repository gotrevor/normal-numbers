# HANDOFF — entropy expedition, lap 7 (2026-09-14, Opus grind)

**Branch** `wip/g4-entropy`.  **HEAD** `1c25799`.  Working tree clean.  `lake build` green,
8948 jobs.  All eight `G4Entropy*` modules are **sorry-free** and introduce **no axioms**.

Spec: `BRIEF-entropy-expedition-2026-09-14.md`; staging
`KICKOFF-2026-09-14-entropy-expedition.md`; DIRECTION override at the top of `DIRECTION.md`.
Laps 1–5: `HANDOFF-2026-09-14-entropy-lap1.md`, `-lap5.md`.  Lap 6: `-lap6.md`.

## Headline: the brief's §4 entropy targets are **both closed**

```
NormalNumbers.G4.Sched.entropy_E0 :          -- lap 6, G4EntropyBudget.lean
  K = 4k₄ → 33856 ≤ K →
    (1/5)·k₄·(K²+1)^K < (jointLaw (gridOf K (N K)) _ k₄ (primeLambertAtBase 4)).H₂

NormalNumbers.G4.Sched.entropy_E1 :          -- lap 7, G4EntropyRate.lean
  K = 4k₄ → 160000 ≤ K →
    k₄·(K²+1)^K − 50·√K·(K²+1)^K < (jointLaw (gridOf K (N K)) _ k₄ (primeLambertAtBase 4)).H₂
```

Both `#print axioms` = `[propext, Classical.choice, Quot.sound]`.  `entropy_E1` **is** brief §4's
E1 (`H₂ ≥ m_K H_K − C H_K √K`) with `C = 50`, `K₀ = 160000`, `m_K = k₄ = K/4`,
`H_K = (K²+1)^K`; dividing by `m_K H_K` gives the qualitative E0 `H₂/(m_K H_K) ≥ 1 − 200/√K → 1`.

`isDisjunctive_four`, `isDisjunctive_two`, `isDisjunctive_base`,
`primeSumAtBase_eq_primeLambertAtBase` all unchanged and still axiom-clean.  No existing G4/G5
file was edited in laps 6–7; the two new modules only *add*.

## The two mathematical points

**1. The entropy deficit replaces the covering deficit (lap 6).**  `gridB_bound` beats the
cylinder count `((b^ℓ−1)^M)^H` with the covering deficit of an *omitted word*.  E0 has no omitted
word: the prefactor is `(2^m)^H` with `2^{−m} ≤ η`, so per unit of `r = (K²)^K` the prefactor
gives `+(K/4)log 2` and the tube fraction `η^g` gives `−(1−1/K)(K/4)log 2` — they cancel to
`O(1)·log 2`, which **loses** to the spectral term `11.5√K`.  The entropy deficit is the
replacement: prefactor `2^{(1−δ/2)mH}` leaves `−δK(log 2)/8`, and `entropy_cover_bound` closes
exactly when

    92√K + 51  ≤  δ · K · log 2        (i.e. δ ≳ 133/√K).

**2. Why the rate is `√K`, not a free parameter (lap 7).**  Since `m_K = K/4`, a deficit
`δ_K = 200/√K` costs `δ_K·m_K H_K = 50·√K·H_K`.  E1's `√K` is the *same* `√K` that the spectral
term put into the cover bound.  The four error allowances then have to be `o(K^{−1/2})`
(brief §4's `e_K`), and all four turned out to have huge unused slack:

| allowance | disjunctivity | entropy schedule | how |
|---|---|---|---|
| cover | `1/8` | `(1/8)/2^K` | `entropy_cover_bound` |
| `δbig` | `1/8` | `2^{−k₄}` | `hbig_small` — `hbig_holds`'s own exported inputs, sharper close (`2Ka⁶+34a⁴ ≤ a·((1/K)a)`) |
| `δfar` | `1/8` | `(1/8)2^{−3k₄}` | `hfar_small` — pure arithmetic on the **existing** `hfar_holds` (`(1/2)^K` vs `ε·η = (1/K)(1/2)^{k₄}`) |
| `2κ` | `1/8` | `1/(8K)` | `jackson_term_small`, new degree `DjE = (16K²2^{k₄})²` |
| `Λδ₃` | `0.106` | `(1/8)/2^{Kr}` | `smallPrime_term_tiny` |

The last row avoided ~200 lines of re-proof.  `main_term_le`/`term_a..d_le` are stated as
`Λ'·t ≤ e^{−4}` with `Λ' = 2^{2Kr}`; read them instead as a bound on `q` alone
(`q ≤ (1/8)2^{−2Kr}`) and spend the *other* half of the exponent as decay.  That needs
`Λ ≤ 2^{Kr}`, i.e. `2D+1 ≤ 2^K` rather than `≤ 4^K`, which `DjE` satisfies
(`2^{17}k₄⁴2^{2k₄} < 2^{4k₄}` for `k₄ ≥ 25`).  Same `DjE` simultaneously buys `2κ ≤ 1/(8K)`.

## Declaration map (laps 6–7)

`src/NormalNumbers/G4EntropyBudget.lean` — `hDim_le_one_add_mul_rDim`, `entropy_cover_bound`,
`entropy_cover_sum_le`, `Sched.b₀_lt_X`, `Sched.budget_terms_le`, `Sched.smallPrime_term_le`,
`Sched.entropy_E0`.

`src/NormalNumbers/G4EntropyRate.lean` — `Sched.pow_four_le_two_pow`, `Sched.DjE`,
`Sched.two_DjE_add_one_le`, `Sched.DjE_le`, `Sched.two_pow_mul_DjE_le`, `Sched.LambdaE_le`,
`Sched.jackson_term_small`, `Sched.smallPrimeBound_tiny`, `Sched.smallPrime_term_tiny`,
`Sched.big_aux1`, `Sched.big_aux2`, `Sched.hbig_small`, `Sched.hfar_small`, `Sched.entropy_E1`.

## Next, hardest first

1. **Brief §5, statement (S)** — the sampled-frequency consequence.  For fixed `ℓ`, bound
   `V^x_{K,ℓ} = (H_K(m_K−ℓ+1))^{−1} ∑_{α,h} ‖Q^x_{K,α,h,ℓ} − U_ℓ‖_TV`.  Route: entropy
   subadditivity over disjoint `ℓ`-blocks (one partition per offset mod `ℓ`, boundary bits
   counted explicitly), then a **finite entropy-to-TV inequality** — the brief warns to *check*
   the inequality rather than assume a log convention.  `entropy_E1` should give `O_ℓ(K^{−1/4})`;
   `entropy_E0` alone suffices for `V → 0`.  Prerequisite: an `H₂` subadditivity lemma for
   `FinLaw` on a product alphabet (check what `G4EntropyInfo` already has — it has `H₂`,
   `H₂_le_logb_card`, the info-set lemma; subadditivity is probably **not** there yet and is
   the first real leaf).
2. **Brief §6, `T_E`** — the frontier, untouched.  `T_E` is the *primary* transfer target
   (`E0 for Z^x_K ⟹ IsNormal 2 x`, for every `x`).  §6 explicitly says a counterexample to
   `T_mix` does **not** refute `T_E`.  The counterexample worker (support/collision structure of
   `w_{K,ℓ}` from `kIdx`/`sampleCentre`) can run independently of item 1.
3. Optional tidy: `entropy_E0` is now strictly weaker than `entropy_E1` (except for the range
   `33856 ≤ K < 160000`).  Keep both — `entropy_E0` is the shorter audit surface.

## Lean gotchas from this lap (worth the reference corpus)

- **`linarith` and non-numeral denominators.**  `a / x` with `x` not a numeral is an *opaque
  atom*: `5/K` and `25/K` never combine, so a plainly-linear budget fails.  Fix: `set B := 5/K`,
  `clear_value B`, and compare against `5 * B`.
- **`set` + big terms.**  A goal created *after* a `set` contains the raw term, not the
  abbreviation, so `linarith`'s atom matching burns the heartbeat budget on `isDefEq` against the
  unfolded `gridFrame`.  Fix: `have hfreq : <raw> = fr := rfl; rw [hfreq]`, then `clear_value`
  every let-variable that appears in the linear combination.
- **`set_option ... in` must precede the docstring**, not sit between `-/` and `theorem`.
- Avoid `nlinarith` in a context holding `(1/2)^K`-style hypotheses; it times out.  Expand to
  explicit `mul_le_mul_of_nonneg_*` steps.

## Claim discipline

Nothing here asserts normality of `G₄`, or of anything.  `entropy_E0`/`entropy_E1` are
unconditional statements about the **joint quantized sample** of the implemented base-four
schedule, for an infinite family of `K`.  The bridge from entropy to `IsNormal 2 G₄` is
brief §6's `T_E` and is **open**.
