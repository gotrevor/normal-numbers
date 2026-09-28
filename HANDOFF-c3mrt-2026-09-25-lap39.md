# HANDOFF c3-mrt 2026-09-25 — lap 39: nondegeneracy is automatic, and the `K`-fold CRT

**Branch** `wip/c3-mrt`.  Both green: `lake build` (9257 jobs) and
`lake build NormalNumbers.C3MrtMultiForms` (new chain tip).
Prior batons: `-lap38.md`, `-lap37.md`, `-lap36.md`, `-lap35.md`.

## The flagged risk is gone

Lap 38 flagged the nondegeneracy of the `K` linear forms as "the next place a `K = 2` accident
could be hiding": at `K = 2` the determinant is exactly `1` (`linear_forms_det_eq_one`), which
looked like luck.  It is not luck.  With `L = lcm(d_i)`, `A_i = L/d_i`, `B_i = (a+i+1)/d_i`:

    A_i B_j − A_j B_i  =  L·(j − i) / (d_i d_j)       (`multi_forms_det`, exact)

a nonzero multiple of `j − i`.  So nondegeneracy holds for **every** `K` and every tuple, with no
hypothesis beyond `d_i ∣ L` and `d_i ∣ a+i+1` — both of which the CRT supplies by construction.
At `K = 2`, `L = d_0d_1` and `j − i = 1` recover the old `1`.

## New module `src/NormalNumbers/C3MrtMultiForms.lean` (sorry-free, trust-triple)

| name | content |
|---|---|
| **`multi_forms_det`** | `d_i d_j (A_i B_j − A_j B_i) = L (j − i)`, an exact integer identity after clearing denominators (so no `ℕ`-division reasoning beyond `Nat.mul_div_cancel'`) |
| `multi_forms_nondegenerate` | hence `A_i B_j − A_j B_i ≠ 0` for `i ≠ j` |
| `nondegenerateForms_multi` | packaged as `NondegenerateForms (fun i => L/d i) (fun i => (a+i+1)/d i)` — literally the hypothesis `ProductLogElliott K` / `KPointLogElliott K` take |
| **`joint_class_multi`** | the `K`-fold CRT: if the joint progression contains `n₀` it is *exactly* `n ≡ n₀ [MOD lcm(d_i)]`.  Needs **no coprimality** — only `d_i ∣ L`, via `Finset.lcm_dvd` on `natAbs` |

## Assembly scoreboard (depth-`K` rung, mirroring laps 23–33 at `K = 2`)

| step | general `K` |
|---|---|
| bridge expansion | ✅ `sum_pow_omega_multi_eq` (lap 36) |
| joint modulus / gain | ✅ `prod_le_lcm_mul_pow` (lap 37) |
| tuple mass finite | ✅ `tuple_mass_le` + `prod_div_lcm_le` (lap 38) |
| `K`-fold CRT to one class | ✅ `joint_class_multi` (lap 39) |
| forms nondegenerate | ✅ `nondegenerateForms_multi` (lap 39) |
| truncate moduli at `Y` | TODO |
| per-tuple rung bound + ε-chase | TODO |
| named input | `ProductLogElliott K` (= Tao–Teräväinen) + VK |

Five of seven.  **Every remaining step is an analogue of a lemma already proved at `K = 2`**, and
no structural surprise is left outstanding: the two that lap 36 and lap 38 flagged (non-coprime
moduli, degenerate forms) are both resolved and both cost less than feared.

## NEXT

1. `filter_linear_lt_eq_range` applies verbatim with `L` in place of `d·e` once
   `joint_class_multi` has rewritten the joint progression as `{k : L·k + a < N}`; do the
   `inner_sum_linear_forms` analogue (reindex `n = L·k + a`, then
   `(n+i+1)/d_i = (L/d_i)k + (a+i+1)/d_i` — the `shift_div_eq_linear` analogue, which is where
   `multi_forms_det`'s ingredients `Nat.mul_div_cancel'` get reused).
2. `multi_truncation_bound`: iterate `offset_truncation_bound_of_mass` `K` times; error
   telescopes to `≤ ∑_{i<K} (∏_{j<i} sqfWMass z_j)·(1 + log(N+K))·bridgeTail z_i Y`.
3. Pay the indexing debt from lap 38 here (`Fin K` vs `range K`): fix on `Fin K` +
   `Finset.univ.lcm`, and restate `prod_le_lcm_mul_pow` / `prod_div_lcm_le` over `Finset.univ`
   by applying the `range` versions to the `ℕ → ℕ` extension.  `joint_class_multi` is already
   `Fin K` + `Finset.univ.lcm`, so that is the convention to standardise on.
4. Then the ε-chase and the `C(D)` widening of `QuantDepthElliott` recorded in lap 37.

## Still refuted — DO NOT RETRY

Unchanged, plus: worrying that the `K` forms might be degenerate (lap 39 proves they never are),
and looking for a coprimality hypothesis in the `K`-fold CRT (there is none — `Finset.lcm_dvd`
suffices).

## Confidence

* `K ≥ 3` assembly completable: **≈ 82%** (up from 75%; the last two flagged structural risks are
  both discharged, and what remains is `K`-indexed analogues of proved `K = 2` lemmas).
* leaf TRUE ≈ 97%; leaf PROVABLE with known techniques ≈ 28%.
