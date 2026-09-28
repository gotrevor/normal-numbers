# HANDOFF c3-mrt 2026-09-25 — lap 35: the `D ≥ 3` input is a THEOREM, not a conjecture

**Branch** `wip/c3-mrt`.  Both green: `lake build` (9257 jobs) and
`lake build NormalNumbers.C3MrtProductPhase` (new chain tip; imports `C3MrtKPoint` →
`C3MrtArchimedean`, so it covers the whole `C3Mrt*` chain).
Prior batons: `-lap34.md`, `-lap33.md`.

## The discovery

Lap 34 concluded that `D ≥ 3` needs `KPointLogElliott k`, a strictly new open input.  That was
right about the *dependency* and wrong about the *literature*.  The relevant published result is

> **Tao–Teräväinen**, *The structure of logarithmically averaged correlations of multiplicative
> functions…*, Duke Math. J. 168 (2019) 1977–2027 (arXiv:1708.02610).  For 1-bounded
> multiplicative `g_0,…,g_k` and shifts `h_0,…,h_k`, the log-averaged correlation is a uniform
> limit of periodic sequences; and **if the product `g_0⋯g_k` does not weakly pretend to be a
> Dirichlet character, the correlation vanishes identically.**

The odd-order restriction in their Chowla corollary is an artefact of `λ^k ≡ 1` for even `k` —
the product degenerates to the constant `1`, which *is* pretentious.  **Our correlation has no
such degeneracy at any `D`,** and that is now machine-checked.

## New module `src/NormalNumbers/C3MrtProductPhase.lean` (sorry-free, trust-triple)

| name | content |
|---|---|
| `geomNat_succ_eq` | `G_{D+1} = 1 + b·G_D` (peel from the bottom) |
| `coprime_pow_geomNat` | `gcd(b^D, G_D) = 1`, because `G_D ≡ 1 (mod b)` |
| `sum_div_pow_eq` | `∑_{i<D} h/b^{i+1} = h·G_D/b^D` |
| `prod_depthRoot_eq_ee` | `∏_{i<D} ζ_i = e(h·G_D/b^D)`, `ζ_i = e(h/b^{i+1})` |
| `norm_prod_depthRoot` | the product is unimodular |
| **`prod_depthRoot_ne_one`** | `∏_{i<D} ζ_i ≠ 1` **iff** `b^D ∤ h` — the non-degeneracy, exactly |
| `exists_depth_prod_ne_one` | for `h ≠ 0` it holds for every `D > log_b|h|`, i.e. every depth the schedule visits |
| `ProductLogElliott K` | the `K`-point statement in TT's shape: non-pretentiousness on `∏ g i` |
| **`nonPretentious_prod_depthRoot`** | that hypothesis **discharged** for our target, by `nonPretentious_zOm` at `z = ∏_{i<D} ζ_i`, granting only the named VK input |

## Revised ledger for `ConjC3`

* `D = 1`: PROVED outright (Delange).
* `D = 2`: `KPointLogElliott 2` (= the dependency's `NonasymptoticLogElliott`, lap 34's `iff`) + VK.
* `D ≥ 3`: `ProductLogElliott D`, whose hypothesis we now discharge — and which is the
  **Tao–Teräväinen structure theorem**, a published theorem, plus the same single VK input.

So the crux's remaining distance is no longer "a `k`-point Elliott conjecture".  It is exactly:
**(a)** logarithmic density → natural density, and **(b)** uniformity of the rate in `D` up to
`D ≍ log log log N`, i.e. `QuantDepthElliott`.  TT is qualitative and fixed-`k`, so (b) is the
live wall; (a) is the classical log→natural gap.

## NEXT

1. **The `Fin K` assembly.**  Generalise laps 23–33 (two shifts) to `K` shifts so that
   `ProductLogElliott K` actually plugs in: the `K`-fold bridge expansion by iterating the
   already-general `sum_pow_omega_offset_eq` (arbitrary `S`, arbitrary offset `c` — written for
   exactly this), then `K`-fold CRT and pairwise coprimality of `K` powerful moduli.
   Start with the expansion identity; the tuple sum is over
   `Fintype.piFinset (fun _ : Fin K => range (B+1))` and the induction peels the LAST shift.
2. `zOmInt_prod`: `∏_i zOmInt (z i) m = zOmInt (∏_i z i) m` — trivial, and it is what turns
   `ProductLogElliott`'s hypothesis into `nonPretentious_prod_depthRoot` verbatim.
3. Then state `UniformProductLogElliott` (TT uniform in `k` with a rate) and prove
   `QuantDepthElliott ⇐ UniformProductLogElliott`.  **That** is the final named input, and it is
   the honest equivalence the kickoff asked for.

## Still refuted — DO NOT RETRY

Unchanged.  Do not attack `TwistedPrimeSumSaving`.  Note in particular: do NOT restrict the
schedule to odd depths — lap 35 shows that was never needed, the product is non-degenerate at
every depth.

## Confidence

* `prod_depthRoot_ne_one` (the non-degeneracy that makes TT applicable at every `D`): **proved**.
* `D ≥ 3` rung on TT + VK once the `Fin K` assembly is done: ≈ 70% (was: "strictly new
  conjecture needed").
* leaf TRUE ≈ 97% (up from 95%: a published theorem now covers the qualitative shape at every
  fixed depth).
* leaf PROVABLE with known techniques ≈ 25% (up from 15%; the remaining wall is uniformity in
  `D` plus log→natural, not a new Elliott conjecture).
