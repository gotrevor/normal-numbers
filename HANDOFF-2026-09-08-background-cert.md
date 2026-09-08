# HANDOFF 2026-09-08 — the background certificate: family I over any `1/D` 🧮

**Branch** `wip/adder-tower-c9` · **Build** 🟢 green (8883 jobs) · trust triple on every new
theorem · no `sorry` in the new file.  `DIRECTION.md` CURRENT DIRECTIVE (2026-09-08 fresh-mind
review lap) governs; this lap executed its mandated move.

## Landed

`src/NormalNumbers/MahlerBackgroundCert.lean` (new, wired into `src/NormalNumbers.lean`):

* **`mahler_lower_bound_background (p D c₀ b M e j) (h : Hyp p D b) (K : Keys p D c₀ b M)
  (C : Closure p D c₀ b e j)`** — the one-junction escape certificate over an arbitrary
  background `1/D` with arbitrary junction source `c₀` and offset `b`, slack `σ = 2b`.
  `MahlerFamilyI.lean` is the special case `D = (p+3)/2, b = 2, c₀ = p^(e−2)`.
* Structure of the proof: far states are shown **unconditionally free** (`key_far`,
  `res_far`, needing only `D < p`), so validity reduces to exactly two arithmetic keys —
  `keyA` at `N₋₁` and `keyB` at `N₀` — plus two size conditions.  `nm1_mod` / `n0_mod`
  compute the two residues in closed form; `dig_far_ne` proves `c ↦ ⌊cp/D⌋` injective on
  residues (because `D < p`), which is what separates the two closed walks at position `3`.
* Instances beyond family II's reach: **`M(29,1) ≥ 180`** (family II: `65`) and
  **`M(71,1) ≥ 1080`** (family II: `408`) — `0.913` and `0.881` of `⌊p/2⌋²`.

## Why this is the crux move

The review lap showed the factor `3` in `mahler_lower_bound_prime_family_II` is the *drift*
`g = −b·c₂⁻¹ − p (mod bD)` of the junction, and that `g = 1` (ratio `1`) ⟺ `−1 ∈ ⟨p⟩ (mod D)`.
Closed-form backgrounds `D = (p+j)/2` are stuck at `g = 3`; a per-prime `D` is not
(`M/⌊p/2⌋² ≥ 0.881` at every prime `17 … 127`, `experiments/mahler_onejunction_scan.py`).
This file is the Lean engine that turns each such `D` into a theorem.

## Next lap — start here

1. Derive `Hyp`/`Keys`/`Closure` for `D = (p+3)/2, b = 2` so **family I becomes a corollary**
   of `mahler_lower_bound_background`, then do the same for family II's `1/3`.
2. Prove `keyA`/`keyB` from the drift instead of checking them per prime: `keyB` holds for
   `M ≈ p(b−1)D/(b·g)` whenever the drift is `g`, and `keyA` for `M ≈ p(p−D)/b`.
   That converts "0.88 at every measured prime" into a theorem conditional only on
   `−1 ∈ ⟨p⟩ (mod D)`.
3. The arithmetic crux behind a uniform constant near `1/4`: for every prime `p`, some
   `D ∈ (p/3, p/2)` with `−1 ∈ ⟨p⟩ (mod D)` — for prime `D = q` this is `ord_q(p)` even.
