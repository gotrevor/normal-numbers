# HANDOFF 2026-09-08 — the uniform prime lower bound is a theorem 🧮

**Branch** `wip/adder-tower-c9` · **HEAD** `6bce341` · **Build** 🟢 green (8882 jobs) · trust
triple on every new theorem · no `sorry` in the new files.  Untracked HOST files and `scratch/`
left alone.  `DIRECTION.md` CURRENT DIRECTIVE (2026-09-08 review lap) governs: its crux
("the GENERAL prime lower bound `M(p,1) ≥ c·p²`") is now proved with `c = 1/12 − o(1)`.

## Landed this lap

* `src/NormalNumbers/MahlerNumCert.lean` (new): `NumCert p` + `NumCert.Good M` ⟹
  `EscapeCert.Valid M [p−1]`; `not_hiMax_of_edge`; `EscapeCert.isClosedWalk_periodic`.
  Any future junction certificate is a `Good` proof (integer inequalities only).
* `src/NormalNumbers/MahlerFamilyI.lean` refactored onto it; base hypothesis `Hyp p e`
  (`p^e ≡ 1 (mod D)`), family-I hypothesis `HypI p k` (`p^k ≡ −1`) only for the walk.
* `src/NormalNumbers/MahlerFamilyII.lean` (new): two-junction cycle, second junction = family
  I's scaled by 3 (keys reused at channel `3m`).  **`mahler_lower_bound_prime_family_II`:
  for every prime `p ≥ 17`, `M(p,1) > (⌊p/2⌋² − 2)/3`**, exponent `e = 3φ((p+3)/2)` by Euler.
  Instance `M(29,1) ≥ 65` (`mahler_lower_bound_base29'`).
* `experiments/mahler_two_junction_scan.py`: bottleneck two-junction cycles over `1/D` at the
  complementary primes (`0.33 … 0.68 · Q²`, always through the `(3,6)` edge).

## Next lap — start here

Close the factor `3` on the complementary primes: a return junction from the coset of `−1` to
the coset of `1` with bottleneck `≈ Q²` (the scan's `j = 3, 4` winners reach `2/3·Q²`), or a
different background `1/D'`.  Order and detail in `PENDING_WORK.md` §top.  The engine needs
nothing new: a new family is a `NumCert.Good` proof plus a closed walk.
