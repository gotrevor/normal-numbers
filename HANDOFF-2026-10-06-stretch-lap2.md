# HANDOFF 2026-10-06 — stretch lap 2 (review lap)

Branch `proof/cantorexp-stretch`.  Kickoff `KICKOFF-2026-10-05-stretch-poke.md` (+ BFR addendum).
File: `src/NormalNumbers/CantorExactExponentStretch.lean`.  Frozen signatures byte-identical
(`ae_not_liouvilleWith_all` and the headline were MOVED to the end of the file, unchanged).

## Done this lap
* Merged `proof/stretch-bfr` (StretchBFR.lean, 3 Maze rows) — commit `f07e5cb3`.
* **The crux is elementary.**  3-adic Farey separation: if `P q₀ ≡ r₀`, `P' q₀' ≡ r₀'
  (mod 3^c)`, `P ≡ P' (mod 3^j)` and `|r₀ q₀' − r₀' q₀| < 3^j`, then `P ≡ P' (mod 3^c)`
  (`padic_sep`).  Run-entering hits are thus fixed by low `j_v = 2m+3+b−L−2v` digits plus top
  `v = v₃(q)` digits: mass `Σ_v 2^{−F[v, L−2m−3+2v)}` (`hit_mass_padic`), `≈ 2^{−(μ₀−2)m}`.
  Real Farey separation for non-entering windows: `hit_mass_farey`, `2^{−F[2m+3, L−2)}`.
  Together: every window decays for every `μ₀ > 2`.
* Wired (proved modulo leaves): `ae_not_liouvilleWith_all`, `exists_computable_mem_cantorSet_irrExponent_normal_all`,
  `ev_expTest_mass_mid` (corollary).  Barrier crux link moved to `hit_mass_padic`.
* Probe `experiments/stretch_farey_perr.py` + `test_stretch_farey_perr.py` (pytest absent; run
  test functions by hand: all pass).  Numeric check of 3-adic injectivity in scratch: 0 collisions.
* Confidence restated in module doc: node 80%, BFR bet 5%.  DIRECTION.md directive set.

## Open leaves (all sorry, in order)
1. `padic_sep` — cross product ≡ (P−P')q₀q₀' mod 3^j, |·|<3^j ⇒ 0 ⇒ 3^c ∣ (P−P')q₀q₀'.
2. `card_image_mod_HS_le` — induction on j generalizing n: `(3h+d) % 3^{j+1} = 3(h % 3^j)+d`.
3. `hit_mass_padic` (crux) — cover hits by exact case (`coins_zero_window`, as in
   `hit_mass_runEntering`) ∪ groups `H_v` (`q = 3^v q₀`, `Nat.exists_eq_pow_mul_and_not_dvd`);
   `T_v := (HS free b).filter (∃ ω ∈ H_v, hd b = ·)`, inject `P ↦ (P / 3^{b−v}, P % 3^{j_v})` into
   `HS free v ×ˢ (HS free b).image (· % 3^{j_v})` (`hd_add_div` gives `P/3^{b−v} = hd v`);
   `coins_hd_mem_le`; `freeCount b = freeCount v + fc v (b−j_v) + fc (b−j_v) b`.
   Bound from hitCond: `3^e |r₀| ≤ 3 q₀` with `e = L+1−b`, `r₀ ≠ 0 ⇒ v + e ≤ m+1`.
4. `farey_sep`, 5. `hit_mass_farey` (cover by `HS free (2m+3)`, `agree_of_close`, `coins_real_cyl`).
6. `ev_expTest_mass_all` — copy `CantorExactExponent.expTest_mass_le` split; BC case: if
   `L−2 ≤ a_{k+1}` Farey (`E_k ≤ 2m+6` from `E_k ≤ m+a_k+3`, `μ₀ a_k ≤ E_k`); else padic with
   `b = a_{k+1}` (`L+1 ≤ E_{k+1}` for `m ≥ 3/(μ₀−2)`+; `E_k = a_{k+1}/(k+2) = o(m)` as k → ∞).
Then: `RunEnteringCount` (def Prop) can be PROVED by a card version of the same argument
(Maze row "per-q residue counting below 1 + log2 3" then resolves; update its verdict).

## Build notes
Scoped: `lake build NormalNumbers.CantorExactExponentStretch`; audits:
`LEAN_NUM_THREADS=1 lake build NormalNumbers.MazeAudit NormalNumbers.BarrierAudit`.
Commit `--no-verify` naming the green build.  New sorries are waived in BarrierAudit (leaves);
delete each waiver when its leaf is proved (the audit fails otherwise).
