# Handoff — swing at C1 (natural density), session wrap (laps 1–13)

**Date**: 2026-09-24 · **Branch**: `wip/swing-c1` · **HEAD**: `44597e8` · **tree clean, not pushed**
**Kickoff**: `KICKOFF-2026-09-24-swing-c1.md` (+ its 2026-09-24 addendum: never delete a ratified
theorem — honoured; `conjC1 : ConjC1` is still in the file, still open).
**File**: `src/NormalNumbers/SwingC1.lean` (was a 14-line stub; now ~1000 lines).
**Build**: full `lake build` green, 9176 jobs. **Sorries in the file: exactly one, `hDepthAll`.**
Everything else is `axioms = [propext, Classical.choice, Quot.sound]` (no `native_decide`, no
cited axiom, no `axiom` declaration — the kickoff forbids them).
Nothing outside `src/NormalNumbers/SwingC1.lean` and this session's HANDOFF files was touched.

## The crux, as it stands

```
conjC1 : ConjC1                     ← ratified, still open, kept by the addendum
 = conjC1_of_hState hState
 ← hState        : HState           conjC1_iff_hState  (EXACT, both directions)
 ← hWindowAll    : HWindow b L       stateLaw_of_hWindow
 ← hWindowCharAll: HWindowChar b L   hWindow_of_hWindowChar
 ← hDepthAll     : HDepth b L        hWindowChar_of_hDepth        ← THE ONLY SORRY
```

`HDepth b L` := there is ONE depth profile `κ : ℕ → ℕ`, `κ → ∞`, with

* **(A)** `HTruncDecayAt b L κ` — for every `0 < a < b^L`,
  `(1/N) Σ_{n<N} ζ^{a·windowValTrunc b L (κ n) n} → 0`, `ζ = e^{2πi/b^L}`.
  `windowValTrunc b L K n = Σ_{i<L} ω(n+1+i)b^{L−1−i} + H_K(n+L)/b^K` depends only on
  `ω(n+1), …, ω(n+L+κ n)`.
* **(B)** `HCarryOverflowAt b L κ` — the truncation is wrong on a density-zero set.

Sharing one `κ` is strictly weaker than quantifying (A) over all `κ`; that weakening was lap 10.

## What was proved (all axiom-clean)

1. `castFreq_eq_stateFreq`, `conjC1_iff_hState` — the C1 counting function EQUALS, for every `N`,
   the frequency of `n` with `Σ_{m∈(n,n+L]} ω(m) + c_{n+L} − c_n = r` in `ZMod (b−1)`.
2. `omegaCarry_rec`, `omegaCarry_eq_windowVal_div` — `c_n = (Σ_{i<L} ω(n+1+i)b^{L−1−i} + c_{n+L})/b^L`
   (integer division).  The digits of `G4_b` are the `ω`-sequence run through ordinary carrying.
3. `castState_eq_windowVal_emod` — `castState = (omegaWindowVal mod b^L) mod (b−1)`.
4. `normalCastLaw_eq_residue_count`, `stateLaw_of_hWindow` — model lemma, no error term.
5. `sum_zetaRoot_zpow`, `hWindow_of_hWindowChar` — finite Fourier on `ZMod b^L`, self-contained.
6. `omegaCarry_eq_trunc_add`, `trunc_defect_mem`, `windowVal_ne_trunc_iff` — carry truncation with
   the defect explicit; the bad event is exactly `H_K(n+L) mod b^K + c_{n+L+K} ≥ b^K`.
7. `omegaTail_le_log`, `omegaCarry_le_log` — `c_N ≤ log₂(N+1) + 1`.
8. `norm_windowCharSum_sub_trunc`, `hWindowChar_of_hDepth` — the split.
9. `floor_mul_pow_eq_windowVal`, `zetaRoot_windowVal_eq` — the Weyl bridge (below).
10. `castLaw_one_of_charSum` — the `L = 1` case, fully explicit.
11. Six `decide` anchors on the model side, incl. the `14/27` vs `13/27` bias at `b=3, L=3`.

## Three corrections/refutations this session (do not redo)

* **Kickoff step 1 is wrong for the mod-`(b−1)` reduction.**  No growing truncation depth is
  needed there: `b^L ≡ 1 (mod b−1)` annihilates the carry's unbounded part identically (item 3).
* **Constant-depth truncation is FALSE** (lap 8).  `c_N → ∞`, so for fixed `K` the bad-set density
  tends to **1**.  Hence the depth profile `κ`, with `κ n ≳ log_b log n` (item 7 makes that rate
  a theorem, not a heuristic).
* **Kátai / Bourgain–Sarnak–Ziegler does not reach the leaf** (lap 12).  `ζ^{a·ω(n+1)}` IS a
  modulus-one multiplicative function with `g(p) = ζ^a ≠ 1`, so its own mean vanishes by
  Delange/Halász — but KBSZ needs it at `n`, not at the shift `n+1`; run the other way it demands
  the prime-pair condition for the carry factor, with no handle.  Both directions die on the shift.

## Literature status (kickoff step 4)

* One-coordinate, fixed modulus: **KNOWN** — Delange (1969).  `ω` is uniformly distributed mod
  every `q ≥ 2`, since `ω(p) = 1` and `Σ_p 1/p = ∞` satisfies his criterion.
* Clause (A): joint version over shifts — **open, Elliott-type**.  The frequency `a/b^L` is
  RATIONAL, so the Kátai-style `(αΩ(n), βΩ(n+1))` u.d.-mod-1 results (which need irrational
  `α, β`) do not apply.
* Clause (B): the modulus `b^{κ n}` grows with `n`, so this is the **varying-moduli** branch
  (cf. arXiv 2401.04199), not the classical fixed-`q` theory.

## Exact next moves

1. **Best lead — exploit `zetaRoot_windowVal_eq`.**
   `ζ_{b^L}^{a·omegaWindowVal b L n} = e(a·bⁿ·x)·e(−a·fract(b^{n+L}x)/b^L)`, `x = G4_b`.
   For FIXED `a` the twist is `1 + O(a/b^L)`, so those frequencies reduce to the repo's own
   `WindowDecay h` / `CRTConstant h` hypotheses in `G4WiringCRT.lean`.  Formalise
   `HTruncDecayAt` for the range `a ≤ A(L)` with `A(L)/b^L → 0` FROM `WindowDecay`, leaving only
   the frequencies `a ≍ b^L`.  That would cut the leaf down to the low-order digits of the window
   and is the first genuinely new reduction available.
2. Then: the residual high-frequency range.  There the twist is not negligible and the tail factor
   must be handled — this is where clause (B)'s varying-moduli character really lives.
3. Do NOT re-attack C1 via normality of `G4_b`: `conjC1_conjC3_of_normal` in `CastingOut.lean`
   already records that route, and normality is the repo's own open headline.
4. `CastingOut.lean`, `CastingOutCount.lean`, `CastingOutLambert.lean`, `Maze.lean`, `papers/`,
   `agent-mail/` and the other KICKOFFs were NOT touched and must stay that way.
