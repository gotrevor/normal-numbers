# HANDOFF — entropy lap 16 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`, HEAD `0b9d4e6`.  `lake build` green, **8956 jobs**.  New module
`src/NormalNumbers/G4EntropyDensityOne.lean` is sorry-free and `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`); so are the four preserved declarations.  No
pre-expedition file edited; `DIRECTION.md`, `STATUS.md` and the brief untouched (grind lap).

## 1. What was proved

The session-wrap's §6 column rested on lap 9's barrier: a satisfiable `S`-local hypothesis can
force binary normality only if `S` has upper density **≥ 1/2**.  That constant was not sharp —
it came from using a single filling (zeros) of the positions `S` does not read.

**The advance: the true constant is 1.**  A digit-local property is insensitive to *every*
filling off `S`, so compare two of them.  Write `A(L) = |ones(x) ∩ S ∩ [0,L)|`, `N(L) = |Sᶜ ∩
[0,L)|`, and `B(L)` for the positions of `Sᶜ` below `L` whose *index inside `Sᶜ`* is even.

* zero filling `y₀`: ones below `L` = `A(L)`;
* parity filling `y₁` (a `1` at even-indexed positions of `Sᶜ`, `0` at odd-indexed ones):
  ones below `L` = `A(L) + B(L)`.

Both agree with `x` on `S`, so both satisfy the hypothesis, so both are normal:
`A(L)/L → 1/2` and `(A(L)+B(L))/L → 1/2`.  Hence `B(L)/L → 0`; and `N(L) ≤ 2·B(L)` always
(`allComp_le_two_mul_evenComp`, induction on `L` using the parity of the running index).  So
`N(L)/L → 0`.

| declaration | statement |
|---|---|
| `G4Entropy.tendsto_density_compl_zero` | `Sᶜ` has density `0` |
| `G4Entropy.tendsto_density_one_of_forces_normal` | `S` has density `1` |
| `G4Entropy.exists_nonnormal_of_digitLocal_of_lt_one` | the barrier at **any** `c < 1` |
| `G4Entropy.not_satisfiable_of_forces_normal_of_lt_one` | refuted-or-vacuous at any `c < 1` |
| `G4.Sched.not_T_E_of_density_lt_one` | lap 8's refutation from `density ≤ 1/4 < 1` |
| `G4.Sched.tendsto_density_one_of_jointLocal` | the sharpened §6 specification |

Supporting lemmas worth reusing: `countOcc_one_eq` (occurrences of `[1]` in the first `n`
digits = the positions below `n` carrying a `1`, exact, via `countOccurrences_range_map`),
`tendsto_ones_of_isNormal` (normality pins the `1`-density at `1/2`), the graft layer
(`graftDigits`/`graftReal`/`digitOf_graftReal`/`graft_local`, a general filling, of which lap
9's `maskReal` is the zero case), and `exists_odd_compIdx` (arbitrarily late odd-indexed
positions of `Sᶜ` — the properness of the parity graft, proved by taking the *least* element of
`Sᶜ` past a given one so the index moves by exactly `1`).

## 2. Which bottleneck moved

The brief §6 positive branch was specified as "find an arithmetic input reading a
positive-density (`≥ 1/2`) set of digit positions".  **That specification was too weak.**  The
requirement is `density → 1`: the sampled set must be co-null in `ℕ`.  Consequences:

* laps 10–14 refuted repairs whose densities were `≤ 1/8`, `≤ 1/12`, etc.  Those refutations
  were never close calls — the target they had to beat is now the whole of `ℕ`.
* `not_readableScale`'s inequality `2 d_min ≤ C·H·m` (lap 14) is a *necessary* condition for a
  repair, but not sufficient: a sampler meeting it with a fixed `C` still reads only density
  `~1/C`, which by this lap is still refuted.  The real target is a sampler whose per-scale
  density tends to `1`.
* a digit-local statement can therefore imply normality only if it is, in the density sense,
  a statement about *all* the digits.  This is the structural reason the entropy route cannot
  be repaired within digit-locality, and it is independent of `GridParams`.

## 3. Next bounded test

Two candidates, in order of value:

1. **Is the constant `1` attained?**  Prove or refute: there exists `S ≠ ℕ` (infinite
   complement, necessarily of density `0`) and a satisfiable `S`-local property that *does*
   imply normality.  Expected: yes — take `S` = the complement of a density-zero infinite set
   `Z` and `P x :=` "`x` is normal and its digits vanish on ... " — but `P` must not read `Z`,
   so the honest question is whether normality itself is `S`-local for some co-density-zero
   `S`.  It is not: normality of `x` depends on all digits, but changing a density-zero set of
   digits preserves normality (`IsNormal` is invariant under density-zero digit changes — a
   clean, provable lemma).  That invariance lemma would show the barrier is **sharp**: `P x :=
   IsNormal 2 x` is `S`-local for every `S` of density `1`.  That is the right next brick:
   `isNormal_congr_of_density_zero`.
2. **Any non-digit-local route.**  Everything in the expedition is digit-local by construction
   (`ZSample_eq_blockVal`).  A sampler reading `x` through a non-digit functional (e.g. a
   continuous test against `{4^k x}` without quantization) escapes this barrier entirely — the
   `G4Jackson`/`G4SeparatingTest` bump layer is exactly such a functional and is already in the
   repo.  Stating what "digit-local" excludes, in the form of a property that is *not* a
   function of the digits on any density-`< 1` set, is the way to name the remaining room.

Item 1 is a bounded, provable brick and makes the barrier an iff; item 2 is the open direction.
