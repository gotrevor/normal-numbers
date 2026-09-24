# Handoff: casting out `b − 1` — KICKOFF complete, `CastingOut.lean` sorry-free

**Date**: 2026-09-24 · **Branch**: `wip/casting-out` · **HEAD**: `daebd03` (clean tree) · Kickoff: `KICKOFF-2026-09-23-casting-out.md`

## Status

`src/NormalNumbers/CastingOut.lean`: **0 sorries**, full-repo `lake build` green (9173 jobs).
`#print axioms` on all ten ratified theorems (and the four added helpers) →
`[propext, Classical.choice, Quot.sound]`. No `native_decide`, no cited axioms.
A `git diff` of the declaration headers against the seed commit `e5f7a87` shows **additions only**:
no ratified statement, definition or binder was touched. `ConjC1/C2/C3` remain untouched `Prop`s.

## What was proved (kickoff order)

1. `windowDigitSum_modEq` — telescoping `floor_mul_pow_succ` with `b ≡ 1 [ZMOD b−1]`; the
   `Int.fract` → `x` transfer costs the extra factor `⌊x⌋(b^{n+L} − b^n)`, killed by
   `sub_dvd_pow_sub_pow`.
2. `isDisjunctive_of_isRich`, 3. `isRich_of_isNormal` — via a new `occursAt_iff_matchesAt`
   (the `OccursAt`/`MatchesAt` bridge) plus `card_filter_matchesAt_le` +
   `tendsto_div_of_bounded_diff` from `Counting.lean`.
4. `primeLambertAtBase_eq_lambertVal` — one `tsum_congr` on `omegaR_eq`.
5. `windowDigitSum_lambert_modEq` — new `floor_lambertVal_mul_pow`:
   `⌊b^N·Σ w(m)/bᵐ⌋ = Σ_{m≤N} w(m)b^{N−m} + carry N`, by `Summable.sum_add_tsum_nat_add (N+1)`.
   The head is then `≡ Σ_{m≤N} w(m)` since `(b−1) ∣ b^j − 1`, and the two ends telescope.
6. `normalCastLaw_closed` — see below. 7. `castLaw_of_isNormal` — see below.
8. `not_castUniform_of_isNormal` — `tendsto_nhds_unique` against 6 at `r = 0`; `norm_num`
   reduces the resulting real identity straight to a disjunction contradicting `b ≥ 3`.
9. `conjC1_conjC3_of_normal` — one term. 10. `erdosBorweinAtBase_eq_lambertVal` — see below.

## The two ideas worth keeping

**The count (`CastingOutCount.lean`).** Don't do Krawtchouk-style inclusion–exclusion on digit
sums. On `ZMod q` (`q = b − 1`) the per-digit counting measure is `c = u + δ₀` — every class is hit
once by `d = j`, and class `0` twice (`d = 0` and `d = q`). Since `u ∗ u = q·u`, the `L`-fold
convolution collapses, and the whole theorem is the **division-free** ℕ identity
`q · sumCount + 1 = b^L + q·[t = 0]`, proved by induction on `L` with a one-letter peel
(`Equiv.sum_comp (Fin.consEquiv …)` + `Fin.sum_univ_succ`). The only external input is
`card_digit_fibre`: `#{d < q+1 : d ≡ t} = 1 + [t = 0]`, done over `range (q+1) = insert q (range q)`.

**The law (`castLaw_of_isNormal`).** The event `windowDigitSum ≡ r` is a *disjoint* union of
length-`L` cylinders, and `Finset.card_eq_sum_card_fiberwise` is exactly the right tool: fibre the
positions by the word they carry, `f n := fun i => ⟨digitOf b (fract x) (n+i), _⟩`. Each fibre is
`MatchesAt` of `List.ofFn`, whose frequency is `b^{−L}` by normality, so `castFreq` is a *finite*
sum of convergent frequencies (`tendsto_finsetSum`) and the limit is `#W · b^{−L}`, which is
`normalCastLaw` definitionally. `L = 0` must be split off first — normality says nothing about the
empty word.

**Erdős–Borwein (`CastingOutLambert.lean`)** mirrors `primeSumAtBase_eq_primeLambertAtBase`
one-for-one with `divPowTerm b (n,k) = b^{-(n+1)(k+1)}` and `divPowIndex (n,k) = (n+1)(k+1)`;
the fibre bijection is `(n,k) ↦ n+1` onto `m.divisors`. Note `(a+1)(c+1) ≥ 1` makes the `m = 0`
fibre empty for free, matching `Nat.divisors 0 = ∅`.

## Gotchas hit this lap (mathlib v4.33.1)

- `Finset.range_succ` is gone; it is `Finset.range_add_one`.
- `Int.floor_sub_int` is `Int.floor_sub_intCast`; `tendsto_finset_sum` → `tendsto_finsetSum`.
- `tsum_subtype` is ambiguous with `Finset.tsum_subtype`: write `_root_.tsum_subtype`.
- `simp only [Finset.mem_filter] at h` does not fire on a `Finset.filter` displayed in
  set-builder form; use `(Finset.mem_filter.mp h).2` instead.
- `simp` normalises `if (0 : ℕ) = 0` to `if True`, so `rw [if_pos rfl]` fails after it — let
  `norm_num` finish the whole hypothesis instead of hand-reducing the `if`.

## Next (exact)

1. Nothing is owed on this kickoff; `box done --green` was signalled and accepted. The branch
   `wip/casting-out` is clean at `daebd03` and has **not** been pushed (no egress from the box) —
   the host pushes.
2. New files added this lap, both sorry-free and imported by `CastingOut.lean`:
   `src/NormalNumbers/CastingOutCount.lean` (the `ZMod q` convolution count) and
   `src/NormalNumbers/CastingOutLambert.lean` (the divisor Lambert series).
3. Resume point for the next session: open `DIRECTION.md` and confirm the CURRENT
   DIRECTIVE, which is untouched by this lap — Theorem C′ and the three
   `src/NormalNumbers/PrimeModelFamilyGraded.lean` leaves, hardest first: `termE5_tendsto`
   (~l.980, route-decisive) → `schedule_admissible` (~l.575) → `termE4c_tendsto` (~l.974).
4. If C1/C2/C3 are ever to be *attacked* rather than stated, the ladder is now explicit in Lean:
   `isDisjunctive_base` ⟸ `IsDisjunctive` ⟸ `IsRich` (C3) ⟸ `IsNormal`, and C1 follows from
   normality of `G4_b` via `conjC1_conjC3_of_normal`. C2 is the one genuinely independent target;
   `erdosBorweinAtBase_eq_lambertVal` now puts it in the same Lambert-value shape as `G4`, so
   `windowDigitSum_lambert_modEq` applies to it verbatim (`w m = d(m)` does **not** satisfy
   `w m ≤ m` for `m = 1`? it does: `d(1) = 1 ≤ 1`; the hypothesis holds for all `m ≥ 1`, and
   `d(0) = 0`, so the bridge is usable as stated).
