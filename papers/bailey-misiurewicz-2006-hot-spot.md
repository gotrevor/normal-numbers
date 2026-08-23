# A Strong Hot Spot Theorem — statement pin for `isNormal_of_visit_upper_bound` 📌

**Pinned 2026-08-23.**  This note is the faithfulness record for the one real-analysis
input of the Stoneham campaign, `NormalNumbers.isNormal_of_visit_upper_bound` in
`src/NormalNumbers/Stoneham.lean`.  **Verdict: the Lean statement as committed is a
faithful corollary of the paper's Theorem 1 and is sufficient for the assembly — no
change needed.  The statement is fixed; the proof route is free.**

## Provenance ⚠️

- PDF alongside this file (`bailey-misiurewicz-2006-hot-spot.pdf`, untracked — never
  commit a PDF to a repo that may go public), fetched 2026-08-23 from
  `https://www.davidhbailey.com/dhbpapers/hotspot.pdf`.
- The PDF is a **preprint**: "A Strong Hot Spot Theorem", **David H. Bailey and Daniel
  J. Rudolph**, dated 2 May 2003.  The published version we cite in the module docstring
  is Bailey–**Misiurewicz**, Proc. AMS 134 (2006) 2495–2501 — same title, different
  second author, and the AMS text is paywalled, so **the published text has not been
  compared**.  This pin rests on the preprint's Theorem 1, whose 4-page proof is
  self-contained and was sanity-read at pin time.

## The paper's content

Throughout, `{·}` is fractional part, `α ∈ [0,1)` real, `b ≥ 2` an integer.

**Base-b hot spot** (eq. 2): a point `x ∈ [0,1)` with

```
liminf_{h→0} liminf_{n→∞}  #{0 ≤ j < n : {bʲα} ∈ (x−h, x+h)} / (2hn)  =  ∞ .
```

**Theorem 1 (Hot spot theorem).**  *α is b-normal if and only if it has no base-b
hot spots.*

Proof inputs (their Lemmas 1–5): Vitali covering lemma; Birkhoff ergodic theorem;
"a measure `ν` with `liminf_h ν(x−h,x+h)/2h < ∞` a.e.[ν] is absolutely continuous
w.r.t. Lebesgue" (Lemma 4); measure-preservation + ergodicity of the digit shift
`T(x) = {bx}` for both Lebesgue and the visit-liminf measure `ν(c,d) =
liminf_n #{j<n : {bʲα} ∈ (c,d)}/n` (Lemma 5).  Direction used here: no hot spots ⟹
`ν = Lebesgue` on intervals ⟹ liminf = limsup = length (via the complement-interval
trick, eq. 11) ⟹ b-normal.

## The pin: deriving the Lean statement from Theorem 1

Lean hypothesis: a single constant `C` with, for every b-adic interval
`I = [m/bᵏ, (m+1)/bᵏ)` (`m < bᵏ`), eventually `visitCount(orbit b {x}, I, n)/n ≤ C/bᵏ`.

Claim: this forbids every hot spot.  Fix `y ∈ [0,1)` and `h > 0`; choose `k` with
`b⁻ᵏ ≤ h < b⁻ᵏ⁺¹`.  Then `(y−h, y+h)` has length `2h < 2b·b⁻ᵏ`, so it meets at most
`2b + 1` scale-`k` b-adic intervals; summing the eventual bounds (finitely many),
eventually

```
#{j < n : {bʲα} ∈ (y−h, y+h)} ≤ (2b+1)·C·b⁻ᵏ·n ≤ (2b+1)·C·h·n ,
```

so the hot-spot ratio is eventually `≤ (2b+1)·C/2 < ∞`, uniformly as `h → 0`.  No
point is a hot spot, and Theorem 1 gives `IsNormal b x`.  ∎

Notes on the formal shape:
- The `∀ᶠ n in atTop` (eventual) hypothesis is what the window counting actually
  delivers and is stronger than `limsup ≤`, which is all the derivation needs — fine.
- Half-open `Set.Ico` b-adic intervals partition `[0,1)`; the covering argument is
  unaffected by endpoint choices.
- Hypothesis speaks of `orbit b (Int.fract x)`, conclusion of `IsNormal b x` —
  consistent with the paper's `α ∈ U` convention (normality sees only the fractional
  part; the RealDefs plumbing owns that equivalence).
- **One-sidedness is the point**: only *upper* visit bounds are demanded, which is
  exactly what survives a partial doubling cycle (a subset of a full cycle) — no
  cancellation, no character sums.

## Proof-route notes for the prover 🔨

The pin constrains the **statement only**.  Two routes exist:
1. **The paper's ergodic route** — needs Vitali covering, Birkhoff, and ×b ergodicity.
   Mathlib candidates to grep (⚠️ from memory, unverified): `Mathlib.Dynamics.Ergodic.AddCircle`
   (`ergodic_nsmul`-family on `AddCircle`), `Mathlib.MeasureTheory.Covering.Vitali`,
   and whatever pointwise-ergodic-theorem coverage exists (`Dynamics.BirkhoffSum` is
   algebra only — check whether the full Birkhoff a.e. theorem is in).
2. **Elementary block counting** — the b-adic form is (essentially) the classical
   Piatetski-Shapiro normality criterion (⚠️ name from memory, unverified); the
   preprint itself says a weaker hot-spot result is in Kuipers–Niederreiter
   [5, pg. 77] with non-ergodic methods.  A direct combinatorial proof of the Lean
   statement avoids the measure-theory stack entirely and may be the shorter formal
   path.

Pick whichever grinds; do not weaken or reshape the statement to fit the route.
