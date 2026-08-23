# A Strong Hot Spot Theorem — statement pin for `isNormal_of_visit_upper_bound` 📌

**Pinned 2026-08-23.**  This note is the faithfulness record for the one real-analysis
input of the Stoneham campaign, `NormalNumbers.isNormal_of_visit_upper_bound` in
`src/NormalNumbers/Stoneham.lean`.  **Verdict: the Lean statement as committed is a
faithful corollary of Theorem 1.1 of the published Bailey–Misiurewicz text (and,
independently, of the Rudolph preprint's Theorem 1) and is sufficient for the
assembly — no change needed.  The statement is fixed; the proof route is free.**

## Provenance ✅ (caveat closed 2026-08-23, same day)

Two PDFs alongside this file (both untracked — never commit a PDF to a repo that may
go public), both from `davidhbailey.com/dhbpapers/`:

- **`bailey-misiurewicz-2006-hot-spot-published.pdf`** (`dhb-mm-hotspot.pdf` upstream,
  Trevor supplied the URL): "A Strong Hot Spot Theorem", **Bailey and Michał
  Misiurewicz, dated 13 Feb 2006** — the author's-site copy of the actual published
  text (Proc. AMS 134 (2006) 2495–2501, DOI `10.1090/S0002-9939-06-08551-0`).  **This
  is the pin's primary source.**  ⚠️ The copy is **truncated**: page 3 announces a
  Section 4 applying Theorem 3.5 to `α₂,₃(0) = Σ 1/(3ⁿ·2^(3ⁿ))` (exactly our Stoneham
  constant), but the file ends at Theorem 3.5 with no Section 4 and no references.
  Section 4 is a nice cross-check for the prover, not needed for the pin — our
  `Stoneham.lean` plan already reconstructs that application (via the Bailey–Borwein
  2013 exposition).  Complete text: the AMS PDF URL (Cloudflare-challenges curl;
  works from a browser).
- **`bailey-misiurewicz-2006-hot-spot.pdf`** (`hotspot.pdf` upstream): an earlier
  **preprint of the same result with a different co-author** — "A Strong Hot Spot
  Theorem", **Bailey and Daniel J. Rudolph**, dated 2 May 2003; real-line formulation,
  self-contained 4-page ergodic proof.  Kept as corroboration (its Theorem 1 is the
  interval form used in the derivation below).

## The published paper's content (Bailey–Misiurewicz 2006)

The pin needs only its **Theorem 1.1** (the "weak hot spot theorem", which the paper
presents as a consequence of Kuipers–Niederreiter [5, page 77]):

> **Theorem 1.1.**  *The real constant α is b-normal if and only if there exists a
> constant B such that for every subinterval `[c,d)` of the unit interval,*
> `limsup_{n→∞} #{1≤j≤n : {bʲα} ∈ [c,d)}/n ≤ B(d−c)`.

The paper's own novelty is the **strong** form — Theorems 3.4/3.5, stated on the digit
sequence space `Σ = {0,…,b−1}^ℕ`: a non-b-normal `x` has a pointwise hot spot `y` with
`liminf_m limsup_n bᵐ·A(x,y,n,m)/n = ∞` (block-occurrence counts of `y`'s length-m
prefixes), proven via weak-* compactness + ergodicity of the shift + a cylinder
Besicovitch covering lemma.  **Our route does not need the strong form** — it's
recorded here because the "hot-spot route" name comes from this paper.

## The preprint's content (Bailey–Rudolph 2003, corroboration)

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

## The pin: deriving the Lean statement

Lean hypothesis: a single constant `C` with, for every b-adic interval
`I = [m/bᵏ, (m+1)/bᵏ)` (`m < bᵏ`), eventually `visitCount(orbit b {x}, I, n)/n ≤ C/bᵏ`.

**Primary derivation, from Theorem 1.1 (⇐ direction).**  Given any `[c,d)` with
`L = d−c > 0`, choose `k` with `b⁻ᵏ ≤ L < b⁻ᵏ⁺¹` (or `k = 0` if `L` is the whole
interval).  `[c,d)` meets at most `⌊L·bᵏ⌋ + 2 ≤ b + 2` scale-`k` b-adic intervals;
summing their eventual bounds (finitely many), eventually

```
#{j < n : {bʲα} ∈ [c,d)} ≤ (b+2)·C·b⁻ᵏ·n ≤ (b+2)·C·L·n ,
```

so `limsup_n (visits)/n ≤ B·(d−c)` with `B = (b+2)·C`, uniformly over intervals.
Theorem 1.1 then gives `IsNormal b x`.  ∎

**Corroborating derivation, from the Rudolph preprint's Theorem 1** (real-line hot
spots — same conclusion via the point form): fix `y ∈ [0,1)` and `h > 0`; choose `k`
with `b⁻ᵏ ≤ h < b⁻ᵏ⁺¹`.  Then `(y−h, y+h)` has length `2h < 2b·b⁻ᵏ`, so it meets at
most `2b + 1` scale-`k` b-adic intervals, and eventually
`#{j < n : {bʲα} ∈ (y−h, y+h)} ≤ (2b+1)·C·h·n`; the hot-spot ratio stays
`≤ (2b+1)·C/2 < ∞` as `h → 0`, so no point is a hot spot and normality follows.  ∎

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
2. **Elementary block counting** — the published paper itself attributes Theorem 1.1
   to Kuipers–Niederreiter [5, page 77] (non-ergodic), so the elementary route is
   paper-sanctioned, not a shortcut.  The b-adic form is (essentially) the classical
   Piatetski-Shapiro normality criterion (⚠️ name from memory, unverified).  A direct
   combinatorial proof of the Lean statement avoids the measure-theory stack entirely
   and is likely the shorter formal path.

Pick whichever grinds; do not weaken or reshape the statement to fit the route.
