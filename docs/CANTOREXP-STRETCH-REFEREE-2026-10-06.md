# Referee: the stretch headline (exact exponent `μ₀ > 2` in `K`, normal to bases prime to 3)

Subject: `CantorExactExponentStretch.exists_computable_mem_cantorSet_irrExponent_normal_all`.  The
check had two independent passes, both started fresh with no conclusions fed in.  (1) An English proof check of
the load-bearing lemmas and of the faithfulness of the statement.  (2) A literature sweep with
forward citations.  This follows `CANTOR-EXACT-EXPONENT-AUDIT-2026-10-04.md`.

## Verdict

**Accept.**  The referee found no mathematical error and the statement is faithful.  All
findings were documentation issues, and they are fixed in the same commit as this report.  The
novelty is the **normality clause**: the exponent-in-`K` half is known, and the counting principle is
classical, but its use here is not.

## Statement faithfulness (pass 1)

- `HasIrrExponent x μ₀` = `(∀ p < μ₀, LiouvilleWith p x) ∧ ∀ p > μ₀, ¬ LiouvilleWith p x`, with
  Mathlib's `LiouvilleWith`.  Since `LiouvilleWith` is antitone in `p`, this is exactly "the
  irrationality exponent is `μ₀`".
- `cantorSet` is Mathlib's middle-thirds set.  `Computable` is Mathlib's partial-recursive
  `Computable` on `ℕ → Bool`.  The existential is classical, since the thresholds come from
  `eventually_atTop`, but the witness is a genuine computable function.  The bad-event test must be
  `Primrec₂`.
- `IsNormal b` is full (block) normality.  The headline uses no `Literature.*` hypothesis.
- Scope: **rational** `μ₀ > 2`, because rationality makes the schedule primitive recursive.  The
  module title said "every `μ₀ > 2`"; it is fixed to say "rational".

## Lemma-by-lemma (pass 1, re-derived by hand)

| Lemma | Check |
|---|---|
| `farey_sep` | Distinct fractions with `q, q' < 3^{m+1}` differ by `> 3^{−(2m+2)}`.  ✓ |
| `hit_mass_farey` | Group by the `2m+3` digit prefix; within a group `farey_sep` forces one fraction, so free coins agree below `L−2`.  ✓ |
| `padic_sep` | The cross product is `≡ 0 (mod 3^j)` and `< 3^j`, so it is `0`, so `3^c ∣ (P−P')q₀q₀'`.  ✓ |
| `hit_classify` | Forced digits on `[b, L]` turn a hit into `P q ≡ r (mod 3^b)` with small `r`.  The case `r = 0` forces zeros on `[m, b)`; otherwise the `v = v₃(q)` bound holds.  ✓ |
| `group_sep` | `3^e·|X| ≤ 6 q₀q₀' < 3^{e+j}`, with `j = 2m+3+b−L−2v`.  ✓ |
| `hit_mass_padic` | Bounds the **union** of bad numerators.  `P ↦ (P / 3^{b−v}, P mod 3^{j_v})` is injective on each group.  The side condition `j_v ≤ b−v` holds, and no ℕ-subtraction truncates.  ✓ |
| `expTest_mass_le_all` | The three cases (triangle; Farey with `L−2 ≤ a'`; 3-adic with `a' < L−2`) cover every `m ≥ M₀`, using `E_k ≤ (μ₀−2)m/2` once `k+2 ≥ ⌈2(μ₀+1)/(μ₀−2)⌉`.  ✓ |
| `ev_expTest_mass_all`, `ae_not_liouvilleWith_all` | Masses are `o(1/m²)`.  Borel–Cantelli plus `hasIrrExponent_of_avoid_two` give the upper bound.  The lower bound comes from run truncations.  ✓ |

The headline does not go through `ae_not_liouvilleWith_all`.  It feeds `ev_expTest_mass_all` to
the derandomizer `exists_computable_normal_avoid` directly; the measure statement is a sibling.

## Documentation findings (fixed)

1. Stale "Confidence 65%" / "the one open leaf" docstrings on `ev_expTest_mass_mid` and
   `ae_not_liouvilleWith_mid`.  The difficulty check in `CantorExactExponent.lean` still listed the
   upper bound as unproved.  `EndpointRationalCount` claimed to be needed (60%).
2. The title overclaimed: "every `μ₀ > 2`" now reads "every rational `μ₀ > 2`".
3. "BFR bet: 5%" had no referent and was stale.  It now says below 1%, with the referent, pointing to `StretchBFR`.
4. The module doc said both cases decay like `2^{−(μ₀−2)m+o(m)}`.  The proved 3-adic bound is
   `2^{12}·2^{−(μ₀−2)m/2}`; it is now stated.
5. Not fixed, recorded: `hit_mass_runEntering` is unused (now marked superseded).  `J₀` is
   extracted from a `Tendsto`, so the proof does not print an explicit program, although `M₀` is
   explicit.

## Prior art (pass 2)

Tags: [read] = PDF text read; [abs] = abstract only; [2nd] = described by a paper that was read.

- **In `K` with exact exponent: known.**  Bugeaud, Math. Ann. 341 (2008) [2nd, via BBS]: lacunary
  `2Σ3^{−n_j}` gives every `μ ≥ 2` (`Literature.Bugeaud2008Thm721`).
  Becher–Bugeaud–Slaman, Proc. AMS 144 (2016), arXiv 1410.1017, Thm 1 [read]: such numbers can be
  taken computable for every rational `μ₀ ≥ 2`.  Levesley–Salp–Velani, Math. Ann. 338 (2007) [read]:
  explicit exact order only for `τ ≥ (3+√5)/2`.  None of these has normality: the lacunary points
  have digit density 0.  Lean: `bugeaud2008_rational_of_stretch` (dropping normality, the headline
  is the rational case of Bugeaud's theorem).
- **Exact exponent with normality, outside `K`: known.**  Bugeaud 2002 and Becher–Heiber–Slaman
  2015 (absolutely normal Liouville); Kaufman 1981 (the exact-exponent set has Fourier dimension
  `2/μ`).  A "Becher–Slaman" theorem (simple normality to a prescribed set of bases, with any
  exponent) appears in Slaman's 2019 IMS slides [read], but its source paper was not located: it
  is in neither arXiv 1311.0332 nor 1311.0333.  None of these reaches `K`, which carries no
  Rajchman measure.
- **In `K` and normal: known only at exponent 2** (Cassels, Schmidt, Hochman–Shmerkin,
  Dayan–Ganguly–Weiss; typical points have exponent 2 by Weiss 2001) **and ∞** (this repo, Bugeaud
  Problem 10.37, `docs/notes/bugeaud-10-37-cantor-liouville.md`).
- **The counting principle.**  `padic_sep` is the standard non-archimedean gap principle (Bugeaud,
  INTEGERS 18 (2018), Lemma 1 [read], now cited in its docstring).  `farey_sep` is the
  one-dimensional simplex lemma (Kristensen–Thorn–Velani 2006).  Not found anywhere: turning a
  real approximation at a forced zero-run into `P q ≡ r (mod 3^b)` and bounding the union of hit
  numerators by their low and top digits.  The known counts (Bugeaud–Durand 2016, Schleischitz
  1812.10689, Chow–Varjú–Yu 2402.18395, Fishman–Simmons, Tan–Wang–Wu) count rationals near `K`,
  a different object.  As `StretchBFR` records, the 3-adic count gives no new count of rationals
  near `K`.
- **2025–26 checked** [abs]: Li–Velani–Wang 2512.17173, He–Liao 2602.01307, Bandi 2606.27034,
  Lai–Xie 2601.03402, Manai 2508.09319 and 2609.24665, Algom survey 2504.18192.  None has
  normality at an exponent strictly between 2 and ∞.

**Freshness: about 80%** that the triple (in `K`, exact exponent `μ₀` for every rational `μ₀ > 2`,
normal to every base prime to 3) is not in the literature.  Instrument limits: citer lists were
filtered by title and abstract.  Bugeaud 2008 was described secondhand, and the snippet that it
"applies to more general missing digit sets" is unverified.  If that snippet holds, it would cover
the exponent half of the base-5 sibling for every `μ ≥ 2`.  The Becher–Slaman theorem is sourced
only from slides.  Forward citations were checked for math/0505074, 1410.1017, 2005.09300,
2103.00544, 1208.2089, 2512.17173, 2002.00455, 1302.5792, 2102.02151 and 2606.27034.
