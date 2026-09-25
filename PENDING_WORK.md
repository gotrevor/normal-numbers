## Lap 102 (2026-09-25) — RESTATEMENT run: the TT interface repaired, consumers re-audited

Operator-scoped restatement lap (no crux advance).  New `src/NormalNumbers/C3MrtTTDefect.lean`.

**(a) Defects machine-checked.**  `ttNonPretentious_trivial` (old `TTNonPretentious` holds for
every 1-bounded `g`, witness `A = 1/L`), `not_kPointNoExcWith_const_one`,
`not_kPointNaturalCorrelationNoExc`, `not_twoPointNaturalCorrelationNoExc` (the `D = 2` "named
open problem" is FALSE), `twoPointNaturalCorrelation_trivially_true` (the Lebesgue-charged
exceptional set is free).  Four new `Maze.lean` kernel rows.

**(b) Faithful restatements + guards.**  `ttPretentiousSumChar` (Dirichlet characters),
`TTNonPretentiousAt A` / `TTNonPretentiousUnif` (constant OUTSIDE `X, L`; conductors
`q ≤ (log X)^{1/125}`; twists `|t| ≤ X²`), `TwoPointDyadicCorrelation` (exceptional set a
`Finset` of dyadic scales, cost a fraction of `#(dyadicScales X)`), `KPointNoExcAtWith A`.
Bridges `ttNonPretentious_of_At`, `kPointNoExcAtWith_of_with` (nothing weakened).  Guards
`not_ttNonPretentiousUnif_one`, `not_ttNonPretentiousAt_one`, `const_one_not_faithful`,
`full_exceptional_set_not_admissible` + `exists_L_cost_lt_one`.

**(c) SURVIVORS table** — `HANDOFF-2026-09-25-tt-interface-restated.md`.  ~50 declarations across
9 modules are VACUOUS (`conjC3_of_geom_input` included); the window/schedule/threshold algebra
and `depthRoot` theory survive with content; the one genuine survivor on the analytic side is
`ttNonPretentious_of_uniformResonantMass`, whose constant is *already* uniform in `X, L`.

**Next attack.** ① Rethread `dyadic_window_bound_with` → … → `conjC3_of_geom_input` onto
`KPointNoExcAtWith A` (the consumer must now SUPPLY `TTNonPretentiousAt A`, with `A` uniform in
`b, h', X, L`).  ② Upgrade `ttNonPretentious_of_uniformResonantMass` to the faithful hypothesis:
the missing content is Dirichlet characters `q > 1` and twists up to `X²`, not the constant.
③ Re-read TT 3.1(ii)'s conclusion once more for the exact exceptional-set shape before freezing
`TwoPointDyadicCorrelation` at general `K`.

## Lap 103 (2026-09-25) — the headline REPAIRED: chain parametric in the archimedean hypothesis

The lap-102 refutation left `conjC3_of_geom_input` vacuous.  Rather than copy the chain, the
archimedean hypothesis is now a **parameter** everywhere:

* `C3MrtUnifK.KPointNoExcFor Pnp cK CstK K` (+ `kPointNoExcFor_of_with`) — `KPointNoExcWith`
  with the non-pretentiousness predicate abstracted and the scale condition `3 ≤ X` (all the
  consumer uses; it applies the input at `X = N²`).  `dyadic_window_bound_with`,
  `windowPhi_hwin`, `depthAvg_le_with` and the whole tendsto stack up to
  `depthAvg_gen_tendsto_of_geom` / `_of_geom_slow` are now stated over it — *in place*, with the
  old call sites wrapped, so nothing downstream was duplicated.
* `C3MrtSlowSched.ArchSupply Pnp b` — the certificate the chain instantiated silently, named:
  for every primitive `h'` an exponent `κ ∈ (0,1]` with `Pnp (zOmegaNat (depthRoot b h' 0)) X L`
  for `1 ≤ L ≤ (log X)^κ`.  `archSupply_tt` is the old (content-free) instance.
* `depthDiagonalSlow_of_geom_for`, `weylLambertTwist_of_geom_slow_for`,
  `weylLambertTwist_of_geom_input_for`, `conjC3_of_geom_input_for` — the chain over `Pnp`.
* **`C3MrtFaithfulInput.conjC3_of_geom_input_at`** — the repaired headline:

      (∀ b ≥ 3, ∀ K, KPointNoExcAtWith A (cKgeom c₀ θ b) (CstKdeg m) K) →
      (∀ b ≥ 3, ArchSupply (TTNonPretentiousAt A) b) → ConjC3        (0 < θ < 1)

  Both hypotheses faithful (constant outside `X, L`; characters of modulus
  `≤ (log X)^{1/125}`; twists `|t| ≤ X²`), neither refuted by the constant-one family
  (`const_one_not_faithful`), neither trivially true (`not_ttNonPretentiousUnif_one`).

**Honest ledger change.** The headline now rests on TWO named open statements, not one: the
`K`-point correlation input AND the archimedean supply.  The second was previously hidden inside
a vacuous instance.

**Next attack.** ① Discharge `ArchSupply (TTNonPretentiousAt A) b` as far as the resonance
machinery reaches: `ttNonPretentious_of_uniformResonantMass` already gives a constant uniform in
`X, L` (`A = exp(−C₁(z))`); the two genuine gaps are Dirichlet characters `q > 1` (needs the
character-twisted resonant-mass bound) and twists `|t| ≤ X²` rather than `(log X)^{1/125}` —
note the latter is where TT's own `M(g; X², Q)` cuts the twist at `X²`, so re-read
`papers/tao-teravainen-2025-quantitative-correlations.txt:557-576` before assuming the wide
range is needed for (3.3) as opposed to for the *conclusion*.  ② Rethread `C3MrtRootsInput` /
`C3MrtDepthInput` / `C3MrtEvtInput` / `C3MrtDyadicInput` onto `KPointNoExcFor` the same way
(mechanical; they are copies of the `_with` chain).  ③ The crux itself (one Weyl sum, laps
100-101) is unchanged; its interface is now `KPointNoExcAtWith`.

## Lap 104 (2026-09-25) — the faithful archimedean supply, DECOMPOSED (and one route refuted)

New `src/NormalNumbers/C3MrtArchFaithful.lean`, all axiom-clean.

**The exact split.**  `ttPretentiousSumChar_eq`: for `‖z‖ = 1`,

    ttPretentiousSumChar (zOmegaNat z) X χ t = ∑_{p ≤ X²} 1/p − Re(z · twistedPrimeSum X χ t)

with `twistedPrimeSum X χ t = ∑_{p ≤ X²} conj(χ(p)) p^{-it}/p`.  With two-sided Mertens
(`abs_primeReciprocals_sub_log_log_le`) this gives `ttPretentiousSumChar_ge`:
`log log X² − mertensBound − Re(z·T) ≤ ttPretentiousSumChar`.  So the ENTIRE faithful archimedean
obligation is one bound on `Re(z · twistedPrimeSum)`.

**Refuted sub-route (recorded in the file's doc-comment).**  Stating the bound on `‖T‖` instead
of `Re(z·T)` is FALSE in the narrow range: at `t = 0`, `χ = 1`, `T` is the full mass
`≈ log log X`.  What makes the pretentious sum large there is the *direction* of `z`, not the
size of `T` — that is precisely the resonance mechanism.  Hence `NarrowTwistSmall` is stated
with `Re` and `WideTwistSmall` with the norm (converted by `re_le_norm`).

**Second refuted sub-route.**  The resonance certificate `ttNonPretentious_of_uniformResonantMass`
CANNOT cover the faithful twist range: its resonant-mass bound carries `log(2+|t|)`, affordable
only for `|t| ≤ (log X)^{1/125}` (that is where its `ht4` step is used).  At `|t| ≤ X²` that term
is `≍ log X` and swamps `log log X`.  So the wide range needs cancellation in
`∑_{p≤Y} conj(χ(p))p^{-it}/p` — a zero-free region for `L(s,χ)` (Vinogradov–Korobov), not a
resonance count.  This is the genuinely NEW analytic debt created by faithfulness.

**The chain now:** `NarrowTwistSmall` + `WideTwistSmall` → `faithfulArchLower_of_twist_small` →
`FaithfulArchLower b C` → `archSupply_of_faithfulArchLower` → `ArchSupply (TTNonPretentiousAt
(exp (−C))) b` → `conjC3_of_geom_input_lower : … → ConjC3`.  `ttNonPretentiousAt_of_lower` is the
exponentiation step, once and for all.

**Next attack.** ① `narrowTwistSmall_of_uniformResonantMass` at `q = 1`: the algebra above turns
the existing `ttPretentiousSum_ge` + `UniformResonantMass` into exactly `Re(zT) ≤ cos ε · log log
X² + (1−cos ε)·resonantMass`, i.e. `NarrowTwistSmall` with `κ ≈ 1 − cos ε − 100ε`.  Do this first;
it is bookkeeping over lemmas that already exist. ② The character case `q > 1` of the narrow
range: the resonance windows must be taken per residue class mod `q`, so `resonant_mass_le` needs
a `φ(q)`-fold version — state it as `UniformResonantMassChar` and check the count. ③ The wide
range `WideTwistSmall`: look for a mathlib/PNTPort route to `∑_{p≤Y} χ(p)p^{-it}/p = O(1)` for
`|t| ≥ (log Y)^{1/125}`; `src/PNTPort` has the Wiener–Ikehara/MediumPNT apparatus but no twisted
zero-free region.

## Lap 105 (2026-09-25) — the narrow range is DISCHARGED at the trivial character

* `C3MrtTTPretentious.ttPretentiousSum_lower_of_uniformResonantMass` — the resonance
  certificate's *content*, extracted from the (now vacuous) TT (3.3) corollary:
  `ttExponent z · log log X − C₁ ≤ ttPretentiousSum (zOmegaNat z) X t` for all `3 ≤ X` and
  `|t| ≤ (log X)^{1/125}`, with `C₁ = C₁(z) ≥ 0` independent of `X, t`.
  `ttNonPretentious_of_uniformResonantMass` is now a five-line corollary of it.
* `C3MrtArchFaithful.narrowTwistSmallTriv_of_uniformResonantMass` —
  `NarrowTwistSmallTriv z (ttExponent z) C` for unimodular `z ≠ 1`, on the route's existing
  single analytic input.  Via `ttPretentiousSumChar_eq` + two-sided Mertens + `log_ceil_sq_le`
  (`log⌈X²⌉ ≤ 3 log X`).

**So the narrow range costs nothing new; the open part of it is exactly the CHARACTERS**
(`narrowTwistSmall_triv_of_narrow` pins that: `NarrowTwistSmall` at `q = 1` is the discharged
statement).  Remaining debts, both explicit:
① narrow range, `q > 1`: resonance windows per residue class mod `q` — a `φ(q)`-fold
`resonant_mass_le`; the count must beat `(1 − ttExponent) log log X`, and `q ≤ (log X)^{1/125}`
is the only size information available.
② wide range `|t| > (log X)^{1/125}`: `WideTwistSmall`, needs cancellation in
`∑_{p≤Y} conj(χ(p))p^{-it}/p` (zero-free region for `L(s,χ)`); the resonance route is refuted
there (lap 104).

## Lap 106 (2026-09-25) — the narrow range's PRINCIPAL characters reduced to `q = 1`

`C3MrtArchFaithful`, all axiom-clean:

* `sum_inv_primes_dvd_le` — `∑_{p ≤ Y, p ∣ q} 1/p ≤ log log q + mertensBound` (`q ≥ 2`).
* `norm_twistedPrimeSum_principal_sub` — the principal character mod `q` and the trivial
  character differ only on `p ∣ q`: `‖T₁ − T_{χ₀}‖ ≤ ∑_{p ∣ q} 1/p`.
* `twistedPrimeSum_zero_modulus` — the `q = 0` corner: in `ZMod 0 = ℤ` no prime is a unit, so
  `T = 0`.
* `narrowTwist_principal_of_triv` — the principal characters cost only `log log q + O(1) ≤
  log log log X + O(1)`, absorbed by halving the saving (`log u ≤ (κ/2)u − 1 − log(κ/2)`).
* `NonPrincipalTwistSmall` + `narrowTwistSmall_of_triv_of_nonPrincipal` —
  `NarrowTwistSmallTriv z κ C` **and** the non-principal debt give the full
  `NarrowTwistSmall z (κ/2) C'`.

So the narrow range is now: `q = 1` **proved** (lap 105, on `UniformResonantMass`), principal
`q > 1` **proved** (this lap), non-principal `q > 1` open — and the non-principal case is
expected to be the *easy* one (`∑_{p≤Y} χ(p)p^{-it}/p = O(log log(q(2+|t|)))` by non-vanishing of
`L(1+it,χ)`, which at `q, |t| ≤ (log X)^{1/125}` is `O(log log log X)`).

**NEW OBLIGATION SURFACED — uniformity of the constant in the twist `h'`.**  `ArchSupply
(TTNonPretentiousAt A) b` fixes ONE `A` across all primitive `h'`, so `FaithfulArchLower b C`
needs `C` uniform in `h'` and a `κ(h') > 0`.  This was invisible while the hypothesis was
vacuous.  It looks provable and should be the next concrete step:
`depthRoot b h' 0 = ee(h'/b)` with `b ∤ h'`, so `|arg (depthRoot b h' 0)| ≥ 2π/b`, hence
`ttEps ≥ min(π/b, 1/256)` — a bound depending on `b` ALONE.  Then `ttExponent` is increasing in
`ε` on `[0, 1/256]`, giving a uniform `κ(b) > 0`; the constant `C₁` of
`ttPretentiousSum_lower_of_uniformResonantMass` must likewise be shown uniform over that finite
angle set (there are at most `b − 1` residues `h' mod b`, so this should be a `Finset.max`
argument, not an analytic one).

**Next attack.** ① The `κ(b)`/`C(b)` uniformity above (`Finset.max` over `h' mod b`; the
`UniformResonantMass` constant depends on `z` only through `arg z`).  ② `NonPrincipalTwistSmall`.
③ `WideTwistSmall` (lap 104's refutation says: needs a zero-free region, not resonance).

## Lap 93 (2026-09-25) — the open input is RESTRICTED to the family the chain actually uses

**New file `src/NormalNumbers/C3MrtRootsInput.lean` (12 declarations, all trust-triple clean).**
Executes PENDING_WORK lap-92 levers ② and ③ in one stroke.

`KPointNoExcWith cK CstK K` quantifies over EVERY coprime-multiplicative bounded family
`g : Fin K → ℕ → ℂ` and EVERY injective shift vector `hsh : Fin K → ℕ`.  The C3 chain uses
neither generality: its factors are always `g i = zOmegaNat (z i)` with `‖z i‖ = 1` (in fact
`z i = depthRoot b h' i`), and its shifts are always `hsh i = i + 1`.  So

    KPointNoExcRoots cK CstK K :=
      ∀ z : ℕ → ℂ, (∀ i, ‖z i‖ = 1) → ∀ X L, 2 ≤ X → 1 ≤ L → L ≤ log X →
        (∃ i : Fin K, TTNonPretentious (zOmegaNat (z i)) X L) →
          ∀ N, √X ≤ N → N ≤ X → ∀ W r, 0 < W → W ≤ L^{cK K} → K+1 ≤ L^{cK K} →
            ‖(W/N) • ∑_{n ∈ (N,2N], n ≡ r (W)} ∏_{i<K} z i ^ ω(n+i+1)‖ ≤ CstK K · L^{-cK K}

with `kPointNoExcRoots_of_with : KPointNoExcWith → KPointNoExcRoots` so nothing is lost, and the
whole chain rethreaded onto it:

    conjC3_of_geom_input_roots :
      (∀ b ≥ 3, ∀ K, KPointNoExcRoots (cKgeom c₀ θ b) (CstKdeg m) K) → ConjC3     (0 < θ < 1)

`dyadic_window_bound_roots`, `windowPhi_hwin_roots`, `depthAvg_le_roots`,
`depthAvg_gen_tendsto_of_unif_roots`, `depthAvg_gen_tendsto_of_geom_slow_roots`,
`depthDiagonalSlow_of_geom_roots`, `weylLambertTwist_of_geom_slow_roots`,
`weylLambertTwist_of_geom_input_roots`.  Only `dyadic_window_bound_roots` differs in its proof,
and only in the one line that applies the input — the shift-bound and injectivity side goals are
now discharged inside `kPointNoExcRoots_of_with` instead.

**Why this narrowing is free where the lap-92 `∀ i` one was not.**  Lap 92 failed because the
consumer could not DISCHARGE the weaker hypothesis at a shared cutoff `L`
(`ttExponent (depthRoot b h' i) → 0`).  Restricting the *family* and the *shifts* asks the
consumer to discharge nothing new: it was already only instantiating at `zOmegaNat ∘ z` with
`hsh i = i+1`.  The gain is entirely on the ledger — the open statement is no longer "the
`K`-point Elliott bound for arbitrary bounded multiplicative functions" but "…for the
one-parameter family `n ↦ z^{ω(n)}`, `|z| = 1`, at consecutive shifts `n+1, …, n+K`".

**Next attack (lap 94+).**
1. **`∀ᶠ K`.**  `KN N = max 1 (depthSlow b N - v) → ∞`, so every fixed `K` is used at only
   finitely many `N` and `depthAvg` at finitely many scales cannot move a `Tendsto`.  Weaken
   `hin : ∀ K, …` to `∀ᶠ K in atTop, …` in `depthAvg_gen_tendsto_of_unif_roots` (its `hin _` sits
   inside a `filter_upwards`, so the change is to add `hKNtop.eventually hin` to that
   `filter_upwards` list), then up the chain.  Cheap; low mathematical value but honest.
2. **Restrict `z` further.**  `KPointNoExcRoots` still quantifies over all unimodular `z : ℕ → ℂ`;
   the chain only feeds `z i = depthRoot b h' i = e(h'/b^{i+1})` — a *geometric* family of roots
   with `z i → 1`.  Defining `KPointNoExcDepth b h'` (the same bound for that one family) would
   cut the open statement down to a single explicit sequence.  Check first whether the rest of
   the chain really never varies `z` (it does not — `depthAvg_le_roots` fixes
   `z := fun i => depthRoot b hh i`), so this should be another free restriction.
3. Then the `Statement.lean` audit surface + ledger writeup (C3-T6).

## Lap 92 (2026-09-25) — the `∀ i` narrowing is REFUTED; the `∃ i` is load-bearing

**Directive items 1 and 4 LANDED, items 2–3 REFUTED by a compiler-checked probe.**  New file
`src/NormalNumbers/C3MrtNoExcAll.lean` (6 declarations, all `[propext, Classical.choice,
Quot.sound]`).

**① `depthRoot_ne_one_of_not_dvd_all`** — every twist level of a primitive `h'` has a nontrivial
root, not just the leading one.  So the *bookkeeping* premise of the `∀ i` plan is true.

**④ `kPointNoExcWith_mono`** — the input is monotone: down in `cK`, up in `CstK`.  Both
hypotheses (`W ≤ L^{cK K}`, `hsh i ≤ L^{cK K}`) tighten exactly when the conclusion
(`≤ CstK K·L^{-cK K}`) loosens, because `L ≥ 1`.  **Ledger consequence:** asking for
`KPointNoExcWith (cKgeom c₀ θ b) (CstKdeg m) K` is not a new statement beyond
`∀ K, KPointNaturalCorrelationNoExc K` — it is exactly the demand that the constants that
statement already produces existentially degrade no faster than `c₀b^{-θK}`, `exp((K+1)^m)`.
The headline hypothesis is a *rate*, and that is now a theorem, not prose.

**②③ REFUTED — and the refutation is quantitative, not bookkeeping.**  `KPointNoExcAllWith`
(defined in the new file, with `kPointNoExcAllWith_of_with` so nothing is lost) weakens
`∃ i, TTNonPretentious (g i) X L` to `∀ i, …`.  The C3 chain *can* show every factor is
non-pretentious — but not at a common cutoff `L`.  `ttNonPretentious_zOmegaNat` certifies
`zOmegaNat z` only for `L ≤ (log X)^{ttExponent z}`, and

    tendsto_ttExponent_depthRoot : ttExponent (depthRoot b h i) → 0   (i → ∞)

because `depthRoot b h i = e(h/b^{i+1}) → 1` (`tendsto_depthRoot_one`) and
`ttExponent z = (1-cos(ttEps z))(1 - (126/125)(100 ttEps z))` with `ttEps z = min(|arg z|/2, 1/256)`.
The `K`-point statement has ONE `L` shared by all `K` factors, so the `∀ i` form would force
`κ ≤ inf_i ttExponent (depthRoot b h' i) = 0`; `no_uniform_ttExponent_depthRoot` shows no positive
`κ` survives.  Quantitatively `ttExponent (depthRoot b h' i) ≍ b^{-2i}`, so at the diagonal level
`K = D_N` even the *threshold* clause `L^{c_K} ≥ K+1` would read
`b^{-(2+θ)K}·log log X ≳ log K`, i.e. `u^{-1-θ}(log u)^{-(2+θ)} ≳ log log u` — false.

**What this tells us about the route (the real content).**  The deep digits of the Lambert
constant are quantitatively *almost* pretentious: `z_i = e(h/b^{i+1})` sits within `O(b^{-i})` of
`1`, so `z_i^ω` is nearly the constant function `1`.  Only the LEADING root carries usable
non-pretentiousness, and that is precisely why the chain fixes `κ = ttExponent (depthRoot b h' 0)`
once and for all.  The `∃ i` in `KPointNoExcWith` is therefore not slack to be trimmed — it is the
shape the problem has.

**Next attack (lap 93+).**  With the `∀ i` door closed, the remaining narrowing levers are:
1. **Weaken `∀ K` to `∀ᶠ K`** (or `∀ K ≥ K₀`).  The chain uses `KN N = max 1 (depthSlow b N - v)`,
   which tends to `∞`, so every small `K` is used for only finitely many `N`; `depthAvg` at
   finitely many scales cannot affect a `Tendsto`.  Cheap, and it is a genuine weakening of the
   assumed family.  Do this FIRST.
2. **Weaken the coprime-multiplicativity quantifier**: `KPointNoExcWith` quantifies over ALL
   `g : Fin K → ℕ → ℂ`; the chain only ever feeds `g i = zOmegaNat (z i)` with `‖z i‖ = 1`.
   Define `KPointNoExcRoots` (the same statement restricted to unimodular-root powers) plus
   `kPointNoExcRoots_of_with`, and rethread.  This restricts the open `Prop` to the family it is
   actually used on — a real narrowing, and the rethread is local
   (`dyadic_window_bound_with` is the only consumer).
3. **Weaken the shift quantifier**: `hsh` ranges over all injective `Fin K → ℕ`; the chain only
   uses `hsh i = i+1`.  Same treatment, same single consumer.
4. Only then: the `Statement.lean` audit surface + ledger writeup (C3-T6).

## Lap 91 (2026-09-25, REVIEW) — the headline rests on ONE statement; now make that statement assume less

**Binding orders: `DIRECTION.md` → CURRENT DIRECTIVE.**  State at entry: branch `wip/c3-mrt`,
HEAD `b7d9f45`, `lake build` green (9257 jobs), the `C3Mrt*` chain sorry-free with zero `axiom`
declarations.  The only campaign `sorry` is `SwingC3Leaf.weylLambertTwist_holds` (disclosed).

**Crux advance landed this lap (lap 90).**  `KPointThresholdSlow b Q P (cKgeom c₀ θ b)` is no
longer a hypothesis — it is a THEOREM for every `0 < θ < 1` (`kPointThresholdSlow_of_geom`), with
the threshold constructed explicitly as `Athr K = 2^(2^⌈φ K⌉)`, `φ K = b^{θK}log(K+2+M₀)/(κc₀log2)`.
Lap 89's NEXT ① guessed this FAILS; it does not, and the refutation is now in the kernel, not in a
numerical table.  Consequently

    conjC3_of_geom_input : (∀ b ≥ 3, ∀ K, KPointNoExcWith (cKgeom c₀ θ b) (CstKdeg m) K) → ConjC3

with NO other hypothesis.  Where `θ < 1` is spent, twice and symmetrically:
* saving side — `b^{-θD_N}·log log a_N ≍ u^{1-θ}(log u)^{-θ}` must beat `log CstKdeg = O(log u)^m`;
* threshold side — `log log Athr(D_N) ≍ (u log u)^θ log log u` must fit inside `log log a_N ≍ u log 2`.
Both are the SAME `u^{1-θ}` margin.  That symmetry is the structural reason `θ = 1` is this
route's real boundary (lap 89), and it is now visible on both sides of the ledger.

**Next attack (lap 92+) — narrow what `KPointNoExcWith` ASSUMES.**  The input is 🔴 and will stay
🔴 (TT: triple correlations "not within current technology"); the remaining honest work is to make
the assumed `Prop` as weak as possible, and to make its shape auditable.

1. `depthRoot_ne_one_of_not_dvd_all {b} (hb : 0 < b) {h'} (hnd : ¬ (b:ℤ) ∣ h') (i : ℕ) :
   depthRoot b h' i ≠ 1`.  Proof: copy `depthRoot_ne_one_of_not_dvd` with `pow_one` replaced by
   `b ∣ b^{i+1}`; `ee_eq_one_iff_int` gives `h' = M·b^{i+1}`, contradicting `¬ b ∣ h'`.
2. `KPointNoExcAllWith cK CstK K` — `KPointNoExcWith` with `(∃ i, TTNonPretentious (g i))`
   weakened to `(∀ i, TTNonPretentious (g i))`.  Strictly less is assumed; ① shows the C3 consumer
   can still discharge it, because every factor it feeds in is `zOmegaNat (depthRoot b h' i)` with
   `depthRoot b h' i ≠ 1`, and `ttNonPretentious_zOmegaNat` is unconditional (lap 83).
   Add `kPointNoExcAllWith_of_with : KPointNoExcWith cK CstK K → KPointNoExcAllWith cK CstK K`
   (take `i = 0`) so no existing consumer is disturbed.
3. Rethread: `dyadic_window_bound_K` currently passes `⟨⟨0, hK⟩, hnp …⟩` at
   `C3MrtKPointNoExc.lean:133` — that is the ONLY place the `∃ i` is used, so the rethread is
   local.  Its `_with` twin in `C3MrtUnifK` (`dyadic_window_bound_with`) is the same pattern.
   Then `depthAvg_gen_tendsto_of_geom_slow` must carry `hnp` for every `i` (its current
   hypothesis names only `depthRoot b hh 0`), and `depthDiagonalSlow_of_geom` supplies it via ①.
   Headline: `weylLambertTwist_of_geom_input_all`, `conjC3_of_geom_input_all`.
4. `kPointNoExcWith_mono {cK cK' CstK CstK'} (hc : ∀ K, cK' K ≤ cK K) (hC : ∀ K, CstK K ≤ CstK' K)
   (hc0 : ∀ K, 0 < cK' K) : KPointNoExcWith cK CstK K → KPointNoExcWith cK' CstK' K`.  Both the
   hypotheses (`W ≤ L^{cK K}`, `hsh i ≤ L^{cK K}`) and the conclusion (`≤ CstK K·L^{-cK K}`) move
   the right way when `cK` shrinks, because `L ≥ 1`.  Consequence to record in the ledger: the
   geometric profile is NOT an extra assumption beyond `∀ K, KPointNaturalCorrelationNoExc K` —
   it is precisely the statement that the per-`K` constants that statement already produces
   existentially degrade no faster than `c_K ≳ c₀ b^{-θK}`, `Cst_K ≲ exp((K+1)^m)`.
5. Only after 1–4: consider whether `∀ K` can be weakened to `∀ K ≥ 2` (the chain uses
   `KN N = max 1 (depthSlow b N - v) → ∞`, so all small `K` are used only for finitely many `N`;
   a `∀ᶠ K` form may be extractable via an eventual-`N` argument).

**Trigger status this lap.**  C3-T1 NOT fired (lap 83 discharged the archimedean hypothesis
outright).  C3-T4 **SERVED** — the diagonal does close from an explicitly-uniform input, and with
the threshold discharged; retired.  C3-T5 satisfied by lap 90 (the headline rests on strictly less:
the threshold hypothesis is gone).  New **C3-T6**: six laps to narrow `KPointNoExcWith` further or
declare the reduction FINAL and write the audit surface + ledger.

**Repetition check (last 3 laps).**  88 → `θ < 1/2` from a degrading input; 89 → `θ < 1` by slowing
the schedule; 90 → the threshold discharged.  No repetition: each lap removed a different
hypothesis, and each is a strictly-less statement about the same headline.  No defect was
re-derived; lap 90 CORRECTED lap 89's mis-estimate of `log log a_N` rather than re-deriving it.

**Crux-neglect check.**  All three laps hit the headline chain itself, none hit side-leaves.  The
one thing NOT yet attacked is the open input's own content — and per the source that is generational,
so the honest attack is the hypothesis-narrowing above, not a proof attempt.

## Lap 88 (2026-09-25) — the crux is a theorem on the K-point input

**Advance on the crux.**  `weylLambertTwist_of_degrading` / `weylLambertTwist_of_geom`: the C3 crux
now follows from `KPointNoExcWith` with EXPLICIT degrading constants (polynomial `c₀/(K+1)^m` or
geometric `c₀ b^{-θK}`, `θ < 1/2`) plus threshold data — the schedule comparison `hgrow` is
DISCHARGED (`hgrow_of_schedule_le`), and both degenerate twist levels are closed
(`depthAvg_zero_tendsto`, `depthAvg_dvd_tendsto_of_primitive`).  See
`HANDOFF-c3mrt-2026-09-25-lap88.md`.

**Next attack.**  `θ < 1/2` is an artefact of `b^{depthLL b N} ≍ (u_N+1)²` while the mean-phase
discard needs only `b^{D_N} ≫ u_N`.  A slower schedule with `b^{D_N} ≍ u log u` should admit
`θ < 1`.  Then: pin the `K`-dependence of a `K`-fold Pilatte decoupling (TT Thm 3.3, `V^{-0.49J'}`).

# PENDING WORK

## Lap 90 (2026-09-25) — the threshold data is PROVABLE, not assumable (in flight)

**Correction to the lap-89 handoff.**  Its NEXT ① guessed `KPointThresholdOKWith` FAILS for the
geometric profile.  That guess was wrong: it estimated the available budget `log log a_N` as
`log u_N` when in fact `u_N = log₂log₂N` gives `2^{u_N} ≍ log₂ N`, so `log log a_N ≍ u_N·log 2`.
The demand is `log log Athr(D_N) ≳ b^{θD_N} log D_N ≍ (u log u)^θ log log u`, and for `θ < 1`
that is `o(u)`.  Numerically confirmed (θ=0.9, b=3): ratio to `u` is 74 at `u=10⁴`, 9.4 at `10²⁰`,
0.003 at `10⁶⁰` — it holds, just slowly.  So the threshold is a THEOREM to prove, and it is the
last assumed piece besides the `K`-point input itself.

**Landed this lap.**  `KPointThresholdSlow b Q P cK` — the threshold demanded only up to the slow
schedule's levels (`K ≤ depthSlow b N`), which is all `depthDiagonalSlow_of_geom` ever uses;
`kPointThresholdSlow_of_with` bridges from the `depthLL` version so nothing is lost;
`depthDiagonalSlow_of_geom` / `weylLambertTwist_of_geom_slow` / `conjC3_of_geom_slow` rewired to
the weaker hypothesis, with `weylLambertTwist_of_geom_slow_of_with` recovering the lap-89 form.
This matters beyond bookkeeping: at `θ > 1/2` the `depthLL` demand `b^{θ·2log_b u} ≍ u^{2θ}` does
exceed the `u` budget, so the slow threshold is the only satisfiable one in the widened range.

**Next attack — construct `Athr` and prove `kPointThresholdSlow_of_geom`.**  Plan, all pieces
checked against existing lemmas:

    φ K    := (b:ℝ)^(θ*K) * log(K+2+M₀) / (κ*c₀*log 2)     -- monotone in K
    Athr K := 2 ^ (2 ^ Nat.ceil (φ K))                      -- so 2·log(Athr K) ≥ 2^⌈φ K⌉

* clause (ii) `max(max 2 (K+1), M₀) ≤ (2 log Athr K)^(κ·cKgeom c₀ θ b K)`: with
  `e_K = κc₀b^{-θK}`, `(2^{g})^{e_K} = exp(g·e_K·log 2) ≥ exp(log(K+2+M₀))` exactly when
  `g ≥ φ K`, which `Nat.le_ceil` gives.  Needs `T_K ≤ K+2+M₀` (trivial) and
  `Real.rpow_le_rpow` to pass from `2^g ≤ 2 log Athr K`.
* clause (iii): `Athr` monotone (⌈·⌉ of monotone), so it suffices that
  `Athr (depthSlow b N) ≤ N/2^{u_N}`.  Reduce via `⌈φ(D_N)⌉ ≤ u_N - 1`, then
  `2^{2^{u-1}} ≤ 2^{(log₂N)/2} ≤ √N ≤ N/2^{u_N}` using `2^{u} ≤ log₂ N` (`two_pow_llLevel_le`)
  and `le_sq_cut`.
* `⌈φ(D_N)⌉ ≤ u_N - 1` is the one analytic step.  Feed `pow_depthSlow_le_log`
  (`b^{D_N} ≤ b(u+1)(2+2t)`) and `depthLL_succ_le_log` (`D_N+1 ≤ 2+3t`), `t = log(u+1)`, then
  with `(2+2t)^θ ≤ 2+3t` and `log(4+3t+M₀) ≤ (M₀+4)(2+3t)` reduce to
  `C(2+3t)^2 + 3 ≤ exp((1-θ)t)`, which is `tendsto_exp_div_polyPow (1-θ) 2` — already in
  `C3MrtUnifK`.  Same `u^{1-θ}` margin as the saving side, which is the right consistency check.



## Review — lap 87 (2026-09-25): the budget layer is VACUOUS; the obligation is the DIAGONAL

Binding orders: `DIRECTION.md` → CURRENT DIRECTIVE.  State at entry: branch `wip/c3-mrt`,
HEAD `990197c`, `lake build NormalNumbers.C3MrtQuantKPoint` green (9004 jobs), the whole
`C3Mrt*` chain (45 files) sorry-free with **zero** `axiom` declarations.

### F1 — every budget already forces the diagonal (route-decisive)

`QuantDepthElliottGen b` (`C3MrtBudget.lean:57`) asks for `C η` with
`‖depthAvg b P Q j h D N‖ ≤ C D · η N` for ALL `D`, plus `C(depthLL b N)·η(N) → 0`.
Instantiate the bound at `D = depthLL b N`:

    C(depthLL b N)·η(N)  ≥  ‖depthAvg b P Q j h (depthLL b N) N‖ .

So the hypothesis is *at least as strong as* the diagonal limit
`Tendsto (fun N => depthAvg b P Q j h (depthLL b N) N) atTop (𝓝 0)`, which is exactly what
`weylLambertTwist_of_depthElliottLL` (`C3MrtSchedule.lean:98`) consumes.  Freeing the budget
`C` therefore buys **nothing**: `budget_absorb`, `budget_absorb_of_tIdx`,
`pow_self_sq_le_exp_cube` and the `sup_D` assembly planned in HANDOFF lap 86 NEXT ③ are all
bookkeeping around a `Prop` that is no weaker than the target.  → Lean it as
`quantDepthElliottGen_forces_diagonal`, and target `DepthElliottLL` directly from now on.

### F2 — fixed-`K` limits cannot reach the diagonal; the input needs explicit `K`-uniformity

Lap 85 gives, for each `K`, `depthAvg_K_tendsto_of_noExc : Tendsto (fun N => depthAvg … K N)`.
A family of sequences each tending to `0` has **no** diagonal limit along a growing index
without uniformity, and `KPointNaturalCorrelationNoExc K` (`C3MrtKPointNoExc.lean:37`) hides
its constants behind a per-`K` `∃ c Cst` with no control on their degradation.  So lap 85 is
the *end* of that layer, not a step toward the diagonal.

The arithmetic of what uniformity is actually needed (worked out this lap, to be Lean'd):
`dyadic_window_bound_K` yields the per-scale `Φ_K(a) ≍ Cst_K (2 log a)^{-κ c_K}/M`; the
halving stack (`class_sum_le_of_window`, cut at `k₀ ≍ log log Y`) yields
`‖class sum‖/Y ≲ Cst_K (log Y)^{-κ c_K} + 1/log Y`; so

    B(K, N)  ≍  Cst_K (log N)^{-κ c_K} + 1/log N .

The diagonal needs `B(depthLL b N, N) → 0`, i.e. `Cst_{D_N}(log N)^{-κ c_{D_N}} → 0` along
`D_N ≍ log_b log log N` (use `pow_depthLL_le : b^{D_N} ≤ b·llProxy N²`).  Sufficient profiles:
* `c_K = c₀·γ^K` with `γ > b^{-1/2}` — then `c_{D_N} ≳ (log log N)^{-θ}`, `θ = 2log(1/γ)/log b
  < 1`, and `(log N)^{-κ c_{D_N}} = exp(-κc₀(log log N)^{1-θ}) → 0`.  (Note `γ = 1/2` is NOT
  enough at `b = 3`: `θ = 2log2/log3 ≈ 1.26 > 1`.  The exponent budget is genuinely tight.)
* `c_K = c₀/K^m` — comfortable: `(log N)^{-κc₀/(log_b log log N)^m} → 0` for every `m`.
* `Cst_K ≤ exp(K^m)` is always affordable: `Cst_{D_N} = exp(O((log log log N)^m))`.
Also needs the `N₀(K)` threshold of `dyadic_window_bound_K` made explicit — it currently
arises from `(2 log N)^{κ c} ≥ max 2 (K+1)`, which along `K = D_N` holds once
`exp(κ c_{D_N} log log N) ≥ D_N + 1`, true for both profiles above.

### F3 — ledger fidelity: the `K = 2` input is 🔴, not "published"

`KPointNaturalCorrelationNoExc 2` = `TwoPointNaturalCorrelationNoExc` is TT Thm 3.1(ii) with
the exceptional set of scales **deleted**.  TT say in print this is out of reach, and
`exceptional_set_can_pin_a_scale` (`C3MrtNoExc.lean:58`, lap 80) proves it is not derivable
from the faithful statement `TwoPointNaturalCorrelation` (`C3MrtTTThm31.lean:107`).  Any doc
calling the `D = 2` rung "published" is wrong.  Ledger updated in `STATUS.md`.

Why E cannot be dodged at the top level either (checked this lap, do not re-derive):
`ConjC3` wants *positive lower density* of every word, i.e. `count(N) ≥ cN` for ALL `N`;
`count` is monotone, so good scales would have to be **bounded-ratio dense**.  But `E ⊂ [√X,X]`
with `∫_E dt/t ≤ Cst L^{-c} log X` and `L ≍ (log X)^κ` can swallow a whole dyadic block as soon
as `Cst(log X)^{1-κc} ≥ log 2`, i.e. always, for large `X`.  Varying `X ∈ [N, N²]` does not
help: Fubini only bounds the doubly-bad set's *log*-measure by `Cst(log A)^{1-κc} ≫ 1`.  This
is the same wall as *log-Chowla ⇏ Chowla*; TT's own Thm 1.3 (irrationality) escapes it because
irrationality needs only *infinitely many* good scales.

### Trigger status

C3-T1 (ζ^ω fails a TT hypothesis): NOT fired — lap 83 discharged the hypothesis outright.
C3-T2 (`D = 2` rung within 6 laps): SERVED — the rung is a theorem (lap 82/84), though on the
🔴 NoExc input.  Retired.
C3-T3 (`K ≥ 3` undisclosed): NOT fired — lap 85's `K`-point layer discloses it in the module
docstring as the generational item.  Retired, superseded by C3-T5.
New: **C3-T4** (`depthElliottLL_of_unif` within 8 laps) and **C3-T5** (every lap's advance must
be statable as "the diagonal now rests on strictly less").

### Attack order (this is what the grind laps execute)

1. `quantDepthElliottGen_forces_diagonal`  ← cheap, retires the budget layer.
2. `KPointNoExcWith (cK CstK : ℕ → ℝ) (K : ℕ)` + `kPointNoExc_of_with`.
3. `progression_avg_le_of_window` — quantitative twin of `progression_avg_tendsto_of_window`.
4. `dyadic_window_bound_with`, then `depthAvg_le_with` (explicit `B cK CstK K N`, explicit `N₀`).
5. `depthElliottLL_of_unif` + a concrete sufficient profile ⇒ `weylLambertTwist_of_unif`.

## Still refuted — DO NOT RETRY (cumulative)

* Removing `E` from TT Thm 3.1 at the `Prop` level (`exceptional_set_can_pin_a_scale`, lap 80),
  including by varying `X` at a prescribed scale, and including via bounded-ratio density of
  good scales at the `ConjC3` end (lap 87, F3).
* A two-point-only proof of the leaf (lap 60, finding R3).
* Sharpening `prod_le_lcm_mul_pow` / the `K^{K²}` exchange constant (laps 40, 60) — and now
  the whole budget layer it lives in (lap 87, F1).
* `TwistedPrimeSumSaving`.
* Lap 80's list (below, in the older sections).

## Reflection — 2026-09-25 (deep-reflection lap 60) — ROUTE VERDICT: **ESCALATE**, re-anchor on Tao–Teräväinen Thm 3.1

Full re-cost in `ROUTE-ESCALATION-2026-09-25-c3mrt.md`.  Binding orders in `DIRECTION.md` →
CURRENT DIRECTIVE.  Summary:

### The destination is unchanged and still worth it

`ConjC3` = *every base-`b` word occurs with positive lower density in the expansion of*
`primeLambertAtBase b = ∑_n ω(n)/bⁿ`, `b ≥ 3`.  That constant is **verbatim** the constant of
Tao–Teräväinen arXiv 2512.01739 Theorem 1.3 (Erdős #69), which they prove **irrational** for
`b = 2` and remark holds for every integer base.  So the repo is formalising the next question
along a live, top-of-the-field line, on a constant whose first unconditional result is 9 months
old.  The ratified success criterion remains the EQUIVALENCE, not a proof; that is honest and
unchanged.

The realistic endpoint, stated plainly: **`ConjC3` will not be proved.**  The Weyl formulation is
intrinsically an *unbounded*-point correlation (re-derived independently this lap: truncating
`∑_k ω(n+k) b^{-k}` at depth `K` leaves a residual of standard deviation `≍ b^{-K}√(log log N)`,
so `K → ∞` is forced, and no reformulation avoids it — richness of a *fixed* word length still
needs the Weyl sum at a fixed frequency `h ≠ 0`, which sees every digit).  TT state in print that
even **three**-point correlations are "not within current technology".  The valuable endpoint is a
ledger that is (i) complete, (ii) anchored on the strongest *published* input, and (iii) honest
about which residue is generational.

### What was wrong with the route (not the destination)

The whole `D ≥ 2` machinery is built against `Erdos67b.NonasymptoticLogElliott`, whose
multiplicativity hypothesis `IsMultiplicativeOnPositiveInt` has **no coprimality clause** —
it is *complete* multiplicativity.  `ζ^ω` fails it, so lap 4 built the `z^ω = z^Ω ⋆ g` powerful-
divisor bridge, and everything expensive in the campaign descends from that one artificial
hypothesis: the `D`-fold tuple sums, `prod_le_lcm_mul_pow`'s `K^{K²}`, the lap-40 budget repair,
and the headline "beat every power of `log log N` by a quasi-polynomial margin" decay class.
Elliott's conjecture, and Tao's Theorem 1.3 that the dependency is formalising, are stated for
merely **multiplicative** functions.  With the literature's own hypothesis class none of that
exists.

### KEEP doing

* **The `Prop`-level ledger discipline.**  Zero `axiom` declarations, every debt carried as an
  explicit hypothesis, every headline trust-triple clean.  This is why the re-anchoring is cheap:
  the obligations are named objects, so swapping the anchor is a proof-engineering task.
* **The archimedean certificate** (`C3MrtArchimedean`, `C3MrtNonPretentious`, laps 18–21).  It
  transfers to the new anchor **verbatim**: the pretentious distance depends on `g` only through
  its values at primes, and `ζ^ω`, `ζ^Ω` agree at primes.
* **The periodicity insights of laps 53–54** (`norm_sum_periodic_le`): the twist `e(jn/Q)` and the
  small primes `ω_{≤P}` are one and the same obstruction, stripped by one decomposition mod
  `M₀ = Q · primorial P`.  TT Thm 3.1 has the progression `1_{n ≡ b (W)}`, `W ≤ (log X)^c`, built
  in — `M₀` is fixed before `N`, so it fits with room to spare.
* Committing every green build; nothing is ever deleted.

### STOP doing

* **Building on `Erdos67b.NonasymptoticLogElliott` as the main line.**  Keep the K-fold stack —
  it is sorry-free and is the correct route *for completely multiplicative functions* — but it is
  no longer the campaign's spine.
* **Quoting the `exp(−C(log log log N)⁴)` decay class as "the distance to the literature".**  It
  is the distance to the literature *through the powerful-divisor bridge*.  Restate it as such.
* **Sharpening `prod_le_lcm_mul_pow`.**  Already recorded as not worth laps; now it is not worth
  anything, because the constant it bounds should not be in the ledger at all.

### R1–R3: three findings to carry forward

**R1 (compiler-grounded).**  `IsMultiplicativeOnPositiveInt` = complete multiplicativity.  Checked
at `.lake/packages/lean-proofs-latest/src/latest/ErdosProblems/Erdos67b/LogElliott.lean:329`.  The
repo's own `KPointLogElliott` inherits it (`C3MrtKPoint.lean:63`), which is why
`kPointLogElliott_two_iff` can be *proved*.  Any lap tempted to say "`KPointLogElliott` only asks
multiplicativity" should re-read that definition.

**R2 (source-grounded).**  TT Theorem 3.1 is strictly better than the dependency's `Prop` on four
axes simultaneously — merely multiplicative, natural (dyadic) averaging, `L^{-c}` saving with
`L ≤ log X`, and progressions `W ≤ L^c` built in — at the price of an exceptional set of scales of
logarithmic density `≪ L^{-c}`.  For `ζ^ω` one may take `L = (log X)^{c'}`, which lands **inside**
`budget_absorb`'s hypothesis class `η N ≤ A (log N)^{-a}`.

**R3 (refuted — do not re-chase).**  A two-point-only proof of the leaf along TT §5's lines.
Their reduction works because the alternating sum over `ε ∈ {0,1}^K` makes each prime-indexed
`X_p` mean-zero **and** of variance `O(2^{-K}/p)`, so the large-prime tail has total variance
`O(2^{-K} log log N) = o(1)` and a second moment (hence pairwise correlations) suffices.  That
shrinkage is bought with the rationality hypothesis (the dilation identity
`ω(n+ph) = ω(n/p + h) + 1 − 1_{p²|n+ph}` at `2^K` distinct primes `p_ε`); an unconditional Weyl
bound has no such identity.  Van der Corput does not substitute — differencing makes `X_p`
mean-zero but doubles the point count and leaves `Var(X_p) ≍ c_h/p`, so the tail variance stays
`≍ log log N`.  A direct moment expansion of `e(h ∑_{p>Y} w_p)` against the small-prime period
fails at the level-of-distribution barrier: the per-progression error costs
`∑_{p>Y} p · E[w_p] ≍ N/log N`.

### The single highest-value next target

**`src/NormalNumbers/C3MrtMultElliott.lean` — the merely-multiplicative anchor and the
bridge-free `K`-point correlation form.**  In order:

1. `def IsCoprimeMultiplicativeInt (g : ℤ → ℂ)` — `g 1 = 1` and `g(mn) = g m * g n` for
   coprime positive `m, n`.  This is Elliott's / Tao's actual hypothesis class.
2. `def KPointLogElliottMult (K : ℕ) : Prop` — `KPointLogElliott` verbatim with
   `IsCoprimeMultiplicativeInt` in place of `Erdos67b.IsMultiplicativeOnPositiveInt`.
3. `kPointLogElliott_of_mult : KPointLogElliottMult K → KPointLogElliott K` — nothing is
   weakened; the new `Prop` is *stronger*, and is the literature's own statement.
4. `zOmegaInt z : ℤ → ℂ`, `z ^ ω(n)`; `isCoprimeMultiplicativeInt_zOmegaInt`,
   `norm_zOmegaInt_le_one`, and the transfer of `nonPretentious_zOm` (values at primes only).
5. **The decisive lemma** `class_sum_eq_kPointLogCorrelation`: the class-restricted `K`-point sum
   `∑_{n ≡ r (M₀)} w(n) ∏_{i<K} z_i^{ω(n+i+1)}` *is* `kPointLogCorrelation` of `zOmegaInt` along
   the affine forms `a i = M₀`, `b i = r + i + 1`, whose pairwise determinant is `M₀(j−i) ≠ 0`
   (`NondegenerateForms` is immediate).  **No divisors, no truncation, no `K^{K²}`.**
6. Then transcribe `multi_correlation_of_uniform_rung_prog`'s ε-chase against step 5 to obtain
   `progression_log_rung_class_mult` — the same conclusion as lap 59's
   `progression_log_rung_class`, on the *merely multiplicative* anchor, with **no** budget.
7. Only then: `TwoPointNaturalCorrelation`, TT Thm 3.1(ii) stated faithfully (natural dyadic
   averaging, `L^{-c}`, `W ≤ L^c`, exceptional set of scales), and the `D = 2` natural-density
   rung from it.

**Progress (same lap, two green commits).**  Steps 1–5 are DONE
(`src/NormalNumbers/C3MrtMultElliott.lean`, `class_window_bound_of_mult` trust-triple clean), and
the rung is DONE (`src/NormalNumbers/C3MrtMultRung.lean`,
**`rung_class_of_named_inputs_mult`**): on `KPointLogElliottMult K` +
`TwistedPrimeSumSavingAllLevels` alone,

    ∃ A₀ ≥ 2, ∀ A ≥ A₀, ∃ i₀, ∀ m ≥ i₀,
      ‖∑_{j ∈ Ioc 0 (A^m)} (1/j) ∏_{i<K} z_i^{ω(M₀·j + r+i+1)}‖
        ≤ (1 + log(A^{i₀})) + m·(ε log A).

That single statement replaces BOTH `rung_multi_of_named_inputs` AND `rung_multi_uniform_prog`:
with no divisor tuples there is nothing to truncate and no `exists_common_threshold` to run, so
the single `A` and the single `i₀` come out directly.

**REMAINING — the one brick between the new anchor and lap 59's conclusion.**
`progression_log_rung_class_mult` needs, from `rung_class_of_named_inputs_mult`:

1. *Reindex.*  `n ≡ r (mod M₀)`, `n < N` ↔ `n = M₀·j + r`, `j < (N−r+M₀−1)/M₀`; then
   `n + i + 1 = M₀·j + (r+i+1)`, which is exactly the rung's argument.  `class_sum_reindex`
   (lap 53) does this bookkeeping already.
2. *The weight bridge* (brick 4b, unchanged in shape and now the ONLY bookkeeping item).  The
   rung carries `harmonicWeight j = 1/j`; the target carries `harmW n = (M₀ j + r + 1)⁻¹`.
   `(M₀ j + r + 1)⁻¹ − M₀⁻¹ j⁻¹ = (M₀ − r − 1)/(M₀ j (M₀ j + r + 1))`, absolutely
   `≤ (M₀ + r)/(M₀ j²)`, and `sum_inv_sq_le` (`C3MrtRungTwo:372`) is in the repo.  `ε ↦ ε M₀`
   absorbs the factor `M₀⁻¹`.
3. *Choose `m`.*  `m = Nat.log A ((N − r)/M₀)`, exactly as in
   `multi_correlation_of_uniform_rung_prog`'s `hrung` step, giving `m log A ≤ log N`.

Why this and not brick 4b: brick 4b perfects the *old* anchor.  Step 5 is the smallest
compiler-grounded probe that tests whether the re-cost of `ROUTE-ESCALATION-2026-09-25-c3mrt.md`
is right — if the forms really are nondegenerate and the correlation really is in
`kPointLogCorrelation`'s shape with no divisor expansion, then eight modules of machinery are
revealed as a hypothesis artefact, and trigger C3-T2 is on course.  If it fails, C3-T1 fires.

---

## 2026-09-25 (review lap 40) — C3/MRT: the budget is repaired; resume the `K`-fold assembly

**The defect this lap found and fixed.**  Lap 37's `prod_le_lcm_mul_pow` puts a factor `K^{K²}`
into the `K`-fold rung.  `QuantDepthElliott` (the `Prop` the whole reduction is stated against)
allows only a `b^{κD}` budget and asks `η` to beat every power of `llProxy ≍ log log N`.
**That cannot pay for `K^{K²}`**, and the lap-39 handoff's claim that it can is arithmetically
wrong:

    (log log N)^m = exp(m · log log log N) ,  writing v = log log log N ;
    D_N ≍ v , so D_N^{D_N²} = exp(Θ(v² log v)) ≫ exp(m v) for every fixed m.

So the `D ≥ 3` assembly was, until this lap, aimed at a `Prop` that could not receive it.

**The fix (`src/NormalNumbers/C3MrtBudget.lean`, sorry-free, trust triple).**

* `QuantDepthElliottGen b` — the budget is a free `C : ℕ → ℝ`; the decay clause becomes the
  JOINT vanishing `C(depthLL b N)·η(N) → 0`.
* `weylLambertTwist_of_quantDepthElliottGen` — the widened `Prop` still closes the crux.
* `quantDepthElliottGen_of_quantDepthElliott` — the old `Prop` implies the new one, so every
  existing ledger row and consumer survives verbatim; nothing was weakened.
* `budget_absorb` — **the route-decisive lemma**.  `C D ≤ exp(c(D+1)³)` together with
  `η N ≤ A(log N)^{-a}`, `a > 0`, gives the joint vanishing.  Mechanism, with
  `t = ⌊log₂(⌊log₂⌊log₂ N⌋⌋+1)⌋`: `D_N + 1 ≤ 2t+3` (`depthLL_le_triple_log`, uniform in `b ≥ 2`
  because `Nat.log b ≤ Nat.log 2`) while `log log N ≥ (2^t − 2)·log 2`
  (`log_log_ge_triple_log`).  Budget POLYNOMIAL in `t`, decay EXPONENTIAL in `t`.
* `pow_self_sq_le_exp_cube` (`K^{K²} ≤ exp(K³)`) and `kfold_budget_le_exp_cube`
  (`A₀·K^{K²}·b^{κK} ≤ exp((log A₀ + 1 + κ log b)(K+1)³)`) put lap 37's constant inside the cap.
* `weylLambertTwist_of_kfold_bound` — **the endpoint the `D ≥ 3` campaign now aims at**:
  a bound `‖depthAvg b P Q j h D N‖ ≤ A₀·D^{D²}·b^{κD}·η N` with `η N ≤ A(log N)^{-a}` closes
  the crux outright.

**What decay the route actually needs — the sharp answer (`budget_absorb_of_tIdx`).**
Write `t_N = ⌊log₂(⌊log₂⌊log₂ N⌋⌋+1)⌋ ≍ log log log N`.  The schedule's depth is LINEAR in `t`
(`D_N ≤ 2t+2`) and `log log N` is EXPONENTIAL in `t` (`≥ (2^t−2)log 2`).  Against a budget
`exp(c(D+1)³)` the requirement is therefore exactly

    η N ≤ exp(−t_N⁴)  ,  i.e.  η N ≤ exp(−C(log log log N)⁴) .

That is **strictly stronger than every fixed power of `log log N`** — since
`(log log N)^{-m} = exp(−m·t_N·log 2 + O(1))` is only LINEAR in `t_N` — but only
*quasi-polynomially* so.  It is far weaker than the `(log N)^{-a}` that `budget_absorb`
assumes.  So the honest ledger entry for the `D ≥ 3` route is:

> the `K`-point log-Elliott saving must beat every power of `log log N`, by a
> quasi-polynomial margin in `log log log N`.

This is the sharpest characterisation the campaign has produced of the gap to the literature:
quantitative log-Chowla/Elliott results of `(log log X)^{-c}` shape fall **just** short, by
that quasi-polynomial margin, and nothing weaker than that margin is needed.  The `(log N)^{-a}`
decay of `budget_absorb` is what the `D = 1` rung actually has (`C3MrtRungOne`,
Selberg–Delange) and what `probes/swingc3_weyl_lambert_twist.py` measures for the leaf itself
(`a ≈ 1.3–3.7`, never plateauing) — so the route has room to spare if the rate can be pushed
that far.

**The constant is `exp(Θ(K²))` intrinsically, not an artefact of lap 37's crude bound.**
`gcd(d_i,d_j)` divides `j−i` and is itself POWERFUL (both `d_i,d_j` are, so every exponent in
the gcd is `≥ 2`).  Splitting the tuple sum by the pairwise-gcd pattern replaces lap 37's
`∏_{i<j}(j−i) ≈ K^{K²/2}` by `∏_{i<j} ∑_{g powerful, g ∣ j−i} 1/g ≤ ∏_p(1+2/p²)^{K²/2}`, i.e.
`exp(Θ(K²))` — better, but still exponential in `K²`, because a positive proportion of the
`K²/2` differences `j−i` are divisible by a square.  Improving lap 37's exponent is therefore
worth at most a constant in the exponent and does NOT change the required decay class.  (Not
formalised; recorded as the reason not to spend laps sharpening `prod_le_lcm_mul_pow`.)

### Attack order from here

1. ~~`inner_sum_linear_forms` analogue at `K` points.~~  **DONE lap 41** —
   `src/NormalNumbers/C3MrtMultiLinear.lean` (sorry-free, trust triple).
   `inner_sum_multi_forms`: for any tuple whose joint progression is nonempty, the inner sum
   equals `∑_j F(Lj+a)·∏_i z_i^{Ω((L/d_i)j + (a+i+1)/d_i)}` over `{j : Lj+a < N}`, with
   `a = n₀ mod L`, `L = Finset.univ.lcm d`.  **No coprimality anywhere** — `joint_class_multi`
   supplies the class, `multi_forms_det` the nondegeneracy.  `inner_sum_multi_empty` covers the
   tuples with no solution.  Helpers: `univLcm_pos`, `shift_div_eq_linear_multi`,
   `joint_base_mod`.  `filter_linear_lt_eq_range` applies to the `j`-index set verbatim with
   `L` for `d·e`.
2. `multi_truncation_bound` — **its quantitative heart is DONE (lap 42)**;
   `src/NormalNumbers/C3MrtMultiMass.lean` (sorry-free, trust triple).
   `joint_multi_harmonic_mass`: for `S ⊆ range M` carrying the consecutive block
   `d_s ∣ n + m + s + 1` (`s < K`),

       ∑_{n∈S} ‖F n‖ ≤ (m+1)/d_0 + (1 + log M)·K^{K²} / ∏_{s<K} d_s .

   **The trap this avoids (record it).**  Bounding the joint mass by ONE congruence, `≍
   (1+log N)/d_m`, makes the stage-`m` truncation error carry `∏_{j>m} sqfWPartial z_j Y`,
   which GROWS like `Y^{(K−m−1)/2}` while `bridgeTail z_m Y` only decays like `Y^{−1/2}`; for
   `K − m ≥ 3` the product DIVERGES and truncation is worthless.  Using the full joint modulus
   (`joint_class_range` + `class_harmonic_mass` + lap 37's `prod_le_lcm_mul_pow`) puts the
   `log`-carrying term against the CONVERGENT `∏_j sqfWMass z_j` instead, and leaves the head
   `(a+1)⁻¹ ≤ (m+1)/d_0` free of `log N` — an `N`-independent constant the `1/log N`
   normalisation kills.  This is the `K`-fold form of the lap-24 trap.
   `joint_class_range` also **pays part of lap 38's indexing debt**: it is the `range K` /
   `ℕ → ℕ` half of `joint_class_multi`, the convention `prod_le_lcm_mul_pow` and
   `prod_div_lcm_le` use.
   **What remains of step 2**: the telescope itself — induct on `K` peeling the LAST shift
   (as `sum_pow_omega_multi_eq` does), feeding `joint_multi_harmonic_mass` as
   `offset_truncation_bound_of_mass`'s `hmass` at each stage, giving

       Err ≤ ∑_{m<K} [(m+1)·∏_{j>m} sqfWPartial z_j Y
                       + (1+log N)·K^{K²}·∏_{j>m} sqfWMass z_j] · bridgeTail z_m Y .
3. Pay lap 38's indexing debt: standardise on `Fin K` + `Finset.univ.lcm` (the convention
   `joint_class_multi` / `nondegenerateForms_multi` already use) and restate
   `prod_le_lcm_mul_pow` / `prod_div_lcm_le` over `Finset.univ` via the `ℕ → ℕ` extension.
4. Per-tuple rung bound + ε-chase, mirroring laps 29–33, landing in
   `weylLambertTwist_of_kfold_bound`'s shape.
5. The uniformity-in-`D` question is now the ONLY remaining structural gap besides
   log→natural density.  Do not restate `QuantDepthElliott`; it is superseded in practice by
   `QuantDepthElliottGen` and kept for the ledger.

### Refuted / settled — do not retry

* The lap-39 estimate "`K^{K²}` is `(log log N)^{o(1)}`" — **false**, corrected above.
* A `(log log N)^{-c}` decay does **not** absorb `K^{K²}` at `D_N ≍ log log log N` (computed
  above).  Only a power of `log N` does.
* Everything in the lap-39 session wrap's "Still refuted" list.

---


## 2026-09-25 (review lap 18) — C3/MRT: the archimedean non-pretentiousness certificate

**Where the crux stands.**  `weylLambertTwist_holds` (`SwingC3Leaf.lean`) is the one `sorry`
carrying `ConjC3`.  Laps 1–17 reduced it, axiom-clean, to `QuantDepthElliott`, and reduced the
log-averaged `D = 2` rung to `Erdos67b.NonasymptoticLogElliott` + non-pretentiousness of `ζ^Ω`
against every Dirichlet–Archimedean twist (`t = 0` done, lap 17).

**Review finding (2026-09-25): the exact shape of the archimedean obligation.**
Elliott's hypothesis is `A ≤ pretentiousDistSqToTwist (ζ₀^Ω) χ t X` for `q ≤ A`, `|t| ≤ A·X`,
with `A` a CONSTANT (not `≫ log log X`).  Writing `S = ∑_{p≤X} χ(p)p^{it}/p` and
`mass = ∑_{p≤X} 1/p`, the distance is exactly `mass − Re(z·S)`, hence `≥ mass − ‖S‖`:

* **Range 2 (`|t| ≥ T/log X`, `T` a constant chosen from `A`).**  Needs only the CONSTANT
  saving `‖S‖ ≤ log log X − A`.  This is `log|L(1+1/log X+it, χ)| ≤ log log X − A`, the
  Vinogradov–Korobov log-derivative bound; the dependency isolates the same input as
  `Erdos67b.PolynomialHeightPrimeCorrelationBound` ("expected proof: the log-derivative
  argument in the Vinogradov–Korobov zero-free region").  NAME IT, do not chase it.
* **Range 1 (`|t| ≤ T/log X`).**  Elementary and OURS.  `|t log p| ≤ T` for `p ≤ X`, so the
  resonance set `{p : ‖arg z − t log p‖_{2π} < ε}` meets only `O(T)` of the intervals
  `log p ∈ (arg z + 2πk ± ε)/t`; each has reciprocal mass `≤ log((θ+2πk+ε)/(θ+2πk−ε)) + 2·
  mertensBound` (bounded, `t` cancels), so the total resonance mass is an `X`-INDEPENDENT
  constant, while the class-`1 mod q` primes carry `(1/φ(q))log log X − C_q → ∞`.

**Refuted this lap (do not retry).**  Extending the resonance-interval argument past
`|t| ≈ (log X)^K`: the number of intervals is `|t|·log X/2π`, so the per-interval Mertens error
`2·mertensBound` alone contributes `≫ log log X`, and the trivial/Brun–Titchmarsh replacement
needs primes in intervals of length `p/|t|` — short-interval-hard.  Equally refuted: hoping the
crude `|ζ(1+it)| ≪ log t` suffices at `|t| ≍ X` (it gives `log log t ≍ log log X`, exactly
cancelling the main term).  A saving factor < 1 in the exponent (i.e. VK) is not optional.

**Attack order.**
1. ~~`C3MrtArchimedean.lean`: the bridge `dist ≥ mass − ‖S‖`; the resonance split.~~  DONE lap 18.
2. ~~Range 1 (the `O(T)`-window Mertens count).~~  DONE lap 19 —
   `range_one_mass_bound`.  **What remains of Range 1**: insert
   `G4.MertensAP.mertensRate_residueClass` at `a = 1` to turn the class mass into
   `c·log log X − C`, and state `range_one_certificate` in `∃ X₀, ∀ X ≥ X₀ … A ≤ dist` form.
   Index-set mismatch to watch: `sumInvPrimesIn` sums `N.primesBelow` (`< N`), `classPrimes`
   uses `primesUpTo` (`≤ X`); the inclusion is in the useful direction.
3. `TwistedPrimeSumSaving A` as the single named Range-2 Prop; assemble
   `nonPretentious_zOm`, then feed `initial_segment_bound_of_elliott`.
4. Then, and only then, the tuple sum over `d,e ≤ Y` (laps 8–13 supply every other piece).

---


## 2026-09-23 — **Theorem C′ is PROVED**; the multicutoff campaign is complete

`isNormal_subsetLambert_of_sqrtFreshMassZero` is sorry-free and
`[propext, Classical.choice, Quot.sound]`.  All three leaves closed this run: `termE5_tendsto`,
`schedule_admissible` (with the `LG` route correction), `termE4c_tendsto`.  `src/` holds only the
two pre-existing off-campaign `sorry`s.  See `HANDOFF-2026-09-23-theoremC-COMPLETE.md`.

### Open items, highest value first

1. **Audit surface for Theorem C′.**  A `Statement.lean`-style unwound statement of
   `SqrtFreshMassZero P`, `DivergentRecip P` and `IsNormal 4 (subsetLambert P 4)`, so the
   headline can be read without chasing definitions.  This repo gates every headline that way;
   Theorem C′ does not have one yet.  Model: the existing `G4WeightStatement`.
1b. **Astra §10, implication half: DONE 2026-09-23** —
   `src/NormalNumbers/PrimeModelGeometricMass.lean` (sorry-free, trust triple) defines
   `geomFreshMass P N = ∑_{j=1}^{J_N} 4^{−j} S_P(y_j, 2N)` (Astra (10.1) on the graded
   schedule) and proves `geomFreshMass_tendsto : SqrtFreshMassZero P → F_N → 0`, with the
   quantitative form `geomFreshMass_le : F_N ≤ 2(3 + 2 log₂ u_N)/u_N² + 2 S_P(⌊√(2N)⌋, 2N)`.
   The mechanism: the geometric weight absorbs the root-chain length, since `j ≤ 2^j` turns
   `4^{−j}(j + 2 + 2 log₂ u_N)` into `2^{−j}(3 + 2 log₂ u_N)`; the doubling step is the
   one-step chain `S_P(N,2N) ≤ S_P(⌊√(2N)⌋, 2N)` (`sqrt_two_mul_le` is unconditional).
   So C′'s hypothesis is *at least as strong* as §10's, i.e. §10 remains a genuine
   generalisation and nothing was lost by proving C′ first.  What is still open is the
   converse direction — the §10 *consumer* (normality from (10.1) alone) — which needs the
   schedule re-parametrised over a freely chosen `u : ℕ → ℕ` (`uG` currently reads `epsG`);
   that is the multi-lap re-parametrisation, still unauthorised.

1c. **Double-exponential block criterion: DONE 2026-09-23** —
   `src/NormalNumbers/PrimeModelSqrtFreshBlocks.lean` (sorry-free, trust triple).
   `dblBlockMass P n = S_P(2^{2^n}, 2^{2^{n+2}})`; `sqrtFreshMassZero_of_dblBlockMass` and
   `isNormal_subsetLambert_of_dblBlockMass`.  The point: in `t = log log x` coordinates the
   window `(√N, N]` has CONSTANT length `log 2`, so it always sits inside one block
   `(2^{2^n}, 2^{2^{n+2}}]` with `n = ⌊log₂⌊log₂⌊√N⌋⌋⌋ → ∞` (`sqrt_window_subset`, via
   `N < (⌊√N⌋+1)²`).  This is precisely the hypothesis Astra §10 verifies for its prime-burst
   example, so Theorem C′ already covers that example and §10 is not needed for it.
   **Upgraded the same day to an EQUIVALENCE** (`dblBlockMass_tendsto_iff`): the block
   `(2^{2^n}, 2^{2^{n+2}}]` is exactly TWO root-chain steps wide (`log M / log y = 4`, so
   `⌈log 4 / log 2⌉ = 2`), whence `dblBlockMass P n ≤ 2 ρ` by `recipSumIoc_le_rootChain`
   (`dblBlockMass_le_of_bound`).  So the double-exponential block mass vanishing is not a
   convenient sufficient condition but a *reformulation* of `SqrtFreshMassZero`.

1d. **Independent faithfulness cross-check: DONE 2026-09-23** —
   the ENGLISH statement of Theorem C′ (never our Lean) was handed to an independent
   auto-formalizer; its rendering is archived at
   `archive/findings/ARISTOTLE-2026-09-23-theoremC-prose-formalization.lean` (input:
   `…-prose-input.md`).  It differs from our audit surface in three places, all reconciled
   in `src/NormalNumbers/PrimeModelGradedCrossCheck.lean` (sorry-free, trust triple):
   (i) `Real.sqrt N < p` over `Icc 1 N` vs `Nat.sqrt N < p` over `Ioc (√N) N` — the index
   sets are EQUAL (`freshWindow_eq`; both say `N < p²`); (ii) `¬Summable` over the subtype
   `{p // p.Prime ∧ P p}` vs our indicator form (`divergentRecip_iff_subtype`);
   (iii) occurrence counting by start position `i < n` vs by suffixes of the first `n`
   digits — now a THEOREM, not a remark: `src/NormalNumbers/OccurrenceCountEquiv.lean`
   (sorry-free, trust triple) proves `countOccurrences ≤ occStart ≤ countOccurrences + |w|`
   and hence `tendsto_occStart_iff`, and
   `isNormal_subsetLambert_crossCheckForm_occStart` states the headline in the independent
   convention.  All three differences are now machine-checked equivalences.
   `isNormal_subsetLambert_crossCheckForm` derives our headline from the independently
   written hypotheses verbatim.  No faithfulness defect found.

2. **Astra §10 abstract consumer** `F_N = ∑_j 4^{−j} S_P(y_j, 2N) → 0 ⇒ normal`.  Strictly
   weaker than `SqrtFreshMassZero` and the same schedule; only the E1 leg
   (`termE1_tendsto`, which currently spends the root chain) needs re-running against `F_N`
   directly.  Everything else (`schedule_admissible`, E4a/E4b/E4c, E5, `tailOK_graded`) is
   hypothesis-free in `N` and reusable verbatim.
3. **Off-campaign, designated open** (do not touch without an override):
   `PrimeLambertOscillation.phaseOscillation`, `MahlerDriftOne.exists_prime_nonresidue`.

### Route findings worth keeping

* **The contracting site index is bounded** (`exists_site_re_nonpos_le`, lap G5c-e):
  `j₀ ≤ log₄|h|`, a constant for fixed `h` uniform in `N`.  This is what lets leg E5 collect its
  contraction at a *near-top* cutoff, hence lets `J_N` be tied to the full mass `S_P(N)`.
  Astra §8 uses `j₀` fixed tacitly.
* **The cut depth must be read off `y_{J−1}`** (lap G5c-l): the two dyadic-cut clauses pin `2^L`
  from both sides, and `yBotG` is too far below `y_{J−1}` on the mass branch of `JG`'s `min`.
* **The constant class count is arithmetically dead** (2026-09-22 review): `log R ≥ 128k log y_0`
  forces a transfer term `≍ ρ_N·L₄N`, and the ungraded E4a diverges like `J e^{20}`.

## 2026-09-22 (lap G5c-e) — ROUTE FINDING: the contracting site index is bounded

`src/NormalNumbers/PrimeModelSiteIndexBound.lean` (NEW, sorry-free, axiom-clean) proves

    exists_site_re_nonpos_le : NontrivialWindow k h →
      ∃ j : Fin k, (j : ℕ) ≤ Nat.log 4 h.natAbs ∧ (zPhase h k j).re ≤ 0

i.e. the site `j₀` whose phase contracts (Theorem A leg E5) has an index bounded by `log₄|h|`
— **a constant for fixed `h`, uniform in `N`**.  (The construction in
`PhaseAlgebra.exists_site_re_nonpos` returns `Nat.find hex − 1`, and
`Nat.find hex ≤ log₄|h| + 1` because `|h/4^j| ∈ (0,1)` once `4^j > |h|`.)

**Why this is route-decisive.**  `windowMean_le_terms` currently discards `j₀` by monotonicity
down to `yBot N`, which is what forces `freshMassTwo_graded` — a fresh-mass bound whose root
chain from `yBot N` costs `≍ L₃N` halvings and is therefore NOT implied by `ε_N → 0`.  With the
index bound, `y_{j₀} ≥ y_{c(h)} = ⌊N^{a_N 2^{-c(h)}}⌋` is a **near-top** cutoff, whose chain to
`N` is only `c(h) + 2 log₂ u_N` halvings: `S_P(y_{j₀}, N) ≤ ε_N(c(h) + 2 log₂ u_N + 1) → 0`,
exactly the `o(1)` that Astra §8 (8.5)–(8.6) uses.  Then `J_N` may be tied to the **full** mass
`S_P(N)` (Astra: `S_N = S_P(0,N)`, NOT the mass below the bottom cutoff), and

* the tail branch becomes the paper's: `S_P(2N) = S_P(N) + S_P(N,2N) < 8J + 8 + ε_N`, where
  `S_P(N,2N) ≤ recipSumIoc P (√(2N)) (2N) ≤ ε_N` is a **one-step** root chain;
* E5 becomes `S_P(2J, y_{j₀}) ≥ S_N − S_P(y_{j₀},N) − (1 + log 2J) ≥ 8J − 1 − log 2J − o(1)`.

**Next attack (in order).**
1. Thread the index bound through the `∃ j₀` of the graded Theorem A chain:
   `PrimeModelKMTGradedModel.norm_model_expectation_le_graded` →
   `PrimeModelTheoremAGraded` (l.307) → `PrimeModelTheoremAGradedM` (ll.133, 241) →
   `PrimeModelWindowSchedule.window_bound_schedule` (l.84).  Each is a conjunct added to the
   existential; the proofs pass `exists_site_re_nonpos_le` instead of `exists_site_re_nonpos`.
2. Rewrite `windowMean_le_terms` to bound E5 at `y_{min(c(h), k-1)}` instead of `yBot N`.
3. Redefine `JG N = min (J1 N) ⌊recipSumLe P N / 8⌋₊` (full mass, per Astra §8) and delete
   `freshMassTwo_graded`; `tail_graded`'s branch 2 then needs only `S_P(N,2N) ≤ ε_N`.
4. `termE5_tendsto` off the new E5 shape.

## 2026-09-22 (lap G5c-d) — leaf status after four closed leaves

CLOSED this run (all `lake build` green, in `src/NormalNumbers/PrimeModelFamilyGraded.lean`):
`yBotG_tendsto` (+ `epsN_le_aMinG`), `termE4b_tendsto` (+ `sum_uuG_le`),
`termE4a_tendsto` (+ `yBotG_le_yG`, `aG_ge_invL3`, `one_add_div_four_le_sqrt`,
`geom_sum_le_two`), `JG_tendsto` (+ `JG_le_L3`, `JG_le_mass`, `JG_lower`, `yBotG_le_self`),
and `tail_graded` / `tailOK_graded` MODULO one new, sharper leaf:

### ⚠️ NEW CRUX: `freshMassTwo_graded`

`∀ᶠ N, recipSumIoc P (yBotG N) (2N) ≤ 1`.  `tail_graded` is otherwise a verbatim port of
`tail_fresh`, and this is the single spot where `FreshMassZero` was used there.  It is NOT a
routine port:

* The root chain from `yBot N = ⌊N^{(1/L₃N)2^{−J₁N}}⌋` costs
  `K_N = ⌈log₂(log 2N / log yBot N)⌉ = J₁N + log₂L₃N + O(1) ≍ L₃N` halvings,
  so `recipSumIoc_le_rootChain` only yields `ε_N · L₃N`, and `ε_N → 0` does not control that.
* The bound is needed ONLY in the second branch of the `min` in `JG` (`J_N = ⌊S_P(yBot)/8⌋ < J₁N`).
  In the first branch `4^{J_N} ≥ (L₂N)^{log 4}/4` already beats the crude
  `S_P(2N) ≤ 12 L₂(2N) + 21` — that branch is fully proved.
* So the true obligation is the weaker: in branch 2,
  `(S_P(yBot,2N) + 13 J_N + 20)/4^{J_N} → 0` with `J_N = ⌊S_P(yBot N)/8⌋ → ∞`.

Two candidate repairs, in order of promise:
1. **Shorten the bottom chain.**  `TailOK` only needs `4^{J} ≫ S_P(2N) ≍ L₂N`, i.e. `J ≳ L₃N/log 4`.
   Nothing forces `2^{−J₁N}` in `aMinG`: `JG ≤ J1` is used only through `yBotG ≤ y_j`.  Replacing
   `J1 N` by `⌈L₃N/log 2⌉`-free data, or grading the chain as `∑_j 4^{−j}` does for E1, may bring
   `K_N` down to `O(log u_N)`.
2. **Branch-2 comparison.**  In branch 2 use the crude `S_P(2N) ≤ 12 L₂(2N) + 21` only when
   `J_N ≥ 0.73 L₃N`, and the root chain otherwise; the gap is the regime
   `log_4 L₂N ≫ J_N ≫ 1`, where `S_P(yBot) ≍ 8J_N` is small, i.e. `P` has almost no mass below
   `yBot`.  Show that this regime contradicts `DivergentRecip` + `SqrtFreshMassZero`, or adjust
   the `/8` in `JG`.

### Still open (unchanged estimates)

1. **`schedule_admissible`** — the eleven pointwise clauses.  `hcutlo` needs `L ≥ 2`
   (`⌊t²⌋^{1/4} ≤ ⌊t⌋` for `t ≥ 2`, which is why `LG = max 2 …`), `hcut2` needs
   `2^{−L} log yBot ∈ [log 2, 2 log 2]`.  `hybot` is now PROVED (`yBotG_le_yG`).
2. **`termE1_tendsto`** — root chain: `S_P(y_j,N) ≤ ε_N(j + 2log₂u_N + 1)`; sum against
   `4^{−j−1}` and use `ε_N log u_N ≤ ε_N log(1/ε_N)/2 → 0`.
3. **`termE4c_tendsto`** — `log R ≤ (540+8u_N)/u_N² · log N`, `(2J)# ≤ 4^{2J}`,
   `∏_j ⌊T_j⌋ ≤ N^{0.22}`; product is `N^{−1+o(1)}`.
4. **`termE5_tendsto`** — `8J ≤ S_P(yBot)` (`JG_le_mass`, PROVED) and `S_P(2J) = O(log log J)`
   give the exponent `≥ 5J`.

Suggested order: `freshMassTwo_graded` (the crux) → E5 → E1 → E4c → `schedule_admissible`.

---


## 2026-09-22 — G5c: Theorem C′ is stated and wired; the open leaves are the five term limits

`src/NormalNumbers/PrimeModelFamilyGraded.lean` (this lap) holds **Theorem C′**,
`isNormal_subsetLambert_of_sqrtFreshMassZero`, wired through
`isNormal_subsetLambert_of_KMT_along`.  Everything structural is proved; the schedule's
*numeric* obligations are the open leaves.  Landed in this chain, all axiom-clean:

| leaf | file | headline |
|---|---|---|
| G4 | `PrimeModelTheoremAGraded.lean` | `KMT.window_bound_gradedG` (graded law, split at `k`) |
| G4′ | `PrimeModelTheoremAGradedM.lean` | `KMT.window_bound_gradedGM` (split at `m = 2k`) |
| G5a | `PrimeModelGradedTiers.lean` | `BlockSieve.empLawG_lower_atom_bands` (tiers eliminated) |
| G5b | `PrimeModelWindowSchedule.lean` | `KMT.window_bound_schedule` (no model/sieve hypothesis) |
| G5c | `PrimeModelFamilyGraded.lean` | `windowMean_le_terms`, `kmt_along_graded`, **Theorem C′** |

### The open leaves (all in `PrimeModelFamilyGraded.lean`)

1. **`schedule_admissible`** — the eleven pointwise clauses of `window_bound_schedule` for the
   Astra §8/§11 schedule.  All floors/rpow bookkeeping; the two that need care are
   `hcutlo` (needs `L ≥ 2`: `⌊t²⌋^{1/4} ≤ ⌊t⌋` for `t ≥ 2`, which is why `LG = max 2 …`) and
   `hcut2` (`2 ≤ y_b^{2^{−L}}`, from `2^{−L} log yBot ∈ [log 2, 2 log 2]`).
2. **`termE1_tendsto`** — root chain: `S_P(y_j,N) ≤ ε_N(j + 2log₂u_N + 1)`; sum against
   `4^{−j−1}` and use `ε_N log u_N ≤ ε_N log(1/ε_N)/2 → 0` (this is what `u_N ≤ ε_N^{−1/2}` is
   for).
3. **`termE4a_tendsto`** — `log T_j/(2 log y_j) = 2^{j/2}u_N²/32`, so the sum is
   `2e^{20}∑_j exp(−2^{j/2}u_N²/32) ≤ 2e^{20}·2·exp(−u_N²/32) → 0`.
4. **`termE4b_tendsto`** — `∑_b e^{−(u_N+b)} ≤ 1.6 e^{−u_N} → 0`.  Needs only `u_N → ∞`; the
   grading of the tier weights is what removes the `J` factor.
5. **`termE4c_tendsto`** — `log R ≤ (540+8u_N)/u_N² · log N` (from `∑_b (b+1)2^{−b} = 4`,
   `∑_b 2^{−b} ≤ 2`), `(2J)# ≤ 4^{2J}`, `∏_j ⌊T_j⌋ ≤ N^{(1/16)/(1−2^{−1/2})} ≤ N^{0.22}`;
   product is `N^{−1+o(1)}`.
6. **`termE5_tendsto`** — `8J ≤ S_P(yBot)` and `S_P(2J) = O(log log J)` give the exponent
   `≥ 5J`, so the term is `≤ e^{−5J} → 0`.
7. **`tailOK_graded`**, **`JG_tendsto`** — verbatim the `tail_fresh` / `JI_tendsto` two-branch
   arguments of `PrimeModelFamilyConsumer` / `PrimeModelFamilyIterMass` with `yBotG` for `yI`
   and `JG` for `JI`.

The arithmetic of each leaf is checked on paper (the table below); nothing in the paper is
refuted.  The ONE structural deviation from the paper's schedule, forced and recorded: the tier
weights are **graded**, `u_b = u_N + b`, not constant.  With a constant `u` the defect term is
`J e^{−u}` and `TailOK` pins `J ≍ L₃N`, so `ρ_N → 0` alone cannot kill it; with `u_b = u_N + b`
the geometric sum is `1.6 e^{−u_N}` and the extra level cost is `∑_b 4b·2^{−b} log y_b = O(a log N)`,
absorbed into the same `540` constant.

---

## 2026-09-22 — ROUTE CORRECTION: Theorem C′ needs the **graded joint state**

Review lap on `KICKOFF-2026-09-22-multicutoff-lean.md` (laps 0–6 landed; Theorem A
`KMT.window_bound_graded` assembled with a hypothesis `hlower`).  The handoff's plan for closing
`hlower` — one tier `κ = Unit`, constant class count `dpK k` — is **refuted**.  See
`DIRECTION.md` → CURRENT DIRECTIVE for the two-line refutation.  Summary of the arithmetic:

| constraint | with constant `d_p = k` | with graded `d_p = #{j : p ≤ y_j}` |
|---|---|---|
| Brun level `log R / log N` | `≥ 128 k a` (top band dominates) | `a ∑_b (128 b + 4u + 14)2^{-b} ≤ a(270+4u)` |
| forced top exponent `a` | `≤ 1/(2048 J)` | `u^{-2}`, `u → ∞` free |
| root chain at site `j` | `≥ 11 + log₂ J + j` | `2 + 2log₂ u + j` |
| transfer `∑_j 4^{-j}·2S_P(y_j,2N)` | `≍ ρ_N log J ≍ ρ_N L₄N` ✗ | `≍ ρ_N log u ≤ ρ_N log(1/ρ_N)/2 → 0` ✓ |
| E4a `∑_{j<J} e^{20}/T_j^{α_j}` | `α = 1/(2 log Y)`: terms → `e^{20}`, sum `≍ J e^{20}` ✗ | `α_j = 1/(2 log y_j)`: `∑ e^{20}e^{-u²2^{j/2}/32} → 0` ✓ |

`TailOK` pins `J ≍ min(L₃N, S_N/8)`, so `J` cannot be capped to rescue the first column, and
`∑_j log T_j ≤ ½ log N` (CRT remainder) cannot rescue the second.  Both walls are structural.

**The good news.**  The whole *arithmetic* half is already graded: `graded_brun_lower` takes an
arbitrary `dp : ℕ → ℕ` with `hdpj : ∀ j, ∀ p ∈ U j, dp p ≤ d j`, and with the geometric schedule
each band is exactly ONE dyadic block (`cut y j 1 = y_j^{1/2}`), so the tier data is
`UU b = P ∩ (y_b, y_{b-1}]`, `yy b = y_{b-1}`, `dd b = b`.  Only the *state* side is ungraded.

**Two structural facts that make the regrade cheap** (both checked on paper this lap, to be
machine-checked):

1. *The graded model is the pushforward of the ungraded one, and the model expectation is
   unchanged.*  In `model_expectation_eqG` the local factor is
   `1 + (∑_{j<k}(zSee_{ij} − 1))/p_i = 1 − d_i/p_i + (1/p_i)∑_{j<d_i} zPhase_j`, because
   `zSee k y h p j = 1` whenever `p > y_j`.  So **E5 and the phase algebra need no change at
   all** — `norm_model_expectation_le_graded` is reusable verbatim.
2. *`statePhaseG` is graded-measurable*: `statePhaseG (truncState d s) = statePhaseG s`, same
   reason.  So the empirical side transfers by rewriting the fibres, not by a new factorisation.

### The named leaves (each a green node)

- **G1** `PrimeModelRadicalGraded.lean` — `localWeightG (d k : ℕ) (q : ℝ) : Option (Fin k) → ℝ`
  (`none ↦ 1 − d q`, `some j ↦ if j < d then q else 0`), `weightG k dp q`.  Leaves:
  `localWeightG_sum` (`= 1`), `weightG_nonneg` (needs `d_i q_i ≤ 1`), `radical_mass_oneG`,
  `radical_phase_productG` (local factor `1 − d_i q_i + q_i ∑_{j<d_i} z_{ij}`),
  **`radical_site_momentG`**: `∑_s weightG(s)·∏_{i : s i = j} t_i = ∏_{i : j < d_i}(1 + q_i(t_i − 1))`
  — the product is over the primes the site actually sees.  All four go through `sum_pi_prod`.
- **G2** `PrimeModelRadicalTailGraded.lean` — `radical_box_tailGG`: `∑_{s ∉ retainedBoxG} weightG
  ≤ ∑_j exp(A j)/T_j^{α_j}`, then discharge `A j ≤ 20` at `α_j = 1/(2 log y_j)` with
  `radical_moment_budget` applied to the subfamily `{i : j < d_i}` (all of whose primes are `≤ y_j`).
  `retainedBoxG_card_le` is over the full state type and is reused verbatim.
- **G3** `PrimeModelJointGraded.lean` — `truncState`, `actualStateG = truncState ∘ actualState`,
  `jointModelG`, `empLawG`; mass one / nonneg for both; graded `actual_state_sifted_iff`
  (`SiftedCondD A U dp jp Q r n ↔ n % Q = r ∧ actualStateG n = s`); graded `state_model_density`;
  **`empLawG_lower_atom`** off `graded_brun_lower` at band-dependent `dp`.
- **G4** `PrimeModelTheoremAGraded.lean` — graded E4 (`finite_phase_of_lower_atoms` is already
  generic), the two transfer identities (`∑_g ν̃ F = ∑_t ν F` from fact 2; `∑_g μ̃ F = ∑_t μ F`
  from fact 1 — both sides are the same explicit product), then Theorem A restated with no
  `hlower`.
- **G5** `PrimeModelFamilyGraded.lean` — lap 7: `Z_N`, `ρ_N`, `u_N`, `J_N`, the schedule
  `y_j = ⌊N^{u^{-2}2^{-j}}⌋`, `T_j = N^{2^{-j/2}/16}`, then `KMT_along` + `TailOK` and the headline.

### Cheap on-path node worth taking when a leaf stalls

`isNormal_subsetLambert_of_sqrtFreshMass_rate` : `(fun N => ρ_N · L₄ N) → 0` (a *rated* square-root
fresh mass) `→ DivergentRecip P → IsNormal 4 (subsetLambert P 4)`, by feeding the lap-0 root chain
`recipSumIoc_le_rootChain` into the EXISTING ungraded `isNormal_subsetLambert_of_freshMassZero`
(`yI N = ⌊N^{(L₃N)^{-4}}⌋`, chain length `≍ 4 log₂ L₃N`).  This is the exact theorem the ungraded
machinery can reach, and it makes the `L₄N` factor in the refutation above a machine-checked
statement rather than a paper remark.

---

## 2026-09-21 — crux advance: the summatory node split (`G4SummatorySplit.lean`)

The sole analytic input of the G4 window law off the Chowla sector, `RoughSummatory h`, has been
**split into one open piece and one classical piece**:

* `RoughSummatoryPrefix h` — the *multi-shift* clause: Selberg-Delange for
  `sum_{m<M} prod_{j=1}^{k} z_j^{omega_{>2}(m+j)}`, a correlation of `k` multiplicative functions at
  `k` distinct shifts, uniformly for `k <= windowJ M`.  **This is now the crux.**
* `SDShiftFree h` — the singleton clause with the shift *removed*: LSD for the single function
  `n |-> z_k^{omega_{>2}(n)}` on each parity class.  Classical (Tenenbaum II.5.3, Euler factor at 2
  split off).

`roughSummatory_of_split` and `isNormal_G4_of_shiftSplit` are axiom-clean; shift removal costs `2k`,
absorbed by `shift_cost_small` (the node budget carries `4^{-k}` and `4^k <= 4(log_2 M)^2` on the
window range).

**Route 1 (pointwise truncation of the shift product) is REFUTED — 2026-09-21.**  The decisive
computation was run.  Truncating `prod_{j<=k}` at `j0` costs, pointwise,
`sum_{j>j0} 2 pi |h| omega_{>2}(m+j) 4^{-j} ≍ (log log M) 4^{-j0}` per `m`, i.e. `M (log log M) 4^{-j0}`
in total, and `j0 <= k <= windowJ M` forces `4^{j0} <= 4 (log_2 M)^2`, so the cost is at least
`≍ M (log log M) / (log M)^2`.  The node's budget is NOT `C M / log M`: it is
`C M (log M)^{Re kappa_k - 1}`, and `Re kappa_k <= -1` as soon as `k` passes the 4-adic valuation of
`h` — this is now a **machine-checked theorem**, `exists_re_sdExponent_le_neg_one` in
`G4SummatorySplit.lean` (at the first site `j` with `4^j` not dividing `h`, `e(h/4^j)` is a quarter
or half turn, so `Re(e(h/4^j)-1) <= -1`; all other sites contribute `<= 0`).  So the budget is at
most `C M (log M)^{-2}`, which the truncation cost exceeds by the factor `log log M`.  No choice of
`j0` repairs this: the loss is intrinsic, because the truncation error is measured against `M` while
the budget is measured against the much smaller main term `M (log M)^{Re kappa}`.  Any future attack
must keep the tail sites **inside** the main term, not discard them.

**Next attack on the crux.**
1. *(dead — see above)*
2. The residual is a `k`-fold shifted correlation with `k -> infinity` very slowly;
   the natural formal input is a Nair-Tenenbaum / fundamental-lemma upper bound plus a main term
   from the `k`-dimensional Selberg-Delange of Tenenbaum II.5 Thm 3 applied to the product
   Dirichlet series, whose singularity exponent is exactly `sdExponent h (Icc 1 k)`.

Also still owed (from `HANDOFF-2026-09-20-summatory-node.md`): a sharper numerical probe of the
equal-constants-on-both-parity-classes clause (see that handoff's "sharper test" section).

## 2026-09-20 — campaign B has reached its pre-registered FINISH LINE

Both terminating conditions of the 2026-09-16 CURRENT DIRECTIVE are met:

* **terminal objective** — `SchedB.isDisjunctive_weightA_logLog` plus its audit theorem
  `audit_isDisjunctive_weightA_logLog` (`G4WeightStatement.lean`), trust-triple clean;
* **the one permitted stretch** (general additive `f`) — **refuted in the kernel** by
  `src/NormalNumbers/G4AdditiveRigidity.lean`: every `TWeight` is affine along every
  prime-power tower (`wN_prime_pow_affine`) and additive across pieces `≡ 1` mod `rad d`
  (`wN_mul_of_modEq_one`), so a non-affine profile is not a `TWeight` at all.  The obstruction
  is in the transport interface, upstream of §4C and §4D; domination cannot reach it.
  `G4WeightInterface`'s prose "iff" is now a machine-checked biconditional.

Build 🟢 9103 jobs, zero `axiom`s.  `src/` = the two pre-expedition forbidden-drift `sorry`s
(`phaseOscillation`, `exists_prime_nonresidue`), both named on the directive's ⛔ list.

**The repo needs a new directive from an altitude lap**, not more work inside this one.
Candidates, with the state of each, are in `HANDOFF-2026-09-20-campaignB-close.md` §4.
### The one genuinely open interface question, stated precisely

**Conjecture.**  For every `W : TWeight`, the function `m ↦ w(m) − w(1)` is additive; equivalently
`W` is `addWeightN g + w(1)` for an affine family `g`, i.e. `w_{a,c}` up to a constant.

*Why the constant is necessary* — **now formalised** as `TWeight.omegaOdd` with
`TWeight.omegaOdd_not_additive` (`decide +kernel`): `w = ω + 1_{m odd}` passes
every axiom — the correction is `overlap_ω(d,m) + 1 − e(d)e(m)` with `e = 1_{even}`, which is
constant `= 1` for odd `d` and, for even `d`, depends on `m` only mod `2 ∈ rad d`, so `ov_congr`
holds; `ovB d = ω(d) + 1`.  It is **not** additive (`w(15) = 3 ≠ w(3) + w(5) = 4`) and has
`w(1) = 1`.  But `1_{m odd} = 1 − 1_{2 ∣ m}` and `1_{2 ∣ m}` is additive, so it is
*additive + constant*.  So the `− w(1)` in `wN_mul_of_modEq_one` is load-bearing, not
cosmetic, and "every `TWeight` is additive" is **false** — the conjecture above is the
corrected statement.

*State of the proof.*  `wN_mul_of_modEq_one` settles the case `m ≡ 1` mod `rad d`.  The tools for
the general case are now in place: `ov_symm`, the cocycle identity `ov_cocycle`
(`ov d m + ov (dm) k = ov m k + ov d (mk)`, forced by `mul_eq` alone) and
`ov_mul_left_of_modEq_one`.  The gap: for coprime `d, m` one wants `ov d m = w(1)`, and the
cocycle only relates corrections at residues that are already `1` somewhere.  The natural next
probe is a Dirichlet prime `q ≡ m` mod `rad d` together with `ord_q(p)`; attempted this lap and
**not** settled — recorded as open, not refuted.

---

# PENDING WORK — **campaign B FINAL: the `a`-side** (DEEP REFLECTION lap, 2026-09-16)

> Campaign B's `c` axis and subset axis are **closed**; the `a`-side is the campaign's
> **TERMINAL** objective and there is a pre-registered FINISH LINE after it.
> See `DIRECTION.md` → CURRENT DIRECTIVE for the binding orders and
> `REFLECTION-2026-09-16-campaignB.md` for the full reasoning.
> Build 🟢 9085 jobs, zero `axiom`s, `src/` = the two pre-expedition forbidden-drift `sorry`s.

## Reflection — 2026-09-16 (deep reflection lap): the `a`-side crux is PROBED and it HOLDS

**ROUTE VERDICT: CONTINUE.**  No registered trigger fired (B-review-1's 🚦 growth-class trigger
did not fire — `Tame` + `isDisjunctive_weight_logLogPow` landed).  Neither rationalization tell
is present: two whole campaigns *closed* in the last day, and the finishability estimate rose.

**The named risk is scope creep, not a false summit.**  B0–B3 attacked the machine; B4/B5 were
growth-class bookkeeping and an audit surface.  Left open-ended this campaign can emit headlines
indefinitely at zero marginal content.  Hence the pre-registered finish line in the directive.

**The decisive probe (`scratch/ProbeA.lean`, compiles against the tree).**  The one genuinely
uncertain question was whether the §4C good-prime contraction survives the *scaled* frequency
`a_p·q` — it can fail catastrophically in principle, since `distZ(a·x)` can vanish while
`distZ(x) > 0`.  It survives, and cheaply:

| lemma | content |
|---|---|
| `phaseA_eq_sum_local` | `Φ_a(n) = ∑_{p∈s} localPhase p ρ (a_p • x) n` — the local phase at `p` is the **ordinary** one at scaled coefficients |
| `vecMul_const_mul` / `coeffAL_const_mul` | `coeffAL` is **linear in the frequency**: `a_p·(q ᵥ* A) = (a_p·q) ᵥ* A` |
| `sum_sq_distZ_coeffA_ge_gen` | `freqSeed bb K ≤ ∑_i distZ(a_p·coeffAL bb q i)²` for `1 ≤ a_p ≤ Ca`, given `N ≥ 1 + ⌈log_bb(2^K·Ca·D)⌉` — **the seed is unchanged** |

Why it is cheap: `sum_sq_distZ_freqDepthB_ge` has **no box hypothesis** — it holds for an
arbitrary nonzero `q`.  The box `D` enters only through `freqDepthB_le`, the admissibility of
the chosen depth inside the layer budget `N`.  So a general bounded `a` costs exactly one
**additive** `⌈log_bb Ca⌉` on `N`, absorbable the way `C` was in B2e.  The roots of
`LocalPhase.ofShifts` depend only on `ρ`, so the four §4C error terms are *identical*, and
`norm_sampleAvg_prod_ee_le` already takes a **per-prime** `LocalPhase` family and a **per-prime**
seed, so no new probabilistic layer is needed.

**Architecture call (binding).**  `omegaOnA 1_S s m = omegaOn (s.filter S) m` — the prime-subset
campaign IS the `a`-side at `a = 1_S`.  Generalize `G4SubsetC*` **in place**; do not build a
fifth parallel §4D stack.  This collapses the `a`-side and the `a`-side × subset merge into one
obligation.

**Stretch, after the `a`-side only**: the **general additive function** `f(p^v) ≤ a_p + c_p(v−1)`
with `f(p) = a_p`, `f` non-decreasing in `v`.  §4C sees only `f(p)`; §4D's estimates are upper
bounds and the far-field `hW` is already a *domination* (`sum_abs_farPartW_le_of_layer`), so it
should ride the `a`-side with no new §4D work.  `w_{a,c}` is exactly the additive functions whose
`p`-local value is affine in `v` — an odd class to headline; this is the natural statement.

**Not targets, and why (all machine-checked, do not re-derive)**: base 2
(`one_le_rowMass_two`), normality of `G₄` on this mechanism (`qForces_normal_iff_density_one`),
`c_p ≍ log p` (`DESIGN-2026-09-16-prime-subset.md`), divergence without a rate (ibid.).
`phaseOscillation` is the *base-two* constant `∑ ω(n)/2ⁿ` — the proved-dead case, and superseded
in the literature by Tao–Teräväinen arXiv 2512.01739 Thm 1.3; the `b ≥ 3` half is ours
(`irrational_primeSum`, trust-triple clean).

## 🎯 Campaign B ladder (the live attack path)

**Target.**  `w_{a,c}(n) = ∑_{p∣n} (a_p + c_p(v_p(n)−1))`, `a` bounded (or `a = 1_S` with
`∑_{p∈S} 1/p = ∞`), **`c` unbounded**.  Instances: `ω` (`a=1,c=0`), `Ω` (`a=c=1`), `ω_S`,
`w_c` (`c ≤ C`), `w_{c,S}`.

| # | leaf | status |
|---|---|---|
| B0 | `TWeight.ov_le` → per-`d` bound `ovB : ℕ → ℕ` | open — **free**: `ovC` is consumed only by `G4TransportW.summable_corrB` (probe, lap B-review-1), never quantitatively.  5 instances to update. |
| B1 | **crux** — `sum_junk_le` with the `c_p` kept inside the sum | ✅ **DONE** (`G4UnboundedJunk.lean`): `sum_junk_le'`, the `C`-free bound functional `junkShiftBoundC`, `sum_junk_C_le'`, and the faithfulness check `sum_junk_le_of_bounded` (the old estimate is the `c ≤ C` case).  All trust-triple clean. |
| B1b | `junkAvgC_le'` — the block average against `junkShiftBoundC` | ✅ **DONE** (`G4UnboundedAvg.lean`) — no hypothesis on `c` at all |
| B2a | `sum_weightW_shiftG_le` — the far-field sample sum via the §4D split | ✅ **DONE** (`G4UnboundedAvg.lean`): `frozenCap c P₀ = ∑_{p∣P₀} c_p·v_p(P₀)`, `frozenExcess_le_frozenCap`, and `∑_n w_c(n+shift_j) ≤ |P|·((farC+2j)/log 2 + frozenCap) + junkShiftBoundC c P₀ X (j·Dm)` |
| B2b | **the effective-constant reduction** | ✅ **DONE**: `Tame c A` (`one_le`/`tail`/`pref`) in `G4UnboundedJunk`, with `tame_of_bounded` (every bounded `c` is tame at `A = max C 1`) and `Tame.coeff_le` (`c_p ≤ A(p+1)`).  In `G4UnboundedAvg`: `effC c P₀ A = max (A + frozenHarm c P₀) (frozenCap c P₀)`, `junkShiftBoundC_le_effC`, `frozenCap_le_effC_mul`, and **`sum_weightW_shiftG_le_effC`** — literally `sum_abs_farPartC_le`'s `h3` with `κ := effC`. |
| B2c' | the far part at `effC` | ✅ **DONE**: `sum_abs_farPartW_le_of_layer` (`G4UnboundedAvg`) — generic in the `TWeight` *and* in `κ`, taking the per-layer bound as a hypothesis.  `κ = max C 1` recovers `sum_abs_farPartC_le`; `κ = effC` + `sum_weightW_shiftG_le_effC` gives the tame case. |
| B2d | **frame plumbing, generic in `W`** | next.  The §4D frame chain is stated for the *subject* `TWeight.weight c C hC`, which has no unbounded analogue.  Four declarations need `W` + `hW : ∀ m, (W.wN m : ℝ) = weightW c m` in place of that subject: `gridFrameW_weightC_Ffull_decomp`, `farAvgC` (→ `farAvgW W`), `gridFrameW_weightC_propD`, `gridFrameW_weightC_propD_of_bounds`.  Their proofs use the subject only through `TWeight.weight_wN`, so `hW` replaces it verbatim. |
| B2e | the schedule at `C := ⌈effC⌉₊` | open — the schedule's numeric facts (`hjunk_holdsCE`'s `100000·C·k₄³ ≤ 2^{k₄}`, `hfarC_holdsE`) take `C : ℕ` and `k₄` is chosen *after* `C` (`exists_good_k₄`), so the natural `⌈effC⌉₊` feeds them unchanged.  Nothing there needs re-deriving. |
| B2 | far field without `κ = max C 1` | open — take the `Ω` route (`ω + frozenExcess_c + junk_c`), not `w_c ≤ κ·Ω` |
| B2c | `TWeight.weightU c hT` — the unbounded weight as a `TWeight` | ✅ **DONE** (`G4UnboundedTW.lean`).  `ovB d = ω(d) + ∑_{p∣d} c_p` needs **no** hypothesis on `c`; only `summable` uses `Tame` (via `weightW_le_tame : w_c(m) ≤ (1+A)(m+1)²` and `summable_weightW_div_pow_tame`).  §4A/§4B/§4C are therefore free for it. |
| B3 | `isDisjunctive_weight_of_tame`, then the merge `w_{c,S}` | ✅ **DONE** — `isDisjunctive_weight_logLog` (2026-09-16) and the merge `isDisjunctive_subsetWeight_logLog` / `isDisjunctive_residueClass_weight_logLog` (`G4SubsetCTW`/`CFrame`/`CWitness`/`CAssembly`, see `HANDOFF-2026-09-16-merge-wcS.md`).  Key move: the far-field `hW` is a *domination*, not an equality. |
| B4 | widen the class to `c_p ≤ A₀(1+log₂log₂ p)^s` | ✅ **DONE** — `tame_of_logLog_pow`, `exists_good_k₄_polyGen`, `isDisjunctive_weight_logLogPow`, `isDisjunctive_subsetWeight_logLogPow`, `isDisjunctive_residueClass_weight_logLogPow`.  See the addendum in `HANDOFF-2026-09-16-merge-wcS.md`. |
| B5 | audit surface for the campaign-B headlines | ✅ **DONE** — `G4WeightStatement` (`audit_isDisjunctive_*_logLogPow`, abbreviations unwound) + `STATUS.md` rows |
| B6 | **the `a`-side of the master weight**: `w_{a,c} = ∑_{p∣m}(a_p + c_p(v_p−1))` for a general *bounded* `a` — **the campaign's TERMINAL objective** | 🔨 in progress.  Arithmetic layer done (`G4WeightA`).  **§4C IS NOW PROVED, IN KERNEL** — `src/NormalNumbers/G4PhaseA.lean` (2026-09-16 deep reflection lap, all trust-triple clean): `omegaOnA` (+ `_one`/`_indicator`: `a=1` is `omegaOn`, `a=1_S` is `omegaOn (sm.filter S)`), `totalPhaseA`, `phaseA_eq_sum_local`, `shiftPhaseA`, **`shiftPhaseA_roots`** (the four §4C error terms are *identical* to the unweighted ones), **`norm_sampleAvg_ee_phaseA_le`**, `vecMul_const_mul`/`coeffAL_const_mul`, **`sum_sq_distZ_coeffA_ge_gen`** (the seed `freqSeed bb K` is unchanged; cost = `N ≥ 1 + ⌈log_bb(2^K·Ca·D)⌉`), `SvalA` (+ `SvalA_one`), `sum_mul_SvalA`, `torusChar_SvalA`, `sum_sq_distZ_coeffA_ge_of_bound`, **`norm_sampleAvg_torusChar_SvalA_le`**.  **Frame layer DONE too** (`G4FrameA.lean`): `gridFrameWA` (= `gridFrameW` with only the `S` field changed, so `PropA`/`PropB` transfer by `exact`), `gridFrameWA_one`, `torusChar_gridFrameWA_S`, `gridFrameWA_propA`, **`gridFrameWA_propC`** (bound is *literally* `smallPrimeBound`, with `sm` pre-filtered to the active primes `{p : 1 ≤ a_p}` — legitimate since an inactive prime contributes 0 to `omegaOnA`), and **`gridFrameWA_propC_gen`** (seed `freqSeed bb K` discharged under `1 + clog bb (2^K*(Ca*D)) ≤ G.N`).  **Remaining**: (4) §4D — `PropD` for `gridFrameWA` at `w_{a,c}`: port `G4SubsetCFrame`'s chain (`weightSC_split` → `frozenWeightSC`/`frozenGammaSC`/`blockSum_frozenSC_eq` → `blockSum_weightSC_split` → `gridFrameW_weightSC_Ffull_decomp` → `gridFrameW_weightSC_propD`) with `omegaOn (·.filter S)` ↦ `omegaOnA a ·` and `Sval` ↦ `SvalA`; the big-prime estimate scales by `Ca` (`omegaOnA a T m ≤ Ca · omegaOn T m`).  (5) schedule + assembly + audit theorem.  🚦 the layer-budget trigger now applies at the *schedule*: watch the moment cap `Mc ≤ 2^{m₂}`. |

**The hypothesis class `Tame c A`** (the replacement for `∀ p, c p ≤ C`):
`1 ≤ A`, `∀ M, ∑_{p<M} c_p/(p(p−1)) ≤ A` (tail), `∀ M, ∑_{p<M} c_p ≤ A·M` (linear prime prefix).
**The concrete unbounded instance**: `c_p = ⌊log₂ p⌋`.  The prefix bound is Chebyshev —
`∑_{p≤M} log₂ p ≤ 2M` follows from mathlib's `Nat.primorial_le_4_pow` — and the tail is
`∑_p log p/p² < ∞`.  So the headline to aim at is: `∑_n (ω(n) + ∑_{p∣n} ⌊log₂ p⌋(v_p(n)−1))/bⁿ`
is disjunctive for `b ≥ 3`, the first such theorem with **unbounded** coefficients.

**Where `C` actually bites** (the complete list, verified lap B-review-1):
`G4SchedWeight.hjunk_holdsCE` (`100000·C·k₄³ ≤ 2^{k₄}`) and `G4SchedWeight.hfarC_holdsE` via
`G4WeightJunkAvg.weightW_le_kappa_mul_cardFactors : w_c ≤ (max C 1)·Ω`.  Nowhere else.

**Proved obstruction, do not re-derive.**  Base 2 is dead for this design family:
`G4RowMassOptimal.two_pow_le_sum_abs` (every integer array with vanishing line sums in all `K`
directions has `∑|μ| ≥ 2^K`) ⇒ `rowL1_le_rowMass` ⇒ `one_le_rowMass_two`.  The only named
escape is signed cancellation in the `p > Y` range — a two-point-correlation input this
programme excludes.

---

## Archive of campaign A's closing state (2026-09-16 late)

## Closed, unconditional, axiom-clean

* `isDisjunctive_residueClass_primeSum`, `isDisjunctive_subsetLambert`,
  `isDisjunctive_subsetLambert_univ` (`HANDOFF-2026-09-16-residueClass.md`).
* `isDisjunctive_Omega`, `isDisjunctive_Omega_primePowerSum`
  (`HANDOFF-2026-09-16-omega-done.md`).
* **`isDisjunctive_weight c C hC (hb : 3 ≤ b) : IsDisjunctive b (weightLambert b c)`** — every
  bounded coefficient vector (`HANDOFF-2026-09-16-weight-headline.md`).  The whole
  `C`-dependence is one schedule condition, `100000·C·k₄³ ≤ 2^{k₄}`.

## Open, in order of interest

1. **`w_c` on a prime subset**: `w_{c,S} = ω_S + excess_{c·1_S}`.  Both axes are proved
   separately; the combination needs the Mertens-in-AP cutoff `e` (subset side) *and* the
   `C`-inflated `k₄` (coefficient side) in one witness.  `ScheduleWitnessS` and
   `ScheduleWitnessC` differ only in the §4D fields, so the merge is a third witness type with
   the `S`-filtered small primes AND the `C`-scaled junk/far budgets.
2. **Unbounded `c`** (e.g. `c_p = p`): the junk budget is linear in `C`, so no `k₄` fixes it —
   this needs a junk estimate weighted by `c_p/p`, not a uniform bound.
3. **Base 2 for `Ω`**: refuted at the design level for this route — the far junk grows like
   `2^j` (`junkShiftBound_layer_le`), so `∑ 2^j bb^{-j}` needs `bb ≥ 3`
   (`HANDOFF-2026-09-16-omega-schedule.md` §2).

## The live crux: `isDisjunctive_Omega` (override item 4, PENDING_WORK §"Next actions" step 3–4)

**Done (`G4OmegaWeight.lean`, 2026-09-16):** `TWeight.cardFactors` — `Ω` as a `TWeight` with
`ov = 0` (complete additivity), so §4A/§4B/§4C are free from `G4TransportW`/`G4FrameW`
(§4C never sees the weight: the retained vector is the `ω`-vector on `smallPrimes R P₀`).
Plus the pointwise split `cardFactors_eq_omegaR_add_excess : Ω = ω + excess 1` and its
integrality `excess_one_eq_cast`.

**The crux, sharply posed.**  `PropD` is the ONLY property of the frame that sees the weight.
For `ω_S` it was proved by *re-splitting by prime size* (`G4RemainderW`, `G4SubsetJunk`); for
`Ω` the split is different and the junk is a **valuation excess**, not a prime-count:

    Ffull_Ω(n,ν) = Ffull_ω(n,ν) + tailFrom(excess 1)(n,ν)

and `excess 1 = frozenExcess P₀ + junk P₀` (`G4WeightJunk.excess_eq_frozen_add_junk`), where
`frozenExcess` depends only on `m mod P₀` (`frozenExcess_congr`) and so is absorbed into the
frame's translate `γ`, while `junk` has the sample-mean bound `G4WeightJunk.sum_junk_le`.

**DONE 2026-09-16 (`G4OmegaRemainder.lean`), the whole §4D *structure* for `Ω`:**

* `cardFactors_split` — the four-way split
  `Ω = [ω_{p∣P₀} + frozenExcess] + ω_{smallPrimes R P₀} + ω_big + junk`;
* `frozenWeightΩ` / `frozenTranslateΩ` / `frozenGammaΩ` / `blockSum_frozenΩ_eq` — the first
  bracket is constant on the progression, so it is absorbed by the frame's translate `γ`;
* `blockSum_cardFactors_split`, `gridFrameW_cardFactors_Ffull_decomp` — `Ffull` for `Ω` is
  `Sval(smallPrimes) + blockSum(ω_big) + blockSum(junk) + farPart`;
* **`gridFrameW_cardFactors_propD`** — `PropD (δbig + δjunk + δfar)` from three sample averages
  `bigAvgΩ`, `junkAvgΩ`, `farAvgΩ`.

**Next attack, in order (each a named leaf in `src/`):**

1. **`junkAvgΩ_le`** — the ONE genuinely new arithmetic estimate: bound `junkAvgΩ` by
   `G4WeightJunk.sum_junk_le` applied at each shift `ρ_{α,jj}` and summed against the layer
   weights `bb^{-layer}`.  Shape to aim for:
   `junkAvgΩ ≤ rowL1 bb G.K · max_{ρ} (2 P₀/X) · (X/P₀ (∑_{p∣P₀} 1/(p−1) + 1) + √(X+ρ)log₂(X+ρ))`,
   i.e. `≤ rowL1 · (2(log ω(P₀) + 2) + 2P₀(√(X+ρmax)+1)log₂(X+ρmax)/X)`.
   Note `∑_{p ∣ P₀} 1/(p−1) ≤ H_{ω(P₀)} ≤ 1 + log ω(P₀)` is `sum_inv_pred_le_harmonic`.
2. **`bigAvgΩ_le` / `farAvgΩ_le`** — should be the existing `ω` estimates verbatim
   (`omegaBig` is the same function; `farPartW TWeight.cardFactors` needs `Ω(m) ≤ log₂ m`
   where the `ω` proof used `ω(m) ≤ log₂ m`, i.e. `cardFactors_le_log`).
3. **Schedule**: `hbig`/`hfar` gain the junk term (no new `Hyp` field at `c = 1`, since
   `C = 1`), then `isDisjunctive_Omega` through `isDisjunctive_of_framesW`.
4. The series identity `∑_n Ω(n)/bⁿ = ∑_{p,a≥1} 1/(b^{pᵃ}−1)`.

# PENDING_WORK

> ⚠️ This file is 493 KB.  Everything below the ACTIVE section is archive.  Write in the ACTIVE
> section; do **not** append to the bottom.

## 🎯 ACTIVE (objective **S**, review **lap 166**, 2026-09-15) — DESIGN §0's third escape CLOSED at the schedule

`DESIGN-2026-09-15-deformation.md` §0 names three deformations the `T(K′)` verdict does not test.
Two were closed (row-balanced cancellation → `Sched.balanced_union_le`; a different matrix →
`RowVariance.union_le_of_determining`).  The third — **giving up the single-`n` joint sample** —
had only a *generic* reduction (`grouped_coeff_le` / `grouped_union_le'`) whose size condition was
never checked at the schedule.  Lap 166 checked it, in the new `src/NormalNumbers/G4GroupedVerdict.lean`
(all four declarations `[propext, Classical.choice, Quot.sound]`, build 🟢 9041 jobs):

| declaration | content |
|---|---|
| `Sched.grouped_size_cond` | at the schedule, `(2dmax+1)^{2E}·m·H²·dmax ≤ dmin^{4E+3}`, so `grouped_coeff_le`'s hypothesis holds once `w ≥ 8E + 5` |
| `Sched.grouped_block_size` | groups are disjoint and cover the atoms: `G · w ≤ H` |
| `Sched.grouped_block_count_le` | hence **`8 K G ≤ K² + 1`** — at most `(K²+1)/(8K) ≈ K/8` blocks (`20000` at `i = 0`) |
| `Sched.grouped_balanced_union_le` | the grouped verdict: read set below `L` at most `L/dmin^{w/2} + G·(2dmax+1)^{2E}·H·m`, rate `dmin^{−w/2} ≤ dmin^{−(4E+2)}` |

**The correction this forced.**  `G4BalancedRigidity`'s `Grouped` docstring and
`DESIGN-2026-09-15-row-balanced.md` both read the criterion as `w ≳ 2 log H / log dmin`,
"a vanishing fraction of `H`", concluding "the single-`n` sample is *not* essential".  That
dropped the family factor `|𝓕|`, which at the schedule is already `dmin^{4E}`.  Both prose
passages are rewritten to the true threshold.  The verdict is unchanged — grouping is allowed,
but only into `≈ K/8` blocks, each a `1/K` fraction of the atoms.

### Next, in order (mirrors `DIRECTION.md` → CURRENT DIRECTIVE)

1. ✅ **The seam — DONE (lap 167).**  `Capture.InsideCapture K K′` packages the analytic side of
   one sampler (dyadic rough primes, released weights, bounded shift gaps, the three scale
   conditions, the capture inequality) as one `Prop`; `Capture.two_le_of_insideCapture` is
   `two_layers_of_dyadic` with that data existentially quantified; and `Sched.budget_confines` /
   `Sched.grouped_budget_confines` are the verdict with `2 ≤ K′` **derived, not assumed** — joint
   sample at rate `dmin^{−H/2}`, blocks of size `w ≥ 8E+5` at rate `dmin^{−w/2}`.  All in
   `G4GroupedVerdict.lean`, all trust-triple clean.

1b. ✅ **Non-vacuity of `InsideCapture` — DONE (lap 168).**  The dyadic route needed
   `|S| ≥ 1920·2^K·k` primes inside `[T, 2T]`, a dyadic prime *count* mathlib does not have (only
   `Nat.bertrand`, one prime).  `Capture.two_layers_of_mertens` replaces it with the `|S|`-free
   Mertens bound (`Budget.budget_forces_two_layers` fed by `roughRowVarianceLower_mertens`; the
   strict positivity of the constant is free, since `ε ≥ 3/(T−1) > 0`), `InsideCapture` is
   re-packaged on it, and **`Capture.structural_satisfiable`** proves every conjunct but the
   capture inequality meetable for every `K`, `k` and every `L > 0`.  The trick: `Q` is
   existential too, so taking `Q = 2^K·L` makes `scales_satisfiable`'s own `Q < T` deliver the
   shift-gap bound `|ρ i − ρ j| < T^{k+1}` for free (shifts enumerated by `finProdFinEquiv`).
   What is left is exactly the sampler's own capture inequality — a genuine constraint, and a
   consistent one: `RoughRowVarianceLower` forces `sm K′ ≥ c·2^K·16^{−K′}/15` against the cap
   `c·2^{−K/2}`, and the two meet precisely when `K′ ≳ 3K/8` — DESIGN §3's (E) recovered as the
   consistency range of the packaged `Prop`.

2. ✅ **The residue, decided from the certificate side — ANSWERED (lap 169): NO threshold.**
   `src/NormalNumbers/G4EntropyBlocks.lean`:
   * `Blocks.H₂_le_sum_blocks` — cutting the coordinates into blocks and keeping only each
     block's own marginal is **subadditive**: `H₂(L) ≤ Σ_g H₂(L|block g)`.  (Generalized
     subadditivity `FinLaw.H₂_le_sum_H₂_map` at the family of padded block restrictions, which is
     injective exactly because the blocks partition the coordinates.)
   * `Blocks.H₂_restrictCoords_le` — a block's marginal carries at most `m` bits per coordinate.
   * `Blocks.weight_of_good_blocks` — the pigeonhole, division-free: per-block caps
     `H_g ≤ m·w_g` plus `Σ H_g ≥ c·m·Σ w_g` force the blocks keeping a `θ`-fraction of the
     maximal rate to carry `≥ (c−θ)/(1−θ)` of the total weight.
   * `Blocks.good_block_weight` — the two combined for a `FinLaw` on `A → Fin (2^m)`.

   At E0's constant (`entropy_E0`: `(1/5)·m·H < H₂`) and `θ = 1/10`: **whatever the block
   structure — blocks of size one included — at least a ninth of the atoms sit in blocks whose
   own marginal still carries a tenth of the maximal rate.**  So the entropy saving is diluted
   at worst proportionally by blocking and never destroyed; there is **no certificate-side
   dimension threshold**, and the certificate is not what forbids small blocks.

3. **The honest residue of objective S, now sharp.**  Everything that forbids blocks below
   `w = 8E + 5` is the *counting* bound, and that bound is essentially tight (lap 164's probe:
   the `skel` count is loose only by a constant factor **in the exponent**).  With lap 169's
   answer on the certificate side, the residue is exactly:

   > a sampler whose blocks carry fewer than `8E + 5` atoms is **not excluded by anything
   > proved**.  Not by the counting bound (vacuous there), not by the error budget
   > (`InsideCapture` is block-independent — it constrains the row second moment, not how the
   > atoms are grouped), and not by the entropy certificate (`good_block_weight`).

   That is where a future escape from the deformation verdict would have to live.  The next
   concrete move is to decide whether a small-block sampler can *exist*: the transport identity
   is atom-local (`G4Grid.add_shiftG_eq` needs only `n ≡ t_α mod d_α` for the atoms sharing `n`),
   so nothing obviously forbids blocks of size one — in which case the read set has density one
   and the obstruction must come from somewhere the present chain does not reach.  Formalize the
   *positive* direction first: a `Prop` saying "a `G`-block sampler with the full certificate
   exists", and see which of the three pillars it contradicts.

### Refuted / checked this lap, do not retry
* **Sharpening `|𝓕|` with the pairwise-coprimality hypothesis.**  `hcop` forces `d` injective on
  all `H` atoms (values `≥ dmin ≥ 9` that are pairwise coprime are distinct), so `|𝓕|` is at most
  the number of injections into `[dmin, dmax]`, `≈ (4H·kk)^H`, i.e. `≈ dmin^H` — **weaker** than
  the MDF bound `dmin^{4E} = dmin^{4H·K/(K²+1)}` by a factor `K/4` in the exponent.  Coprimality
  cannot lower the group threshold.
* The two pre-expedition `sorry`s stay where they are: `MahlerDriftOne.exists_prime_nonresidue`
  is a prime in `(p/3, p/2)` with prescribed Legendre symbol (Linnik strength — character sums
  over primes at `x ≈ q`, unconditionally out of reach and nowhere near mathlib), and
  `PrimeLambertOscillation.phaseOscillation` is the open analytic obligation of an *open*
  irrationality problem.  Both are on the forbidden-drift list and neither is in a headline cone.

## 🗄️ SUPERSEDED (objective R, **laps 146–160**, 2026-09-15) — R ✅ verdict + **(E) PROVED** + R's three open items all closed

Objective R had its kernel verdict at lap 136 (`G4BalancedRigidity`).  Laps 146–160 closed
everything the R session wrap listed as "still open"; all in `src/NormalNumbers/G4RowVariance.lean`,
every declaration `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).

| item | declaration | status |
|---|---|---|
| (E) weight norms | `sum_abs_released`, `sum_sq_released`, `ratio_released`, `released_row_lower` | ✅ |
| (E) interface | `roughRowVarianceLower_of_released`, `roughRowVarianceLower_arith` | ✅ |
| (E) gap-divisor budget `g` | `card_rough_divisors_le`, `gap_divisor_sum_le` | ✅ |
| (E) at explicit scales | `dyadic_variance_ge`, `dyadic_scales`, `roughRowVarianceLower_dyadic` | ✅ |
| (E) Mertens form (`|S|`-free tail) | `inv_sq_le_telescope`, `sum_inv_sq_rough_le`, `roughRowVarianceLower_mertens` | ✅ |
| (E) non-vacuity | `exists_rough_primes`, `scales_satisfiable` | ✅ |
| verdict with (E) supplied | `dyadic_v_pos`, `two_layers_of_dyadic`, `cancelled_union_le` | ✅ |
| layer count linear in `K` | `layers_of_budget`, `three_eighths_of_budget` (`K′ > (3K−8)/8`) | ✅ |
| R item 2 — a different matrix `A` | `union_le_of_determining` (confinement for any determined invariant) | ✅ |
| R item 3 — grouped sample | `grouped_coeff_le`, `grouped_union_le'` (criterion without logarithms) | ✅ |
| R threshold exact for all `K ≥ 3` | `toggle`, `sum_alt_toggle_zero`, `balanced_of_cube_ignores`, `ptrFun_balanced`, `ptrFun_not_ignoring`, `threshold_exact` | ✅ |

**What this means.**  `Budget.RoughRowVarianceLower` — the single hypothesis the deformation
verdict rested on — is now a *theorem* from explicit arithmetic data on a CRT progression, and
its hypotheses are demonstrably meetable for every `K`, `k`, `Q`.  The chain
*arithmetic of `ω` → variance lower bound → capture budget → cancelled layers → upper density
`≤ dmin^{−H/2}`* is machine-checked end to end.  R's refutation of
"row-balanced ⇒ ignores a coordinate" is now a uniform family (`ptrFun α = α (α 0)`) at every
`K ≥ 4`, not one searched witness.

Nothing here is a claim about the normality of `G₄`.

### A concrete sharpening this opens (lap 162)
`balanced_strictly_stronger` shows balance is *strictly* stronger than `MDF`, and the confinement
(`union_le_of_determining`) consumes only `MDF` via `skel`.  So **any determining set for
row-balance smaller than `skel`** would sharpen the density coefficient of
`Sched.balanced_union_le` directly, with no new confinement proof.  That was the one visible route
to a better exponent than `dmin^{−H/2}` for balanced families.

**Refuted the same lap.**  The natural candidate — the *axis skeleton*
`skel₁ = {α : at most one coordinate nonzero}`, polynomial size `Ks+1` against `skel`'s
`K(s+1)^{K−1}` — fails: `balance_not_determined_by_axes` exhibits
`pairWit α = [α₁ = 1 ∧ α₂ = 1]`, balanced (it ignores coordinate `0`), not identically zero, and
vanishing on all of `skel₁`.  (An exhaustive probe at `K = 3, s = 2` found `15786` colliding
pairs among the `128` `0/1`-valued balanced functions before the clean witness was extracted.)
So the exponential `skel` is not an artifact of routing through `MDF`, and `dmin^{−H/2}` is not
improvable by shrinking the determining set to the axes.

### Refuted, do not retry (laps 163–164)
* Shrinking the determining set for balance to the axis skeleton — `balance_not_determined_by_axes`.
* Counting balanced families more tightly — `PROBE-2026-09-15-balanced-count.md`: the `skel`
  bound is loose only by a constant factor in the exponent, which moves the coefficient and not
  the density rate `dmin^{−H/2}`.

### Next (nothing on the critical path is open)
* The two pre-expedition `sorry`s (`PrimeLambertOscillation.phaseOscillation`,
  `MahlerDriftOne.exists_drift_one_background`) remain on DIRECTION's forbidden-drift list.
* **Answered (lap 161): NO.**  `cube_ignores_not_necessary` — `ex` is balanced yet on the cube
  `c ≡ 1` no coordinate is ignorable (a Python probe first showed `c ≡ 1` is the only such cube
  for `ex`; the Lean proof is `decide`).  So cube-local ignoring is *strictly* sufficient for
  balance, and no strengthening of that criterion characterizes the balance condition — balance
  constrains only the level-set alternating sums.

## 🗄️ SUPERSEDED (after-the-extraction **lap 131**, 2026-09-15) — L1 ✅, L2 ✅, F ✅ (verdict in kernel), W ✅ (withdrawn form) — override STOP condition met

**F verdict (`DESIGN-2026-09-15-deformation.md`): proved limitation of T(K′).**  The deformation
"vary multipliers and offsets jointly, cancel only the first `K′` layers coordinatewise" is
rigid (additive form R3), so its family has `≤ (4M+1)^{(s+1)^{K−K′}(K′(s+1)+2)}` members; with
`K′ ≥ 2` the union over the *whole* family reads upper density `≤ dmin^{−H/2}` at the schedule.
The error budget (draft (6.4)–(6.5), base 4, `η = 2^{−K/4}`) forces `K′ ≥ 3K/8`; the two escape
values `K′ ∈ {0,1}` cost `≥ 2^{K/2}` in the row second moment.  (E) is documented, not
formalized, no axiom.

| item | module | status |
|---|---|---|
| F (R1) `diff_rel`, (R2) `mixed_diff_zero(_t)`, `additive_of_mixed_diff`, (R3) `additive_form` | `G4TensorRigidity` | ✅ clean |
| F (C) `card_family_le`, `family_exponent_le`, (U) `G4Confine.union_card_le` | `G4TensorRigidity` | ✅ clean |
| F 🎯 `Sched.deformation_coeff_le` (coefficient `≤ dmin^{−H/2}`), `Sched.deformation_union_le` | `G4DeformationVerdict` | ✅ clean |
| F (E) rough-error pricing `K′ ≥ 3K/8` | design doc §3 | 📄 documented external estimate |

### Next
* **W** (on slack): `docs/extracted-normal-number-2026-09-15.md`.
* The honest frontier after F (design §4): non-coordinatewise *balanced* cancellation on the
  rows of `D_s^{⊗K}` — does "balanced on every row" force "ignores a coordinate"?  `K = 1` yes.
  A question about the tensor matrix, not `G₄`; not started (F's verdict is what the override
  asked for).

## 🗄️ (after-the-extraction **lap 129**, 2026-09-15) — L1 ✅, L2 ✅

**Objective: `DIRECTION.md`'s ACTIVE "AFTER THE EXTRACTION" override** (L1, L2, then F with
W on slack).  Grind laps do not edit DIRECTION or the brief.

| item | module | status |
|---|---|---|
| L1 `G4Confine.recentring`, `recentring_anchor` (17 vs 15) | `G4ResidualConfinement` | ✅ clean (anchor: no axioms) |
| L1 `G4Confine.physIdx_of_pinned` — `k_α = (a−t_α)/d_α + (D/d_α) q` | same | ✅ |
| L1 `G4Confine.density_bound` — count `≤ L·m(Σd_α)/(2D) + |ι|·m`, hypothesis only `n ≡ t_α (mod d_α)` | same | ✅ |
| L1 `Sched.confinement_at_scale`, `Sched.density_coeff_le` — coefficient `≤ kk·|ι|/(2·dmin^(|ι|−1))`, `|ι| = (K²+1)^K` | same | ✅ |
| L1 prose: `not_dense_of_any_residue` scoped to its re-centred sampler | `G4EntropyResidueProbe` docstrings, wrap footnote | ✅ |
| L2 `Rigidity.const_of_update_invariant`, `offset_rigidity`, `physIdx_translate`, `grid_cancel` | `G4OffsetRigidity` | ✅ clean |

**Numbers for L1 at `i = 0`**: `K = 160000`, `|ι| = (2.56·10¹⁰+1)^160000 > 10^1665000`,
`dmin > 10^6`, so the density coefficient is `< 10^(−10^1665000)`.  The fixed grid at one scale
reads a set of upper density essentially zero, *whatever* the multiplier residues and frozen
classes do — CRT alone pins `n mod D`.

### Lap 131 — W in its withdrawn form (DIRECTION: no `docs/` essay)
One paragraph in the module docstrings of `G4EntropyWStatement` and `G4EntropyWSqueeze`: the
definition of `fullRealW`, density-zero read set (`Sched.density_coeff_le`), positions above
`wLo i` (`wLo_le_fnthW`), and NOT normality of `G₄`.  Re-verified this lap in real output:
`lake build` 🟢 9038 jobs; `deformation_coeff_le`, `deformation_union_le`, `density_coeff_le`,
`offset_rigidity`, `isNormal_two_of_schedule_read` all `[propext, Classical.choice, Quot.sound]`;
`recentring_anchor` no axioms.  **The override's stop condition (F verdict + L1 + L2) is met.**
The honest frontier after F, recorded in `DESIGN-2026-09-15-deformation.md` §4: a non-coordinatewise
(row-balanced) cancellation of the heavy layers — a question about the tensor matrix, needs a new
decision, not a grind lap.

### F design lap (done, lap 130)
`DESIGN-2026-09-15-deformation.md` — choose ONE deformation (L1+L2 force: vary the
multipliers, replace exact coordinatewise cancellation, or control its error) and discharge the
brief's four preconditions on paper with numbers before any Lean.  Then frozen `Prop`
interfaces, transport identity + error term first.

### Open, nothing on the critical path
* `src/` carries exactly the **two** pre-expedition off-path `sorry`s
  (`PrimeLambertOscillation.phaseOscillation`, `MahlerDriftOne.exists_drift_one_background`).

## 🗄️ SUPERSEDED (entropy **lap 128**, 2026-09-15) — 🏁 THE BASE-`2^k` UPGRADE IS **PROVED**

**Read `DIRECTION.md`'s CURRENT DIRECTIVE (lap 126 close) first; it outranks any handoff.  Its
🎯 is now MET — by the successor route of lap 127's E-T13 escalation, not by its own steps 3–4
(step 3 is refuted; see `ROUTE-ESCALATION-2026-09-15-base2k-step3.md`).  E-T7 applies: this lap
does not pick the next target; an altitude lap does.**

| theorem | module | trust triple |
|---|---|---|
| `PowerBase.tendsto_resCount` | `PowerBaseLimit` | clean |
| `PowerBase.isNormalSequence_pow` | `PowerBaseBlock` | clean |
| `PowerBase.isNormal_pow` — `IsNormal b x → IsNormal (b^K) x` | `PowerBaseReal` | clean |
| 🎯 `G4.Sched.isNormal_four_fullRealW` — **`IsNormal 4 fullRealW`** | `PowerBaseReal` | clean |
| 🎯 `G4.Sched.isNormal_two_pow_fullRealW` — **`IsNormal (2^k) fullRealW`**, `k ≥ 1` | `PowerBaseReal` | clean |

The route is strictly more general than the directive asked: `isNormal_pow` holds for **every**
base and **every** normal number, with no Wall, no Fourier, no Maxfield, no measure theory —
`BlockRigidity.Sys.eq_uniform` (ergodicity of the Bernoulli shift, by two Cauchy–Schwarz steps on
a finite energy) plus an ultrafilter compactness argument.

Small supporting change: `BlockRigidity.Sys.shift` now carries `k < b ^ m` (every call site
already had the bound); this is what lets the ultrafilter limit `G` serve as `F` with no
mod-`b^m` reindexing.

### Retired with this lap
The lap-126-close steps 2–4 ("parity ↔ offset classes", "transport to the read", "the digit
bridge"): step 2 was proved (`G4EntropyResidue.abs_posAvgRes_sub_le`, kept), step 3 is **refuted**
(the local class alternates with the window index `b` because `kk i` is odd for odd `i`, and the
compensating index is the sorted *rank*, which the certificate cannot see), and step 4 is
subsumed by `blockOf_digitOf` in `PowerBaseReal`.

### Open, nothing on the critical path
* `src/` carries exactly the **two** pre-expedition off-path `sorry`s
  (`PrimeLambertOscillation.phaseOscillation`, `MahlerDriftOne.exists_drift_one_background`).
* The Aristotle line-by-line diff of job `48c7d703-d18e-4e47-ae9c-6734f6737047` (cheap, optional).

## 🗄️ SUPERSEDED (entropy **lap 126 close**, 2026-09-15) — THE BASE-`2^k` UPGRADE

**Read `DIRECTION.md`'s CURRENT DIRECTIVE (lap 126 close) first; it outranks any handoff.**

🏁 The base-two objective is **MET**: `isNormal_fullRealW : IsNormal 2 fullRealW`, axiom-clean.
The successor is the natural strengthening of the *same* object:
**`IsNormal 4 fullRealW`, then `IsNormal (2^k) fullRealW`.**

### The finding that opens it (probe run and PROVED this lap)

`abs_posAvg_sub_le` is not a monolithic average.  Its proof splits the `m − ℓ + 1` window
positions into the **`ℓ` offset classes** `p ≡ r (mod ℓ)` — `posEquiv` is literally
`(r, j) ↦ r + jℓ` — certifies each class *separately*, and only then sums.  Extracted and
generalised in `G4EntropyOffsetClass.lean` (both axiom-clean):

* **`abs_offset_class_le`** — each class `r` on its own obeys `|classSum − 2^{−ℓ}·classCard| ≤
  B·classCard` with `B = 2√(log2·ℓδ/(m − ℓ + 1))`, the *same* `B` as the full average.
* 🎯 **`abs_posAvgR_sub_le`** — therefore the average over **any** sub-family `R : Finset (Fin ℓ)`
  of classes obeys the same bound `B`.

> Consequence: restricting to positions of a fixed residue mod `k` costs **nothing** — not a
> factor `√k`, not even a constant — whenever `k ∣ ℓ`.  A base-`2^k` word of length `ℓ'` is a
> binary word of length `ℓ = kℓ'`, so `k ∣ ℓ` always holds where it is needed.

### Next, in order

2. **Parity ↔ offset classes.**  For `k ∣ ℓ` and `c < k`, the positions `p < m − ℓ + 1` with
   `p ≡ c (mod k)` are exactly `⋃ {class r : r ≡ c (mod k)}`; state it against `posEquiv`
   (`toFun (r,j) = r + jℓ`, so `p ≡ r (mod k)` since `k ∣ ℓ`).
3. **Transport to the read.**  Parity-restricted analogues of the `bandWLaw` chain,
   `abs_prefix_ratio_sub_le_cap`, `tendsto_fullWRead_freq`, `abs_ratio_mid_le`.  In window `a` of
   band `i` the needed class is `q ≡ (fTW i + a·kk i) (mod k)` — it depends on `a`, but **every**
   class carries the same bound, so this costs nothing.
4. **The digit bridge** — `digitOf (b^k) y j` in terms of `digitOf b y (k·j + t)` (new,
   `Bridge`-level), then `IsNormal 4 fullRealW`, then general `k`.

### ⛔ STEP 3 IS REFUTED (lap 127) — read `ROUTE-ESCALATION-2026-09-15-base2k-step3.md`

Steps 1, 2 and the whole counting layer are PROVED and kept (`G4EntropyOffsetClass`,
`G4EntropyResidue`, `G4EntropySubLaw`, `G4EntropyResRead`).  Step 3 fails: for a fixed READ class
the local class inside window `b` is `locRes i k c b`, which alternates with `b` because
`kk i = 40000 + i` is odd for odd `i`; and `{b : b ≡ e (mod k)}` is neither a sample-time set nor
a coordinate set (window index = sorted RANK of `2(n − t_α)/d_α` over `bandW i ×ˢ Atoms`), so the
entropy machinery cannot price it.  Certified: `∑_b N_b(r)` for each FIXED `r`, and the sum over
classes — two equations, four unknowns.

### 🎯 THE SUCCESSOR ROUTE (elementary, and the heart is already in kernel)

`NormalNumbers/BlockRigidity.lean` — **`Sys.eq_uniform`, axiom-clean**: a density system on
base-`b` words that refines on the right, closes up under `K` prepends, and is dominated by
`C·b^{−m}`, IS the uniform one.  Elementary: energy `A m = ∑_k b^m (F m k)²` is bounded with
nonneg increments `Var m`, and the shift relation gives `Var m ≤ Var (m+K)`; a summable sequence
nondecreasing along each class mod `K` vanishes.  (= ergodicity of the Bernoulli shift, with no
measure theory.)

Next, in order:
1. the ultrafilter/density layer: for `d` normal in base `b` and `g ≤ atTop` an ultrafilter, the
   class densities `F m k = lim_g (K/n)·#{p<n : p ≡ 0 mod K, word at p}` satisfy `Sys b K K F`;
2. `tendsto_iff_ultrafilter` ⇒ the densities converge to `b^{−m}` ⇒
   **`IsNormal b y → IsNormal (b^K) y`**;
3. corollaries off `isNormal_fullRealW`: `IsNormal 4 fullRealW`, `IsNormal (2^k) fullRealW`.

### Do not retry
* Wall + Maxfield as the route to base `2^k`.  It is a genuinely harder classical theorem: u.d. of
  `(b^n x)` does **not** formally give u.d. of `(b^{kn} x)`, and the Fourier route only yields
  `μ̂(hb) = −μ̂(h)`-type periodicity, not vanishing.  The offset-class route above is strictly
  easier *here* because we own the entropy certificate.

---

## 🗂️ SUPERSEDED ACTIVE (entropy **review lap 126 opening**, 2026-09-15) — THE SQUEEZE AND THE ENDPOINT

**Read `DIRECTION.md`'s CURRENT DIRECTIVE (lap 126) first; it outranks any handoff.**

Lap 122's steps 1–3 are DONE (laps 123–125): `G4EntropyWPrefix`, the sandwich +
`abs_prefix_ratio_sub_le_cap` (no upper hypothesis; flanks capped at `wTop i`), and
`head_frac_tiny` on the new `G4GridP0Lower.P₀_growth`.  **One obligation is left.**

### The attack path (concrete, do not re-derive)

For `fTW i ≤ n < fTW (i+1)`, `i ≥ 1`; `T := fTW i`, `s := n − T`, `a := s / kk i`,
`G := winCount v T`, `D := winCount v n − G`, `r := 2^{−ℓ}`, `F := kk i − ℓ + 1`.

1. **`G4EntropyWMediant.lean` — the mediant lemma** (schedule-free, `ℝ`):
   `(r−e₁)T ≤ G ≤ (r+e₁)T`, `(r−e₂)s ≤ D ≤ (r+e₂)s`, `0 < T`, `0 ≤ s`
   ⇒ `|(G+D)/(T+s) − r| ≤ max e₁ e₂`.  Pure algebra: `(G+D) − r(T+s) = (G−rT) + (D−rs)`.
2. **`G4EntropyWSqueeze.lean` — the band-`i` increment.**  `winCount_split` at `T`;
   `fullW_prefix_winCount_bounds x i a v` gives
   `fullGoodWPre i a ≤ winCount v (T + a·kk i) ≤ fullGoodWPre i a + T + a·ℓ`;
   the partial window costs `≤ kk i` (`winCount` monotone, increments `≤ n−m`);
   `s ∈ [a·kk i, (a+1)·kk i)`.
3. **Gated branch** (`8·wFloor i ≤ cutLo i c`, `c := fnthW i (a−1)`, `a ≥ 1`): `aLe_fnthW`
   turns the read index into the cutoff (`aLe i c = a`), then `abs_prefix_ratio_sub_le_cap`
   gives `|fullGoodWPre i a/(a·F) − r| ≤ ε_i + 128/K_i`; `F/kk i = 1 − O(ℓ/kk i)` converts to
   `|D/s − r| ≤ ε_i + 128/K_i + O(ℓ/kk i)`.
4. **Ungated branch**: `aLe_le_headW` gives `a ≤ headW i`, and `head_frac_tiny` gives
   `a·kk i·KK i ≤ T`, so `s ≤ T/KK i + kk i` and directly
   `|(G+D)/(T+s) − r| ≤ |G/T − r| + 2/KK i` (use `D ≤ s`, `G/(T+s) ≥ (G/T)(1 − 1/KK i)`).
5. **The limit.**  `|winCount v n/n − r| ≤ |winCount v (fTW i)/fTW i − r| + midErr i` at
   `i = fgrpW n`; `fgrpW n → ∞` (`self_le_fTW`, `lt_fTW_fgrpW_succ`); the first term → 0 by
   `tendsto_fullWRead_freq` at `i−1`; `midErr i → 0`.  `n < fTW 1` by `eventually_ge_atTop`.
6. **The endpoint.**  `isNormalSequence_of_tendsto_winCount` →
   `IsNormalSequence 2 (fullDigW (primeLambertAtBase 4))`; then `properDigits_fullDigW`,
   `fullRealW`, `Bridge.isNormal_realOfDigits` → **`IsNormal 2 fullRealW`**.
   (`properDigits_fullDigW`, `fullRealW` do not exist yet; `exists_matchesAt_fullDigW` needs a
   wide non-vacuity witness.)

### Progress (lap 126)

Steps 1–4 of the attack path are **PROVED**, axiom-clean:

* `G4EntropyWMediant` — `mediant_abs_le`, `mediant_abs_le_max`, `mediant_abs_le_trivial`.
* `G4EntropyWSqueeze` — `winCount_mono`, `winCount_sub_le`, `one_le_headW`,
  **`kk_mul_KK_le_fTW`** (`head_frac_tiny` at `a = 1`: ONE read window is a `1/KK` fraction of the
  history — this is what makes the head, the partial window and the `a = 0` stub all cost
  `O(1/KK)`), `incr_bounds`, `mid_gated_core`, `mid_trivial_core`, `mid_assemble_gated`,
  `mid_assemble_trivial`, and 🎯 **`abs_ratio_mid_le`**.

**The threshold that makes the three branches close** (record it — it is not in the directive):
split on `a` vs `A := Nat.sqrt (KK j)`.
* `a ≤ A` — trivial bound; `s < (a+1)·kk ≤ (A+1)·kk`, so `s·A ≤ (A²+A)·kk ≤ 2·kk·KK ≤ 2T`, error `2/A`.
* `a > A`, gate holds — certified; the leftover `2E/s = 2aℓ/s + 2kk/s ≤ 2ℓ/kk + 2/a ≤ 2ℓ/kk + 2/A`.
* `a > A`, gate fails — trivial again, via `aLe_le_headW` + `head_frac_tiny`: `s·KK ≤ 2T`.
A *fixed* threshold does not work: at `a = 1` the certified branch's leftover `2·kk/s` is `O(1)`.
Hence `midErrW i ℓ = 2√(808 log2·ℓ/√(KK i)) + 128/KK i + 2ℓ/kk i + 2/⌊√(KK i)⌋`.

**Still open (2 leaves):** `tendsto_midErrW` (needs `Nat.sqrt (KK i) → ∞`) and
`tendsto_winCount_fullDigW` (the limit at every `n`: `fgrpW n → ∞`, `tendsto_fullWRead_freq` at
`i−1`, `eventually_ge_atTop` for `n < fTW 1`), then step 6, the endpoint.

### Refuted, do not retry
* `Mprod = ∏_α d_α²  ≥ gridQ^{2|Atom|}` and the primorial as routes to a `P₀` **lower** bound
  (lap 125 §1: `log Mprod(K+4) ≈ K^{6K}` against `log P₀(K) ≳ K^{8K}`).
* `abs_prefix_ratio_sub_le`'s **upper hypothesis** `cutHi i c ≤ wTop i` — genuinely false for the
  top `O(1/K)` of each band.  The cap (`cutBot`/`cutTop`) is the fix; `abs_prefix_ratio_sub_le_cap`
  is the statement to use.

---

## 🗂️ SUPERSEDED ACTIVE (entropy **review lap 122**, 2026-09-15) — MID-BAND PREFIX CONTROL

**Read `DIRECTION.md`'s CURRENT DIRECTIVE first; it outranks any handoff.**

### Where the headline stands

`fullPosW` (`G4EntropyFullSeqW`) is a `StrictMono`, schedule-only read of `G₄`'s binary digits;
`tendsto_fullWRead_freq` gives every binary word its correct frequency **at the band cutoffs
`fTW (i+1)`**.  `IsNormalSequence 2` quantifies over **all** `n`.  So exactly one obligation is
left: the read ratio at an arbitrary read index.

### Why it is not a corollary of `abs_posAvg_bandWLaw_le` — and how it closes

The read consumes band `i`'s distinct window starts *in increasing order*, so a read index cuts
the band at a **position** threshold `c`.  A start is `2·kIdx(gridAt i) n α` with
`d_α·kIdx(n,α) ≤ n < d_α·(kIdx(n,α)+1)`, so `2·kIdx(n,α) ≤ c` means `n ≲ c·d_α/2` — the cutoff
**depends on the atom**, and the consumed set is not a truncated sample.

`gridOf.mul_d_le_mul_d` (`K·d_β ≤ (K+1)·d_α`) and `G4EntropyMultiplierSpread.kIdx_cross` bound the
spread by `1/K`, so with `X₁ := ⌊c·d_min/2⌋`, `X₂ := ⌈d_max·(c+2)/2⌉`:

> `bandWtr i X₁ ×ˢ univ  ⊆  pairsLe i c  ⊆  bandWtr i X₂ ×ˢ univ`,  `X₂/X₁ ≤ (K+1)/K·(1+2/c)`.

Both flanks are honest truncations at scales inside `[Xlo (KK i), Xlo (KK (i+1))]`, both certified
by `H₂_bandWLaw_ge` / `abs_posAvg_bandWLaw_le`.  The sandwich costs a **relative `O(1/K)`**, against
a capture error already `O(K^{−1/4})`.  Arithmetic of the sandwich (record so it is not re-derived):

```
Σ_{X₁} ≤ Σ_{pairsLe c} ≤ Σ_{X₂}                        winOcc ≥ 0
Σ_{X₂} ≤ (2^{−ℓ}+ε)·|bandWtr X₂|·|Atom|·F              abs_posAvg_bandWLaw_le at X₂
|pairsLe c| ≥ |bandWtr X₁|·|Atom|                       lower inclusion
⇒ ratio ≤ (2^{−ℓ}+ε)·(1+δ),  δ := |bandWtr X₂|/|bandWtr X₁| − 1 = O(1/K)
⇒ ratio ≥ (2^{−ℓ}−ε)·(1−δ)   symmetrically
```

`δ = O(1/K)` needs `X₁ ≥ 4·wFloor i` (the gate), which is what makes step 3 necessary.

### Landed (grind laps after 122)

```
G4EntropyWSandwich   two_kIdx_le_of_lt_cutLo, lt_cutHi_of_two_kIdx_le   THE TWO INCLUSIONS
                     cutLo/cutHi, flank_gap, cutLo_le_cutHi
                     card_bandWtr_add, card_bandWtr_{le,ge}_real
                     KK_le_Xlo, KK_mul_P₀_le_Xlo, KK_mul_{P₀,dRef}_le_wFloor
                     card_flank_ratio   K·|bandWtr cutHi| ≤ (K+16)·|bandWtr cutLo|
G4EntropyWPrefix     fnthW_surj/_mono'/_le_iff, startsLe, aLe, idxLe, idxLe_eq_range,
                     startsLe_eq_image   THE READ-INDEX ↔ POSITION-THRESHOLD BRIDGE
                     fullGoodWPre, fullGoodWPre_eq,
                     fullW_band_prefix_winCount_bounds, fullW_prefix_winCount_bounds
G4EntropyFullSeqW    card_badWPairs_le_real   (extracted from overhangW_le_real, no change)
G4EntropyWTrunc      startsOf, sum_pairs_eq_gen, card_startsOf_le, sum_pairs_sub_le_gen,
                     overhang_gen_le, overhang_gen_le_real   the multiplicity bridge GENERIC in
                                                             the pair collection T ⊆ bandWPairs i
                     pairsLe, startsOf_pairsLe,
                     prod_cutLo_subset_pairsLe, pairsLe_subset_prod_cutHi   THE PRODUCT FLANKS
```

**Next**: the certified count at a truncated scale — the generic `posAvg_bandWLaw_eq_digits` at
`X'` (the `bandWLawTop` proofs are already `X'`-generic in content), then the sandwich
`Σ_{cutLo flank} ≤ Σ_{pairsLe} ≤ Σ_{cutHi flank}` and the read-ratio bound at a mid-band cutoff.

All trust-triple clean.  Route trigger **E-T11 did NOT fire**: the bracket exists in-kernel.

### Lap 124 — **`head_frac_tiny` is PROVED**; the active crux has no open leaf

```
G4GridP0Lower      gridQ_le_dist      same-layer shifts differ by a nonzero multiple of Q
                   distProd_ge, P₀_ge_pow      P₀ ≥ Q^{T(H−1)}          THE LOWER BOUND
                   P₀_le_pow_gridQ             P₀ ≤ Q^{7T²}
                   gridSum/gridB/gridUmax/gridQ_mono, gridDm_le_gridQ_sq,
                   two_gridT_succ_le_gridQ, gridH_le_gridUmax, mul_self_pred_le_factorial
                   exponent_growth             T'(H'−1) ≥ 7T² + 3
                   P₀_growth   256·(K+4)²·Dm(K+4)·H(K+4)·P₀ K ≤ P₀ (K+4)
G4EntropyWHead     gridOf_congr, gridAt_succ_eq, head_growth, sq_succ_le_two_pow,
                   head_junk_le_Xlo, head_slack, head_core
                   head_frac_tiny   ✅ no longer a sorry
```

The handoff's guessed route (`Mprod ≥ gridQ^{2|Atom|}`) does **not** work: `log Mprod(K+4) ≈
K^{6K}` loses to `log P₀(K) ≈ K^{8K}`, and the primorial fallback (`2^{2T'}`) loses too.  What
works is that `freezeQ` counts **pairs**: its shift-difference product has `T(H−1)` factors that
are each a nonzero multiple of `Q`, and `T(K+4)² ≥ K^{16}·T(K)²`.  Recorded so the dead route is
not retried.

**Remaining on the headline:** `DIRECTION` item 4 — the squeeze and the endpoint
(`IsNormalSequence 2 (fullDigW …)` → `IsNormal 2 fullRealW`), per lap 123's "Next lap" item 2.
`exists_matchesAt_fullDigW` still needs a wide non-vacuity witness.

### Lap 125 (in progress) — item 4, the squeeze

`G4EntropyWCap.lean` (landed): `abs_prefix_ratio_sub_le` **with no upper hypothesis**.
`cutHi i c ≤ wTop i` fails for the top `O(1/K)` of every band (a start is `c ≤ 2n/d_α`, so
`cutHi ≈ wTop·(1+2/K)`), so both flanks are capped at the tile top:
`cutBot = min (cutLo) (wTop)`, `cutTop = min (cutHi) (wTop)`.  Both inclusions survive
(`pairsLe ⊆ bandWPairs` already forces `z.1 < wTop`), and `card_flank_ratio_cap` is a case
split: below the cap it is the old statement, above it both flanks are `bandWtr i (wTop i)`.

**Next (the squeeze proper).**  For `fTW i ≤ n < fTW (i+1)`, `i ≥ 1`, put `a := (n − fTW i)/kk i`
and `T := fTW i`, `G := winCount v T`, `D := winCount v n − G`, `s := n − T`:
* `fullW_prefix_winCount_bounds` bounds `D` by `fullGoodWPre i a ± (a·ℓ + kk i)`;
* gated (`8·wFloor i ≤ cutLo i (fnthW i (a−1))`): `abs_prefix_ratio_sub_le_cap` +
  `aLe_fnthW` give `|D/s − r|` small;
* ungated: `aLe_le_headW` + `head_frac_tiny` give `s ≤ T/KK i`, and then
  `|(G+D)/(T+s) − r| ≤ |G/T − r| + 1/KK i` directly;
* the mediant lemma `|(G+D)/(T+s) − r| ≤ max(|G/T − r|, |D/s − r|)` closes both.
Then `|g n − r| ≤ |g (fTW (fgrpW n)) − r| + midErr (fgrpW n)`, and `fgrpW n → ∞`, so the
band-end limit `tendsto_fullWRead_freq` transfers to all `n`.

### Landed since (grind laps, 2026-09-15)

```
G4EntropyWCount      posAvg_bandWLaw_eq_count/_eq_digits at a GENERAL gated X'
                     abs_occ_bandWtr_sub_le   the packaged capture estimate at any flank
                     pairCount_prod_eq        the triple count over any sample set
G4EntropyWOverhang   card_Atom_sq_le_PKtr     |Atom|² ≤ |PKtr i X'| at every gated scale
                     badPairsAt, overhang_gen_le_at, card_badPairsAt_le_real,
                     overhang_gen_le_band     ov T ≤ 8·|bandWtr i X'| — the overhang charged
                                              against the FLANK's own scale, not the band's
G4EntropyWMid        mid_core_lower/_upper/mid_ratio_arith   the ratio arithmetic, closed form
                     gate_cutLo/gate_cutHi, fullGoodWPre_eq_startsOf, sum_pairsLe_sandwich,
                     abs_flank_sum_sub_le, card_pairsLe_ge/_le, aLe_ge_real/aLe_le_real,
                     bandWtr_mono, fullGoodWPre_le
                     🎯 abs_prefix_ratio_sub_le   MID-BAND PREFIX CONTROL, THE CRUX
G4EntropyWHead       aLe_fnthW (read-index ↔ cutoff, both ways), cutHi_le_of_ungated,
                     headW, aLe_le_headW
                     ⚠️ head_frac_tiny — THE ONE OPEN LEAF (see below)
```

**The crux is closed.**  `abs_prefix_ratio_sub_le` (all trust-triple clean):

> `|fullGoodWPre i (aLe i c) x v / (aLe i c · (kk i − ℓ + 1)) − 2^{−ℓ}| ≤ ε_i + 128/K_i`

at every position cutoff above the gate `8·wFloor i ≤ cutLo i c`.  Route trigger **E-T11 did not
fire**.

### ⚠️ The one open leaf — `head_frac_tiny`

`headW i · kk i · KK i ≤ fTW i` (stated at `i+1`; band 0 has no history and does not affect the
limit).  The head is a bounded multiple of the floor in sample-time scale
(`cutHi_le_of_ungated`), so it consumes `≈ 16·wFloor_i·|Atom_i|/P₀_i` windows; against
`fTW i ≥ fLW (i−1) ≥ Xlo (KK i)·kk_{i−1}/(4·P₀_{i−1})` and `wFloor i = 4·gridDm_i·Xlo (KK i)` the
`Xlo (KK i)` cancels and what is left is

> `256·gridDm_i·|Atom_i|·kk_i·P₀_{i−1} / (P₀_i·kk_{i−1})`.

**What is missing is a LOWER bound on `P₀`.**  The repo carries only upper bounds (`P₀_le`,
`P₀_le_two_pow`, `logP₀Nat_le_two_pow`) — every estimate in the E0 cone wants `P₀` small.  Closing
the leaf needs `P₀_i = Mprod_i·freezeQ_i ≥ gridDm_i·|Atom_i|·kk_i·P₀_{i−1}·K_i/kk_{i−1}`, i.e. one
of:
* a Chebyshev-type lower bound on the primorial `∏_{p ≤ 2|Idx|} p` with `|Idx| = (K²+1)^K·N(K)`
  (mathlib has `Nat.primorial_le_4_pow`, the upper bound; the lower one is not there), or
* a lower bound on `Mprod = ∏_α d_α²` — i.e. on the multipliers `d_α = mult B Q D₀ α`, which are
  `≡ 1 mod gridQ`, so `d_α ≥ gridQ + 1` unless `d_α = 1`; **this looks like the cheap route** —
  check whether `mult` is ever `1`, and if not, `Mprod ≥ gridQ^{2|Atom|}` closes it against
  `P₀_{i−1} ≤ gridP₀Bound (K−4)` by a pure exponent comparison.

Everything else in the headline is now above this leaf.

### Open, in order (review lap 122)

1. ✅ **`G4EntropyWPrefix.lean` — the prefix read count.**  DONE.
   * `startsLe i c := (winStartsW i).filter (· ≤ c)`,  `aLe i c := (startsLe i c).card`
   * `image_fnthW_range`: `Finset.image (fnthW i) (Finset.range (aLe i c)) = startsLe i c`
     (order-embedding: `q ≤ fnthW i (a−1) ↔ ∃ b < a, q = fnthW i b`)
   * `fullGoodWPre i a x v := ∑ b ∈ range a, |{q < kk i − ℓ + 1 : OccursAt 2 x v (fnthW i b + q)}|`
   * `fullW_band_prefix_winCount_bounds` / `fullW_prefix_winCount_bounds`: verbatim
     `fullW_band_winCount_bounds` / `fullW_winCount_bounds` with `range a` for
     `range (winStartsW i).card` and `Ico (fTW i) (fTW i + a·kk i)`.
2. **`G4EntropyWPrefixSandwich.lean` — THE CRUX.**  `pairsLe i c := (bandWPairs i).filter
   (fun z => 2·kIdx (gridAt i) z.1 z.2 ≤ c)`; the two inclusions with explicit `X₁ X₂`;
   `card_bandWtr_ratio`; the truncated overhang (`card_multi_atom_le_real_at` is already
   scale-generic).
3. **`head_frac_tiny` — the ungated head.**  For `c` below the gate, bound band `i`'s read
   trivially and absorb into `fTW i`: `fLW (i−1) ≥ |bandW (i−1)|·kk (i−1)`,
   `wTop (i−1) = Xlo (KK i)`, so `Xlo (KK i)` cancels and what remains is
   `16·gridDm_i·|Atom_i|·kk_i·P₀_{i−1}/(P₀_i·|Atom_{i−1}|·kk_{i−1})`, astronomically small because
   `m ≥ K³ ≫ 21K²`.  Imitate `granuleW_exceeds_previous_scale`.
4. **The squeeze and the endpoint.**  `winCount` monotone in `n` ⇒ control at the cutoffs
   `fTW i + a·kk i` suffices (partial window costs `kk i`, and `kk i / fTW i → 0`).  Then
   `IsNormalSequence 2 (fullDigW …)`, `properDigits_fullDigW`, `fullRealW`,
   **`IsNormal 2 fullRealW`**.  (`exists_matchesAt_fullDigW` needs a wide non-vacuity witness.)

### Deliberately not ported

`isSampled_fullPos` — `IsSampled` is pinned to `sampledPos … (X (KK i))` and the wide read visits
sample times above it.  A density remark, not an input to normality.

## 🗂️ SUPERSEDED ACTIVE (entropy **review lap 119**, 2026-09-14) — the two-dimensional `(K, j)` ladder

**Read `DIRECTION.md`'s CURRENT DIRECTIVE first; it outranks any handoff.**

### The course correction

Laps 61–118 diagnosed the blocker to `IsNormal 2 fullReal` as the **head of each band** — cutoffs
below the certificate floor `Xlo (KK i)` — and `G4EntropyScaleGap` proved no rung covers it
(`Xhi K k₄ + 1 < Xlo (K+4)`, tower-separated).  The truncated-scale work (laps up to `bbeb413`)
then pushed the bad fraction of each band from `K^{−1/2}` down to `X^{−1/2}`, and the handoff
concluded normality was blocked on this mechanism.

**It is not.**  The audit this lap of every `m`/`m₁`-sensitive hypothesis in `entropy_E0`'s cone
shows the gap is an **artifact of pinning `m` to `K`**:

| declaration | how `m₁`/`m` enters | under `m₁ → m₁ + j` |
|---|---|---|
| `dyadic_factor_le` | only through `m − m₁ = m₂` | **unchanged** |
| `sample_term_le`, `log_Mx_div_le` | `K ≤ 2^m`, `Y²P₀·4 ≤ X`, `Mx ≤ 2X = 2Y^{100}` | improve / constant `≤ 101` |
| `m₁_ge_cube`, `twentyone_sq_le_m`, `logP₀Nat_le_two_pow_m`, `two_mul_P₀_le_X`, `gridDm_le_X`, `J_mul_gridDm_le_X` | lower bounds on `m` | improve |
| budget main term (`hm₁`) | `(1/8)^K·m₁ = 1000·K·r`, used as a lower bound | improves |
| **`Mc_le_two_pow_m₂`** | `Mc = 10⁵·T·m₁ ≤ 2^{8K²}` | ⚠️ real ceiling, `j ≲ 2^{8K²}/(10⁵TK)` |
| **`four_mul_le_four_pow_N`** | `4K(logP₀Nat + m + 2J + 13) ≤ 2^{200K²}` | ⚠️ real ceiling, `j ≲ 2^{200K²}/(4K)` |

Both ceilings clear `jstar K = m (K+4) − m K − 1` with a factor-`K/log K` margin.  And raising
`m₁` by one **squares `Y`**, so `Xlom K (j+1) = Y_{j+1}^{50} = Y_j^{100} = Xm K j`: contiguous
tiling, no gap.  **A0's NO does not apply** — A0 raised `X` with `Y, R, Mc` fixed (so
`log Mx / log Y` broke its `Y^{2^{3K/4}}` ceiling); the march raises all of them together.

### Proved this lap — `G4EntropyMTower.lean`

```
mm₁, mm, Rm, Ym, Xm, Xlom, Mcm            the marched scales;  j = 0 is the old schedule
Xlom_succ          Xlom K (j+1) = Xm K j                 THE TILING IDENTITY
jstar K            = m (K+4) − m K − 1
Xm_jstar           Xm K (jstar K) = Xlo (K+4)            reaches the next rung EXACTLY
Mcm_le_two_pow_m₂  Mcm K j ≤ 2^{m₂ K}   for j ≤ jstar K  (binding: 6K²+31K+81 ≤ 8K²)
four_mul_le_four_pow_N_m                 the hfar ℕ inequality on the whole march
exists_tile        ∀ X' ∈ [Xlo K, Xlo (K+4)], ∃ j ≤ jstar K, Xlom K j ≤ X' ≤ Xm K j
entropy_E1_march_zero   the j = 0 instance IS `entropy_E1_down`   ← definitions line up
entropy_E1_tile    E1 at EVERY outer scale in [Xlo K, Xlo (K+4)]  ← THE GAP CLOSED
```

All trust-triple clean except `entropy_E1_tile`, which is honestly gated on the one named leaf.

### Proved 2026-09-15 (grind laps after 119)

```
G4EntropyMTowerHarmonic   sum_inv_smallPrimes_{ge,le}_gen   Mertens, generic in the cutoff exponent
G4EntropyMTowerBudget     smallPrime_term_tiny_down_m       the five terms at (Rm, Mcm), downward
G4EntropyMTowerDown       hbig_small_down_m, hfar_small_down_m
G4EntropyMTowerAssembly   entropy_E1_march  ✅ PROVED       →  entropy_E1_tile is a THEOREM
G4EntropyBandTrunc        card_bandTtr_ge   ✅ PROVED       (m_step_seven, band_gap_strong_Xlo)
G4EntropyBandHead         bandLoH, bandTH, card_bandTH_ge, Xlo_le_of_mem_bandTH,
                          bandTop_le_bandLoH, head_gate
```

All trust-triple clean.  **No `sorry` remains in the expedition's part of `src/`.**

### The design change that `entropy_E1_tile` unlocks — `bandLoH`

Item 3's `density_antitone` and item 4's level-switch were designed to pay for an *uncertified
head*.  With the raised floor there is no head to pay for:

> **`bandLoH i := 2·Xlo (KK i)`.**  `bandLo` is a free design parameter.  Raising it to twice
> the level-`i` certificate floor makes every sample time of the band satisfy
> `n ≥ gridDm·2·Xlo (KK i) ≥ Xlo (KK i)` (`Xlo_le_of_mem_bandTH`), so **every** mid-band
> truncation `X'` is inside `G4EntropyBandTrunc`'s certified range and the truncated chain
> (`H₂_bandTLawTr_ge`, `abs_posAvg_bandTLawTr_le`) applies at it.

Nothing is lost: the raised band still keeps half the sample (`card_bandTH_ge`), because
`X (KK i) = Xlo (KK i)²` — the dropped stretch is the *square root* of the range and the gate
`8·gridDm·Xlo + 4P₀ ≤ X` has `2^{49·2^m}` to spare (`head_gate`); and the raised floor still
clears the previous band's ceiling (`bandTop_le_bandLoH`, exponents `100·2^{m_i}` vs
`50·2^{m_{i+1}} ≥ 6400·2^{m_i}`), so the read stays strictly increasing.  The cost is a skipped
*position* gap between `bandTop i` and `bandLoH (i+1)`, which is harmless — the read was already
a density-zero subsequence (`tendsto_density_fullPos`).

`density_antitone` is therefore **not needed** on this route and is withdrawn as an objective.

### Open, in order (revised 2026-09-15)

0. **`fullPos'` on the raised band.**  Re-run `G4EntropyFullSeq`'s construction with `bandTH`
   in place of `bandT`: `winStartsH`, `fnthH`, `fLH`, `fTH`, `fullPosH`, `fullDigH`.  The
   window-gap and overhang arguments are `bandLo`-free and port verbatim; what changes is the
   count lemma (`card_bandTH_ge` for `card_bandT_ge'`) and the floor lemma
   (`bandLoH_le_pos_of_mem_bandTH` for `bandLo_le_pos_of_mem_bandT`).
0b. **Mid-band prefix control.**  For a cutoff `a` inside band `i`, the read's first `a` window
   starts are those of `bandTtr`-style truncation at `X' = ` (the `a`-th sample time), and
   `Xlo_le_of_mem_bandTH` puts `X'` above the floor, so `abs_posAvg_bandTLawTr_le` applies
   with **no** restriction price.  Then `IsNormalSequence 2 (fullDigH …)` and
   `Bridge.isNormal_realOfDigits`.

### Superseded (kept for the record) — the pre-`bandLoH` plan

1. **`Sched.entropy_E1_march`** (the leaf).  Port the cone to `(K, j)`, mirroring
   `G4EntropyE0Down`/`G4EntropyE1Down`'s verbatim-copy-plus-substitution:
   * ✅ **DONE** (`G4EntropyMTowerBig.lean`): `hbig_holds_m` — and `dyadic_factor_le_m` is the
     original *verbatim*, exactly as the audit predicted, because `mm − mm₁ = m₂ K` by definition
     of the march.  Supporting: `X_le_Xm`, `two_mul_P₀_le_Xm`, `gridDm_le_Xm`,
     `J_mul_gridDm_le_Xm`, `sample_nonempty_m`, `K_le_two_pow_mm`, `P₀_le_two_pow_m`,
     `natLog_Ym`, `natLog_Rm`, `sample_term_le_m`, `log_Mx_div_le_m` (`≤ 101`, a constant —
     the A0 ceiling is never approached).
   * ✅ **DONE**: `hfar_holds_m`, via `farC_le_m` and `four_mul_le_four_pow_N_m`.
   * the five `smallPrimeBound` terms — `Mcm_le_two_pow_m₂` in place of `Mc_le_two_pow_m₂`;
     `R_pow_two_Mc_le` becomes `Rm^{2Mcm} ≤ 2^{10·2^{mm}}` by the same two-line argument.
   * `hm₁`'s equality becomes `1000·K·r ≤ (1/8)^K·mm₁ K j` (only improves).
   Then `entropy_E0_m`, `entropy_E1_m`, and the downward run to `Xlom K j`.
2. **`Sched.card_bandTtr_ge`** (carried leaf, `G4EntropyBandTrunc`).  `4·Dm·bandLo i + 4P₀ ≤
   Xlo (KK i)` via `gridDm_le_Xlo`, `two_mul_exp_le_Xlo`, `logP₀Nat_le_two_pow_m`, `Xlo_cast`.
3. **`density_antitone`** — `d_K·|Atom_K|·kk_K/P₀ K ≥ d_{K+4}·|Atom_{K+4}|·kk_{K+4}/P₀ (K+4)`.
   Ladder: `log P₀ ≈ K^{20K+17}` against `log d ≈ W log W ≈ K^{7K+4}(7K+4)log K`.  This is what
   pays for the head the level switch skips: the skipped head's certified deviation mass is
   `≤ 4ε·Xlo(K+4)·c_{K+4}`, a `4ε·density_{K+4}/density_K` fraction of the level-`K` history.
4. **`fullPos'` and the endpoint** — level `K` for `n ∈ [Xlo K, Xlo (K+4)·d_K/d_{K+4}]`, then
   level `K+4`; prefix control inside a level from (1)+(2); the switch from (3).  Then
   `IsNormalSequence 2` + `Bridge.isNormal_realOfDigits`.

### Still-true, now non-binding

`certified_granule_exceeds_previous_scale`, `ScheduleWitness.X_lt_X_step`,
`ScheduleWitness.X_lt_Xlo_step`, `Sched.Xhi_succ_lt_Xlo_step` are all statements about the
**one-dimensional** ladder (rungs `K, K+4, …` with `m` pinned to `K`).  They remain correct and
should not be re-derived or re-litigated; they simply do not bound the `(K, j)` ladder.  The
refuted sub-approaches recorded below (skip the head, certified annuli, pad the history, raise
the previous rung's reach) were all refuted *against the one-dimensional ladder* for the same
reason — none of them is the `m`-march.

## 🗂️ SUPERSEDED ACTIVE (entropy review lap 51, 2026-09-14) — an explicit NORMAL NUMBER from `G₄`'s sampled digits

**Read `DIRECTION.md`'s CURRENT DIRECTIVE first; it outranks any handoff.**

## ✅ DONE (laps 93–117) — the schedule-only strictly increasing read

`Sched.tendsto_fullRead_freq` + `Sched.fullPos_strictMono` + `fullReal`: **`G₄`'s digits along a
strictly increasing position map defined from the schedule alone, carrying every binary word at
its correct frequency along the band cutoffs.**  See `HANDOFF-2026-09-14-entropy-lap117.md`.

Modules: `G4EntropyWindows` (`Q_dvd_P₀`, `windows_eq_or_disjoint`, the multiplicity toolkit),
`G4EntropyBand` (`bandT`), `G4EntropyBandFull` (the certified joint band law),
`G4EntropyFullSeq` (`winStarts`, `fullPos`, the count bridge, `read_freq_error_bound`,
the headline, `fullReal`).

**Open next**: port laps 84–89 (mid-band cutoffs and arbitrary cutoffs) from `bandPos` to
`fullPos`; transfer the lap-90 density-zero non-vacuity.  Normality is not *deducible* from the
fixed sampled data alone (`certified_granule_exceeds_previous_scale`, a size comparison — see its
⚠️ scope note), but is open for arithmetic extensions such as `entropy_E0_down`.

## 🔭 LIVE (2026-09-14, post-wrap) — the **scale gap**, and E1 downward

**Build** 🟢 9001 jobs · both new modules sorry-free · endpoints
`[propext, Classical.choice, Quot.sound]`.

### What the crux is, now that E0/E1 run downward

A band-`i` window start is `2·kIdx(n,α)`, increasing in `n`, so a **position cutoff inside band
`i` selects the truncated sample `n ≤ X'`** — a mid-band prefix of the read *is* a sample at a
smaller outer scale.  `entropy_E0_down` (last session) and now `entropy_E1_down` certify exactly
that, for every `X' ∈ [Xlo K, X K]`, `Xlo K = √(X K)`.  So **prefix control inside a band is not
the obstruction**.

The obstruction is the **head**: cutoffs with `X' < Xlo K_i`.  `G4EntropyScaleGap` proves the
previous rung cannot cover it either:

```
Sched.Xhi K k₄ := 2^2^(m K + 3k₄) + X K      A0's ceiling: every witness at rung K has W.X ≤ Xhi
Sched.Xhi_succ_lt_Xlo_step                    Xhi K k₄ + 1 < Xlo (K+4)
Sched.ScaleGap / Sched.scaleGap               the gap is inhabited
ScheduleWitness.X_lt_Xlo_step                 no rung-K witness reaches rung K+4's FLOOR
```

So the outer scales in `(Xhi (K−4), Xlo K)` are certified by **no rung of the ladder**, and the
head of band `i` lives entirely inside that interval.  The separation is by a tower
(`m₁(K+4) ≥ 4096·m₁ K`), so no constant, no deficit improvement and no change of residue class
(objective B) bridges it.

### Attempts refuted this lap (record, so they are not retried)

* *Skip the head* (start band `i` at `Xlo K_i`): the read chunk `[Xlo, X']` is then only an
  `(X'−Xlo)/X'` fraction of the certified `[0, X']`, so the error is `≈ 2ε·Xlo/(X'−Xlo)`, which
  blows up exactly where the chunk first dominates the history.  Same gap, relocated.
* *Certified annuli* (differences of two certified truncations): same computation, same gap.
* *Pad the history* (all `P₀` residue classes at rung `K−4`, longer windows, more atoms): every
  such gain is polynomial in `K` or bounded by `P₀`, against a tower separation.
* *Raise rung `K−4`'s reach*: that is objective A0, verdict NO (`G4EntropyXCeiling`).

The one mechanism in the repo that *does* solve a prefix problem of this shape is
`BlockConcat.rep` (repetition, `G4EntropyConcat`) — and repetition is exactly what forfeits
strict monotonicity of the read.  That is the honest statement of the tension.

### What the downward chain buys, and the next rung

`abs_midRead_freq_sub_le`'s error at `a` windows into band `i` pays the restriction price
`(δ+1)|P_K|/a`, so it is vacuous below an `≈ K^{−1/2}` fraction of the band.  With
`entropy_E1_down` the mid-band prefix carries **its own** certificate and the price disappears:
the bad initial fraction drops from `K^{−1/2}` to `X^{−1/2}`.

**Next rung (open):** port the consumers of `entropy_E1` at a truncated scale —
`G4EntropyGoodAtoms.atomDeficit`/`card_good_ge`, then `abs_posAvg_preLaw_le`, then a truncated
`abs_midRead_freq_sub_le`.  The statement to aim at:

> for every cutoff `a` with `Xlo K_i ≤ X'(a)`, the read frequency at `bT i + a·m_i` is within
> `O(K^{−1/4})` of `2^{−|v|}` — no `|P_K|/a` term.

**The per-atom caveat is CLOSED — route (i), with the factor `1 + 1/K`**
(`G4EntropyMultiplierSpread.lean`).  The schedule grid takes `d_α = 1 + Q(D₀ + u_α)` with
`D₀ = K·U` and `0 ≤ u_α ≤ U`, so the atom-dependent part is a `1/K` perturbation:

```
gridOf.d_ge, gridOf.d_le'
gridOf.mul_d_le_mul_d        K · d_α ≤ (K+1) · d_β   for EVERY pair of atoms
G4Entropy.mul_kIdx_le, two_mul_le_of_two_kIdx_le
G4Entropy.kIdx_cross         2·kIdx(n,β) ≤ c  →  K·(2·kIdx(n,α)) ≤ (K+1)(c+4)
```

So the atom-indexed truncation a position cutoff induces is sandwiched between two plain outer
scales of ratio `(K+1)/K + O(1/c)`; the sandwich costs a relative `≈ 1/K`, negligible against
the `O(K^{−1/4})` errors the capture inequality already carries.  Route (ii) (restating
`entropy_E1_down` for a truncation vector) is **not needed**.

## 🔭 LIVE (laps 93–101) — `Q ∣ P₀`: the sampled windows are pairwise disjoint

A structural discovery, and the route to an **x-free** (schedule-only) band read.

```
G4EntropyWindows.lean
  kIdx_mod_Q, kIdx_cast_Q      every orbit index ≡ its sample time (mod Q)
  rho_modEq                    ρ_{α,j} ≡ j (mod Q)   [shiftG_eq]
  Q_dvd_freezeQ, Q_dvd_P₀      **Q ∣ P₀**
  kIdx_congr_Q                 ALL orbit indices, all atoms, all times, ≡ (mod Q)
  windows_eq_or_disjoint       **every two sampled windows coincide or are disjoint**
  ActiveIdx, shared_idx_apart  two atoms' shared indices are P₀ apart (coprime_d)
  card_shared_le, card_collide_pair_le, card_multi_atom_le
  card_Atom_sq_le_d            |Atom|² ≤ d_α  (B ≥ (K²+1)², gridUmax ≥ B^K ≤ Q ≤ d)
  card_multi_atom_le_real      collision fraction ≤ 2/|Atom| + 2|Atom|/|P_K| → 0
```

**Why `Q ∣ P₀`.**  `freezeQ` contains, as a factor, the distance between the shifts of two
*different* atoms at the *same* layer; `shiftG_eq` makes those shifts congruent mod `Q`, so `Q`
divides that distance.  Hence every sample time is congruent mod `Q`, hence so is every orbit
index of every atom — and `Q = (U+K+N+2)!` dwarfs `m_K`.

**What it unlocks.**  The `bandPos` read of laps 76–89 needs one *good* atom per scale, which
depends on `G₄`'s entropy data, so the map is explicit but not schedule-only.  With full
disjointness the read can instead take the **whole** sampled position set of a band — a
schedule-only object.  Two obstacles, both now removed:
* the band floor must be an `n`-only condition (else the restriction is not a sample-time
  restriction and the entropy machinery does not apply) — achievable since
  `kIdx(n,α) ≥ n/D₀ − 1`, so a threshold on `n` alone puts *every* atom's window above the floor;
* reading the position *set* counts each window once while the entropy statistic counts each
  `(n,α)` pair once — the difference is the window multiplicity, now bounded by
  `card_multi_atom_le_real`.

**Remaining for the x-free upgrade** (the natural next objective): the assembly — an `n`-only
band threshold, the increasing enumeration of a band's distinct window starts, the count bridge
against `posFreq` (using the multiplicity bound), and the cutoff limit.  This is a re-run of
laps 69–89 with "one good atom" replaced by "the whole sample", and would give a
**schedule-only, strictly increasing** position map with the correct word frequencies — the
lap-51 objective's x-freeness and E-T8's strict monotonicity at once.

## 🔭 LIVE (laps 61–88) — the wall, and the band read that saturates it

**The arc in one line.**  Laps 61–63 proved a wall that closes normality on this mechanism;
laps 64–88 then built the strongest object the wall leaves standing and proved it correct.

### Part I — the wall (laps 61–63)

```
G4EntropyGoodAtoms.card_good_ge          ≥ (1−ρ)|A| atoms are good ONE AT A TIME
G4EntropyGranule.granule_exceeds_previous_scale   |Atom_i|·|P_i|·m_i < |P_{i+1}|
G4EntropyMixture.FinLaw.H₂_mix_le        H₂(mix) ≤ σH₁+(1−σ)H₂+1
G4EntropyMixture.H₂_empirical_window_restrict_ge  sample-time restriction costs (δ+1)/σ
G4EntropyMixture.certified_granule_exceeds_previous_scale
```

> Any sub-collection of scale `i+1`'s sample times whose derived capture bound is **not vacuous**
> already reads more digits than scale `i` produced in total.

So **no prefix bound can be assembled from per-scale certificates**: the first certified granule
of scale `i+1` outweighs everything scale `i` produced, independently of how the granule is cut
(by atoms, by sample times, or both).  ⚠️ **Scope (attended review 2026-09-14):** this is a *size
comparison*, not a proof that prefix frequencies diverge.  Normality is closed here only for
*deduction from the fixed sampled data alone*; arithmetic extensions that control the head of
band `i+1` — e.g. `entropy_E0_down`, which certifies truncated outer scales — are untouched.  The
cause is `X(K) = 2^{100·2^{m(K)}}` with `m(K) ≥ K³`, not the atom count: lap 54's
`chunks_insufficient` was the weaker statement.

### Part II — the band read (laps 64–88)

```
G4EntropyAtomFreq   exists_good_atom, goodAtom, tendsto_goodAtom_occursCount
                    ONE atom per scale carries every word at its correct density
G4EntropyWindows    window_gap_same_atom — one atom's windows are pairwise disjoint
G4EntropyBand       band_gap(_strong), bandS, card_bandS_ge' — ordered bands, half the sample kept
G4EntropyBandFreq   bandLaw, abs_posAvg_bandLaw_le, tendsto_band_occursCount — still certified
G4EntropyBandSeq    bandPos (STRICTLY MONOTONE), bandDig, bT, bandGood,
                    tendsto_bandRead_freq, bandReal, isDisjunctive_bandReal, irrational_bandReal
G4EntropyBandPrefix bandPre, preLaw, abs_posAvg_preLaw_le, winCount_mid_bounds,
                    tendsto_midRead_freq, abs_midRead_freq_sub_le(′),
                    tendsto_midRead_freq_of_depth
```

> **`tendsto_bandRead_freq`** — for every finite binary word `v`,
> `winCount (bandDig G₄) v (bT (i+1)) / bT (i+1) → 2^{−|v|}`, with `bandPos` strictly monotone.
>
> **`tendsto_midRead_freq_of_depth`** — the same limit at **any** cutoff sequence
> `bT i + a_i·m_i` whose relative depth `t_i = |bandS i|/a_i` is `o(√K)`: all but an initial
> `K^{−1/4}` fraction of each band is a good cutoff.

`G₄`'s binary digits, read along a **strictly increasing** schedule-defined position sequence,
have the correct frequency of every finite binary word at every cutoff except an initial portion
of each band, and that portion is a vanishing *fraction of its band*.

⚠️ **Not a density-one statement, and deliberately not stated as one.**  The bad portion of band
`i` has length `≈ θ_i·m_i`, while *everything before band `i`* has length `bT i ≤ 4|bandS i|`,
which is far smaller.  So at a cutoff inside the bad portion, the bad cutoffs below it are most
of them: the bad set has lower density `0` and upper density `1`.  That is the wall
(`certified_granule_exceeds_previous_scale` — a size comparison, ⚠️ see its scope note) seen from
the cutoff side: it is why the *sampled data alone* does not give normality.  Controlling the head
of band `i+1` by a truncated-scale certificate (`entropy_E0_down`) is not excluded.

**Where this sits.**  The repo previously had *either* normality along a non-injective position
map (`isNormal_realOfDigits_samplePos`, lap 52) *or* a strictly increasing map carrying only
disjunctivity (`isDisjunctive_enumReal`, laps 56–60).  This is strictly between, and new.

**Open next.**  (a) `abs_freq_sub_freq_mid` (lap 89) lifts every mid-band estimate to arbitrary
cutoffs `N`, at cost `1/a`; what is *not* available — and is provably not — is a density-one
good set (see the ⚠️ above).  (b) The only way past
the wall is a schedule with `X(K)` growing polynomially rather than as `2^{2^{K³}}`; `X` is fixed
by `G4ScheduleFar`'s far-tail control, so that is a question about the *schedule*, not about the
entropy argument.

## 🔭 LIVE (laps 61–63) — the granularity wall, and what it closes

Laps 61–63 settled the question the lap-60 handoff left open ("is `realOfDigits 2 enumDigits`
normal?") at the level of *routes*: every argument that reads the sampled digits in position
order as a concatenation of **certified** granules is now refuted, with a theorem.

```
G4EntropyGoodAtoms.lean   (lap 61)
  FinLaw.coordDeficit / sum_coordDeficit_le / card_badCoords_le   Markov on per-coordinate deficits
  coordAvg, abs_coordAvg_sub_le      ONE atom's own window statistics, certified
  card_good_ge                       ≥ (1−ρ)|A| atoms are good ONE AT A TIME, price √(δ/ρ)
  Sched.card_goodAtoms_primeLambertFour_ge

G4EntropyGranule.lean     (lap 62)
  card_PK_ge, total_scale_le
  granule_exceeds_previous_scale     |Atom_i|·|P_i|·m_i  <  |P_{i+1}|

G4EntropyMixture.lean     (lap 63)
  FinLaw.mix, H₂_mix_le              H₂(mix) ≤ σH₁+(1−σ)H₂+1  (extra bit = binEntropy σ)
  H₂_empirical_window_restrict_ge    a sub-collection of SAMPLE TIMES costs (δ+1)/σ
  capture_bound_vacuous
  Sched.certified_granule_exceeds_previous_scale
```

**The argument.**  (61) The deficit certifies individual atoms, so the granule is not limited by
the atom count — lap 54's `chunks_insufficient` was not the real obstruction.  (63) Restricting
the *sample times* costs `(δ+1)/σ` exactly as restricting coordinates costs `δ/ρ`, so a granule
whose capture bound is not vacuous reads `≳ |P_K|` digits.  (62) That minimum at scale `i+1`
already exceeds `|Atom_i|·|P_{K_i}|·m_i`, scale `i`'s entire output — because
`X(K) = 2^{100·2^{m(K)}}` with `m(K) ≥ K³`, a doubly exponential jump per scale.

**So the first granule of every new scale wipes out the history and prefix frequencies cannot
converge.**  The disjunctivity endpoints of laps 56–60 stay the strongest infinite objects the
mechanism supports.

**Where the mechanism could still be changed**: `X(K)` is fixed by `G4ScheduleFar`'s far-tail
control, not by the entropy argument.  A ladder with polynomially-growing `X` would move the
wall.  That is a question about the *schedule*, and is the first honest pivot point.

## 🔭 LIVE (laps 56–57) — the strictly increasing enumeration, at the disjunctivity level

`chunks_insufficient` (lap 54) refutes E-T8's upgrade at the **normality** level.  At the
**disjunctivity** level it is reachable and is now proved — `src/NormalNumbers/G4EntropyEnum.lean`:

```
IsSampledPos q            ∃ i n α p, n ∈ P_i ∧ p < m_i ∧ q = 2·kIdx(n,α) + p
infinite_isSampledPos     (one window at scale i already spans kk i = 40000+i positions)
sampleEnum j = Nat.nth IsSampledPos j          x-free, schedule-only
sampleEnum_strictMono     a GENUINE subsequence of G₄'s digit positions
sampleEnum_run            consecutive sampled positions are ADJACENT in the enumeration
exists_occursAt_sampled   every binary word occurs in some sampled window (goodCount > 0)
occurs_along_sampleEnum   ⟹ every finite binary word occurs in G₄'s digits along sampleEnum
```

**The structural point** that makes this work where normality fails: nothing can sit strictly
between `q` and `q+1`, so a word occupying a run of positions *inside one window* survives the
increasing enumeration as a contiguous block.  No block-frequency control is needed — only
occurrence — so the `ρ ≫ δ/m` barrier never enters.

**Lap 58 closed the follow-up** — and the "unbounded occurrence positions" detour was not
needed.  `ProperDigits` comes from applying `occurs_along_sampleEnum` to the word
`List.replicate (N+1) 0`: a match at `t` puts a `0` at subsequence index `t + N ≥ N`, which is
exactly `ProperDigits`' requirement.  Hence:

```
enumDigits j = digitOf 2 (fract G₄) (sampleEnum j)
properDigits_enumDigits    ProperDigits 2 enumDigits
isDisjunctive_enumReal     IsDisjunctive 2 (realOfDigits 2 enumDigits)
irrational_enumReal        Irrational (realOfDigits 2 enumDigits)
```

**An explicit irrational, disjunctive real read off a genuine strictly increasing subsequence of
`G₄`'s binary digits.**

**Lap 59 — non-vacuity, which was a real gap.**  `density_le_pow_real` bounds each scale's own
density, but the headline reads the **union over all scales**, which nothing controlled: if that
union were cofinite, `sampleEnum` would be the identity and `isDisjunctive_enumReal` a
restatement of `isDisjunctive_two`.  Now closed:

```
isSampledPos_iff_isSampled   the new predicate is the repo's IsSampled
exists_cover                 positions < L are covered by finitely many scales
card_filter_isSampled_le     #{q < L : IsSampled q} ≤ L/4
```

The union's density is at most `¼` (each scale ≤ `⅛(2/K⁶)^K ≤ ⅛·2^{−K}`, summed geometrically).
**Lap 60 sharpened this to density ZERO** (`card_tail_le`, `tendsto_density_isSampled`): each
`sampledPosAt i` is a *finite* set, so the head scales contribute a constant, and the tail beyond
`I` at most a `2^{−I}/8` fraction — hence `#{q < L : IsSampled q}/L → 0`.  **`sampleEnum` skips
almost every digit of `G₄`.**

Open next: whether `realOfDigits 2 enumDigits` is *normal*.  Lap 54 refutes the chunking route;
`enumDigits` is not a block concatenation so that argument does not transfer directly, but the
same prefix problem reappears — `|S_i|` explodes with `i` and the enumeration order is forced, so
repetition (rung 3's fix) is unavailable.  A frequency estimate is further blocked because the
enumeration interleaves windows from different scales, so a word may straddle two scales'
windows.

## ✅ OBJECTIVE MET (lap 52) — and the E-T8 successor's arithmetic

The lap-51 objective is **proved**, in `src/NormalNumbers/G4EntropyBlockWord.lean`:
`samplePos` (schedule-only, `samplePos_spec` shows every value is a sampled position),
`isNormalSequence_digits_along_samplePos`, `isNormal_realOfDigits_samplePos`.  All
`[propext, Classical.choice, Quot.sound]`.  E-T7 fires: the next altitude lap sets the successor.

### E-T8 (strictly increasing `samplePos`) — the affirmative tool is proved, the arithmetic is tight

Lap 52 also proved the tool the directive named, in `src/NormalNumbers/G4EntropySubsample.lean`:

* `FinLaw.H₂_restrictCoords_ge` — restricting a window law to a subset `G` of coordinates costs
  at most `m` bits per dropped coordinate, so the **total** deficit `δ·|A|` survives: the
  restricted law's per-coordinate deficit is `δ/ρ`, `ρ = |G|/|A|`.
* `abs_posAvg_restrict_sub_le` — hence a sub-collection's word frequency obeys the capacity
  bound with `δ ↦ δ/ρ`.  **The cost of restriction is `√(1/ρ)`, not `1/ρ`.**

The arithmetic this settles, and why E-T8 is *not* a bookkeeping follow-up:

* Repetition (`rep m` copies of block `m`) is what makes `samplePos` non-injective.  It can only
  be removed by supplying, at each scale, `c` **disjoint** good chunks in place of the `rep`
  copies — then each chunk uses fresh windows.
* A chunk of relative size `ρ = 1/c` has error `≈ 2√(log 2 · ℓ · δ/(ρ·m))`.  With the implemented
  `δ = 50√K`, `m = K/4` this vanishes only for `ρ ≫ 200ℓ/√K`, i.e. **`c = O(√K)` chunks per
  scale** — exactly the directive's `ρ ≫ K^{−1/2}`.
* But the prefix condition needs the first chunk of scale `i+1` to be dominated by everything
  before it: `ρ_{i+1}·L_{i+1} ≪ ∑_{j≤i} L_j ≈ L_i`, i.e. `ρ_{i+1} ≪ L_i/L_{i+1}`.  And
  `L_{i+1}/L_i ≥ |Atom_{i+1}|/|Atom_i| = ((K+1)²+1)^{K+1}/(K²+1)^K ≈ e²K²`.
* So E-T8 on this mechanism needs `K^{−1/2} ≪ ρ ≪ K^{−2}`: **impossible**.  Chunking by
  coordinates cannot replace repetition here.

**Lap 54 formalized the obstruction** (`G4EntropySubsample.lean`): `card_Atom_growth`
(`(K²+1)⁴·|Atom_i| ≤ |Atom_{i+1}|`) and **`chunks_insufficient`**:

> `kk i / (50·√(KK i))  <  |Atom_{i+1}| / |Atom_i|`

left = the most disjoint chunks one scale can certify (`m/δ`), right ≤ the block-length growth
that repetition-free assembly must cover.  Never enough.

**Route (b) is closed too, and for a better reason than the atom count.**  The barrier `ρ ≫ δ/m`
is *dimension-independent*: truncating each window to its top `s` bits is the same subadditivity
argument as `H₂_restrictCoords_ge` (`lowTuple`'s dual), so a chunk cut by atoms **and** by window
length has per-coordinate deficit `δ|A|/|G|` on `s` bits and is certifiable exactly when
`ρ = (|G|/|A|)·(s/m) ≫ δ/m`.  In one line: **a chunk is certifiable only if its digit count
exceeds the collection's total entropy deficit** — so the minimal certifiable granule at scale
`i+1` is `≈ δ_{i+1}·W_{i+1}` digits, already larger than scale `i`'s entire block `m_i·W_i`.
Splitting the sample times `P_K` instead of the atoms does not escape this (and the naive
analogue is false anyway: `H₂` of a one-point empirical law is `0`).

**Therefore E-T8 needs a different construction, not a different chunking.**  What is NOT
excluded: any mechanism that lowers the deficit `δ` below `m/K²` at some scale, or one that
produces good blocks of *comparable* length at many scales.  Neither is visible in the current
schedule.

### What is now settled (do not re-attack)

* Frequencies **averaged over positions**: complete.  `tendsto_occursCountP_primeLambertFour`
  (`t = 1`, all positions), `tendsto_occursCountJointUniform_…` (lap 45, aligned `t`-vectors),
  `tendsto_occursCountJointFree_…` (lap 47, **all** vectors in `[0,m_K−ℓ+1)^t`, no alignment).
* Frequencies **pointwise** (a fixed position vector): **refuted**, `no_pointwise_bound_from_deficit`
  (lap 48).  The averaging is necessary; it is not an artefact of the estimates.
* **Richness** per block: `joint_richness_primeLambertFour` (laps 49–50), half the blocks,
  `≥ 2^{t m_K − 200t√K}` joint values.
* Normality of `G₄` on this mechanism: **closed** (lap 37 reflection; quantified lap 39).
  The three escapes (varied frozen residue, shifted real `2^σ x`, more scales) are each closed by
  something already proved — do not re-derive them.

### The target

Every endpoint above is a statistic *at scale `i`, with `i → ∞`*: a sequence of finite statements.
The objective is the expedition's **first infinite object**.

> **`samplePos : ℕ → ℕ`**, defined from the schedule alone (no reference to `x`), every value a
> sampled position, with
> `IsNormalSequence 2 (fun j => digitOf 2 (Int.fract (primeLambertAtBase 4)) (samplePos j))`
> and hence `IsNormal 2 (realOfDigits 2 …)`.

**Not a claim about `G₄`.**  The new real is built *from* `G₄`'s digits; `G₄`'s own normality stays
closed on this mechanism.  Say so in every module docstring.

### The three rungs

**Rung 1 — `G4EntropyOcc.lean`, the counting bridge.  THE DECISIVE PROBE; do it first.**
`IsNormalSequence` is phrased through `countOccurrences v ((List.range n).map s)` =
`((List.range n).map s).tails.countP (v.isPrefixOf ·)`.  Everything downstream wants the
arithmetic shape `occCount s v n := #{p < n : ∀ q < |v|, s (p+q) = v[q]}` instead.  Needed:
* `occCount_eq_countOccurrences` up to a seam `≤ |v|−1` (windows that start below `n` but run past
  it are counted by `occCount` and not by `countOccurrences`);
* `occCount` additivity over a split `n = a + b` with the same seam;
* the `ℕ→ℝ` versions with the seam as an explicit additive constant, so `CFChainFreq`'s
  `countOccurrences_append_addslack₂` shape can be mirrored.
If the `tails.countP` shape resists ⇒ **trigger E-T9**: record the exact obstruction here and
restate rungs 2–3 in list-of-blocks form (`CFChainFreq`'s lemmas already work on lists, so this is
a change of shape, not of plan).

**Rung 2 — `G4EntropyBlockWord.lean`, one scale as one block.**
Enumerate the scale-`i` sample in a fixed order: `(n, α, p) ∈ P_i × Atom_i × [0, m_i)` ↦ digit of
`G₄` at `2·kIdx(gridAt i) n α + p`.  Block length `L_i := |P_i|·|Atom_i|·m_i` (all three factors are
`x`-independent naturals; `P_i ≠ ∅` was recorded in lap 1).  Endpoint:
`occCount (block i) v / L_i → 2^{−|v|}`, straight out of `tendsto_occursCountP_primeLambertFour`
whose denominator is `|P_i|·|Atom_i|·(m_i − ℓ + 1)`.  Two corrections, both `O(ℓ/m_i) → 0`:
the `(m_i−ℓ+1)/m_i` normalisation and one seam per `(n,α)` block.

**Rung 3 — `G4EntropyNormalReal.lean`, the assembly.**
`T_0 = 0`; `r_m` any natural with `r_m·L_{i_m} ≥ (m+1)·(T_{m−1} + L_{i_{m+1}})`;
`T_m = T_{m−1} + r_m·L_{i_m}`; `samplePos` walks group `m` = `r_m` copies of block `i_m`.
Three estimates for a prefix of length `N` landing in group `m` after `q` whole copies and a
partial copy of length `s < L_{i_m}`:
1. the past `T_{m−1}` contributes error `≤ T_{m−1}/N ≤ 1/m`;
2. the `q` whole copies contribute the block's own error `ε_{i_m}(v) → 0` plus `q` seams;
3. the partial copy contributes `≤ s/N ≤ L_{i_m}/T_{m−1} ≤ 1/m`.
Then `ProperDigits` (infinitely many `0`s — from the frequency of `v = [0]`) and
`Bridge.isNormal_realOfDigits`.
**Why repetition**: `L_{i+1} ≫ ∑_{j≤i} L_j` because `|P_i|` explodes with `i`, so prefixes of a
fresh block can never be made negligible without repeating the earlier ones.

### Afterwards, not before (trigger E-T8)

A strictly increasing `samplePos` — a genuine *subsequence* of `G₄`'s binary digits — needs the
frequency theorem for the empirical law on a **subset** `S ⊆ P_K`.  The cost is exactly
`deficit(μ_S) ≤ (Δ+1)/ρ` for `ρ = |S|/|P_K|` (concavity: `H(μ) ≤ ρH(μ_S)+(1−ρ)H(μ_{S^c})+h(ρ)`),
affordable while `ρ ≫ K^{−1/2}` since the frequency error is `O(√(Δ/(|A|m)))`.  That is the next
target once the headline lands; it is an upgrade, not a prerequisite.

### Bounded secondary, only on an E-T3 stall

**Measure the wall**: `Sched.density_le_pow` (`≤ ½(3/K⁴)^K`) and `Sched.window_needed_ge`
(density `≥ 1/2` needs `mm i ≥ K^{4K}·m_K`).  A negative result's value is its constant.

---

## 🎯 ACTIVE (entropy DEEP REFLECTION lap 37, 2026-09-14) — the JOINT (`t`-wise) sampled-word frequency theorem

**Read `DIRECTION.md`'s CURRENT DIRECTIVE first; it outranks any handoff.  Full reasoning:
`REFLECTION-2026-09-14-entropy.md`.**

### Where the campaign stands

Brief §2–§6 are all closed.  `entropy_E0`/`entropy_E1` unconditional and axiom-clean;
`T_E`/`T_S`/`T_mix` refuted with witnesses meeting their exact premises; §5 answered positively and
rendered on real digits (`tendsto_occursCountT_primeLambertFour`).  **Normality of `G₄` is closed on
this mechanism, by theorem and quantitatively**: `qForces_normal_iff_density_one` needs density
**one**, `sum_weight_le` gives every admissible family over every scale `≤ 1/8`, the sampled density
is `≤ ½(3/K⁴)^K` (from `key_size`'s own slack `Q·D₀ ≥ K·B^{2K}` vs `H_K m_K ≤ (2(K²+1))^K K`), and
`entropy_cover_bound` pins the window at exactly `m_K = K/4`.  Gap `≈ K^{4K}`.  Cause:
`GridParams.hQdvd` ⟹ `Q ≥ lcm(1,…,U)`, `U ≥ B^K`.

**Do not re-derive these three closed escapes** (reflection §1): varying the frozen residue
(`b₀ ≡ t_α + d_α σ_α mod d_α²` gives a family of size `√Mprod` against gaps `2P₀/d_α`, `P₀ ≥ Mprod`);
shifting the real `x ↦ 2^σ x` (transported point becomes `2^σ F_K(n) + (1−2^σ)(θ−γ)`, needing Fourier
degree `2^σ D_j`; equivalently a longer window, closed by `not_qForces_normal_of_levels`); more
scales (`sum_weight_le` sums over all `(K,N)`).

### The target

`entropy_E1` bounds the law of the **whole vector** `Z^{G₄}_K = (Z_α)_{α∈Atom}` under one uniform
`n ∈ P_K`.  Every result so far projects it to one coordinate.  Used jointly it says the sampled
windows **decorrelate**:

> for every `t`, every partition of `Atom` into `t`-blocks, and all binary words `w₁,…,w_t` of
> length `ℓ`, the frequency over `(n, block, positions)` of *"`G₄`'s block at `2·kIdx(n,α_s)+p_s`
> spells `w_s`, simultaneously for every `s ≤ t`"* tends to `2^{−tℓ}`.

Mechanism: partition `A` into `⌊|A|/t⌋` blocks of size `t`; `FinLaw.H₂_le_sum_H₂_map` over the
block-indexed coordinate family gives average deficit `≤ t·δ` per block; the per-block pattern
coordinate is the product of the `t` per-window tiling coordinates (`fullCoord`/`posAt`), injective
because each factor is; then the existing Hellinger/Pinsker step on `tℓ` bits.

### The three rungs (in order)

1. **`G4EntropyPosition.lean` — render lap 36 at the schedule.**  `posFreq i ℓ x w :=
   posAvg (kk i) ℓ (jointLawAt i x) w`; `abs_posFreq_sub_le_of_deficit` (the deficit hypothesis is
   *verbatim* `abs_blockFreqT_sub_le_of_deficit`'s, and `abs_posAvg_sub_le` is already the abstract
   form of the proof); the `E0` and `entropy_E1` instances; the general-`p` form of
   `G4EntropyRender.blkAt_blockVal_min` (same proof with `(j+1)*ℓ ↦ p + ℓ`); endpoint
   `tendsto_occursCountP_primeLambertFour`.  This is `t = 1` of the target and the thread lap 36 left
   dangling.
2. **`G4EntropyJoint.lean` — the abstract `t`-wise capacity bound.**  Probe the uncertain step FIRST:
   does `∑_blocks (tℓ − H₂(pattern coord)) ≤ t·Δ` hold?  (Trigger **E-T6**: if not, record the exact
   degradation here and re-state with the true `t`-dependence; do not retreat to `t = 1`.)
3. **The schedule instance + digit rendering** of rung 2 → `tendsto_occursCountJoint_…`.

### ✅ RUNG 2 DONE (lap 37) — `G4EntropyJoint.lean`, sorry-free, trust triple

**E-T6 does not fire, and the answer is better than the directive guessed: the deficit is NOT
multiplied by `t`.**  With `blk : B → Fin t → A` injective the bits ledger closes exactly:

```
H₂ L ≤ ∑_{b,j} H₂(patCoord b j) + ∑_b H₂(patRem b) + ∑_{α ∉ im blk} H₂(z α)
     ≤ ∑_{b,j} H₂(patCoord b j) + |B|·t·(m%ℓ) + (|A| − t|B|)·m
m|A| − Δ ≤ H₂ L,   ⌊m/ℓ⌋·ℓ + m%ℓ = m
⟹  sum_patCoord_deficit_le :  ∑_{b,j} (ℓt − H₂(patCoord b j)) ≤ Δ      -- the SAME Δ, zero slack
⟹  abs_avg_patCoord_prob_opt : |avg_{b,j} Pr[pattern = w] − 2^{−ℓt}|
                                  ≤ 2√(log 2 · ℓ · Δ / (|B|·m))
```

With `Δ = δ|A|` and `|B| ≈ |A|/t` the bound is `2√(log 2 · tℓδ/m)` — the `t = 1` bound with
`ℓ ↦ tℓ`, i.e. pinning `t` words at once costs exactly the `t` extra words' worth of bits and
nothing more.  Declarations: `packFin`, `patCoord`, `patRem`, `leftCoord`, `jointFam`,
`jointFam_injective`, `H₂_map_patRem_le`, `H₂_map_leftCoord_le`, `FinLaw.H₂_map_const_le`,
`sum_patCoord_deficit_le`, `abs_avg_patCoord_prob_le`, `abs_avg_patCoord_prob_opt`.

### ✅ RUNG 3 DONE (lap 38) — `G4EntropyJointSched.lean`, sorry-free, trust triple

**The 🎯 objective of the lap-37 directive is MET.**  Endpoint
`Sched.tendsto_occursCountJoint_primeLambertFour`: for every `t`, every `ℓ`, and any `t` binary
words `v₀,…,v_{t−1}` of length `ℓ`,

```
#{(n,b,j) ∈ P_K × Fin(nblk) × Fin(m_K/ℓ) : ∀ s < t,
    OccursAt 2 G₄ (v s) (2·kIdx(n, blkSched b s) + jℓ)} / (|P_K|·nblk·⌊m_K/ℓ⌋)  →  2^{−ℓt}
```

i.e. the `t` sampled windows of a block **decorrelate**.  `t = 1` is
`tendsto_occursCountT_primeLambertFour`.  Chain: `blkSched` / `blkSched_injective` (enumerate the
atoms, cut into consecutive `t`-blocks; injective by uniqueness of division) → `patFreq` →
`abs_patFreq_sub_le_of_deficit` (`≤ 2√(2 log2·ℓtδ/m_K)`; the factor 2 pays for
`nblk = ⌊|A|/t⌋ ≥ |A|/(2t)`) → `abs_patFreq_sub_le_primeLambertFour`
(`≤ 2√(400 log2·ℓt/√K)` at `entropy_E1`'s `δ = 50√K`) → `tendsto_patFreq_primeLambertFour` →
`patCoord_eq_pack_iff` / `patFreq_eq_count` / `patFreq_eq_digits` → the endpoint.

**Design correction applied** (as scoped): `leftCoord`'s hypothesis `m ≤ ℓ*t` is gone.  All three
families of `jointFam` now land in `Fin (2 ^ (ℓ*t + m))` via `upPat` / `upLeft`
(`Fin.castLE`, injective), so `sum_patCoord_deficit_le`, `abs_avg_patCoord_prob_le` and
`abs_avg_patCoord_prob_opt` no longer carry `hm` — necessary, since at the schedule `m_K = K/4 →
∞` with `ℓ, t` fixed.  All bits bounds unchanged.

Build 🟢 8973 jobs; `#print axioms` on the endpoint, `abs_patFreq_sub_le_primeLambertFour`,
`sum_patCoord_deficit_le`, `entropy_E0`/`entropy_E1`, `isDisjunctive_four/two/base`,
`primeSumAtBase_eq_primeLambertAtBase`: trust triple only.

Per **E-T7** this lap does not pick its own next target; the next altitude lap sets one.

### 🗄️ (superseded) rung 3 scoping notes

1. **The blocking at the schedule.**  `blkAt_sched i t : Fin (Fintype.card (gridAt i).Atom / t)
   → Fin t → (gridAt i).Atom := fun b s => (Fintype.equivFin _).symm ⟨b*t+s, _⟩`; injectivity from
   uniqueness of division (`Nat.add_mul_div_right`/`omega`), the bound `b*t+s < card` from
   `b < card/t`, `s < t`.  Also need `m ≤ ℓ*t` — at the schedule `m_K = kk i`, so this holds once
   `ℓ*t ≥ kk i`; note the hypothesis is only used by `leftCoord`'s cast, so a **weaker** variant
   `leftCoord` into `Fin (2^(max m (ℓ*t)))` would drop it.  ⚠️ decide this before instantiating:
   for fixed `t` and `ℓ` the hypothesis `m ≤ ℓ·t` FAILS at the schedule (`m_K = K/4 → ∞`).
   **Fix**: change `leftCoord`'s codomain to `Fin (2^(ℓ*t + m))` (or drop the uncovered atoms by
   requiring `t ∣ card Atom`).  Cheapest is to let all three families land in
   `Fin (2^(ℓ*t + m))` — `patCoord`/`patRem` cast up, `leftCoord` casts `z α` up — and the bits
   bounds are unchanged.
2. `Sched.patFreq i ℓ t x w` and `abs_patFreq_sub_le_of_deficit` / `…_primeLambertFour`.
3. Digit rendering + `tendsto_occursCountJoint_primeLambertFour`: the pattern event is
   `∀ s < t, OccursAt 2 G₄ (v s) (2·kIdx(n, blk b s) + jℓ)` — `posAt_blockVal` and
   `blockVal_eq_wordVal_iff` are already general enough; the only new step is unpacking `packFin`
   into the `t` component events.

### ✅ DONE (laps 40–41) — the objective's *stated* endpoint: independent per-window offsets

`DIRECTION.md`'s 🎯 asks for a position `p_s` **per window** (`2·kIdx(n,α_s)+p_s`).  Rung 3
(lap 38) delivered only the *common* aligned position `jℓ`.  Lap 40 closes that gap abstractly
and at the schedule; the digit rendering is the remaining step.

**The mechanism (no new information theory): change the window, not the ledger.**
`G4EntropyJointPos.lean`:

```
cutCoord / cutTuple / outCoord / cut_out_injective / cutFam
H₂_cutTuple_ge     L.H₂ − |A|(m−D) ≤ H₂(L.map (cutTuple m D ρ))     -- per-coordinate offsets
blkAt_cutCoord     blkAt D ℓ j (cutCoord m D a z) = posAt m ℓ (a+jℓ) z
shiftOf / shiftOf_blk / patPos
abs_avg_patPos_prob_opt
    |avg_{b,j} Pr[pattern at (pp s + jℓ)_s] − 2^{−ℓt}| ≤ 2√(log2·ℓΔ/(|B|·D))
Sched.ppMax / posPatFreq / abs_posPatFreq_sub_le_of_deficit
    ≤ 2√(2 log2·ℓtδ/(m_K − max pp))
```

The key point: cutting each window to its **own** `D`-bit sub-window costs exactly `|A|(m−D)`
bits, so an `m`-window deficit `Δ` becomes a `D`-window deficit of the **same** `Δ` — the
offsets are free and the only price is the shortened window `D ≤ m_K − max pp`.  `pp = 0`,
`D = m` recovers `abs_avg_patCoord_prob_opt` verbatim.

**Lap 41 closed the rendering**: `abs_posPatFreq_sub_le_primeLambertFour`
(`≤ 2√(800 log2·ℓt/√K)` whenever `2(max pp + ℓ) ≤ m_K`),
`tendsto_posPatFreq_primeLambertFour`, `patPos_eq_pack_iff`, `posPatFreq_eq_count`,
`posPatFreq_eq_digits`, and **the endpoint**

```
tendsto_occursCountJointPos_primeLambertFour :
  #{(n,b,j) : ∀ s < t, OccursAt 2 G₄ (v s) (2·kIdx(n, blkSched b s) + pp s + jℓ)}
    / (|P_K|·nblk_K·⌊(m_K − max pp)/ℓ⌋)   →   2^{−ℓt}
```

— a position `p_s = pp s + jℓ` **per window**, chosen freely.  `pp = 0` is
`tendsto_occursCountJoint_primeLambertFour`.  The `DIRECTION` 🎯 is now met **as stated**.

**⚠️ The lap-40 narrowing is RETRACTED (lap 42).**  It said the *uniform* average over all
position vectors was unreachable, because a jointly injective family of `(m/ℓ)^t` pattern
coordinates per block would carry `tℓ(m/ℓ)^t` bits against the `tm` its windows hold.  True —
but **no such single family is needed**.  Decompose `jj ∈ [0,J)^t` (`J = ⌊m/ℓ⌋`) uniquely as
`jj = d + j·1` with `min d = 0`.  Each *diagonal* `d` is exactly what `abs_avg_patPos_prob_opt`
controls, at `pp s = d s·ℓ` and cut length `D_d = m − (max d)ℓ`, so the diagonal's unnormalized
contribution is

```
(J − max d)·2√(log2·Δ/(|B|(J − max d)))  ≤  2√(log2·Δ·J/|B|)      uniformly in d
```

and there are `≤ t·J^{t−1}` diagonals, giving

```
|uniform average − 2^{−ℓt}|  ≤  (t J^{t−1}/J^t)·2√(log2·Δ·J/|B|)  =  2t√(log2·ℓΔ/(|B|·m))
```

— **the aligned bound times `t`**.  The blow-up of the individual diagonal bounds as
`max d → J` is exactly cancelled by those diagonals' weight.

### 🔨 IN FLIGHT (laps 42–43) — `G4EntropyJointUniform.lean`

Landed lap 42: `jjPat`, `patPos_eq_jjPat`, `uniPatFreq`, `diagSet`.
**Landed lap 43, both leaves now PROVED (module sorry-free):**

- `card_diagSet_le : (diagSet t J).card ≤ t * J^(t−1)` — `diagSet ⊆ ⋃_s {d | d s = 0}`,
  each fibre injecting into `Fin (t−1) → Fin J` by `Fin.succAbove`.
- `minv` / `minv_le` / `exists_minv_eq` / `diagOf` / `diagOf_mem` / `diagOf_add_minv` /
  `minv_lt` / `minv_add_sup_lt` / `minv_shift`, and
  `sum_diag_decomp (ht : 0 < t)` — the reindexing `jj ↦ (jj − min jj, min jj)`, via
  `Finset.sum_fiberwise_of_maps_to` over `diagOf` and then `Finset.sum_nbij'` on each fibre.
  The inverse `k ↦ (d + k)` is made total by the clamp `((d s) + k) % J` (`J = 0` handled
  separately: both sides are empty).

**Remaining:** `abs_uniPatFreq_sub_le` (assemble: `sum_diag_decomp` + `patPos_eq_jjPat` +
`abs_avg_patPos_prob_opt` per diagonal + `card_diagSet_le`), then the schedule instance and the
digit rendering to `tendsto_occursCountJointUniform_primeLambertFour`.

### ✅ BOUNDED SECONDARY DONE (lap 39) — `G4EntropyWall.lean`, sorry-free, trust triple

The wall is measured, and the reflection's estimate was **conservative**: the schedule's
`N = 100K²` makes `B = K²(K+N)+1` **quartic**, not cubic (`quartic_le_gridB : 100K⁴ ≤ B`), so

```
density_le_pow      8·(B²)^K·#{sampled positions of scale i below L} ≤ (K²+1)^K·L    (ℕ)
density_le_pow_real #{…}/L ≤ ⅛·(2/K⁶)^K                                              (ℝ)
```

— against the density **one** `qForces_normal_iff_density_one` demands.  (The estimate in
`REFLECTION-2026-09-14-entropy.md` was `½(3/K⁴)^K`, from `cube_le_gridB`.)  Read as a window
length:

```
levelBudget_of_le_superpow    (∀ i, mm i ≤ K^{4K}·m_K) → LevelBudget mm
window_needed_ge              density > 1/4 at any L ⟹ ∃ i, K^{4K}·m_K < mm i
not_qForces_normal_at_superpow
```

i.e. a level function must read `K^{4K}` times the implemented window `m_K` before the counting
argument can even *fail* — and failing it is only necessary, not sufficient.  This supersedes
`not_qForces_normal_at_pow` (which spent only `B^K ≥ K^{3K}`).

### 🗄️ (superseded) original scoping of the bounded secondary

`Sched.density_le_pow` : sampled density `≤ ½(2(K²+1)/B²)^K ≤ ½(3/K⁴)^K`, and
`Sched.window_needed_ge` : any level function reading density `≥ 1/2` needs `mm i ≥ K^{4K}·m_K`.
Both are `key_size` re-proved keeping its own slack (`hcube : K³ ≤ gridB K N`).

---

## 📚 ARCHIVE — ACTIVE section of entropy review lap 23 (objective MET at lap 31)

## 🎯 (entropy review lap 23, 2026-09-14) — the sampled-word FREQUENCY theorem for `G₄`

**Read `DIRECTION.md`'s CURRENT DIRECTIVE first; it outranks any handoff.**

### The correction that opened this

Lap 15 filed §5 as answered negatively.  Its theorem
`entropy_rate_not_control_bit : 1 ≤ m → ∃ L : FinLaw (Fin (2^m)), L.H₂ = m − 1 ∧
L.prob (highHalf m) = 0` is true, but `highHalf m` is the event **"the leading bit of the window
is 1"** — a *fixed offset*.  Normality is built from the frequency of a word **averaged over the
offsets** inside the window, and on lap 15's own witness (uniform on the leading-bit-zero half)
that averaged 1-frequency is `(m−1)/(2m) → 1/2`, i.e. correct.  Entropy controls the averaged
frequency; only the fixed-offset one is free.  So §5's real answer is POSITIVE.

### The target

For a fixed word length `ℓ`, put `r = ⌊m_K/ℓ⌋` and let `N_K(w)` count the triples
`(n, α, j)` with `n ∈ P_K`, `α ∈ Atom_K`, `j < r` such that the `ℓ` binary digits of `G₄` at
positions `2·kIdx(n,α) + jℓ, …, +jℓ+ℓ−1` spell `w`.  Then

    N_K(w) / (|P_K|·|Atom_K|·r)  →  2^{−ℓ}   as K → ∞ along the admissible scales.

Quantitatively the deviation is `O(√(ℓ·√K⁻¹))`, from `entropy_E1`'s deficit `Δ_K = 50√K·H_K`
against `m_K H_K` total bits.  **Not a normality claim**: the sampled positions have density
zero (laps 9–22).  It *is* strictly stronger than `isDisjunctive_two` on this system, and it is
the load-bearing input any future positive branch would need.

### ✅ PROVED (entropy lap 23) — `Sched.tendsto_blockFreq_primeLambertFour`

```
blockFreq i ℓ x w                                          (G4EntropyFreq.lean)
  = avg over (α, j) of ((jointLawAt i x).map (blkCoord (kk i) ℓ (α,j))).prob {w}

tendsto_blockFreq_primeLambertFour (ℓ) (0 < ℓ) (w : Fin (2^ℓ)) :
  Tendsto (fun i => blockFreq i ℓ (primeLambertAtBase 4) w) atTop (nhds (1/2^ℓ))
```
axiom-clean, plus the quantitative `abs_blockFreq_sub_le`:
`|blockFreq i ℓ G₄ w − 2^{−ℓ}| ≤ log 2·(ℓ + 50√K)/(t·(m_K/ℓ+1)) + t/2` for every `t > 0`.

The chain as built: `FinLaw.gibbs` → `H₂_le_sum_H₂_map` (joint injectivity from
`blkAt_injective`) → `sum_block_deficit_le` → `abs_prob_singleton_sub_le` (Hellinger) →
`abs_avg_sub_le` (AM-GM) → `abs_avg_block_prob_sub_le` → `entropy_E1`.

### ✅ PROVED (entropy lap 24) — the faithfulness rendering

`G4EntropyRender.lean`: `blkAt_blockVal_min` (the dictionary for *every* block index, the last
overlapping one included), `blockFreq_eq_count`, `blockFreq_eq_digits`, and
`tendsto_wordCount_primeLambertFour` — the headline stated purely as a digit-pattern count of
`G₄`, no `FinLaw` anywhere in it.  Item 1 below is therefore DONE; the remaining thread is the
*word-list* rendering (`OccursAt`) and the general-`x` version.

**Still open in this thread (next):**
0. ~~**Word-list rendering.**~~ (done, lap 25) — `seqVal`/`wordVal`, `seqVal_inj` (uniqueness
   of the binary encoding), `blockVal_eq_wordVal_iff`, and
   `tendsto_occursCount_primeLambertFour`: the headline counts exactly the triples at which
   `OccursAt 2 G₄ w` holds, the same predicate `isDisjunctive_two` uses.
0''. ~~**The quantitative edge.**~~ (done, lap 26) — `abs_blockFreq_sub_le_sqrt`:
   `|blockFreq i ℓ G₄ w − 2^{−ℓ}| ≤ √(8 log 2 (ℓ²/K + 50ℓ/√K))`, uniform in `w`; and
   `tendsto_blockFreq_growing`: the frequency is pinned for **every** word length
   `ℓ(K) = o(√K)`, with the words allowed to change with `K`.  E-T5 rate: the sample
   controls words up to length `o(√K)` inside windows of `m_K = K/4` bits.

0'. ~~**The general-`x` version.**~~ (done, lap 27) — `defRatio`,
   `abs_blockFreq_sub_le_defRatio` (`≤ log2·ℓ/(t·D) + log2·ℓ·defRatio/t + t/2` for every
   `t > 0`) and `tendsto_blockFreq_of_E0`: **`E0 x` alone** pins every word's sampled
   frequency, for every real `x`.  `G₄` is now an instance
   (`tendsto_blockFreq_primeLambertFour'` via `E0_primeLambertFour`).  So §5's positive answer
   is a theorem about the *sampling scheme*, not about `G₄`.

0'''. ~~**The capacity trade-off.**~~ (done, lap 28) — `abs_blockFreq_sub_le_of_deficit`:
   a per-window deficit of `δ` bits controls every word of length `ℓ` to within
   `√(2 log 2 · ℓ(ℓ+δ)/m_K)`, uniformly in `w` and in `x`; `tendsto_blockFreq_of_capacity`
   is the limit form (words, reals and deficits all free to vary with the scale).  Reading:
   `√(ℓ²/m)` is the *sampling* cost and `√(ℓδ/m)` the *deficit* cost; lap 26's `o(√K)`
   ceiling is exactly where they cross, so it is NOT an artifact of the averaging step —
   improving `entropy_E1`'s `δ = 50√K` would extend control to `o(min(√m_K, m_K/δ))`.

0''. **Superseded:** is the frequency statement *uniform* in `ℓ` — i.e. can
   `ℓ = ℓ(K)` grow, and at what rate does `O(√(ℓ/√K))` still vanish?  That is the quantitative
   edge of what entropy controls here (route trigger E-T5 territory, recorded not hidden).
1. ~~**The faithfulness rendering.**~~ (done, lap 24)  `blockFreq` is *defined* through `FinLaw.map`; prove
   `blockFreq_eq_count` — it equals `#{(n,α,j) : the ℓ-block …} / (|P_K|·H_K·(m_K/ℓ+1))` —
   from `map_empirical_p`, and `blockFreq_eq_digits` — that block `j` IS the ℓ binary digits
   of `G₄` at `2·kIdx(n,α) + jℓ` — from `blkAt_blockVal` + `ZSample_eq_blockVal`.  Until those
   land, the headline is honest but its *meaning* rests on definitional unfolding rather than
   on a stated dictionary.
2. Optional: the same for every `x`, not just `G₄` (the abstract theorem already is).

### 🔧 IN FLIGHT (lap 29) — the disjoint tiling, removing the `ℓ²/m` floor

`G4EntropyTiling.lean` (green, axiom-clean): `remCoord` (the low `m % ℓ` bits), `tileCoord`
(the `m/ℓ` disjoint blocks **plus** the remainder), `tile_injective`/`tileCoord_injective`,
`H₂_map_rem_le` (`≤ m % ℓ` bits) and **`sum_block_deficit_tile_le`**: with the window tiled
exactly, the full blocks carry a total deficit `≤ Δ` — **zero slack**, against
`sum_block_deficit_le`'s `|A|·ℓ + Δ`.

*Correction to the lap-28 handoff:* the `√(ℓ²/m)` term is NOT a sampling limit.  It came
entirely from the overlapping last coordinate.  With the tiling it disappears, so the
capacity inequality should read `≈ √(log 2 · ℓδ/m_K)` and the controlled range is
`ℓ = o(m_K/δ)` with **no** other ceiling.  (At `δ = 0` the bound then correctly gives an exact
frequency, which the lap-28 form did not.)

**✅ chain finished (lap 30):** `abs_avg_block_prob_tile_le` (averaging over the `⌊m/ℓ⌋`
disjoint blocks), `blockFreqT`, `abs_blockFreqT_sub_le_of_deficit`
(`≤ 2√(log 2·ℓδ/m_K)`, **no** deficit-free floor), `abs_blockFreqT_sub_le_primeLambertFour`
(`≤ 2√(200 log 2·ℓ/√K)`) and `tendsto_blockFreqT_growing`.  The controlled range is exactly
`ℓ = o(m_K/δ_K)`; for the implemented schedule `δ_K = 50√K` and `m_K = K/4` give `o(√K)`.

**✅ (a) done (lap 32):** `tendsto_blockFreqT_of_capacity` — deficits, words and reals all
free to vary, single hypothesis `ℓ_K δ_K/m_K → 0`.  `δ_K = K^{1/2−ε} ⇒ ℓ = o(K^{1/2+ε})` is
an instantiation.

**✅ (b) traced (lap 32), see `HANDOFF-2026-09-14-entropy-lap32.md`:**
`entropy_E1`'s `50√K` ← `entropy_cover_bound`'s floor `(92√K+51)/(K log 2)` ← `Lg = rDim(log 2
+ 23√K)` ← `log_det_one_add_tensorGram_le'` ← `√(K μ₂ + K(K−1) μ₁²)` with `μ₂ ≤ 520`.  The
`√K` is a **CLT-scale fluctuation** of `log Λ_j = ∑_i log λ_{j_i}`, not accounting slack; the
one loose step (`log(1+Λ) ≤ log 2 + |log Λ|`, wasteful for `Λ ≪ 1`) does not move the order,
because the log-spectrum is centred (`μ₁ → 0`) so ~half the tensor eigenvalues exceed 1.
**Verdict: `δ_K ≍ √K` is a wall of the spectral/cover route as built**; beating it needs
cancellation across `j`, not a better constant.

**✅ probe executed (lap 33)** — `G4EntropySpectral.lean`:
`log_one_add_le_log_two_add_posPart`, `sum_log_tensorLam` (exact first moment
`K s^{K−1} log(s+1)`), `log_det_one_add_tensorGram_le_pos`, and
**`log_det_one_add_tensorGram_le_twelve`**: at `s = K²`, `K ≥ 4`,
`log det(1+T^{⊗K}) ≤ (K²)^K(log 2 + 12√K)` against the `23√K` in use.  The constant nearly
halves (cover floor `92√K → 48√K`, so `entropy_E1` could run at `δ ≈ 25√K`); the **order does
not move**, because the gain is exactly the `1/2` of `(x)^+ = (|x|+x)/2` plus a mean term of
size `O(log K/K)`.  **`δ_K ≍ √K` is a wall of the spectral/cover route as built**; §5's
quantitative thread is closed.

### Decomposition — hardest first, and the order to build

1. **`G4EntropyGibbs.lean` — Gibbs + generalized subadditivity.**  The workhorse; reused three
   times.
   - `FinLaw.map (f : Ω → Ω') : FinLaw Ω'` — the pushforward, `p' ω' = ∑_{f ω = ω'} p ω`.
   - `gibbs : (∀ ω, 0 ≤ q ω) → (∑ ω, q ω ≤ 1) → (∀ ω, 0 < L.p ω → 0 < q ω) →
      L.H₂ ≤ −∑ ω, L.p ω * logb 2 (q ω)`.
     Proof: `∑ p·log(q/p) ≤ ∑ p·(q/p − 1) = ∑ q − 1 ≤ 0` via `Real.log_le_sub_one_of_pos`.
   - `H₂_le_sum_H₂_map : Function.Injective (fun ω i => f i ω) → L.H₂ ≤ ∑ i, (L.map (f i)).H₂`.
     Proof: Gibbs at `q ω = ∏ i, (L.map (f i)).p (f i ω)`; `∑_ω q ω ≤ ∑_{v} ∏ (L.map (f i)).p (v i)
     = ∏_i 1 = 1` by injectivity + `Finset.prod_univ_sum`.
   - ⚠️ the injectivity hypothesis is what makes this true; `E-T4` fires if the `ℓ`-block
     coordinates cannot meet it.
2. **`G4EntropyPinsker.lean` — the Hellinger route (no calculus).**
   - `key : 0 ≤ a → 0 < b → 2a − 2√a√b ≤ a·log a − a·log b`
     (at `a > 0` it is `log √(b/a) ≤ √(b/a) − 1` doubled; at `a = 0` both sides are `0`).
   - hence `klb p u ≥ (√p−√u)² + (√(1−p)−√(1−u))² ≥ (p−u)²/2` (nats), i.e.
     **`KL₂(p‖u) ≥ (p−u)²/(2 log 2)`** — a factor 4 weaker than Pinsker and entirely sufficient.
   - two-point Gibbs (`q = p/|E| on E, (1−p)/|Eᶜ| off`) gives
     `KL₂(L B ‖ |B|/|Ω|) ≤ logb 2 |Ω| − L.H₂`.
3. **`G4EntropyWord.lean` — the block coordinates and the assembly.**
   - `blockCoord ℓ j : Fin (2^m) → Fin (2^ℓ)` extracting the `j`-th aligned `ℓ`-block, plus the
     remainder coordinate; injectivity of the combined map.
   - bridge to digits: `blockVal y (p + jℓ) ℓ` via `blockVal_succ` / `blockVal`'s definition.
   - `∑_{(α,j)} ε_{α,j} ≤ Δ_K` from (1) + `entropy_E1`; then
     `|freq(w) − 2^{−ℓ}| ≤ (1/(rH))·∑ √(2 log 2 · ε) ≤ √(2 log 2 · Δ_K/(rH))` by AM-GM
     (`√x ≤ (x/t + t)/2`, optimise `t`), **not** by hunting a Cauchy–Schwarz lemma name.
   - final `Filter.Tendsto` along the admissible scales.

### Not to do

Re-proving or tidying `entropy_E0`/`entropy_E1`; more barrier/characterization variants (closed
at lap 22); any pre-expedition G4/G5 file; a trusted axiom for any of the above; retreating to a
fixed-offset frequency statement (lap 15 already refuted that one).

---

## ✅ CLOSED — brief §6 is a CHARACTERIZATION, not a bound (entropy laps 16–17, 2026-09-14)

Lap 16 (`G4EntropyDensityOne.lean`) sharpened the locality barrier from *density ≥ 1/2* to
*density = 1*: comparing the zero filling of the unread positions with the parity filling (a `1`
at the even-indexed positions of `Sᶜ`) forces both ones-densities to be exactly `1/2`, so `Sᶜ`
has density `0`.  `exists_nonnormal_of_digitLocal_of_lt_one` therefore refutes at **any** `c < 1`.

Lap 17 (`G4EntropyStable.lean`) showed the threshold is attained: normality is invariant under
density-zero digit changes (`isNormal_congr_of_density_zero`), so at density one normality is
itself digit-local.  `exists_digitLocal_forces_normal_iff` states the characterization (modulo
the existence of a binary normal number in `[0,1)`, carried as a hypothesis).

**Consequence for the campaign.**  Inside digit-locality there is no repair to look for: a
sampler would have to read all but a density-zero set of the digits of `G₄`, at which point its
hypothesis *is* normality.  The open room is outside digit-locality only.

Open items, hardest first:

1. **Name the non-digit-local room.**  State `IsBlockLocal` and prove the `G4Jackson` /
   `G4SeparatingTest` bounded-Lipschitz bump functional is not block-local (two reals with the
   same sampled blocks at every scale, different bump values).  That is what an entropy
   statement would have to be about instead of `E0`.
2. ~~`∃ z ∈ [0,1), IsNormal 2 z`~~ — **done, lap 18**: the repo's `isNormal_two_stoneham23`
   supplies it (`exists_isNormal_mem_Ico`), so `forces_normal_iff_density_one` is
   unconditional.
3. A sampler not built from a frozen CRT modulus (session-wrap item 2).  Still open as
   mathematics, but lap 16–17 raise its bar from `density ≥ 1/2` to `density → 1`, which no
   arithmetic sampler of this shape can meet.

---

## ✅ RESOLVED — brief §6 `T_E` is **REFUTED** (entropy lap 8, 2026-09-14)

`NormalNumbers.G4.Sched.not_T_E : ¬ T_E`, axiom-clean, `HANDOFF-2026-09-14-entropy-lap8.md`.
The witness is `maskedReal G₄` — `G₄`'s digits at the sampled positions, `0` elsewhere — which
has *literally the same joint law at every scale* (so it satisfies `entropy_E0`/`entropy_E1`
verbatim) and at most a quarter `1`s.  The plan below was executed as written.

**The frontier moves to brief §6's POSITIVE branch.**  Open items, hardest first:

1. `T_S`, `T_mix` — state over the same family, refute with the same witness
   (`jointLawAt_maskedReal`).  Cheap; completes the §6 column.
2. **Which extra arithmetic input reads a positive-density set of positions?**  The
   obstruction is now explicit and quantitative: `d_α ∣ kIdx` (`kIdx_spec`) plus `kIdx ≠ 0`
   confine scale-`K` positions to multiples of `2 d_α` with `d_α ≥ 1 + Q_K D₀_K`, so ONE grid
   can never exceed density `H_K m_K/(2 d_min)`.  Any repair must vary `t_α` (equivalently
   `b₀`) across a family of admissible samplers covering a positive fraction of the residues
   mod `2 d_α` — and the brief warns that an output translation `θ − γ` does NOT grant
   arbitrary input residues.  Name the property, prove the implication, compute `w_{K,ℓ}`.
3. Brief §5's (S): still open, still a leaf — worth stating as *what entropy controls*, not as
   a step toward normality.

---

## (executed) THE CRUX — brief §6 `T_E` (entropy review lap 8, 2026-09-14)

**Read the entropy CURRENT DIRECTIVE in `DIRECTION.md` first; it outranks any handoff.**
§2/§3/§4 are closed (`entropy_E0`, `entropy_E1`, axiom-clean).  §5's (S) is a LEAF and is
deprioritized.  The route-decisive blocker is the transfer

  `T_E : ∀ x ∈ [0,1), E0 for Z^x_K → IsNormal 2 x`.

### The lap-8 insight: the sample is DIGIT-LOCAL, so `T_E` is a DENSITY statement

`ZSample_eq_blockVal` : `Z^x_{K,α}(n) = blockVal (fract x) (2·kIdx G n α) m_K` — the `m_K`-bit
binary window of `x` at position `2k`.  So `Z^x_K`, `jointLaw`, and `H₂` depend on `x` ONLY
through the digits of `x` on the sampled position set

  `S_K := {2·kIdx G n α + h : n ∈ P_K, α ∈ Atom, h < m_K}`,   `S := ⋃_{K admissible} S_K`.

Hence if `y` copies `G₄`'s digits on `S` and is `0` off `S`, then `E0(y) ↔ E0(G₄)`, and
`E0(G₄)` is **proved** (`entropy_E1` + `H₂_jointLaw_le_mul` pin the ratio in
`[1 − 200/√K, 1]`).  So

  `T_E ⟹ IsNormal 2 y ⟹ (density of 1s in y) → 1/2 ⟹ lower density of S ≥ 1/2.`

### Why `S` is sparse (the arithmetic that has to be formalized)

1. `kIdx_spec` **already proves `d_α ∣ kIdx G n α`** (the frozen multiplier residue).
2. `kIdx G n α = 0` would force `n = t_α`; but `n ≡ b₀ (mod P₀)` with `n, b₀ < P₀` gives
   `n = b₀`, so `b₀ = t_α`; then for every `β`, `t_α ≡ t_β (mod d_β²)` with both
   `< d_β²` (`t_γ = Q·gridV γ ≤ Q·D₀ < d_β`), so `gridV` is constant — false, since
   `gridV 0 = 0` and `gridV e₀ = B ≠ 0`.  **So `kIdx ≥ d_α`.**
3. Therefore every sampled position is `2·(c·d_α) + h` with `c ≥ 1`, `h < m_K`, so
   `|S_K ∩ [0,L)| ≤ Σ_α m_K·⌊L/(2 d_α)⌋ ≤ H_K·m_K·L / (2·d_min(K))`,
   `d_min(K) = 1 + Q_K·D₀_K`, `Q_K = (gridUmax + K + N + 2)!`.
   `Q_K ≥ 2^{gridUmax} ≥ 2^{B^K}` dwarfs `H_K m_K = (K²+1)^K·K/4`, so each scale contributes
   density `≤ 2^{-K}`; and the terms with `2 d_min(K) > L` vanish identically, so the union
   over all admissible `K` is a FINITE sum at each `L`.  Upper density of `S` is `≪ 1/4`.
4. Witness: `y := realOfDigits 2 (fun j => if j ∈ S then digitOf 2 (fract G₄) j else 0)`,
   proper (infinitely many `0`s), `y ∈ [0,1)` (`realOfDigits_mem_Ico`),
   `digitOf 2 y = s` (`digitOf_realOfDigits`).  The count of `1`s below `L` is
   `≤ |S ∩ [0,L)| ≤ L/4`, so the frequency cannot tend to `1/2`.

The SAME witness refutes `T_S` and `T_mix` (identical laws), so brief §6's whole transfer
column falls together.

### Files (one writer each)

| file | content | status |
|---|---|---|
| `G4EntropyLocality.lean` | `blockVal_congr`, `ZSample_congr`, `ZVec_congr`, `jointLaw_congr`, `H₂_congr` | lap 8 |
| `G4EntropyPositions.lean` | `kIdx_pos`, `kIdx_ge_d`, `sampledPos`, the `⌊L/2d⌋` count, `dmin` bound | lap 8 |
| `G4EntropyTransfer.lean` | `E0`/`T_E`/`T_S`/`T_mix` `Prop`s, `E0_primeLambertFour`, masked witness, `not_T_E` | lap 8+ |

### After `not_T_E` (do NOT drift to §5 as a consolation)

The expedition's real output becomes: *which additional arithmetic input closes the gap?*
Brief §6 positive branch item 1 — average over a proved family of admissible samplers
(translated grids / varied frozen residues) so the sampled positions stop having density zero.
Name that property independently of normality and prove the implication it supplies.

---

## Entropy expedition (2026-09-14, branch `wip/g4-entropy`) — ACTIVE

Lap 1 done (`HANDOFF-2026-09-14-entropy-lap1.md`).  Proved sorry-free: the information-set
lemma (`G4EntropyInfo.prob_infoSet_ge` + `card_infoSet_le`), the frozen arithmetic sample and
its binary dictionary (`G4EntropySample.ZSample_eq_blockVal`, `kIdx_spec`), and the abstract
capture inequality (C) with its bounded-Lipschitz bump
(`G4EntropyCapture.capture_inequality`, `abs_sampleAvg_sub_integral_le`, `bump_sub_le`).

Lap 2 added `G4EntropyJackson.lean` (Fejér smoothing for an ARBITRARY bounded `dAv`-Lipschitz
test, budgets independent of the test; `Frame.propJackson` recovered as
`propJackson_of_general`) and `G4EntropyFrame.lean` (`capture_inequality_torus`,
`Frame.capture_le`: (C) on the torus with every input supplied by existing machinery).

**After lap 2 the ONLY remaining obligation between the implemented schedule and E0 is the
cover bound (G).**  `Frame.capture_le` reads

    |Good|/|P| ≤ vol(tube E res) + δ₂ + 2/(res√(D+1)) + (2D+1)^r·δ₃

for an arbitrary nonempty `E` — δ₂ is `PropD`, δ₃ is `PropC`, and the κ/Λ budgets are the
frame's own and do not depend on `E`.  Choosing `E = E_K(ℬ)` leaves `vol(tube (E_K ℬ) res)`
as the single unproved quantity.

Lap 3 proved **(G)** in `G4EntropyCover.lean`: `volume_tube_le_joint` gives
`vol(tube (E 𝓑) res) ≤ ∑_{G good} |𝓑|·η^{|G|}·vol(pieceCube G)` — the cover factor is
**linear in the number of joint boxes**, not `(#Bs)^H`.  The old product statement is
recovered as `volume_tube_le_of_joint`.

Lap 4 proved **§3A** in `G4EntropyTransport.lean`: `Ffull_eq_of_progression` exposes the exact
transported vector as an EQUATION (`PropA` recovered via `propA_of_Ffull_eq`), and
`gridFrame_Ffull_mem_boxUnion` closes the chain §3A ⟹ §3B: the quantized sample of `n` selecting
a centre in `𝓑` puts `Ffull n` in `imageOfSet (boxUnion 𝓑 2^{-m})`, which is exactly the
hypothesis of `Frame.capture_le` for the set whose tube `volume_tube_le_joint` bounds by `|𝓑|`.

Lap 5 assembled **E0** as `G4EntropyE0.entropy_gt_of_budget`: whenever

    2^{(1−δ/2)M}·(∑_{G good} η^{|G|}·vol(pieceCube G)) + δ₂ + 2κ + Λδ₃  <  δ/(2−δ)

holds (with `PropC δ₃`, `PropD δ₂`, `2^{-m} ≤ η`, `0<δ<1`, `0<M`), then
`(1−δ)·M < H₂(jointLaw)`.  **E0 now has NO remaining structural obligation** — it is a single
numeric inequality about the implemented schedule.

**What remains, hardest first:**

1. **Discharge the E0 budget at `M = m_K H_K`, `δ = δ_K`** against `G4ScheduleParams`.  The
   left side is the old tube/determinant budget with the entropy factor `2^{(1−δ/2)m_K H_K}`
   replacing `(#Bs)^{H_K}`; the right side is `δ/(2−δ)`, which for `δ → 0` is `≈ δ/2`, so the
   budget must beat a *shrinking* target — that is the real content of brief §4 and the place
   where the proposed `D_K = (16K²2^{m_K})²` and `κ_K ≤ 1/(16K)` must be justified.
   Note `∑_G η^{|G|}vol(pieceCube G)` is exactly what `G4GridTube`/`G4Ellipsoid`/`G4Tensor`
   already bound for the disjunctivity endpoint; only the prefactor changed.
2. **`a_K/ρ_K → 0`** — recover the average transport error from the actual remainder bounds
   (`G4Remainder`, `G4FarTail`), not the old fixed 1/8 allowances.
3. **Jackson at the entropy degree** — `G4Jackson` must approximate the `1/ρ_K`-Lipschitz,
   `[0,1]`-valued `bump` to within `κ_K ≤ 1/(16K)` at `D_K = (16K²2^{m_K})²`, and the arithmetic
   budget must still accept that degree (an obligation, not a given — brief §4).

Then E0/E1 by combining (C), (G) and the information-set lemma; then §5 (S); then §6 T_E.

---

# PENDING WORK — Phase 3 publishing-prep complete locally

## G5 — 2026-09-14 (lap 1, grind) — the interface EXISTS: `w_c = ω + ∑_p c_p (v_p − 1)`, transport exact, junk AP-mean proved

### Proved this lap (axiom-clean, `lake build` 8938 jobs green)

`src/NormalNumbers/G4WeightInterface.lean` (new)
* `valWeight c m = ∑_p c_p v_p(m)` (completely additive, `valWeight_mul`), `omegaW c m = ∑_{p∣m} c_p`,
  `excess c = valWeight − omegaW = ∑_{p∣m} c_p (v_p(m) − 1)`, **`weightW c = ω + excess c`**,
  `weightLambert b c = ∑_n w_c(n)/bⁿ`, and the ℕ-valued `weightN c` with `weightW_eq_cast`
  (the digits are integers — needed by the orbit identity `bᵏx = ℤ + tail`).
* **Instances**: `weightW_zero : weightW 0 = omegaR` (so `weightLambert_zero :
  weightLambert b 0 = primeLambertAtBase b`, literally) and `weightW_one : weightW 1 = Ω`
  (`weightLambert_one : weightLambert b 1 = ∑ Ω(n)/bⁿ`).
* **Exact transport** `excess_mul : excess(dm) = excess(d) + excess(m) + ∑_{p∣d, p∣m} c_p`,
  `weightW_mul : w(dm) = w(m) + w(d) − ∑_{p∣d,p∣m}(1 − c_p)`, periodic modulo `rad d`
  (`overlapW_congr`).  So `G4Transport` ports with `corrB` replaced by `overlap − overlapW`.
* Growth/summability: `excess_le : excess c ≤ C(Ω − ω)`, `two_pow_cardFactors_le : 2^Ω(m) ≤ m`,
  `summable_weightW_div_pow` for `b ≥ 2` and `c_p ≤ C`.

`src/NormalNumbers/G4WeightJunk.lean` (new)
* **The split on the progression modulus** `P₀`: `excess_eq_frozen_add_junk` —
  `excess = frozenExcess + junk`, with `frozenExcess c P₀ m = ∑_{p∣P₀} c_p (min(v_p(m), v_p(P₀)) − 1)`
  a function of `m mod P₀` (**`frozenExcess_congr`**, so it goes into the translate `γ`) and
  `junk c P₀ m = ∑_p c_p (v_p(m) − E'_p)₊`, `E'_p = max(v_p(P₀), 1)`.
* **One-congruence counting** `card_filter_pow_dvd_le`:
  `#{n ∈ apSample X P₀ b₀ : p^{E'_p+u} ∣ n+ρ} ≤ X/(P₀ p^{E'_p+u−v_p(P₀)}) + 1`
  (the condition cuts the progression to one class mod `P₀ p^{…}`: `gcd(p^a, P₀) = p^j`, `j ≤ v_p(P₀)`,
  cancel, count a residue class in `[0, X/P₀]`).
* **`sum_junk_le`** — the sample sum of the junk at any shift `ρ ≥ 1`:
  `∑_{n∈P} junk(n+ρ) ≤ C·((X/P₀)(∑_{p∣P₀} 1/(p−1) + 1) + (√(X+ρ)+1)·log₂(X+ρ))`,
  with `sum_inv_pred_le_harmonic : ∑_{p∈S} 1/(p−1) ≤ H_{|S|}` and `H_n ≤ 1 + log n`, so against
  `|P| ≥ X/(2P₀)` the mean is `≤ 2C(log ω(P₀) + 2) + 2C P₀(√(X+ρ)+1) log₂(X+ρ)/X`.

### STRUCTURAL FINDING — the directive's "decisive probe" (C2 with valuations) is NOT needed

The CURRENT DIRECTIVE names `G4LocalContraction.norm_localSum_le` as the decisive case, with
the local model to be changed from the indicator `1_{p∣m}` to residues mod `p^T`.  In the
formulation above that step does not exist: the frame's small-prime vector `S` stays the
`ω_sm`-vector (`Sval` over `smallPrimes R P₀`), so `PropC` (§4C, C1–C3, the CRT input, the
Fourier box) is **untouched**; the whole difference `w_c − ω = excess c` is linear in the
statistic and rides `PropD` (§4D) as one more averaged remainder, exactly like the very-large
primes.  So the honest decisive case is the **junk AP-mean**, and it is now proved
(`sum_junk_le`).  (One could alternatively fold the valuations into the Fourier model — C2 with
multiplicities and junk classes is a triangle-inequality corollary of the present C2, the gain
becomes `4(1−1/p)D` — but that is strictly more work for nothing: the junk needs no
cancellation, only smallness.)  W-T1 therefore does not fire; the interface survives.

**Why exactly this class** (isolated, not yet a theorem): for an additive `w = ∑_p g_p(v_p)`,
the exact transport identity (`w(dm) − w(m) − w(d)` periodic mod `rad d`) holds iff every
`g_p` is affine on `v ≥ 1`, i.e. `g_p(v) = a_p + c_p(v − 1)`; and the Fourier control is proved
for the indicator model, i.e. `a_p = 1`.  Hence `weightW c` is the largest class the present
proof reaches without re-doing §4C.  Coefficients must be natural numbers (integer digits).

### Budget check (paper, to be formalised in the schedule port)

Retained-layer junk: `≤ rowL1 · max_ρ E[junk(n+ρ)] ≤ ((2/b)^K/(b−1)) · 2C(log ω(P₀) + 2 + o(1))`
against `δ·εη = δ 2^{−K/4}/(8K)`: needs `(b/2)^K 2^{−K/4} ≳ CK log(logP₀Nat)`, i.e. `C ≤ 2^{K/10}`
say — put `C ≤ K` into `Hyp`.  Far-tail excess (`j > J`): `excess ≤ C(Ω−ω)`, whose AP-mean at
shift `ρ_j ≤ j·Dm` is `≤ C(log₂ P₀ + 2 log ω(P₀) + 4) + C·2P₀(√(X+jDm)+1)log₂(X+jDm)/X`; the
first is of the size of `farC`, the second is `≤ (j+1)²·(tiny)` with `tiny = 4P₀ log₂X/√X`, and
`∑_{j>J} b^{−j}(j+1)² ≤ 4(2/b)^{J+1}/(1−2/b)`.  Both fit the existing `farBound` shape after
widening `C₀`.

### Next actions (in order; every step green + committed)

1. ✅ DONE (`f9c2f62`). **Weight-generic frame** (`G4Wiring`): add `w : ℕ → ℝ` and `x : ℝ` to `Frame`, `Ffull` with
   `w`, `image` over `orbitClosureOf bse x`; `gridFrame` sets `w := omegaR, x := primeLambertAtBase`
   so every existing theorem is unchanged.  `finite_contradiction`, `isDisjunctive_of_frames`
   generalised to `SeparatingFrameExistsW bb x` with the old one its instance.
2. **Transport** (`G4Transport`): `tailBW`, `tailIntW` via `weightN`, `corrW = overlap − overlapW`,
   `dilatedTailW_eq`, `propA_of_progression` for `w_c`.
3. **Remainder** (`G4Remainder`/`G4FarTail`): `Ffull_w = Ffull_ω + excessPart`; retained excess =
   frozen (into `γ_w`) + junk (`sum_junk_le`); far excess via `excess ≤ C(Ω−ω)` and the same
   split at `c = 1`.  New `PropD` bound = old + `C·junkBound`.
4. **Schedule** (`SchedB`): `Hyp` gains `C ≤ K`; `hbig`/`hfar` gain the junk terms; assemble
   `isDisjunctive_weight : 3 ≤ b → (∀ p, c p ≤ C) → C ≤ ? → IsDisjunctive b (weightLambert b c)`;
   instances `isDisjunctive_base'` (must equal `isDisjunctive_base`'s statement) and
   `isDisjunctive_Omega`.
5. The series identity `∑_n Ω(n)/bⁿ = ∑_{p,a} 1/(b^{pᵃ}−1)` (W-T2 if rearrangement resists).

## G5 — 2026-09-14 (review lap 16) — base two REFUTED at the design level; new campaign = the weight interface

### Proved this lap (axiom-clean, `lake build` 8935 jobs green, HEAD `4991939`)

* `NormalNumbers.IsDisjunctive.irrational` — disjunctive ⇒ irrational, **any** base.
  `x = a/q` makes `q·orbit b x n` an integer for every `n`, so the orbit misses
  `[1/(2|q|), 1/|q|)`, an interval disjunctivity must hit.
* `NormalNumbers.IsDisjunctive.exists_ge` — every target interval is hit **arbitrarily late**:
  cut `[a,c)` into `N+1` disjoint pieces, each is hit, the hitting times are distinct (the
  pieces are disjoint), so one of them is `≥ N`.  Word form `exists_occursAt_ge`.
* Instances: `G4.irrational_primeSum : 3 ≤ b → Irrational (∑' p : Nat.Primes, 1/(bᵖ−1))`,
  `irrational_primeLambertAtBase`, `irrational_primeLambertFour`,
  `every_word_occurs_base_late`, `every_binary_word_occurs_late`.
  This is an independent machine-checked proof of the `b ≥ 3` half of the prime-Lambert
  irrationality family (Tao–Teräväinen arXiv 2512.01739 Thm 1.3 is the base-two case).

### REFUTED this lap: base two, for the whole design family (not just our parameters)

Lap 13 showed `rowL1 2 K = 1` for **our** array `A = D_s^{⊗K}`.  The sharper statement:

1. `rowL1 = (∑_α |A_{aα}|) · ∑_{j>K} b^{−j}`.  A tensor coordinate kills exactly one layer
   (the shift is `ρ_{αj} = j·d_α − t_α`, affine in the atom digits, so `α_i` drops out of
   layer `j` iff `j·D_i = T_i` — one `j` per coordinate).  Hence to leave the survivors at
   `j > K` one must kill layers `1..K`, i.e. have vanishing line sums in `K` directions.
2. **Lower bound (formalisable, and the next proof item):** a nonzero integer array on a
   `K`-dimensional grid whose line sums vanish in every direction has `L¹ ≥ 2^K`.  Induction:
   each slice has vanishing line sums in the other `K−1` directions, at least two slices are
   nonzero (their sum is zero), each has `L¹ ≥ 2^{K−1}`.
3. So `rowL1 ≥ 2^K·b^{−K}/(b−1)`, which at `b = 2` is `≥ 1` for **every** design in the
   family: the factor 2 cost of killing a layer exactly cancels the factor `b^{−1}` gain.
4. And no choice of the cutoff `Y` escapes.  The medium range's pair-counting error is
   `π(Y)²·rowL1²/|P|`, so it needs `Y ≲ √X`; a far range handled by *non-negativity*
   (pointwise or on average) costs `rowL1 · ∑_{p>Y} 1/p ≍ rowL1 · log(log Mx/log Y)`, which is
   `≳ rowL1·log 2` unless `Y ≥ X^{1−o(1)}`.  At `b ≥ 3` the vise is harmless because `rowL1`
   decays in `K`; at `b = 2` it is closed.
5. The only repair is **signed** cancellation in `p > Y`, i.e. an asymptotic for the shifted
   correlations `E_n[1[P⁺(n+u) > Y]·1[P⁺(n+v) > Y]] = ρ² + o(rowL2/rowL1²)` uniform in the
   shift pair — a Bombieri–Vinogradov / Titchmarsh-divisor-strength input, and precisely the
   "deep two-point correlation theorem" the brief forbids inheriting.  **Struck from the
   stretch list; base two belongs to Tao–Teräväinen.**

### New campaign G5 — the arithmetic input becomes an interface

Objective, attack order and triggers: `DIRECTION.md` CURRENT DIRECTIVE.  In brief —
`IsDisjunctive b (∑_n w(n)/bⁿ)` for `b ≥ 3` and every additive weight `w` in a named
interface, instantiated at `w = ω` (must re-derive `isDisjunctive_base`) and at `w = Ω`
(new: `∑_{q = pᵃ} 1/(b^q − 1)`).  `ω` is load-bearing in five places; four need only
`w(n) ≤ log₂ n` and the multiplicative defect.  **Decisive case: C2**
(`G4LocalContraction.norm_localSum_le`), whose model is the indicator `1_{p∣m}` and must
become `v_p(m)`: keep the `v_p = 1` classes (mass `(1/p)(1−1/p)`, phase exactly `xᵢ`), absorb
`v_p ≥ 2` as junk of mass `≤ k/p²`; `∑_p k/p² = O(T) = L^{0.02+o(1)}` loses to the gain
`θ₀L = L^{1−o(1)}`.

### Note on the two legacy `src/` sorries (unchanged, both correctly disclosed)

* `MahlerDriftOne.exists_prime_nonresidue` — needs cancellation in `∑_{q ∈ (p/3,p/2)} χ_p(q)`
  over primes with `q ≍ p`, i.e. Burgess + Vinogradov (Karatsuba); not Linnik-repairable,
  reaches only a CONDITIONAL theorem.
* `PrimeLambertOscillation.phaseOscillation` — the old base-two irrationality route, now
  superseded in the literature and refuted *on this repo's route* by the item above.


## G4B — 2026-09-14 (lap 14) — CAMPAIGN CLOSED: `isDisjunctive_base` proved for every `b ≥ 3`

`NormalNumbers.G4.isDisjunctive_base : 3 ≤ b → IsDisjunctive b (primeLambertAtBase b)`
(`G4SchedBAssembly.lean`), `#print axioms = [propext, Classical.choice, Quot.sound]`.
Corollaries: `isDisjunctive_primeSum` (`∑_p 1/(bᵖ−1)` form), `every_word_occurs_base`,
`isDisjunctive_root` (base `c` for `∑ ω(n)/(cᵏ)ⁿ`, `cᵏ ≥ 3`), `isDisjunctive_four'` (the
`b = 4` instance; the original `isDisjunctive_four` / `isDisjunctive_two` are untouched).

What was proved this lap, bottom-up (all committed green, HEAD `20c43d8`+):
1. The concrete grid layer in any base `bb ≥ 2` (`97179b1`): `Sval bb`, `blockSum bb`,
   `farPart bb`, `rowCoeff bb`, `gridFrame bb hbb`; named masses `rowL1/rowL2/farBound`;
   PropA/B/C/D closed forms in `bb`.
2. The frequency-separation seed in any base (`56e4808`): `freqDepthB`, `freqSeed b K =
   b^{−4}(2/b²)^K`, `sum_sq_distZ_freqDepthB_ge`, `gridFrame_propC_gen`.
3. `ScheduleWitnessB bb ℓ w`, `isDisjunctive_of_witnessB` (`3aef25c`).
4. The §5 schedule in `(b, K)`: `SchedB` (`G4SchedBParams`, `G4SchedBBudget`,
   `G4SchedBAssembly`) with `m₁ b K = 1000·b^{2K+4}·K^{2K+1}` so that
   `θ₀·m₁ = 1000·2^K·Kr`; ladder under `Hyp b K = (3 ≤ b, 2b² ≤ K, 100 ≤ K)`;
   `k₄ = 8464 ℓ² b^{2ℓ+2}`, `M = ⌈K log 2/(4ℓ log b)⌉`; `hbig`/`hfar` at the worst case
   `b = 3` (`rowL1 ≤ (2/3)^K/2 ≤ η²/2`, `rowL2 ≤ (2/9)^K/8 ≤ η⁸/8`, `farBound b ≤ farBound 3`).

Design note (deliberate): the base-four `Sched` modules are kept verbatim and `SchedB` is a
parallel, base-general schedule (`m₁` differs, so the old numeric schedule is not literally
the `b = 4` instance of the new one).  The *theorem* `isDisjunctive_four'` IS an instance of
the general theorem, which is what `DIRECTION.md` requires; `isDisjunctive_four` stays as the
independent base-four proof.  Retiring `G4Schedule{Far,Big,Harmonic,Budget,Assembly}` in favour
of `SchedB` would be a docs/cleanup lap, not mathematics.

Nothing open on G4B.  Base two remains REFUTED on this route (`rowL1 2 K = 1`, see below).

## G4B — 2026-09-14 (review lap 13) — the base-`b` theorem, and why `b = 2` is refuted

### Verification of the closed base-four campaign (re-done from scratch this lap)

`lake build` 8930 jobs green.  `#print axioms` = `[propext, Classical.choice, Quot.sound]`
for `G4.isDisjunctive_four`, `G4.isDisjunctive_two`, `G4.G4DisjunctiveFour_holds`,
`G4.G4DisjunctiveTwo_holds`, `G4.every_binary_word_occurs`,
`PrimeLambert.primeSumAtBase_four`, `PrimeLambert.summable_omegaR_div_pow`.
`grep -rn '^ *axiom ' src/` → **nothing**: the repo contains no local axiom at all.
Definitional audit against the brief's frozen statement: `IsDisjunctive b x = ∀ a c, 0 ≤ a →
a < c → c ≤ 1 → ∃ n, orbit b x n ∈ Ico a c` ✓, `orbit b x n = Int.fract (x·bⁿ)` ✓,
`omegaR n = ArithmeticFunction.cardDistinctFactors n` ✓, `primeLambertAtBase b = ∑' n, ω(n)/bⁿ`
✓, `primeSumAtBase b = ∑' p : Nat.Primes, 1/(bᵖ−1)` ✓, `OccursAt` via `digitOf` ✓.
Because the kernel guarantees the proof *given* the definitions, and the definitions are
faithful, the base-four theorem stands.

### The `b`-dependence of the five `ScheduleWitness` inequalities (symbolic re-derivation)

Write `A = D_s^{⊗K}`, so every row has `2^K` entries `±1` and `∑_α|A_{aα}| = ∑_α A_{aα}² = 2^K`
(`G4RowMass.sum_abs_kronPow_diffZ`, `sum_sq_kronPow_diffZ`).  Retained layers are `K < j ≤ J`.
Replacing the base-four weight `4^{−j}` by `b^{−j}`:

| quantity | base four (in `src/`) | general `b` | `b = 2` | `b = 3` |
|---|---|---|---|---|
| `∑_{j>K} b^{−j}` | `4^{−K}/3` | `b^{−K}/(b−1)` | `2^{−K}` | `3^{−K}/2` |
| `∑_{j>K} b^{−2j}` | `16^{−K}/15` | `b^{−2K}/(b²−1)` | `4^{−K}/3` | `9^{−K}/8` |
| row `L¹` `∑_{α,j}|c|` | `(1/2)^K/3` | `(2/b)^K/(b−1)` | **`1`** | `(2/3)^K/2` |
| row `L²` `∑_{α,j}c²` | `(1/8)^K/15` | `(2/b²)^K/(b²−1)` | `2^{−K}/3` | `(2/9)^K/8` |
| freq. seed `θ₀` | `4^{−4}8^{−K}` | `b^{−4}(2/b²)^K` | `2^{−4}2^{−K}` | `3^{−4}(2/9)^K` |
| `hB` deficit per `M` | `4^{−ℓ}` | `b^{−ℓ}` | `2^{−ℓ}` | `3^{−ℓ}` |

**hB (the `X`-free geometry) gets EASIER as `b` shrinks.**  With `η = e^{−λ}` and
`M = ⌈λ/(ℓ log b)⌉` (the minimum allowed by `hM : b^{−ℓM} ≤ η`), `log(b^ℓ−1) ≤ ℓ log b − b^{−ℓ}`
gives a deficit `M·b^{−ℓ} ≈ λ b^{−ℓ}/(ℓ log b)` against the `b`-independent costs
`(log 2)/4 + log 6 + log 2 + 11.5√K`.  So `hB` needs `λ ≳ 11.5·√K·ℓ·b^ℓ·log b`; at `b = 4`,
`λ = (K log 2)/4` and `K ≥ 33856 ℓ²16^ℓ` is the recorded sufficient hypothesis, matching
`√K ≥ 184ℓ4^ℓ`.  General `b`: `√K ≥ Θ(ℓ b^ℓ log b)`.

**θ₀ gets LARGER as `b` shrinks** (`(2/b²)^K` vs `(2/16)^K`), so `hbudget`'s contraction
`exp(−4θ₀∑_{p∈sm}1/p)` is *better* at small `b`.

**hbig is where `b` bites, and it REFUTES `b = 2`.**  `hbig`'s last term is the
very-large-prime (`p > Y`) contribution, bounded **pointwise** in `G4MediumPrimes.
abs_blockSum_omegaVL_le` by `(log Mx / log Y) · ∑_{α,j>K}|c_{αj}|`, i.e. by
`(log Mx/log Y)·(2/b)^K/(b−1)`, and `hbig` requires it `≤ δbig·(ε·η)`.  Since `ε < 1`,
`η < 1`, `δbig ≤ 1` and `log Mx/log Y ≥ 1`, a NECESSARY condition is `(2/b)^K/(b−1) < 1`.

* **`b = 2`: the row `L¹` mass is exactly `2^K·2^{−K}/1 = 1`, independent of `K`.**  `hbig`
  is then unsatisfiable for every `η, ε, K, X, Y, R`.  Raising `η` cannot help (`εη < 1`),
  and lowering it is worse.  **`b = 2` is refuted on this route**, which is precisely why the
  brief's §7.1 says `b ≥ 3`.  Downstream: `gridFrame_propD_of_bounds` is the implication that
  fails; the weakest repair actually justified is to demand `2/b < 1` strictly, i.e. `b ≥ 3`.
* **`b ≥ 3` closes**: the mass is `(2/b)^K/(b−1) = e^{−Θ(K)}` and must beat
  `εη = e^{−Θ(√K)}/K`, which holds for `K` large in terms of `ℓ` — the same regime `hB`
  already forces.

**hfar** scales as `2^K b^{−(K+N)}(farC + 2(K+N) + 2)/(b−1)`; the same `(2/b)^K` factor appears,
so `b ≥ 3` again, and `N = Θ(log_b(K·L))` as before.

### Attack order (mirrors `DIRECTION.md`)

1. ✅ **DONE (lap 13)** `G4ScheduleB.lean` in `b` — `log_pow_sub_one_le`,
   `deficit_dominates`, `gridB_bound` all base-general; `gridParams_hB` is the `b = 4`
   instance and recovers `K ≥ 33856 ℓ² 16^ℓ` exactly.
2. ✅ **DONE (lap 13)** `G4Covering.lean` — `block`, `block_lt`, `orbit_eq_block_add`,
   `orbit_expansion`, `block_ne_of_omit`, `orbit_mem_cyl`, `orbitClosure_subset_cylinders`
   all take the base `bb` with only `0 < bb`.  `cylLeft`/`cyl`/`admissible` were already
   base-free.  `G4GridTube.exists_cover_of_omit` is the `b = 4` call site.
3. ✅ **DONE (lap 13)** the abstract `Frame` layer is base-general.  `Frame` carries
   `bse : ℕ` and `hbse : 2 ≤ bse`; `Ffull n ν = (∑_α A_{να} ∑_{j≥1} ω(n+ρ_{α,j})/bse^j) − γ_ν`;
   `orbitClosure bb = closure {orbit bb (primeLambertAtBase bb) n}` and `Frame.image` uses
   `orbitClosure fr.bse`; `G4Transport`'s transport identity is now stated at `fr.bse`
   (`coe_tailB`, `transportTheta` with `ω(d_α)/(b−1)`, `coe_sum_dilatedTailB`,
   `propA_of_progression`) — the base-`b` tail machinery `tailB/tailIntB/corrB/dilatedTailB`
   was ALREADY general, only the `Frame` face was pinned at 4.  `SeparatingFrameExists bb`
   and `isDisjunctive_of_frames : SeparatingFrameExists bb → IsDisjunctive bb
   (primeLambertAtBase bb)` are the general conditional headline; `isDisjunctive_four_of_frames`
   is its `b = 4` instance.  `gridFrame` sets `bse := 4`, so the whole concrete grid layer
   (`G4Remainder`, `G4RowMass`, `G4MediumPrimes`, `G4FarTail`, `G4Schedule*`) is untouched
   and still green.
4. ✅ **DONE (lap 14, `97179b1`)** the concrete grid layer in any base `bb ≥ 2`.  The base is
   an explicit argument (not a `GridParams` field): `coeffAL bb`, `Sval bb`, `blockSum bb G`,
   `farPart bb G`, `rowCoeff bb G`, `frozenGamma bb G`, `bigAvg bb`, `farAvg bb`,
   `gridFrame bb hbb G …`.  Named masses `rowL1 b K = (2/b)^K/(b−1)`,
   `rowL2 b K = (2/b²)^K/(b²−1)`, `farBound b J C = b^{−J}((C+2J+2)/(b−1) + 2/(b−1)²)`
   with `rowL1_four`/`rowL2_four`/`farBound_four` the draft constants.  Closed forms in `bb`:
   `abs_blockSum_le` (`C·rowL1`), `sum_abs_rowCoeff_le`, `sum_sq_rowCoeff_le`,
   `sum_sq_blockSum_med_le`, `abs_blockSum_omegaVL_le` (`(log Mx/log Y)·rowL1 bb K` — the
   `b = 2` killer, now visible as a named constant), `bigAvg_le'`, `hasSum_farBound`
   (any real `b ≥ 2`), `farAvg_le`, `gridFrame_propD_of_bounds`, `exists_cylinder_subset`,
   `exists_cover_of_omit`, `gridFrame_propB_of_bound` (for `orbit bb (primeLambertAtBase bb)`),
   `gridFrame_propA`, `gridFrame_propC` (the frequency-separation seed `θ₀` is a hypothesis
   `hsep : ∀ q ≠ 0, ‖q‖∞ ≤ D → θ₀ ≤ ∑ distZ(coeffAL bb q i)²`; `gridFrame_propC_four`
   discharges it from `sum_sq_distZ_coeff_ge`).  `ScheduleWitness` is still the base-four
   §5 object; `ScheduleWitness.propD` bridges its draft-constant fields.  `isDisjunctive_four`
   unchanged, axiom-clean.
5. ✅ **DONE (lap 14)** `G4FreqSep` in base `b`: `freqDepthB b K w = K + 1 + Nat.clog b |w|`,
   `pow_clog_le_gen`, `mem_window_freqDepthB` (window `[b^{−(K+2)}, b^{−(K+1)}]`),
   `le_distZ_freqDepthB`, `freqDepthB_le`, `freqSeed b K = b^{−4}(2/b²)^K` with
   `freqSeed_four`, and `sum_sq_distZ_freqDepthB_ge : freqSeed b K ≤ ∑_α distZ(w_α b^{−j_α})²`.
   On the atom/layer set: `sum_sq_distZ_coeff_ge_gen` (`G4SmallPrimeVector`), and
   `gridFrame_propC_gen` (`G4Frame`) — PropC in base `bb` with `θ₀ = freqSeed bb K`, under
   `1 + Nat.clog bb (2^K D) ≤ N`.  **All five §4 inputs are now discharged on `gridFrame bb`
   for every `bb ≥ 2`**: A (`gridFrame_propA`), B (`gridFrame_propB_of_bound`, one real
   inequality), C (`gridFrame_propC_gen`), D (`gridFrame_propD_of_bounds`, two real
   inequalities), Jackson (`Frame.propJackson`).
6. **NEXT** `G4Schedule*` — the schedule in `(b, ℓ)`.  First the interface: a
   `ScheduleWitnessB bb ℓ w` (fields as `ScheduleWitness` but with `rowL1 bb`, `rowL2 bb`,
   `farBound bb`, `freqSeed bb`, `Nat.clog bb`, cylinders `w < bb^ℓ`) and
   `separatingFrameExists_of_witnessB : (∀ ℓ w, … → Nonempty (ScheduleWitnessB bb ℓ w)) →
   SeparatingFrameExists bb`, hence `isDisjunctive_of_witnessB`.  Then the five inequalities
   in `(bb, ℓ)`: `hB` (already general, `G4ScheduleB.gridB_bound`), `hfar`, `hbig`, `hbudget`
   with the `(2/bb)^K` masses — these need `bb ≥ 3` (`hbig`), the B-T1 restriction.

### Stretch target (NOT the objective): repair base two

`b = 2` would give `IsDisjunctive 2 primeLambert` — strictly stronger than the
Tao–Teräväinen irrationality of `∑_p 1/(2^p−1)` (arXiv 2512.01739 Thm 1.3), and it would
retire this repo's `phaseOscillation` gate honestly.  The single obstruction is that the
`p > Y` range is handled **pointwise**.  A repair must give that range signed cancellation
(as the medium range `R < p ≤ Y` already has via `sum_rowCoeff_eq_zero`), replacing the row
`L¹` mass by something like the row `L²` mass `(2/b²)^K/(b²−1)`, which at `b = 2` is
`2^{−K}/3` and *does* decay.  Only attempt this after `b ≥ 3` lands.

### Still open elsewhere in `src/` (off this campaign, unchanged)

* `MahlerDriftOne.exists_prime_nonresidue` — a prime `q ∈ (p/3, p/2)` with `(p|q) = −1`.
  The interval is *shorter than the modulus* `4p` of the reciprocity classes, so this is
  strictly beyond Linnik; genuinely out of reach, correctly disclosed.
* `PrimeLambertOscillation.phaseOscillation` — the old base-two irrationality route.
  Superseded in the literature by Tao–Teräväinen; the disjunctivity stretch target above is
  the only route in this repo that would retire it.


## G4 lap 12 — 2026-09-14 — CAMPAIGN CLOSED: headline proved

`isDisjunctive_four`, `isDisjunctive_two` (`G4ScheduleAssembly.lean`) on the trust triple.
The §5 schedule of lap 11 instantiated without change.  Nothing open on G4.  Follow-on
queue (brief §7) untouched: base `b ≥ 3`, affine entropy, ordinary-frequency transfer.

## Reflection — 2026-09-14 (DEEP REFLECTION LAP, after G4 lap 9b) 🧘

**Read this lap**: the brief §§4–5 verbatim, `G4Wiring.lean`, `G4ScheduleWitness.lean`,
`G4Frame.lean` (`smallPrimeBound`), `G4FarTail.lean` (`farC`, `farAvg_le`),
`G4MediumPrimes.lean` (`bigAvg_le'`), `G4Progression.lean` (`P₀`), `G4Schedule.lean`,
`G4Tensor.lean` (`log_det_one_add_tensorGram_le'`), `PrimeLambertFour.lean`, `DIRECTION.md`,
`CHECK-g4-route-deviations.md`, handoffs lap 7–9b, `papers/literature-review.md`, and a
fresh `lake build` + `#print axioms` sweep.  Every §5 number below was **re-derived here**,
not copied from a handoff.

### 1. Destination — UNCHANGED and now genuinely in reach

`IsDisjunctive 4 primeLambertFour` (⇒ base two by `isDisjunctive_two_of_four`), for the
constant pinned by the proved identity `primeSumAtBase 4 = primeLambertFour`
(`∑_p 1/(4ᵖ−1) = ∑_n ω(n)/4ⁿ`).  Faithfulness re-audited against the brief: the frozen
endpoint, `IsDisjunctive`, and the `orbit`/word dictionary all say what the brief says.

Ten laps in, **all five named inputs of brief §4 are machine-checked theorems about ONE
concrete frame** (`gridFrame`): `gridFrame_propA`, `gridFrame_propC`, `Frame.propJackson`
(no side conditions), `gridFrame_propD_of_bounds` (2 real inequalities),
`gridFrame_propB_of_bound` (1 real inequality).  The entire residual content of the campaign
is the `ScheduleWitness` structure — a finite bundle of explicit real inequalities in
explicit parameters.  There is **no unproved mathematics left outside §5's arithmetic**.
Nothing in the G4 wing carries a `sorry` or an axiom; every headline is `[propext,
Classical.choice, Quot.sound]`.

### 2. ROUTE VERDICT: **CONTINUE** — no registered trigger has fired

* **G-T1** — retired 2026-09-14 (C3 proved; no sieve theorem in the route).  Still true.
* **G-T2** (a measured counterexample to §4A transport or to the frequency-separation
  seed) — has not fired; both are proved theorems.
* **G-T3** (A–D discharged but §5 cannot close every budget simultaneously) — **now live,
  and it has NOT fired.**  A–D *are* discharged, so this lap's job was to test §5 directly.
  I re-derived all five inequalities from the Lean statements (§3 below): they close, with
  two corrections to the recorded parameter values.
* **G-T4** (concrete frame cannot instantiate `Frame`) — did not fire; the seam compiled in
  lap 6 with no `G4Wiring` edit.
* False-summit tells: neither is present.  Laps 6–9 each *closed a named `Prop`* (A, C, D,
  Jackson, B), so "the crux is almost cracked" has not recurred without a target closing.
  My finishability estimate has **risen**, not declined.

### 3. Two CORRECTIONS to the lap-9b paper check — both would have sent grind laps at FALSE inequalities

Lap 9b's addendum recorded a §5 parameter set and declared "everything closes on paper".
Re-deriving it from the *Lean* definitions (not the prose) finds two errors:

**(a) `lam = 1` makes `hbudget` UNSATISFIABLE.**  `smallPrimeBound`'s third error term is
`2·(2e/lam)^{Mc}·∏_{p∈sm}(1 + e^{lam}·T/p) ≤ 2·exp(Mc·log(2e/lam) + e^{lam}·T·L)`.  At
`lam = 1` the first factor is `exp(+Mc·log(2e)) = exp(+1.69·Mc)`, so the term is
`exp(+Θ(TL)) → ∞`; `Λ·δ₃ < 1` is then impossible at any `Mc`.  The term is small only for
`lam > 2e`, and needs `C > e^{lam}/log(lam/(2e))` in `Mc ≍ C·T·L`.  That function is
minimised near `lam ≈ 6.4` at `≈ 3690`.  **Use `lam = 6.4` (or `13/2`), `lam' = e`,
`C = 10⁴`** — then term (c) `= exp(−Θ(TL))`, term (b) `= exp(−(C−2e)TL)`, and terms (a),(d)
are `≈ 4^{Mc}·X^{1/10}·P₀/X = exp(−0.9 log X)`.  (`C ≥ 10⁴` agrees with
`CHECK-g4-route-deviations.md` §3.)

**(b) `N ≈ 10 K log K` is NOT enough for the far tail.**  `farC G X Dm =
log((X+Dm)/|P|) + log(log(X+Dm)+1)`, whose **second** term is `≈ log log X = L` — lap 9b
counted only the first (`≈ log P₀ = L^{0.07+o(1)}`).  The far bound is
`2^K·4^{−(K+N)}·(farC + 2(K+N) + 2)/3 / log 2`, so `hfar` needs
`4^{−N} ≲ εη/(2^K·L)`, i.e. **`N ≳ 0.63K + log₄(K·L) = Θ(log L)`**.  At
`N = 10K log K ≈ (log L)/10` the bound is `2^K·L^{0.86} → ∞`, not `o(εη)`.
The brief's own schedule already gets this right — `J = ⌈3 log₂ L⌉`, i.e.
`N = J − K ≈ 4.33 log L` — and so does `farAvg_le`'s docstring (`O(2^K L^{−6}(L+log P₀))`).
**Keep the brief's `J`; discard the lap-9b `N`.**

### 4. NEW structural finding — the §5 schedule has a TWO-SIDED window on `K`, and the lower edge is why `K` may not be frozen

No document in the repo or the brief states the lower edge; it is the mechanism behind the
brief's flat prohibition "do not freeze `K` and then send `X → ∞`".

* **Upper edge (stated, `schedule_budget`/C4).**  `Λ·δ₃ = (2D+1)^r·exp(−c·8^{−K}·L) < 1`
  forces `r·K·8^K = K^{2K+1}8^K ≪ L`, so `K ≲ log L/(2 log log L)`.
* **Lower edge (NEW).**  C's finite-sample errors force `R = X^{1/(20Mc)}` with
  `Mc ≍ C·T·L`, hence `log Mc ≥ log L`.  D's medium range then pays
  `bigAvg ≥ 0.52·8^{−K/2}√(log(Mc/5))`, which must beat `εη = 2^{−K/4}/K`:

      K · 2^{−1.25K} · √(log Mc) ≤ δbig      ⟹   2^{1.25K} ≳ K√(log L)
      ⟹  **K ≳ 0.58 log log L**.

  With `K` frozen this is `const·√(log L) → ∞` and **`hbig` fails outright** — that is
  exactly what "freezing `K` destroys the rough-error estimates" means.  It is a
  *medium-prime* obstruction, not a budget one.
* Both edges hold for the brief's `K = ⌊log L/(100 log log L)⌋` (`0.0087 log L/log log L`
  vs `1.5 log log L` at the lower edge — fine, but only once `log L > 173 (log log L)²`).
  Verified this lap that `K = ⌊log log L⌋` also sits inside the window with
  polynomial-in-`log L` margin on both sides; **not** adopting it, because
  `schedule_budget` is already proved for `scheduleK` and a replacement must re-prove
  every budget.  Recorded so that no future lap "simplifies" `K` downward and silently
  breaks `hbig`.

### 5. Independent re-derivation of the whole witness (record; supersedes lap 9b's)

Schedule: `L = log log X`, `K = scheduleK L`, `s = K²`, `r = K^{2K}`, `H = (K²+1)^K`,
`J = K + N = ⌈3 log₂ L⌉`, `η = 2^{−K/4}`, `ε = 1/K`, `M_cyl = ⌈K/(8ℓ)⌉`,
`D = ⌈(16K·2^{K/4})²⌉`, `T = #Idx = H·N`, `Mc = ⌈10⁴·T·L⌉`, `lam' = e`, `lam = 13/2`,
`R = X^{1/(20Mc)}`, `Y = X^{1/100}`, `B = s·J + 1`, `U ≥ max gridU`, `Q = U!`
(divisibility by every `m ≤ U` is `Nat.dvd_factorial` — no `lcm` needed), `D₀ ≥ max gridV`.
Budget split `δ₁ = δbig = δfar = 1/8`, `2κ ≤ 1/8`, `Λδ₃ ≤ 1/8`, total `5/8 < 1`.

* `log P₀ = log Mprod + log freezeQ ≤ 2H·log d + (2T + T²·log(J·Q·D₀))`; the `T² log(QD₀)`
  term dominates, giving `L^{0.07+o(1)}` — matches the brief's "`log P ≤ L^{0.07+o(1)}`".
  `Q = U!` (`log Q ≈ U log U`, `U ≈ K²B^K = L^{0.03+o(1)}`) is comfortably inside.
* **B**: with `H ≤ e^{1/K} r`, `g ≥ (1−1/K) r`, `(H+g)/g ≤ 2.72` (`K ≥ 4`), and
  `M_cyl·log(4^ℓ−1) ≤ (K/4)log2 + 2ℓ log2 − K·4^{−ℓ}/(8ℓ)`, the exponent per unit `r` is
  `≤ 0.396 + 1.78ℓ − K4^{−ℓ}/(8ℓ) + 0.347 + 11.5√K + 1.919 + log 2`, so **`hB` holds as
  soon as `K/(8ℓ4^ℓ) ≥ 11.5√K + 1.78ℓ + 4.36`, for which `K ≥ 33856·ℓ²·16^ℓ` suffices**.
  Everything here is elementary and `X`-free.
* **C**: `∑_{p∈sm} 1/p ≥ log log R − ∑_{p|P₀} 1/p − O(1) = L − O(log L)`, so
  `δ₃ ≈ exp(−4·4^{−4}8^{−K}L)`; `Λ = (2D+1)^r = exp(O(rK))`; `schedule_budget` closes it.
  Error terms as in §3(a).
* **D-big**: `0.52·8^{−K/2}√(log(Mc/5)) + 100·2^{−K}/3 ≤ δbig εη` — the lower edge of §4.
* **D-far**: `2^K 4^{−J}(farC + 2J + 2)/3/log2 ≤ δfar εη` with `farC ≈ L` — needs the
  brief's `J`, §3(b).
* **Jackson**: `2κ = 2K2^{K/4}/√(D+1) ≤ 1/8` at `D = ⌈(16K2^{K/4})²⌉`.

### 6. What to KEEP doing

* Hardest-first on §5, in the order that gates the most: the `X`-free inequality **`hB`**
  first (self-contained, the brief's "central formalization target"), then the `GridParams`
  constructor with an explicit `log P₀` bound, then `hfar`, `hbig`, `hbudget`.
* Re-deriving every §5 number from the **Lean statement**, never from a handoff docstring.
  Both errors in §3 came from prose that was never checked against the definition.
* One frame, all five props (`separatingFrameExists_of_witness` is the audit surface).

### 7. What to STOP doing

* **Stop trusting recorded "paper checks" as settled.**  Lap 9b's addendum is now known to
  contain two false claims; treat every remaining §5 claim as unverified until a lap
  re-derives it from the Lean definition or the compiler accepts it.
* Stop adding new §4 machinery.  §4 is closed; anything new there is drift.
* Stop citing `N ≈ 10K log K` or `lam = 1` anywhere.

### 8. Single highest-value next target

**`hB` as a standalone real-analysis theorem** (new module `G4ScheduleB.lean`):

    theorem gridB_bound (ℓ K M g r H : ℕ) (hℓ : 1 ≤ ℓ)
        (hK : 33856 * ℓ^2 * 16^ℓ ≤ K) (hr : r = K^(2*K)) (hH : H = (K^2+1)^K)
        (hM : K ≤ 8 * ℓ * M) (hMle : 8*ℓ*M ≤ K + 8*ℓ)
        (hg : (1 - 1/(K:ℝ)) * r ≤ g) (hgle : g ≤ r) :
      ((4^ℓ - 1 : ℕ) : ℝ)^(M*H) * (2:ℝ)^(-(K:ℝ)*g/4) * Real.exp (r*(Real.log 2 + 23*Real.sqrt K)/2)
        * (Real.sqrt (2*Real.pi*Real.exp 1/g) * Real.sqrt (H+g))^g ≤ (1/8) / 2^r

Why this one: it is the only one of the five that involves **no** `X`, no primes and no
progression, so it can be proved today without the `GridParams` constructor; it is the
piece the brief singles out as "a central formalization target, not routine bookkeeping";
and it is the only §5 inequality whose failure would be a *geometry* failure rather than a
bookkeeping failure.  Decompose it as: (i) the scalar exponent inequality after `Real.log`,
(ii) `H/r ≤ e^{1/K}` and `(H+g)/g ≤ 2.72`, (iii)
`M log(4^ℓ−1) ≤ (K/4)log2 + 2ℓ log2 − K4^{−ℓ}/(8ℓ)` from `log(1−x) ≤ −x`, (iv) the final
`√K` comparison.


## ✅ GRIND 2026-09-14 (G4 lap 9b): `ScheduleWitness` — the exact residual obligation (`69e3ebf`)

`G4ScheduleWitness.lean`: `separatingFrameExists_of_witness` and `isDisjunctive_four_of_witness`
(trust triple).  **Everything in brief §4 is machine-checked on the concrete frame.**  The whole
remaining content is: for every omitted cylinder `[w/4^ℓ,(w+1)/4^ℓ)`, produce a
`ScheduleWitness ℓ w` — grid parameters + scales + the five real inequalities `hB`, `hbig`,
`hfar`, `hbudget` (with `δ₃ = smallPrimeBound …`) and the side conditions.

### Paper feasibility of the full witness (this lap — record it; one NEW constraint found)

Schedule: `L = log log X`, `K = ⌊log L/(100 log log L)⌋`, `s = K²`, `r = K^{2K}`, `H = (K²+1)^K`,
`η = 2^{−K/4}`, `ε = 1/K`, `M_cyl = ⌈K/(8ℓ)⌉`, `D = ⌈(8K·2^{K/4})²⌉`, `Mc ≈ C·T·L` with
`T = #Idx = H·N`, `lam' = e`, `lam = 1`, `R = X^{1/(20 Mc)}`, `Y = X^{1/100}`,
`B ≈ s(K+N)+1`, `U ≈ s·B^K`, `Q = lcm(1..U) ≈ e^U`, so `log P₀ ≈ H·2 log(QU) ≈ K^{5K} N^K`.
* **B**: exponent `(K/4)(dH − g) + O(r√K) < 0` once `√K(1−d−1/K−1/K) ≳ 70`. ✓
* **C** (`Λδ₃`): `exp(−c8^{−K}(L − log(20Mc) − ∑_{p∣P₀}1/p))·(2D+1)^r → 0` by `schedule_budget`;
  `∑_{p∣P₀}1/p ≲ log log log P₀ = O(log K)`; the moment terms are `exp(2eTL − Mc)`,
  `(2e)^{Mc} exp(eTL)`, `R^{2Mc}/|P| = X^{1/10}P₀/X` — all fine with `Mc ≈ 3eTL` and
  `log P₀ ≪ log X`. ✓
* **D-big**: `8^{−K/2}√(log(Mc/5)) = 8^{−K/2}√(log L + O(K log K))` vs `εη = 2^{−K/4}/K`: needs
  `2^{5K/4} ≫ K√log L`, true since `K log 2 ≫ log log L`. ✓  (`Y²4^{−K}P₀/X`, `100·2^{−K}` fine.)
* **D-far — NEW CONSTRAINT**: `farC ≈ log P₀ + L ≈ K^{5K} N^K`, and the far bound is
  `2^K 4^{−(K+N)} farC`.  The brief's only condition on `N` is `1 + ⌈log₄(2^K D)⌉ ≤ N` (from C),
  which gives `4^{−N} ≈ 2^{−3K/2}` — **NOT enough**: `2^{−2.5K}·K^{5K} ≫ εη`.  Fix: take
  `N = ⌈10 K log K⌉`; then `4^{−N} = K^{−13.9K}` beats `K^{5K}N^K = K^{6K+o(K)}`.  `N` enters
  nowhere else harmfully (`T = HN` only shifts `Mc`; `B, U, P₀` grow polynomially in `N`).
  So the retained depth is forced by the **far tail's dependence on `log P₀`**, not by C.
* **Jackson**: `2κ = 2K 2^{K/4}/√(D+1) ≤ 1/4` at the `D` above. ✓

Conclusion: the witness exists on paper with `N ≈ 10K log K`; the Lean proof is a multi-lap
asymptotic-inequality job.  Attack order: (1) a `GridParams` constructor from `(K, N)` with
`B, U, Q, D₀` explicit and size bounds `log P₀ ≤ K^{5K}N^K·C`; (2) `hfar` (needs (1) + the
`N` choice); (3) `hbig`; (4) `hbudget` from `schedule_budget` + the `smallPrimeBound` terms;
(5) `hB` (pure real inequality in `K, ℓ, d`).

## ✅ GRIND 2026-09-14 (G4 lap 9): `PropB` DISCHARGED on the grid modulo one real inequality

`G4TubeVolume.lean` + `G4GridTube.lean` (trust triple).  **`gridFrame_propB_of_bound`**:
for the concrete frame, if the orbit omits `[w/4^ℓ,(w+1)/4^ℓ)`, `4^{−ℓM} ≤ η`, `ε < 1`, `r ≥ 1`,
`Lg ≥ log det(1 + T_s^{⊗K})`, `0 ≤ δ₁`, and

    ∀ g, (1−ε) r ≤ g ≤ r →  ((4^ℓ−1)^M)^H · η^g · e^{Lg/2} · (√(2πe/g)·√(H+g))^g ≤ δ₁ / 2^r,

then `PropB δ₁`.  Inputs: `Frame.volume_tube_le` (Markov in `dAv` + marginal projection +
torus projection + `addHaar_smul`), `Frame.volume_pieceCube_le_of_reindex` (ellipsoid +
det monotonicity through the `rowEquiv`/`atomEquiv` reindexing), `exists_cylinder_subset`,
`exists_cover_of_omit`, `card_goodSets_le`.

**All of §4 is now discharged modulo §5 arithmetic**: A ✅, C ✅, Jackson ✅ (no side
conditions), D = two inequalities, B = one inequality.  Next: the §5 schedule module (see
`HANDOFF-2026-09-14-g4-lap9.md`).

## ✅ GRIND 2026-09-14 (G4 lap 8): `PropJackson` DISCHARGED for every frame

`src/NormalNumbers/G4Jackson.lean` (trust triple on `Frame.propJackson`).  Zero laps → closed in
one, because the average metric makes the smoothing error dimension-free exactly as the brief
says: `|f(y+w) − f(y)| ≤ dAv(y+w,y)/ρ = r⁻¹∑_ν ‖w_ν‖/ρ`, and the product kernel integrates each
coordinate separately.

* **`Frame.propJackson : fr.PropJackson (1/(res·√(D+1))) ((2D+1)^r)`.**
* Fejér kernel `F_D = ‖∑_{k≤D} e(kt)‖²/(D+1)`; the only analytic inputs are `F_D ≤ D+1` and
  `‖t‖·‖∑_{k≤D} e(kt)‖ ≤ 1/2` (geometric sum + Jordan, reusing
  `eight_mul_distZ_sq_le_one_sub_cos`).  The first moment comes from the *pointwise* split
  `‖t‖F_D ≤ aF_D + 1/(4(D+1)a)` at `a = 1/(2√(D+1))` — no interval integral, no closed form for
  `1 − |m|/(D+1)` (coefficients are fibre counts; only `0 ≤ c_m ≤ 1`, `c_0 = 1`, `c_{−m} = c_m`
  are used).
* The trig polynomial is `∫ f(y+w)P(w)dw` written out via translation invariance of Haar on
  `Torus r` (`integral_add_left_eq_self`) and `χ_q(z−y) = χ_q(z)χ_{−q}(y)`.
* Rate is `κ = O(1/(εη√D))`, weaker than the draft's `O(1/(εηD))`; harmless — `D` polynomial
  in `1/(εη)` keeps `Λ = (2D+1)^r = exp(O(rK))`, which is what `schedule_budget` (C4) absorbs.

**Dependency map now**: `PropA` ✅ · `PropC` ✅ · `PropD` ✅ (two §5 inequalities) ·
**`PropJackson` ✅** · `PropB` open (inputs proved, assembly is the remaining §4 work) ·
§5 schedule open.  `isDisjunctive_four_of_frames` still CONDITIONAL on `SeparatingFrameExists`.

### Lap 8b — B assembly landed at the abstract level (`G4TubeVolume.lean`, `d39c41d`)

`Frame.volume_tube_le`: whenever `orbitClosure ⊆ ⋃_{c ∈ Bs} π[c, c+h]` with `h ≤ η`,

    vol(tube(image, εη)) ≤ ∑_{G ∈ goodSets} (#Bs)^H · η^{|G|} · vol([A_G, I_G]·[−1,1]^{H+G}),

`goodSets = {G ⊆ Fin r : (1−ε) r ≤ |G|}`.  Steps (ii)–(iv) of the plan are done abstractly:
`tube_subset_pieces` (Markov in `dAv`, nearest image point by compactness, real lifts),
`volume_piece_le` (marginal projection is measure preserving, `volume_image_torusProj_le`,
translation invariance, `addHaar_smul`).  Trust triple.

**Left for `gridFrame_propB`** (bookkeeping, no new mathematics):
1. `vol(pieceCube G) ≤ exp(½ r(log 2 + 23√K)) (√(2πe(H+|G|)/|G|))^{|G|}` for the grid's `AR`:
   `volume_augmented_image_le (ARsub G)` + `det_one_add_submatrix_mul_transpose_le` with
   `e = Subtype.val` + `AR * ARᵀ = reindex (tensorGram)` (`Amat` is `kronPow` reindexed by
   `rowEquiv`/`atomEquiv`; `Matrix.det_reindex_self`) + `log_det_one_add_tensorGram_le'`.
   Needs `0 < |G|`, i.e. `ε < 1` and `r ≥ 1`.
2. The dyadic cylinder: from `0 ≤ a < c ≤ 1` produce `ℓ, w` with `[w/4^ℓ, (w+1)/4^ℓ) ⊆ [a, c)`,
   then `orbitClosure_subset_cylinders` at `M` with `4^{−ℓM} ≤ η`; `Bs = image cylLeft (admissible)`,
   `#Bs ≤ (4^ℓ − 1)^M`.
3. `#goodSets ≤ 2^r`, and the §5 arithmetic (exponent check above).

### B exponent check (paper, this lap — record it)

With `vol(tube) ≤ 2^r (B−1)^{MH} η^g e^{½r(log 2+23√K)} (√(2πe(H+g)/g))^g`, `η = 2^{−K/4}`,
`4^{ℓM} ≈ η^{−1}`, `g ≥ (1−ε)r`, `r/H ≥ 1 − 1/K`: the base-2 exponent is
`(K/4)(dH − g) + O(r√K)`, negative iff `√K (1 − d − ε − 1/K) ≳ 70`, `d = log_B(B−1)`.  Closes
in the single limit `K → ∞` for each fixed omitted word (`ℓ` fixed, `d < 1` fixed).  The
`O(r√K)` spectral term is what forces `K ≫ (1−d)^{−2}`; nothing else competes.

### Next attack (ordered)

1. **B assembly** → `gridFrame_propB`: (i) pick a cylinder `[w/4^ℓ,(w+1)/4^ℓ) ⊆ [a,c)`;
   (ii) `orbitClosure_subset_cylinders` at `M` with `4^{−ℓM} ≤ η`; (iii) Markov in `dAv`:
   `y ∈ tube ⟹ ∃ G, |G| ≥ (1−ε)r, y_G ∈ π(c_G + η[A_G,I_g]cube)`; (iv) union over `G` (`≤ 2^r`)
   and over cylinder choices (`(B−1)^{MH}`), `volume_tubePiece_le`, `volume_image_torusProj_le`,
   `addHaar_smul` for `η^g`.  Note `image` uses `mulVecT` over `ℤ`-matrices on the torus,
   `tensorDiff` is over `ℝ`; the seam is `Matrix.map` + the lift `ℝ^H → 𝕋^H`.
2. **§5 schedule module**: instantiate `bigAvg_le'`, `farAvg_le`, the B bound, and
   `propJackson` at `η = 2^{−K/4}`, `ε = 1/K`, `D = ⌈(4K 2^{K/4})²⌉`, and close
   `δ₁ + δ₂ + 2κ + Λδ₃ < 1` via `schedule_budget`.

## ✅ GRIND 2026-09-14 (G4 lap 7b): `farAvg` DISCHARGED to closed form — §4D is two real inequalities

`src/NormalNumbers/G4FarTail.lean` (trust triple on every headline).  Entirely elementary; no
Mertens, no Hardy–Ramanujan, and **no remote cutoff** — the earlier handoff worry was wrong: the
AP-mean bound grows only logarithmically in the shift, so `4^{−j}` kills it.

* `two_pow_omega_le_card_divisors` (`2^ω ≤ d`), `sum_card_divisors_le`
  (`∑_{m<N} d(m) ≤ N(log N+1)`), `sum_log_le_card_mul_log_avg` (Jensen for `log` by hand).
* **`sum_omegaR_add_le`** — on any `P ⊆ range X`, `∑_{n∈P} ω(n+ρ) ≤ |P| log((X+ρ)(log(X+ρ)+1)/|P|)/log 2`.
* **`sum_omegaR_shiftG_le`** — at layer `j`: `≤ |P|(C₀ + 2j)/log 2`, `C₀ = farC G X Dm =
  log((X+Dm)/|P|) + log(log(X+Dm)+1)`, `Dm ≥ every d_α`.
* `hasSum_farBound`, **`sum_abs_farPart_le`**, **`farAvg_le`**:
  `farAvg ≤ 2^K 4^{−J} ((C₀ + 2J + 2)/3 + 2/9)/log 2`, `J = K+N`.
* **`gridFrame_propD_of_bounds`** — `PropD (δbig + δfar)` from the two closed forms
  (`bigAvg_le'` and `farAvg_le`) each `≤ δ·εη`.  **§4D is now two real inequalities in the
  schedule parameters** (`R, Y, Mx, Dm, |P|, K, N, ε, η`).

### Next attack (ordered)

1. **`PropJackson`** (product Jackson kernel, one-coordinate first moment `O(1/D)`; average
   metric ⇒ `κ = O(1/(εηD))`).  Zero laps so far.
2. **B assembly** (Markov + torus marginals + finite unions; steps in lap-2 handoff).
3. **§5 schedule module**: instantiate `bigAvg_le'`/`farAvg_le` with `R = X^{1/(20M)}`,
   `Y = X^{1/100}`, `Mx = X + J·Dm`, `|P| ≥ X/P₀ − 1`, and the size bounds on `P₀`, `Dm`
   (draft (3.2)), and check both `< δ·εη` with `η = 2^{−K/4}`.

## ✅ GRIND 2026-09-14 (G4 lap 7): `bigAvg` DISCHARGED to closed form — the `Y`-split, tripwire honoured

`src/NormalNumbers/G4MediumPrimes.lean` (trust triple on every headline).  `CHECK §4`'s tripwire
is honoured: the medium range `R < p ≤ Y` is an **L²** two-congruence estimate preserving the
signed cancellation; only `p > Y` is pointwise.

* **`sum_sq_block_le`** (abstract): sample equidistributed (deviation 2) mod the good moduli,
  pairwise-coprime primes `S`, shifts separated mod each `p ∈ S`, `∑ c_i = 0` ⇒
  `∑_n (∑_{p∈S}∑_i c_i 1[p∣n+ρ_i])² ≤ |P|(∑_{p∈S}1/p)(∑c_i²) + 2|S|²(∑|c_i|)²`.
  Off-diagonal `p ≠ p'` main terms carry `(∑c)² = 0`; diagonal cross terms `i ≠ i'` vanish
  exactly by separation, which on the grid is `goodPrime_of_not_dvd_P₀` (no size hypothesis on
  the shifts needed).
* **`sum_sq_blockSum_med_le`**, **`sampleAvg_abs_blockSum_med_le`**: on the concrete grid the
  first moment of the medium block is `≤ √medBudget`, `medBudget = (∑_{med}1/p)8^{−K}/15 +
  2|med|²(2^{−K}/3)²/|P|`.
* **`abs_blockSum_omegaVL_le`**: `p > Y` block `≤ (log Mx/log Y)·2^{−K}/3` pointwise
  (`ω_{>Y}(m) ≤ log m/log Y`, `card_filter_gt_mul_log_le`).
* **`sum_inv_primes_Ioc_le`**: dyadic Chebyshev from `primorial_le_four_pow`:
  `∑_{R<p≤Y} 1/p ≤ 4(1 + log⌊log₂Y⌋ − log⌊log₂R⌋)` for `2 ≤ R ≤ Y`.  Constant irrelevant, so no
  lower Mertens and no Mertens' first theorem enter.
* **`bigAvg_le'`** — closed form:
  `bigAvg ≤ √(4(1+log⌊log₂Y⌋−log⌊log₂R⌋)·8^{−K}/15 + 2Y²(2^{−K}/3)²/|P|) + (log Mx/log Y)2^{−K}/3`.
  Under §5 (`R = X^{1/(20M)}`, `Y = X^{1/100}`, `Mx ≤ 3X`) this is `O(8^{−K/2}√log M) + O(2^{−K})`.

**Schedule check done on paper this lap (record it):** `η = 2^{−K/4}` and `2^K = L^{o(1)}` but
`2^K ≫ (log L)^C` because `K log 2 = Θ(log L / log log L) ≫ log log L`; so `8^{−K/2}√log M = o(η)`
requires exactly that `log log Y − log log R = log(M/5)` is a *log of a polylog*, which the
`R = X^{1/(20M)}` cutoff delivers.  Had the medium diagonal been `∑_{p≤Y} 1/p ≈ L` instead, the
term would be `8^{−K/2}√L ≫ η` and the route would FAIL — the small-prime cutoff `R` is
load-bearing for D, not only for C.

### Next attack (ordered)

1. **`farAvg`** via the AP-mean of `ω`: `2^{ω(m)} ≤ d(m)`, hand-rolled Jensen
   (`log x ≤ log c + x/c − 1` at `c = E[d]`), `∑_{m<N} d(m) ≤ N(log N + 1)`; gives
   `E[ω(n+ρ)] = O(L + log P₀)` and `E|farPart| = O(2^K 4^{−J} L)`.  Then `gridFrame_propD` is
   fully discharged given the §5 sizes.
2. `PropJackson`; then the B assembly; then the §5 schedule module (instantiate `bigAvg_le'`
   with `R, Y, Mx` and check `< δ·εη`).

## ✅ ALTITUDE + GRIND 2026-09-14 (G4 lap 6): `PropA` and `PropC` DISCHARGED; §4D reduced to two named averages

**Review finding.**  Five laps of *inputs*, zero named `Prop` closed, and the abstract-`Frame` ↔
concrete-object seam never compiled.  `DIRECTION.md` rewritten accordingly (G-T1 retired as
satisfied — C3 is proved via `crt_input` + `norm_sampleAvg_prod_ee_le`; G-T4 registered).

**The seam holds.**  `G4Frame.lean`: `gridFrame` + `gridFrame_propA` + `gridFrame_propC`.  `θ` is
the transport translate by `rfl`; `card_roots_shiftPhase_le` (roots of `shiftPhase ρ x p` do not
depend on `x` at all) is what makes §4C uniform over the whole Fourier box, giving the
frequency-free `smallPrimeBound`.

**§4D.**  `G4Remainder.lean` + `G4RowMass.lean`.  The first `K` layers cancel for ANY weight
(`sum_kronPow_mul_shiftG_eq_zero`); `Ffull n = (Sval n + bigBlock n + farPart n) mod 1` exactly
(`gridFrame_Ffull_decomp`), with `γ = frozenGamma G` absorbing the primes dividing `P₀`; hence
`gridFrame_propD` reduces `PropD` to `bigAvg` and `farAvg`.  Row masses proved exactly:
`∑_α A_{aα} = 0` (the signed cancellation), `∑_α |A_{aα}| = ∑_α A_{aα}² = 2^K`, with the layer
budgets `4^{−K}/3` and `16^{−K}/15`.

### Next attack (ordered)

1. **`bigAvg`, split at `Y = X^{1/100}` — the tripwire.**  `p > Y` pointwise via
   `abs_blockSum_le` with `C = 100`; `R < p ≤ Y` by the L² two-congruence count, whose main
   terms cancel by `sum_kronPow_diffZ_eq_zero`.  A single pointwise bound over all `p > R`
   typechecks and is WRONG (brief §4D).
2. **`farAvg`** via the AP-mean of `ω`.  Elementary route found this lap, no Mertens needed:
   `2^{ω(m)} ≤ d(m)`, Jensen-for-log by hand (`log x ≤ log c + x/c − 1` at `c = E[d]`), and
   `∑_{m<N} d(m) ≤ N(log N + 1)`.  Gives `E[ω(n+ρ)] = O(L + log P₀)` and
   `E|farPart| = O(2^K L^{−5}) = o(η)`.
3. `PropJackson`; then the B assembly; then §5.


## ✅ GRIND 2026-09-14 (G4 lap 5): the §2 grid PROVED (A's arithmetic seed); §4C instantiated on the concrete small-prime vector

**Advance on the crux.**  §4C was closed abstractly in lap 4 for arbitrary phase sums of shifted
`ω`; what stood between it and `PropC` was the concrete object.  This lap builds it.

`src/NormalNumbers/G4Grid.lean` (sorry-free, trust triple) — draft §2 verbatim:
* `gridU`, `gridV`, `proj B j α = j·u − v = ∑ᵢ (j − (i+1)) αᵢ B^{i+1}`.
* `balanced_digits_eq_zero` — base-`B` digits with `|digit| < B` are unique.  Only `|digit| < B`
  is needed, not the draft's `B > 2sJ+1` (bottom digit is divisible by `B`, peel).
* **`sum_kronPow_diffZ_mul_eq_zero`** — for `j = i₀+1 ≤ K`, every row of `A = D_s^{⊗K}` kills
  any function of `proj B j`: **the first `K` layers cancel exactly**, for any `ω`.  (General
  form `sum_kronPow_mul_eq_zero`: Kronecker power of a row-sum-zero matrix annihilates any
  function ignoring one coordinate; proof via `Fin.insertNthEquiv`.)
* `proj_injective` (`K < j`, `s·j < B`), `gridU_injective` (`s < B`).
* `mult d = 1 + Q(D₀ + u)`, `offset t = Q v`, `shiftG ρ = j d − t` (draft (2.3));
  `coprime_mult` (needs only: `Q` divisible by every `m ≤ U ≥ max u`, `1 < Q`, `s < B`);
  **`shiftG_injective`** — the surviving shifts `K < j, j' ≤ J < Q` are globally distinct;
  `add_shiftG_eq` — `n = t + d k ⇒ n + ρ_j = d (k + j)`, the transport input.

`src/NormalNumbers/G4SmallPrimeVector.lean` (sorry-free, trust triple):
* `AtomLayer K s N = atoms × Fin N`, `layer K jj = K+1+jj`, `shiftAL`, `coeffAL q (α,jj) = w_α/4^j`
  with `w = q ᵥ* A`; `Sval sm ρ n a = ∑_α A_{aα} ∑_jj ω_{sm}(n + ρ(α,jj))/4^{layer jj}`.
* **`torusChar_Sval`** — `∏_a e(q_a S_a(n)) = e(totalPhase sm ρ (coeffAL q) n)`: the concrete
  character IS a phase sum of shifted `ω_{sm}`.
* **`sum_sq_distZ_coeff_ge`** — `∑_i dist(x_i,ℤ)² ≥ 4^{−4}8^{−K}` for `0 ≠ q`, `‖q‖∞ ≤ D`, once
  `N ≥ 1 + ⌈log₄(2^K D)⌉` (every frequency-depth layer retained; `freqDepth_le`).
* `goodPrime_of_not_dvd` — injective shifts + `p ∤ (ρ_i − ρ_{i'})` ⇒ `GoodPrime ρ p`;
  `shiftAL_injective`.
* **`norm_sampleAvg_torusChar_Sval_le`** — §4C for the concrete vector, uniformly on the box:
  `‖avg ∏_a e(q_a S_a n)‖ ≤ exp(−4·4^{−4}8^{−K} ∑_{p∈sm} 1/p) + (the four lap-4 errors)`.

**What now separates this from `Frame.PropC`** (all bookkeeping, no new mathematics):
(a) the reindexing `(Fin K → Fin s) ≃ Fin r` to the wiring's `Torus r`; (b) `hgood` from
`goodPrime_of_not_dvd` once the progression modulus `P₀` is built to contain every prime
dividing a nonzero shift difference (§3); (c) the harmonic sum `∑_{p∈sm} 1/p ≥ L − O(log L)`
— needs an elementary lower Mertens bound `∑_{p≤R} 1/p ≥ log log R − 1` (NOT in mathlib;
route: `∏_{p≤R}(1−1/p)^{−1} ≥ ∑_{n≤R} 1/n ≥ log R` and `−log(1−1/p) ≤ 1/p + 1/p²`), and the
excluded primes `p ∣ P₀` cost `≤ ∑_{k≤ω(P₀)} 1/(k+1) ≤ log ω(P₀) + 1 = O(log L)` (trivial);
(d) C4 numerics: `M = 10⁴·|ι|·L`, `λ = λ' = 8` against `Λ = (2D+1)^r`, via `schedule_budget`.

### ⬆️ UPDATE (same lap, third commit): both harmonic-mass inputs PROVED — `G4Mertens.lean`

* **`log_log_le_sum_inv_primesBelow`** — lower Mertens, `log log N ≤ ∑_{p<N} 1/p + 1` (`N ≥ 2`),
  via mathlib's finite Euler product over `N`-smooth numbers, `log N ≤ H(N−1)`,
  `−log(1−1/p) ≤ 1/(p−1)`, and the telescoping `∑ 1/(n(n−1)) ≤ 1`.  (c) above is now supplied.
* **`sum_inv_le_log_card_add_one`** — any finset of integers `≥ 2` has harmonic mass
  `≤ log|T| + 1` (`Finset.induction_on_max`: the max of `k` distinct integers `≥ 2` is `≥ k+1`).
  The excluded primes `p ∣ P₀` therefore cost `≤ log ω(P₀) + 1 = O(log L)`.

### ⬆️ UPDATE (same lap, fourth commit): the exact transport identity and `PropA` — `G4Transport.lean`

* `tailB b k = ∑_{j≥1} ω(k+j)b^{−j}`, **`tailB_eq`**: `tailB b k = b^k G_b − tailIntB b k` (integer);
  `corrB b d k` (the periodic correction `E`), `corrB_congr` (depends on `k` mod `rad d`);
  **`dilatedTailB_eq`**: `∑_{j≥1} b^{−j} ω(d(k+j)) = T_b(k) + ω(d)/(b−1) − E_{d,b}(k)` — fixed-base
  §1 verbatim, any `b ≥ 2`.  Trigger G-T2's transport identity is PROVED, not refuted.
* `coe_tailB_four`: `T₄(k) ≡ orbit 4 G₄ k (mod 1)`; `Frame.transportTheta c` = the translate
  `θ_ν = ∑_α A_{να}(ω(d_α)/3 − E_α(c_α))`.
* **`Frame.propA_of_progression`** — for ANY wiring frame whose sample points are
  `t_α + d_α k_α` with `k_α ≡ c_α` mod every prime of `d_α`, and `θ = transportTheta c`,
  `PropA` holds.  So A is reduced to the §3 progression construction (draft §3), which is the
  same object C needs (the modulus `P₀` freezing multiplier residues and shift-difference primes).

### ⬆️ UPDATE (same lap, fifth commit): the §3 progression — `G4Progression.lean`

`GridParams` bundles `K, s, B, Q, D₀, N, U` with the five `G4Grid` side conditions.  From it:
`Mprod = ∏ d_α²`, the CRT residue `b₀ < Mprod` (`Nat.chineseRemainderOfFinset`, coprimality
from `coprime_mult`), `freezeQ = ∏_{p≤2T} p · ∏_{i≠i'} |ρ_i − ρ_{i'}|`, and `P₀ = Mprod·freezeQ`.
* **`exists_mult_mul`** — on `apSample X P₀ b₀` every `n = t_α + d_α k` with `d_α ∣ k`: this IS
  the hypothesis of `Frame.propA_of_progression` (with `c = 0`).  Uses `t_α < d_α` (from
  `d ≡ 1`, `t ≡ 0 (mod Q)`), so `n % d_α² = t_α` without any sign worry.
* **`two_mul_card_le_of_not_dvd`**, **`goodPrime_of_not_dvd_P₀`** — a prime `p ∤ P₀` exceeds
  `2T` and is good: these are the hypotheses `hk`, `hgood` of `norm_sampleAvg_torusChar_Sval_le`
  for `sm = {p ≤ R prime : p ∤ P₀}`, and `hsP` is `Nat.Coprime` from `p ∤ P₀`.

**So A and C are both input-complete on ONE concrete object.**  Remaining for A: build the
wiring `Frame` from `GridParams` (reindex `Atom ≃ Fin H`, `Fin K → Fin s ≃ Fin r`) — pure
plumbing.  Remaining for C: the same reindexing plus the C4 numerics.  Draft (3.2)'s size bound
`log P₀ = o(L)` is the §5 module's.

**Also needed for D and noted here (not yet Lean)**: the far tail `j > J` needs the sample mean
`𝔼 ω(n+ρ) ≪ L` — an UPPER Mertens bound `∑_{p≤z} 1/p ≤ log log z + O(1)`, also not in mathlib;
route: `primorial_le_four_pow` ⇒ `#{p ∈ (y,2y]} ≤ 2y log 4 / log y`, dyadic blocks.  The crude
`∑_{p≤z} 1/p ≤ log z` is NOT enough (`2^K 4^{−J} log X ≫ η`).

Next attack: the transport identity (fixed-base §1 / draft (4.1)) from `omegaR_mul_eq` +
`add_shiftG_eq`: `∑_{j≥1} 4^{−j} ω(n+ρ_{α,j}) = T₄(k_α) + ω(d_α)/3 − E_α`, `T₄(k) − 4^k G₄ ∈ ℤ`,
giving `PropA` for the grid frame.  Then the §3 progression `P₀`.

## ✅ GRIND 2026-09-14 (G4 lap 4): C3core (the sample exponential moment / Shiu) is NOT NEEDED — C3 reduced to CRT counting alone

`src/NormalNumbers/G4TransferMoment.lean` (new, sorry-free, all headlines `[propext, Classical.choice, Quot.sound]`).

**The structural insight.**  Lap 3's skeleton expanded `∏_p g_p` around the independent means
`μ_p`; every subset term is then a genuine fluctuation and the `|T| > M` tail can only be paid by
an exponential moment `avg_n ∏_p(1+lam‖g_p−μ_p‖)` **over the sample** — a Shiu-type sieve theorem
(the named input `B`, "C3core").  Expand around `1` instead:
`∏_{p∈s} g_p(n) = ∑_{T⊆s} ∏_{p∈T}(g_p(n)−1)`, and the term of `T` vanishes unless every `p ∈ T`
is *active* at `n` (`g_p(n) ≠ 1`, i.e. `n` in one of the `k` active classes mod `p`).  So the tail
is supported on `{V(n) > M}`, `V(n)` = number of active primes, and there the truncated sum is
`∑_{m≤M} C(V,m)2^m ≤ (2eV/M)^M` — **a degree-`M` polynomial in `V(n)`**.  `V^M` is a sum over
`M`-tuples of primes of indicator products on moduli `≤ R^M`, hence CRT-transferable to the
independent model, where the exponential moment `𝔼 e^{λV} = ∏_p(1+(e^λ−1)π_p)` is an exact product.
No sieve theorem enters anywhere.

* `norm_truncation_le` — pointwise: `‖∏_s g − ∑_{|T|≤M}∏_T(g−1)‖ ≤ 2(2e|A|/M)^M` (`A` the active
  set, `M ≥ 1`).  The `(1+2θ)^V ≤ e^M` trick with `θ = M/(2V)` avoids all factorials.
* `sampleAvg_card_pow_le` — moment transfer: `avg_n V(n)^M ≤ ∑_{D⊆s}|D|^M∏_Dπ_p + |s|^M ε'`,
  given the CRT input `avg_n 1[D ⊆ Act n] ≤ ∏_D π_p + ε'` for nonempty `D`, `|D| ≤ M`.
* `sum_card_pow_mul_prod_le` — `∑_{D⊆s}|D|^M∏_Dπ_p ≤ (M/λ)^M ∏_p(1+e^λπ_p)` (via
  `k^M ≤ (M/λ)^M e^{λk}`, from `(λk)^M/M! ≤ e^{λk}` and `M! ≤ M^M`).
* **`norm_sampleAvg_prod_sub_prod_le'`** — the assembled skeleton:

      ‖avg ∏_s g − ∏_s μ‖ ≤ N_M ε + λ'^{−M}∏_p(1+λ'c_p) + 2(2e/λ)^M ∏_p(1+e^λπ_p) + 2(2e/M)^M|s|^M ε'

  with `‖μ_p−1‖ ≤ c_p`, `‖g_p‖ ≤ 1`, `g_p = 1` off the active set.

**Budget check (paper).**  In the application `π_p = k/p`, `c_p = 2π_p`, `μ := ∑_p π_p ≍ kL`,
`M = Cμ`.  Term 2: `≤ exp(−M log λ' + 2λ'μ) = exp(−M(log λ' − 2λ'/C))`.  Term 3:
`≤ 2 exp(−M log(λ/2e) + e^λ μ) = 2 exp(−M(log(λ/2e) − e^λ/C))`.  With `λ = 8`, `λ' = 8`,
`C ≥ 10^4` both are `exp(−Θ(M))`, and `M ≍ kL ≫ L·8^{−K}` so they sit far below the main term
`exp(−cL8^{−K})`.  Terms 1 and 4 are the two CRT errors, `ε, ε' ≲ 2^M P R^M/X`, times at most
`(2e)^M R^{M}`: `X^{−1+o(1)}` under the §5 schedule `R = X^{1/(20M)}`.  **C3 is now entirely
elementary.**

### ⬆️ UPDATE (same lap): `CRTInput` PROVED — C3 is now input-complete

`src/NormalNumbers/G4CRTInput.lean` (sorry-free, trust-triple axioms):
* `PeriodicMod h p` (`h n = h (n % p)`), `PeriodicMod.of_dvd`, `periodicMod_prod`.
* `sum_range_mul_eq_mul_sum` — two-modulus CRT: `∑_{b<mn} f b · g b = (∑_{i<m} f i)(∑_{j<n} g j)`
  (bijection `b ↦ (b%m, b%n)` on `range (mn)`, `Nat.chineseRemainder` for surjectivity,
  `Nat.modEq_and_modEq_iff_modEq_mul` for injectivity).
* `resMean_prod` — residue mean of a product over pairwise-coprime moduli = product of the means.
* `norm_sampleAvg_sub_resMean_le` — equidistributed sample (each class mod `Q` within `δ` of
  `|P|/Q`) ⟹ `‖avg h − resMean h Q‖ ≤ Qδ/|P|` for bounded `Q`-periodic `h`.
* `abs_card_filter_modEq_sub_le` — `|#{n<X : n ≡ c (m)} − X/m| ≤ 1` (`Nat.count_modEq_card`);
  `apSample_filter_eq` — a class mod `Q` inside the AP sample is ONE class mod `P₀Q`;
  `abs_card_filter_apSample_sub_le` — the AP sample is equidistributed mod coprime `Q`, `δ = 2`.
* **`crt_input`** — `‖avg_{apSample X P₀ a} ∏_T h_i − ∏_T resMean(h_i, p_i)‖ ≤ 2Q/|sample|`.

Both hypotheses of `norm_sampleAvg_prod_sub_prod_le'` are instances (`h_i = g_i − 1` and
`h_i = 1[active]`, means `μ_i − 1` and `π_i`), so **§4C's transfer C3 has no open input**.

### ⬆️ UPDATE (same lap, third commit): §4C ASSEMBLED ABSTRACTLY — `norm_sampleAvg_prod_ee_le`

`src/NormalNumbers/G4FourierControl.lean` (sorry-free, trust-triple axioms):
* `crt_input_two` — `crt_input` for fluctuations bounded by `2` (error picks up `2^{|T|}`).
* `LocalPhase p` — active roots `⊆ range p`, phases `x`, good-prime condition `2k ≤ p`;
  `θ`, `Active`, `periodicMod_ee_theta`, `periodicMod_indicator`, `ee_theta_eq_one_of_not_active`.
* `resMean_ee_theta` — `μ_p = p⁻¹((p−k) + ∑_{roots} ee x_b)`, the C2 local average;
  **`norm_resMean_ee_theta_le`** — `‖μ_p‖ ≤ 1 − 4θ/p` for `θ ≤ ∑_{roots} dist(x_b,ℤ)²` (C1+C2);
  `norm_resMean_ee_theta_sub_one_le` — `‖μ_p − 1‖ ≤ 2k/p`; `resMean_indicator` — mean `k/p`.
* **`norm_sampleAvg_prod_ee_le`** — for good primes `s` (prime, coprime to `P₀`, `≤ R`) with local
  data and lower bounds `θ_p`:

      ‖avg_{n<X, n≡a(P₀)} ∏_{p∈s} ee(θ_p n)‖ ≤ exp(−∑_p 4θ_p/p)
          + N_M · 2^M · 2R^M/|P|  +  λ'^{−M} ∏_p(1+2λ'k_p/p)
          + 2(2e/λ)^M ∏_p(1+e^λ k_p/p)  +  2(2e/M)^M |s|^M · 2R^M/|P|.

**What separates this from `PropC`**: only the identification `torusChar q (S n) = ∏_p ee(θ_p n)`
for the concrete `S`, with `θ_p` the `LocalPhase` built from the roots `−ρ_{α,j} mod p` and phases
`w_α 4^{−j}`, plus `θ_p := 4^{−4}8^{−K}`-type lower bounds from `sum_sq_distZ_freqDepth_ge` (which
needs the roots distinct mod `p` so every `(α,j)` contributes its own phase — the "good prime"
condition), and the harmonic sum `∑_{p∈s} 1/p`.  That is the Frame instantiation (§5 module).

### ⬆️ UPDATE (same lap, fourth commit): the phase decomposition — §4C for phase sums of shifted `ω`

`src/NormalNumbers/G4PhaseDecomp.lean` (sorry-free, trust-triple axioms):
* `ee_add`, `ee_sum`; `omegaOn s m = #{p ∈ s : p ∣ m}`; `totalPhase s ρ x n = ∑_i x_i ω_s(n+ρ_i)`
  (this IS `q·S(n)` with `ι = {(α,j) : K<j≤J}`, `ρ = ρ_{α,j}`, `x = w_α 4^{−j}`);
  `localPhase p ρ x n = ∑_i x_i 1[p ∣ n+ρ_i]`; **`ee_phase_eq_prod`** — `ee(Φ n) = ∏_{p∈s} ee(θ_p n)`.
* `root p ρ i = −ρ_i mod p`, `dvd_add_iff_mod_eq_root`.
* `LocalPhase.ofShifts` — the induced local data (roots = image of `root`, phase = sum of the
  coefficients landing there); `theta_ofShifts` — its `θ` is `localPhase`; `shiftPhase` (trivial
  off the good-prime condition `0 < p ∧ 2|ι| ≤ p`).
* **`sum_sq_ofShifts_eq`** — for a good prime (`root p ρ` injective), `∑_{roots} dist(x_b)² =
  ∑_i dist(x_i)²`: the frequency-separation quantity of `G4FreqSep` is exactly what C2 sees.
* **`norm_sampleAvg_ee_phase_le`** — `‖avg ee(Φ n)‖ ≤ exp(−∑_{p good} 4θ₀/p) + (four errors)` for
  any `θ₀ ≤ ∑_i dist(x_i,ℤ)²`.

**Status of C.**  C1, C2, C3 proved; C assembled for arbitrary phase sums of shifted `ω`.  To reach
`PropC` verbatim one needs only: (a) the concrete `Frame.S` written as `totalPhase` per `q`
(`torusChar q (S n) = ee(∑_ν q_ν S_ν n)` and `∑_ν q_ν S_ν = totalPhase` with `w = Aᵀq` — pure
algebra on the definition of `S`), (b) `θ₀ = 4^{−4}8^{−K}` from `sum_sq_distZ_freqDepth_ge` (note
that lemma bounds `∑_α dist(w_α4^{−j_α})²`, a SUB-sum of `∑_{α,j} dist(w_α 4^{−j})²`, so it is a
valid `θ₀`), (c) `∑_{p ≤ R good, p ∤ P₀} 1/p ≥ L − o(L)` (Mertens, minus the excluded primes and
the bad primes — the bad primes are those dividing some `ρ_{α,j} − ρ_{α',j'} ≠ 0`, at most
`|ι|² log(3X)/log p`... their harmonic mass is the §5 `O(log L)`), and (d) **C4**: the budget.
(c) and (d) are the §5 schedule module.

### ⬆️ UPDATE (same lap, fifth commit): C4 — the budget is dominated (`G4Schedule.lean`)

`src/NormalNumbers/G4Schedule.lean` (sorry-free, trust-triple axioms): `scheduleK L =
⌊log L/(100 log log L)⌋`; `scheduleK_log_bound` — for `log L ≥ 1000`, `K ≥ 1`:
`(2K+1) log K + K log 8 ≤ (log L)/10`; **`schedule_budget`** — for every fixed `C, c > 0`,
eventually `C·K^{2K+1}·8^K < c·L`, i.e. `exp(C·r·K)·exp(−c·L·8^{−K}) < 1` with `r = K^{2K}`.
This is C4 in the abstract: the `exp(O(rK))` ℓ¹ budget against the `exp(−cL8^{−K})` decay, one
simultaneous limit in `L`.  Wiring it to `Λ = (2D+1)^r` (`D = O(2^{K/4})`, so `log Λ = O(rK)`)
and to `δ₃` from `norm_sampleAvg_ee_phase_le` is the Frame-instantiation step.

**§4C is now closed at the abstract level: C1, C2, C3, C4 all proved.**  What remains for
`PropC` is purely the concrete Frame: the `S`-as-`totalPhase` identity, `θ₀` from `G4FreqSep`,
and the good-prime harmonic sum.

### C3 remaining before these updates: ONE lemma, `CRTInput` (now PROVED above)
For pairwise-coprime moduli `p ∈ T` (all coprime to the progression modulus `P₀`), functions
`h_p : ℕ → ℂ` periodic mod `p` with `‖h_p‖ ≤ 1`, and the sample `{n ≤ X : n ≡ a (mod P₀)}`:

    ‖avg_n ∏_{p∈T} h_p(n) − ∏_{p∈T} (p⁻¹∑_{b<p} h_p(b))‖ ≤ Q·P₀/X · 2   (Q = ∏_T p, once Q P₀ ≤ X).

Both `hsmall` (`h_p = g_p − 1`, mean `μ_p − 1`) and `hcrt` (`h_p = 1[active]`, mean `π_p`) are
instances.  Proof: each residue class mod `Q` receives `N/Q + O(1)` sample points; CRT
(`ZMod.chineseRemainder` / `Nat.ModEq`) factorizes the mod-`Q` average.  Next lap's target.
Then C4 (`Λδ₃ < 1`) and the instantiation `PropC` from `G4LocalContraction` + this file.

## 🧭 REVIEW 2026-09-14 (G4 lap 3): crux moved B → C; §4C's arithmetic seed PROVED; C decomposed

**Course correction.**  Laps 1–2 both spent themselves on §4B.  §4B is now *input-complete*
(spectral bound, ellipsoid volume, tube piece, torus projection, cylinder covering, det
monotonicity) and what remains there is assembly: Markov + marginals + finite unions.  §4C —
the half the brief itself leaves unproved ("the growing-array moment and exponential-moment
bounds still need proofs"; "the transfer from the independent residue model to the actual
progression is not automatic independence") — had received **zero** laps.  It is now the
mandated target (`DIRECTION.md` CURRENT DIRECTIVE, 2026-09-14).

### Proved this lap (unconditional, `#print axioms` = trust triple)

`src/NormalNumbers/G4MinWeight.lean`
* `wt` / `MinWeight`; `two_le_wt_of_sum_eq_zero`.
* **`minWeight_kronPow`** — minimum distance of a product code: `MinWeight M d` ⟹
  `MinWeight (M^{⊗K}) (d^K)`.  Induction peeling one tensor coordinate
  (`wt_cons`, `vecMul_kronPow_cons`); the row/column argument, not a dimension count.
* **`minWeight_diff`** — `D_s` has minimum weight `2`: rows telescope (`sum_diff_row`) so the
  image has zero total sum, and `D_sD_sᵀ = T_s` with `det T_s = s+1 ≠ 0` gives injectivity.
* **`minWeight_tensorDiff`** / `minWeight_kronPow_diffZ` (ℤ form): `‖supp(Aᵀq)‖₀ ≥ 2^K`.
* `colSum_diff_le`, `abs_vecMul_kronPow_le`, **`abs_vecMul_tensorDiff_le`**: `‖Aᵀq‖∞ ≤ 2^K‖q‖∞`.

`src/NormalNumbers/G4FreqSep.lean`
* `distZ`, `le_distZ` (no need to identify `round x`: either it is `0`, or the distance is `≥ ½`).
* **`freqDepth K w = K + 1 + ⌈log₄|w|⌉`**, `lt_freqDepth` (`j > K`, a *retained* layer),
  `mem_window_freqDepth` (`4^{−(K+2)} ≤ |w|4^{−j} ≤ 4^{−(K+1)}`), `le_distZ_freqDepth`.
* **`freqDepth_le`** — uniform `j_α ≤ K+1+⌈log₄(2^K D)⌉` over the whole box `‖q‖∞ ≤ D`
  (the brief's "`j_α < J` uniformly").
* **`sum_sq_distZ_freqDepth_ge`** — `∑_α dist(w_α4^{−j_α},ℤ)² ≥ 4^{−4}·8^{−K}` for every
  nonzero integer `q`.  Stronger than the brief's double-sum form, which it implies (the
  omitted `j ≠ j_α` terms are nonnegative and `K < j_α`).

**Why the constant is structural.**  `16^{−K}` is the *square of the window scale* `4^{−(K+2)}`;
`2^K` is the *code distance* of `D_s^{⊗K}`.  Weakening the support bound from `2^K` to `2`
(which a naive "the image is nonzero" argument gives) would leave `16^{−K}`, and `L·16^{−K}`
does **not** dominate `rK` with room to spare in the §5 schedule the way `L·8^{−K}` does.  Both
inputs are load-bearing.

### Checked on paper this lap (NOT yet Lean) — the §5 budget is not the risk

With `s=K²`, `H=(s+1)^K`, `r=s^K`, `η=2^{−K/4}`, `L=log log X`, `K=⌊log L/(100 log log L)⌋`:
* `H/r = (1+1/K²)^K → 1`, so `r/H → 1` as §5 asserts; `log r = 2K log K = (0.02+o(1))log L`.
* Tube exponent `−((1−ε) − d'·H/r)·r·(K log2)/4 + O(r√K) → −∞` whenever `1−ε−d' > 0`, because
  `rK ≫ r√K`.  The covering count needs `log(1/δ)/log(1/η) ≤ d'/d`, and choosing `M` minimal with
  `4^{−ℓM} ≤ η` gives ratio `≤ 1 + ℓ log4/((K/4)log2) → 1`; fine for any `d' > d` once `K` is large.
* `8^{−K} = L^{−o(1)}`, so `L·8^{−K} = L^{1−o(1)}` dominates `rK = L^{0.02+o(1)}`, i.e. the decay
  beats the `exp(O(rK))` ℓ¹ budget.
So the parameter schedule is self-consistent on all four of the brief's essential comparisons.
**The risk is C3, not the budget.**

### ⬆️ UPDATE (same lap, after the decomposition): C1, C2 and **the C3 skeleton** are PROVED

`src/NormalNumbers/G4LocalContraction.lean`
* **C1** `eight_mul_distZ_sq_le_one_sub_cos` : `1 − cos2πx ≥ 8·dist(x,ℤ)²`.
* **C2** `norm_localSum_le` / `norm_localSum_le'` / `norm_localAvg_le_of_sum_sq`.
* `prod_one_sub_le_exp_neg_sum`, `prod_contraction_le_exp` : `∏(1−c/p) ≤ exp(−c∑p⁻¹)`.

`src/NormalNumbers/G4Transfer.lean` — **the C3 skeleton, proved in full**:
* `prod_sub_expansion` : `∏_{p∈s} g_p = ∑_{T⊆s}(∏_T f_p)(∏_{s∖T}μ_p)`, `f_p = g_p − μ_p`.
* **`mul_pow_sum_powerset_card_gt_le`** — the Chernoff subset tail
  `lam^M·∑_{|T|>M}∏_T c_p ≤ ∏_{p∈s}(1+lam·c_p)` for `lam ≥ 1`, `c ≥ 0`.  This is what makes the
  `2^{|s|}` subsets summable at all: the tail is paid by ONE exponential moment, not termwise.
* **`norm_sampleAvg_prod_sub_prod_le`** —
  `‖avg_n ∏_{p∈s}g_p(n) − ∏_{p∈s}μ_p‖ ≤ N_M·ε + B/lam^M`, given
  (i) `‖avg_n ∏_{p∈T}f_p(n)‖ ≤ ε` for all nonempty `T ⊆ s` with `|T| ≤ M`, and
  (ii) `avg_n ∏_{p∈s}(1+lam‖f_p(n)‖) ≤ B`.
* **`norm_sampleAvg_prod_le_exp`** — composed with C2:
  `‖avg_n ∏ g_p‖ ≤ exp(−c∑_{p∈s}w_p⁻¹) + N_M ε + B/lam^M`.  With `c = 4·4^{−4}·8^{−K}`,
  `w_p = p`, `∑_{p≤R}p⁻¹ = L−o(L)` this is `exp(−cL8^{−K}) + errors` — **the shape `PropC δ₃`
  needs**.

**So C3 is no longer "not automatic independence" — it is TWO named quantitative inputs:**

* **C3a** = `ε`.  For nonempty `T` with `|T| ≤ M`, `∏_{p∈T}f_p(n)` depends only on
  `n mod ∏_{p∈T}p`, and `∏_{p∈T}p ≤ R^M = X^{1/20}`, so CRT + equidistribution of `P∩[1,X]`
  gives `𝔼 = ∏_{p∈T}𝔼f_p + O(P R^M/X) = 0 + O(P R^M/X)`.  Since `N_M ≤ (|s|+1)^M ≤ R^M`, the
  first error term is `P R^{2M}/X` — **exactly the brief's "bounded schematically by
  `P R^{2m}/X` for `m ≤ M`"**, which confirms the reading.  Elementary counting; do this next.
* **C3core** = `B`.  `avg_n ∏_{p∈s}(1+lam‖f_p(n)‖)`.  In the G4 application `f_p(n)` is `O(k/p)`
  unless `n` lies in one of the `k = H(J−K)` active classes mod `p`, so pointwise
  `∏_p(1+lam‖f_p‖) ≤ (1+2lam)^{V(n)}·exp(2 lam k ∑_p p⁻¹)` with `V(n)` = number of active
  primes, `V(n) ≤ ∑_{α,j}ω_{≤R}(n+ρ_{α,j})` and `𝔼V ≍ kL`.  So `B = exp(O_{lam}(kL))` and
  `lam^{−M} = exp(−M log lam)` beats it exactly when `M ≍ C k L` with `C` large — **the brief's
  `M ≍ C T L` is calibrated for precisely this**, which is independent confirmation of the
  schedule.  Bounding `𝔼(1+2lam)^{V(n)}` over the progression is a Shiu-type exponential moment
  for `ω` — a PROVEN, project-scale theorem, not an open conjecture.
  ⚠️ Alternative worth trying first, to avoid Shiu entirely: `𝔼 V^m` for `m ≤ M` is itself
  CRT-computable (modulus `R^M ≤ X^{1/20}`), so a *moment* tail may replace the exponential one.
  That would make all of C3 elementary.  **Test this before importing Shiu.**

### §4C decomposed — the next attacks, hardest-first

Write `S_ν(n) = ∑_α A_{να} ∑_{K<j≤J} 4^{−j} ω_{≤R}(n + ρ_{α,j})`, so with `w = Aᵀq`

    q·S(n) = ∑_{p ≤ R} θ_p(n),   θ_p(n) = ∑_{α, K<j≤J} w_α 4^{−j} · 1[p ∣ n + ρ_{α,j}],

and `θ_p(n)` depends only on `n mod p`.  Hence `e(q·S(n)) = ∏_{p≤R} e(θ_p(n))` — a product of
functions of `n` in distinct prime moduli.  The four named obligations:

* **C1 — phase-to-distance (elementary, do first, it is the input to C2).**
  `1 − cos(2πx) ≥ 8 · distZ(x)²` for every real `x`.  Proof: `1−cos2πx = 2sin²(πx)` and
  `|sin πx| = sin(π·distZ x) ≥ 2·distZ x` by Jordan (`Real.mul_le_sin`, already used in
  `G4Spectral`).  This is the "reduce mod one **before** moment comparison" step of the brief:
  `distZ` is exactly the reduced representative, and nothing downstream sees `w_α4^{−j}` again.
* **C2 — one good prime contracts.**  If `p` is prime, `x : ι → ℝ` a family indexed by the
  active roots with `card ι ≤ p` and the roots distinct mod `p` (so exactly one root fires per
  nondefault class and the default class has probability `≥ 1/2`), then
  `|p⁻¹ ∑_{a mod p} e(θ_p(a))| ≤ 1 − (8/p)·∑_i distZ(x i)²`.
  Combined with `sum_sq_distZ_freqDepth_ge`: `≤ 1 − 8·4^{−4}·8^{−K}/p`.
  Then `∏_{p∈𝒫}(1 − c·8^{−K}/p) ≤ exp(−c·8^{−K}·∑_{p∈𝒫}p^{−1})`, and `∑_{p≤R}p^{−1} = L − o(L)`
  once the excluded primes' harmonic mass `O(log L)` is removed.  **Independent model only.**
* **C3 — THE CRUX: transfer from the independent model to the progression.**  The brief:
  "The transfer from the independent residue model to the actual progression is not automatic
  independence.  Expand moments to even degree `M`, count residue classes by CRT, and sum the
  finite-sample errors, bounded schematically by `P R^{2m}/X` for `m ≤ M`."  Concretely, with
  `f_p(n) = e(θ_p(n)) − 𝔼e(θ_p)`, bound `|𝔼_{n∈P∩[1,X]} ∏_p (𝔼e(θ_p) + f_p(n))| ` by expanding
  and controlling `𝔼_{n} ∏_{p∈T} f_p(n)` for `|T| ≤ M` via CRT counting on the modulus
  `P·∏_{p∈T}p ≤ P·R^M`, with `R = X^{1/(20M)}` making `P R^{M} = X^{o(1)}`.
  **This is the only obligation in C whose failure would force a redesign.  Attack it first
  as a named `Prop` in `src/`, then decompose.**  Trigger **G-T1**: 5 grind laps.
* **C4 — the budget is uniform.**  `Λ = (2D+1)^r = exp(O(rK))` and `δ₃ = exp(−cL8^{−K})`;
  show `Λδ₃ < 1` under §5.  Never "for each fixed `q`, let `X → ∞`" — one estimate, uniform on
  the whole box.

### §4B assembly to `PropB` — secondary (labour, not risk); all inputs proved

1. Choose a cylinder `[w/4^ℓ,(w+1)/4^ℓ) ⊆ [a,c)` strictly inside the omitted interval.
2. `orbitClosure_subset_cylinders` ⟹ `C^H ⊆ ⋃_{b} ∏_h π(cyl b_h)`, `(B−1)^{MH}` products, each a
   cube of side `4^{−ℓM} ≤ η`.
3. Markov on `dAv`: `dAv(y,z) ≤ 2εη` ⟹ `#{ν : dist > η} ≤ 2εr`, so `∃ G`, `|G| ≥ (1−2ε)r`,
   `y_G ∈ c_G + η[A_G,I_g]([−1,1]^{H+g})` after absorbing the cylinder cube; `≤ 2^r` sets `G`.
4. Torus marginal: `vol_{𝕋^r}(π_G^{-1}(B)) = vol_{𝕋^G}(B) ≤ vol_{ℝ^g}(·)`
   (`volume_image_torusProj_le`), then `volume_tubePiece_le` and `addHaar_smul` for `η^g`.
5. Arithmetic as verified above.  Note `Frame.A` is over `ℤ` while `tensorDiff` is over `ℝ`;
   `G4FreqSep.diffZ` + `cast_vecMul_kronPow_diffZ` is now the bridge to use.

## 📏 MEASURED 2026-09-08 (lap 4): the run+jump theorem alone reaches `1/4 − O(1/p)` at EVERY prime `< 2000`

`experiments/mahler_runjump_admissible.py`: for each prime `p < 2000`, the best `b` with
`3 ≤ b < p/2` and `−1 ∈ ⟨p⟩ (mod b)` (the hypothesis of the PROVED `mahler_lower_bound_runjump`).
* The gap `j = p − 2b` of the best admissible `b` is **at most 33** (`p = 853`), typically `≤ 9`;
  so `b(p−b−1)/p² ≥ 0.2416` for every prime `p ≥ 61`, `0.2497` near `p = 2000` — **including every
  `p ≡ 1 (mod 12)`** (the class the `b ∣ p+1` corollaries miss).  The route's T3 dichotomy
  (`3/16` vs `1/12`) was too pessimistic: the theorem's own hypothesis is nearly always satisfiable
  near `p/2`.
* Against the census: deficits `1, 0, 1, 3, 0, 5, 0` at `p = 11 … 31` — exact at `13, 23, 31`.
* **Landed**: `mahler_lower_bound_runjump_near_half` — `p = 2b + j`, `−1 ∈ ⟨p⟩ (mod b)` ⟹
  `M(p,1) > (p−j)(p+j−2)/4 − 1`.  This IS trigger T3's "clean conditional `1/4`", as a theorem.
* **Open arithmetic (for the altitude lap)**: prove that some `b ∈ (p/2 − C, p/2)` is admissible.
  `b = (p−j)/2` is admissible iff `−1 ∈ ⟨j⟩ (mod (p−j)/2)` (since `p ≡ j`).  `j = 1` never
  (`⟨1⟩`), `j = 3` iff `−1 ∈ ⟨3⟩ mod (p−3)/2` (= family-I's hypothesis).  A uniform proof needs
  a small odd `j` with `−1 ∈ ⟨j⟩ (mod (p−j)/2)` — a character-sum / Artin-type question; NOT a
  grind-lap target.  The unconditional floor stays `3/16` (`p ≢ 1 mod 12`) / `1/12`.

## ✅ GRIND 2026-09-08 (lap 3): `mahler_lower_bound_runjump` PROVED — the directive's mandated move is DONE

`src/NormalNumbers/MahlerRunJumpWalk.lean` (new, sorry-free, `#print axioms` clean, build 8888 jobs):

* **`key_of_congr`** — the departure congruence mod `Dh`, the landing congruence mod `Dn`, and
  `Coprime Dh Dn` give the exact identity `key` with the forced digit.  So the data needs only
  congruences, never an explicit `dj`.
* **The data** (`mk`): `al i = p^{T−1} mod Dh i`, `cj i = p^{2T−2} mod Dh i`, `ap i = 1` along the run;
  at the jump `al 0 = p^{3f−2} mod b` (`p^f ≡ −1` ⟹ `p²·al 0 ≡ −1`), `cj 0 = p^{3f−3+T} mod b`,
  `ap 0 = p^{T−1} mod (b+L)` (works because `p ≡ b (mod b+L)`).  `T` is abstract in `Arith`
  (`p^T ≡ 1 mod every Dh j`, `T ≥ 1`); the theorem takes `T = 2φ((p−b)!)`.  The two ZMod
  computations (`mk_dep` at `i = 0`, `mk_land` at `i = 0`) are the only arithmetic; the run is
  `Nat.div_add_mod` + `linear_combination`.
* **The walks**: walk A = block `L` (`F_L(p^{T−1}) … F_L(p^{2T−2}), J_L`), middle blocks
  `j = L−1 … 1` (`F_j(1) … F_j(p^{2T−2}), J_j`, each of length `2T`), block `0`
  (`F_0(1) … F_0(p^{t₀}), J_0`, `t₀ = 3f−3+T`); period `PA = T+1 + (L−1)·2T + t₀+2`.  Positions are
  decoded by a three-case formula (`pos_cases`), no lists.  Walk B = the far cycle in background `L`
  (period `T`).  Common start `F_L(p^{T−1})`; digits differ at the start of block `0`
  (`dig F_0(1) = ⌊p/b⌋ ≥ 2` vs `dig F_L(1) = 1`); every far→far edge is non-`hi`-extremal
  (`not_hiMax_far`: the width shrinks by `p`).
* **Theorem + corollaries**: `mahler_lower_bound_runjump`, `…_of_dvd` (`f = 1`), `…_three` (`2/9`),
  `…_four` (`3/16`), anchors `base13` (`M ≥ 35`, exact) and `base31` (`M ≥ 224`, exact).

**Census cross-check (T2 tripwire)**: every admissible `(p, b)`, `p ≤ 31`, gives `b(p−b−1) ≤ M(p,1)`;
exact at `(13,5) → 35`, `(23,10) → 120`, `(31,14) → 224`.  So the run+jump chain is OPTIMAL at
`p = 13, 23, 31` — the census value is attained by a certificate we can now name.

### Lean gotchas this lap
* `subst h` with `h : n = T` (both local variables) eliminated `T`, breaking every later `T`; use
  `rw [h]` when the right-hand variable must survive.
* `rw [← ap_run …]` (rewriting `1` backwards) hits EVERY `1`, including `L − 1`; rewrite the
  hypothesis forwards instead.
* `Nat.div_add_mod` is `k * (n / k) + n % k`; `omega` needs `Nat.div_add_mod'` when the goal has
  `n / k * k`.
* `subst` on `p = 3 * c + 2` inside a corollary makes every hypothesis about `p` concrete — then
  `omega` handles the `−1 mod b` residues directly.

### Next (altitude lap decides; T1 is satisfied within 2 grind laps)
* The uniform constant is now `3/16` for `p ≢ 1 (mod 12)` and still `1/12` for `p ≡ 1 (mod 12)`
  (trigger **T3**).  For `p ≡ 1 (mod 12)`: `−1 ∈ ⟨p⟩ (mod b)` for a large `b` is the remaining
  arithmetic; e.g. `b ∣ p^2 + 1` (`f = 2`), `b = (p²+1)/2` is too big, but any divisor `b` of `p²+1`
  in `(p/3, p/2)` works — worth a census of which primes `p ≡ 1 (mod 12)` have one.
* The three EXACT hits suggest the run+jump chain with the best admissible `b` is the true
  optimum whenever `M(p,1) = ⌊p/2⌋² − 1` or `− 4`; check against the census at `p = 13, 19, 23, 29, 31`.


## ✅ GRIND 2026-09-08 (lap 2): `MahlerRunJump.valid` PROVED — the certificate is sorry-free

`src/NormalNumbers/MahlerRunJump.lean` is now **sorry-free**; `RunJump.valid : (cert D).Valid M [p-1]`
for every `M < b(b+L−1) = b(p−b−1)`, `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
Build green 8887 jobs.

### How the four sub-sorries fell (one mechanism, not four)

**The generic two-denominator edge** (`section generic`, `gen_lo/gen_hi/gen_carry_lo/gen_carry_hi/
gen_x/gen_rec/gen_block`).  Every edge `s → s'` has `lo s = N/E`, `lo s' = N'/E'` with LOCAL
denominators, carries `⌊mN/E⌋`, and the exact integer identity

    d·E·E' + N'·E = p·N·E' + δ        (δ ≥ 0)

— the per-edge form of `NumCert.Good.edge`.  From it: `edges` (both sides), `recursion` and `block`
follow via `gen_x`: `m·d + ⌊mN'/E'⌋ = ⌊(p·(mN mod E)·E' + mδ)/(EE')⌋ + p·⌊mN/E⌋`, and the block
inequality is `p·(mN mod E)·E' + mδ + EE' < p·EE'` (stated without `p−1` so `omega` handles it).
The carry inequality is `(mN mod E) + m·w·E ≤ E`.

**Local data** (`En`, `Nn`, `wd`): far `(i,r)`: `E = Dh i`, `N = r`, `w = wid i`; junction `J i`:
`E = p·Dh·Dn`, `N = al·p·Dn + 1`, `w = wid(nx i)/p`.  `lop_eq/hip_eq/cc_eq` show these are
definitionally the certificate's `lo/hi/c`.

**The three edge types** (`edge_data`, via `nxt_cases`):
* far→far: `δ = 0`, identity = `Nat.div_add_mod`; block ⇐ `Dh < p`.
* injection far→`J i`: `δ = Dh i`, identity from `inj` (`Dh·q + al = cj·p`) times `Dh·p·Dn`;
  width ⇐ `p·Dh'Dn' + Dh·Dn ≤ p²·Dh'Dn'`; block ⇐ `m + Dn·Dh < p·Dn` (×p, the `p`-times-weaker cost).
* junction `J i`→far: `δ = 0`, identity = `key` times `p·Dn` (EXACT); block ⇐ `jmod` +
  `m + Dn·Dh < p·Dn`.

**The one line of content** is `cost_ge`: `b(b+L−1) + Dn i·Dh i ≤ p·Dn i` for all `i ≤ L`, i.e.
`M < Dn i·(p − Dh i)` — with `p − Dh i = b+L−i` and `Dn i = b+i−1` the product is
`b(b+L−1) + (i−1)(L−i) ≥ b(b+L−1)`, equality at `i = 1` and `i = L`; the jump `i = 0` costs `(b+L)²`.
`jmod` is the junction residue `m(al·p·Dn+1) mod (p·Dh·Dn) = p·Dn·(m·al mod Dh) + m` for `m < p·Dn`.

### Lean gotchas this lap
* `linear_combination` over ℕ works but has no negation: flip the hypothesis (`h.symm`) instead of
  negating the coefficient.
* `nlinarith` TIMES OUT (200k heartbeats) on goals that are linear in the monomials once the
  product hints are supplied — `linarith` proves them instantly (it treats monomials as atoms).
* Under `include hb hp`, lemmas that don't use them still get them auto-included; `omit hb hp in`
  each one, or call sites break with "expected `3 ≤ b`".
* `field_simp` closes cast-identities itself; end with `try ring`, not `ring`.
* `positivity` cannot see through `set` variables — supply `mul_pos`/`div_pos` by hand.
* `set i := rs s` does NOT fold `rs s` produced by LATER rewrites — `rw [← hi]` after them.

### Next (in order) — the theorem itself
1. **`Data` existence**: for `i ≥ 1`, `al i = p⁻¹ mod Dh i` (needs `gcd(p, Dh i) = 1`: `p` prime,
   `Dh i < p`), `ap i = 1`, `dj i = (p·al i − 1)/Dh i`; check `key` reduces to `p·al ≡ 1 (mod Dh)`.
   `cj i = al i · p⁻¹ mod Dh i`.  For `i = 0` the closing jump: `al 0` with `p·al 0·(b+L) ≡ −1 (mod b)`,
   i.e. `p·al 0·L ≡ −1`, from `−1 ∈ ⟨p⟩ (mod b)` — this is where `hord` enters.
2. **The walk**: a closed walk through all junctions, each far cycle traversed to its injection
   source (`p^(φ(D)−2)` steps, Euler), with mixing (a non-`hi`-extremal edge).  Template:
   `MahlerFareyJunction.lean`'s walk + `EscapeCert.isClosedWalk_periodic`.
3. **`mahler_lower_bound_runjump`** and the two `b ∣ p+1` corollaries (`2/9`, `3/16`).


## 🔨 GRIND 2026-09-08 (post-reflection): `MahlerRunJump.lean` started — crux decomposed into 4 named sub-`sorry`s

**Landed** `src/NormalNumbers/MahlerRunJump.lean` (wired into `NormalNumbers.lean`; build green
8887 jobs).  The directive's run+jump chain, set up as a direct `EscapeCert` instance.

### Design decision (recorded so it is not re-litigated)

**It does NOT go through `NumCert`.**  A numerator certificate needs ONE common denominator `E`
for all states; with `Θ(p)` backgrounds `E = p·lcm(b … p−b)` and the junction perturbations
`1/(pDD')` become enormous multiples of `1/E`, breaking `NumCert.Good`'s `δ < (p−1)σ` slack
budget (checked on paper: `σ` would have to be `≈ E/(p²b²)`, and then the `res` condition caps
`M` below the target).  Instead `EscapeCert` is instantiated directly with **rational intervals of
per-background width** `wid i = 1/(p · Dh i · Dn i)` — exactly the scale that absorbs the
perturbation.  A single global width does NOT work (checked: the carry condition at the junction
of the largest background then fails whenever `b ≲ p/13`).

### What is in the file

* `Dh b i = b + i` (backgrounds, `Dh 0 = b`, `Dh L = p − b` with `p = 2b + L`);
  `nx L i = if i = 0 then L else i − 1` (the closing jump `0 ↦ L`); `Dn b L i = Dh b (nx L i)`.
* `Data` = the four per-junction functions `al` (departure), `cj` (injection source),
  `ap` (landing), `dj` (junction digit); `Hyp` = their ranges plus TWO arithmetic facts:
  `inj : cj i * p % Dh i = al i` and the single **exact-landing identity**
  `key : p · al i · Dn i + 1 = ap i · Dh i + dj i · (Dh i · Dn i)`.
  Reducing `key` mod `Dh i` gives the departure condition `p·al·Dn ≡ −1`; mod `Dn i` it gives the
  landing condition `ap·Dh ≡ 1`.  One identity, both conditions — this is the packaging that makes
  the general chain tractable.
* States `Fin ((L+1)·p + (L+1))`: far `(i,a) ↦ i·p + a`, junction `J i ↦ (L+1)·p + i`; `s.1 / p`
  decodes the kind (`≤ L` far, `= L+1` junction).  Indices whose residue exceeds the background are
  harmless aliases — every definition reduces `rs s % Dh`.  Decoding lemmas `far_val`, `ix_far`,
  `rs_far`, `jn_val`, `ix_jn`, `rs_jn`, `state_cases` all proved.
* **PROVED**: `dig_lt` (digits legal) and `intervals` (`0 ≤ lo ≤ hi ≤ 1`, both state kinds; the
  junction case needs `d·dn ≤ b²(p·dn − 1)`, which holds because `b² ≥ 9` and `p·dn ≥ 21`).

### The 4 open sub-`sorry`s, with the paper proof of each

1. **`edges`** — `lo s ≤ (dig s + lo s')/p` and `(dig s + hi s')/p ≤ hi s`.  Three edge types:
   *far* `F_i(a) → F_i(pa mod Dh)`: exact on the left (`δ = 0`), and `w/p ≤ w` on the right.
   *injection* `F_i(cj i) → J_i`: left gap `1/(p²·Dh·Dn) ≥ 0`; right needs
   `1/(p²·Dh·Dn) ≤ wid i · (p−1)/p`, i.e. `p(p−1)·Dh·Dn ≥ p²·Dh·Dn/…` — true since
   `wid i = 1/(p·Dh i·Dn i)`.  *junction* `J_i → F_{nx i}(ap i)`: EXACT by `key`, right needs
   `wid (nx i)/p ≤ wid (nx i)/p` — equality by construction of `hip` at junction states.
2. **`carries`** — `⌊m·lo⌋ ≤ m·lo` (free) and `{m·lo} + m·w ≤ 1`.  Far: worst
   `{} = (Dh−1)/Dh`, so `m ≤ p·Dn` suffices.  Junction: `{m·lo} = (p·Dn·(m·al mod Dh) + m)/(p·Dh·Dn)`
   provided `m < p·Dn` (no overflow), and then `m ≤ p·Dn/(1 + v·p·Dh·Dn)` with
   `v·p·Dh·Dn = Dh·Dn/(p·Dh(nx)·Dn(nx)) ≤ (5/3)/p`.  Both hold for `M < b(b+L−1) < p·b ≤ p·Dn`.
3. **`recursion`** — `⌊m·lo s⌋ = (m·dig s + ⌊m·lo s'⌋)/p`.  Follows from
   `m·dig s + ⌊m·lo s'⌋ = x + p·⌊m·lo s⌋` with `x = ⌊p·{m·lo s} + m·ε⌋` and `0 ≤ x < p`, where
   `ε = dig s + lo s' − p·lo s ≥ 0` is the per-edge gap.
4. **`block`** — the SAME `x`, with `x < p − 1`.  **This is where `M` comes from, and it is the
   one line of real content**: far edges have `ε = 0` and `p(ma mod Dh) < (p−1)Dh` because
   `Dh < p` (free); junction edges have `ε = 0` and reduce to
   `p·Dn·(m·al mod Dh) + m < (p−1)·Dh·Dn`, which follows from `m ≤ M` and
   `m·al mod Dh ≤ Dh − 1` by the exact identity
   `p·Dn·(Dh−1) + Dn·(p−Dh) = Dh·Dn·(p−1)` — i.e. **`M < Dn·(p − Dh)` is exactly the junction
   cost**; injection edges give the same with `p·Dn(p−Dh)`, `p` times weaker.
   `min_i Dn i·(p − Dh i) = b·(p − b − 1) = b(b+L−1)`, attained at both ends of the run.

### Next actions
1. `edges` (structural, three cases; needs `far`/`jn` decoding of `nxt`).
2. `block` + `recursion` together via a shared `chDigit`-style lemma, mirroring
   `NumCert.chDigit_eq`.
3. `carries`.
4. Then `Data` existence: `al i = p⁻¹ mod Dh i` for `i ≥ 1` (with `ap = 1`, `dj = (p·al−1)/Dh`),
   and for `i = 0` the closing jump; then the corollaries `b = (p+1)/3`, `b = (p+1)/4`.

## 🧘 REFLECTION — 2026-09-08 (deep reflection lap, every-9th)

**Ground truth gathered this lap** (not inherited): `lake build` green, 8886 jobs, HEAD `cc51d22`.
`#print axioms` re-run on every Mahler headline — all trust triple. Exactly ONE `sorry` in
`src/`: `exists_prime_nonresidue` (`MahlerDriftOne.lean:380`), feeding only the *conditional*
`mahler_lower_bound_prime_drift_one`. Nothing unconditional depends on it.

### 1. Destination — KEPT, and it is worth it

Pin the Mahler multiplier `M(g,k)`. The repo already answers Berend–Boshernitzan's stated open
question (`M(g,k) < g^(k+1)`, `mahler_multiplier_lt`), pins the universal constant
(`sup_g M(g,k)/g^(k+1) = 1`, sharp), and — the part with no analogue in the literature — proves a
**quadratic** prime lower bound `M(p,1) > (⌊p/2⌋²−2)/3` where B–B Thm 3.3 has only the **linear**
`M(g,1) ≥ (3/2)(g−1)`. At `k = 1`, prime base, the sandwich is `p²/12 ≤ M(p,1) ≤ p²/4 + O(p)` and
the census says the truth is `⌊p/2⌋² − {0,1,2,4}`. The crux — the factor 3 — is real and worth
closing.

### 2. Route — CONTINUE, but the *sub*-route is re-decided

`DIRECTION.md` registers no Mahler-chapter abort trigger (all its registered triggers belong to the
retired B5′ campaign), so no trigger has fired: **ROUTE VERDICT: CONTINUE.** Triggers for this
chapter are now registered (below). But the mandated *move* of the last directive — "hunt a free-`D`
background certificate, then prove `∃D ∈ (p/3,p/2)` with `−1 ∈ ⟨p⟩ (mod D)`" — is retired, because
this lap settled the structure of the whole certificate space.

### 3. What this lap PROVED (paper) and MEASURED (validated instrument)

**(a) An exact combinatorial model of the lower side.** Backgrounds `D`, `3 ≤ D < p`; a construction
is a closed walk `… → D_{i−1} → D_i → D_{i+1} → …` with consecutive `D` coprime; junction `D → D'`
costs `D'(p − D)`; the vertex condition at `D_i` is `−D_{i−1}/D_{i+1} ∈ ⟨p⟩ (mod D_i)`. Then
`M(p,1) = max over closed walks of min junction cost`. **Measured exact against the census** by
max-bottleneck-cycle search (`experiments/mahler_bg_cycle_model.py`): equal at `p = 13,19,23,29,31`,
off by one at `p = 7,11,17`. This is a *far* cheaper instrument than the trimmed-product SCC and it
localises exactly where arithmetic enters: the vertex condition, nowhere else.

**(b) Orbit-free (identity-closed) cycles are REFUTED — with a proof, not a search.** "Orbit-free"
means every vertex condition holds at exponent `0`, i.e. `D_{i−1} + D_{i+1} ≡ 0 (mod D_i)`, i.e.
`D_{i−1} + D_{i+1} = λ_i D_i` with `λ_i ≥ 1` integers. At the maximum `D_j`, `λ_j D_j ≤ 2D_j` so
`λ_j ≤ 2`, and `λ_j = 2` forces `D_{j±1} = D_j` hence (propagating) all equal, i.e. consecutive
`gcd > 1`. So `λ_j = 1` and `D_j = D_{j−1} + D_{j+1}`: the divisibility system then pins the `D_i` to
a *primitive* small tuple (the monodromy `∏[[λ_i,−1],[1,0]]` is parabolic, so the solution space is
one-dimensional and consecutive coprimality forces the scale to 1), so `D_i = O(1)` and the cost is
`O(p)`, **linear, never quadratic**. Confirmed by the `E = 0` column of
`experiments/mahler_bg_cycle_ecap.py`: **empty for every prime `7 … 89`.** The 3-cycle lead
`(5p+7)/9, (4p+2)/9, (2p+4)/3` of the previous lap is therefore **dead** — its cost `5/27 ≈ 0.185`
exceeds the general cap `3−2√2 ≈ 0.1716` that the same argument gives, so it could not have been an
orbit-free cycle; direct check confirms the vertex condition fails at `D₂`.

**(c) The single-background frames are closed off — both floor and ceiling computed.**
* *Closed-form single background* `D = (p+j)/c` (`c | p+j`, so `p ≡ −j (mod D)` and the scale `k = j`
  is free): bound `≈ p²/(2cj)`; `j = 1` is degenerate for **every** `c` (`gcd(D, p+1) = gcd(D, 1−j) =
  D`), so the best admissible pair is `cj = 6`, i.e. **exactly `p²/12` — family II is the ceiling of
  this whole frame, not a lucky instance.**
* *Single background, several offsets* `b, b' | p+1`: bound `(b−1)p²/(b + b'b − b')`, maximised over
  integers at `(b,b') = (2,3)` giving **`1/5`** — the measured ceiling, now derived. But it has **no
  uniform floor**: when `p + 1 = 2q` with `q` prime the only offsets are `2, q, 2q` and the bound
  collapses to `O(p)`. **The offset frame is dead as a uniform route.**

**(d) THE FINDING — the run+jump family.** Reading the `E ≤ 1` optima out of the model
(`experiments/mahler_bg_cycle_ecap.py`, then `mahler_runjump.py`) the winning cycles all have ONE
shape: the descending run of **consecutive integers** `p−b, p−b−1, …, b+1, b`, closed by the single
jump `b → p−b`. Every interior vertex is free (`prev = D+1 ≡ 1`, `next = D−1 ≡ −1`, condition
`p^f ≡ 1`), the vertex `p−b` is free (`f = 1`), and the ONLY arithmetic condition in the whole
construction sits at the bottom:

> **`M(p,1) ≥ b(p − b − 1)` for every `b` with `3 ≤ b < p/2`, `gcd(b,p) = 1` and `−1 ∈ ⟨p⟩ (mod b)`.**

Validated exhaustively: **2512 `(p,b)` pairs over primes `11 … 397`, ZERO mismatches** — every
vertex condition holds and the bottleneck is exactly `b(p−b−1)`
(`experiments/mahler_runjump.py`). With the best `b`, the family reproduces the free-model optimum
(`p = 37`: `b = 17`, `323`, equal to the unrestricted max) and gives ratio **≥ 0.1983 for every
prime `11 … 20000`, median `0.2499`**.

**(e) Why this is the route.** `−1 ∈ ⟨p⟩ (mod b)` is FREE whenever `b ∣ p+1` (`p ≡ −1`, `f = 1`).
So there are unconditional, closed-form, named instances:

| hypothesis | `b` | bound | ratio |
|---|---|---|---|
| `3 ∣ p+1` (i.e. `p ≡ 2 mod 3`) | `(p+1)/3` | `2(p+1)(p−2)/9` | **`2/9 ≈ 0.2222`** |
| `4 ∣ p+1` (i.e. `p ≡ 3 mod 4`) | `(p+1)/4` | `(p+1)(3p−5)/16` | **`3/16 = 0.1875`** |
| general | largest `b ∣ p+1`, `b < p/2` | `b(p−b−1)` | `(1/ℓ)(1−1/ℓ)` |

Every prime `p ≢ 1 (mod 12)` satisfies one of the first two ⟹ **`M(p,1) > 3p²/16 − O(p)` for 3/4 of
all primes, unconditional — 2.25× family II's `1/12`.** `p = 11` (`b = 4`) gives `24` against the
census `25`; `p = 23` (`b = 8`) gives `112` against `120`.

### 4. What a sharp outsider would say we were missing

The four grind laps before this one each invented a *new certificate shape* and each reduced to the
*same* arithmetic existence statement, with no map of the space. The missing thing was the map: one
model that (i) reproduces the census exactly, (ii) says where arithmetic can and cannot be avoided.
With the map in hand the answer is unambiguous — the run of consecutive integers is the unique free
skeleton, and `b ∣ p+1` is the unique free closure. Everything else in four laps of search was a
special case or a dead end.

### 5. Faithfulness at altitude

Re-read `MahlerMultiplier.lean`'s statement against Mahler 1973 / B–B 1994 (`papers/*.md`):
`mahler_multiplier` quantifies `∀ irrational α, ∀ base g ≥ 2, ∀ block w` then `∃ 1 ≤ m ≤ g^(k+1)`
with `w` occurring **infinitely often** in `m·α` — matches Mahler's Theorem 1 shape with the
sharpened constant. Lower-bound statements are `∃ α irrational, ∀ m ∈ [1,M], ∃ N, ∀ n ≥ N, ¬OccursAt`
— the correct dual (finitely many occurrences), and `M(p,1) ≥ M+1` is read off correctly. No
transcription drift found. Claim hygiene held: B–B constants are still cited as tier-S secondary,
never attributed.

### KEEP / STOP / NEXT

* **KEEP**: the background–junction frame; one coherent green commit per lap; measuring a
  construction against the census before formalising it.
* **STOP**: hunting new certificate *shapes* (the space is mapped); per-class 2-cycle theorems (the
  offset frame is dead uniformly); any further lap spent on `exists_prime_nonresidue` (Linnik-strength,
  correctly parked as a disclosed `sorry` under a conditional theorem).
* **NEXT (highest value, route-decisive)**: `src/NormalNumbers/MahlerRunJump.lean` —
  `mahler_lower_bound_runjump (p b) (hb : 3 ≤ b) (hlt : 2*b < p) (hord : ∃ f, p^f % b = b−1)`
  giving `M(p,1) > b(p−b−1) − 1`, then the two named corollaries. The state space is
  `(j, a)` with `j ≤ p−2b` and `a < D_j = p−b−j` — one index more than
  `MahlerFareyJunction.lean`, which is exactly its `b = (p−3)/2` two-background shadow.


## 🎯 GRIND LAP 2026-09-08 (Farey junction): the census construction identified — the GENERAL JUNCTION RULE

**Landed** `src/NormalNumbers/MahlerFareyJunction.lean` (wired; build green 8886; trust triple,
no sorry): `mahler_lower_bound_farey' (p k s) (hk : 3 ≤ k) (hp : p + 1 = 2k) (hs : 1 ≤ s)
(hpow : p^s % (k+1) = k)`: `M(p,1) > k² − 2k − 1 = ⌊p/2⌋² − 2` for every odd `p = 2k−1 ≥ 5`
(no primality); instances `M(19,1) ≥ 79`, `M(23,1) ≥ 119`, `M(31,1) ≥ 223` (census `80, 120, 224`).

⚠️ **Honest status: this bound and hypothesis coincide with family I's**
(`mahler_lower_bound_family_I`, `⌊p/2⌋² − 2` when `−1 ∈ ⟨p⟩ (mod (p+3)/2)`).  The review lap's
"family I has drift 3, ratio 1/3" was wrong about the theorem actually in the repo: the
**factor 3 is family II's** (the unconditional one).  Family I's near state `N₀ = 1/D + 2/(pD)`
is exactly `1/D₁ + 1/(pD₁D₂)` with `D₁ = (p+1)/2` — family I was a two-background certificate
in disguise.  What is new is the *structure*, which generalises (below), and the weaker
hypotheses (`p ≥ 5`, any `s ≥ 1`).

### What the lap established (source: the exact SCC of `experiments/mahler_exact_M.py`,
dumped as shadow intervals at `p = 11, 13, 17, 19`; scratch `scc_dump.py`)

1. **The census optimum is a CYCLE OF BACKGROUNDS near `p/2`.**  `p = 19`: `D ∈ {10, 11}`;
   `p = 13`: `{5, 6, 7, 8}`; `p = 11`: `{4, 5, 6, 7}`; `p = 17`: `{7, 8, 9, 10}`.  Every state is
   an exact `a/D` or a pre-junction `a/D + 1/(pDD')`; there are NO offsets `b/(pD)`.
2. **General junction rule** (derived, verified on the dumps).  For coprime `D, D' < p` the
   forward junction `D → D'` leaves from `a ≡ −1/(pD') (mod D)` (state `a/D + 1/(pDD')`) and
   lands EXACTLY on `a' ≡ 1/D (mod D')`, with digit `d = (paD' + 1 − a'D)/(DD')`.  Its
   channel cost is sharp: first failure at `m = D'(p − D)`.  Far states are free (`D < p`).
3. **Orbit condition** at a background `D` with cycle-neighbours `D_prev → D → D_next`:
   `p^e ≡ −D_prev/D_next (mod D)` for some `e ≥ 0`.  A 2-cycle `{D, D'}` needs `−1 ∈ ⟨p⟩`
   at both ends unless `p ≡ −1` there; the AP chain `D−1 → D → D+1` (and back) is FREE at
   every interior vertex (`−(D−1)/(D+1) ≡ 1`).
4. **The chain theorem (paper, not yet Lean):** backgrounds `k, k+1, …, k+t` up and back
   down, `k = (p+1)/2`.  Bottom turnaround free (`p ≡ −1 (mod k)`); the ONLY condition is
   `−1 ∈ ⟨p⟩ (mod k + t)` at the top.  Costs: up `k² − (j+1)²`, down `k² − 2k − j² − 2j`;
   so **`M(p,1) > k² − 2k − t² = ⌊p/2⌋² − 1 − t²`**.  `E = p·lcm(k, …, k+t)`, `σ = 1`.
   Measured (`scratch tdist.py`): the least `t` (either direction) is `≤ 4` for 90 % of
   primes and `≤ 24` for every prime `< 20000`; `t = 1` (family I) covers 23 %.
5. **Refuted: an orbit-free cycle with `D_i = (p + r_i)/2`.**  Proof: the vertex condition
   as a rational identity is `(−r_i)^{e_i}(r_{i+1} − r_i) = r_i − r_{i−1}`; a cycle needs a
   sign flip (turnaround), which forces `(−r)^e = −1`, i.e. `r = 1`; negative `r` are traps
   (all `(−r)^e > 0`); so at most one turnaround exists and no cycle closes.  Exhaustive
   search `|r| ≤ 31`, steps `≤ 30`, length `≤ 6`: none (`scratch rcycle.py`).
6. **Closed-form 2-cycles (the handoff's item 1) are SETTLED as a per-class tool, not the
   route:** the exact periodic cover (`scratch cover.py, refine.py, mincover.py`) shows the
   family `b, b' ≤ 12`, `k ≤ 8b` covers every `p ≢ 1 (mod 12)` with modulus `13440`
   (24 triples, greedy), but the uniform floor is **`1/16`** (thin 2-adic classes such as
   `p ≡ 2549 (mod 13440)`, a genuine infinite family even with `b, b' ≤ 24`, `k ≤ 16b`),
   below family II's `1/12`; the ceiling of any drift-one 2-cycle is `1/5` (`(2,3,5)`).
   Do not write the 140 class theorems.
7. **New lead (running when the lap ended):** identity-closed 3-cycles with RATIONAL
   backgrounds `D_i = (a_i p + b_i)/c_i` exist once CRT-consistency is imposed, e.g.
   `D = (5p+7)/9, (4p+2)/9, (2p+4)/3` for `p ≡ 4 (mod 9)`, cost `min x_{i+1}(1−x_i) = 5/27
   ≈ 0.185` — UNCONDITIONAL (no orbit condition) and above `1/12`.  Unverified: needs the
   literal `NumCert.Good` check (`scratch farey_cert.py` pattern, generalised to several
   backgrounds), coprimality of consecutive `D_i`, digits `< p − 1`.  Search script
   `scratch multibg2.py A C B L num den`.

### Next attack, in order

1. **Verify the 3-cycle lead numerically** (`Good` checker with several backgrounds, walk
   closure by explicit orbit).  If real: enumerate identity cycles per residue class of `p`
   (mod `lcm` of the `c_i`) and find a covering family — that would make **`M(p,1) ≥ c p²`
   with `c ≈ 0.18` UNCONDITIONAL for every prime**, retiring the factor 3 outright.
2. **The chain theorem in Lean** (`MahlerFareyJunction.lean` generalised to `k … k+t`):
   states `(j, a)`, `E = p·lcm`, cost bookkeeping per item 4.  Turns the crux into
   "`∃ t ≤ T` with `−1 ∈ ⟨p⟩ (mod (p+1)/2 + t)`" — far weaker than `exists_prime_nonresidue`
   (composite `D` allowed, interval above `p/2`), constant `1/4 − t²/p²`.
3. Retire `mahler_lower_bound_prime_drift_one`'s route once 1 or 2 lands.


## 🎯 GRIND LAP 2026-09-08 (drift one): BOTH KEYS PROVED FROM THE ARITHMETIC — the crux is now a bare existence

**Landed** `src/NormalNumbers/MahlerDriftOne.lean` (wired; build green 8884; trust
triple on everything except the one disclosed `sorry`):

* **`mahler_lower_bound_drift_one (p D c₀ t) (h : DriftOne p D c₀ t)`**:
  `M(p,1) ≥ D(p−1)/2 − 1` (`driftBound p D`) whenever `p` odd, `D` odd `≥ 3`,
  `2D < p`, `c₂(p+1) ≡ −2 (mod D)` (drift one) and `p^t ≡ −1 (mod D)`.  **No
  per-channel `decide`**: `keyB` is proved for every `m < D(p−1)/2` by the parity
  argument (the only bad channel would be `2m = (p+1)(v+1) − D`, odd), `keyA` is
  automatic for `2D < p`, closure from `p^t ≡ −1` with `e = 4t`, `j = t+2`, and
  `hne` from `D ∤ 2`.  Measured: `Keys` fail EXACTLY at `m = D(p−1)/2`, so the bound
  is sharp for this certificate (`scratchpad keys.py`, primes `< 400`).
* `exists_c₀`: a drift-one source exists iff `gcd(D, p(p+1)) = 1`
  (`c₀ = (D−2)(p²(p+1))⁻¹`).
* Instances with no scan input: **`M(127,1) ≥ 3843`** (`0.968·⌊p/2⌋²`, `D = 61`),
  **`M(101,1) ≥ 2450`** (`0.980`, `D = 49`).
* **`mahler_lower_bound_prime_drift_one (hp : p.Prime) (h61 : 61 ≤ p)`**:
  `M(p,1) > (⌊p/3⌋+1)(p−1)/2 − 1 ≈ p²/6` — conditional on the ONE disclosed sorry
  `exists_drift_one_background`.

**The crux, now exactly stated** (`exists_drift_one_background`): *every prime
`p ≥ 61` has an odd `D` with `p/3 < D < p/2`, `gcd(D, p+1) = 1`, `−1 ∈ ⟨p⟩ (mod D)`.*
`experiments/mahler_drift_one_probe.py`: true for every prime `61 ≤ p < 4000`;
FALSE at `p = 23` (best `D = 5`) and `p = 59` (best `D = 19`) — hence the threshold.
Worst `D/p` for `p ≥ 61` in range is `0.373` (`p = 83`); for `p ≥ 200` the best `D`
is always above `0.4p`, so the true constant this route delivers is near `1/4`, but
the provable interval is what the sorry says.

**Refuted this lap (do not retry):** structural `D` from `D | p+1` — every such `D`
has `gcd(D, p+1) > 1`, which kills drift one (`c₂ = −2/(p+1)` needs `p+1` a unit);
this is the SAME degeneracy as `D = (p+1)/2`.  So `t = 1` never works; `t ≥ 2` is
forced, and `D | p^t + 1` for `t ≥ 2` has no closed-form divisor in `(p/3, p/2)`.


### Lap 2 (2026-09-08, drift one, continued): the crux is now CLASSICAL

* **Refuted: drift `−1`.**  `c₂ = −b/(p−1)` lands on `c₂` itself (closure free for
  every prime), but its trigger `w₀ = p − 1` sits INSIDE the bad zone at `v = 0`, so
  `keyB` fails at channel `(p−1)/2` for every `D` (`scratchpad neg.py`; `Keys` max
  `= (p−1)/2` at `p = 71, 101, 127`).  The sign of the drift is not symmetric: `+1`
  starts just past the zone, `−1` inside it.  Do not retry.
* **Landed in Lean:** `pow_half_mod_of_not_isSquare` (Euler's criterion in `ℕ`),
  `background_of_nonresidue`: a prime `q ∈ (p/3, p/2)`, `q ∤ p+1`, `p` a non-residue
  mod `q`, is a drift-one background with `t = q/2`.  `exists_drift_one_background` is
  now PROVED from **`exists_prime_nonresidue`** (the only `sorry`: primes `p ≥ 73`)
  plus explicit witnesses `61 → 23`, `67 → 23`, `71 → D = 29, t = 7` (`71` is the
  one prime `< 6000` with no non-residue prime in `(p/3, p/2)`; `--qnr` mode of
  `experiments/mahler_drift_one_probe.py`).
* Chain of the conditional headline `mahler_lower_bound_prime_drift_one`:
  `exists_prime_nonresidue ⟹ exists_drift_one_background ⟹ DriftOne ⟹ Keys` —
  everything past the first arrow is trust-triple.
* **Why the sorry is a wall (source-grounded):** by reciprocity `(p/q) = −1` is a
  condition on `q` modulo `4p`, and the interval `(p/3, p/2)` is SHORTER than the
  modulus; even one such prime is Linnik-strength.  The elementary substitutes
  (Burgess/Vinogradov least non-residue) give a non-residue prime of size `p^{1/4+ε}`,
  useless here because the constant is `D/p`.  A composite `D = q₁q₂` with both
  `v₂(ord_{qᵢ}(p))` equal moves the problem to primes near `√p` with a Legendre
  condition — same wall.  Mathlib has none of this analytic machinery.
* Next: either (a) accept the classical sorry as the frontier and improve the
  CONSTANT of the conditional theorem (the best `D` is `> 0.4p` for `p ≥ 200`, i.e.
  `p²/5`, and the `D > p/2` regime of keyA would give `≈ p²/4`), or (b) look for a
  closure not needing `−1 ∈ ⟨p⟩`: the offset graph `b → b'` iff `−b'/b ∈ ⟨p⟩ (mod D)`
  (drift one needs `b ∣ p+1`) — a 2-cycle `{2, 4}` needs `−2 ∈ ⟨p⟩` and `4 ∣ p+1`,
  `{2, 3}` needs `−3/2 ∈ ⟨p⟩` and `3 ∣ p+1`; more targets per `p`, same type.

## Next attack, in order

1. **[crux] `exists_drift_one_background`.**  Sufficient: a prime `q ∈ (p/3, p/2)`,
   `q ≡ 3 (mod 4)`, `(p/q) = −1` (then `p^((q−1)/2) ≡ −1`, and `q ∤ p+1`
   automatically since `q < p/2`, `q ≠ (p+1)/3`… check `3q = p+1` separately).
   Unconditionally this is a prime in a short interval with a Legendre condition —
   Linnik-strength for the analytic route.  Cheaper: allow COMPOSITE `D` and use
   the CRT: `−1 ∈ ⟨p⟩ (mod q₁q₂)` iff both orders have the same 2-adic valuation…
   the density of good `D` is positive, so a **Brun–Titchmarsh-free counting
   argument on `D ∈ (p/3, p/2)`** (count `D` with `ord_D(p)` even via characters
   of order 2 in `(ℤ/D)^×`) may be within reach: this is the thread to open next.
   Fallback that needs NO new theorem: extend the threshold check by `decide` on a
   finite range and state the theorem for `61 ≤ p ≤ N`.
2. Family I as a corollary of `mahler_lower_bound_drift_one`: `D = (p+3)/2` is
   NOT `< p/2`, so family I is the `D > p/2` regime (keyA binding) — a second
   `DriftOne'` with the `keyA` residue argument gives `M ≥ p(p−D)/2 − O(p)` there.
3. Census-matching `M(p,1) ≥ ⌊p/2⌋² − 4` on all primes (needs `D ≈ p/2` exactly).

## 🎯 REVIEW LAP 2026-09-08 (fresh-mind): the factor `3` is a DRIFT, and it is NOT intrinsic

**What the review established (all numbers from `experiments/mahler_onejunction_scan.py`,
which checks `NumCert.Good` literally — `full=True` column).**

### 1. The one-junction certificate, in closed form

Every `MahlerFamilyI`-shaped certificate is fixed by `(D, K, L, σ, c₀, b)`:

    E = p^(K+L)·D,  far state F_c: num = c·p^(K+L)  (c in the ⟨p⟩-orbit of c₀ mod D)
    near chain t = 0..K−1: num = (c₀p^(t+1) mod D)·p^(K+L) + b·p^(t+L)
    jump F_{c₀} → near(0) with δ = b·p^L        (needs δ + σ < σp)
    landing near(K−1) → F_{(c₀p^(K+1) + b) mod D}

Far states are FREE (only `D < p` and `σm < p^(K+L)`), so validity is exactly the
near chain.  Writing `c₂ = c₀p² mod D` and `bm = pv + w` (`w = bm mod p`), the two
binding conditions of the family-I shape (`K=2, L=1`) are

    (A)   m·c₁ ≡ −1 (mod D)              ⟹  b·m < p·(p−D)          [state N₋₁]
    (B)   m·c₂ + v ≡ −1 (mod D)          ⟹  w < p − D              [state N₀]

and (B) linearises: the trigger is `w ≡ w₀ + g·v (mod bD)` with

    **w₀ = −b·c₂⁻¹ (mod bD),   g = w₀ − p (mod bD)**  — the DRIFT.

The bad zone for `w` is `[p−D, p)`, of length `D`; the safe zone has length `(b−1)D`.
So the run is `≈ (b−1)D/|g|` and

    **M ≈ min( p(p−D)/b ,  p(b−1)D/(b|g|) ),   optimal at D = pg/(g+b−1),
      giving  M/⌊p/2⌋² ≈ 4(b−1)/(b(g+b−1)).**

Verified against the exhaustive scan: **every winner at every prime `17 ≤ p ≤ 127`
has drift `g = 1`**, and `M` matches `min(A,B)` to within `D`.

### 2. What the drift says about families I and II

* `g = 1` ⟺ `c₂ ≡ −b/(p+1) (mod D)`, and then the junction maps `orbit(c₂) → orbit(−c₂)`.
  Closing the cycle therefore forces **`−1 ∈ ⟨p⟩ (mod D)`** — exactly family I's
  hypothesis, now seen as *equivalent* to "drift 1", not as an artifact of `D = (p+3)/2`.
* A junction scaled by `k` (family II's second junction, `k = 3`) has its conditions at
  channel `km`, so `M` is divided by `k`, and closure needs `−k ∈ ⟨p⟩ (mod D)`.
* `g ≡ −p (mod b)`.  With `b = 2` the drift is **always odd**.
* The closed-form backgrounds `D = (p+j)/2` have `p ≡ −j (mod D)`, hence drift `j`,
  automatically — `j` odd.  `j = 1` (`D = (p+1)/2`) is **degenerate**: `w₀ = −2c₂⁻¹`
  is even while `p` is odd, so `g = w₀ − p = 1` is unreachable; the best odd `g` there is
  `3`.  `j = 3` is `D = (p+3)/2`, drift `3`, ratio `1/3`.

  ⛔ **REFUTED this lap: `1/3` is exactly the barrier of any closed-form `D = (p+j)/2`
  background with a `b = 2` junction.**  Family II's constant is not slack — it is the
  parity of the drift.  Do not look for a cleverer scaling `k`, and do not retry
  `D = (p+1)/2` with `b = 2`; `b = 3` at `D = (p+1)/2` reaches drift `2` (ratio `2/3`)
  but its closure `−c₂ + 3 ≡ ±c₂` forces `D | 9`.

### 3. What is NOT capped: free `D`

The exhaustive scan over `(D, K, L, σ, c₀, b)` gives, per prime, `M/⌊p/2⌋²` =

    p   17    19    23    29    31    37    41    43    47    53    59    61
        .969  .975  .983  .913  .991  .941  .995  .995  .996  .960  .902  .966
    p   67    71    73    79    83    89    97   101   103   107   109   113   127
        .936  .881  .944  .999  .883  .999  .999  .980  .999  .886  .981  .999  .968

**minimum `0.881`** — always `K=2, L=1, σ=4`, `b ∈ {2,3}`, `D` between `p/3` and `p/2`,
drift `1`.  So the factor `3` is an artifact of insisting on a *closed-form* background:
a per-prime `D` already reaches `0.88·⌊p/2⌋²`.

## Next attack, in order

0. ✅ **DONE (2026-09-08 grind lap): `src/NormalNumbers/MahlerBackgroundCert.lean`.**
   `mahler_lower_bound_background (p D c₀ b M e j) (h : Hyp p D b)
   (K : Keys p D c₀ b M) (C : Closure p D c₀ b e j)` — the family-I junction over
   an ARBITRARY background `1/D`, junction source `c₀` and offset `b`, slack
   `σ = 2b`.  `Hyp` is `3 ≤ p`, `0 < D`, `0 < b`, `b + D < p`; `Keys` is
   `keyA : p²·(m·c₁ mod D) + m·b < (p−1)pD`, `keyB : m(c₂p+b) mod pD < (p−1)D`
   (both `∀ m ≤ M`), plus `keyJ : bM + p²D < p³` and `keyR : 2bM < p²D`;
   `Closure` is `2 ≤ D`, `0 < e`, `j < e`, `p^e ≡ 1 (mod D)`,
   `(c₂p+b) ≡ c₀p^j (mod D)`, `c₀p^j ≢ c₀p³ (mod D)`.  Trust triple.
   Instances: **`M(29,1) ≥ 180`** (`D=11, c₀=9, b=3, e=10, j=7`; family II gave
   `65`, `⌊29/2⌋² = 196`) and **`M(71,1) ≥ 1080`** (`D=41, c₀=4, b=2, e=40,
   j=22`; family II gave `408`, `⌊71/2⌋² = 1225` — the worst ratio `0.881` of the
   whole scan).  Far states are proved free (`key_far`, `res_far`), so the two
   sharp keys are the ONLY per-instance input; `dig_far_ne` (strict monotonicity
   of `c ↦ ⌊cp/D⌋` for `D < p`) gives the walk separation at position `3`.
   *Remaining on this item*: a `Hyp`+`Keys`+`Closure`-producing lemma that turns
   family I's `D = (p+3)/2, b = 2` into an instance (so family I is literally a
   corollary), and the general `M ≥ min(p(p−D), p(b−1)D/g)/b` bound proved from
   the drift rather than checked per prime.
1. **[the new arithmetic crux] uniform drift 1.**  A uniform `M(p,1) ≥ c·p²` with
   `c > 1/12` needs: *for every prime `p` there is `D` with `p/3 < D < p/2`,
   `−1 ∈ ⟨p⟩ (mod D)` and the non-degeneracy `gcd(c₂, bD) = 1`.*  For `D = q` prime
   this is `ord_q(p)` **even**, density `17/24` (Hasse), so heuristically many `q`
   work; the open point is an unconditional existence in a short interval.  Weaker
   sufficient forms worth trying first: `q ≡ 3 (mod 4)` prime with `p` a quadratic
   non-residue mod `q`; or `D | p^t + 1` with `p/3 < D < p/2`.
2. **[fallback, unconditional]** drift `2` needs `b` odd (`g ≡ −p mod b`), i.e. `b = 3`
   with `3 | p+2`; ratio `2/3` at `D ≈ p/2`, closure `p^t ≡ −2 (mod D)`.  Measure the
   coverage of `{D = (p+j)/2, j ≤ 9} × {k ≤ 3}` before writing Lean.
3. `M(p,1) ≥ ⌊p/2⌋² − 4` exactly on all primes is the census-matching target; the
   engine (`NumCert.Good`) needs nothing new for it.

## 🎯 CRUX CLOSED: `M(p,1) > (⌊p/2⌋² − 2)/3` for EVERY prime `p ≥ 17` (2026-09-08, grind lap 2)

**Landed (trust triple, no sorry):**
* `src/NormalNumbers/MahlerNumCert.lean` — generic **numerator certificate** layer:
  an `EscapeCert` with tails `[num/E, (num+σ)/E]`, carries `⌊m·num/E⌋`; `NumCert.Good`
  (integer data: `dig < p`, `num + σ ≤ E`, per-edge `dig·E + num' = p·num + δ` with
  `δ + σ < σp` and `p·((m·num) mod E) + mδ < (p−1)E`, per-state `(m·num) mod E + σm < E`)
  ⟹ `Valid M [p−1]`; no edge is `hi`-extremal (`not_hiMax_of_edge`);
  `EscapeCert.isClosedWalk_periodic`.
* `MahlerFamilyI.lean` refactored onto it; base hypothesis is now `Hyp p e`
  (`p` odd `≥ 17`, `p^e ≡ 1 (mod D)`, `e ≥ 2`) and the `−1` condition (`HypI`) is
  only on the family-I walk.
* **`MahlerFamilyII.lean`** — the two-junction cycle `1 →(1,2) −1 ⇝ 3c₋₂ →(3,6) −3 ⇝ c₋₂`:
  junction 2 is the family-I junction scaled by 3 (`T₀' = 3/D + 6/(pD)`, digit `5`,
  `δ = 6p`, slack `8/E`), so its digit conditions are the family-I keys at channel `3m`
  (`res_nm1'`).  `mahler_lower_bound_family_II (h : Hyp p e) (he : 3 ≤ e)`: bound
  `(n² − 2)/3`, `n = ⌊p/2⌋`.  **`mahler_lower_bound_prime_family_II (hp : p.Prime)
  (h17 : 17 ≤ p)`**: `e = 3·φ(D)` by Euler — the uniform `M(p,1) ≥ p²/12 − O(p)` on all
  primes `≥ 17`, no per-prime input.  Instance `M(29,1) ≥ 65` (family I does not apply
  at 29).
* Measured (`experiments/mahler_two_junction_scan.py`): the exact two-junction bottleneck
  over `1/D` at the uncovered primes is `0.33 … 0.68 · Q²`, always with the `(3,6)` edge;
  so `1/3` is the natural constant of this construction, not an artifact of the `3m` reuse.

**State of the Mahler crux.**  Upper: `M(p,1) ≤ (p²+6p+1)/4` (`MahlerQuarter.lean`).
Lower, uniform: `M(p,1) ≥ ⌊p/2⌋²/3 − 1` all primes `≥ 17`; `≥ ⌊p/2⌋² − 1` when
`−1 ∈ ⟨−3⟩ (mod (p+3)/2)` (29 % of primes).  Census says `M(p,1) = ⌊p/2⌋² − {0,1,4}`.
The gap on the general prime is the factor `3`.

**Next attack (closing the factor 3 on the complementary primes), in order.**
0. A junction from the coset of `−1` back to the coset of `1` with bottleneck `≈ Q²`
   rather than `Q²/3`: scan `(c, j)` pairs with `c ∈ −⟨−3⟩` and `(cp + j) mod D ∈ ⟨−3⟩`
   for the max safe `M` (generalize `mahler_two_junction_scan.py` to report the best
   return edge per prime, not just the bottleneck).  The scan's non-`(3,6)` winners
   (`(17,3)` at 59: `0.665`; `(3,3)` at 67: `0.675`; `(11,4)` at 73: `0.514`) suggest
   `j = 3, 4` junctions from other residues reach `2/3·Q²`; find the uniform pattern.
1. Different backgrounds `1/D'` for the complementary primes (a `D'` with `−1 ∈ ⟨p⟩`
   mod `D'`): the one-junction template gives `Q² − O(Q)` whenever the orbit closes;
   the family-I file is written so only `num`/`dig`/keys/walks change.
2. `M(p,1) ≥ ⌊p/2⌋² − 4` exactly on all primes is the census-matching target; the
   engine (`NumCert.Good`) needs nothing new for it.

## 🎯 CRUX: family I is a THEOREM — `M(p,1) > ⌊p/2⌋² − 2` uniformly (2026-09-08, grind lap)

**Landed: `src/NormalNumbers/MahlerFamilyI.lean` (new, trust triple, no sorry).**

* `mahler_lower_bound_family_I (p k) (h : Hyp p k)`: for every odd `p ≥ 17`
  (**primality is not used**) and every `k` with `p^k ≡ −1 (mod D)`,
  `D = (p+3)/2`, there is an irrational `α` with no digit `p−1` in `m·α` for
  all `1 ≤ m ≤ ⌊p/2⌋² − 2`.  That is `M(p,1) ≥ ⌊p/2⌋² − 1`, matching the exact
  census to within `1`–`2` at every such prime.  `mahler_lower_bound_prime_family_I`
  is the prime-facing form with hypothesis `∃ k, p^k % ((p+3)/2) = (p+3)/2 − 1`.
* Instances by `decide` on the hypothesis: `M(41,1) ≥ 399` (new) and
  `M(199,1) ≥ 9799` (`199⁵⁰ ≡ −1 mod 101`).
* The certificate: states `Fin (D+2)` = all far residues `F_c` (tail
  `[c/D, c/D + 4/(p³D)]`, digit `⌊cp/D⌋`) + `N₋₁` + `N₀`; ONE junction edge
  `F_{c₋₂} → N₋₁` with `c₋₂ = p^(2k−2) mod D`.  Every interval has the same
  slack `4/E`, `E = p³D`, so `lo = num/E`, `hi = (num+4)/E`, carries are
  `⌊m·num/E⌋`, and every edge satisfies `dig·E + num' = p·num + δ`,
  `δ ∈ {0, 2p}` (`edge_data`).  Validity reduces to four residue
  inequalities `p·((m·num) mod E) + mδ < (p−1)E`:
  `key_far` (all `m`, needs only `D < p`), `key_junction` (`2m < p²`),
  `key_n0` (`m ≠ Dn`, via `m = Du + r` and a two-case `ℤ`-mod computation),
  `key_nm1` (the sharp one: fails iff `m ≡ 3 (mod D)` and `⌊m/D⌋ = n − 2`,
  i.e. `m = n² − 1` — hence `n² − 2`).  No edge is `hi`-extremal, so mixing
  is free; the witness pair is the junction walk (period `3k+1`, repeated
  `2k` times) against the far cycle (period `2k`), differing at position 3
  (`p − 2` vs `p − 6`).
* `experiments/mahler_family_I_cert_check.py` evaluates exactly this
  certificate; valid at `n² − 2` and failing at `n² − 1` on `N₋₁ → N₀` for
  all 33 odd `p ≤ 259` with the hypothesis.

**What is still open — the general prime lower bound.**  Family I covers the
primes with `−1 ∈ ⟨−3⟩ ⊂ (ℤ/D)^×` (29 % of primes below 2000).  For the rest
the far cycle from `1` never reaches `D − 1`, so the `N₀ → F_{D−1}` landing
is off-orbit and a second junction is needed to return.  Next attack, in order:
0. **Two-junction closure for the remaining primes.**  In the orbit graph of
   `c ↦ −3c` the cosets of `⟨−3⟩` are the components; family I is the
   junction `T₀ = 1/D + 2/(pD)`, digit `1`, landing on `−1`.  Search
   (`experiments/mahler_junction_cert.py`, generalized to two junctions) for a
   junction from the coset of `−1` back to the coset of `1`, or a junction
   `c → c'` within a coset that lands on the coset of `1` — the certificate
   engine already handles any finite set of near states.  Target `c ≥ 1/4 − ε`
   uniformly; anything `≥ 1/8` uniform on ALL primes is the headline.
1. Alternatively a different background denominator `D' ∈ {Q, Q+1, Q+3, …}`
   whose dynamics `c ↦ (p mod D')c` has `−1` in the orbit of `1` for the
   complementary primes; then the same one-junction template
   (`MahlerFamilyI.lean` is written so that only `num`, `dig`, the keys and
   the walks change).
2. Upper side is done (`MahlerQuarter.lean`).  Nothing else on the Mahler
   crux is cheaper than 0/1.

## 🎯 CRUX: Law 2 PROVED, every position is now an affine congruence + carry (2026-09-08, grind lap)

**Landed: `src/NormalNumbers/MahlerBurstCarry.lean` (new, trust triple).**

1. **Carry normalization** (`carryG`, `digit_of_carry`): for ANY integer-coefficient
   expansion `N = Σ_{j<D} F_j g^j` (negative or oversized `F_j` allowed), digit
   `i < D` of `N` is `G_i mod g` with `G_0 = F_0`, `G_{j+1} = F_{j+1} + ⌊G_j/g⌋`.
2. **The family, position by position** (`bgDigit_family`): for odd `g`,
   `Q = (g−1)/2`, `r = m mod Q`, and a burst written with ANY integer digits
   `B = Σ e_j g^j`, the adder digit at position `i` is `G_i mod g` with
   `F_j = 2r + e_j m`.  Since `e_j m = e_j(Qu + r)` and `2Q = g − 1`, every
   position is an **affine form in `(u, r)` plus a bounded carry**, uniformly
   in `g`.  This is the tower from the review lap made exact and Lean-checked;
   there is no more "window form" or `decide` in the way of a uniform proof.
3. **Law 2 proved** (`bgDigit_one_ne`): `B ≡ −4 (mod g²)` ⟹ position `1` is
   safe for every `m < Q²` (digits `(−4, 0, ℓ)`: `G_1 = 2r − 2u − [u<r] ∈ (−g, g)`,
   never `−1` by parity, never `2Q` by size).  With `bgDigit_zero_ne` that is
   the two-position uniform law the DIRECTIVE asked for.

**Structure now visible in the exact recursion (paper, this lap).**  With signed
EVEN digits `B = Σ 2e_j g^j` the forms are
`G_j = (2 + 2e_j) r + (e_{j−1} − e_j) u + ⌊G_{j−1}/g⌋`.  Position `1` admits
exactly two safe continuations of `e_0 = −2`: `e_1 = −2` (the `g`-adic ideal
`B = 2/Q`, all positions safe for ALL `m` but never terminating) and `e_1 = 0`
(Law 2), which is **self-similar**: `B = g²ℓ − 4` reduces to the same problem
for `ℓ` with the twist `−[u > r]`, so iterating `−4, 0, −4, 0, …` only
postpones the top.  The top digit is the whole difficulty: a positive top
`ℓ_K` with `ℓ_K ≢ −4 (mod g)` gives a form with `u`-coefficient `−ℓ_K/2` and
`r`-coefficient `2 + ℓ_K`, whose zero line crosses the box unless `ℓ_K` scales
with `Q` (then `⌊G/g⌋` is itself affine — the "floors break affinity" wall).

**Measured this lap (`experiments/mahler_burst_len_scan.py`,
`mahler_signed_digit_tower.py`).**
- Bursts of ≤ 3 base-`p` digits (exact DFS, frontier cap 20000): `M/Q²` =
  `.94 .69 .67 .98 .50 .63 .36 .42 .36 .41 .31 .57 .33` at `p = 13 … 61`.
  ≥ `0.30` throughout but drifting DOWN with `p`; ≤ 2 digits: `.20` at `p = 61`.
  ⚠️ The DIRECTIVE's "terminate at length 3" route is probably capped — the
  extremal length grows (`2 … 6`).
- Fixed small signed digits `(e_0, e_1[, e_2])` with `|e| ≤ 6`: best min `c`
  over `p ≤ 60` is `0.058`, decaying like `1/p`.  Confirms: the top digit must
  scale with `Q`.  Digits from `{small} ∪ {±Q + small, ±2Q + small}` at
  length 2, target `c = 0.3`: no pattern common to all primes `11 … 47`.

**⛔ Refuted later the same lap (do not retry; scripts in `scratch/` were not kept,
the evaluators are `experiments/mahler_signed_digit_tower.py` and the `finish`
of `mahler_burst_tower.py`).**
- **Three digits with a small top** (`B = t p² + d₁ p + (p−4)`, `t ≤ 12`, every
  `d₁`): at target `c = 1/8` the solution set thins to `0` by `p = 97`
  (`89, 88, 75, … , 3, 3, 0, 1, 3, 2, 1` hits at `p = 11 … 109`).  The extremal
  tops `4, 5, 9` are real but the middle digit has no closed form and the
  family dies.  Burst LENGTH must grow with `p`.
- **The `u`-killing family** `B = (2 + p^K(Qt + λ₀))/Q`, `t = 2λ₀ S_L`, which
  makes every position above `K` a condition on `r` alone: `λ₀ ≡ −2 (mod Q)` is
  FORCED because `p ≡ 1 (mod Q)` (so `−2p^{−K} ≡ −2`), the junk at level `K` is
  `⌊(Q−2)m/Q⌋ ≈ m`, and `M ≈ 3Q` (measured `p ≤ 67`).  This is the handoff's
  `λ ≡ −2 (mod Q)` seen from the other side.
- **Repunit quotients** `B = t S_{kQ}/Q` (so `QB = t S_{kQ}` has constant digits
  and the `u`-part of `X = r(2S+B) + u(QB)` is trivial): fails at `m = Q + 1`,
  `M = Q` exactly, because `B = S_j/Q`'s own digits are those of `−1/Q²`.
- **Two-shadow cycles** `1/Q ↗ 1/(Q−1) ↘ 1/Q` with bursts `B ≤ 3`: `M ≤ 2Q`.

**Structural fact found (paper, worth a Lean statement later).**  A junction
`ρ → ρ + δ` with `0 < δ < 1/M` (a "tiny ascent") is safe for EVERY `m ≤ M`
with denominators `< p`: `m·δ < 1` adds at most a carry, and every `j/D` with
`D < p` has all digits `≤ p − 2`.  In particular `1/Q → 1/(Q−1)` is safe up to
`M = Q(Q−1) − 1` — full strength, one-line proof.  But shadows live in
`[0, 1 − 1/p)` and there are finitely many with denominator `< p`, so an
infinite bad orbit cannot ascend forever; a tiny DESCENT is fatal at every
`m ≡ 0 (mod D)` (`m·ρ` integral, borrow yields `(p−1)(p−1)…`).  Hence **bursts
(integer parts `⌊m·(ρ' − ρ + B)⌋ ≠ 0`) are intrinsic to any bad orbit** — the
top-digit problem is not an artifact of the burst family.

**🎯 FOUND (same lap, later): a ONE-JUNCTION uniform construction reaching
`M = ⌊p/2⌋² − 2` — family I.**  Background `1/D` with `D = (p+3)/2 = Q+2`
(so `p ≡ −3 (mod D)` and the digit dynamics is `c ↦ −3c`), a single junction
digit `1` at the tail `T₀ = 1/D + 2/(pD) = (p+2)/(pD)`, landing exactly on the
periodic tail `(D−1)/D`.  Exact check (`experiments/mahler_family_I_check.py`,
the `max_M` of `mahler_junction_cert.py`): `M = Q² − 2` at EVERY prime
`17 ≤ p ≤ 199` where the cycle closes, i.e. where `−1 ∈ ⟨−3⟩ ⊂ (ℤ/D)^×`
(then the periodic dynamics brings `(D−1)/D` back to `1/D` for free, so ONE
ascent per cycle suffices — this is the trick the burst family lacks).  That is
`29 %` of primes below `2000` (`88` of `299`).  The "mirror" junction `(D−3 → 3, J = p−2)` is
the same orbit one step later.  Why `Q² − 2` exactly: the depth-1 tail
`T₋₁ = c₋₁/D + 2/(p²D)` (`c₋₁ = (−3)⁻¹ mod D`) fails first at the `m ≡ 3 (mod D)`
with `m ≥ Q² − Q/2`, and `Q² ≡ 4 (mod D)` puts that at `m = Q² − 1`.
The construction is a **finite escape certificate** (`AdderEscapeCert.lean`):
far states `[c/D, c/D + 2/(p³D)]` for `c` in the orbit (carry pinning needs
only `m ≤ p³/2`), two exact near states `T₋₁, T₀`, junction edge `T₀ → (D−1)/D`
with digit `1`; the far edges are non-`HiMax` so `Mixing` holds.  A uniform
Lean theorem `M(p,1) ≥ ⌊p/2⌋² − 2` for every prime with `−1 ∈ ⟨−3⟩ (mod (p+3)/2)`
is therefore a symbolic `EscapeCert.Valid` proof: (i) far-state digits are safe
because `D < p`; (ii) three explicit inequalities in `m mod D`, `⌊m/D⌋` for
`m ≤ Q² − 2`.

**Second strong junction, `D = Q`: the wrap** `(Q−1)/Q → 1/Q`, digit `p−2`
(`T₀ = (Q−1)/Q + 2/(Qp)`, an ascent by `2/Q` through `1`): `M = Q² − 1` at every
prime `29 … 73`.  But `p ≡ 1 (mod Q)`, the dynamics is trivial, and the RETURN
`1/Q → (Q−1)/Q` is the burst problem again: best two-digit return decays
(`.92 .94 .97 .67 .98 .35 .99 .36 .49 .36 .47 .30 1.00 .23 .20 .19 .23 .22` at
`p = 11 … 79`).  Generic `+2` ascents `c → c+2` on `D = Q` are `O(Q)`.
No closed one-junction cycle exists at any `D ∈ [Q−4, Q+6]` for
`p = 29, 37, 53, 61, 67, 71, 73` (`experiments/mahler_closed_cycle_scan.py`).

**Next attack, in order (revised after family I).**
0. **Formalize family I** as a symbolic `EscapeCert` and prove `Valid` uniformly:
   `M(p,1) ≥ ⌊p/2⌋² − 2` for all primes with `−1 ∈ ⟨−3⟩ (mod (p+3)/2)`.  This is
   the first uniform-in-`p` quadratic lower bound and matches the census to
   within `2`.  Then hunt the closing cycle for the other primes: a junction
   from the coset of `−1` back to the coset of `1` (`k = 2, 3` digits, or a
   detour through `D = Q` / `D = Q+1` states via tiny ascents).
1. (superseded unless 0 stalls) Work the exact burst recursion at the top with `ℓ_K = αQ + β`.  Now that
   `bgDigit_family` is a theorem, a uniform certificate is a finite list of
   affine-form case analyses (`omega` after `ediv_small`-style floor
   evaluations).  Find, by computer, a top digit of the form `αQ + β` (small
   rational `α`, allowing a parity-of-`u` split) with a length-3 or -4 signed
   tower that holds `c ≥ 1/8` on all primes `7 … 200`; then transcribe.
2. If no such closed form exists, the **generalized junction certificate**
   (`experiments/mahler_junction_cert.py`) — the census extremal mixes shadows of
   denominators `Q−1 … Q+2`; the burst family is the single-shadow special case.
3. A uniform bound weaker than quadratic is NOT the goal; do not settle for
   `M(p,1) ≥ c·p` (already known from the per-prime table).

## 🎯 CRUX: the prime lower side reformulated — `B ≡ −4 (mod p)` PROVED uniform (2026-09-08, review lap)

The DIRECTIVE crux is a **general** prime lower bound `M(p,1) ≥ c·p²`.  This lap
reformulated the family, extracted two uniform laws (one now a Lean theorem),
refuted the closed forms they suggest, and settled the route question with data.

**The reformulation (this is the working frame from now on).**  For the family
`α = 2/(p−1) + B·Σ p^(−i!)`, target digit `W = p−1`, `Q = (p−1)/2`, write
`m = uQ + r`, `r = m mod Q`.  The background digit of `m·α` is `2r`, and the
certificate condition is *exactly*

    for all k ≥ 1:  { r/Q + m·B / p^k }  <  1 − 1/p                         (★)

equivalently: the **p-adic** integer `Z_m = mB − r/Q` has no base-`p` digit
equal to `p−1`.  `−r/Q` is the constant string `2r 2r 2r …`, so (★) is a school
long addition: constant background `+` burst, one condition per digit position.
Formalized this lap as `MahlerBurstDigit.lean` (`bgCarry`, `bgDigit`,
`bgResidue_div_eq_bgDigit`, `mahler_lower_bound_bg_adder`) — the window form
`hdig` over distances `d` and the adder form over positions `i` are the same
statement, and `hstab` is no longer needed (the carry dies when the burst runs
out).  **This is the form in which a uniform-in-`p` proof is possible;** the
window form re-derives the whole addition for each `d`.

**Law 1 (position 0), PROVED uniformly: `B ≡ −4 (mod p)`.**  Then
`2r + mB ≡ 2r − 4m ≡ 2(u − r) (mod p)`, and `2(u−r) ≡ −1 (mod p)` forces
`p ∣ 2(u−r)+1`, an odd number of size `≤ 2Q−1 = p−2`.  So position `0` is
**safe for every `m < Q²`** — and `Q² = ⌊p/2⌋²` is exactly the census value.
Lean: `bgDigit_zero_ne` (trust triple).  Empirical confirmation: the lowest
base-`p` digit of the extremal burst is `p−4` at **every** prime `7 … 59`
(exact digit-DFS, `experiments/mahler_burst_tower.py`).

**Law 2 (position 1): `λ ≡ −2 (mod p)`, where `QB = p·λ + 2`.**  The
position-1 failure locus is an arithmetic progression in `r`,
`u ≡ 2r(1 + λ⁻¹) − c₁λ⁻¹ (mod p)` with `c₁ = [u ≥ r]`; the difference is
`d = 2(1+λ⁻¹)`, and `λ ≡ −2` makes `d = 1` while the carry shifts the constant
by `Q`, so every failure sits at `u = r + Q + 1 > Q`.  Confirmed exactly: the
best `B` at `p = 7, 11, 13, 17, 19, 23` has `λ mod p = p−2` in every case.
This **explains and refines the previously recorded `κ ≡ −8/3 (mod p)` law**
(same law, different normalization: `κ = 2ℓ` at level 2, see below).

**The tower, and why there is no closed form.**  Integrality forces
`λ ≡ −2 (mod Q)` too, hence `λ = pQℓ − 2`, and then
`I = λu + ⌊λr/Q⌋ = pℓm − (2u + 1 + [2r>Q])`: the level-2 integer is `ℓm − 1`.
So each base-`p` digit of `B` is a new parameter pinned `mod p` by that level's
condition — a genuine recursion, not a formula.  Level 2 gives coefficient
`2 + 4/ℓ`, safe iff `≡ ±1 (mod p)`, i.e. `ℓ ≡ −4` or `ℓ ≡ −4/3 (mod p)`.
Beyond level 2 the floors `⌊λr/Q⌋` break affinity: the third digit of the
extremal `B` is `5, 2, 4, 17, 16` at `p = 13, 17, 23, 31, 59` — no pattern.

**⛔ REFUTED this lap (do not retry).**  The closed forms the two laws suggest,
`B = p²−4` (`ℓ=1`) and `B = p²(p−4)−4` (`ℓ = p−4`), and the whole shape
`B = p^K(p−c) − 4`: all only `Θ(p)`, killed by the higher digits of `I`
(measured `M` for `B = p²−4`: `13, 3, 22, 5, 31, 40, 9, …` at `p = 11 … 37`).

**✅ ROUTE SETTLED: the single-burst family IS uniformly quadratic.**  Exact
digit-DFS (build `B` low digit first; digit `i` of `mB` depends only on
`B mod p^(i+1)`, so pruning is exact) gives, for `M/Q²`:

    p    7    11   13   17   19   23   29   31   37   41   43   47   53   59
    M/Q² .78  .92  .94  .97  .58  .98  .71  .99  .61  .44  .52  .44  .44 1.00

never below `0.43` — i.e. `M(p,1) ≥ 0.43·⌊p/2⌋² ≈ p²/9.3` on all data.  The
obstruction to the theorem is **a formula for `B`, not existence**.  (Lengths:
the extremal `B` needs `2 … 6` base-`p` digits, non-monotone in `p`.)

**New certificate this lap**: `mahler_lower_bound_base29` — `M(29,1) ≥ 140`
(`B = 3273893`, adder form, `decide +kernel`), first use of the new engine.

**Next attack, in order.**
1. **Prove Law 2 in Lean** (`bgDigit_one_ne`): position `1` is safe for all
   `m < Q²` whenever `QB ≡ 2 (mod p²)` and `λ ≡ −2 (mod p)`.  Combined with
   `bgDigit_zero_ne` that is a *two-position* uniform theorem; with a burst of
   **exactly three** base-`p` digits the tower terminates and positions `≥ 3`
   are the `bgDigit_of_lt` tail — i.e. a genuine uniform `M(p,1) ≥ c·p²`.
   The open question is which `c` a 3-digit burst can reach: measure it
   (`mahler_burst_tower.py` restricted to length 3) before writing Lean.
2. The **generalized junction model** (`experiments/mahler_junction_cert.py`)
   if (1) caps out: background = ANY rational `c/D` with `D < p` (only `D < p`
   is needed — `D ∤ p−1` is fine), certificate `(D, c₀, c_k, junction word)`.
   Sound (never exceeds the census; attains it exactly at `p = 13`).
   ⚠️ Two traps found: `Δ = T₀ − c₀/D` must be `> 0` (approach the background
   from ABOVE — from below, every `m` with `D ∣ m c` is fatal at deep levels);
   and using two DIFFERENT backgrounds is UNSOUND unless the *return* junction
   is certified too (that bug produced `M` values above the census).


## 🔬 PRIME LOWER SIDE: the burst family's structure, and why it is not uniform (2026-09-08, autonomous, lap 3)

Target: a general prime lower bound `M(p,1) ≥ p²/4 − O(p)` (the missing half
of the DIRECTIVE crux; upper side `(p²+6p+1)/4` is proved).  This lap
reverse-engineered the census witnesses (`experiments/mahler_bg_burst_structure.py`
and scratch scans over `B < p³`, then over `B = p²κ − 4p − 4`, `κ < p²`).

**Structure (all `a = 2`, target `W = p − 1`, `Q = (p−1)/2`, `m = uQ + r`).**
Every extremal burst has the shape

    B = p^j·κ − 4·S_j          (S_j = 1 + p + ⋯ + p^(j−1)),   i.e. B ≡ −4 (mod p),

and the digit sums of `X = 2r·S_D + m·B` are then FORCED:
position 0 is `2(u − r)` (mod `p`), positions `1 … j−1` are `p − 2r − 1`
(or `0` when `r = 0`), and the top is `2r·S + κ·m − 2u − [r ≥ 1]`.
The affine principle behind it: a digit sum of the form `2(u − r) + c`
(`c` even, `O(1)`) avoids `p − 1` on the whole box `u, r < Q` except at
`u − r = Q − c/2`, i.e. `m ≈ Q²`; any form with `u`-coefficient `≥ 3` or odd
`c` fails at `m = O(p)`.  Requiring the top digit to be affine in `(u, r)`
with small `u`-coefficient forces `κ ≡ −4 (mod p)` again — the recursion
`κ = pκ' − 4` just increases `j` — so the top `κ` must be a genuine integer
`≥ 1` whose multiples `κ·m` are added into the `2r` background, and its
`u`-coefficient `Qκ ≈ pκ/2` sweeps residues.  There is no uniform `κ`:

    p     11   13   17   23   31   | 19, 29 (κ < p²)
    κ      1    6   88    5  142   | best 55/81, 69/196 — family fails
    M ≥   24   35   63  120  224   | census 25 35 64 120 224

New certificates this lap (`MahlerPrimeLowerBound.lean`, trust triple):
`mahler_lower_bound_base17` (`≥ 63`), `mahler_lower_bound_base31` (`≥ 224`,
exact).  Exact SCC at `p = 13` (`scratch scc_prime.py`): the live automaton
shadows `1/6, 5/6, 5/8, 6/7, 3/5` — denominators `Q−1 … Q+2` — and mixes them;
at `p = 19, 29` the extremal orbit is presumably such a mixture, not a burst.

**Refuted sub-approaches (do not retry):** `B = 2S_j` and all `B ≤ 2p+1`
(linear, junction digit `2r + u`); `B = (p^j K' + 1)/Q` (pushes `u` to the
bottom digit but leaves `2rS + κm − u` on top, same obstruction);
one-parameter recursions `κ = pλ − c` for `c ≠ 2`.

**The `κ` law (lap 4).**  At every prime where the family is exact,
`κ ≡ −8/3 (mod p)`, i.e. `κ₀ = (p−8)/3` or `(2p−8)/3` plus `λp`: it makes the
position-`j` digit sum `c(u + r) − [r≥1]` with `c ≡ −2/3` invertible, which
cannot be `≡ −1` for `u + r < p`.  The next position carries the floors
`⌊κ₀ m/p⌋`, and there the law is not enough: scanning `λ ≤ 5` for
`11 ≤ p ≤ 257` the ratio `m*/p²` is `≈ 0.2` only at `11, 13, 23, 31, 59`
(`λ = 0, 0, 0, 4, 4`) and decays to `< 0.01` elsewhere (scratch `law.py`).
So the `j = 2` burst family is NOT uniformly quadratic — the exact witness at
a general prime needs longer bursts or automaton mixing.  Banked: `M(59,1) ≥
840 = ⌊59/2⌋² − 1` (`mahler_lower_bound_base59`), the first data point beyond
the census, consistent with Finding 2's `⌊p/2⌋² − {0,1,4}`.

**Period-2 backgrounds (lap 5).**  The `p = 19` extremal automaton (digit
`0`/`18`, scratch `scc19.py`) shadows `9/10 = 1/(Q+1)` — a PERIOD-2 background
`(17,1)` whose multiples `(2r−1, p−2r)` never contain `p − 1` — with a 4-digit
excursion word.  The `1/(Q+1)` burst family (background `2(p−1)/(p²−1)`, burst
`B` in base `p²`) is exact at `19` (`80`) and matches `1/Q` at `11, 13, 17`.
Formalized with NO new engine (`MahlerLowerBoundPeriod2.lean`): a period-2
background is a single-digit background in base `g²`, and `digitOf_pow_digitAt`
(Pillai) transports "digit `W` in base `g`" to "a base-`g²` digit with a half
equal to `W`".  `mahler_lower_bound_bg2_digit` is the general certificate;
`mahler_lower_bound_base19 : M(19,1) ≥ 80` (exact).  So the prime table is now
exact at `5, 7, 13, 19, 23, 31` and one short at `11, 17`; `59 ≥ 840`.
The general prime witness thus needs at least the pair of backgrounds
`1/Q`, `1/(Q+1)` — which is precisely the two-shadow mixing of (a).

**Escape engine COMPLETE as a general theorem (lap 6).**
`AdderEscapeCert.lean`: `EscapeCert g` (states, digits, successor lists,
rational tail intervals `[lo, hi]`, per-channel carries), `Valid C M w`
(decidable), and `escape_mahler_lower_bound`: a valid certificate plus a
`WitnessPair` (two equal-length closed walks from a common state, each with a
digit `≠ g−1` and an internal non-`hi`-extremal edge, differing in a digit)
gives an irrational `α` with block `w` NEVER occurring in `m·α` for
`1 ≤ m ≤ M`.  Bricks: `tail_mem` (closed intervals, limit of the
`g^(−k)`-approximations), `tail_lt_hi` (strictness from one non-extremal
later edge — this is what excludes the rational endpoints where `m·x` is an
integer), `carry_eq`, `digit_mul_eq`, `not_occursAt_of_path`, mixing by
`Set ℕ` and irrationality by cardinality.  Trust triple.
**Next brick**: the `(7,2)` instance — generate the 10-state certificate
(`experiments/mahler_scc_cycles.py 7 2 175 00`), intervals as the SCC's
least/greatest fixed points (rationals), carries per channel, a witness pair
from the cycles `15·15` and `5412`; `decide +kernel` on `Valid` and
`WitnessPair`.  The same engine gives EXACT `k = 1` values at `p = 11, 17`
(where bursts are one short) — and at any prime, from its SCC.

**Next attack.**  (a) Two-shadow mixing as a PROVABLE family: `α` whose
orbit alternates blocks of `r/Q` and `r'/(Q+1)` expansions; the transition
digit sums need the affine principle with both residues.  Instrument first:
extract the `p = 19` SCC cycles and their rationals.  (b) Weaker but uniform:
any `M(p,1) ≥ c·p²` for a fixed `c > 0` would already settle "prime bases are
quadratic"; try `Q' ≈ p/4` backgrounds (`a = 4`) where the box is
`u, r < Q'` and the failure `u − r = Q'` sits at `m ≈ Q'² = p²/16`.

## ✅ THE UNIVERSAL CONSTANT IS `1` — `sup_g M(g,k)/g^(k+1) = 1`, in Lean (2026-09-08, autonomous, lap 2)

`MahlerLowerBoundSmooth.lean` (new, trust triple, `#print axioms` checked on
all four headlines).  The host doc `docs/mahler-universal-constant-is-one-2026-09-07.md`
found numerically that the `a = 0` burst family with `B = c`, `t·c = g^j`,
`t < g` gives `M(g,1) ≥ (g−1)t`; this lap proves it for every `k`:

    mahler_lower_bound_smooth :  t ∣ g^j, t < g  ⟹  M(g,k) ≥ t·(gᵏ − 1)

The arithmetic is two lemmas.  `digit_le_of_smooth`: with `t c = g^j`, every
digit `i < j` of `r·c` (ANY `r`) is `≤ g − 2`, because
`⌊r c/gⁱ⌋ mod g = ⌊v g/t⌋` with `v = (r g^(j−i−1)) mod t ≤ t − 1`, and
`(t−1)g < (g−1)t ⟺ t < g`.  `avoid_of_split`: if `N = e + q g^j` with all
low digits of `e` `≤ g − 2` and `q ≤ gᵏ − 2`, the `k`-digit window at any
position `d − k` is `≤ gᵏ − 2` (below `j` it contains a digit of `e`; at or
above `j` it is a window of `q`).  Then `mahler_lower_bound_general` does the
rest, exactly as the divisor bound (`j = 1`).

Instances (`decide` on `625 ∣ 630⁴`, `26244 ∣ 26250⁸`):
`M(630,1) ≥ 393125 = 0.9905·630²`, `M(26250,1) ≥ 688878756 = 0.99973·26250²`.

Sharpness (`mahler_constant_one_sharp`): for every `k ≥ 1`, `ε > 0`, `L`,
some `g ≥ L` has `M(g,k) ≥ (1 − ε) g^(k+1)`.  Proof: Dirichlet
(`Real.exists_int_int_abs_mul_sub_le` on `log 3/log 2`) gives `2^a`, `3^b`
within a factor `e^δ`; `g = 2^a 3^b L`, `t = min(2^a,3^b)² L` has `t ∣ g²`,
`t < g` (`2^a ≠ 3^b` by parity), `t ≥ (1−δ)g`; and
`t(gᵏ−1) ≥ (1−δ)²g^(k+1) ≥ (1−2δ)g^(k+1)` once `δ g ≥ 1`.  The scale factor
`L` is what makes the base arbitrarily large at a fixed ratio.

Against `mahler_multiplier_lt` (`M(g,k) < g^(k+1)`): the constant `1` cannot
be lowered, for any `k`.  The "sharp universal constant" wing is closed.

### What remains on the Mahler thread (in order of value)
1. **Prime bases** (the DIRECTIVE's crux): `M(p,1) ≤ (p²+6p+1)/4` is proved
   (`MahlerQuarter.lean`), census says `M(p,1) ≈ ⌊p/2⌋²`; lower side at primes
   is `MahlerPrimeLowerBound` (exact at `5, 7, 13, 23`).  Open: a general
   prime lower bound `M(p,1) ≥ p²/4 − O(p)`.  The census witnesses (`a ≠ 0`
   background) are the family; what is missing is the general `t`-like
   parameter.  Conjecture from the data: `a = (p−1)/2` background,
   `B = (p+1)/2`-type burst — check `experiments/mahler_exact_M.py` witnesses.
2. **`k ≥ 2` lower side** via the escape engine (`AdderEscape.lean`, plan in
   the section below): `M(7,2) ≥ 176`.
3. The rate `1 − M(g,1)/g²` for composite `g` (Størmer-type); and the bases
   `21, 27, 28, 32` where the burst family is beaten — the construction is
   unidentified.

## 🔬 THE `(7,2)` EXTREMAL ORBIT, DISSECTED — and the escape engine started (2026-09-08, autonomous)

`experiments/mahler_scc_cycles.py 7 2 175 00` pulls the surviving SCC of the
adder machine (10 states) and its simple cycles; `mahler_scc_mix_test.py`
random-walks it and checks all `m ≤ 175` exactly on a 3000-digit prefix.

* **The language.**  Three cycles, as digit words: `15` (the point `1/4`,
  `0.(15)₇`; and `3/4 = 0.(51)₇`), `5412` (`4/5 = 0.(5412)₇`), and
  `541251512`.  Any mixing of them escapes `00` for every `m ≤ 175` — the
  numeric check passed on 3000 digits, so the instrument's `M(7,2) = 176` is
  sound and a genuine irrational witness exists (aperiodic mixing).
* **The anatomy = the drop mechanism verbatim.**  On the period-9 point
  `x = 0.(541251512)₇` the canonical shadow denominators are
  `5,5,5,28,4,4,35,5,5`: the orbit hovers at `4/5` and `3/4` and moves between
  them through `28 = 7·4` and `35 = 7·5` — a jump to `g·d'` followed by a DROP
  to `d'`.  Both jump estimates of `MahlerFarey` are tight there
  (`1/(7E) = 28`, `35` exactly).  And `176` is the first `m` with `00` in
  `m·x`: the periodic point is itself the exact witness.
* **What the sign structure does.**  At tails near `1/4` the true carry of
  `4·α` depends on which side of `1/4` the tail lies; the automaton's carries
  force "below" (`4α = 0.666…`, not `1.000…`), and every junction in the
  language respects that (`…5151512…` `<` `…5151515…`).  This is what a
  background+burst family cannot express — hence its cap at `102`
  (`mahler_lower_bound_base7_k2`), and the periodic-background variant
  (`P/(7⁹−1) + B·L`) also fails for every `B ≤ 3000` under the sharp
  extended-window condition.  The exact lower side at `k ≥ 2` needs the
  automaton itself.
* **Why covering + Farey cannot give the `k ≥ 2` upper side.**  With drops the
  engine's stage inequality is `μ ≲ Q·d''` for the post-drop denominator
  `d'' ≤ g − 1` — the trivial bound.  The real constraint is digit-level: after
  a drop to `d''`, multiples `m ≡ 0 (mod d'')` sit at integers from a fixed
  side (runs of `6`s or `0`s — sign!), the others at `r/d''` minus a small
  amount whose borrow pattern must avoid the block.  The `k = 2` constant is a
  renormalization of that structure.  Open; not this lap's tool.

**Escape engine, first bricks** (`AdderEscape.lean`, trust triple):
`carry g x m i = ⌊m·{gⁱx}⌋`, `carry_recursion`
(`carry i = (m·aᵢ + carry (i+1)) / g`), `digitOf_mul` (`i`-th digit of `m·x`
is `(m·aᵢ + carry (i+1)) % g`).  So an automaton run that agrees with the
TRUE carries reads the digits of `m·x` exactly.

### Next bricks (the plan)
1. `realOfDigits` from an infinite path of a certificate automaton (states,
   digit-labelled edges, per-channel carries), `ProperDigits` automatic when
   no state emits `g−1` forever.
2. **Tail intervals**: per state `s` rationals `lo_s ≤ hi_s` with
   `lo_s ≤ (a + lo_{s'})/g` and `(a + hi_{s'})/g ≤ hi_s` on every edge; then
   every tail from `s` lies in `[lo_s, hi_s]` (telescoping + limit).
3. **Carry soundness**: `m·lo_s ≥ c_s(m)` and `m·hi_s < c_s(m) + 1` pins the
   true carry to the certificate's; with `digitOf_mul` the channel digits are
   the certificate's, so the word never occurs.
4. Irrationality by cardinality (a branching state gives `2^ℵ₀` paths,
   injective into `ℝ`; `exists_setReal_irrational` is the template).
5. Instance: `M(7,2) ≥ 176` from the 10-state SCC (`decide +kernel` on
   175 carry components per state).

## 🚨 `g^(k+1)/4` IS THE WRONG TARGET FOR `k ≥ 2` — refuted by exact data; first `k = 2` prime lower bounds (2026-09-07, autonomous)

The kickoff's general-`k` objective "`M(g,k) ≤ (1/4 + O(1/g))·g^(k+1)`" is
**false at `k = 2`** as a constant-`1/4` statement.  Exact values
(`experiments/mahler_exact_M.py`; `M(7,2)` new this lap,
`experiments/mahler_exact_M_k2_g7.txt`):

    g          3      5      7
    M(g,2)     8     48    176        (blocks 00 and 66 at g = 7)
    /g³      .296   .384   .513       — ABOVE 1/4 and CLIMBING with g

So the `k = 1` constant `1/4` (proved: `MahlerQuarter.lean`) does not persist:
the drop mechanism found while formalizing (§below — a canonical denominator
divisible by `g` drops by a factor `g`, which is impossible at `k = 1` and
available at `k ≥ 2`) is not a proof deficiency, it is where the extra
multipliers live.  The `k ≥ 2` question is a DIFFERENT constant; guess from
three points: `M(g,2)/g³ → 1/2`?  (Also `M(3,3) = 43 = 0.53·3⁴`.)

**Lower side started** (`MahlerPrimeLowerBoundBlock.lean`, trust triple):
`mahler_lower_bound_bg_block` generalizes the digit certificate to blocks
(stabilized top-`k` digits are all the background digit), and

    mahler_lower_bound_base5_k2 :  M(5,2) ≥ 44    (exact 48)
    mahler_lower_bound_base7_k2 :  M(7,2) ≥ 103   (exact 176)

⚠️ The background+burst family is EXACT at `k = 1` (`g = 5, 7, 13, 23`) but at
`(7,2)` caps at `102` against `176`: the `k = 2` extremal orbit has a shape the
family does not reach (both extremal blocks are RUNS, `00`/`66`, i.e. the orbit
must stay `≥ 1/49` from every integer under all `m ≤ 175`).  Finding that
witness family is the lower-side crux for `k ≥ 2`.

### Next (in order)
1. Lower side, `k = 2`: reverse-engineer the `g = 7` extremal from the
   adder-machine SCC (`experiments/mahler_exact_M.py` keeps the live states) —
   what rationals does the escaping orbit shadow?  Prediction from the drop
   mechanism: denominators `≈ c·g²` divisible by `g`, i.e. `x_n ≈ p/(g·d')` with
   `d' ≈ c·g`, dropping to `d'` and jumping back.
2. Upper side, `k = 2`: the engine's per-stage bound with drops allows the
   canonical denominator to cycle, so it currently gives nothing below
   `g^(k+1) − g(g−2) − 1` (`mahler_multiplier_prime_gen`).  The missing
   constraint must be what the run blocks see: the exit-time defect is
   `≈ 1/(2Q)` and the shadow denominator is `≤ Q/g` after a drop.
3. `M(11,2)` exact (expensive: `M ≈ 700` channels) — one more point on the
   ratio curve before conjecturing `1/2`.

## ✅ THE MULTI-SCALE BOUND LANDED AT `k = 1`: `M(g,1) ≤ (g² + 6g + 1)/4` (2026-09-07, autonomous)

`MahlerQuarter.lean` (new, trust triple).  `mahler_multiplier_quarter`: for every
odd prime `g` some `m ≤ (g² + 6g + 1)/4` has any digit occurring i.o. in `m·α`.
That is `g²/4 + O(g)` — the constant the census `docs/mahler-exact-values-2026-09-07.md`
sits at (`M(p,1) ≈ ⌊p/2⌋²`, ratio climbing to `1/4` from below).  Sanity: the
smallest `M` the method allows (`(g+1)(g+5)/4 − 2`) is above every census value.
`mahler_multiplier_prime_half_of_quarter` retires the `g(g+1)/2` bound to a
corollary for `g ≥ 5` (at `g = 3` the quarter bound is `7 > 6`).

### How the bookkeeping actually went (two simplifications, one gap)

1. **No exit-time count, no `⌈1/(M/(gQ) − 1/4)⌉` induction.**  The canonical
   shadow (denominator `≤ Q`, defect `< 1/(2Q)`) exists at every bad time
   (`canonical_exists`: Dirichlet, then the covering lemma with `μ = M+1 > 2Q`)
   and is unique (`orbit_approx_unique`).  A *stage* (`stage_jump`) shows its
   denominator strictly increases: follow the shadow chain (`shadow_chain`) until
   the defect first reaches `1/(2Q)` (a `Nat.find`); one step before, covering
   gives `(μ−2d)E < 1 − d/Q`; at exit the shadow is not canonical, so Farey
   against the new canonical `τ` gives `τ.den·gE + d·F ≥ 1` with `d·F ≤ d/μ`.
   Then `τ.den > d` follows from the one-variable **jump condition**
   `d·μ·g·(Q−d) ≤ (μ−d)(μ−2d)·Q`.  Since denominators are integers `≤ Q`, `Q`
   stages contradict (`den_grows`, `no_bad_orbit`).
2. **The `O(1/g)` loss is `d·F ≤ d/μ`, not `1/2`** — `stage_arith`, Step A: from
   `(μ−2t)FQ < Q−t` and `2QF < 1` get `μF < 1`.  This is what moves the fixed
   point from `M/g ≤ Q/2` to `M/g ≤ Q/4`.
3. **The constant.**  At `k = 1` the jump condition is the quadratic
   `(μ+2)d² − μ(g+3)d + μ² ≥ 0`; at `μ = (g+1)(g+5)/4` its discriminant is exactly
   `−4μ²` (`jump_condition_k1`: `4(μ+2)·(…) = (2(μ+2)d − μ(g+3))² + 4μ²`), so it
   holds for every REAL `d` and no case split on `d` is needed.

🚨 **The gap the paper argument glossed — `k ≥ 2` is NOT covered.**  The shadow
`ρ' = gρ − ⌊g x_n⌋` keeps `ρ.den` only when `g ∤ ρ.den`.  If `g ∣ ρ.den` the
denominator DROPS by a factor `g` with the defect unchanged, and the jump then
lands only at `≳ μ/g ≈ Q/4`, not above the previous denominator: the sequence of
canonical denominators can cycle `Q/2 → Q/4 → …` and the iteration gives no
contradiction.  At `k = 1` every canonical denominator is `< Q = g`
(`canonical_den_lt`), hence coprime to a prime `g`, so no drop occurs — that is
the only place primality and `k = 1` enter.  The general theorem
`mahler_multiplier_quarter_param` carries the hypothesis
`hcop : ∀ d, 1 ≤ d → d < gᵏ → Nat.Coprime g d`, which is FALSE for `k ≥ 2`.
**Reaching `g^(k+1)/4` for `k ≥ 2` needs a new idea** for the drop case (e.g.
exploit that a drop means `x_{n+1}` is within `~1/M` of a rational of
denominator `≤ Q/g`, or a potential that survives drops).  Not claimed.

### Next

* `k ≥ 2`: the drop case above.  Candidate: at a drop, `d' = d/g ≤ Q/g` and the
  defect `E ≲ (1 − d/Q)/μ` is unchanged; the near-grid conversion of
  `MahlerPrimeHalf` costs `d'·gᵏ` — too much unless `d' ≤ g`.  Look for a
  second Farey partner instead.
* Tighten `O(g)`: the integer-only jump condition allows `μ = (g+1)(g+5)/4 − 1`;
  and `d·F ≤ d/μ` used `d ≤ Q` nowhere, so the constant `6` is not sharp.

## 📜 (superseded by the above) THE MULTI-SCALE ARGUMENT REACHES `g^(k+1)/4` — ENGINE FORMALIZED (2026-09-02, autonomous)

The crux (prime-base upper bound) now has a COMPLETE argument on paper reaching
the empirical constant, and its engine is in `src/` (`MahlerFarey.lean`,
trust triple).  What remains is chain/exit-time bookkeeping, not a new idea.

### The argument

Fix `Q = gᵏ`, `M` the multiplier budget, `x` bad (no `m ≤ M` puts `m x` in the
cell of `W`).  Two facts about a bad point:

1. **`defect_small_of_bad`** — the covering lemma applies to EVERY reduced
   rational of denominator `≤ Q`, so the Dirichlet approximation `σ` has defect
   `< 1/(2Q+1)`, not merely Dirichlet's `1/(Q+1)`.  (`M ≥ 4Q` makes the
   coefficient `M + 1 − 2σ.den ≥ 2Q + 1`.)
2. **`den_jump_of_bad`** — hence by Farey separation (`defect_pair_ge`) any
   other reduced `p/a` with `a ≤ Q` satisfies

       σ.den · |a x − p| > 1/2,   i.e.   σ.den > 1 / (2|a x − p|).

Now run the shadow chain of `orbit_escapes` from a rational of denominator `a`.
Its defect multiplies by `g` each step; let `n*` be the first time the defect
`E` leaves `[0, 1/Q)`.  At `n* − 1` the covering lemma gives
`E/g < (1 − a/Q)/(M + 1 − 2a)`, so at `n*`

    σ.den  >  1/(2E)  >  (M + 1 − 2a) / (2 g (1 − a/Q)).

So the canonical denominator **jumps**.  Iterating with `a_{j+1}` the new
denominator, `a_{j+1} ≳ (M/g)/(1 − a_j/Q)` (the factor `2` is absorbed because
`a·(defect of σ) ≤ Q/(2Q+1)`, i.e. the loss is `O(1/g)`, not `2`).  The map
`f(a) = (M/g)/(1 − a/Q)` has a fixed point iff `a(1 − a/Q) = M/g` is solvable,
i.e. iff `M/g ≤ Q/4` — the maximum of `a(1−a/Q)` on `[0,Q]`, attained at
`a = Q/2`.  So for

    **`M > g Q / 4 = g^(k+1)/4`**

there is no fixed point, `f(a) − a ≥ (M/g − Q/4)` for every `a`, the
denominators increase by a fixed amount each stage, and they must exceed `Q` —
contradiction.  Target: **`M(g,k) ≤ (1/4 + O(1/g))·g^(k+1)`**.

That is exactly where the exact values sit: `M(p,1)` is `6, 9, 25, 64` at
`p = 5, 7, 11, 17` against `(p−1)²/4 = 4, 9, 25, 64`.  So the constant `1/4` is
not an artefact of the method — it is the truth, and `a = Q/2` being the
double root explains WHY the extremal witnesses sit at shadow denominator
`q ≈ g/2` (`PENDING_WORK`'s earlier observation, now derived).

### What remains (next lap)

* the exit-time `n*` as a `Nat.find`, and the shadow chain's defect recursion
  `E_{i+1} = g·E_i` restated so `n*` is well defined (`orbit_escapes` has the
  recursion but discards it at the contradiction);
* the stage iteration as an induction on `⌈1/(M/(gQ) − 1/4)⌉` steps;
* the `O(1/g)` bookkeeping (`a·defect σ ≤ Q/(2Q+1)`) carried through.

Nothing here needs a new idea; `defect_pair_ge`, `defect_small_of_bad`,
`den_jump_of_bad` are the load-bearing lemmas and are proved.

### Superseded by the above (kept for the record)

The two-branch bound `max(q₀·gᵏ, g^(k+1) − q₀(g−2) − 1)` of
`MahlerPrimeHalf.lean` gives `g(g+1)/2` at `k = 1` — a factor `2` off.  The
analysis that localized that factor (cost_A `= q·Q` vs the extremal `q²`) is
still correct but is no longer the route: the multi-scale iteration replaces
both branches.

## ✅ THE PRIME-BASE UPPER BOUND, HALVED: `M(g,1) ≤ g(g+1)/2` (2026-09-02, autonomous)

`MahlerPrimeHalf.lean` (new, trust triple).  The chain at a prime base is now

    g^(k+1)                      `mahler_multiplier`
    g^(k+1) − 2g + 3             `mahler_multiplier_prime`      (q = 1 excluded)
    g^(k+1) − (g−1)² − ...       `mahler_multiplier_prime_gen`  (k ≥ 2)
    g(g+1)/2                     `mahler_multiplier_prime_half` (k = 1, g odd)

### The idea: CONVERT small denominators, don't exclude them

The recorded wall was that excluding a shadow denominator `q ≥ 2` is
unavailable (for `q ≥ 2` the natural modulus `q gᵏ` shares `gᵏ` with
`⌊gᵏ x⌋`, so `cell_hit_of_coprime` does not apply).  The way past it:

> if `x_n` is within `g^(−k)/q` of `p/q`, then `q x_n` is within `g^(−k)` of an
> integer — i.e. the orbit of `q·α` has a run of `k` zeros or `k` `(g−1)`s at
> time `n`.  `MahlerRunBranch` settles that for `q·α` at `m' ≤ gᵏ`, and
> `m'·(qα) = (m' q)·α`.

So a small denominator costs a multiplier `q gᵏ` (`mahler_multiplier_near_grid`)
— no exclusion and no coprimality.  With a threshold `q₀`, every orbit point is
either near a `< q₀` grid (cost `(q₀−1)gᵏ`) or has all shadows of denominator
`≥ q₀`, where the sweep needs only `M ≥ g^(k+1) − q₀(g−2) − 1`
(`defect_contracts_of_bad_ge`; tight, `M+1−2q ≥ g(Q−q)` ⟺ `(q−q₀)(g−2) ≥ 0`).
`mahler_multiplier_prime_param` balances the two.  At `k = 1`,
`q₀ = (g+1)/2` makes both sides exactly `g(g+1)/2`.

### 📐 WHERE THE REMAINING FACTOR 2 LIVES (the crux, decomposed)

Write `Q = gᵏ` and let `q` be the shadow denominator.  Our two branch costs are

    cost_A(q) = q·Q        (near-grid, via the run branch on qα)
    cost_B(q) = g(Q − q)   (covering sweep)

and the theorem is `max_q min(cost_A, cost_B)`, maximized at `q = gQ/(Q+g)`
(`= g/2` at `k = 1`), value `≈ g²/2`.  The TRUTH is `≈ g²/4`, attained by
`bgLiouville` with `a = 2`: there `b = 2`, `gcd(2, g−1) = 2`, so the shadow is
`1/((g−1)/2)` and **`q = (g−1)/2`, with `M = q²`** — i.e. the extremal cost is
`q²`, not `qQ ≈ 2q²`.  So:

* **`cost_A` is loose by ~2 at the extremal `q`** (`qQ` vs `q²`, and `Q ≈ 2q`).
  The looseness is real, not an artefact: `m' ≤ gᵏ` IS tight for the run branch
  in isolation (Liouville needs `gᵏ − 1`), so the gain has to come from the
  *joint* constraint — an `α` that is near the `q`-grid AND whose `qα` is a
  full Liouville witness is over-determined.  That joint constraint is the
  crux's remaining content.
* **`cost_B` is loose too**, and cannot be blamed on `q` alone: at
  `q = 0.618·g` (where `cost_A = q²` would meet `cost_B`) the balance gives
  `0.382 g²`, still above `g²/4`.  So a proof of the truth needs BOTH branches
  sharpened, or a single argument replacing them.
* Verified NOT the source of the slack: the window `E ∈ [1/(gQ), 1/Q)` for the
  critical defect is exactly a ratio-`g` window, so the adversary can place `E`
  at its bottom — `E ≥ 1/(gQ)` is tight.  And the covering constant is tight
  for a fixed configuration: `M ≈ q·d/E` with `d ≤ 1/q − 1/Q` the (fixed,
  `w`-determined) distance from the grid point below the cell to the cell.

**Next attack**: the joint constraint.  Formalize "the orbit is within
`g^(−k)/q` of the `q`-grid infinitely often" and "`qα` has full-strength
`0ᵏ` runs" and show they cannot both hold at full strength; the target is
`cost_A(q) ≈ q²`, which with `cost_B` would give `≈ 0.382 g²`, and then the
matching sharpening of `cost_B`.

## ✅ `M(7,1) = 9` AND `M(g,k) ≤ g^(k+1) − 2g + 3` (PRIME `g`) (2026-09-02, autonomous)

Two upper-side results, both kernel-checked, trust triple.

### `M(7,1) = 9` exact (`MahlerBase7Exact.lean` + `MahlerBase7Cert0..6.lean`)

The blocker recorded last lap ("a single `decide +kernel` over ambient
`9! = 362880` ran > 45 min without finishing") is **dissolved, not chunked
around**.  The multiplier is quantified *after* the digit, so for each `w`
separately it suffices that SOME subset of `{1,…,9}` collapses:

| `w` | multipliers | ambient | live |
|---|---|---|---|
| 0, 3, 6 | `1,2,3,4,5,6,8` | `5760` | `12, 18, 12` |
| 1, 5 | `1,3,4,5,6,9` | `3240` | `27` |
| 2, 4 | `1,2,3,4,5,6` | `720` | `16` |

Total ambient `25200` vs `7 × 362880` — a **100×** cut
(`experiments/mahler_subset_hunt_perdigit.py`).  The old uniform-subset hunt
found nothing under `30000` and was right to; the gain is entirely in letting
the family depend on `w`.  ⚠️ One certificate PER MODULE: the seven kernel
`decide`s in one `lean` process exhaust memory (7.4 GB, no termination),
each alone runs 18 s – 2 min.  ⚠️ Also: a `lake build` killed mid-flight
leaves ORPHAN `lean` workers holding ~60k fds each; three of them reproduce
the box's "Too many open files" mystery.  `ps -eo pid,etimes,rss | grep lean`
and `kill -9` before blaming the environment.

`mahler_M_seven_eq_nine` joins `M(3,1) = 2` (B–B) and `M(5,1) = 6`.  The
general sandwich gives only `5 ≤ M(7,1) ≤ 49`.

### `M(g,k) ≤ g^(k+1) − 2g + 3` for prime `g` (`MahlerPrimeUpper.lean`)

The `q = 1` exclusion listed as "the cheapest remaining upper-side item" is
done.  `orbit_run_of_den_one`: a denominator-`1` shadow with defect `< g^(−k)`
at `x_n` forces `0ᵏ` or `(g−1)ᵏ` at `n` (the only integers in range are `0`
and `1`, and their cells ARE those blocks), which `MahlerRunBranch` settles at
`m ≤ gᵏ`.  So the sweep runs with `q ≥ 2`, and
`defect_contracts_of_bad_two` is tight: `M + 1 − 2q ≥ g(Q − q)` reduces to
`(q−2)(g−2) ≥ 0`.  **This is the end of what the covering method can give**
— see the structural finding below for why `q ≥ 3` is not available.

### Next attack, in order

1. **The prime `Θ(g²)` upper side** (the standing crux).  Empirically
   `M(p,1) = ⌊(p−1)²/4⌋ − δ` with `δ` small: `7→9, 11→25, 17→64` hit it
   exactly, `19→80` (81), `23→120` (121), `29→192` (196); `5→6` is the
   outlier above.  The covering method stops at `≈ g²/2` even in the best
   case, so this needs Farey-hopping (track TWO shadow denominators and hop
   between neighbouring Farey fractions rather than following one shadow).
2. **`M(11,1) = 25`?**  The per-digit subset trick is the lever, but subsets
   of `{1,…,25}` are `2²⁵`; needs a greedy peel (start from the full set,
   drop the largest multiplier that keeps collapse) rather than enumeration.
3. **A uniform `B(g)`** for a general prime `Θ(g²)` lower-bound theorem.
   Probe data in `experiments/mahler_bg_burst_structure.py`.
4. Composite-`g` run theorem ("predecessor digit coprime to `g`"); B–B Thm 3.2.

## ✅ THE UNIVERSAL MAHLER CONSTANT IS `≥ 0.840` (was `1/2`); THE POWER FAMILY IS EXACT ON 13 COMPOSITE BASES (2026-09-02, autonomous)

Scanning `mahler_lower_bound_power` over `L ≤ 5`
(`experiments/mahler_power_family_scan.py`), the best admissible `t`
**matches the exact adder-machine value of `M(g,1)`** at 13 of the 20
composite bases `4 ≤ g ≤ 28`: `g = 4, 6, 8, 9, 10, 14, 15, 16, 18, 20, 22,
24, 26`.  On composite bases this family is apparently not merely a lower
bound but *the extremal construction*.  (Misses: `21` (180 vs 224), `25`
(120 vs 189), `27` (234 vs 375), `28` (432 vs 500) — all have `t ∤ g^L` for
the exact `t = M(g,1)/(g−1)`, or a non-integer such `t`.)

Formalized (`MahlerPowerInstances.lean`, new; trust triple, `decide` guards):

| `g` | `t, c, L` | bound | `k = 1` | `/g²` | divisor family |
|---|---|---|---|---|---|
| 18 | `16, 6561, 4`  | `16(18ᵏ−1)` | `272` | **0.840** | `153` |
| 20 | `16, 25, 2`    | `16(20ᵏ−1)` | `304` | 0.760 | `190` |
| 22 | `16, 14641, 4` | `16(22ᵏ−1)` | `336` | 0.694 | `242` |
| 24 | `18, 32, 2`    | `18(24ᵏ−1)` | `414` | 0.719 | `276` |
| 26 | `16, 28561, 4` | `16(26ᵏ−1)` | `400` | 0.592 | `338` |

**`mahler_universal_constant_ge`**: no multiplier `m ≤ 271` works for a
certain irrational and a single base-18 digit.  Against
`mahler_multiplier_lt`'s `M(g,k) < g^(k+1)` this gives

    0.840 · g^(k+1)  ≤  sup_{g,k} M(g,k)  <  g^(k+1),

cutting the room for the universal constant from the even-base divisor
family's factor `2` to a factor **`1.19`**.

## 📐 STRUCTURAL FINDING: THE COVERING METHOD CANNOT BEAT `g^(k+1) − q(g−2)`

Analysis of `MahlerMultiplier.lean`'s sweep (recorded so the crux is not
re-attacked blindly).  `defect_bound_of_bad` gives, for a bad `x` and any
reduced `p/q` with `q ≤ gᵏ`, `0 < |η| < g⁻ᵏ`:

    |η| < (1 − q/gᵏ) / (M + 1 − 2q).

The escape lemma needs `|η| < g^(−k−1)` (so that the `×g` per step keeps the
shadow inside the quality window `g⁻ᵏ`), i.e.

    **M ≥ g^(k+1) − q(g − 2) − 1**,   binding at the SMALLEST admissible `q`.

* `q = 1` is exactly "the orbit point is within `g⁻ᵏ` of an integer" = a run
  of `k` zeros or `k` `(g−1)`s, which `mahler_multiplier_of_zero_runs`
  (`MahlerRunBranch.lean`) already settles with `m ≤ gᵏ`.  So for prime `g`
  the sweep may start at `q ≥ 2`, giving `M(g,k) ≤ g^(k+1) − 2g + 3` — a real
  but small (`2g − 4`) improvement, and the surgery on `MahlerMultiplier.lean`
  is the cheapest remaining upper-side item.
* Excluding larger `q` is **not** available: the `q = 1` argument works only
  because `Q = gᵏ` and `A = ⌊gᵏ x⌋` can be a *unit mod `gᵏ`*; for `q ≥ 2` the
  natural `Q = q gᵏ` has `gcd(A, Q) ≥ gᵏ`, so `cell_hit_of_coprime` does not
  apply.  And the empirical prime witnesses sit at `q ≈ g/2`, so even a
  perfect `q`-exclusion would stop at `≈ g²/2`, still a factor 2 above the
  truth `≈ g²/4`.
* **Conclusion: the prime `Θ(g²)` UPPER side needs the Farey-hopping analysis,
  not a sharper covering constant.**  That is the standing crux.


## ✅ `M(10,k) ≥ 8(10ᵏ − 1)` VIA A NEW POWER-DIVISOR FAMILY (2026-09-02, autonomous)

The directive's named cheap win, taken at **full generality in `k`** rather
than as a `k = 1` `decide` (`MahlerLowerBoundPower.lean`, new; trust triple):

| theorem | claim |
|---|---|
| `pred_pow_div_mod` | `(gᵏ − 1)/gⁱ % g = g − 1` for `i < k` |
| **`window_lt_of_digit`** | if ANY digit of `N` in the window `[d−k, d)` is not `g − 1`, then `N % g^d + g^(d−k) + 1 ≤ g^d` — the arithmetic shadow of "the window is not the all-`(g−1)` block", and the reusable core |
| `power_split`, `avoid_of_power` | `m·c = q·g^L + s·c`, guard block `s·c < g^L` |
| **`mahler_lower_bound_power`** | `t·c = g^L` with every guard block `s·c` (`s < t`) free of the digit `g−1` ⇒ **`M(g,k) ≥ t(gᵏ − 1)`** |
| **`mahler_lower_bound_base10`** | `8 · 125 = 10³`, guards `0,125,…,875` have no `9` ⇒ **`M(10,k) ≥ 8(10ᵏ − 1)`** |

`L = 1` recovers `mahler_lower_bound_divisor` (B–B Thm 3.1) exactly; `L > 1`
admits `t` larger than any proper divisor of `g`.  Base 10, `k = 1`:
`72 ≤ M(10,1) ≤ 100` (factor `1.39`), against the divisor family's `45` — and
`72` is the exact adder-machine value, so base 10 joins base 5 in being pinned
from below by a witness known to be optimal.

## 🔜 `M(7,1) = 9` — CERTIFICATES COMPUTED, LEAN ENCODING PENDING

`experiments/mahler_collapse_cert.py 7 9` produced all seven digit
certificates for the nine-channel base-7 family (`x, 2x, …, 9x`):

    ambient 362880 (= 9!),  live 12 / 38 / 29 / 26 / 29 / 38 / 12,
    omega-support ≤ 123,  every surviving component a simple cycle.

So the mathematics is settled and the data is small; what is missing is only
the Lean side.  A single `decide +kernel` over `362880 × 7 = 2.54M`
`gfamPred` evaluations (each recursing over 9 channels of `Int` arithmetic) is
too big for one goal — this needs the **chunked** `checkEdgesOnA` path that
`AdderTowerC8/C9` already use (`experiments/emit_cert_lean.py` packs the
tables; `AdderCertSplit.lean` assembles the chunks).  With the lower half
already proved (`mahler_lower_bound_base7`), that lands `M(7,1) = 9`.

⚠️ Recorded refutation: no subset of `{1,…,9}` with product `≤ 30000`
collapses at base 7 (`experiments/mahler_subset_hunt.py 7 9 30000`), so the
ambient cannot be cheaply shrunk the way base 5 could (there
`{1,2,3,4,6}`, ambient `144`, already collapses — `5x` is redundant).


## ✅ `M(5,1) = 6` — THE MAHLER CONSTANT PINNED EXACTLY AT A PRIME BASE (2026-09-02, autonomous)

Both halves, kernel-checked, trust triple (`MahlerBase5Exact.lean`, new):

* **upper** `m5_mahler_upper`: for every irrational `X` and every base-5 digit
  `w`, some `1 ≤ m ≤ 6` has `w` i.o. in `m·X`.  Five `decide +kernel`
  certificates of `signed_engine_g_single` on the six-channel single-track
  base-5 family `x, 2x, …, 6x` (ambient `6! = 720`; after pruning only `6`–`11`
  live states, every surviving component a simple cycle).  Emitter +
  independent re-verification: `experiments/mahler_collapse_cert.py 5 6`
  (validated against `AdderTowerC1`'s base-3 shape).
* **lower** `Mahler.mahler_lower_bound_base5` (previous entry).
* **`mahler_M_five_eq_six`** conjoins them.

This is the **first Mahler constant pinned to a point at a prime base beyond
Berend–Boshernitzan 1994's `M(3,1) = 2`**.  The general sandwich gives only
`4 ≤ M(5,1) ≤ 25`.

### NEXT on this thread (in order)

1. **`M(7,1) = 9`.**  Lower half already proved.  Upper half needs channels
   `1..9`: ambient `9! = 362880`, alphabet 7 ⇒ `2.5M` edge checks — too big for
   one `decide`, so it needs the **chunked** `checkEdgesOnA` path that
   `AdderTowerC8/C9` already use (`experiments/emit_cert_lean.py` packs the
   tables).  ⚠️ `M = 8` genuinely FAILS: at `g = 7, w = 1` the live graph has an
   SCC of size 2 with intra-out-degree 2 (two cycles) — i.e. a real irrational
   witness, matching `M(7,1) = 9`.  That refutation is itself the check that the
   emitter is not over-reporting collapse.
2. `M(11,1)`, `M(13,1)`: the lower halves are 1 short (24 vs 25) and exact (35);
   uppers need ambient `11!`/`35!` — out of reach by the naive product, so they
   need the incremental **trimmed** product (`mahler_exact_M.py`'s SCC trimming)
   lifted into the certificate emitter before Lean can see them.
3. A uniform `B(g)` for the general prime `Θ(g²)` lower bound (see below).


## ✅ PRIME-BASE LOWER SIDE IS `Θ(g²)` — THE OPEN HALF OF THE MAHLER CHAPTER, SETTLED (2026-09-02, autonomous)

The crux carried into this lap was: *for prime `g`, is `M(g,1)` of order `g`
(Berend–Boshernitzan 1994 Thm 3.3, `(3/2)(g−1)`) or of order `g²` (what the
exact adder machine reports)?*  **It is `g²`, and the witnesses are a
two-parameter generalisation of the family already formalized here.**

### The family (`MahlerLowerBoundBackground.lean`, new; trust triple)

    α = a/(g − 1) + B · Σᵢ g^(−i!)          `bgLiouville g a B`

— constant background digit `a`, with the integer `B` *added into it* (carries
and all) at each burst position `i!`.  Multiplying by `m` preserves the shape:
the background becomes `b = (m a) mod (g − 1)` (because `gⁿ ≡ 1 mod (g−1)`) and
the burst becomes `N = m B`.

| theorem | claim |
|---|---|
| `orbit_bg_mem` | **the crux identity**: for `n` late there is `d ≥ 1` with `orbit g (mα) n ∈ [ρ/g^d, (ρ+1)/g^d)`, `ρ = bgResidue g a B m d = (b·S_d + mB) mod g^d`, `S_d` the repunit.  The orbit is *pinned to a single order-`d` cell*, not merely bounded — which is what admits an arbitrary target block, in either direction |
| `mahler_lower_bound_bg` | if every such cell misses the cell of `w`, no `1 ≤ m ≤ M` puts `w` i.o. into `m α`; so `M(g,k) > M` |
| `repunit_burst_lt`, `bgResidue_digit_stab` | the digits stabilize at the background `b` once `b·S_D + N < g^D` |
| `mahler_lower_bound_bg_digit` | hence for `k = 1` the infinite hypothesis is a **finite, `decide`-able certificate** |

### The values (`MahlerPrimeLowerBound.lean`, new; all `decide +kernel`)

| base | `a, B, W` | proved | true `M(g,1)` | B–B Thm 3.3 |
|---|---|---|---|---|
| 5  | `2, 1, 1`     | `M(5,1)  ≥ 6`   | 6   | 6  |
| 7  | `2, 1, 1`     | `M(7,1)  ≥ 9`   | 9   | 9  |
| 11 | `2, 73, 10`   | `M(11,1) ≥ 24`  | 25  | 15 |
| 13 | `2, 958, 12`  | `M(13,1) ≥ 35`  | 35  | 18 |
| 23 | `2, 2549, 22` | `M(23,1) ≥ 120` | 120 | 33 |

**Exact at `g = 5, 7, 13, 23`**, one short at `g = 11`.  `120/23² ≈ 0.227 ≈ 1/4`
— the quadratic order for a prime base, in the kernel, beating the linear
bound by `3.6×`.  `M(5,1) = 6` and `M(7,1) = 9` are now sandwiched to a point
once the matching collapse certificates land (item 2 below).

**Why `a = 2`.**  For odd `g` the background digit `b = 2m mod (g−1)` is always
*even and `< g − 1`*, so `W = g − 1` never arises from the background for any
`m`: the entire multiplier budget is spent on the burst, and `B` tunes it to
be quadratic.  The pure Liouville multiple (`a = 0`) cannot do this.

### NEXT on this thread

1. **A uniform `B(g)`** giving `M(g,1) ≥ c g²` for *every* prime `g` — the
   general theorem, not a table.  Probe `experiments/mahler_bg_burst_structure.py`
   (`a = 2`, `W = g−1`, `B ≤ 40g²`) attains `((g−1)/2)² − 1` at `g = 11, 13, 23`
   but only `~0.6·((g−1)/2)²` at `g = 17, 19, 29, 31`, so either `B` must range
   further or those bases need the Farey-hopping (run-free) mechanism.  Best
   `B` found: `5:781, 7:1123, 11:803, 13:1010, 17:1492, 19:1991, 23:2641,
   29:3893, 31:4398` — no formula spotted yet; `B/g² ≈ 4.6–6.6` throughout,
   which is the first structural hint.
2. **Matching upper halves** (`M(5,1) ≤ 6`, `M(7,1) ≤ 9`) as collapse
   certificates of the `AdderTowerC*` kind ⇒ the first exactly-known prime
   values beyond B–B's `M(3,1) = 2`.
3. `k ≥ 2` version of the certificate (the general `mahler_lower_bound_bg`
   already takes arbitrary `k` and arbitrary blocks; only the *finite*
   reduction is `k = 1`).
4. Composite-`g` run theorem; B–B Thm 3.2.


## ✅ `M(g,k) < g^(k+1)` — BEREND–BOSHERNITZAN'S OPEN QUESTION ANSWERED; ATTRIBUTIONS FIXED (2026-09-02, autonomous)

The host answered `ON-LINE-REQUEST.md` with the full B–B 1994 paper
(`archive/findings/ON-LINE-FINDINGS-2026-09-02-berend-boshernitzan-1994.md`;
the PDF is `papers/berend-boshernitzan-1994-mahler-multiples.pdf`).  Three
consequences, all acted on this lap:

1. **Their open question (p. 320) is answered.**  *"We do not know whether it
   is true in general that `M(g,k) < g^(k+1)`."*  Our contraction
   (`defect_contracts_of_bad`) survives at the budget `g^(k+1) − 1`: if
   `g|qx − p| ≥ g⁻ᵏ` then `(gQ − 2q)|qx − p| ≥ 1 − 2q/(gQ) ≥ 1 − q/Q`,
   contradicting the covering lemma.  `Mahler.mahler_multiplier_lt`
   (`MahlerMultiplierStrict.lean`, trust triple): **some `1 ≤ m < g^(k+1)`**
   for every irrational `α`, `g ≥ 2`, block `w`.  Ledger:
   `Literature.berendBoshernitzan_strict` (verbatim question) +
   `berendBoshernitzan_strict_holds`.  With their Thm 3.2
   (`M(g,k) ≥ (1 − ε)g^(k+1)`, `g` not a prime power, `k` large) the order
   `g^(k+1)` is sharp for every non-prime-power base.
2. **Attribution.**  `mahler_lower_bound_divisor` (`t(gᵏ − 1)`) is B–B
   **Theorem 3.1** (same witness); `8(10ᵏ − 1)` is their **Example 3.1**.
   Docstrings of `MahlerLowerBoundGeneral.lean` and `Literature.lean` now
   say so; the "Renewal-type theorems…" title in the ledger was a
   misattribution and is fixed.  The lower-side files remain formalizations
   of known theorems (no Lean formalization known).
3. **Their Theorem 3.3** (`M(g,1) ≥ (3/2)(g − 1)`, odd `g ≥ 5`, witness
   `α = 1/2 + Σ g^(−nⱼ)`) is the periodic-background family of the entry
   below with `c = (g−1)/2`.  Our exact values show it is **tight for
   `g = 5, 7`** (`6 = 9 − 3`, `9`) and far from tight from `g = 11` on
   (`25` vs `15`, `35` vs `18`, `192` vs `42`): the `Θ(g²)` prime-base
   lower bound is not in the paper.

## ✅ MAHLER RUN BRANCH SETTLED AT `gᵏ`; PRIME-BASE CONJECTURE REFUTED BY EXACT COMPUTATION (2026-09-02, autonomous)

**The prime-base question of the chapter is now answered the OTHER way
round.**  The previous lap asked whether `M(g,k) = Θ(gᵏ)` for prime `g`
(upper side weak) or `Θ(g^(k+1))` (lower side weak).  Exact computation
says the latter, and a new theorem says where the witnesses must live.

### The theorem (`MahlerRunBranch.lean`, new; trust triple, no sorries)

| theorem | claim |
|---|---|
| `cell_hit_of_coprime` | `Q·x = A + ε`, `A` a unit mod `Q`, `0 < ε < 1/Q` ⇒ every cell `[W/Q,(W+1)/Q)` is hit by some `{m x}`, `1 ≤ m ≤ Q` |
| `hit_of_zero_run` / `hit_of_pred_run` | orbit form: `k` zeros (resp. `(g−1)`s) after position `n+k`, pre-run block `⌊gᵏ·orbit n⌋` (resp. `+1`) coprime to `g` ⇒ every `k`-block hit at `n` by some `m ≤ gᵏ` |
| `exists_maximal_zero_run` | `0ᵏ` i.o. in an irrational ⇒ maximal runs (nonzero predecessor digit) arbitrarily late |
| **`mahler_multiplier_of_zero_runs`** | **`g` prime, `0ᵏ` occurs i.o. in `α` ⇒ some `m ≤ gᵏ` has any given `k`-block i.o. in `m·α`** |
| **`mahler_multiplier_of_pred_runs`** | same for `(g−1)ᵏ` (reflection `α ↦ −α`, `occursAt_neg_iff`) |

So for prime `g` the multiplier problem splits into a **run branch**, now
pinned `gᵏ − 1 ≤ M_run ≤ gᵏ` (the Liouville witnesses of
`MahlerLowerBound.lean` live there), and a **run-free branch** (no `0ᵏ`,
no `(g−1)ᵏ` eventually; orbit confined to `[g⁻ᵏ, 1 − g⁻ᵏ]`), which is
where ALL the remaining room `gᵏ … g^(k+1)` lives.  The proof is four
lines of arithmetic: `gᵏ·x = A + ε` with `A` invertible mod `gᵏ`, take
`m ≡ W·A⁻¹`.  (For composite `g` the same theorem holds with "predecessor
digit coprime to `g`" — that is exactly the hypothesis the divisor-family
witnesses `B = g/t`, `B = 125` violate.)

### The numerics (exact, `experiments/mahler_exact_M.py`)

An exact single-track adder machine (right-to-left deterministic carries,
state = `(k−1)`-digit window × carry vector; bug found and fixed on the
known case base 2 / `11` / channels `{1,2}`), run as an **incremental
trimmed product** (add one channel, keep only SCCs with `|E| > |V|`),
gives the least `M` such that channels `1..M` collapse for every block:

    g       2  3  4  5   6  7   8   9  10  11  13   14   15   16  17   18  19   20   21   22  23   24  25   26   27   28  29
    M(g,1)  1  2  6  6  20  9  28  24  72  25  35  104  126  120  64  272  80  304  224  336 120  414 189  400  375  500 192

    M(2,k) = 1, 3, 7, 17 (k = 1..4)   M(3,k) = 2, 8, 43 (k ≤ 3)   M(5,2) = 48

Cross-checks: B–B `M(3,1) = 2` ✓; divisor family exact for `g = 4, 8, 9`
(`6 = 2·3`, `28 = 4·7`, `24 = 3·8`) ✓; the `B = 125` witness is EXACT for
base 10 (`72 = 8·9`) ✓; base 24: `414 = 18·23`, base 26: `400 = 16·25`.
Per-digit values are in `experiments/mahler_exact_M_k1_g14plus.txt`.

**Odd primes: `M(g,1)` tracks `((g−1)/2)²`** — `9, 25, 36→35, 64, 81→80,
121→120, 196→192` for `g = 7, 11, 13, 17, 19, 23, 29`.  So `M(g,1) = Θ(g²)`
for primes; the conjecture "`Θ(gᵏ)` for prime `g`" (last lap's item 3) is
**refuted**.  The `g^(k+1)` upper bound has the right order for every
base; the constant is `≈ 1/4` for primes and up to `≈ 0.85` for
highly composite bases (`18: 272/324`).

**Mechanism of the prime witnesses (run-free, as the theorem demands):**
the orbit hops between rationals `p/q`, `q < g`, approached from BELOW,
all of whose multiples avoid the cell (`g = 23`, digit 0: `10/11 = 0.(20)`,
`11/12 = 0.(21 1)`, `7/10 = 0.(16 2 6 20)`, `1/11 = 0.(2)`).  A hop
`p/q → p''/q''` is possible when they are Farey neighbours
(`p q'' − p'' q = 1`) and costs `M ≤ (g − q)·q''`; a closed system needs
the `×g` cycles mod `q` and mod `q''` to connect the hops.  Maximised at
`q ≈ q'' ≈ g/2`, giving `≈ (g/2)²`.  For `g = 5, 7` (digit 1) the
witness is the golden-mean / full shift on digits `{2,3}`, realised by
`α = c/(g−1) + Σ_{i≥2} g^(−i!)` (`c = 2`): channels `1..5` (`g = 5`) and
`1..8` (`g = 7`) avoid digit 1 — checked by hand, both EXACT
(`M(5,1) = 6`, `M(7,1) = 9`).

### NEXT (the crux is now the prime-base LOWER side)

1. **Formal `Θ(g²)` witness for primes, `k = 1`.**  Cheapest first step:
   `α = 2/(g−1) + Σ_{i≥2} g^(−i!)` (periodic background + Liouville
   bursts) and digit `W = 1`: for `m ≤ M` the digits of `m·α` are those of
   `2m/(g−1)` (periodic, digit `2m mod (g−1)`) with `m` added at the
   burst positions — a finite check per `m`.  Gives `M(5,1) ≥ 6`,
   `M(7,1) ≥ 9` exactly; find its general value `f(g)` (probe: brute force
   over background `c/(g−1)` and burst `B`) and prove the family theorem
   in the shape of `mahler_lower_bound_general` (orbit form
   `{m·orbit} = {m c/(g−1) + m B g^(−d)}`).  Then the Farey-hopping family
   for `≈ g²/4` (needs a uniform choice of the two denominators; the data
   `((g−1)/2)²` suggests `q = (g−1)/2`, `q'' = (g+1)/2`).
2. **Exact small values as theorems.**  Upper halves (`M(5,1) ≤ 6`,
   `M(7,1) ≤ 9`) are collapse certificates of the kind the tower wing
   already checks in-kernel (`AdderTowerC*`); lower halves are the
   witnesses above.  Would make `M(5,1) = 6` the first exactly-known
   prime value beyond B–B's `M(3,1) = 2`.
3. **Composite `g` run theorem**: state `mahler_multiplier_of_zero_runs`
   with "predecessor digit coprime to `g`" (the orbit-form lemmas already
   are general; only the descent `exists_maximal_zero_run` uses "nonzero").
4. `B = 125` generalisation (`t·c = g^L`, `s·c` digit-`(g−1)`-free for
   `s < t` ⇒ `M(g,k) ≥ t(gᵏ − 1)`): base 10 → `8(10ᵏ − 1)`, exact at `k = 1`.
   This is B–B Example 3.1 / the `p^r/g` witness of their Theorem 3.2
   (`α = (p^r/g)·Σ g^(−nⱼ)`, `g^l < p^r < (1+ε)g^l`) — formalizing Thm 3.2
   itself (`(1 − ε)g^(k+1)` for non-prime-powers) would close the
   composite side to `(1−ε)g^(k+1) ≤ M ≤ g^(k+1) − 1`.

**Lean gotchas this lap.**  `Int.add_mul_emod_self_left` wants
`(a + b*c) % b`, so `add_comm` first.  `one_div_pow` needs explicit args
when used as a term.  `positivity` does not know `0 ≤ orbit g α n`; use
`(orbit_mem_Ico g α n).1`.  `set j₀ := Nat.find hex` does not rewrite a
later `Nat.find_spec hex`; ascribe the spec's type with `j₀` instead.
`Irrational.ne_zero`, `IsCoprime.pow_right`, `IsCoprime.neg_left`,
`Int.natCast_dvd`, `Nat.Prime.coprime_iff_not_dvd`,
`Int.isCoprime_iff_gcd_eq_one` all exist under these names.


## ✅ MAHLER LOWER BOUND SHARPENED TO `t·(gᵏ − 1)` — the factor-`g` gap collapses to ~2 (2026-09-02, autonomous)

**The chapter's open question is (mostly) answered, and the answer is on the
LOWER side.**  `MahlerLowerBoundGeneral.lean`:

| theorem | claim |
|---|---|
| `mahler_lower_bound_general` | for any `B ≥ 1`: `M(g,k) ≥ min{ m : m·B contains (g−1)ᵏ in base g }` |
| `mahler_lower_bound_divisor` | for any factorization `g = t·c`, `c ≥ 2`: **`M(g,k) ≥ t·(gᵏ − 1)`** |
| `mahler_lower_bound_even` | `g` even: **`M(g,k) ≥ (g/2)(gᵏ − 1)`** |

All trust triple.  Against `mahler_multiplier`'s `M(g,k) ≤ g^(k+1)` the
two sides are now within a factor `2 + o(1)` for every even base
(`45 ≤ M(10,1) ≤ 100`, `495 ≤ M(10,2) ≤ 1000`), where the previous state of
the chapter was `9 ≤ M(10,1) ≤ 100`.  The old `gᵏ − 1` is the `t = 1` case.

**The idea.**  `α = B · liouvilleNumber g` — then `m·α = (m B)·liouvilleNumber g`,
so every multiplier question collapses to ONE integer `N = m B`.  The base-`g`
expansion of `N · Σ g^(−i!)` is a copy of the digit string of `N` right-aligned
at each position `i!`, separated by huge zero gaps, so `(g−1)ᵏ` occurs i.o. in
`m·α` **iff** `(g−1)ᵏ` occurs as a substring of `m·B`.  The multiplier problem
becomes a digit problem about the multiples of a single integer.  Formally we
never touch digits: the arithmetic shadow of "no `k` consecutive `(g−1)`s" is
`∀ d ≥ k, N % g^d + g^(d−k) + 1 ≤ g^d`, and that is exactly what
`orbit_liouvilleMul_lt` consumes.

**Why `B = c` (a cofactor of `g`) wins.**  `m = q t + s` ⇒ `m c = q g + s c`
with `s c ≤ g − c ≤ g − 2`: the *last* digit of `m c` is never `g − 1`, so a run
must live inside `q = ⌊m/t⌋`, and the smallest integer containing `(g−1)ᵏ` is
`gᵏ − 1`.  Budget stretched by exactly the factor `t`.

**Numerics (probes, session scratch — 30 lines to re-derive).**  Brute force over
all `B ≤ 4·10⁵` for `g ≤ 12, k ≤ 2` reproduces `t(gᵏ − 1)` as the optimum in every
case; an independent exact-integer digit check of `α = 2·liouvilleNumber g`
confirms the theorem's own window (`m = t(gᵏ−1) − 1` clean at `n ∈ [600,720)`,
`m = t(gᵏ−1)` occurs at `n = 718`) — the bound is SHARP for this `α`.

**Left open (the new frontier of the chapter):**
1. **Odd prime bases.**  `t_max(g) = 1` for prime `g`, so for `g ∈ {2,3,5,7,11,…}`
   the lower bound is still `gᵏ − 1` while the upper is `g^(k+1)` — a factor `g`.
   B–B's `M(3,1) = 2 = gᵏ − 1` says the LOWER side is right there; so for prime
   bases the open work is on the UPPER side, and the binding case of the sweep is
   `q = 1` (see `MahlerMultiplier.lean`).  ⇒ **the prime-base upper bound is the
   crux now.**
2. **Beyond the divisor family.**  Brute force finds `B` that beat the best
   divisor when the low block merely avoids *runs* rather than the digit `g−1`
   (`g = 10`: `B = 125`, `t = 8` ⇒ `M(10,k) ≥ 8(10ᵏ−1)`, only `1.25×` below the
   upper bound; `g = 6, k = 2`: `B = 243` ⇒ `187 > 4·35`).  Formalizing the
   `B = 125` witness needs a finite `decide` check over `d ≤ k+3` — cheap, and it
   would make base 10 the tightest sandwich in the chapter.
3. Is `M(g,k) = Θ(g^(k+1))` for composite `g` and `Θ(gᵏ)` for prime `g`?  The
   heuristic count says a random `B` of length `L` survives to `M ≈ gᵏ ln g`.

**Lean gotchas.**  `maxHeartbeats` is per declaration: the first draft timed out at
three unrelated lines; splitting the two arithmetic branches of the cell estimate
into `cell_bound_ge` / `cell_bound_lt` fixed all three.  `omega` refuses `m / t`
and `m % t` with a *variable* divisor — package the division as
`∃ q r, m = t*q + r ∧ r < t` and everything downstream is linear.  `positivity`
cannot prove `0 < g ^ k` in ℕ without `0 < g` in context.  `field_simp` closed the
`(1 − 1/A − 1/(D·A))·(D·A) = D·A − D − 1` identity on its own; the trailing `ring`
then errored with "no goals".

## ✅ MAHLER LOWER BOUND `gᵏ − 1` PROVED — chapter now two-sided (2026-09-01, autonomous)

`Mahler.mahler_lower_bound` (`src/NormalNumbers/MahlerLowerBound.lean`):
for every `g ≥ 2` and `k`, there are irrational `α` and a `k`-digit block
`w` such that NO `1 ≤ m ≤ gᵏ − 2` has `w` occurring i.o. in `m·α` (in fact
`w` occurs at no position `n ≥ (k+2)!`).  Witnesses `α = liouvilleNumber g`
(mathlib: `liouville_liouvilleNumber` ⇒ irrational), `w = (g−1)ᵏ`.  Trust
triple.  Paired with `mahler_multiplier`:

    gᵏ − 1 ≤ M(g,k) ≤ g^(k+1)   — both sides machine-checked.

Proof never touches digits: `occursAt_iff_orbit_mem` reduces to
`{m α gⁿ} < 1 − g⁻ᵏ`; with `j! ≤ n < (j+1)!`, `d = (j+1)! − n ≥ 1`,
`m α gⁿ = (ℕ) + (m mod g^d)/g^d + T`, `T = m gⁿ·remainder g (j+1) < g^(−k−1)`
(`LiouvilleNumber.remainder_lt`), and `(m mod g^d)/g^d ≤ 1 − 2g⁻ᵏ` in both
regimes `d ≥ k` / `d < k`.  Claim hygiene: B–B 1994 are reported to have
`gᵏ − 1`; we state OUR quantifiers and do not attribute the statement.

Gotchas: `partialSum_eq_rat` casts `g ^ j!` as a ℕ (normalize with
`push_cast`); `((m / g^d : ℕ) : ℤ)` gets rewritten by `Int.natCast_div`
under `push_cast` — keep the integer part as a ℕ-cast and use
`Int.cast_natCast` at the `fract_eq_of_eq_int_add` call; `linarith` treats
`2 / g^k` and `1 / g^k` as unrelated atoms (bridge with `ring`).


## ✅ FURSTENBERG 1967 dense-orbit theorem WIRED (2026-09-01, autonomous)

`Literature.furstenberg_dense_orbit_holds` (`src/NormalNumbers/LiteratureFurstenberg.lean`):
for irrational `x` and `0 ≤ a < c ≤ 1`, some `{2^m 3^n x} ∈ [a, c)`.  Trust
triple.  The theorem behind it — ×p×q topological rigidity, `Y` closed and
`p•`,`q•`-invariant ⇒ finite or `univ` (`Furstenberg.isClosed_invariant_finite_or_univ`,
`src/NormalNumbers/Furstenberg.lean`, 1200 lines) — is a verbatim re-homing
(namespace + 4 lint fixes) of the author's `collatz-moonshot`
`Rigidity/Furstenberg.lean` (commit `4727694`; same mathlib `0df444a3`,
Lean `v4.33.1`), re-checked by this repo's kernel.  Route: Boshernitzan 1994
as presented in Manners arXiv:1305.1514 §4 (climb lemma + intersection
induction).  I had independently reconstructed the reduction (non-lacunarity
from `log 3 / log 2 ∉ ℚ`, spreading, rational-limit-point spreading with the
sub-semigroup `{t ≡ 1 mod q}`) before finding the corpus note
(`2026-08-26-lean-addcircle-rigidity-toolkit.md`) that the crux — forcing
accumulation at a torsion point — was already done there; porting beat
re-proving.  Bridge lemmas: `AddCircle.not_isOfFinAddOrder_iff_forall_rat_ne_div`,
`QuotientAddGroup.isOpenMap_coe`, `Dense.exists_mem_open`,
`AddCircle.coe_eq_coe_iff_of_mem_Ico`, and the file's own `coe_fract`.

Ledger: `Literature.lean` docstring marked WIRED; brief table row updated.
Remaining cited-only ledger nodes: see `BRIEF-literature-statements.md`
(`waldschmidt_conjecture_1_1` is OPEN, not a target).


## ✅ MAHLER'S THEOREM M — bound sharpened to `g^(k+1)` (2026-09-01, autonomous)

`NormalNumbers.Mahler.mahler_multiplier` (`src/NormalNumbers/MahlerMultiplier.lean`):
for every irrational `α`, base `g ≥ 2`, block `w` of length `k`, some
`1 ≤ m ≤ g^(k+1)` has `w` i.o. in `m·α`.  Trust triple, no sorries,
self-contained (imports only `Disjunctive`).  Supersedes the `(g+3)·gᵏ`
proof of `8afbd05` (which left `g = 2` short of Berend–Boshernitzan).

**The two insights that collapsed the constant** (both recorded in the
module docstring):
1. *Two-grid-point sweep* (`sweep_pos` + new `start_in_cell`).  If the
   progression through the grid point `j/q` just below the cell needs more
   than `M` multiples to climb into it, then the *next* grid point
   `(j+1)/q` is already inside the cell together with the start of its
   own progression.  Guaranteed once `(M+1−2q)|η| ≥ 1 − q/gᵏ`.  This makes
   the covering lemma **universal**: a bad `x` has
   `(M+1−2q)|qx−p| < 1 − q/gᵏ` for EVERY reduced `p/q`, `q ≤ gᵏ`,
   `|qx−p| < g⁻ᵏ` (`defect_bound_of_bad`), not just Dirichlet's.
2. *Shadow-rational escape* (`orbit_escapes`, rewritten).  With a universal
   covering lemma there is no need to show two nearby rationals coincide:
   follow `ρ' = gρ − ⌊g x_n⌋` (denominator divides `ρ.den`); the
   normalized defect is multiplied by exactly `g` by construction, and at
   `M = g^(k+1)` the covering bound contracts every quality-`g⁻ᵏ`
   approximation to quality `g⁻ᵏ/g` (`defect_contracts_of_bad`), so the
   shadow stays quality-`g⁻ᵏ` forever while its defect grows like `gⁱ`.

Numerically pre-checked (refined sweep: 5149 samples, 0 violations, min
slack 1).  The same argument gives `g^(k+1) − 1`; the method's floor is
`M ≥ 2gᵏ` (needed for `M+1−2q > 0`), and B–B's lower bound `gᵏ − 1` says
the truth is within a factor `g` of what we have.

**Ledger edges (`LiteratureMahler.lean`, axiom-clean):**
- `mahler_theoremM_holds` — Mahler 1973 Thm M for ALL `g ≥ 2`, no `(2,1)`
  special case any more.
- `berendBoshernitzan_bound_holds : berendBoshernitzan_bound` — B–B 1994
  `m ≤ 2g^(k+1)` for ALL `g ≥ 2` (the `g = 2` gap is closed).  ⚠️ The
  transcribed B–B constant is tier-S; "half their constant" is conditional
  on it — primary-source check requested in `ON-LINE-REQUEST.md`
  (2026-09-01).

**NEXT (open):** (a) once the B–B PDF is read, decide whether `g^(k+1)`
is genuinely new (their paper may already contain a bound of this shape;
never headline before checking); (b) can the factor `g` be attacked? The
sweep loses `2q` (one from the start-point offset `rη/q`, one from the
`⌊M/q⌋`-style floor); the escape needs `g|η| < g⁻ᵏ` only for the
*shadow's* denominator, which shrinks — a denominator-aware contraction
might reach `M ≈ (g−1)gᵏ + …`.  Low priority vs the ledger's cited-only
nodes (`furstenberg_dense_orbit` next).


## ✅ C10 tower claim PROVED via a REDUCTION FINDING (2026-09-01, autonomous)

`c10_disjunction_universal` (`src/NormalNumbers/AdderTowerC10.lean`) — the
last named tower claim, in the dossier's exact nine-disjunct base-5 form —
is proved kernel-tier, trust triple.  NOT by the dossier's 540 396-state
certificate: the family SPLITS (C5 pattern).  Irrational `Y` ⇒ the four
`Y`-only channels collapse alone (`c10_y_branch`, 24 ambient / 5 live);
rational `Y` ⇒ `Z = X+Y` irrational and the diagonal channels `Z,2Z,3Z,4Z`
avoiding digit 2 collapse alone (`c10_z_branch`, 24 ambient / 6 live).
`X+4Y` is unused.  Full two-track automaton also collapses in Python
(46080 ambient, 18 live) — verdict agrees with the dossier.  RESULT in
`BRIEF-adder-tower.md` (C10 addendum).  Tower brief now fully closed
(C1–C10).  Open follow-ups: novelty of the two single-track base-5
sub-claims vs Berend–Boshernitzan 1994 general-`g` (operator sweep).

## ✅ Aristotle faithfulness cross-check of `PiSqBBP` — PASSED (2026-09-01)

Project `7ee16d3a` (prose of Bailey Formula 29 only) returned
`HasSum (fun j => (1/16^j) * (16/(8j+1)^2 - 16/(8j+2)^2 - 8/(8j+3)^2
- 16/(8j+4)^2 - 4/(8j+5)^2 - 4/(8j+6)^2 + 2/(8j+7)^2)) (π^2)` — term-for-term
identical to `piSqTerm`/`PiSqBBP := HasSum piSqTerm (Real.pi^2)`.
Independent confirmation that `piSqBBP_proved` states the theorem.  (It
also proved it, via the same dilogarithm-reflection route; the returned
proof was NOT imported — ours is already axiom-clean in-kernel.)


## ✅ Merged + ledger deepened (2026-08-31, autonomous, master)

- `wip/pisq-bbp-decomp` MERGED to master (`3003362`, --no-ff per repo
  precedent); `piSqBBP_proved` axiom-clean, full build green.
- Ledger deepening (per DIRECTION mandate, statement-only): three new
  `Literature.lean` entries — `philipp_psi_mixing` (Philipp Satz 3 /
  Scheerer Thm 2.1, cylinder form; new `cfCylinderFrom` in CFDefs),
  `baileyMisiurewicz_strong_hot_spot` (B–M Thm 3.4, via `IsSeqHotSpot`/
  `bmHotSpotRatio`), `baileyMisiurewicz_strong_hot_spot_criterion`
  (Thm 3.5 uniform-C form). Commit `b71ed1b`.
- **Remaining ledger gaps** (never-fabricate): B–B `g^k−1` lower bound
  (quantifiers unpinned by secondary sources), Fisher–Schmidt 2014
  skew-product ergodicity (heavy geometric defs, PDF held). Next
  standing-mandate candidate: weigh against novel-proofs doctrine +
  check Literature.lean before claiming novelty.

## 🔬 Aristotle faithfulness cross-check of the merged headline (2026-08-31, in flight)

Post-merge, re-confirmed `piSqBBP_proved : PiSqBBP` is axiom-clean on master
(`[propext, Classical.choice, Quot.sound]`, no `sorryAx`). Then submitted the
**prose** of Bailey Formula 29 (never the Lean) to Aristotle for an independent
NL→formalization faithfulness check — the "one cross-check that carries value"
per the doctrine. **Project `7ee16d3a-f125-48f0-9381-d39b95c4ba42`.**
NEXT LAP: `aristotle show 7ee16d3a…` (or `download`), and check its statement
is logically equivalent to `PiSqBBP := HasSum piSqTerm (Real.pi^2)` with
`piSqTerm j = (1/16^j)·(16/(8j+1)² − 16/(8j+2)² − 8/(8j+3)² − 16/(8j+4)²
− 4/(8j+5)² − 4/(8j+6)² + 2/(8j+7)²)`. Do NOT trust any returned *proof*
without in-kernel `#print axioms`; the check here is statement equivalence only.

## ✅ B–M weak hot spot Thm 1.1 (full iff) VERIFIED (2026-08-31)

`baileyMisiurewicz_weak_hot_spot_holds` (`LiteratureBMStrong.lean`) — the
named headline "weak hot spot theorem" (`IsNormal b x ↔ ∃ B, ∀ intervals
limsup visit-freq ≤ B·length`) is now a fully machine-checked **iff** edge,
axiom-clean. `⟸`: specialise to b-adic intervals + `isNormal_of_visit_upper_bound`
(reusing `eventually_ratio_le_of_limsup_le` + `visitCount_le`); `⟹`: Wall's
`isNormal_iff_equidistributed_orbit` pins each limsup to `d−c` (`B=1`). The
repo previously held only "the b-adic corollary of one direction"; now the
whole theorem is independently verified. Ledger def + brief marked WIRED.

## ✅ B–M strong hot spot Thm 3.5 DISCHARGED into a verified edge (2026-08-31)

`baileyMisiurewicz_strong_hot_spot_criterion_holds`
(`src/NormalNumbers/LiteratureBMStrong.lean`) — the freshly-added ledger
node (Thm 3.5, uniform-`C` block-occurrence ⇒ normality) is now an
independently machine-checked **edge**, axiom-clean
(`[propext, Classical.choice, Quot.sound]`, no `sorryAx`). Proof routes the
block-occurrence hypothesis to the repo's proven `isNormal_of_visit_upper_bound`:
- `blockOfNat` + `blockNatVal_blockOfNat`/`blockOfNat_lt`/`length_blockOfNat`
  — the big-endian base-`b` `k`-digit word of `m < bᵏ` (round-trips);
- `matchesAt_iff_occursAt` + `occursAt_iff_orbit_mem` — block occurrence =
  b-adic-interval visit; `visitCount_eq_card_matchesAt` packages it;
- `eventually_visit_bound_of_limsup` — the analytic step: `limsup` bound +
  the clipped/unclipped gap (`card_filter_matchesAt_le`, `≤ |w|`) + vanishing
  boundary term `bᵏ|w|/n → 0` ⇒ the eventual visit bound.
Same "upgrade cite→verify" move as `adamczewskiRampersad_boundary_holds`.
Ledger `def` + brief RESULT marked WIRED.

## 🧭 Graph-frontier state audit (2026-08-31, autonomous)

Verified the ln-2 run tower (the `DIRECTION.md` sink-path frontier):
- Tier-1 `LnTwoExpSep` is **discharged**, `lnTwoRun_le_unconditional_sharp`
  (**binary `ln 2` runs at `n` ≤ 9n, unconditional**) + `_holds`/`_sharp`
  all **axiom-clean** (`[propext, Classical.choice, Quot.sound]`, no
  `sorryAx`) — re-verified in-kernel this lap.
- **β<9 sharpening is pin-walled** (route named in `LnTwoExpSepSharp`
  header): needs PNT-strength `lcm(1..ℓ) ≤ e^{(1+ε)ℓ}`, but mathlib
  v4.33.1 has no PNT — `Chebyshev` tops out at `theta_le_log4_mul_x`
  (= the `4^ℓ` already used) and `psi_le_const_mul_self` (worse). Recorded
  in `docs/lnTwo-kick-blueprint.md` §5 item 6. Future β<9 needs PNT ported
  first (machinery wall).
- **Weakest genuinely-open nodes on the sink path** remain the
  equidistribution/disjunctivity hypotheses `LnTwoHypothesisFreq` /
  `LnTwoHypothesisLambda` / `LnTwoHypothesisD` and `Equidistributed
  lnTwoOrbit` — these ARE normality/disjunctivity of `log 2` (hard-open);
  Tier-2 `LnTwoPolySep` is Mahler-class open. No cheap edge available.


## ✅ PiSqBBP lane-2 node FULLY PROVED, axiom-clean (2026-08-31, autonomous)

`piSqBBP_proved : PiSqBBP` (Bailey Formula 29, `HasSum piSqTerm π²`) is
DISCHARGED — `#print axioms` = `[propext, Classical.choice, Quot.sound]`,
no `sorryAx`.  mathlib had no dilogarithm, so the full theory was built:
`Li2` + summability, term-wise derivative (`hasDerivAt_Li2'`:
`Li₂'w=−log(1−w)/w`), duplication (`dilog_add_neg`), the **reflection
formula** (`dilog_reflection`, via `F'≡0` on the lens `ball 0 1 ∩ ball 1 1`
+ constant pinned by the `t→0⁺` limit using Abel/`hasSum_zeta_two`),
`dilog_special_values`, and the fiber assembly.  All in
`src/NormalNumbers/PiSqBBPProof.lean` on branch `wip/pisq-bbp-decomp`.
The history below records the incremental laps.

## 🔻 (historical) PiSqBBP lane-2 crux narrowing (2026-08-31, autonomous)

`src/NormalNumbers/PiSqBBPProof.lean` (branch `wip/pisq-bbp-decomp`).
Node `piSqBBP_proved : PiSqBBP` (Formula 29, `HasSum piSqTerm π²`) is now
a fully-structured proof resting on a SINGLE disclosed `sorry`.

**Machine-checked axiom-clean this run:**
- Degree-2 roots-of-unity filter `w2 n = (−16·xⁿ+16·z₁ⁿ−16·(−x)ⁿ+16·z̄₁ⁿ)/n²`
  — the SAME four points as `PiBBP` (DFT of the Formula-29 coeff vector
  is supported on frequencies {0,1,4,7}, real integer weights; verified
  in `experiments/pi_sq_bbp.py`).
- `dilogSummable` (dilog series summable on open disk), `w2_block`,
  `num0..num7` (residue algebra over I²=−1, x²=½), `hasSum_fiber2`
  (∑_{r<8} w2(8j+r)=piSqTerm j), assembly via `divModEquiv` +
  `HasSum.prod_fiberwise`.
- `dilog_add_neg` : `Li₂ z + Li₂(−z) = ½·Li₂(z²)` — pure even/odd series
  split, NO special functions (axiom-clean).
- `hasSum_w2` analytic convergence PROVEN; value reduced via
  `dilog_add_neg` to the crux below.

**The one remaining `sorry` — `dilog_reflection`** (2026-08-31, further
narrowed): `Li₂ z + Li₂(1−z) = π²/6 − log z·log(1−z)` for `z, 1−z` both
in the open unit disk.  **Foundation now built (2026-08-31, axiom-clean):**
`hasDerivAt_Li2` (term-wise derivative of the `Li2` tsum on any sub-ball,
via `hasDerivAt_tsum_of_isPreconnected` + geometric bound),
`tsum_Li2_deriv` (its closed form `−log(1−w)/w` for `w≠0`, via
`Complex.hasSum_taylorSeries_neg_log`), and `hasDerivAt_Li2'`
(`HasDerivAt Li2 (−log(1−w)/w) w`), and **`hasDerivAt_dilogRefl`**
(2026-08-31, axiom-clean): `HasDerivAt (fun w => Li₂ w + Li₂(1−w) +
log w·log(1−w)) 0 z` on the region `‖z‖<1 ∧ ‖1−z‖<1 ∧ z,1−z ∈ slitPlane`
— the F'≡0 core.  **Constancy now PROVED (2026-08-31, axiom-clean):**
`lensL := ball 0 1 ∩ ball 1 1` (= `{‖z‖<1 ∧ ‖1−z‖<1}`) is convex/open and
`mem_slitPlane_of_mem_lensL` shows `lensL ⊆ slitPlane` (a real point of the
lens has `0<re<1`), so `hasDerivAt_dilogF` holds on all of `lensL` and
`dilogF_const` (`IsOpen.is_const_of_fderiv_eq_zero`) gives `F` constant on
the lens.  `dilog_reflection` is now `dilogF_const z ½` + `dilogF_value`.
**THE ONE REMAINING `sorry` — `dilogF_value`:** `dilogF(½) = π²/6`
(equivalently `2·Li₂(½)+log²(½)=π²/6`; and `C=π²/6` IS the whole content —
target `−8Li₂(½)+16(Li₂z₁+Li₂z₂)=π²` ⟺ `12C−π²=π²`).  **Next attack:**
`dilogF` is constant on `lensL`, so `dilogF(½) = lim_{t→0⁺} dilogF(t)`
(t real, `t ∈ lensL` for `0<t<1`; use `dilogF_const` + a `Tendsto` of the
constant, OR `ContinuousWithinAt`).  `dilogF(t) = Li₂ t + Li₂(1−t) +
log t·log(1−t)`: `Li₂ t → Li₂ 0 = 0` (Li2 continuous at 0), `Li₂(1−t) →
π²/6` via **Abel** `Real.tendsto_tsum_powerSeries_nhdsWithin_lt` with
coeffs `1/n²` and partial sums `→ π²/6` (`hasSum_zeta_two`), and
`log t·log(1−t) → 0` (`log(1−t) ~ −t`, `t·log t → 0`).  Assemble the three
limits, uniqueness of limits pins `dilogF(½)=π²/6`.  `dilog_special_values` is PROVEN from `dilog_reflection`
(reflection at `z=½` self-dual and at `z=z₁` with `1−z₁=z̄₁`, using the
`PiBBPProof` log values `log z₁=−½log2+(π/4)i`, `log z₂=−½log2−(π/4)i`,
`log ½=−log2`; all arithmetic machine-checked, `linear_combination` over
`I²=−1`).  So the ENTIRE π² node now rests on this one functional
equation.  **Obstruction:** mathlib has NO dilogarithm.  **Next attack:**
prove `dilog_reflection` for the local `Li2` via term-wise derivative —
`HasDerivAt Li2 (−log(1−w)/w) w` on the disk (differentiate the `tsum`;
`Mathlib/Analysis/Calculus/SmoothSeries.lean` `hasDerivAt_tsum` or the
power-series `HasFPowerSeriesOnBall.hasDerivAt`), then `F z := Li₂ z +
Li₂(1−z) + log z·log(1−z)` has `F'≡0` on the (connected) slit disk, so
`F` is constant `= π²/6` (limit `z→0`, `Li₂ 0=0`, `Li₂ 1 = ∑1/n² =
π²/6` — mathlib `hasSum_zeta_two`/basel).  Fallback: cite the reflection
formula as a lane-2 node (Lewin, *Polylogarithms* eq. 1.11).


## ✅ Tower C1–C8 COMPLETE (2026-08-30, autonomous)

All eight tower claims proved kernel-tier (RESULT table at top of
`BRIEF-adder-tower.md`; handoff `HANDOFF-2026-08-30-tower-complete.md`).
Base-g engine: `AdderBaseG.lean` (`signed_engine_g`,
`signed_engine_g_single`), emitter `experiments/adder_baseg_emit.py`.
No non-collapse findings; C1/C3 lane-2 cited (B–B 1994), C2 novelty
under check.  NEXT: `BRIEF-literature-statements.md` (ledger + wire
`c1_ternary_digit` → B–B M(3,1)=2 edge), then standing mandate.

## ✅ Adder operator addendum COMPLETE (2026-08-30)

All three briefs discharged, every theorem trust-triple; see
`HANDOFF-2026-08-30-adder-briefs-complete.md` and the RESULT sections of
`BRIEF-adder-disjunction-formalization.md`, `BRIEF-adder-universal.md`,
`BRIEF-adder-signed-engine.md`.  Headline surface: `adder_sixfold_disjunction`
(+ universal + engine-instance forms), `signed_engine`,
`adder_musical_disjunction` (+ universal).  Next attack (pending operator
authorization / altitude lap): k-track channels, other bases, word-sets —
listed out-of-scope in the signed brief; otherwise resume the conjecture-graph
objective (ln-two ladder / run tower / Diophantine-wall interface).

## 🔨 Adder six-fold disjunction (BRIEF-adder-disjunction) — lap 2026-08-30

Executing `BRIEF-adder-disjunction-formalization.md` per the DIRECTION operator
addendum, from `HANDOFF-2026-08-29-adder-foundation.md`.  Landed this lap
(both green, committed on `wip/adder-disjunction`):

1. `AdderShadow.lean` — true state (`winCode`/`chanCode`/`famState`) +
   **shadowing lemma** (`famState_shadow`, `hstep_famState`, `famState_lt`);
   bit-list injectivity `bitsVal_inj` turns the formed-window test into
   `OccursAt`.  Note: `winCode z m k` takes the digit COUNT (channel window
   = `winCode z m (ell-1)`, formed window = `winCode z m ell`).
2. `AdderCert.lean` + `AdderCertToy.lean` — generic `checkCert` sweep over
   `(σ, s')` with C1/C1'/C3' extraction lemmas; toy 16-state certificate
   passes **kernel `decide` in ~1s**, `#print axioms` = `[propext]`.
   Module-3 route settled at toy scale.

**DONE 2026-08-30 (later same lap):** `AdderDescent.lean` (module 4) and
`AdderEndgame.lean` (module 5 generic engine) are green.  **`toy_disjunction`
is proved END-TO-END, kernel tier, trust triple**
`[propext, Classical.choice, Quot.sound]` — the whole pipeline
(carry/shadow/certificate/descent/endgame) is validated.  Remaining:
`AdderCertMain.lean` (73728-state certificate, native_decide phase-1) +
`AdderMain.lean` (frozen six-fold statement) + RESULT in the brief.

**Historical next-attack notes (now executed):**
3. `AdderDescent.lean` — from an infinite HStep path with states `< famSize`
   + checked conditions ⇒ eventually periodic state AND input sequences
   (C3' ω-descent kills dead states; ρ non-increasing, finitely many drops;
   beyond last drop steps = `forced`, pigeonhole).  No König needed.
4. `AdderEndgame.lean` — eventually periodic σ ⇒ periodic `rdigit X` ⇒
   `2^N(2^p−1)·log 2 ∈ ℤ` ⇒ contradiction with `irrational_log_two`
   (Legendre route, ALREADY LANDED — do not use lnTwoExpSep, see
   route-correction in the foundation handoff).  Constants via `Real.log_mul`.
5. `AdderCertMain.lean` — 73728-state certificate (JSON at
   `experiments/certs/adder_cert_main.json`), `native_decide` phase-1,
   kernel stretch.  Then `AdderMain.lean` frozen statement + RESULT in brief.


## ✅ Phase 3 publishing-prep pass — 2026-08-26

The facts-first metadata audit and production comparator harness are complete.
Active prose now records image-Khinchin, Track D, and
`IsNormal.isDisjunctive` as complete; `ae_tail_average_tendsto` is proved, and
the older open-crux material below is explicitly historical. The
formal-conjectures correction is PR-ready local sibling work (definition fix
`c6126c56`, empty-block test follow-up `5d5832d0`), not an upstream merge. The
Champernowne contribution remains staged and externally unpublished.

The exact Wall and conditional ln-two theorems are in a strong-pattern
comparator harness: Mathlib-only Challenge with faithful real definition
bodies, import-only Solution, three semantic anchors, exact trust-triple
whitelist, nanoda enabled, non-default Comparator library, pinned Linux CI,
and a local identity probe with a missing-name teeth test. Both full builds,
all five identity closures, the teeth test, exact headline axiom gates, config
and YAML checks, and the independent artifact audit pass locally. The complete
pinned landrun/lean4export/comparator binary set is not available offline, so
the landrun + nanoda end-to-end invocation was not run locally and remains the
configured CI gate.

No mathematical proof work is pending in this phase. External publication,
the two prepared PRs, and the Zulip announcement are operator-owned. Preserve
the two known-false bypassed `CFScheduleA.lean` sorries.

Everything below is retained as historical proof-campaign state.

## ✅ Track D3 operator override complete — 2026-08-26

The boxed Track D objective is complete.  `IsNormal.isDisjunctive` was first
landed separately in `b755fd5`.  `QuadraticDisjunctive.lean` contains the
faithful named Prop `QuadraticHypothesisM`, the explicit closed
forward-invariant missing-word subshift, the endpoint-safe cover, and the
proved Hausdorff-cost decay.  The exact wrapper
`quadratic_irrationals_disjunctive_of_hypothesisM` consumes only
`QuadraticHypothesisM b` (besides `b ≥ 2`) and concludes that every quadratic
irrational is `b`-disjunctive.  Guarded `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]`; the full build passes at 8766 jobs.
The two known-false `CFScheduleA.lean` sorries remain untouched as required.

## ✅ 2026-08-25 (grind lap, post-completion) — headline faithfulness RATIFIED + Track D0 opened

The image-Khinchin directive crux is DONE and kernel-verified this lap (`#print axioms`
= trust triple, no `sorryAx`); build 🟢 8762. The only remaining `src/` sorries are the two
FALSE/REFUTED dead schedule stubs (`CFScheduleA.lean:4400`,`:5774`) — directive-forbidden,
provably unprovable (their RHS is beaten by the LHS for large n; B6 proved via the measure
route instead), so the anti-premature-quit gate cannot be cleared by proving them. An
altitude lap must retarget or ratify completion.

**Two genuine advances this lap (both non-forbidden, real value):**

1. **Faithfulness cross-check of the headline (endorsed NL→formalization).** Handed Aristotle
   ONLY the English prose of the image-Khinchin statement (never the Lean). Its independent
   formalization reproduced the EXACT logical content: for every countable `Q ⊆ ℝ×ℝ` with
   `0<q`, `∃ x ∈ Ioo 0 1` that is CF-normal ∧ Khinchin-typical ∧ every affine image `q·x+r`
   ((q,r)∈Q) CF-normal — with matching CF-normal (block-frequency), Khinchin-typical
   (geometric-mean → Khinchin constant), and affine-image definitions. Independent confirmation
   that `exists_cfNormal_khinchinTypical_and_affine_family_cfNormal` faithfully states the theorem.
   (Aristotle project `6d56b648`.)

2. **Track D0 opened — `Disjunctive.lean` (roadmap "orbit dictionary", `docs/conditional-disjunctivity.md` §0).**
   The topological twin of Wall's theorem, self-contained (imports only `RealDefs`), axiom-clean:
   - `IsDisjunctive b x` — interval-visit form: every `[a,c) ⊆ [0,1)` is visited by the orbit
     `n ↦ bⁿx mod 1` (the density weakening of `Equidistributed (orbit b x)`).
   - `orbit_mem_Ico`, `orbit_fract` (local copy), `isDisjunctive_fract`.
   - **`isDisjunctive_iff_denseOrbit`** — `IsDisjunctive b x ↔ Ico 0 1 ⊆ closure (range (orbit b x))`,
     the "dense orbit ⟺ disjunctive" equivalence (fully proved). This is the base layer the
     conditional-disjunctivity axioms (Λ, D_w) will sit on. Next D0 bricks: `omegaLimit` basics
     (closed + forward-invariant), and the D1 0-1 law (`λ(K)>0 ∧ closed ∧ T_b K ⊆ K ⟹ K = [0,1)`)
     via b-adic Lebesgue density.



## 🚧 2026-08-25 (review lap #3) — image-Khinchin crux: decorrelation core LANDED, variance→a.e. chain remaining

> **Historical snapshot, superseded later the same day.** The crux described in
> this section is proved; see the completion entry above. It is not active work.

**The ONE open obligation across the whole repo**: `ae_tail_average_tendsto K`
(`CFAeKhinchin.lean:343`), `∀ᵐ x ∂γ, logBirkhoffSum K n x / n → ∫ logTailFn K dγ`. Only
`K=0` consumed (g-direct) ⇒ closes `ae_khinchinTypical` (+sorryAx) ⇒ image-Khinchin headline
(graft into `exists_cfNormal_and_affine_family_cfNormal'`). A strong law for the UNBOUNDED
log-digit function under the Gauss measure — L²→a.e. variance route mirroring PROVEN `ae_orbit_freq`.

**Route = FINITE TRUNCATION (Approach B)** — reduces the second moment to Finset algebra + one
MCT limit, sidestepping fragile nested `integral_tsum`. Notation: `A_a := cfCylinder [K+1+a]`,
`u_a := log(K+1+a)`, `f_M := Σ_{a<M} logTailTerm K a`, `S_n^M := Σ_{i<n} f_M∘gaussMapⁱ = Σ_{a<M} u_a·blockCount(A_a) n`.

**LANDED this lap (both axiom-clean, `CFAeKhinchin.lean`, green 8760→8746 partial):**
- `integral_blockCount_cross A B` : `∫ blockCount A n·blockCount B n dγ = Σ_{i,j<n} γ.real(T⁻ⁱA∩T⁻ʲB)`
  (+ helpers `blockIndic_iterate_mul₂`, `integrable_blockIndic_iterate_mul₂`). Cross of `integral_blockCount_sq`.
- `abs_cov_two_cyl_pair_le a b (ha) (hb) {i j} (hij:i≠j)` : `|γ.real(T⁻ⁱ[a]∩T⁻ʲ[b]) − γ[a]γ[b]| ≤`
  `4·(9/10)^{dist(i,j)∸1}·(|[b]|γ[a] + |[a]|γ[b])`. Symmetric bound covers i<j and i>j (each branch
  reduces via `gaussMeasureReal_pair_shift₂` to an aligned gap, then `abs_cov_two_cyl_le`).

**LANDED lap #3b (green, axiom-clean):** sub-lemmas `integral_logBirkhoffTrunc_sq` (2nd-moment
expansion), `sq_logTruncMean_eq` (squared mean), constants `logTailC1/2/3` + summabilities +
nonneg, `logVarConst K = C₃+C₁²+176C₁C₂`, `sum_logMul_gaussMeasure_inter` (disjointness collapse),
and **`inner_pair_bound`** — the covariance FOLD: `|Σ_{j,j'}(γ.real(T⁻ʲ[K+1+a]∩T⁻ʲ'[K+1+b])−γ_aγ_b)|
≤ n(γ(A∩B)+γ_aγ_b) + 88n(vol_bγ_a+vol_aγ_b)` (diagonal j=j' via measure-preservation; off-diag folds
brick 2 via sum_range_dist_le+geom_trunc_sum_le). This is the hard analytic core.

**BRICK 3 DONE (green, axiom-clean):** `variance_truncated_le K M n : |∫(S_n^M)² − (n·μ_M)²| ≤ n·logVarConst K`,
UNIFORM in M. Assembly landed via hΔ + nested-abs + `inner_pair_bound` + `sum_logMul_gaussMeasure_inter`
(collapse) + `(summable_logTailC*).sum_le_tsum` partial bounds + final `gcongr`.

**REMAINING (hardest-first, next laps):**
1. `variance_logBirkhoffSum_le K n` : `|∫(logBirkhoffSum K n)² − (n·μ)²| ≤ n·logVarConst K` via MCT
   M→∞. Need `S_n^M := logBirkhoffTrunc K M n ↑ logBirkhoffSum K n` a.e. (pointwise: `logBirkhoffTrunc`
   is `Σ_{a<M} log(K+1+a)·blockCount[K+1+a] n`, and `logBirkhoffSum K n x = Σ_{i<n} logTailFn K(Tⁱx)`;
   the truncation ↑ the full via `logTailTerm_tsum_ae_eq` at each `Tⁱx` — but likely cleaner: show
   `logBirkhoffTrunc K M n = Σ_{i<n} (Σ_{a<M} logTailTerm K a)∘Tⁱ` and `(Σ_{a<M} logTailTerm K a) ↑ logTailFn K`).
   Then `∫(S_n^M)²↑∫(logBirkhoffSum)²` (MCT: `MeasureTheory.integral_tendsto_of_tendsto_of_monotone`
   or lintegral+`lintegral_iSup`; limit integrable via the uniform bound `≤(nμ)²+n·logVarConst`), and
   `logTruncMean K M → ∫ logTailFn K = logTailC1 K = μ` (partial sums → tsum). Pass the bound to the limit.
   ALT (maybe cleaner, avoids identifying μ): keep the RHS `n·logVarConst K` (M-independent) and only
   need `∫(S_n^M)² → ∫(logBirkhoffSum)²` and `logTruncMean K M → μ` where `μ = ∫ logTailFn K` (from
   `integral_logTailFn_eq_of_hasSum`; note `μ = logTailC1 K`).
2. `chebyshev_logBirkhoffSum` + `ae_tail_average_tendsto` : TRANSCRIBE `chebyshev_blockCount` +
   `ae_orbit_freq` (`CFAeNormal.lean:81`), `blockCount A p`↦`logBirkhoffSum K p`, `γv`↦`μ`, variance
   const `(8|v|+80)γv`↦`logVarConst K`. Monotone gap-squeeze OK (`logBirkhoffSum_nonneg`, ↑ in n).
3. Graft ⇒ image-Khinchin headline; re-`#print axioms` clean.
   OLD note (superseded, kept for context): `|∫(S_n^M)² − (n·μ_M)²| ≤ n·(C₃+80C₁C₂)` UNIFORM in M. Via
   `integral_blockCount_cross` (S_n^M is a finite Σ_{a,b} u_a u_b blockCount·blockCount). Split
   `Σ_{i,j}` diagonal i=j (⇒ `n·Var(f_M) = n·(∫f_M²−μ_M²) ≤ n·∫f_M²`; distinct A_a,A_b DISJOINT so
   cross a≠b vanish at m=0, `∫f_M² = Σ_a u_a²γ(A_a) ≤ C₃`) vs off-diag i≠j (bound each via brick 2,
   fold `Σ_{i≠j}(9/10)^{dist∸1}` with `sum_range_dist_le`+`geom_trunc_sum_le`, `|v|=1`). Constants:
   `C₁=Σ' u_aγ(A_a)` = tail of `summable_gaussKuzmin_log`; `C₂=Σ' u_a·vol(A_a)` = `summable_logMul_vol_cfCylinder`;
   `C₃=Σ' u_a²γ(A_a)` = `summable_sqLog_gaussMeasure_cfCylinder`. Finite partial sums ≤ tsum (nonneg, `sum_le_tsum`).
2. `variance_logBirkhoffSum_le K n` : MCT M→∞. `S_n^M ↑ logBirkhoffSum K n` a.e. — need
   `logTailFn K (Tⁱx) = Σ'_a u_a 1_{A_a}(Tⁱx)` a.e. (`logTailTerm_tsum_ae_eq` at `Tⁱx`; γ-preserving,
   finite intersect over i<n), so `f_M∘Tⁱ ↑ logTailFn K∘Tⁱ`, sum over i<n. Then `∫(S_n^M)² ↑ ∫(logBirkhoffSum)²`
   (MCT, `MeasureTheory.integral_tendsto_of_tendsto_of_monotone` or `lintegral_iSup`), `μ_M→μ`
   (from `integral_logTailFn` partial sums), pass the uniform bound to the limit.
3. `chebyshev_logBirkhoffSum` + `ae_tail_average_tendsto` : TRANSCRIBE `chebyshev_blockCount` (Markov on
   `(S−nμ)²`) + `ae_orbit_freq` (`CFAeNormal.lean:81`), `blockCount A p`↦`logBirkhoffSum K p`, `γv`↦`μ`.
   Monotone gap-squeeze OK (`logTailFn K ≥ 0` ⇒ `logBirkhoffSum K n` ↑ in n, `logBirkhoffSum_nonneg`).
4. Graft ⇒ image-Khinchin headline; re-`#print axioms` clean.

**Watch-outs**: (a) diagonal m=0 does NOT obey the `4vol[b]γ[a]` bound (fails at a=b, large a) — MUST
split it out as the `C₃` term, not fold into brick 2. (b) `gaussMeasure.real` vs `.toReal`: equal by
`measureReal_def`, bridge with `rw [MeasureTheory.measureReal_def]` (as in `abs_cov_two_cyl_pair_le`).
(c) MCT needs the limit integrable — the uniform bound gives `∫(logBirkhoffSum)² ≤ (nμ)²+nC < ∞`.

## 🎉 2026-08-25 (Tier-2 grind) — B6 TIER 2 LANDED: `exists_cfNormal_and_affine_family_cfNormal` AXIOM-CLEAN

New file `src/NormalNumbers/CFAffineFamily.lean` (sorry-free, build 🟢 8759). Extends the
single-map measure route to a **countable FAMILY** of affine maps simultaneously:

> `(Q : Set (ℝ×ℝ)) (hQ : Q.Countable) (hqr : ∀ p∈Q, 0<p.1 ∧ 0≤p.2) →`
> `∃ x∈(0,1), IsCFNormal x ∧ ∀ p∈Q, IsCFNormal (affineMap p.1 p.2 x)`

`#print axioms` = trust triple. Structure:
- **Crux `volume_notCFNormal_Ici0`**: the non-CF-normal set is Lebesgue-null on all of `[0,∞)`.
  Proof: `(0,1)`-nullity `volume_notCFNormal_Ioo01` (from `ae_isCFNormal` + `volume ≤ C·γ` on
  `(0,1)`) + positive integer-shift invariance (`isCFNormal_add_nat`): every bad `w≥0` is a
  nonneg integer or an integer translate of a bad point in `(0,1)`, so `N∩[0,∞)` is covered by
  `⋃ₙ (·+n)''(N∩(0,1)) ∪ range(ℕ↪ℝ)`, all null (translate = `affineMap 1 (-n)⁻¹`, reuse
  `volume_preimage_affineMap`).
- `gaussMeasure_notCFNormal_affine_Ioo01`: each `{x∈(0,1)|¬IsCFNormal(ψx)}` is γ-null (ψx>0 on
  the domain lands in `[0,∞)`; pull the null superset back, `γ≤C·vol`).
- Assembly: `measure_biUnion_null_iff` (Q countable) + `measure_sdiff_null` + `γ(0,1)>0`.

**✅ DONE (same grind) — FULL generality `exists_cfNormal_and_affine_family_cfNormal'` (any real `r`, `q>0`).**
The `r≥0` restriction is REMOVED, matching Vandehey §7 exactly. Crux upgraded to
`volume_notCFNormal_univ` (bad set Lebesgue-null on ALL of `ℝ`). Negative half avoided the
piecewise change-of-variables: the involution identity `gaussMap⁻¹(Z)∩Iio0 = inv''(Int.fract⁻¹Z∩Iio0)`
(inv is its own inverse on `Iio0`), `Int.fract⁻¹Z` null (`volume_fract_preimage_notCFNormal`,
ℤ-translate union), inv differentiable off 0, then `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`.
Axiom-clean (trust triple). Both family forms + single-map B6 + B5′ headlines untouched.

**🟢 DECOMPOSED (same grind) — image-Khinchin crux set up in `src/NormalNumbers/CFAeKhinchin.lean`.**
Target `ae_khinchinTypical : ∀ᵐ x ∂γ, KhinchinTypical x` (the co-null set to intersect into the
family witness). Reduction NAILED (no general ergodic theorem needed):
- `khinchinTypical_iff_log_tendsto` ⇒ suffices `(1/n)Σ_{i<n} log a_i → log K₀` a.e.
- Split at a FIXED cutoff `K`: `Σ log a_i = Σ_{a≤K} log a·#{i<n:a_i=a} + logBirkhoffSum K n x`
  (tail = `CFLogTail.logBirkhoffSum`, = `Σ_{i<n} log a_i·1[a_i>K]`).
- **Bounded part** → `Σ_{a≤K} log a·γ([a]) = Σ_{k<K} logTailG k` a.e.: FINITE sum of the singleton
  frequency limits `ae_digitCount_tendsto a` (= `ae_orbit_freq [a]`). **PROVED** this lap (leaf,
  axiom-clean).
- **Tail part** → `∫ logTailFn K dγ` a.e.: the ONE disclosed crux `ae_tail_average_tendsto K`.
- **Exact cancellation**: bounded-limit + tail-limit = `Σ_{k<K} logTailG k + ∫logTailFn K dγ =
  log K₀` for ANY fixed K, by `integral_logTailFn_eq_of_hasSum` + `HasSum logTailG (log K₀)`
  (`gaussKuzmin_logsum_hasSum`). No `K→∞` limiting. Pick e.g. K=0.

**ROUTE REORIENTED (cleaner) — g-DIRECT instead of the K-split.** The `logBirkhoffSum`/`logTailFn K`
tail device was for the FIRST-moment-only engine. For the L²→a.e. route it's simpler to target the
FULL log-digit `g(x) = log(cfDigit x 0)` directly: `g ≥ 0` (so its Birkhoff sum `S_n^g = Σ_{i<n} log a_i`
is MONOTONE in n ⇒ gap-squeeze applies), `g ∈ L²` (heavy tail is summable), and `∫ g dγ = log K₀`
(= `Σ_k logTailG k` via `gaussKuzmin_logsum_hasSum`). Then `khinchinTypical_iff_log_tendsto` closes
`ae_khinchinTypical` from a.e. `(1/n) S_n^g → log K₀`. No cutoff K, no `ae_tail_average_tendsto`.

BRICKS LANDED (all axiom-clean, serve the g-direct variance bound):
- `gaussMeasureReal_pair_shift₂`, `abs_cov_two_cyl_le` — two-distinct-cylinder mixing.
- `summable_logMul_vol_cfCylinder` (Σ log·vol), `summable_sqLog_gaussMeasure_cfCylinder` (Σ (log)²·γ,
  via `sq_log_le_sixteen_sqrt`) — the finite variance constants + `∫g²<∞` input.

**NEXT ATTACK (hardest-first):** the g-direct variance bound `variance_logDigitSum_le`:
`|∫ (S_n^g)² dγ − n²(log K₀)²| ≤ C·n`. Route: (i) `∫ g dγ = log K₀` and `∫ g² dγ < ∞` from the
disjoint-cylinder tsum expansion `g = Σ_a log a·1_{[a]}` (MCT / `integral_tsum` over disjoint
indicators, weights summable by the two bricks above). (ii) second moment
`∫(S_n^g)² = Σ_{j,j'<n} Σ_{a,b} log a log b·γ(T^{-j}[a]∩T^{-j'}[b])`, per-gap correlation
`|Cov(g,g∘Tᵐ)| ≤ (9/10)^{m∸1}·4·(Σ log γ)(Σ log vol)` from `abs_cov_two_cyl_le` + the two summability
bricks, then fold with `sum_range_dist_le`/`geom_trunc_sum_le` (reuse `variance_blockCount_le`'s
pattern) ⇒ `≤ C·n`. (iii) Chebyshev + Borel–Cantelli on `p=(k+1)²` + monotone gap-squeeze (as in
`ae_orbit_freq`) ⇒ `ae_khinchinTypical`. (iv) graft one co-null intersection into
`exists_cfNormal_and_affine_family_cfNormal'`. The `logBirkhoffSum`-based `ae_tail_average_tendsto`
sorry in `CFAeKhinchin.lean` is now SUPERSEDED scaffolding — leave it or delete when g-direct lands.

**OLD PLAN (superseded):** prove `ae_tail_average_tendsto K` (`CFAeKhinchin.lean:60`, disclosed
sorry). This is the L²→a.e. Borel–Cantelli of `ae_orbit_freq` applied to `logBirkhoffSum K` instead
of `blockCount`. Needs a **variance bound for the log-tail Birkhoff sum**:
`∫ (logBirkhoffSum K n − n·∫logTailFn K)² dγ ≤ C·n·(…)`. Build it from the SAME Gauss two-point
mixing behind `variance_blockCount_le` (`CFBlockFreq:401`): `logTailFn K = Σ_{a>K} log a·1_{cfCylinder[a]}`
so its Birkhoff-sum variance decomposes into the cylinder correlations already controlled. Then
Chebyshev + Borel–Cantelli on `p=(k+1)²` + the MONOTONE gap-squeeze (`logBirkhoffSum K n x` ↑ in n
since `logTailFn K ≥ 0`) — same skeleton as `ae_orbit_freq`. mathlib has NO pointwise-Birkhoff /
maximal-ergodic theorem, so this variance route (not an ergodic-theorem import) is the path.
Then assemble `ae_khinchinTypical` (the split identity `blockCount(cfCylinder[a]) = digit-count` +
finite-sum a.e. + the cancellation) and graft one more co-null intersection into
`exists_cfNormal_and_affine_family_cfNormal'` for the image-Khinchin headline.

**ALT stretch:** image-Khinchin — strengthen the witness so `x` is
additionally Khinchin-typical (the Khinchin-typical set is γ-co-null; intersect one more co-null
set in the SAME assembly). Cheap given `KhinchinTypical` a.e. infrastructure if present.

## 🎉 2026-08-25 (measure-route grind) — B6 COMPLETE: `exists_cfNormal_and_affine_cfNormal` is AXIOM-CLEAN

**The crux `ae_orbit_freq` is PROVED** (`CFAeNormal.lean`, sorry-free) — the classic L²→a.e. argument:
`chebyshev_blockCount` bound → Borel–Cantelli (`ae_eventually_notMem`) along `p=(k+1)²`
(∑1/(k+1)² summable via `summable_nat_add_iff`) per `δ=1/(m+1)`, intersected over `m`
(`ae_all_iff`) ⇒ a.e. convergence on the squares; then the monotone gap-squeeze
(`Nat.sqrt`, `Nat.sqrt_le'`/`lt_succ_sqrt'`, product-form limits `k²/(k+1)²→1` via
`tendsto_natCast_div_add_atTop`, `tendsto_of_tendsto_of_tendsto_of_le_of_le'`).

**Headline WIRED + FLIPPED CLEAN.** `exists_cfNormal_and_affine_cfNormal` (`CFScheduleA:6270`)
now consumes `exists_feasible_cfNormal_affine` in all three branches (feasible + two integer-shift);
`CFScheduleA` imports `CFAeNormal` (no cycle). Real `#print axioms` this lap:
- `exists_cfNormal_and_affine_cfNormal` → `[propext, Classical.choice, Quot.sound]` ✅ **DONE**
- `exists_absolutely_normal_cf_normal`, `_khinchin` → trust triple (untouched) ✅
- `ae_isCFNormal` → trust triple ✅

The schedule/two-stream chain (`schedA_block_linear` + 8 other refuted sorries) is now DEAD CODE —
the headline no longer flows through it. Kept in-src marked REFUTED per directive, NOT deleted.
**B6 (Vandehey §7 single affine map) is closed.** No open obligation remains on any headline.

---

## 🟢 2026-08-25 (measure-route grind) — LANDED: `CFAeNormal.lean` scaffold, B6 reduced to ONE a.e. crux

New file `src/NormalNumbers/CFAeNormal.lean` (build 🟢 8758). Fully proved, axiom-status modulo the
one crux sorry:
- `ae_irrational`, `ae_mem_Ioo` (γ supported on (0,1), rationals null) — DONE.
- `ae_isCFNormal : ∀ᵐ y ∂γ, IsCFNormal y` — DONE, assembled from the crux `ae_orbit_freq` via
  `ae_all_iff` over countable `List ℕ` + `isCFNormal_of_irrational_orbit_freq`.
- `exists_feasible_cfNormal_affine {q}(hq:0<q) r (hr:-q<r∧r<1) : ∃ x, IsCFNormal x ∧ IsCFNormal (ψx)`
  — **DONE**. Measurability of the CF-normal set is DODGED: `exists_measurable_superset_of_null`
  gives a measurable null superset `W⊆(0,1)` of `{¬IsCFNormal}∩(0,1)`; `volume_le_ofReal_mul_gaussMeasure`
  ⇒ `vol W=0`; `volume_preimage_affineMap` ⇒ `vol(ψ⁻¹W)=0`; `gaussMeasure_le_volume` ⇒ `γ(ψ⁻¹W)=0`.
  Feasible `F=Ioo lo hi` has `γ F>0`; `F⊆(F∩A∩B)∪(F∩Aᶜ)∪(F∩Bᶜ)` with the last two γ-null ⇒ nonempty.

**THE one remaining crux — `ae_orbit_freq` (`CFAeNormal:81`, disclosed sorry):** for genuine `v`,
`∀ᵐ y ∂γ, blockCount(cfCyl v) p y/p → γv`. Classic L²→a.e.: `chebyshev_blockCount` (already in
`CFBlockFreq:470`, gives `γ{|S_p/p−γv|≥δ}≤(8|v|+80)γv/(δ²p)`) + Borel–Cantelli
(`MeasureTheory.ae_eventually_not_mem`) along `p=(k+1)²` (∑1/(k+1)² summable) for each `δ=1/(m+1)`,
intersect over `m` ⇒ a.e. convergence along squares; then monotone gap-squeeze
(`p↦blockCount` nondecreasing, `Nat.sqrt`, `k²/(k+1)²→1`).

**NEXT:** (1) prove `ae_orbit_freq`. (2) wire: edit `exists_cfNormal_and_affine_cfNormal`
(`CFScheduleA:6270`) to consume `exists_feasible_cfNormal_affine` (add `import CFAeNormal` to
CFScheduleA — no cycle, CFAeNormal doesn't import CFScheduleA), keeping the 3-branch integer-shift
(re-`obtain ⟨x,hxN,hyN⟩` instead of the interleaved witness); then B6 is sorryAx-free, retire the
schedule `sorry`s as dead. (3) re-`#print axioms` both B5′ headlines (trust triple) + B6.


## 🚨 2026-08-25 (review lap #2b) — ROUTE PIVOT: schedule crux is FALSE → MEASURE route

**`variance_blockCount_psi_pushed` is PROVABLY FALSE** (`OBSTRUCTION-2026-08-25-variance-psi-pushed-FALSE.md`).
So the "step 1a/1c" plan in the section immediately below is **DEAD** — do NOT grind it. The restricted
2nd-moment identities landed in `a92dd8c` are still TRUE and axiom-clean (pure measure theory), but the
mixing bounds they were meant to feed are FALSE, so the whole `psi_pushed_*` chain is retired.

**NEW PLAN (B6 via the measure argument — `ROUTE-ESCALATION-2026-08-25.md`, DIRECTION.md CURRENT DIRECTIVE):**
the stated headline is bare existence, trivially true a.e.  Build in a NEW file `src/NormalNumbers/CFAeNormal.lean`:
1. **`ae_isCFNormal` (THE new crux):** `∀ᵐ y ∂gaussMeasure, IsCFNormal y`, via L²→a.e.:
   - per-word `v`: `variance_blockCount_le` (`CFBlockFreq:401`) + Chebyshev + Borel–Cantelli on `p=k²`
     + monotone-squeeze on gaps ⇒ a.e. `blockCount(cfCyl v) p ·/p → γv`;
   - intersect over countable valid `v` + a.e. orbit-in-`(0,1)` ⇒ `isCFNormal_of_orbit_freq`
     (`CFOrbitFreq:34`) ⇒ `IsCFNormal y` a.e.
2. **`ae_isCFNormal_affine`:** `∀ᵐ x, IsCFNormal(ψx)` via `ψ⁻¹` preserves γ-null
   (`volume_preimage_affineMap` `CFAffine:94` + γ≈volume bounded-density).
3. **Assemble** `exists_cfNormal_and_affine_cfNormal`: two co-null sets on the feasible interval meet ⇒
   witness; plug into the feasible branch (integer-shift reduction for `r∉(-q,1)` already present).
The schedule/explicit-witness chain (`variance_blockCount_psi_pushed`, `psi_pushed_*`, `_poly`,
two-stream `schedA_block_linear`, `exists_interleaved_affine_witness`) stays in `src` marked REFUTED,
NOT deleted, NOT to be attacked.

## 🟢 2026-08-25 (review lap #2) — LANDED: crux step 1a (restricted ψ-pushed 2nd-moment identities)

Committed `a92dd8c` (build green 8757, axiom-clean). In `CFScheduleA.lean` before the crux:
- `integral_blockCount_psi_restricted`   : `∫_S (S_n∘ψ) dγ  = Σ_{j<n} γ(S ∩ ψ⁻¹T^{-j}A)`
- `integral_blockCount_sq_psi_restricted`: `∫_S (S_n∘ψ)² dγ = Σ_{j,j'<n} γ(S ∩ (ψ⁻¹T^{-j}A ∩ ψ⁻¹T^{-j'}A))`
  (+ helpers `blockIndic_comp`, `measurable_affineMap`, `blockIndic_psi_mul`,
  `setIntegral_indicator_one_gaussMeasure`). Pure measure theory, NO mixing. These reduce the
  monolithic crux `variance_blockCount_psi_pushed` to **bounding the pair-correlation masses**
  `γ(cfCyl wx' ∩ ψ⁻¹T^{-j}A ∩ ψ⁻¹T^{-j'}A)` — the ψ-conjugated interval-base Gauss mixing.

**NEXT — crux step 1b (the hard core) + 1c (assembly). Concrete reduction of `variance_blockCount_psi_pushed`:**
Set `S=cfCyl wx'`, `A=cfCyl v`, `c=nγv`, `μ_j=γ(S∩ψ⁻¹T^{-j}A)`, `μ_{jj'}=γ(S∩(ψ⁻¹T^{-j}A∩ψ⁻¹T^{-j'}A))`.
Expand `(S_n∘ψ − c)² = (S_n∘ψ)² − 2c(S_n∘ψ) + c²`; integrate over S (each term is now a landed
identity + `∫_S c² dγ = c²·γ(S)` via `setIntegral_const`):
  `∫_S (S_n∘ψ−c)² dγ = Σ_{jj'} μ_{jj'} − 2c Σ_j μ_j + c²·γ(S)`.
The bound needs, per pair, TWO ψ-conjugated interval-base mixing facts (state as named sub-sorries):
  (1-pt) `|μ_j − γ(S)·γv| ≤ 4·γ(S)·γv·(9/10)^{?}`  [note: no `∸|v|` shift for 1-pt; the affine
         base has no cylinder depth — the decay index is `j` itself or `0`; work it out from CoV];
  (2-pt) `|μ_{jj'} − γ(S)·γv²| ≤ 4·γ(S)·γv·(9/10)^{Nat.dist j j' ∸ |v|}`  [the pair-correlation,
         mirror `abs_cov_pair_le`].
Then the same geometric fold as `variance_blockCount_le` gives `≤ (8|v|+80)·n·γv·γ(S)` PLUS a
`2c·|Σ_j μ_j − nγv γ(S)|` 1-point correction (absent in the full-measure model, where
`∫ S_n = nγv` EXACTLY; here it is only ≈, up to 1-pt mixing) — bound it by `2nγv·Σ_j(1-pt err)`,
also `O(n·γv·γ(S))`, absorbed by enlarging the constant if needed (check the `+80` slack).
**The mixing sub-sorries (1-pt, 2-pt) are step 1b, THE research core.** Route to prove them:
change-of-variables `y=ψx` turns `μ_{jj'}` into an INTERVAL-base (`J=ψ(S)`) pair-correlation in
`γ` times a bounded density ratio `ρ=gaussDensity(ψ⁻¹y)/(q·gaussDensity(y))` (elementary,
`CFAffine` + `gaussDensity` bounds); the content is then interval-base mixing = extend
`gaussMeasure_cylinder_mixing` (`CFGammaMixing:236`) from a `cfCylinder` base to a subinterval
`J⊆(0,1)`. If interval-base mixing is big, split it (cylinder-cover of `J` + per-cylinder mixing)
as its own named sorry. **Do step 1c (the algebra/assembly, given the two mixing sorries) FIRST**
next lap — it is landable now and further narrows the crux to exactly the two mixing statements.

## 🟢 2026-08-25 — LANDED: ψ(xA) irrationality (subtlety 1) + Z-I budget atom

- **`exists_xA_L4_psi_irrational`** (axiom-clean): the diagonalisation filler digit
  (StepSpecL4 rebuild) forces `ψ(xA)` irrational. Subtlety-1 CLEARED.
- **`exists_scale_cfCylinder_psi_avoid_zbad`** + **`exists_scale_zgood_wxSeq_L4`**
  (axiom-clean): Chebyshev budget discharge + per-stage z-good witnesses on `wxSeq_L4 s`.

## 🟢 2026-08-25 — LANDED: ψ-conditional z-Chebyshev (the crux analytic lemma)

**`chebyshev_blockCount_brick_psi_conditional`** (`CFWordBridge.lean`, axiom-clean, trust
triple). This is the "one genuinely-open analytic lemma the z-side rests on" flagged in the
CRUX FINDING below — now discharged. Statement: for `z ∈ cfCylinder wz` (`L=|wz|`), full-orbit,
`n>L`, and slack `2L ≤ δ·n`,
`γ{z ∈ cfCylinder wz : δ ≤ |blockCount(cfCyl v) n z/n − γv|}
  ≤ 7·(8|v|+80)·γv/((δ/2)²·(n−L))·γ(cfCylinder wz)` — the RELATIVE density `O(1/(n−L))`,
not the too-weak absolute `O(1/n)`. Proof route (as planned in the handoff): `blockCount_split`
peels the COMMON pinned-prefix count `C∈[0,L]` (perturbs the frequency by `≤ L/n`) off the
scale-`n` count, leaving the shifted scale-`(n−L)` count on `gaussMap^[L] z`, bounded by
`chebyshev_blockCount_brick` at base `wz`; the slack `2L≤δn` makes a scale-`n` `δ`-bad point a
shifted scale-`(n−L)` `(δ/2)`-bad point (subset + `measure_mono` + `ENNReal.toReal_mono`).

**Also landed (aggregate brick):** `gaussMeasure_aggregate_psi_cond_le` (`CFWordBridge`,
axiom-clean) — the finite-family (`F : Finset (List ℕ)`) union of the pinned-prefix
absolute-count bad sets is bounded by `∑_{v∈F} 7(8|v|+80)γv/((δ/2)²(n−L))·γ(cfCyl wz)`, the
`O(1/(n−L))` selection budget. Mirrors `gaussMeasure_aggregate_cfBadZone_le` with the conditional
brick swapped in for `chebyshev_blockCount_brick`. This is the exact aggregate the pinning-stage
selector consumes.

**Also landed (ψ-pullback selector):** `exists_cfCylinder_psi_avoid_zbad_cond` (`CFScheduleA`,
axiom-clean) — the relative-density counterpart of `exists_cfCylinder_psi_avoid_zbad`. Given the
pulled-back conditional z-bad budget on the cylinder hull is `< γ(cfCylinder wx')`, yields an
irrational `p ∈ cfCylinder wx'` whose ψ-image avoids EVERY pinned-prefix absolute-count bad set
`{z ∈ cfCylinder wz : δ ≤ |blockCount(cfCyl v) n z/n − γv|}` for `v ∈ F`. Same pullback plumbing
(`gaussMeasure_cfCylinder_inter_preimage_affineMap_le` + cylinder selector); caller discharges
`hbudget` from `gaussMeasure_aggregate_psi_cond_le`. This is the pinning-stage selector.

**Also landed (scale-threshold budget discharge):** `exists_scale_cfCylinder_psi_avoid_zbad_cond`
(`CFScheduleA`, axiom-clean) — the full conditional analog of `exists_scale_cfCylinder_psi_avoid_zbad`.
For genuine `wx'` (hull `[a,b]`), genuine pinned prefix `wz`, family `F`, `δ>0`, produces a threshold
`N` such that ∀ `n ≥ N` there is irrational `p ∈ cfCylinder wx'` whose ψ-image avoids every
pinned-prefix absolute-count bad set for `v ∈ F`. `N` bakes in `n>|wz|`, slack `2|wz|≤δn`, and
`n−|wz| > (2/q)·Ssum/((δ/2)²·γ(cfCylinder wx'))`. The complete pinning-stage z-selection engine is
now in the kernel; only the SCHEDULE-side wiring remains.

**Also landed (multi-scale interface):** `exists_cfCylinder_psi_avoid_zbad_cond_multiscale`
(`CFScheduleA`, axiom-clean) — the `NSz`-band generalization of the conditional selector, matching
the `exists_cfCylinder_psi_avoid_zbad` NSz shape. A single witness `p ∈ cfCylinder wx'` whose
ψ-image avoids the pinned-prefix bad sets across an ENTIRE finite band `NSz` of scales — the shape
the s↔n coupling needs (each stage certifies ψ-goodness over its whole window `(|w_{s-1}|,|w_s|]`).
`hbudget` is the harmonic-band total; feasibility left to caller.

## 🔴 2026-08-25 — CORRECTION (adversarial re-check): the tight discharge does NOT dissolve the obstruction

**The "DECISIVE" claim in the section below is REFUTED by a careful range/coverage analysis done the
next lap. The lemmas are all valid (correct conditional statements, axiom-clean, kept); only the
INTERPRETATION that they resolve the scale-regime obstruction was wrong.** Precise wall:

- Tight-discharge threshold: the witness `p` is z-good at scale `n` only for `n − |wz| > K` where
  `K = (2/q)·Ssum·Cbridge/((δ/2)²)` (a per-stage constant). So `n > |wz| + K`.
- Digit-agreement transfer (`notMem_cfBadZone_nil_of_cfDigit_agree` + `exists_tail_cfCylinder_subset_ball`):
  needs `n + |v| ≤ m`, where `m` = z-digits pinned by `cfCyl wx'`. Since `ψ` is `q`-Lipschitz and
  `cfCyl wx'` has width `~φ^{-2|wx'|}`, the ψ-image fits a depth-`m` z-cylinder only for `m ≲ |wx'| + O(1)`.
  So `n ≲ |wx'| − |v|`.
- Bridge constant: `Cbridge = γ(cfCyl wz)/γ(cfCyl wx') ~ φ^{2(|wx'| − |wz|)}`.

**The irreconcilable triangle:** bounded `Cbridge` ⟺ `|wz| ~ |wx'|` ⟹ threshold `n > |wx'|+K` while
transfer needs `n ≤ |wx'|−|v|` ⟹ range EMPTY. Conversely a non-empty range needs `|wz| < |wx'|` ⟹
`Cbridge` exponential ⟹ threshold `K` exponential ⟹ range empty again. And `tendsto_of_scale_coverage`
needs EVERY large `n` covered; a per-stage band of width `~|wx'_s|` (needed because block lengths, hence
`|wx'_s|`, grow geometrically leaving gaps) enters `Cbridge` exponentially. So the single-stream
conditional-at-base-`wz` route hits a density-vs-coverage wall.

## 🟢 2026-08-25 — CLEAN REDUCTION: the whole z-side now reduces to ONE disclosed crux brick

**`psi_pushed_chebyshev_brick`** (`CFScheduleA:~4270`, DISCLOSED SORRY — the ψ-pushed, x-cylinder-
relative Chebyshev; see its docstring for why it is the research-level crux). Everything above it is
PROVED modulo this one brick:
- **`gaussMeasure_aggregate_psi_pushed_le`** (axiom-clean given the brick) — finite-family aggregate.
- **`exists_scale_cfCylinder_psi_avoid_zbad_poly`** (proved from the aggregate) — POLYNOMIAL-threshold
  z-good point selection: `∃N~Ssum/δ², ∀n≥N, ∃ irrational p∈cfCylinder wx', ψp ∉ cfBadZone [] v n δ ∀v∈F`.
  The `γ(cfCylinder wx')` factor of the crux CANCELS the cylinder mass — no `2/q` pullback loss, no
  exponential, so the transfer range `n ≲ |wx'|` is NON-EMPTY (scale-regime-CORRECT). Composes directly
  with the existing absolute digit-agreement transfer `notMem_cfBadZone_nil_of_cfDigit_agree`.

So the single-stream z-side is now a fully-proved chain DOWN TO one precisely-stated analytic brick.
The messy conditional-at-`wz` lemmas (walled, see CORRECTION) are kept but OFF the critical path; the
clean path is: `psi_pushed_chebyshev_brick` → `_poly` discharge → absolute transfer → `CFOrbitEquidist`.

**Also landed (Markov wrapper — crux narrowed one level):** `psi_pushed_chebyshev_brick` is now PROVED
from a deeper sorry **`variance_blockCount_psi_pushed`** (the ψ-pushed L² / second-moment estimate
`∫_{cfCyl wx'} (blockCount n (ψ·) − nγv)² dγ ≤ O(n)·γ(cfCyl wx')`). The Chebyshev/Markov packaging
(restricted-measure Markov `mul_meas_ge_le_integral_of_nonneg`, the `f ≤ n²` integrability bound, the
`(δn)²`-rescale, and the arithmetic cancelling the `γ(cfCyl wx')` factor) is all PROVED. So the crux is
now the pure L² estimate `variance_blockCount_psi_pushed` — no probabilistic packaging left, just the
second-moment bound whose content is the ψ-conjugated pair-correlation decay.

**NEXT:** (0) prove `variance_blockCount_psi_pushed` — expand the square into the diagonal
(`∑_k γ(cfCyl wx' ∩ ψ⁻¹T^{-k}A)`, `O(n)` term) + off-diagonal pair correlations
(`∑_{k≠k'} [γ(cfCyl wx' ∩ ψ⁻¹T^{-k}A ∩ ψ⁻¹T^{-k'}A) − …]`), and bound the off-diagonal by the
ψ-conjugated mixing (extend `gaussMeasure_cylinder_mixing` to interval / affine-image bases). This is
THE irreducible analytic core. (1) prove `psi_pushed_chebyshev_brick` — SUBSUMED, now `= _poly` chain
down to the L²-core. (See old note:) attack via interval-base mixing (extend
`gaussMeasure_cylinder_mixing` from `cfCylinder` bases to `Ioo` bases; the ψ-image is an interval).
(2) In parallel (independent, doesn't need the brick proved): wire `exists_scale_cfCylinder_psi_avoid_zbad_poly`
+ the absolute transfer into `StepSpecL4`/the schedule to deliver `CFOrbitEquidist (ψ xA)`, then the
interleaved witness + excise the two-stream sorry. That wiring can proceed against the disclosed brick.

**THE ONE SURVIVING ESCAPE (now realized as `psi_pushed_chebyshev_brick` above).** All the trouble is that
the conditional Chebyshev is based at the z-cylinder `wz` (giving the `γ(cfCyl wz)` factor that won't
cancel). What is actually needed is a **ψ-pushed, x-cylinder-relative Chebyshev**: a bound
`γ(cfCyl wx' ∩ ψ⁻¹(cfBadZone [] v n δ)) ≤ O(1/n)·γ(cfCyl wx')` — the bad FRACTION *within the deep
x-cylinder itself*, local density `O(1/n)`, NO `wz`, NO `Cbridge`. That gives a polynomial threshold
`n > C` with transfer range `n ≲ |wx'|` non-empty, and every-`n` coverage as `|wx'_s|→∞`. This is a
Chebyshev for the observable `blockCount_n ∘ ψ` under `γ` conditioned on `cfCyl wx'` — i.e. the Gauss-map
variance/mixing must survive conjugation by the affine `ψ`. `chebyshev_blockCount_brick` proves exactly
this shape but for a z-CYLINDER base (via `gaussMeasure_cylinder_mixing`); the open question is whether
the mixing bound transfers through `ψ` to an x-cylinder base. THIS — not the bridge — is the real crux
lemma to attack. (If it's false, the single-stream route may be genuinely obstructed and a different
z-mechanism is needed; test by attempting the ψ-pushed variance bound.)

## 🟡 2026-08-25 — (SUPERSEDED / OVER-CLAIMED, see CORRECTION above) tight discharge

**Root-cause correction found this lap.** `tendsto_of_scale_coverage` needs EVERY large `n` covered
(not a cofinal subsequence — `CFOrbitEquidist` is a genuine `Tendsto … atTop`, `hcover` quantifies
∀ n ≥ n₀). Tracing the threshold arithmetic of `exists_scale_cfCylinder_psi_avoid_zbad_cond` exposed
that it is CORRECT but LOSSY: it bounds `γ(cfCylinder wz) ≤ 1`, discarding a `φ^{-2|wz|}` factor,
producing an EXPONENTIAL threshold `N ~ φ^{2|wz|}` — the SAME empty-range obstruction as the old
post-hoc witness. **The fix:** KEEP the `γ(cfCylinder wz)` factor and cancel it against
`γ(cfCylinder wx')` (both `~ φ^{-2·depth}`, comparable), via a bounded multiplicative bridge
`γ(cfCylinder wz) ≤ Cbridge·γ(cfCylinder wx')`.

**`exists_scale_cfCylinder_psi_avoid_zbad_cond_tight`** (`CFScheduleA`, axiom-clean) does exactly
this: with the bridge hypothesis, the threshold becomes `N ~ |wz| + O(Cbridge·Ssum/δ²)` —
**POLYNOMIAL in `|wz|`, no exponential**. So the transfer range `n ≲ |wx'| ~ |wz|` is NON-EMPTY.
This is the real dissolution of the scale-regime obstruction; the harmonic-band worry below is moot
because a polynomial-threshold single/narrow-band witness now lands inside the transfer range.

**Also landed (engine glue):** `notMem_cfBadZone_nil_of_notMem_psiCond` (`CFScheduleA`, axiom-clean)
— for full-orbit `z ∈ cfCylinder wz`, conditional avoidance (my tight selector's bad set) ⇒ absolute
`∉ cfBadZone [] v n δ` (what the EXISTING digit-agreement transfer `notMem_cfBadZone_nil_of_cfDigit_agree`
consumes). So the tight conditional selector and the existing absolute transfer now COMPOSE: select
`p` with polynomial threshold → strip to absolute goodness here → transfer to `ψ(xA)` via digit
agreement. The z-side is now a chain of composable in-kernel bricks with ONE geometric gap (`Cbridge`).

**SOLE remaining geometric input:** the bridge constant `Cbridge` (bounded, `~ 2/q`). Concretely
`γ(cfCylinder wz) ≤ Cbridge·γ(cfCylinder wx')` where `wz` = tightest z-prefix with
`ψ(cfCylinder wx') ⊆ cfCylinder wz`. Route: `vol(cfCylinder wz) ~ vol(ψ(cfCylinder wx')) =
q·vol(cfCylinder wx')` (ψ affine, factor q; wz is the minimal z-cylinder ⊇ image so its width is
within a bounded factor of the image width), then `γ ~ 2log2·vol` on `(0,1)` both ways. This is a
clean geometry/measure lemma — the NEXT target. Formalizing it + the `exists_tail_cfCylinder_subset_ball`
determination of `wz` completes the z-selection engine end-to-end.

**⚠️ (SUPERSEDED by the tight discharge above — kept for the record) harmonic-band worry:**
The band budget `∑_{n∈(L,M]} ∑_{v∈F} 7(8|v|+80)γv/((δ/2)²(n−L))·γ(wz)` carries a HARMONIC factor
`∑_{n=L+1}^{M} 1/(n−L) = H_{M−L} ~ log(M−L)`. For the geometric window `M ~ |w_s| ~ 2|w_{s-1}|`,
`M − L` is comparable to `L`, so `H_{M−L} ~ log L` — GROWS with the stage. So a fixed-`δ` single
witness canNOT cover a full geometric band with bounded budget: `budget ~ (2/q)Ssum·log L/((δ/2)²γcylR)`
must stay `< γcylR`, but `γcylR = γ(cfCylinder wx') ~ φ^{-2L}` SHRINKS. **This is the crux of
subtlety 2 and must be confronted head-on next lap.** Candidate resolutions, in order of promise:
  (a) **Per-scale δ decay absorbs the harmonic factor is FALSE** (δ_s→0 makes it worse). Instead,
      **thin the band**: don't cover every n∈(L,M] from one stage — cover a SPARSE subsequence (e.g.
      n = ⌈L·(1+1/k)⌉) and rely on `blockCount` near-monotonicity / the `|v|`-boundary slack
      (`blockCount_sub_countOccurrences_bounds`) to interpolate goodness at intermediate n. Budget
      then sums O(log) TERMS but each O(1/L)·(band width), possibly bounded.
  (b) **Coverage need not be per-stage-exhaustive.** Re-examine `tendsto_of_scale_coverage`'s actual
      hypothesis: it may only need goodness along a cofinal sequence of scales n_k→∞ with n_k good,
      NOT every n. If so, ONE scale per stage (the single-scale `exists_scale_cfCylinder_psi_avoid_zbad_cond`,
      already landed) suffices and the band/harmonic problem DISSOLVES. **Check this FIRST — it may
      obviate (a) entirely.** Read `tendsto_of_scale_coverage` + `CFOrbitEquidist` def carefully.
  (c) If genuinely every-n needed: the γcylR shrink is fought by the fact that Ssum also involves
      only FIXED-stage words (wordFamily s grows slowly); re-derive whether (2/q)Ssum·logL vs φ^{-2L}
      is actually violated or if a tighter cylinder-relative Ssum (using γ(cfCyl wz) not 1) saves it.

**THEN (schedule wiring, after the above is settled):**
1. **Thread `exists_scale_cfCylinder_psi_avoid_zbad_cond` into the block builder / `StepSpecL4`.**
   The analytic + measure spine is DONE; what remains is combining the z-good point pick with the
   x-freq-good block selection in `exists_uniformly_freq_good_block_steer_len_rel_cfK` (interval
   template `exists_irrational_notMem_xbad_psi_zbad_nil_in_Ioo`), and recording the per-stage
   conjunct `∀ n ∈ (|w_{s-1}|,|w_s|], ψ(witness) z-good at n` in `StepSpecL4`. The `wz` for stage `s`
   is the ψ-image pinned prefix of `cfCylinder wx_s` (`exists_tail_cfCylinder_subset_ball` +
   digit-agreement gives `ψ(cfCylinder wx_s) ⊆ cfCylinder wz`, so avoiding the `cfCylinder wz`-based
   conditional bad set is exactly ψ-image z-goodness). Blocks stay LINEAR (budget adds `O(1/|u|)·γ`).
   (`exists_uniformly_freq_good_block_steer_len_rel_cfK`): feed this bound as the z-bad budget
   over the window `(|w_{s-1}|,|w_s|]`, keeping blocks LINEAR (extra term `O(1/|u|)·γ`, absorbed
   like the x-freq term). Record `∀ n ∈ (|w_{s-1}|,|w_s|], ψ(witness) z-good at n` in `StepSpecL4`.
   Interval-scale selector template = `exists_irrational_notMem_xbad_psi_zbad_nil_in_Ioo`.
2. Z-II coverage via `tendsto_of_scale_coverage`: every large `n` pinned at exactly one stage
   `s*` (`|w_{s*}|≥n>|w_{s*-1}|`), `δ_{s*}→0`, transfer range `n≲|w_{s*}|` matches ⇒ no gap.
3. Assemble NEW `exists_interleaved_affine_witness` on the L4 stream + excise the two-stream sorry.

## 🔴 2026-08-25 — CRUX FINDING: the z-transfer has a SCALE-REGIME OBSTRUCTION (Z-II)

**The post-hoc z-good witness (`exists_scale_zgood_wxSeq_L4`) and the (Z-I) plan below
are in the WRONG SCALE REGIME for the transfer. Precise diagnosis:**

- The z-good threshold on cylinder `wx_s` is `N_s ~ (2/q)·Ssum_s/(δ_s²·γcyl_s)` where
  `γcyl_s = γ(cfCylinder wx_s) ~ φ^{-2|w_s|}` (SHRINKS exponentially in `|w_s|`). So the
  witness `p_s` is z-good only at scales `n ≥ N_s ~ φ^{2|w_s|}` (doubly-exp in `|w_s|`).
- The transfer (`exists_ball_cfDigit_psi_eq` + `exists_tail_cfCylinder_subset_ball` +
  `blockCount_eq_of_cfDigit_agree`) requires `ψxA` and `ψp_s` to agree on the first
  `m = n+|v|` CF digits. Agreement holds only when `cfCylinder wx_s ⊆` an x-ball of
  radius `~φ^{-2m}/q`; since the cylinder width is `~φ^{-2|w_s|}`, this needs
  `m ≲ |w_s|`, i.e. **transfer range `n ≲ |w_s|`**.
- `[N_s, |w_s|] = [φ^{2|w_s|}, |w_s|]` is EMPTY. The post-hoc witnesses are unusable.

**ROOT CAUSE (this is the real B6 crux, now sharply located).** Within a deep cylinder
`cyl_s`, `ψ` pins the first `~|w_s|` z-digits of ALL points to a COMMON value, so for
`n ≲ |w_s|` the quantity `blockCount(cfCyl v) n (ψx)` is DETERMINED (= its value at
`ψxA`) — not selectable. z-digit `n` becomes selectable only at the stage `s*` where
`|w_{s*}|` first exceeds `n` (the "pinning stage"). There the block `u_{s*}` controls
z-digits in the window `(|w_{s*-1}|, |w_{s*}|]`. The bad-zone density that matters is the
CONDITIONAL one — density `~1/(free-length) = 1/(n-|w_{s*-1}|)` given the pinned prefix —
which is small (feasible) ONLY if measured as a cylinder-RELATIVE bad zone
`cfBadZone w …` (whose `gaussMap^[|w|]` basepoint skips the pinned prefix), NOT the
ABSOLUTE `cfBadZone [] …`. But `ψ` does not map x-cylinders to z-cylinders, so there is
no clean `cfBadZone w` for the ψ-image. **The missing ingredient is a ψ-CONDITIONAL
z-Chebyshev bound: within `cyl_s`, the mass of points whose ψ-image is z-bad at scale
`n ∈ (|w_{s-1}|,|w_s|]` is `≤ O(1/(n-|w_{s-1}|))·γ(cyl_s)`** (relative, not absolute).
This is what makes the pinning-stage selection feasible; the absolute aggregate bound
(`gaussMeasure_aggregate_cfBadZone_le [] …`) is too weak here.

**WHY the two-stream avoided this (and why it was still refuted):** the two-stream gives
`zA=ψxA` its OWN cylinder chain `wz_s`, so its bad zones are cylinder-relative
`cfBadZone wz_s` (density `O(1/n)·γ`, feasible) — but coupling `x` and `z` chains under a
single `ψ` forces super-exponential blocks (`OBSTRUCTION-2026-08-24`). Single-stream
removes that coupling but reintroduces the absolute-vs-relative gap above.

**NEXT ATTACK (hardest-first, do NOT resurrect two-stream / post-hoc deep-cylinder):**
1. Establish the ψ-conditional z-Chebyshev: for `x` ranging over `cfCylinder w` with a
   pinned ψ-prefix of length `L~|w|`, `γ{x∈cfCylinder w : ψx ∈ cfBadZone [] v n δ}
   ≤ C·(8|v|+80)/(δ²(n-L))·γ(cfCylinder w)` for `n > L`. Likely route: pull back
   `chebyshev_blockCount_brick` through `ψ` using that `blockCount n (ψx) = (pinned
   count on [0,L)) + blockCount_{[L,n)}`, and the free part is a genuine conditional
   variance on the shifted orbit `gaussMap^[L](ψx)`. This is the one genuinely-open
   analytic lemma the z-side rests on.
2. Thread the pinning-stage z-selection into the block builder
   (`exists_uniformly_freq_good_block_steer_len_rel_cfK`): add the window-`(|w_{s-1}|,
   |w_s|]` z-bad avoidance to its budget (joint selector
   `exists_irrational_notMem_xbad_psi_zbad_nil_in_Ioo` is the interval-scale template),
   keeping blocks LINEAR (the extra budget term is `O(1/|u|)·γ`, absorbed like the
   x-freq term). Record `∀ n ∈ (|w_{s-1}|,|w_s|], ψ(witness) z-good at n` in StepSpecL4.
3. Then Z-II coverage closes: every large `n` is pinned at exactly one stage `s*` with
   `|w_{s*}| ≥ n > |w_{s*-1}|`, `δ_{s*}→0`, transfer range `n ≲ |w_{s*}|` MATCHES — no gap.

`exists_scale_zgood_wxSeq_L4` is TRUE but OFF the critical path (kept; not deleted).

## 🔴 2026-08-29 — STRUCTURAL FINDING: `schedL4_block_linear` DONE, but the L4 z-side is NOT reuse

**`schedL4_block_linear` is PROVED** (commit `030d8fb`, axiom-clean) and the x-side
downstream is landed: `schedL4_hfreq_x` (`ebf28fa`), `exists_xA_L4_orbit_equidist`
(`c0d188b`). Build 🟢 8757; headline still trust-triple. Sole `src/` sorry = the DEAD
two-stream `schedA_block_linear`.

**BUT** the block-linear rebuild of `StepSpecL4`/`schedStepL4_exists` (commit `acdcb19`,
"rewired onto the cfK builder") carries **ZERO z-side control** — `grep cfBadZone|affineMap`
over `StepSpecL4` = 0 hits. The DIRECTIVE calls the z-side "REUSE", but that assumed the
EARLIER StepSpecL4 (brick-4b plan, §248 below) which recorded a per-stage `ψ(p_s)`-avoidance.
The cfK rewire dropped it. **So the current `wxSeq_L4` makes `x` normal but gives NO control
on `ψ(x)`.** `ψ(xA)` normality (the other half of the interleaved witness) genuinely requires
the schedule to steer ψ away from z-bad-zones — it cannot be recovered post-hoc from an
x-only chain (xA is the unique intersection point; ψ(xA) is then fixed, no freedom to pick).

**REFINED REMAINING WORK (two parts, hardest-first):**
- **(Z-I) Re-integrate z-avoidance into `StepSpecL4` + `schedStepL4_exists`.** Add a conjunct
  recording a point `p_s ∈ cfCylinder (wx')` with `ψ(p_s)` irrational, full-orbit in (0,1),
  and `∀ v∈F_s, ∀ n∈NSz_s, ψ(p_s) ∉ cfBadZone [] v n (δ_s)`. The selection is a measure
  argument on the FIXED cylinder `cfCylinder wx'`: need pulled-back z-bad mass
  `γ(cfCylinder wx' ∩ ψ⁻¹(⋃_{n∈NSz_s} cfBadZone[] v n δ_s)) < γ(cfCylinder wx')`. Tune
  `NSz_s` (bounded window) + `δ_s` per s so the Chebyshev budget
  (`gaussMeasure_aggregate_cfBadZone_le`, pulled back via
  `gaussMeasure_interval_inter_preimage_affineMap_le`, factor `≤2/q`) stays below the
  cylinder mass. **This must NOT disturb the LINEAR block length** (the p_s selection is a
  point pick inside the already-chosen block cylinder, so |block| is unchanged — keep the
  x-block builder as-is, add an independent point selection after it). Threading the new
  conjunct breaks 4 `obtain ⟨…⟩` destructurings (schedL4_block_linear, schedL4_hfreq_x,
  wxSeq_L4_length_ge, cfK_wxSeq_L4_le) — add one `_` to each.
- **(Z-II) z-transfer engine → `CFOrbitEquidist (ψ xA)`.** From (Z-I)'s per-stage p_s
  avoidance + `δ_s→0` + `NSz` cofinal, transfer to the limit: for fixed n, take s large so
  `cfCylinder(wx_{s+1}) ⊆` an x-ball around xA on which ψ agrees with ψxA on the first
  `m=n+|v|` z-digits (`exists_ball_cfDigit_psi_eq` at x₀=xA, needs ψxA irrational — TRUE:
  xA irrational, q≠0; `exists_tail_cfCylinder_subset_ball` gives the s-threshold). Then
  `blockCount_eq_of_cfDigit_agree` ⇒ ψxA shares p_s's block count ⇒
  `notMem_cfBadZone_nil_of_cfDigit_agree` ⇒ ψxA ∉ cfBadZone[] v n δ_s ⇒
  `|blockCount(cfCyl v) n ψxA/n − γv| < δ_s`. Feed `tendsto_of_scale_coverage` (f n =
  blockCount/n, L=γv, S s = NSz_s∩{n large}, hcover from cofinality + s-n coupling). All six
  transfer lemmas (§252) exist + axiom-clean; the delicate part is the s↔n coupling in
  `hcover` (each n needs its own large-enough s for the ball inclusion at depth n+|v|).
- **(Z-III) assemble** NEW `exists_interleaved_affine_witness` (xA from
  `exists_xA_L4_orbit_equidist`, ψxA equidist from Z-II, ψxA∈(0,1) from feasibility+interval,
  ψxA irrational from xA irr + q≠0), then EXCISE the two-stream `schedA_block_linear` sorry.

**Z-I MEASURE LAYER — DONE (2026-08-29):** the per-stage z-selection engine is built +
axiom-clean:
- `exists_irrational_mem_cfCylinder_notMem_of_gaussMeasure_lt` (`07d832d`) — cylinder selector.
- `gaussMeasure_cfCylinder_inter_preimage_affineMap_le` (`c23d0b5`) — cylinder pullback bound.
- `exists_cfCylinder_psi_avoid_zbad` (`996ad56`) — the engine: `hbudget` (pulled-back z-bad
  mass on hull < cylinder mass) ⇒ irrational `p ∈ cfCylinder wx'` with `ψ(p) ∉ cfBadZone[] v n δ`
  for `v∈F, n∈NSz`. `hbudget` deferred to caller (Chebyshev, `n≳cfK²`).
- `countable_preimage_affineMap_range_rat` (this lap) — `ψ⁻¹(ℚ)` countable (Z-III fix).

**Two NEWLY-SURFACED design subtleties (flag for altitude lap):**
1. **`ψ(xA)` need NOT be irrational for real `q,r`** — the PENDING Z-III note "ψxA irrational
   from xA irr + q≠0" is FALSE (e.g. xA=√2,q=1/√2,r=0 ⇒ ψxA=1∈ℚ). Two-stream got it free
   (`ψ(xA)=zA`, zA chosen irrational). Single-stream must FORCE it: the chain-limit selection
   must avoid the countable null set `ψ⁻¹(ℚ)`. But `exists_irrational_mem_iInter_cfCylinder`
   picks the UNIQUE Cantor-intersection point (no post-hoc freedom) — so a strengthened iInter
   selector must avoid `ℚ ∪ ψ⁻¹(ℚ)` at the limit. REQUIRED: `ψxA` irrational ⇒ full Gauss orbit
   in `(0,1)` ⇒ `blockCount_eq_of_cfDigit_agree`'s `horb` holds.
2. **Z-II `hcover` s↔n coupling** — transferring `p_s`-avoidance to `ψ(xA)` at scale `n` needs
   `cfCylinder(wx_s) ⊆` an x-ball of radius set by depth `m=n+|v|` (`exists_ball_cfDigit_psi_eq`),
   i.e. each `n` needs its own large-enough `s` (`exists_tail_cfCylinder_subset_ball`).
   `tendsto_of_scale_coverage`'s `hcover` must thread this per-`n` `s`-threshold with `δ_s→0`
   and `n∈NSz_s` cofinality.

**NEXT probe:** either (a) the Chebyshev budget lemma discharging `exists_cfCylinder_psi_avoid_zbad`'s
`hbudget` for concrete `NSz_s`/`δ_s`, then thread into `StepSpecL4`; or (b) resolve subtlety (1)
via a strengthened iInter selector avoiding an extra countable set (⇒ `ψxA` irrational directly).
(b) is more route-decisive.


## 🎯 2026-08-24 REVIEW LAP — CRUX = the cfK-cap graft (bridge + layer 1 DONE)

The block-linear support layer is proved (relative regularization, below). The ONE
remaining open sub-obstruction for `schedL4_block_linear` is the **cfK cap**: the
steer block must expose `cfK(u) ≤ e^{κ|u|}` so `exists_fib_threshold_linear_of_cfK`
(proved) + `four_div_volume_cfCylinder_le` (proved) make the resolution `Nfib` AFFINE
in `|wx|` (⇒ linear blocks). This is a POSITIVE-MEASURE Lévy-uniform selection, NOT
the refuted hard digit-cap (L4's target is the cylinder's OWN hull, `ρ=1`, no
small-corner navigation). Whole measure/selection stack pre-exists:
`exists_rate_gaussMeasure_cfKbadExtSet_le`, `cfK_append_le`,
`exists_irrational_notMem_multiscale_cfBadZone_cfK_in_Ioo`.

**Attack path (cfK cap threads up the 3-layer block-builder chain, then assembles):**
- ✅ **layer 0 (bridge)** `cfK_le_of_notMem_cfKbadExtSet` — a point avoiding
  `cfKbadExtSet wx κ ntop` in `cfCylinder(wx++u)` (u genuine, |u|=ntop) has
  `cfK u ≤ e^{κ·ntop}`.  DONE this lap.
- ✅ **layer 1** `exists_multiscale_freq_good_block_steer_len_cfK` — mirror of
  `..._len`, swaps in the cfK selection core, exposes `cfK u ≤ e^{κ|u|}`.  DONE.
- ⬜ **layer 2** `exists_uniformly_freq_good_block_steer_cfK` — mirror of
  `exists_uniformly_freq_good_block_steer` (:2136-ish) calling layer 1 at
  `NS = quadScales n₁ m`; cfK bound `e^{κ(n₁+m²)}=e^{κ|u|}` passes straight through
  (same digit block, |u| unchanged). The `hbound` gains the cfKbadExtSet-mass room
  term (at `ntop = quadScales.max' = n₁+m²`).
- ⬜ **layer 3** `exists_uniformly_freq_good_block_steer_len_rel_cfK` — mirror of
  `..._len_rel` calling layer 2; carries cfK through the relative-β length exposure.
  The `hbound`/measure-budget grows by the cfK term; check `(m+1)·A₁(n₁)+cfKmass < γtar`
  still solvable (it is: cfKmass `≤ (log2)⁻¹·ε·|I_wx|`, pick ε small via the rate κ).
- ⬜ **assemble `schedL4_block_linear`** — fix κ once (`exists_rate_gaussMeasure_cfKbadExtSet_le`
  with `ε := γtar/4`); `schedStepL4_exists` calls the layer-3 cfK builder so each
  block carries `cfK(u_s) ≤ e^{κ|u_s|}`; thread through recursion with `cfK_append_le`
  (`cfK(wxSeq s) ≤ 2^s·∏cfK(u_i) ≤ C₀·e^{(κ+log2)|wxSeq s|}`, using `s ≤ |wxSeq s|`);
  then `four_div_volume_cfCylinder_le` + `exists_fib_threshold_linear_of_cfK` ⇒
  `Nfib ≲ |wx|`; combine with exposed `|u|=n₁+m²`, the `m²` bound, `two_div_beta_rel_le`
  ⇒ `|chainApp| ≤ K₁|w|+K₂`.
- ⬜ **downstream = REUSE**: seed `exists_seedStateL4`, `wxSeq_L4` (`Nat.rec`), x-side
  `chain_orbit_equidist_uniform`, z-side scale-coverage (`tendsto_of_scale_coverage`
  + brick-4a transfer lemmas), assemble new `exists_interleaved_affine_witness`,
  excise the two-stream `sorry`.

NOTE: `StepSpecL4` currently does NOT carry the length/cfK fields — extend it to
expose `|u|`'s bound and the cfK cap when wiring `schedL4_block_linear` (thread the
layer-3 builder's extra return values through the step, as the len_rel docstring notes).

---

## 🎯🎯🎯 2026-08-24 CRUX LOCATED — block-linear fails at the `S+1` ABSOLUTE regularization, NOT the route

**Sharpest finding of the L4 campaign.** After reading the full block machinery
(`exists_uniformly_freq_good_block_steer_len` :2139, `exists_uniform_block_param_tight`
:2077, `schedA_block_linear` :3346), the `|chainApp| ≤ K₁|w|+K₂` obligation reduces
to bounding the block `|u| = n₁ + m²` with `m² ≤ 6(Lc+Nfib)+2+2(⌈2/β⌉+1)⁴`
(tight param). The three inputs:
- **Lc = L = s** — LINEAR in stage, fine.
- **Nfib** = fib-threshold for `4/(d−c)`; for the L4 self-hull steer `d−c ≈ φ^{−|wx|}`
  so `Nfib ≈ |wx|` — LINEAR, fine (needs a small `Nfib ≲ |wx|` lemma).
- **β = γtar·δ²/(S+1)**, `S = γwx·Σ'`, `Σ' = ∑_{v∈F} 7(8|v|+80)γ(cfCyl v)`
  (word-independent), `γtar = γ(middle-half of hull) ≈ γwx/8`. **← THE OBSTRUCTION.**

**The `+1` in `S+1` breaks the scaling.** Both `γtar` and `S` are `Θ(γwx)`, so the
ratio `γtar/S = Θ(1/Σ')` is WORD-INDEPENDENT — that's the whole point of route B (x
steers into its OWN hull, `γtar/γwx = Θ(1)`, unlike two-stream's `γtar/γwx ≈ φ^{−κ|zblk|}`).
But `β = γtar·δ²/(S+1)`: as the cylinder deepens `γwx→0` ⇒ `γtar→0`, `S→0`, so
`β → γtar·δ² ≈ (γwx/8)δ² ≈ φ^{−|wx|}δ² → 0`. Then `⌈2/β⌉ ≈ φ^{|wx|}/δ²` EXPONENTIAL,
`m² ≈ (⌈2/β⌉)⁴` SUPER-exponential. **So the current block lemma gives
super-exponential blocks even for the L4 self-hull steer — block-linear is NOT
automatic from the route pivot.** (This is why `schedA_block_linear` is genuinely open,
independent of two- vs single-stream.)

**THE FIX — relative regularization `S + γwx` (or `S + c·γwx`) in place of `S + 1`.**
Then `β = γtar·δ²/(S+γwx) = γtar·δ²/(γwx(Σ'+1)) = (γtar/γwx)·δ²/(Σ'+1) ≥ (1/8)δ²/(Σ'+1)`
— WORD-INDEPENDENT and bounded below, so `⌈2/β⌉` is a per-family constant and `m²`,
hence `|u|`, is LINEAR in `Lc+Nfib ≈ s+|wx|`. `γwx > 0` always (genuine cylinder), so
`S+γwx > 0` is a valid regularizer; `F` nonempty ⇒ `Σ'>0`. The density machinery is
ALREADY present: `gaussMeasure_Ioo_toReal_ge` (:2021, docstring literally says
"`γtar ≥ q·c₀·γwx`") + a matching upper bound give `γtar/γwx ∈ [c₀, 1]`.

**NEXT BRICK (the real crux, hardest-first):** a variant
`exists_uniformly_freq_good_block_steer_len_rel` using `β := γtar·δ²/(S+γwx)` + the
TIGHT param, exposing `|u| ≤ Krel·(L + Nfib) + Crel(F,δ)` with `Krel, Crel`
word-INDEPENDENT. Then: (b) `Nfib ≲ |wx|` from `d−c = width(hull) ≥ φ^{−(|wx|+O(1))}`
(`volume_cfCylinder_ge_fib`-type / hull-width lower bound); (c) `γtar ≥ γwx/8` from the
density bounds. Feed all into the L4 schedule ⇒ `schedL4_block_linear` (the L4 analog
of the open `schedA_block_linear`), now PROVABLE. THEN `SchedStateL4`/step/chain/z-side.
The z-transfer machinery (bricks 4a + 5 transfer lemmas) is already complete + axiom-clean.


## ✅✅✅ 2026-08-24 REVIEW LAP — PIVOT RATIFIED: RESUME SINGLE-STREAM L4 (the two-stream route is DEAD)

**The "box stuck" was a FALSE STOP.** The two-stream construction is genuinely
obstructed (super-exponential blocks — `OBSTRUCTION-2026-08-24`, re-verified), but
the fix does not need an operator: the **single-stream L4 route is the ORIGINAL
design** (`CFScheduleA.lean:24–31` module docstring) and its foundational pullback
lemma is ALREADY PROVED — `volume_preimage_affineMap` (`CFAffine:94`,
`volume(ψ⁻¹ s)=|q⁻¹|·volume s`), whose own docstring says it is "the union-bound
ingredient for L4". The two-stream `wxSeq`/`wzSeq`/`schedA`/`schedA_block_linear`
layer was a later drift into a wall. **DIRECTION.md CURRENT DIRECTIVE now mandates
resuming L4.** This section is the attack path.

### Why L4 removes the obstruction
Two-stream nests a z-cylinder as the x-target ⇒ target relative size
`ρ ≈ e^{−2κ|zblock|}` ⇒ measure budget `n₁ ≳ 1/ρ` ⇒ super-exponential blocks.
L4 keeps the target = the FULL current x-cylinder (`ρ=1`): control `ψ(x)`'s
z-frequency STATISTICALLY by having `x` avoid the ψ-PULLBACK of the z-bad-zones,
never nesting a z-cylinder. `zA := ψ(xA)` is then DEFINITIONAL (no gluing/squeeze).
Blocks become polynomial-in-stage ⇒ `o(word)` — comfortably past the affine bound.

### The crux statement does NOT change
`exists_interleaved_affine_witness` (`:2676`) is route-agnostic:
`∃ x, (Irr x ∧ x∈(0,1) ∧ CFOrbitEquidist x) ∧ (Irr ψx ∧ ψx∈(0,1) ∧ CFOrbitEquidist ψx)`.
L4 gives it a NEW proof; the two-stream proof (bottoming at the `schedA_block_linear`
`sorry`) becomes excisable dead code once L4 lands.

### Attack path (hardest-first)
1. ✅ **DONE (2026-08-24, commit `5ba3a3d`, axiom-clean).**
   `gaussMeasure_preimage_affineMap_le` (`CFScheduleA.lean`, just before
   `gaussMeasure_multiscale_cfBadZone_le`): for `q>0`, measurable `S ⊆ (0,1)`,
   `gaussMeasure (affineMap q r ⁻¹' S) ≤ ENNReal.ofReal (2/q) * gaussMeasure S`.
   Assembled from `gaussMeasure_le_volume` ∘ `volume_preimage_affineMap` ∘
   `volume_le_ofReal_mul_gaussMeasure`; the two `log2` cancel to `2/q`. The
   route-decisive measure-budget probe — PASSED (clean, small). **Next lap starts
   at brick 2.**
2. **Pulled-back z-bad-zone control — SPLIT this lap into 2a (DONE) + 2b (the
   route-decisive crux).**

   2a. ✅ **DONE (2026-08-24, commit `3169e1a`, axiom-clean).**
   `gaussMeasure_preimage_multiscale_cfBadZone_le` (`CFScheduleA.lean`, after
   `gaussMeasure_multiscale_cfBadZone_le`): the ψ-preimage of the z-cylinder-based
   multiscale bad zone (base `wz`) has γ-measure `≤ (2/q)·|NS|·(∑_v …/(δ²n₁))·γ(cfCylinder wz)`.
   Clean: brick 1 ∘ `gaussMeasure_multiscale_cfBadZone_le`. Bound is ABSOLUTE
   (`·γ(cfCylinder wz)`).

   2b. **✅ ROUTE-DECISIVE UNCERTAINTY RESOLVED (2026-08-24 grind lap): use
   ABSOLUTE-scale z-bad-zones + INTERVAL COVERING at scales `N ≳ 2|wx|` — no
   alignment, LINEAR blocks. (Supersedes the "alignment C-bound" framing, which was
   the WRONG cut.)**

   The alignment framing ("find z-cylinder `wz ⊇ ψ(cfCylinder wx)` with
   `γ(wz)=O(1)·γ(wx)`") FAILS: `J = ψ(cfCylinder wx)` can straddle a shallow
   z-boundary ⇒ deepest containing z-cylinder is shallow ⇒ `C` exponential, and
   no bounded refinement provably fixes it (straddle recursion). Both refine-to-align
   and "deepest containing cylinder" are DEAD. The correct route:

   - **Control `ψ(x)`'s z-frequency at ABSOLUTE scales via `cfBadZone [] v N δ`**
     (base EMPTY: bad v-freq in the FIRST `N` z-digits, clean slack `δN`, no
     cylinder-prefix seam). Select `x ∈ cfCylinder wx` avoiding `ψ⁻¹(cfBadZone [] v N δ)`.
   - **The selection mass is `(2/q)·γ(J ∩ cfBadZone [] v N δ)`, `J = ψ(cfCylinder wx)`.**
     `cfBadZone [] v N δ` is a union of BAD depth-`N` z-cylinders (freq depends only
     on first `N` digits). Bound `γ(J ∩ bad)` by covering `J` with depth-`d`
     z-cylinders (`d ≈ |wx|`, so depth-`d` width `≈ |J|`): full-inside cylinders +
     `≤ 2` boundary cylinders (residual `≤ 2·max depth-d width ≤ 2/fib(d+1)²`, via
     `volume_cfCylinder_le_fib`). On each full cylinder, TWO-SCALE Chebyshev split:
     `[0,N)`-bad ⊆ (`[0,d)`-prefix-bad, scale `d`) ∪ (`[d,N)`-tail-bad, base = that
     cylinder = existing `cfBadZone wz'`); both controlled by
     `gaussMeasure_aggregate_cfBadZone_le`.
   - **THE key regime: `N ≳ 2|wx|`.** Then depth-`N` z-cylinders are `≪ |J|` (no
     all-or-nothing straddle — that pathology only bites when `N < |wx|`), the bad
     mass is a genuine fraction `≈ S/(δ²N)·γ(J)`, and the residual `2/fib(N/2)² ≈
     φ^{−N}` is `< γ(J) ≈ φ^{−2|wx|}` exactly when `N ≳ 2|wx|`. So the z-burn-in
     `n₁z ≳ 2|wx|` — **LINEAR in the word, i.e. exactly `schedA_block_linear`'s
     budget.** Blocks `|u_s| ≈ 2|wx_s| + m_s²` linear; word grows geometrically.
   - **z-side normality = SCALE COVERAGE, not telescoping.** `ψ(xA)`'s digits are
     NOT built blockwise, so there is NO z-side `hslack`. Instead: the controlled
     z-scale-ranges `[≈2|wx_s|, …]` (with `δ_s → 0`) cover all large `N` cofinally;
     for each large `N`, the stage controlling it gives `δ_{s(N)}`-goodness,
     `δ_{s(N)} → 0`, so `ψ(xA)`'s window freq at `N → γ`. ⇒ `CFOrbitEquidist (ψxA)`.
     (x-side STILL uses the blockwise `chain_cf_digit_freq_tendsto_uniform`
     telescoping — its `C_s = 4√|u_s| + 2|v| + n₁x` with n₁x poly is `o(word)`,
     fine under geometric growth.)

   **Route B is UNCONDITIONAL (works for any interval `J`), gives linear blocks, and
   needs NO alignment.** This is the resolution of the whole B6 crux's feasibility.

   **Remaining route-B bricks (next laps, hardest-first):**
   - **2b-i (covering): ✅ ALREADY EXISTS — reuse, do NOT re-derive.**
     `volume_interval_sdiff_covered_le` (`CFIntervalGood.lean:89`, sorry-free) is
     exactly this brick in Lebesgue form: `vol((a,b) \ coveredByCyl a b n) ≤
     4/fib(n+1)²`, where `coveredByCyl a b n` (`:73`) = union of depth-`n` cylinders
     `⊆ (a,b)`. This is the L1 boundary-strip lemma; the "≤2 straddling" count is
     side-stepped (straddlers all lie within `M=1/fib(n+1)²` of an endpoint, total
     mass `≤4M`). The γ-version is `≤2×` via `gaussMeasure_le_volume`. NOTE: base
     `[]` in `cfBadZone` matches `coveredByCyl`'s genuine depth-`n` words; the seam
     term is absorbed by 2b-ii, not the covering. **2b-iii only needs to package the
     γ-residual and combine — the hard covering geometry is done.**
   - **2b-ii (two-scale split): ✅ DONE (2026-08-24, this lap, axiom-clean).**
     REFORMULATED far cleaner than the old "prefix-bad ∪ tail-bad Chebyshev" plan:
     the count `blockCount` is a genuine Birkhoff sum, so `birkhoffSum_add` gives
     `bc A N x = bc A d x + bc A (N−d)(gᵈx)` with NO seam junk. The length-`d` seam
     term `∈[0,d]` shaves only `d/N` of the slack. Two src lemmas in `CFScheduleA.lean`
     (after brick 2a):
       · `cfBadZone_nil_shift_mem_cfBadZone` (pointwise): for `x ∈ cfBadZone [] v N δ
         ∩ cfCylinder w'` with `gᵈx ∈ (0,1)` and `|w'|=d<N`, `x ∈ cfBadZone w' v (N−d)
         (δ − d/N)`. Pure Birkhoff + triangle ineq; NO countOccurrences bridge.
       · `gaussMeasure_cfBadZone_nil_inter_cylinder_le` (measure): `γ(cfBadZone [] v N δ
         ∩ cfCylinder w') ≤ γ(cfBadZone w' v (N−d)(δ−d/N))`. Null rationals absorbed via
         `withDensity_absolutelyContinuous`; `gᵈx∈(0,1)` from `irrational_orbit`.
     So on each depth-`d` interior cylinder `w'`, the base-`[]` bad mass at scale `N`
     is bounded by a base-`w'` bad mass at scale `N−d` (slack `δ−d/N`) — feed that to
     `gaussMeasure_aggregate_cfBadZone_le`/`variance_blockCount_le` (Chebyshev) for the
     per-cylinder fraction. δ−d/N ≈ δ when `N ≳ 2d` (route-B regime), so the fraction
     is `≈ (8|v|+80)/((δ−d/N)²(N−d))·γ(w')`. NOTE the old `δN/(2d)` prefix scale is GONE
     — there is no separate prefix-bad set, just a slack shave.
   - **2b-iii (assemble): ✅ SINGLE-SCALE DONE (2026-08-24, commit `db09458`,
     axiom-clean).** `gaussMeasure_interval_inter_cfBadZone_nil_le` (`CFScheduleA.lean`,
     after the per-cylinder frac lemma): `γ((a,b) ∩ cfBadZone [] v N δ) ≤ frac·γ(a,b)
     + residual`, `frac = 7·(8|v|+80)·γ(v)/(δ'²(N−d))`, `δ'=δ−d/N`, `residual =
     (log2)⁻¹·4/fib(d+1)²`, for any `d < N`, `δ−d/N > 0`. Cover-by-depth-`d` +
     `measure_biUnion` (disjoint cover) + `ENNReal.tsum_mul_left` + 2b-i residual.
     **This IS the route-decisive B6 measure bound — the whole crux feasibility
     uncertainty, now proved in-kernel.** REMAINING for full 2b-iii: (a) aggregate
     over `v ∈ F` (finite sum, `measure_biUnion_finset_le`) and `N ∈ NS` (finite sum);
     pick `d ≈ depth(J)`, `N ≥ n₁ ≈ 2d` so `frac` small + `residual < γ(J)`; (b) bridge
     to brick 3 (`exists_irrational_notMem_xbad_psi_zbad_in_Ioo`) — its `hbound` z-term
     is currently a z-CYLINDER-based multiscale bound (`wz≠[]`); needs a `wz=[]` /
     route-B variant fed by this lemma + brick 1 pullback (`gaussMeasure_preimage_affineMap_le`).
     THEN bricks 4/5/6.
     **✅ (a) DONE `37ba36a` `gaussMeasure_interval_inter_iUnion_cfBadZone_nil_le`
     (F/NS aggregate). ✅ (b) DONE: ψ-pullback bridge `08ba500`
     `gaussMeasure_interval_inter_preimage_affineMap_le` (`γ((c,d)∩ψ⁻¹S) ≤
     (2/q)γ(S∩ψ((c,d)))`) + route-B brick 3′ `f4ac8fd`
     `exists_irrational_notMem_xbad_psi_zbad_nil_in_Ioo` (combined single-stream
     selection, base-`[]` z-bad, linear budget). THE ENTIRE ROUTE-B MEASURE+SELECTION
     LAYER IS NOW COMPLETE + AXIOM-CLEAN.** Only remaining `hbound` plumbing for a
     concrete stage: choose `d, n₁z` s.t. the double-sum + residual `< γ(c,d)` (a
     numeric threshold pick — done inside the recursion, brick 4). NEXT = bricks 4/5/6.
   - **2b-iii (OLD framing — superseded, kept for context):** Now has BOTH inputs in hand:
     `γ(J ∩ ⋃_{v∈F,N∈NS} cfBadZone [] v N δ) ≤ (fraction)·γ(J) + residual`, `J=(α,β)`.
     Decompose `J = coveredByCyl α β d ∪ (J \ coveredByCyl α β d)`, `d ≈ depth(J)`:
       · residual term `γ(J \ coveredByCyl) ≤ 2·vol(J\coveredByCyl) ≤ 8/fib(d+1)²`
         (brick 2b-i, `volume_interval_sdiff_covered_le` + `gaussMeasure_le_volume`);
       · interior term: `coveredByCyl α β d ∩ bad = ⋃_{w'⊆J} (cfCylinder w' ∩ bad)`;
         per interior `w'` apply 2b-ii (`gaussMeasure_cfBadZone_nil_inter_cylinder_le`)
         then Chebyshev (`gaussMeasure_aggregate_cfBadZone_le`) → `≤ frac·γ(w')`;
         sum over the DISJOINT interior `w'` (`cfCylinder_disjoint`) → `≤ frac·γ(J)`.
     Regime `N ≳ 2d` makes `frac ≈ (8|v|+80)/(δ²N)` and residual `< γ(J)`. Then feed
     brick 3 (with `wz := []`, NS the absolute z-scales) — brick 3 currently takes a
     z-cylinder base `wz`; a `wz=[]` specialization or route-B variant is the bridge.
   - Then bricks 4 (recursion), 5 (z-coverage → `CFOrbitEquidist ψxA`), 6 (assemble).
3. ✅ **DONE (2026-08-24, commit `d255444`, axiom-clean).**
   `exists_irrational_notMem_xbad_psi_zbad_in_Ioo` (`CFScheduleA.lean`, after
   `exists_irrational_notMem_multiscale_cfBadZone_in_Ioo`): selects ONE irrational
   `x ∈ (c,d)` avoiding BOTH x-CF bad zones (base wx, scales NSx) AND ψ⁻¹(z-CF bad
   zones) (base wz, scales NSz), given ONE measure hypothesis `hbound`
   (x-bad mass + `(2/q)`·z-bad mass < γ(c,d)). Uses brick 2a for the z-term. **The
   full MEASURE+SELECTION layer of L4 (bricks 1, 2a, 3) is now complete and
   axiom-clean.** What `hbound` needs from the schedule is exactly the C-bound (2b).
4. **Single-stream recursion (brick 4).** Rebuild as ONE stream: a `SchedStateL4`
   carrying only `wx` + the interval, extended by brick-3′ selection each stage;
   `wxSeq_L4`, its chain, limit `xA`. Reuse `chain_orbit_equidist_uniform` for `xA`.

   **✅ BRICK-4 Z-TRANSFER INGREDIENTS COMPLETE + AXIOM-CLEAN (2026-08-24, this lap
   sequence).** The mechanism transferring the selected point's z-frequency to the
   chain limit `ψ(xA)` is now fully in-kernel, via FIVE reusable lemmas in
   `CFScheduleA.lean` (all trust-triple):
   - `blockCount_eq_of_cfDigit_agree` (`4b8cfb8`) — first-`m` digit agreement (`n+|v|≤m`)
     ⇒ equal `blockCount (cfCyl v) n`.
   - `exists_nhds_cfDigit_eq` (`3b6d753`) — z-ball on which first `m` CF digits are const.
   - `exists_ball_cfDigit_psi_eq` (`60c9465`) — ψ `q`-Lipschitz pullback of that ball to
     an x-ball: nearby `x` ⇒ `ψx` agrees with `ψx₀` on first `m` z-digits.
   - `notMem_cfBadZone_nil_of_cfDigit_agree` (`6186ef0`) — digit-agreement transfers
     ABSOLUTE-scale bad-zone AVOIDANCE (`cfBadZone [] v n δ`).
   - `exists_cfCylinder_prefix_subset_ball` (`bb439bd`) — a deep genuine extension of
     `wx` whose cylinder ⊆ any ε-ball around one of its irrational points (diam→0).
   - `cfDigit_eq_of_mem_cfCylinder` (this lap) — co-membership in a cylinder pins the
     leading digits (cylinder-based agreement, no metric ε).

   **✅ ROUTE-DECISIVE DESIGN — z-transfer needs NO boundary strip; irrationality of
   `ψ(xA)` does all the work.** (Supersedes an earlier over-complicated "boundary-strip
   avoidance" note — that was solving a non-problem.)  The per-stage step just
   freq-good-extends `wx→wx₁` (LINEAR block, uniform-good, x-side) and selects a brick-3′
   point `p_s ∈ cfCylinder wx₁` with `ψ(p_s) ∉ cfBadZone [] v n δ_s` for `n∈NSz_s,v∈F`.
   NO ball-refinement, NO straddle worry at selection time.  The transfer to the limit is
   deferred to the z-side assembly and rests on ONE fact: **`ψ(xA)` is IRRATIONAL** (xA
   irrational, `q≠0`), so for every depth `m` it is STRICTLY interior to its own depth-`m`
   z-cylinder.  Hence (via `exists_ball_cfDigit_psi_eq` applied at `x₀:=xA`) there is an
   x-ball around `xA` on which every point's ψ-image agrees with `ψ(xA)` on the first `m`
   z-digits; since `cfCylinder (wxSeq s) → {xA}` (diam→0), for large `s` the WHOLE cylinder
   sits in that ball, so `ψ(p_s)` (for `s` large) agrees with `ψ(xA)` on `m` digits ⇒
   `blockCount` equal (`blockCount_eq_of_cfDigit_agree`) ⇒ `ψ(xA) ∉ cfBadZone [] v n δ_s`
   (`notMem_cfBadZone_nil_of_cfDigit_agree`).  Feed that + `δ_s→0` + cofinal `NSz_s` to
   `tendsto_of_scale_coverage`.  Straddle is irrelevant: we never demand a single cylinder
   contain the whole image, only that the SHRINKING images eventually enter a fixed ball
   around the irrational `ψ(xA)` — which they must.  Blocks stay LINEAR.

   **NEXT BRICKS (concrete, hardest-first):**
   - (4a) `exists_tail_cfCylinder_subset_ball`: for a genuine extending chain `w` with
     limit `xA ∈ ⋂ cfCylinder (w s)` and `ε>0`, `∃ S, ∀ s≥S, cfCylinder (w s) ⊆
     Ioo (xA-ε)(xA+ε)` (diam→0, reuse `eq_of_mem_cfCylinder_chain`'s diameter estimate). ✅ NEXT.
   - (4b) `SchedStateL4` (only `wx` + interval `(e,f)`, invariant `cfCylinder wx ⊆
     ψ⁻¹(Ioo e f)`) + `StepSpecL4` (x-side uniform block payload + the per-stage
     `ψ(p_s)`-avoidance record) + `schedStepL4_exists` (mirror
     `exists_freq_good_extend_cfCylinder` for the x-block, brick-3′ for `p_s`).
   - (4c) `wxSeq_L4`, its chain, limit `xA`; x-side via `chain_orbit_equidist_uniform`.
   - (5-proper) z-side: assemble `ψ(xA)` avoidance at every controlled scale from (4a)+
     the transfer lemmas, feed `tendsto_of_scale_coverage` ⇒ `CFOrbitEquidist (ψxA)`.
   - (6) NEW `exists_interleaved_affine_witness`; excise the two-stream `sorry`.
5. **z-side chain frequency.** ✅ **CORE DONE (2026-08-24, commit `6933f05`,
   axiom-clean):** `tendsto_of_scale_coverage` (`CFScheduleA.lean`, after brick 3′) —
   `f n → L` when `|f n − L| < δ s` for `n ∈ S s` and the stages cover all large `n`
   with `δ s → 0`. This is the whole z-side engine; brick 5 proper = instantiate it
   with `f n = blockCount (cfCyl v) n (ψxA)/n`, `S s = NSz_s`, `havoid` from the
   stage's `ψ(x)∉cfBadZone[]` avoidance, `hcover` from the schedule's `δ_s→0` +
   cofinal z-ranges. NO chain telescoping needed. Original note:
   `ψ(xA)`'s window frequency converges because at
   stage `s` we forced `ψ(x) ∉ cfBadZone_z v n δ` for `n` in the stage's z-range,
   i.e. `|countOcc v (cfPref (ψxA) n) − γv·n| < δn + slack` at a cofinal set of
   `n` with `δ→0`. Package as a chain-frequency lemma for `ψxA` (mirror
   `chain_cf_digit_freq_tendsto_uniform`, blocks = z-digit ranges; per-block
   goodness from pullback-avoidance). ⇒ `CFOrbitEquidist (ψxA)`.
6. **Assemble** the NEW `exists_interleaved_affine_witness` proof: `xA` from (4),
   `ψxA` equidist from (5), `ψxA ∈ (0,1)` from feasibility + interval nesting,
   irrationality of `ψxA` from `xA` irrational + `q≠0`. Then EXCISE the two-stream
   `sorry` block (`schedA_block_linear` and its dead callers).

### Machinery confirmed present (survey 2026-08-24)
- Pullback: `affineMap`, `preimage_affineMap_Ioo`, `image_affineMap_Ioo`,
  `volume_preimage_affineMap_Ioo`, `volume_preimage_affineMap`,
  `good_mass_in_affine_preimage`, `affine_image_Ioo_subset_Icc_pre` (CFAffine / CFScheduleA).
- Gauss↔vol: `gaussMeasure_le_volume` (`≤ (log2)⁻¹·vol`), `volume_le_gaussMeasure`,
  `volume_le_ofReal_mul_gaussMeasure` (`vol ≤ (2 log2)·gauss` on `(0,1)`),
  `gaussMeasure_Ioo_toReal_ge/le`.
- Bad zones: `cfBadZone` (`TBrick:191`), `gaussMeasure_aggregate_cfBadZone_le`
  (`TBrick:201`, relative to base cylinder), `gaussMeasure_multiscale_cfBadZone_le`
  (`CFScheduleA:252`), `volume_iUnion_cfBadZone_le_vol`.
- Selection: `exists_irrational_mem_Ioo_notMem_of_gaussMeasure_lt` (`:402`),
  `exists_irrational_notMem_multiscale_cfBadZone_in_Ioo` (`:438`).
- Cylinder geom: `volume_cfCylinder` (`=1/(K(K+K'))`), `cfK_append_le`,
  `cfCylinder_subset_Icc_length`, `cfCylinder_endpoints`, `volume_cfCylinder_ge_inv`.
- Chain freq (reuse for x-side, mirror for z-side): `chainApp`,
  `chain_cf_digit_freq_tendsto_uniform`, `chain_orbit_equidist_uniform`,
  `chainTail_dev_prefix_var`, `slack_telescoping` (CFChainFreq).

---

## 📌 LAP STATUS 2026-08-24 (grind) — all DIRECTION-permitted doable work DONE; crux operator-gated (SUPERSEDED by the review-lap pivot above)

This lap discharged EVERY open DIRECTION obligation except the crux:
- **Item 2 (`TODO(shift)`) — DONE.** `exists_cfNormal_and_affine_cfNormal` proved
  for ALL real `r` (both infeasible halves) via new axiom-clean integer-shift
  machinery (`gaussMap_iter_two_add_nat`, `cfDigit_add_nat_shift`,
  `isCFNormal_add_nat`).  Commits `768edf0`, `da17950`.
- **Item 3 signpost (a) — DONE.** `interleaved_affine_target_not_always_nonempty`
  (proved negation, `q=1,r=1` witness).  Commit `83a420b`.
- **Item 3 signpost (b) — SATISFIED at sanctioned tier.** The `hdom` refutation is
  docstring-tier on both replacement cracks (`chain_cf_digit_freq_tendsto_uniform`,
  `chain_orbit_equidist_uniform`); kernel-tier is NOT owed (no cheap concrete
  witness — refuting the asymptotic needs the full Θ(word) construction).
- **Item 1 (crux `schedA_block_linear` :2537) — OPERATOR-GATED.** DIRECTION's
  ratified digit-capped route is refuted; the two-stream construction is obstructed
  (measure-budget blowup, `OBSTRUCTION-2026-08-24`); the obstruction doc + DIRECTION
  both say STOP for attended review, and the only viable route (single-stream
  pivot) needs altitude ratification a grind lap may not give ("do not grind
  substitutes").  → this is the `box stuck` (blocked-on-operator) condition:
  an altitude/attended lap must re-route DIRECTION to the single-stream pivot
  before the crux can advance.

## 🛑🛑🛑 ROUTE-DECISIVE OBSTRUCTION (2026-08-28) — see `OBSTRUCTION-2026-08-24-block-measure-budget.md`

**The two-stream construction forces SUPER-EXPONENTIAL blocks; `schedA_block_linear`
is NOT provable as-is.**  Deeper than the cfK issue: the freq-good *measure budget*
`n₁ ≳ 1/ρ` blows up because the x-block target `ρ = μ(target)/μ(cfCylinder wx) ≈
e^{-2κ|zblock|}` is exponentially small (the other stream is one full block deeper).
`n₁` sits inside the slack `C_s`, so `hslack` (`CFChainFreq.lean:567`) fails
independently of the length bound.  Verified against the code (target = full hull
`exists_Ioo_irrational_subset_cfCylinder`; budget `NS.card·A₁ < μ(target)`;
`schedEps s = 1/(s+1)`).  **This session's cfK lemmas are correct and reusable but
do NOT fix this** — the blowup is in the measure budget, not the resolution.

**PROPOSED PIVOT (needs attended ratification — DIRECTION mandates the two-stream
route, so a review lap must sanction the change):** single-stream construction
selecting `x` to avoid BOTH the x-CF bad zones AND the ψ-pullback
`ψ⁻¹(cfBadZone_z …)` of the z-bad-zones.  Target becomes the full `cfCylinder wx`
(`ρ=1`), budget polynomial, blocks linear.  Full analysis + why alternatives fail
in the obstruction doc.

**Directive item 2 — DONE (2026-08-24).** `exists_cfNormal_and_affine_cfNormal`
now proved for ALL real `r` (was: feasible `-q<r<1` only). Landed axiom-clean in
`CFScheduleA.lean`: `gaussMap_iter_two_add_nat` (`g²(y+n)=y`),
`cfDigit_add_nat_shift` (`cfDigit(y+n)(k+2)=cfDigit y k`), `isCFNormal_add_nat`
(integer up-shift invariance of CF-normality). Infeasible regime splits:
- **`r ≥ 1`:** shift the IMAGE up. `n=⌊r⌋≥1`, `r₀=r−n=fract r∈[0,1)⊂(−q,1)`,
  feasible witness at `r₀`, `ψ(x)=y+n` normal via `isCFNormal_add_nat`.
- **`r ≤ −q`:** shift the DOMAIN up (the earlier "length 1/q" worry was a MISCALC;
  shifting `x`, not the image, gives an interval of length `1+1/q>1` that ALWAYS
  contains an integer). Pick `M=⌊(−q−r)/q⌋+1≥1` (lower end `≥0` as `r≤−q`), so
  `r₁=qM+r∈(−q,1)`; feasible witness at `r₁` gives `x`, `y=qx+r₁∈(0,1)` normal;
  witness real `x'=x+M` is normal (up-shift) and `ψ(x')=qx'+r=qx+r₁=y`.

**The B6 crux `schedA_block_linear` (:2537) is now the SOLE remaining `sorry` in
src/** — under the two-stream measure-budget obstruction (below).

- **Landed 2026-08-28 (reusable core, axiom-clean, `CFScheduleA.lean`):**
  `cfFreq_tendsto_of_digit_shift` — window-frequency limit is invariant under a
  fixed digit shift `d'(k+m)=d k` (first `m` entries arbitrary).  Proof: split
  `(range p).map d' = pre ++ (range (p−m)).map d`, sandwich the count via
  `countOccurrences_le_append_left` / `countOccurrences_append_le`, squeeze
  `count_d(p−m)/p → γ` (product of `h∘(·−m)` and `(p−m)/p → 1`).
- **Orbit fact still needed (item-2 remainder):** for `y ∈ (0,1)` irrational and
  `n ≥ 1`, `cfDigit (y+n) 0 = 0`, `cfDigit (y+n) 1 = n`, and
  `cfDigit (y+n) (k+2) = cfDigit y k` — i.e. `digits(y+n) = [0,n] ++ digits(y)`.
  Verified on paper via the Gauss orbit: `g(y+n) = 1/(n+y)`, `g²(y+n) = y`, so the
  orbit from position 2 is `y`'s orbit.  With this, `IsCFNormal (y+n)` follows from
  `IsCFNormal y` by `cfFreq_tendsto_of_digit_shift` (`m := 2`, `d := cfDigit y`,
  `d' := cfDigit (y+n)`).  Then the `TODO(shift)` `sorry` closes: pick integer
  `n` with `r − n ∈ (−q, 1)` (feasible), apply the feasible witness at `r₀ = r−n`,
  and shift `ψ(x) = (qx+r₀) + n`.  **Caveat (r ≤ −q case):** `n` may be negative,
  making `qx+r < 0`; the `[0,n]++` prepend argument only covers `y+n > 1` (n ≥ 1).
  For the `r ≥ 1` half of the infeasible regime, `n ≥ 1` and this closes it; the
  `r ≤ −q` half needs either a negative-shift orbit fact or choosing `x` in a
  higher unit interval so `qx+r ∈ (0,1)`.  Prove the `cfDigit`-orbit facts next
  (elementary `gaussMap` computation — `gaussMap`, `Int.fract`, `cfDigit` defs in
  `CFDefs.lean`).

## 🧭 ROUTE CORRECTION (2026-08-28 grind lap) — DIGIT-CAP IS FATAL; cfK-BOUND-VIA-goodC IS THE ROUTE

The CURRENT DIRECTIVE's ratified "DIGIT-CAPPED steering" route for
`schedA_block_linear` is **refuted**, on two independent grounds:
- **A FIXED cap `D`** makes the limit `x` have no CF digit `> D` ⇒ `x` is badly
  approximable ⇒ NOT CF-normal (Gauss–Kuzmin puts mass on every digit).  Fatal to
  the headline.
- **A GROWING cap `D_s → ∞`** (needed for normality) makes
  `log cfK(w_s) ≈ ∑_t block_t·log(D_t+1)` **super-linear**, so the block length
  `|u_s| ≳ log cfK(w_s)` grows FASTER than `|w_s|` and the geometric bound
  `blk ≤ ρ·word` (fixed `ρ`, the exact hypothesis `slack_telescoping` needs)
  **fails**.  So the cap that was meant to *secure* the geometric bound *destroys*
  it.

**Correct control = the B5′ `cfK u ≤ exp(goodC·|u|)` bound** (`CFSchedule.lean`
`SchedStep` line 224, from `goodExtSet w goodC n` with volume `≥ ½·|I_w|`).  This
is the Lévy constant `(1/n)log q_n → π²/(12 ln 2)` made *uniform* — it holds on a
FULL-Gauss-measure set (not a support restriction), so it is compatible with
CF-normality, and it gives `log cfK(w_s) = O(|w_s|)` ⇒ resolution length `Nfib =
O(|w_s|)` ⇒ the geometric/affine block bound.

**Landed this lap (axiom-clean, `CFScheduleA.lean`):**
`exists_fib_threshold_linear_of_cfK` — the RESOLUTION HALF of
`schedA_block_linear`, discharged conditionally on the cfK-exp-bound:
`a ≤ 8·cfK(w)² ∧ cfK w ≤ exp(κ|w|) ⇒ ∃ N, (∀ n≥N, a < fib(n+1)²) ∧
N ≤ (κ/log φ)·|w| + C`.  The target-width reciprocal `a = 4/(d−c) ≤ 8 cfK²` holds
because `d−c ≥ 1/(2 cfK²)` (`volume_cfCylinder_ge_inv`, PROVED) when the target is
a fixed fraction of the cylinder.

**Landed 2026-08-28 (measure enabler, axiom-clean, `CFDigitLaw.lean`):**
`frac_mass_bad_extensions` — the ε-strengthening of `half_mass_long_extensions`:
`∀ ε>0, ∃ κ>0, ∀ w n, (cfK-bad extension mass, cfK u > e^{κn}) ≤ ε·|I_w|`.
Same Markov-on-`tsum_mul_log_cfK_le` argument, threshold `e^{κn}`, `κ = C₀/ε`.
This is the FRACTIONAL cfK-tail control the steer graft needs (the half-measure
`goodExtSet` bound alone is too weak to dominate a small steering target `A ⊆
I_wx`; the ε-version lets κ be chosen so the cfK-bad set cannot swallow the
freq-good surplus `μ(A\B)`).

**Landed 2026-08-28 (extraction core, axiom-clean, `CFScheduleA.lean`):**
`exists_irrational_mem_Ioo_notMem_of_gaussMeasure_lt` — abstract: any `B'` with
`gaussMeasure B' < gaussMeasure (Ioo c d)` misses an irrational point of `Ioo c
d`.  The graft passes `B' = (bad zones) ∪ (cfK-large extensions)`; it now only
needs `gaussMeasure(bad ∪ cfKbad) < gaussMeasure(Ioo c d)`.

**IMMEDIATE NEXT STEP — DONE (2026-08-28, axiom-clean, `CFDigitLaw.lean`):**
`cfKbadExtSet w κ n` defined; `volume_cfKbadExtSet` (= bad-branch tsum),
`measurableSet_cfKbadExtSet`, and `exists_rate_gaussMeasure_cfKbadExtSet_le`
(∀ε>0 ∃κ>0, `gaussMeasure(cfKbadExtSet w κ n) ≤ ofReal((log 2)⁻¹·ε)·volume(I_w)`)
all proved.  So the graft's `B'`-mass bound is in hand.

**Landed 2026-08-28 (combined selection, axiom-clean, `CFScheduleA.lean`):**
`exists_irrational_notMem_multiscale_cfBadZone_cfK_in_Ioo` — same as the
multiscale selection but `hbound` leaves room for `(gaussMeasure(cfKbadExtSet wx κ
ntop)).toReal`, returning an irrational point of `(c,d)` that is freq-good at every
scale AND avoids the cfK-large set (⇒ `cfK` of its length-`ntop` extension past
`wx` is `≤ e^{κ·ntop}`).  Also confirmed `cfK_append_le` (`CFCylinder.lean`):
`cfK(w++u) ≤ 2·cfK w·cfK u`, so the accumulated invariant `cfK(w_s) ≤ e^{κ'|w_s|}`
closes with `κ' = κ + log 2` (each stage's `log 2` is absorbed since `s ≤ |w_s|`).

**NOW: build the cfK-carrying steer block** — a `_cfK` variant of
`exists_multiscale_freq_good_block_steer_len` that calls the combined selection
above (instead of `exists_irrational_notMem_multiscale_cfBadZone_in_Ioo`), reads
off the digit block `u` via `range_map_cfDigit_eq`, and adds the conclusion
`(cfK u : ℝ) ≤ e^{κ·ntop}` (from `x ∉ cfKbadExtSet` unpacked through
`cfKbadExtSet` membership: `x ∈ cfCylinder(wx++u)` with `u` its digit word forces
the good branch, i.e. `cfK u ≤ e^{κ ntop}`).  The `hbound` for the combined
selection is met by choosing `ntop`'s `n₁` large (measure budget, as now) AND `κ`
from `exists_rate_gaussMeasure_cfKbadExtSet_le ε` with `ε` a fixed fraction of the
inner-target surplus.  ⚠️ still open: the κ-uniformity check (see below) — verify
`ε` (hence `κ`) can be a per-level CONSTANT, using the recursion's hull invariants
(`SchedStateA.hzhull`, `hinv`) to lower-bound the target/cylinder Gauss-measure
ratio.  If that ratio is bounded below across stages, `κ` is uniform and the graft
closes; establish it as a lemma about the seeded recursion geometry.

**(historical detail) assemble the cfK-carrying steer block.** With `A = Ioo c' d'`,
`B` = multiscale bad zones, `S = cfKbadExtSet wx κ ntop`:
`gaussMeasure (B ∪ S) ≤ gaussMeasure B + gaussMeasure S`; bound `gaussMeasure B`
by `gaussMeasure_multiscale_cfBadZone_le`+`hbound` (already `< μ(inner target)`)
and `gaussMeasure S ≤ ofReal((log2)⁻¹ε)·volume(I_wx) ≤ 2ε·gaussMeasure(I_wx)`
(via `volume_le_gaussMeasure`).  Pick ε so the sum stays `< gaussMeasure(Ioo c
d)`; feed `exists_irrational_mem_Ioo_notMem_of_gaussMeasure_lt` to get an
irrational `x ∈ (c,d)\(B∪S)`.  `x∉S` + `range_map_cfDigit_eq` ⇒ the block word
`u` has `cfK u ≤ e^{κ·ntop} = e^{κ·|u|}`.  Thread this cfK field up through
`StepSpecA`/`schedStepA`, maintain the accumulated invariant `cfK(w_s) ≤
e^{κ|w_s|}` (needs a `cfK_append_le`: `log cfK(w++u) ≤ log cfK w + log cfK u +
O(1)` — check `CFCylinder`/`CFDigitLaw` for `cfK` recurrence), and feed
`exists_fib_threshold_linear_of_cfK` to close `schedA_block_linear`.

**⚠️ ROUTE-DECISIVE QUESTION SURFACED THIS LAP (κ-uniformity):** the rate
`κ = C₀/ε` from `frac_mass_bad_extensions` grows as the surplus fraction
`ε ~ μ(A\B)/μ(I_wx)` shrinks.  For `schedA_block_linear` to have a FIXED `K₁ =
κ/log φ`, `κ` must be bounded across stages, i.e. the steering target `A_s` must
stay a bounded fraction of `cfCylinder wx_s`.  If targets shrink unboundedly
(likely, since nested cylinders converge), `κ_s → ∞` and the affine bound
degrades.  **Candidate fix:** apply `frac_mass` to the TARGET sub-cylinder rather
than `I_wx` (the block's cfK is a property of digits past `wx`, so the relevant
base is the deepest common cylinder containing `A_s`, not `wx_s`), OR restructure
so each block first refines to a cfK-good sub-cylinder of controlled relative
size THEN steers within it (B5′-style refine-then-place).  This is the next
route-decisive probe; settle it before the full plumbing.

**NEXT (the graft, now with both halves in hand):** build
`exists_multiscale_freq_good_block_steer_len` + a cfK conclusion by intersecting
the selection with the `cfK ≤ e^{κ·ntop}` set.  Concretely, in
`exists_irrational_notMem_multiscale_cfBadZone_in_Ioo` the point is chosen from
`A \ B` with `μ(A\B) > 0` (`A = Ioo c' d'`, `B` = bad zones,
`μ(B) < μ(A) − μ(A\B)`).  Add a third excluded set `G^c` (cfK-bad extensions
past `wx`): by `frac_mass_bad_extensions` with `ε = μ(A\B)/(2·μ(I_wx))` and the
volume→gauss comparison, `μ(A ∩ G^c) ≤ ...` stays below `μ(A\B)`, so
`(A\B) ∩ G` has positive measure ⇒ an irrational point there.  Read off its digit
word `u` (`range_map_cfDigit_eq`); `exists_word_of_mem_goodExtSet`-style gives
`cfK u ≤ e^{κ·ntop} = e^{κ·|u|}`.  Then feed `exists_fib_threshold_linear_of_cfK`
to close `schedA_block_linear`.  ⚠️ the one arithmetic wrinkle: `frac_mass_bad`
bounds LEBESGUE volume of the bad extensions, while `A\B` positivity is in GAUSS
measure — bridge with `volume_le_ofReal_mul_gaussMeasure` /
`volume_le_gaussMeasure` (`TBrickRefine.lean`), both directions available.

**OLD framing (superseded by the two lemmas above):**
graft `cfK u ≤ exp(goodC·|u|)` onto the multiscale steer block
`exists_multiscale_freq_good_block_steer_len` — intersect its scale-selection set
with `goodExtSet wx goodC ·` (positive measure retained: freq-good set has measure
`≥ γ`, `goodExtSet` has measure `≥ ½·|I_w|`, and for the tail-controlled subset
both hold simultaneously by the B5′ `goodC_half` union bound).  Once the steer
block carries an exp-cfK field, thread it up through `StepSpecA` and feed
`exists_fib_threshold_linear_of_cfK` to close `schedA_block_linear` with an
explicit affine `(K₁,K₂)`.  **This SUPERSEDES the `exists_uniform_block_param_tight`
"tight length" path in the item-1 note below — the length is now controlled through
`Nfib = O(|w|)`, not through shrinking `m`.**


## 🟢🟢🟢 FRONTIER (2026-08-24 grind session): B6 CRUX ASSEMBLED — rests on ONE math lemma

The crux `exists_interleaved_affine_witness` is now FULLY MACHINE-CHECKED except
for `schedA_block_linear` (+ the shift branch). Built this session (all axiom-clean,
`CFScheduleA.lean`):
- `SchedStateA`/`StepSpecA`/`schedStepA_exists`/`exists_seedStateA`/`schedA` — the
  two-stream recursion + feasible seed (seed uses wz-hull `(e0,f0) ⊆ [r,q+r]`).
- `wxSeq`/`wzSeq` genuine extending chains; `SchedStateA.hzhull` invariant
  (`cfCylinder wz ⊆ Icc e f`) threaded through the uniform ψ-step.
- Crux proof: both limit points; `ψ(xA)=zA` via shrinking-`Icc` squeeze
  (`Ioo_sub_le_volume_cfCylinder` + `cfCylinder_chain_volume_tendsto` +
  `eq_of_mem_iInter_Icc`); both orbits via `chain_orbit_equidist_uniform`.
- `chain_hfreq_of_uniform_blocks` (shared): discharges `hblock` (schedEps→0) +
  `hslack` (`slack_telescoping`), all hyps proved incl. `chain_slack_littleO`
  (C=o(blk), PROVED via squaring trick) and `schedA_block_geom` (PROVED from
  `schedA_block_linear` via `|w s|≥1`).
- `exists_fib_threshold_log` (PROVED): resolution threshold `N ≤ log_φ(√5√a+1)+1`.

**THE ONE OPEN MATH OBLIGATION — `schedA_block_linear`** (`CFScheduleA.lean`):
`|chainApp w s| ≤ K₁·|w s| + K₂` (affine block-length bound). Path (all atoms exist):
1. **Tight length-exposing ψ-step.** Rebuild `exists_uniformly_freq_good_block_steer_len`
   → `_tight`: use `exists_uniform_block_param_tight` (PROVED, gives `m² ≤
   6(L+Nfib)+2+2⌈2/β⌉⁴`) instead of `exists_uniform_block_param` (quadratically
   lossy). Block `|u| = n₁+m² ≤ 2m²`. Expose `|u| ≤` explicit(L,Nfib,β) through
   `exists_freq_good_extend_affine_steer_uniform` → add an upper-length field to
   `StepSpecA`.
2. **Resolution `Nfib ≲ |w|`.** Target width `d−c ≳ 1/cfK²` (`volume_cfCylinder_ge_inv`,
   PROVED), so `Nfib ≤ log_φ(√5√(4/(d−c))+1)+1 ≲ log(cfK)` via `exists_fib_threshold_log`
   (PROVED). **🚩 ROUTE-DECISIVE FINDING (2026-08-24):** `log(cfK w) = O(|w|)` holds
   ONLY IF the block digits are controlled — `cfK(a₁…aₙ) ≤ ∏(aᵢ+1)` (`cfK_le_prod`),
   unbounded for large digits. The affine steer block (`exists_uniformly_freq_good_block_steer`)
   currently produces digits ≥1 with NO upper bound, so `cfK` (hence target width, hence
   `Nfib`) is UNCONTROLLED and `schedA_block_linear` is NOT provable as-is. **FIX:** the
   steer block must additionally satisfy `cfK u ≤ exp(c·|u|)` — the B5′ `goodExtSet
   goodC` mechanism (`CFSchedule` `SchedStep` line 233 `cfK u ≤ exp(goodC·nFn)`). Since
   the bounded-`cfK` set has full Gauss measure (Lévy: `cfK^{1/n}→e^{π²/12ln2}` a.e.),
   intersecting it with the bad-zone-avoiding set keeps positive measure ⇒ a freq-good
   AND `cfK`-bounded block exists. This is the NEW hardest sub-obligation: rebuild the
   steer block to carry a `cfK`-bound. (Atoms: `cfK_le_prod`, `tsum_mul_log_cfK_le`,
   B5′ `goodExtSet`/`goodC`.)
3. **Word-independent β.** `β = γtar·δ²/(S+1)`; `γtar/γwx = Θ(q)` by Gauss-density
   ratio bounds `gaussMeasure_Ioo_toReal_ge/le` (PROVED) ⇒ `⌈2/β⌉ ≲ poly(s) ≤ |w|`.
4. Assemble `|u_s| ≤ K₁|w_s|+K₂`.

Then B6 (feasible) is DONE; only the shift branch (`IsCFNormal_add_int`) remains for
the unconditional deliverable.

---

## 🚩🚩🚩 JUDGE-FLAG 2026-08-24 (grind lap): the crux was FALSE as stated — RESTRICTED to feasible `r`, deliverable reduction now needs a shift lemma (commit `<this>`)

**Route-decisive discovery (for the altitude/review lap to ratify).** The crux
`exists_interleaved_affine_witness` demanded, unconditionally in `r`, a single
`x` with `x ∈ (0,1)` AND `ψ(x)=q·x+r ∈ (0,1)`. **This is outright FALSE for
`r ∉ (-q, 1)`**: e.g. `(q,r)=(1,5)` needs `x∈(0,1)` and `x+5∈(0,1)`, impossible.
The feasible set `(0,1) ∩ ψ⁻¹(0,1) = (max 0 (-r/q), min 1 ((1-r)/q))` is nonempty
**iff `-q < r < 1`**.  No hdom-free assembly can ever discharge the old statement
— the entire directive's "assemble the limit" plan rested on a false target.

**Fix applied this lap (additive-safe; crux was the open `sorry`, not frozen):**
- **Crux now carries `(hr : -q < r ∧ r < 1)`** — exactly the feasibility that
  seeding the two-stream recursion needs, and now a TRUE statement the recursion
  CAN close.  The item-2/item-3 recipe below is unchanged EXCEPT the seed state
  is built inside the feasible interval (`hr` gives it nonempty).
- **`exists_cfNormal_and_affine_cfNormal` stays UNCONDITIONAL** (`q>0`, all `r`):
  `by_cases` on `-q<r<1`; feasible → crux directly; else a NEW disclosed `sorry`
  (`TODO(shift)`) reducing general `r` to the feasible representative via
  integer-shift invariance of CF-normality (the Gauss orbit ignores the integer
  part of `ψ(x)`).  **New leaf obligation:** `IsCFNormal_add_int` (or a mod-1
  reduction) — CF-normality of `y` and `y - ⌊y⌋` coincide asymptotically because
  a single anomalous digit-0 at position 0 is frequency-negligible.  This is the
  ONLY piece keeping the deliverable at `sorryAx`; it is genuine but leaf-level.
- Axioms re-checked: B5′ headline stays `[propext, Classical.choice, Quot.sound]`;
  `exists_cfNormal_and_affine_cfNormal` carries `sorryAx` (crux + shift, disclosed).

**Two open `src/` sorries now:** (1) the feasible crux (item-3 recursion, below),
(2) the `TODO(shift)` general-`r` reduction (leaf: `IsCFNormal_add_int`).

### 🎯 NEXT crux-blocker (grind lap 2026-08-24): `hgeom` (block ≤ ρ·word) needs a WORD-INDEPENDENT block bound — the current block sizer is quadratically lossy
`slack_telescoping` (PROVED this lap) reduces `hslack` to `hgeom : blk s ≤ ρ·word s`
(+ `C=o(blk)`, `blk→∞`).  Supplying `hgeom` needs the per-round block length
`|u_s| = n₁+m²` bounded by `ρ·|w_s|`.  Two lossy spots in the CURRENT sizer block this:
1. **`exists_uniform_block_param` is quadratically lossy.**  It returns
   `m = max(Lc, Nfib, ⌈2/β⌉², 1)` but the constraints only require `m² ≥ Lc`,
   `m² ≥ Nfib`, `(m+1)/(m√m) < β` — i.e. `m ≥ √Lc, √Nfib, ~1/β²`.  Picking `m ≥ Lc`
   (not `√Lc`) makes `|u| = m² ~ Nfib² ~ |wx|²` — QUADRATIC in the word, breaking
   `hgeom`.  **Fix:** a tight variant returning `m = max(⌈√Lc⌉, ⌈√Nfib⌉, ⌈4/β²⌉+1)`,
   so `m² ~ max(Lc, Nfib, 16/β⁴)`.  Since `Nfib ~ |wx|` (resolution `4/(d−c) <
   fib(|wx|+block+1)²`, `d−c ~ φ^{−2|wx|}` ⇒ `Nfib ~ |wx|`), tight `|u| ~ |wx|` ⇒
   `word` roughly DOUBLES per step (geometric) ⇒ `hgeom` with `ρ ~ 2`. ✓
2. **`β = γtar·δ²/(S+1)` with `S ∋ γwx` is word-dependent.**  As `|wx|→∞`,
   `γtar, γwx ~ φ^{−2|wx|} → 0`, so the `+1` dominates `S`, `β ~ γtar·δ² → 0`, and
   `1/β⁴ → φ^{8|wx|}` (exponential block).  **Fix:** the REAL constraint `hbound` is
   `(m+1)·S₀·γwx/(δ²n₁) < γtar` i.e. `(m+1)/n₁ < (δ²/S₀)·(γtar/γwx)`, and
   **`γtar/γwx = Θ(q)` is WORD-INDEPENDENT** (both are Gauss measures of intervals
   of comparable width `~φ^{−2|wx|}`; the Gauss density is bounded in `[1/(2ln2),
   1/ln2]` on `[0,1]`, and `|ψ-image|/|source| = q`).  So use `β := (δ²/(S₀+1))·(q-lower-bound-on-γtar/γwx)`, word-independent ⇒ the `16/β⁴` term is a
   per-level CONSTANT `B(t)` ⇒ with promotion (`|w_s| ≥ B(t)` before bumping `t`),
   `|u_s| ~ max(|wx|, B(t)) ~ |wx|`. ✓
- **Net remaining item-3 build (revised, hardest-first):**
  (i) tight `exists_uniform_block_param'` (`m ~ √max(...)`) — ✅ DONE
      (`exists_uniform_block_param_tight`, commit `9b90960`, axiom-clean).
  (ii) word-independent-`β` uniform block variant exposing `|u| ≤ ρ·|wx|` (factor
       `γwx` out of the budget via `γtar/γwx ≥ q·c₀`); (iii) length-exposing affine
  step; (iv) `SchedStateA`+promotion; (v) chains → `slack_telescoping`+`hblock` →
  `chain_orbit_equidist_uniform` → assemble feasible crux.  Analytic core DONE
  (`slack_telescoping`); (i) DONE; (ii) is the route-decisive measure lemma.

### 🔗 item-(ii) REFINEMENT (grind lap 2026-08-24): the measure ratio needs STREAM BALANCE `|wx| ~ |wz|`
Building (ii), the `γtar/γwx` cancellation is subtler than "both `~φ^{−2|wx|}`":
- In the z-block placement (`exists_freq_good_block_steer wz … into ψ((a,b))`), the
  `_len` budget's `γwx` is `gaussMeasure (cfCylinder wz)` (word being extended) while
  `γtar` = middle-half measure of the target `ψ((a,b))`, with `(a,b) ~ cfCylinder wx`.
  So `γtar/γwz ~ q·(φ^{−2|wx|}/φ^{−2|wz|})` — word-independent **iff `|wx| ~ |wz|`**
  (the two streams' cylinder widths must stay comparable).  If a stream races ahead,
  its cylinder is exponentially narrower and the ratio blows up.
- **⇒ new recursion invariant: `|wx_s| ~ |wz_s|` (balance).**  The affine step already
  extends both streams each round by comparable freq-good blocks; the schedule must
  pick block lengths to keep `| |wx_s| − |wz_s| |` bounded (e.g. extend the shorter
  stream first, or clamp both blocks to a common target length).  This is an EXTRA
  invariant `SchedStateA` carries alongside promotion + the interval invariant.
- **Cleaner build for (ii)+(iii):** do NOT rebuild `exists_uniformly_freq_good_block_steer_len`.
  Call the non-`_len` `exists_uniformly_freq_good_block_steer` DIRECTLY (it takes
  `m,n₁,hbound,hres` and returns exact `|u| = n₁+m²`).  Supply `m` from
  `exists_uniform_block_param_tight` (word-independent bound), and prove `hbound`
  from the measure-ratio lemma `γtar ≥ q·c₀·γwx` (the one genuinely new measure fact,
  provable from Gauss-density bounds `[1/(2ln2), 1/ln2]` + `|ψ-image|/|source| = q` +
  balance) and `hres` from `Nfib ~ |wx|`.  Output exposes `|u| = n₁+m² ≤ tight-bound`.
- **Route status:** both isolated analytic doubts (telescoping, tight length) are
  KERNEL-PROVED; remaining item-3 work is COUPLED BOOKKEEPING (balance + promotion +
  measure-ratio), not a new analytic wall.

### ✅ RESOLVED item-3 feasibility (grind lap 2026-08-24, later): `hslack` CLOSES — tool = `Asymptotics.IsLittleO.sum_range`; needs block ≤ ρ·word (length-exposing step + promotion)
Corrects the (over-pessimistic) note below.  Two facts settle `hslack`:
- **Geometric measure factors CANCEL.**  Budget `hbound`: `(m+1)·A₁ < γtar` with
  `A₁ = Σ_v 7(8|v|+80)·γ_v·γ_wx/(δ²n₁)` and `γtar` = middle-half measure of the
  steer target.  BOTH `γ_wx` and `γtar` scale like the current interval width
  `~φ^{-2|w_s|}`, so they cancel: forced block `|u_s| = n₁+m² ~ (S₀/δ²)²` with
  `S₀ = Σ_v 7(8|v|+80)γ_v` **family-only, `|w_s|`-independent**.  ⇒ between
  promotions block length is a CONSTANT `B(t)`; word grows LINEARLY by `B(t)/step`.
- **`hslack` via `Asymptotics.IsLittleO.sum_range`** (mathlib,
  `Analysis/Asymptotics/SpecificAsymptotics.lean:136`): if `f =o[atTop] g`, `g≥0`,
  `Σg → ∞`, then `Σf =o Σg`.  Take `f i = C(s₀+i)+(|v|−1)`, `g i = |u_{s₀+i}|`.
  Then (a) `C_s/|u_s| → 0` [from `n₁²≤|u|·√|u| ⇒ n₁≤|u|^{3/4}`, so
  `C_s = 4√|u_s|+2|v|+n₁_s = o(|u_s|)`], (b) `Σ|u_s| → ∞` [from `|u_s|≥L_s→∞`].
  ⇒ `Σ_{i<n} f = o(Σ_{i<n}|u|) = o(|w(s₀+n)|−|w s₀|)`.
- **THE off-by-one CATCH (real, localizes the promotion need).**  `hslack`'s
  numerator sums `range(k+1)` (`k+1` blocks) but its RHS word `|w(s₀+k)|` holds
  only `k` blocks.  `o(|w(s₀+k+1)|)` gives the needed `< ε|w(s₀+k)|` **iff
  `|w(s₀+k+1)| ≤ ρ·|w(s₀+k)|`** — block `≤ ρ·word`, i.e. word grows at most
  geometrically.  This upper bound is the ONLY thing promotion is needed for: it
  keeps `B(t) ≤ ρ|w_s|` (promote to `t` only once `|w_s| ≥ promThreshold(t)`), so
  `|u_s| = O(|w_s|)`.  Without an UPPER block bound the tail term
  `|u_{s₀+k}| ~ |w(s₀+k+1)|` can dwarf `|w(s₀+k)|`.

**Concrete item-3 build order (revised):**
1. **Length-exposing uniform affine step** — variant of
   `exists_freq_good_extend_affine_steer_uniform` that calls
   `exists_uniformly_freq_good_block_steer` DIRECTLY (not the `_len` wrapper),
   taking `m,n₁` (or exposing `|u_·| = n₁+m²`) so the CALLER controls block length
   and can enforce `|u_s| ≤ ρ|w_s|`.  (The `_len` wrapper hides the length — that's
   why the current `_steer_uniform` can't supply the upper bound.)
2. **Abstract slack lemma** `slack_telescoping` — from `IsLittleO.sum_range`, the
   generic `Σ(C+c) < ε·word` conclusion given `C=o(blk)`, `Σblk→∞`,
   `word(s+1)=word s+blk s`, `blk s ≤ ρ·word s`.  Self-contained; PROVABLE NOW.
3. **`SchedStateA` + promotion** (counter `t`, mirror `CFSchedule`); `schedA`;
   chains; feed `chain_orbit_equidist_uniform` (`hblock` from `δ_s→0`+coverage,
   `hslack` from the abstract lemma).  Assemble the feasible crux.

### ⚠️ (SUPERSEDED by the ✅ above) SHARPENED item-3 feasibility: the NAIVE schedule breaks `hslack` — SLOW PROMOTION is mandatory
The directive/handoff item-3 sketch (`F_s = wordFamily s`, `δ_s = 1/(s+1)`,
`L_s = |w_s|`) does NOT close `hslack`.  Reason, traced through the block sizer:
- `exists_uniformly_freq_good_block_steer` fixes `|u| = n₁ + m²` with `n₁ = m·⌊√m⌋`,
  and the measure budget forces `m ≳ (S/(δ²·γtar))²` where
  `S = ∑_{v∈F} 7(8|v|+80)·γ_v·γ_wx` (`exists_uniform_block_param`, `hbound`).
- With `F_s = wordFamily s`, `|F_s| ~ s^s` and `δ_s² = 1/(s+1)²`, so `S_s` and hence
  the forced block `|u_s| = m² ≳ (S_s (s+1)²/γtar)²` grow **tower-like** — far faster
  than any geometric word growth.  Then `|w_{s+1}| ≫ |w_s|`, and the `hslack` term
  `C(s₀+k) ~ |u_{s₀+k}|^{3/4} ~ |w_{s₀+k+1}|^{3/4}` is NOT `o(|w_{s₀+k}|)` (ratio
  `|w_{s+1}|^{3/4}/|w_s| → ∞` once `|w_{s+1}| ≫ |w_s|^{4/3}`).  **`hslack` FAILS.**
- **Fix = mirror `CFSchedule`'s promotion** (`SchedState.t`, `promThreshold`,
  `sched_prom_invariant`): keep the family FIXED at `wordFamily t` across many
  stages, bumping `t → t+1` only once the accumulated word is long enough that the
  next block is still `o(word)`.  Then between promotions `S` is constant, blocks
  are `poly`-bounded, word growth dominates, and `∑ C_i = o(word)` telescopes.
  Coverage (every `v` eventually in `F`) still holds because `t → ∞` (mirror
  `sched_t_tendsto`); `mem_wordFamily_eventually` (PROVED this lap, `CFScheduleA`)
  supplies the per-`v` threshold.
- **Net:** item-3's `SchedStateA` must carry a promotion counter `t` (as
  `CFSchedule.SchedState` does), not just `(wx,wz,e,f)`.  `L_s`/`δ_s` tie to `t`,
  and the promotion rule guarantees `|u_s|/|w_s|` stays bounded — the real content
  behind `hslack`.  This is the route-decisive uncertainty, now LOCALIZED to the
  promotion-rate bookkeeping (not a new analytic wall).  Building block landed:
  `mem_wordFamily_eventually`.


## ⭐⭐⭐⭐⭐⭐⭐ ADVANCE 2026-08-24 (review lap, later): per-round FEASIBILITY discharged — `exists_uniformly_freq_good_block_steer_len` (commit `4d1e5c9`, axiom-clean)

The directive's item-2 route-decisive question — *can each round jointly satisfy
the measure budget AND the resolution?* — is now settled YES in the kernel.
- **`exists_uniform_block_param`** (`CFScheduleA`): archimedean core. For any
  `β>0`, `Lc`, `Nfib`, gives `m>0` with `m²≥Lc`, `m²≥Nfib`,
  `(m+1)/(m·⌊√m⌋) < β`.  (`n₁ = m·⌊√m⌋` ⇒ `m ≪ n₁ ≪ m²`.)
- **`exists_uniformly_freq_good_block_steer_len`** (`CFScheduleA`): caller gives
  only a min-length `L`; internally sets `β = γtar·δ²/(S+1)` and discharges both
  budget inequalities. Output: `∃ u n₁, L≤|u| ∧ … ∧ cfCylinder(wx++u)⊆(c,d) ∧
  n₁²≤|u|·⌊√|u|⌋ ∧ (∀k≤|u|,∀v∈F, |dev(u.take k)| < δ·k + (4⌊√|u|⌋+2|v|+n₁)) ∧ ∃x…`.
  The folded bound is EXACTLY the `hblock` shape; `n₁²≤|u|·⌊√|u|⌋` (⇒ `n₁≤|u|^{3/4}`)
  is the `o(|u|)` witness the `hslack` telescoping needs.

### REMAINING item 2 — wire the len-wrapper into the ψ-round
Build `exists_freq_good_extend_affine_steer_uniform` (copy-extend, do NOT edit the
existing `exists_freq_good_extend_affine_steer`): same shape but call
`exists_uniformly_freq_good_block_steer_len` for BOTH streams (z into the image
interval `J_z`, x into `(a,b)∩ψ⁻¹(J_z')`), passing a caller min-length `L`. Emit,
per stream, the appended block `w'.drop|w| = u` with:
  (i) the folded uniform prefix bound (`hblock`-ready), and (ii) `n₁,u² ≤ |u|·⌊√|u|⌋`.
Everything else (interval bookkeeping, `hinv'`, nesting) copies the existing steer
ψ-round verbatim — only the block-producer call + the two extra emitted facts change.

### THEN item 3 — the two-stream recursion (`SchedStateA`/`schedStepA`/`schedA`)
Mirror `CFSchedule.sched`. Choose per round `δ_s = 1/(s+1)` (→0 ⇒ `hblock` margin),
`L_s = |w_s|` (⇒ geometric growth `|w_{s+1}| ≥ 2|w_s|`). Then build, for each stream,
`C_s := 4⌊√|u_s|⌋ + 2|v| + n₁,s` and prove:
  - `hblock`: `∀ε>0 ∃s₀ ∀s≥s₀ ∀q≤|u_s|, |dev(u_s.take q)| < ε·q + C_s` — from the
    folded bound + `δ_s→0` (pick `s₀` with `1/(s₀+1)<ε`).
  - `hslack`: `∑_{i≤k}(C(s₀+i)+(|v|−1)) < ε·|w(s₀+k)|` — from geometric `|w_s|`
    growth: `∑4⌊√|u_i|⌋`, `∑n₁,i` (each `≤|u_i|^{3/4}=o(|w_i|)`), `∑2|v|`, `∑(|v|−1)`
    all `o(word)` (geometric sum dominated by last term; `Filter.Tendsto` lemmas).
Feed both into `chain_orbit_equidist_uniform` → both streams `CFOrbitEquidist` →
assemble `exists_interleaved_affine_witness`. Limit-gluing toolkit READY
(`eq_of_mem_iInter_Icc`, `cfCylinder_chain_volume_tendsto`,
`irrational_mem_Ioo_of_mem_iInter_cfCylinder`).

## ⭐⭐⭐⭐⭐⭐⭐ ADVANCE 2026-08-24 (review lap): the ROUTE-DECISIVE mid-block bound is PROVED hdom-free — `chainTail_dev_prefix_var` (commit `2c61e7c`, axiom-clean)

The review lap named the decisive open question: *does the mid-block prefix bound
close WITHOUT `hdom`?*  Now settled YES in the kernel.
**`chainTail_dev_prefix_var`** (`CFChainFreq.lean`, after `chainTail_dev_split_var`):
given each appended block is uniformly prefix-good
(`∀ q ≤ |block s|, |dev(block_s.take q)| < ε·q + C s`), EVERY prefix of the
accumulated tail `chainTail w s₀ (s₀+k+1)` is good:
`∀ q ≤ |tail|, |dev(tail.take q)| < ε·q + ∑_{i≤k}(C(s₀+i)+(|v|−1))`.
Induction on `k`: prefix lands in the tail (IH) or reaches the last block
(whole-tail bound via `chainTail_dev_split_var` ⊕ block's OWN prefix bound at `j`,
composed by `countOccurrences_append_addslack₂`).  This is the exact hdom-free
replacement for `cfDiscLt_append_take` (CFChainFreq:450).

### REMAINING for the hdom-free limit (metric wrapper) — decomposition worked out this lap
**`chain_cf_digit_freq_tendsto_uniform`** (copy-extend `CFChainFreq`, NEVER edit
the existing `chain_cf_digit_freq_tendsto`): `Tendsto (fun p => countOcc v (cfPref y p)/p) atTop (𝓝 γv)`.
Clean hypothesis set (schedule-providable):
- `C : ℕ → ℝ`, `hC : ∀ s, 0 ≤ C s`  (per-stage additive slack; for the schedule
  `C_s = 4√|block_s| + 2|v| + n₁_s`).
- `hblock : ∀ ε>0, ∃ s₀, ∀ s ≥ s₀, ∀ q ≤ |chainApp w s|, |dev((chainApp w s).take q)| < ε·q + C s`
  — absorbs the margin `δ_s → 0` (past `s₀(ε)`, `δ_s < ε`).  Feeds `chainTail_dev_prefix_var`.
- `hslack : ∀ ε>0, ∀ s₀, ∃ K, ∀ k ≥ K, ∑_{i∈range(k+1)}(C(s₀+i)+(|v|−1)) < ε·(w (s₀+k)).length`
  — the `∑ C = o(word)` telescoping.  **NB use `(w (s₀+k)).length` (word BEFORE
  the last block), not `(s₀+k+1)`**: for the stage `k` with `|w(s₀+k)| < p ≤ |w(s₀+k+1)|`,
  this gives `∑ < ε·|w(s₀+k)| < ε·p` (the `+1` form is `≥ p`, wrong direction).
Proof (mirror `chain_cf_digit_freq_tendsto` steps, hdom-free):
  1. fix ε; `hblock (ε/4) → s₀`; feed `chainTail_dev_prefix_var` (ε:=ε/4) → tail
     prefix bound.  `hslack (ε/4) s₀ → K`.
  2. `cfPref y p = w s₀ ++ (chainTail w s₀ S).take (p−L₀)` for `S = s₀+k+1` large
     (`chain_cfPref_eq` + `w_eq_append_tail` + `List.take_append`), `L₀ = |w s₀|`.
     Locate `k` = least with `|w(s₀+k+1)| ≥ p` (via `chain_exists_stage`); then
     `|w(s₀+k)| < p`.
  3. compose fixed short prefix `w s₀` (`|dev(w s₀)| ≤ L₀`, crude `C₀ = L₀+1`) with
     the tail prefix via `countOccurrences_append_addslack₂`:
     `|dev(cfPref y p)| < (ε/4)·p + (C₀ + ∑_{i≤k}(...) + (|v|−1))`.
  4. `∑_{i≤k} < (ε/4)|w(s₀+k)| < (ε/4)p` (hslack, k≥K), and `C₀+(|v|−1) < (ε/4)p`
     for `p` large ⇒ `|dev| < ε·p`.  Convert to `Metric.tendsto_atTop` (mirror
     CFChainFreq:451-465).
Then `chain_orbit_equidist`-style wrapper (the orbit↔window tail at CFChainFreq:491-525
is REUSABLE — feed the new limit instead of `chain_cf_digit_freq_tendsto`).
Then ψ-round `_uniform` + `SchedStateA` recursion discharge `hblock`/`hslack` from
`exists_uniformly_freq_good_block_steer` + geometric block growth.

## ⭐⭐⭐⭐⭐⭐ ROUTE-DECISIVE CORRECTION 2026-08-24 (this lap, LATER): `hdom` is UNATTAINABLE for the affine schedule — steer blocks are `Θ(word)`, NOT `o(word)`. The hdom-free UNIFORM-GOODNESS route is MANDATORY, and its crux is **uniformly-good steer blocks**.

**This SUPERSEDES the "tight blocks ⇒ hdom holds" claim I made earlier THIS lap
(the four `goldenRatio`/`fib` commits).** Those lemmas are still needed (they cut
block length from `exp(word)` to `Θ(word)` and bound the additive slack), but they
do NOT rescue `hdom`. Compiler-grounded proof of unattainability:

### Why blocks are `Θ(word)`, not `o(word)`
To keep `ψ(cfCylinder wx') ⊆ cfCylinder wz'`, the x-block must RESOLVE `wx` down to
`wz'`'s metric scale. The z-target width is `≈ volume(cfCylinder wx) = 1/(Kₓ(Kₓ+Kₓ'))`
where `Kₓ = cfK wx` (the continuant), so the resolution needs
`fib(|wz|+nz+1)² > 4/(q·width) ≈ Kₓ²`, i.e. `|wz|+nz ≈ log_φ Kₓ`. But `log_φ Kₓ`
is `Θ(|wx|)` — NOT `O(1)` — because `cfK` grows geometrically with LENGTH
(Lévy: `log Kₙ/n → π²/(12 ln2) ≈ 1.19`, so `log_φ Kₓ ≈ 2.46·|wx|`). Hence
`nz ≈ 2.46|wx| − |wz| = Θ(word)`. Balanced streams ⇒ each round appends
`block_s ≈ κ·|w_s|` (`κ = Θ(1)`) ⇒ `|w_{s+1}| ≈ (1+κ)|w_s|` (GEOMETRIC growth) ⇒
`block_s/|w_s| ≈ κ`, a CONSTANT. `hdom` (`block_s < ε|w_s|` ∀ε) is impossible.
Unbalancing only compounds (the resolve cost feeds back). **`hdom` cannot hold.**
(This is the same "each block ≈ accumulated word" the 2026-08-24 super-exponential
analysis flagged; the intervening "filler-free ⇒ o(word)" optimism was the error.)

### Why uniform-goodness is then FORCED (not optional)
`chain_cf_digit_freq_tendsto` (CFChainFreq:327) needs the frequency at EVERY
prefix length `p`, incl. mid-block. It handles a mid-block `p` by decomposing
`prefix = w s ++ (chainApp w s).take (p−|w s|)` (line 391-397) and calling
**`cfDiscLt_append_take`**, whose control of the partial last block IS `hdom`
(block short vs word). With `block = Θ(word)` the partial block is `Θ(p)`, so the
frequency can OSCILLATE by a constant WITHIN each block — equidistribution FAILS at
those `p` — UNLESS the partial block is itself freq-good, i.e. the block is
**uniformly prefix-good**. A maximal/dyadic union bound over all prefix lengths `k`
does NOT close (`Σₖ O(1/(δ²k)) = O(log n)` diverges; dyadic chaining leaves an
`Θ(p)` interpolation gap). So uniform-goodness needs a genuine idea, not a union
bound.

### THE REAL CRUX (next attack)
Build a **uniformly-prefix-good steerable block**: `∃ u` with `cfCylinder(wx++u) ⊆
(c,d)` AND `∀ k ≤ |u|, u.take k` is `δ`-freq-good (bounded additive slack), then a
hdom-FREE `chain_cf_digit_freq_tendsto` variant that consumes it via
`chainTail_dev_split` (already built) for the boundary tail + the per-block uniform
bound for the partial. Candidate constructions to probe (smallest first):
  (a) **maximal inequality** on `cfBadZone` deviations (Doob/Kolmogorov over the
      orbit) — deep but standard; check if the γ-mixing already proved gives it.
  (b) **self-similar block**: build `u` as a concatenation of geometrically-growing
      freq-good sub-blocks with the RESOLVING sub-block LAST (so every proper prefix
      is a union of good sub-blocks + a partial that is `o(sub-accumulation)` —
      recovering the single-stream `hdom` WITHIN the block, where there is no
      per-sub-block resolution constraint). This localizes the resolution to the
      final sub-block and may dodge the maximal inequality entirely.
Probe (b) first — it reuses the single-stream engine and needs no new deep import.

### ✅ CRACK (this lap, refined): MULTI-SCALE bad-zone avoidance gives uniform-goodness with BOUNDED total measure — no maximal inequality needed
The union bound over ALL prefix lengths `k` diverges, but over a SPARSE
quadratically-spaced set of scales it CONVERGES, and quadratic spacing is `o(scale)`
so it interpolates. Concretely, require the good point `x` to avoid `cfBadZone wx v nⱼ δ`
for `v∈F` at scales `nⱼ = n₁ + j²`, `j = 0..m` (so `n_m = n₁+m² =` the block length `n`):
- **Measure (crude, no integral needed):** each aggregate bad zone at scale `nⱼ`
  has `γ ≤ (S/(δ²nⱼ))·γ(I_wx) ≤ (S/(δ²n₁))·γ(I_wx)` (since `nⱼ ≥ n₁`), where
  `S = Σ_{v∈F} 7(8|v|+80)γ(I_v)` (`gaussMeasure_aggregate_cfBadZone_le`). So the
  union over the `m+1` scales has `γ ≤ (m+1)·(S/(δ²n₁))·γ(I_wx)`. Pick `n₁` large
  enough that `(m+1)S/(δ²n₁) < ρ` (`ρ = γ(target)/γ(I_wx)`), i.e.
  `n₁ ≳ S·√n/(δ²ρ)` (`m ≈ √n`); then the good set ∩ target has positive measure.
  Feasible per round once `|w_s|` is large: need `n ≳ 1/δ_s⁴`, and `n ≈ κ|w_s|`
  (geometric) beats `1/δ_s⁴ = (s+1)⁴` (poly).
- **Uniform goodness:** any prefix length `p ∈ [nⱼ, nⱼ₊₁)` has
  `|dev(p)| ≤ |dev(nⱼ)| + (nⱼ₊₁−nⱼ) < δ·nⱼ + (2j+1) ≤ δ·p + 2√p` (since
  `2j+1 ≤ 2√(p−n₁)+1 ≤ 2√p`). So EVERY prefix is `(δ + 2/√p)`-good — additive
  interpolation term is `o(p)`. Exactly the `chainTail_dev_split` shape.
- **⇒ uniformly-prefix-good steer block**, hdom-FREE. The outer chain feeds these
  blocks to a hdom-free `chain_cf_digit_freq_tendsto` variant.

### NEXT (concrete, this is the build):
1. **`gaussMeasure_multiscale_cfBadZone_le`** (TBrick/CFScheduleA): for a Finset of
   scales `NS` with `∀ n∈NS, n₁ ≤ n`, `γ(⋃_{n∈NS}⋃_{v∈F} cfBadZone wx v n δ) ≤
   |NS|·(S/(δ²n₁))·γ(I_wx)`. Sum `gaussMeasure_aggregate_cfBadZone_le` over `NS`
   (each term `≤` the `n₁` term). ✅ DONE this lap (CFScheduleA, before
   `exists_irrational_notMem_cfBadZone_in_Ioo`, axiom-clean).
2. ✅ DONE this lap: `exists_irrational_notMem_multiscale_cfBadZone_in_Ioo`
   (CFScheduleA, after the single-scale core, axiom-clean). Takes the scale-set
   `NS` (all `≥ n₁`) and the caller-supplied measure hypothesis
   `|NS|·(Σ_v …/(δ²n₁))·γw < γ(c,d)`; returns an irrational point of `(c,d)`
   avoiding `⋃_{n∈NS}⋃_{v∈F} cfBadZone wx v n δ` simultaneously. Same combine
   core (A\B positive, strip rationals).
3. **PER-SCALE part DONE this lap:** `exists_multiscale_freq_good_block_steer_len`
   (CFScheduleA, after `exists_freq_good_block_steer_len`, axiom-clean). Block `u`
   of length `NS.max'` with `cfCylinder(wx++u) ⊆ (c,d)` AND
   `∀ n∈NS, ∀ v∈F, |countOcc v (u.take n) − γv·n| < δ·n + |v|` (freq-good at EVERY
   scale in `NS`). REMAINING (interpolation to all `k`): a pure arithmetic lemma
   `∀ k ≤ |u|, |countOcc v (u.take k) − γv·k| < δ·k + |v| + 2·(gap near k)` from the
   per-scale bound + `|countOcc(u.take k) − countOcc(u.take n)| ≤ k−n` for the
   largest `n∈NS` with `n ≤ k`. With `NS = {n₁+j² : j≤m}` the gap `k−n ≤ 2√k`.
   This slots directly into a hdom-free chain limit.
   ✅ **Interpolation arithmetic DONE this lap:** `abs_countOccurrences_take_interp`
   (CFScheduleA, after the multiscale block, axiom-clean): for `n ≤ k ≤ |u|`,
   `|countOcc v (u.take k) − γv·k| ≤ |countOcc v (u.take n) − γv·n| + 2(k−n) + |v|`
   (`countOcc` monotone in prefix + grows `≤1`/position + `|v|−1` seam). Combined
   with the per-scale block, every prefix `k` is `(δ + (2(k−n)+2|v|)/k)`-good where
   `n` = nearest lower scale; with `NS = {n₁+j²}` the gap `k−n ≤ 2√k` so it is
   `δ + o(1)`-good. The uniformly-prefix-good block is now ASSEMBLED (per-scale +
   interpolation); packaging it into a single `∀k` statement + the quadratic-`NS`
   covering (`∀k∈[n₁,ntop], ∃n∈NS, n≤k ∧ k−n≤2√k`) is the next small step.
4. hdom-free `chain_cf_digit_freq_tendsto` variant + the recursion.

### ✅✅✅ UNIFORMLY-PREFIX-GOOD BLOCK ASSEMBLED (this lap) — the crux crack is PROVED
`exists_uniformly_freq_good_block_steer` (CFScheduleA, axiom-clean): a steer block
`u` of length `n₁+m²` with `cfCylinder(wx++u) ⊆ (c,d)` AND **every** prefix good:
`∀ k∈[n₁,|u|], ∀ v∈F, |countOcc v (u.take k) − γv·k| < δ·k + (4√k + 2|v|)`.
The slack `4√k+2|v| = o(k)`, so this is the hdom-FREE block-goodness the affine
schedule needs. Supporting (all axiom-clean, CFScheduleA): `quadScales n₁ m` +
`quadScales_{nonempty,card_le,mem_ge,max,cover}`. Caller supplies the measure
budget `(m+1)·A₁(n₁) < γ(c',d')` and the top-scale resolution
`4/(d−c) < fib(|wx|+n₁+m²+1)²`.

### REMAINING (step 4 only): plug into the schedule
- ✅ **STARTED this lap:** `chainTail_dev_split_var` (CFChainFreq, after
  `chainTail_dev_split`, axiom-clean) — the varying-slack telescoping: per-block
  slack `C s` may grow (uniformly-good blocks have `C_s = 4√|u_s|+2|v|`), tail
  deviation `< ε·len + ∑_{i≤k}(C(s₀+i)+(|v|−1))`. The `∑ C_j` is `o(word)` when
  `|u_j|` grows geometrically, so the accumulated word stays good. This is the
  base-word-goodness half of the hdom-free limit.
- **hdom-free chain limit:** a variant of `chain_cf_digit_freq_tendsto` /
  `chain_orbit_equidist` whose per-block hypothesis is uniform-prefix-goodness
  (`∀k, |dev(u.take k)| < δ_s·k + o(k)`) INSTEAD of `hgood ∧ hdom`. With the block
  above, mid-block prefixes are handled by the block's OWN prefix bound (no
  `cfDiscLt_append_take`/hdom needed); across blocks, `δ_s → 0`. This replaces the
  `hdom` reliance at CFChainFreq:391-397.
- **ψ-round + recursion:** rebuild `exists_freq_good_extend_affine_steer` to emit
  uniformly-good blocks (call `exists_uniformly_freq_good_block_steer` for each
  stream, choosing `m_s, n₁,s` per the budget/resolution — `n₁,s ~ poly(1/δ_s)`,
  `m_s` s.t. `n₁+m²` hits the resolution length `~κ|w_s|`), then the two-stream
  `SchedStateA`/`schedStepA`/`schedA` recursion → two uniformly-good chains → the
  hdom-free limit → `CFOrbitEquidist` for both streams → the crux witness.

---

## ⭐⭐⭐⭐⭐ ROUTE-DECISIVE CORRECTION 2026-08-24 (this lap): `hdom` needs TIGHT (logarithmic) steer blocks — the current steer lemma's block length is EXPONENTIAL and BREAKS `hdom`

Before wiring `exists_interleaved_affine_witness` I quantified the ONE unverified
hypothesis the whole route rests on: `chain_orbit_equidist`'s `hdom`
(`|chainApp w s| < ε·|w s|` eventually, i.e. each appended block `= o(accumulated
word)`). The last handoff asserted "hdom follows from slow growth" and marked the
recursion as pure wiring. **That is wrong as currently built**, for a concrete,
compiler-checkable reason:

- `exists_freq_good_block_steer` (CFScheduleA:352) fixes its block length as
  `n = max(N0, N1, L, 1)+1` where **`N1 := (exists_fib_threshold (1/β)).choose`**
  and `β = (target width)/4`. `exists_fib_threshold` (TBrickRefine:164) is the
  CRUDE threshold: its `N ≈ a` (LINEAR in `a`), because it only uses
  `n+1 ≤ fib(n+1)`. So the steer block has length `n ≳ N1 ≈ 1/β`.
- In the interleaved schedule the x-target is the overlap of `wx`'s convergent
  interval (width `≈ φ^{-2|wx|}`) with `ψ⁻¹(wz'-interval)` (width `≈ φ^{-2|wz'|}`),
  so `β ≈ φ^{-2|w_s|}` and `1/β ≈ φ^{2|w_s|}`. Hence the steer block is
  `n_s ≈ φ^{2|w_s|}` — **exponentially longer than the accumulated word**, the
  exact negation of `hdom` (`n_s = o(|w_s|)`). Even the information-theoretic
  minimum (resolve a cylinder of the OTHER stream's scale) is `n_s ≈ |w_s|`, still
  only a constant factor — with the crude `N1` it is doubly hopeless.

### The fix (STARTED this lap, axiom-clean): tight logarithmic block length
The minimal `n` with `fib(n+1)² > 1/β` is `≈ (1/2)log_φ(1/β) ≈ |w_s|·(refinement
ratio)`, NOT `1/β`. The per-round refinement ratio is what matters, not the
absolute cylinder scale: placing a block inside a target that is a bounded factor
`ρ` smaller than the current cylinder costs only `≈ log_φ(1/ρ)` digits. So with
the schedule `L_s = s`, `δ_s = 1/(s+1)`: each stream's block length
`n_s ≈ L_s ≈ s`, the accumulated word `|w_s| = Σ_{j<s} n_j ≈ s²/2`, and
`n_s/|w_s| ≈ 2/s → 0` — **`hdom` HOLDS** (with the tight bound, not the crude one).

Landed (TBrickRefine, axiom-clean `[propext, Classical.choice, Quot.sound]`):
- **`goldenRatio_pow_le_sqrt5_mul_fib_add_one`**: `φⁿ ≤ √5·fib(n) + 1` (tight
  Binet lower bound, from `ψⁿ ≤ 1`). The exponential lower bound on `fib`.
- **`fib_sq_gt_of_goldenRatio`**: `a < fib(n+1)²` as soon as `√5·√a + 1 < φ^(n+1)`
  — the LOGARITHMIC (consumable) threshold: minimal `n ≈ log_φ√a`, replacing the
  crude `exists_fib_threshold`.
- **`exists_nat_goldenRatio_pow_gt`**: `∃ n, y < φⁿ ∧ (n:ℝ) ≤ log_φ(max y 1)+1`
  — the EXPLICIT logarithmic exponent. Feeding `y = √5·√(1/β)+1` into this then
  `fib_sq_gt_of_goldenRatio` gives a resolve-block of length `≤ log_φ(1/β)+O(1)`
  with an explicit numeric handle (what the `hdom` bookkeeping in the recursion
  consumes). The three lemmas together are the full logarithmic-block toolkit.

### NEXT (concrete, ordered)
1. ✅ **DONE (this lap): `exists_freq_good_block_steer_len`** (CFScheduleA, after
   `exists_freq_good_block_steer`, axiom-clean). The tight-length steer lemma:
   exposes the measure-core threshold `N0` and takes the block length `n` as an
   EXPLICIT caller parameter, returning `∃ u, u.length = n ∧ …` given only the
   resolution hypothesis `4/(d-c) < fib(|wx|+n+1)²` (which the caller discharges at
   logarithmic `n` via `fib_sq_gt_of_goldenRatio`+`exists_nat_goldenRatio_pow_gt`).
   Length is now fully caller-controlled — the `hdom` handle. Everything else
   (measure core, freq-goodness, `cfCylinder ⊆ (c,d)`) copied verbatim from
   `exists_freq_good_block_steer`.
2. **Propagate the length bound through `exists_freq_good_extend_affine_steer`**
   (→ `_len` variant) so the ψ-round outputs, for both `ux`,`uz`, an explicit
   `|block| ≤ (input word length gap) + O(log …)`. Needs, per stream:
   (i) a LOWER bound on the convergent-interval width `b−a ≥ c/fib(|w|+O(1))²` (so
   the target width `≥ c'/fib²`, giving `4/width ≤ C·fib(|w|)²`); (ii) the tight
   Binet bounds — LANDED both:
   `goldenRatio_pow_le_sqrt5_mul_fib_add_one` (φⁿ ≤ √5·fibₙ+1) and its dual
   `sqrt5_mul_fib_le_goldenRatio_pow_add_one` (√5·fibₙ ≤ φⁿ+1), pinning
   `√5·fibₙ ∈ [φⁿ−1, φⁿ+1]`; combine with `exists_nat_goldenRatio_pow_gt` to solve
   `4/width < fib(|w|+n+1)²` at `n = |wtarget|−|w| + O(1)`. Then call
   `exists_freq_good_block_steer_len` at that `n`. The interval-width LOWER bound
   (i) is the one still-missing analytic atom — check `cfCylinder_endpoints` /
   `cfCylinder_subset_Icc_length` for an existing two-sided width bound before
   proving it.
3. THEN the recursion (`SchedStateA`/`schedStepA`/`schedA`, `L_s = s`) can prove
   `hdom` from the length bounds + `|w_s| ≥ Σ L_j`, and feed
   `chain_orbit_equidist`. Items 2–5 of `HANDOFF-2026-08-24-1641.md` (limit point,
   ψ-chain gluing) are unaffected — only the block-length control was missing.

**Provenance:** the "infra not needed / pure wiring" claim in the 2026-08-27
handoff is SUPERSEDED by this correction. The uniform-goodness / `addslack` infra
is a SECOND independent escape (drop `hdom` entirely by requiring every block
PREFIX freq-good) — kept in reserve; the tight-block route above is simpler
(reuses `chain_orbit_equidist` as-is) and is the primary plan.

---

## ⭐⭐⭐⭐⭐ ROUTE-DECISIVE RESOLUTION 2026-08-27: the `hdom` obstruction is REMOVABLE

**The filler/balance obstruction (recorded 2026-08-24) is pinned to a SINGLE
hypothesis of the abstract telescoping — `chain_orbit_equidist`'s `hdom` — and
`hdom` is STRONGER THAN NECESSARY.** This lap proved the enabling lemma that lets
us drop it; the schedule can then close.

### The precise diagnosis
`chain_cf_digit_freq_tendsto` (CFChainFreq) needs, per stream, TWO facts on each
appended block `chainApp w s`:
- `hgood` — the block is freq-good (used for the tail-chain tier + `hbound`);
- `hdom` — `|chainApp w s| ≪ |w s|` (block a VANISHING fraction of the accumulated
  word). **Used ONLY for mid-block prefixes** (line ~262-274, via
  `cfDiscLt_append_take`): a prefix ending inside a block must not see enough
  uncontrolled digits to move the frequency.

The interleaved schedule CANNOT satisfy `hgood ∧ hdom` simultaneously: maintaining
the interval invariant in lockstep forces `filler_s ≈ (other stream's payload
this round)`, and burying the filler under the freq-good tail (`hgood`) forces
tails to grow super-exponentially (`tail_x,k ≫ tail_z,k ≫ tail_x,k-1 ≫ …`), which
makes each block `≈` the accumulated word — the exact NEGATION of `hdom`.

### The escape (proved viable this lap)
**Never require the whole appended block to be freq-good.** Split each block as
`chainApp = filler ++ payload` and require only:
  - **(a)** `filler_s = o(|w s|)` — the SHORT-vs-accumulated-word part of `hdom`,
    but on the FILLER ONLY (not the payload);
  - **(b)** `payload_s` **uniformly good** — every prefix `(payload_s).take k` is
    freq-good with a bounded additive slack.
Then every prefix stays good by two sub-steps, NEITHER needing the payload short:
  1. prefix ends in filler → `cfDiscLt_append_take` (filler short vs `|w s|`) ✓;
  2. prefix ends in payload → `(w s ++ filler)` good, then append `payload.take k`
     via the NEW **`countOccurrences_append_addslack`** (good ++ uniformly-good
     stays good, **additive slack, NO shortness**) ✓.
Both (a),(b) ARE satisfiable: with SLOW lockstep growth (e.g. linear payloads) no
single payload dominates the accumulated sum, so `filler_s ≈ other-payload_s =
o(word)` — (a); and payloads built from the single-stream engine keep every prefix
good — (b). The super-exponential-growth contradiction was an artifact of the
spurious `hgood`-on-the-whole-block requirement, now dropped.

### Landed (axiom-clean `[propext, Classical.choice, Quot.sound]`)
- `countOccurrences_append_addslack` / `…₂` (CFChainFreq): good-with-slack `++`
  good-with-slack stays good, additive slack, **NO shortness**. The hdom-free
  append. `cfDiscLt_short_append`/`_append_take` (frozen CFConcat) cover only the
  SHORT-block case.
- `chainTail_dev_split` (CFChainFreq, commit `c0c9db1`): iterating `…addslack₂`
  over `filler++payload` blocks gives tail deviation `< ε·len + (#blocks)·(C+(|v|−1))`
  — the hdom-free replacement for `chainTail_cfDiscLt`, no per-round tolerance
  compounding (additive term ÷ len is bounded, → small with long payloads).

### ⚠️ DEFINITIVE ROUTE FINDING (2026-08-27, cont.): a per-round UNCONTROLLED filler CANNOT be telescoped away — item 2 (freq-good navigation) is UNAVOIDABLE
Pushed the telescoping analysis to the end. Two — and only two — ways to fold a
per-round filler into the frequency limit, BOTH fail when `filler_s ~ payload_s`
(which the geometry forces — see below):
- **`cfDiscLt_short_append` (ε→2ε per filler).** The existing proof keeps the tail
  at a FIXED tolerance across arbitrarily many blocks ONLY because every block is
  margin-good (`CFDiscLt.append` preserves ε exactly). A filler needs
  `short_append`, which DOUBLES the tolerance. One filler per round ⇒ `2^s·ε` —
  compounds without bound. Fillers therefore cannot live in the tolerance-preserving
  tail-chain.
- **`countOccurrences_append_addslack₂` (no compounding, but +C accumulates).** The
  hdom-free path this lap built: no tolerance doubling, but each filler leaves a
  residual additive `C_s ~ |filler_s|`. `chainTail_dev_split` ⇒ total additive
  `Σ_j C_j`. When `filler_s ~ payload_s`, `Σ C_j ~ Σ payload_j ~ |w s|`, so
  `additive/len ~ Θ(1)` — the tail is NOT asymptotically good.

**Why `filler_s ~ payload_s` is forced (not a schedule artifact):** the ψ-stage
must land `ψ(cfCylinder wx')` in the freshly-refined z-cylinder `wz'`. `wz'` shrank
by `~φ^{-2·payload_{z,s}}`, so x's re-navigation into `ψ⁻¹(wz')` costs
`~payload_{z,s}` digits — the OTHER stream's per-round payload. Symmetric for z.
Driving `δ_s→0` (required for equidistribution) forces BOTH payloads `→∞`, hence
BOTH fillers `~` the other payload `→∞`. No schedule makes `filler_s = o(payload_s)`
on both streams simultaneously (would need `n_{other,s}=o(n_s)` AND `n_s=o(n_{other,s})`).

**Conclusion:** the interleaved schedule closes IFF the navigation digits are
themselves frequency-good — then `chainApp = u` is a single margin-good block,
`filler` vanishes, the EXISTING `chain_orbit_equidist` applies (blocks are `o(word)`
under slow growth ⇒ `hdom` holds). **The route-decisive crux is `exists_freq_good_block`
STEERED into `ψ⁻¹(target)`.**

### ✅✅ CRACK (2026-08-27, cont.): the steerable good block is TRACTABLE (NOT a deep wall)
Earlier pessimism ("steering base uncontrolled ⇒ deep Vandehey wall") was WRONG — it
conflated the split engine `exists_freq_good_block_in_Ioo` (placement base + good
tail) with what the bad-zone machinery actually gives. `cfBadZone wx v n δ`
(`TBrick.lean:191`) controls `blockCount v` over the ENTIRE next `n` steps FROM base
`wx` — so take base = `wx` directly (NO navigation prefix) and intersect the good set
with the target interval:
- `Gₙ := cfCylinder wx \ ⋃_{v∈F} cfBadZone wx v n δ`.
- `gaussMeasure (⋃ cfBadZone wx v n δ) ≤ (Σ_v 7(8|v|+80)γ(I_v)/(δ²n))·γ(I_wx)` —
  **already proved: `gaussMeasure_aggregate_cfBadZone_le` (TBrick.lean:201)**, `= O(1/n)·γ(I_wx)`.
- target `(c,d) ⊆ cfCylinder wx` has `γ(c,d) = ρ·γ(I_wx)`, INDEPENDENT of `n`.
- ⇒ `γ(Gₙ ∩ (c,d)) ≥ ρ·γ(I_wx) − O(1/n)·γ(I_wx) > 0` for `n > O(1/ρ)`.
Extract irrational `x ∈ Gₙ ∩ (c,d)`: `x ∈ (c,d)` AND its `n`-block `u` from `wx` is
δ-freq-good (via `abs_blockCount_lt_of_notMem_cfBadZone` + blockCount↔countOccurrences
bridge, EXACTLY as `exists_freq_good_block` CFFreqBlock:86–100). **The freq-good digits
themselves steer into `(c,d)` — no separate filler.** `cfCylinder (wx++u) ⊆ (c,d)`
by choosing the point in `(c',d') ⊂⊂ (c,d)` with `n` large (cylinder width → 0), as
`exists_cfCylinder_subset_Ioo` does.
The addslack/split-tail lemmas become UNNEEDED for the main route (kept as infra).

### NEXT — measure core DONE; wrap it into the steerable freq-good WORD.
✅ **`exists_irrational_notMem_cfBadZone_in_Ioo`** (CFScheduleA, commit `010c30e`,
axiom-clean) — the measure core: for `n ≥ N`, an irrational `x ∈ (c,d)` avoiding
ALL of `wx`'s `n`-step CF bad zones for `F`. Hypotheses: `Ioo c d ⊆ cfCylinder wx`,
`0 < γ(Ioo c d)`. This is the crack — freq-good digits steer into the target.

✅ **`exists_freq_good_block_steer`** (CFScheduleA, commit `80faa12`, axiom-clean) —
DONE. The steerable filler-free freq-good block: given `(c,d)` with all its
irrationals in `cfCylinder wx`, yields genuine `u` (`|u|≥L`, δ-good ∀v∈F) with
`cfCylinder (wx++u) ⊆ (c,d)` + irrational witness. NO placement prefix. **The crux
ingredient is now in hand.** Remaining = pure schedule wiring (items 2–3 below).

<details><summary>(superseded) build recipe for exists_freq_good_block_steer</summary>
1. wrap the core into a WORD.
   From `x` (the core's output at suitable `n ≥ max(N, L, …)`): set
   `u := (range n).map (fun i => cfDigit x (wx.length+i))`, so `x ∈ cfCylinder (wx++u)`
   (via `range_map_cfDigit_eq`, as `exists_freq_good_block` CFFreqBlock:90-91).
   - freq-good of `u`: `abs_blockCount_lt_of_notMem_cfBadZone` (TBrickRefine:78) +
     `blockCount_sub_countOccurrences_bounds` bridge ⇒ `|count v u − γv·n| < δn + |v|`
     for all `v∈F` (COPY CFFreqBlock:84-105 verbatim — same shape).
   - `cfCylinder (wx++u) ⊆ Ioo c d`: choose the core's target as `(c',d') ⊂⊂ (c,d)`
     with a buffer, and `n` large enough that cylinder width `≤ 1/fib(...)² <` buffer
     ⇒ the whole cylinder ⊆ (c,d). (Or: derive from `x ∈ (c',d')` + `cfCylinder_subset`
     diameter bound; see `exists_cfCylinder_subset_Ioo` for the fib-threshold idiom.)
   - genuineness/extension: `|u|=n > wx.length`, `wx++u` extends `wx` trivially.
   Output signature ~ `exists_freq_good_block_in_Ioo` but `u` is the WHOLE steered
   block (no placement prefix) and lands in `(c,d)`.
</details>

✅ 2. **`exists_freq_good_extend_affine_steer`** (CFScheduleA, commit `2adf047`,
   axiom-clean) — DONE. The filler-free ψ-round: `wz' = wz ++ uz`, `wx' = wx ++ ux`
   with `uz, ux` single steerable freq-good blocks, each exposed as `w'.drop w.length`
   (the WHOLE freq-good word, no `wp`), maintaining the interval invariant. This is
   the drop-in whose `chainApp = w'.drop w.length` is a single margin-good block.

3. **Wire `exists_interleaved_affine_witness`** (THE remaining sole `src/` `sorry`,
   CFScheduleA:~975): `SchedStateA`/`schedStepA` mirroring
   `CFSchedule.sched`, feeding both chains (blocks = whole freq-good `u`, `o(word)`
   under slow growth ⇒ `hdom` holds) into the EXISTING `chain_orbit_equidist`.
   The interval invariant glues the ψ-chain limit to `ψ(xA)` (limit toolkit ready:
   `eq_of_mem_iInter_Icc`, `cfCylinder_chain_volume_tendsto`).
- **Infra kept (now off the main route):** `countOccurrences_append_addslack`/`₂`,
  `chainTail_dev_split` — the hdom-free telescoping, reusable if a future variant
  needs a residual bounded filler; not needed for the filler-free route above.

---

## ⭐⭐⭐⭐ CRUX ADVANCE 2026-08-24 (cont.): ψ-ROUND STEP `exists_freq_good_extend_affine` PROVED ✅

`CFScheduleA`, **axiom-clean** `[propext, Classical.choice, Quot.sound]`, green 8757.
B5′ headlines re-verified trust-triple. **The novel geometric heart of B6 —
maintaining the interval invariant `cfCylinder wx ⊆ ψ⁻¹(Ioo e f)` through one
joint refinement round — is done.** Given genuine `wx, wz`, the wz-interval `(e,f)`
(`irr(e,f)⊆cfCylinder wz`), the invariant, `F`, `δ`, `L`, it produces:
- `wz'` extends wz, freq-good, `L≤|wz'|`, `cfCylinder wz'⊆cfCylinder wz`, with the
  freq-good block exposed `∃ wp u, wz'=wp++u ∧ L≤|u| ∧ (∀v∈F, δ-good u)`;
- `wx'` extends wx, freq-good, `L≤|wx'|`, `cfCylinder wx'⊆cfCylinder wx`, same
  exposed block;
- new wz-interval `(e',f')` (`0≤e'<f'≤1`, `irr(e',f')⊆cfCylinder wz'`);
- **new invariant** `cfCylinder wx' ⊆ ψ⁻¹(Ioo e' f')`.
Proof followed the recipe exactly: image bounds (`affine_image_Ioo_subset_Icc_pre`
+ `closure_Ioo`/`Icc_subset_Icc_iff`) ⇒ place good z-block in `ψ((a,b))` ⇒ shared
point `x₀=(pz−r)/q` gives strict overlap `max a a' < min b b'` of `(a,b)` with the
pullback `ψ⁻¹(Ioo e' f')` ⇒ place good x-block in the overlap; both extensions via
`take_eq_of_mem_cfCylinder` with block length `n > |word|`.

### ⚠️ ROUTE-DECISIVE FINDING (this lap): the FILLER/BALANCE obstruction is REAL
Analyzing the telescoping wiring quantitatively surfaced a genuine difficulty the
"just assembly" framing hid. `chain_orbit_equidist` needs, per stream: `hgood`
(chainApp margin-good) AND `hdom` (`|chainApp_s| < ε|w_s|`, block a VANISHING
fraction of the accumulated word — CFCorrect's `uSched_dominance` direction:
block SMALL vs word). The interleaved schedule's navigation FILLERS threaten both:

- **Filler size = the OTHER stream's payload.** To make `ψ(cfCylinder wx')` land
  in the new good z-cylinder `wz'` (width `~φ^{-2|wz'|}`), `x` must be refined to
  depth `|wx'| ≳ |wz'|`; the FORCED navigation digits number `~|wz'|−|wx| ≈` z's
  growth this round `≈ z-payload`. Symmetrically z's placement into `J_z=ψ(wx-int)`
  costs `~x-payload` when x leads. So **filler_s ≈ (other stream's payload)**,
  NOT `o(payload)`.
- **The tension.** To BURY a stream's filler we need its own payload
  `≫ filler ≈ other-payload`; but then that stream outgrows the other, and next
  round the LAGGING stream's filler `≈` this stream's (now huge) payload. The
  imbalance + fillers compound: with alternating navigation the fillers are an
  IRREDUCIBLE Θ(payload) fraction, so the appended block is a constant-fraction
  of uncontrolled (non-freq-good) digits ⇒ frequency need not converge.
- **Why `hdom` alone doesn't save it.** Even sub-linear block growth
  (`|app_s|=o(|w_s|)`, e.g. `√|w_s|`) keeps `hdom`, but the filler is a constant
  fraction of each `app_s`, so a prefix ending mid-filler (length `~|w_s|+filler`)
  has count deviating by `~filler ≈ payload ≈ |app_s|` — a Θ(1)·|app_s| error;
  since `hdom` only says `|app_s|<ε|w_s|`, at that prefix the deviation/prefixlen
  can still be Θ(ε), not →0. Actually CFCorrect's `cfDiscLt_short_append` REQUIRES
  the foreign (filler) segment to be short vs the GOOD block (`|u|+(k−1)<ε|x|`),
  i.e. filler `o(good mass)` — which the Θ(payload) filler VIOLATES.

**So this is a genuine route-decisive obstruction, not assembly bookkeeping.**
The abstract telescoping (`chain_orbit_equidist`) and the round step
(`exists_freq_good_extend_affine`) are both CORRECT and reusable, but wiring them
needs the navigation fillers to be `o(freq-good mass)`, which the naive
alternating navigation does not provide.

**Candidate escapes (next lap must pick/test ONE, hardest-first):**
1. **Make the fillers freq-good too.** The navigation digits into `ψ⁻¹(wz')` have
   FREEDOM (any x-cylinder inside the target preimage interval works); choose that
   whole extension freq-good via `exists_freq_good_block_in_Ioo` on the preimage
   interval — then there is NO uncontrolled filler, only a bounded PLACEMENT word
   `wp` whose length is the RELATIVE depth `~log_φ(width(cfCylinder word)/width(target))`
   `≈ payload`. ⚠ but `wp` is still Θ(payload) and uncontrolled → same problem
   unless `wp` is ALSO absorbed. Needs: expose `|wp_s|` from the round step and
   bound it, then require `|wp_s| = o(|u_s|)` (payload `≫` placement) — but that
   reintroduces the burial-vs-balance tension. LIKELY still stuck.
2. **Relative-placement primitive.** Prove that extending `word` into a
   sub-interval of `cfCylinder word` of RELATIVE width `ρ` costs only
   `~log_φ(1/ρ)` new digits AND those can be chosen freq-good — i.e. a
   `exists_freq_good_extend_into_subcylinder`. Then the x-reselection into
   `ψ⁻¹(wz')` (relative width `~q·φ^{-2·zpayload}`, so `~zpayload` new digits) is
   itself freq-good, killing the filler entirely. This is the most promising —
   the navigation digits become part of the freq-good block. Requires a genuinely
   new placement lemma with freq control on the navigation portion.
3. **Different frequency criterion** tolerating Θ(1)-fraction STRUCTURED fillers
   (prove the forced navigation digits are themselves equidistributed / the
   targets are "generic"). Deep; likely needs a natural-extension/measure argument
   (closer to Vandehey's actual method). Escalate if 1–2 fail.

**DECISION for next lap:** attack escape #2 (relative freq-good placement) — it is
the route-decisive probe: if a word can be freq-good-extended into a preimage
sub-interval with new-digit-count `≈` the relative depth (all freq-good, no
uncontrolled filler), the interleaved schedule closes; if not, escalate toward #3
(write `ROUTE-ESCALATION`). Do NOT build `SchedStateA` until #2 is settled — the
recursion is worthless if the per-round extension carries Θ(payload) uncontrolled
filler.

---

## ⭐⭐⭐ CRUX ADVANCE 2026-08-24 (cont.): interval-invariant image lemma + round-step design

`affine_image_Ioo_subset_Icc_pre` PROVED (`CFScheduleA`, axiom-clean, green 8757):
the ESTABLISHABLE-invariant variant of `affine_image_Ioo_subset_Icc`. Hypothesis
is the interval-preimage invariant `cfCylinder wx ⊆ ψ⁻¹(Icc e f)` (the one the
schedule can maintain — lap 19), conclusion `ψ((a,b)) ⊆ Icc e f`. Same two
`exists_irrational_btwn` contradiction blocks, landing the image directly in
`Icc e f` (no wz-cylinder hop). This unblocks the ψ-round's image step.

### The round step `exists_freq_good_extend_affine` (NEXT — the crux body)
Proposed signature (interval invariant, Ioo form):
```
(wx wz genuine) (0≤e<f≤1) (hzint: ∀x∈Ioo e f, Irr x→x∈cfCylinder wz)
(hinv: cfCylinder wx ⊆ ψ⁻¹(Ioo e f)) (F δ>0 L) →
∃ wx' wz' e' f', <wz' extends wz, freq-good> ∧ <wx' extends wx, freq-good, L≤|wx'|>
  ∧ 0≤e'<f'≤1 ∧ (∀x∈Ioo e' f',Irr x→x∈cfCylinder wz') ∧ cfCylinder wz'⊆Icc e' f'
  ∧ cfCylinder wx' ⊆ ψ⁻¹(Ioo e' f')
```
Recipe (atoms all ready):
1. wx-interval `(a,b)` [`exists_Ioo_irrational_subset_cfCylinder wx`].
2. `hinv`→Icc; `affine_image_Ioo_subset_Icc_pre` ⇒ `ψ((a,b))=Ioo(qa+r)(qb+r)⊆Icc e f`;
   extract `e ≤ qa+r`, `qb+r ≤ f` via `closure_Ioo`+`Icc_subset_Icc_iff`.
3. `J_z:=Ioo(qa+r)(qb+r)` (0≤qa+r<qb+r≤1). `exists_freq_good_block_in_Ioo F .. J_z`
   ⇒ wz'=wpz++uz freq-good, cfCylinder wz'⊆J_z, irr pt pz. pz∈J_z⇒(e<pz<f)⇒
   pz∈cfCylinder wz (hzint) ⇒ (take_eq) wz' extends wz.
4. wz'-interval `(e',f')` [`exists_Ioo_irrational_subset_cfCylinder wz'`];
   cfCylinder wz'⊆Icc e' f', irr(e',f')⊆cfCylinder wz'.
5. wx': `exists_cfCylinder_subset_affine_preimage` on `(e',f')` INTERSECTED with
   `(a,b)` [`_Ioo_inter`] ⇒ wx_mid ⊆ ψ⁻¹(Ioo e' f')∩(a,b), extends wx (via irr pt
   in cfCylinder wx). Then `exists_freq_good_extend_cfCylinder wx_mid F δ L` ⇒ wx'
   freq-good, ⊆cfCylinder wx_mid ⊆ ψ⁻¹(Ioo e' f'). New invariant ✓.
   ⚠ nonemptiness of the intersection `(a,b)∩((e'-r)/q,(f'-r)/q)`: cfCylinder wz'
   ⊆ Ioo(qa+r)(qb+r)=ψ((a,b)), so its interval (e',f') overlaps ψ((a,b));
   pull back ⇒ overlaps (a,b). Establish `max lo < min hi` from a shared point
   (e.g. pz, or an irrational of cfCylinder wz' pulled back).

### ⚠️ ALIGNMENT / margin-good insight (for the recursion-assembly lap)
The engines give `word' = wp ++ u` with `u` freq-good at the END and
`word'.take|word| = word`. The chain contract wants `chainApp = word'.drop|word|`
MARGIN-good. Two cases by `|wp|` vs `|word|`: if `|wp|≥|word|`, chainApp =
`wp.drop|word| ++ u` (short filler ++ good); if `|wp|<|word|`, chainApp =
`u.drop(|word|−|wp|)` (a suffix of u, a bounded-length edit of a good block).
EITHER WAY chainApp is a margin-good block perturbed on ≤|word| entries, hence
margin-good once `|u|=L` dominates `|word|` and `|v|`. So the recursion must pick
`L_s` per round ≥ (growing) `|word_s|`·(2/ε)+… — the sizing discipline. The
`hgood`/`hdom` proofs at assembly use `cfDiscLt_short_append`/`_append_take`
(both already in `CFConcat`) to absorb the ≤|word| edit. NOT an abstraction gap;
a per-round length choice + a short-edit lemma.

---

## ⭐⭐ CRUX ADVANCE 2026-08-24 (review lap, same session): `chain_orbit_equidist` PROVED ✅

**The route-decisive question is ANSWERED: CFCorrect's telescoping DOES abstract
cleanly.** New additive module `src/NormalNumbers/CFChainFreq.lean` (imports
`CFConcat`, `CFOrbitFreq`, `TBrickRefine`; frozen modules untouched), green 8757,
**axiom-clean** `[propext, Classical.choice, Quot.sound]`. B5′ headlines
re-verified trust-triple.

Proved (all axiom-clean):
- `chainApp`/`chainTail` + algebra (`chainApp_eq`, `w_eq_append_tail`,
  `chainTail_succ`, `w_length_ge`, `le_chainTail_length`, `chain_exists_stage`)
  — the generic ports of `CFCorrect`'s `tailSched`/`exists_stage` block.
- `chainTail_cfDiscLt` — abstract B–Y Lemma 7 induction (tail is ε-good from
  margin-good blocks).
- `chain_cf_digit_freq_tendsto` — **THE CRUX PORT**: for a nested genuine chain
  `w` with limit `y∈⋂cfCylinder(w s)`, IF appended blocks are eventually
  margin-good (`hgood`) AND eventually short vs the accumulated word (`hdom`),
  THEN `countOccurrences v (y's digit prefix)/p → γv`. Faithful port of
  `xstar_cf_freq_tendsto` with the `sched`-specific level machinery replaced by
  the two abstract hypotheses.
- `chain_orbit_equidist` — wraps the above + the orbit↔window bridge
  (`blockCount_sub_countOccurrences_bounds`) → `blockCount(cfCylinder v) p y/p →
  γv` ∀ genuine v, i.e. the `CFOrbitEquidist` payload, for an irrational chain
  limit `y∈(0,1)`.

**What this buys.** The two abstract hypotheses are EXACTLY the contract the
interleaved schedule must fulfil, for EACH stream:
```
hgood : ∀ε>0, ∃s₀, ∀s≥s₀, |count v (chainApp w s) − γv·|app s|| < ε·|app s| − (|v|−1)
hdom  : ∀ε>0, ∃s₀, ∀s≥s₀, |chainApp w s| + (|v|−1) < ε·|w s|
```
(per genuine v; `chainApp w s = (w(s+1)).drop|w s|` = the block appended at stage s.)
The FILLER + ALTERNATION frictions are now PRECISELY localized: `chainApp w s`
is the whole appended block INCLUDING the per-stage filler, so the recursion must
make each stage's block (filler ++ freq-good `u`) margin-good and dominant. Since
`u`'s length `L_s` is chosen freely AFTER the filler is placed, pick `L_s` huge so
`u` dominates the filler AND the accumulated word — then `hgood`/`hdom` hold. No
abstraction gap remains; it's a per-stage sizing discipline in `schedStepA`.

**REMAINING (mechanical modulo sizing):**
1. **`exists_freq_good_extend_affine` (ψ-stage)** — emit wz freq-good extension
   + interval invariant (recipe: lap-21 item 1 below), choosing `L_s` to satisfy
   the `hgood`/`hdom` contract.
2. **`SchedStateA`/`schedStepA`/`schedA`/limit** — joint recursion by choice;
   at build time record, for each stream, the per-stage `hgood`/`hdom` witnesses
   (choose `L_s ≥` a growing target so `|u_s|`/`|w s|→∞` and filler/`|u_s|→0`).
   Then feed each stream's chain into `chain_orbit_equidist`.
3. **Glue**: `xA` = wx-limit; `CFOrbitEquidist xA` from stream-x
   `chain_orbit_equidist`; `ψ(xA)=ζ` (wz-limit) via `eq_of_mem_iInter_Icc` +
   `cfCylinder_chain_volume_tendsto`; `CFOrbitEquidist (ψ xA)=CFOrbitEquidist ζ`
   from stream-z `chain_orbit_equidist`. Obligation (A) both via
   `irrational_mem_Ioo_of_mem_iInter_cfCylinder`.

The hardest, most uncertain piece is now BANKED. Next lap: the ψ-stage sizing
(item 1) — the smallest probe that the `hgood`/`hdom` contract is fulfillable.

---

## ⭐ REVIEW LAP 2026-08-24 — PIVOT TO THE CRUX (read this first)

**Finding:** laps 11–21 proved 15 geometric/analytic ATOMS (all axiom-clean,
each a green commit) but the crux `sorry` `exists_interleaved_affine_witness`
stayed untouched and the recursion/telescoping was deferred "next lap" ~7×. The
atom toolkit is now DECLARED COMPLETE (list under "TOOLKIT NOW COMPLETE" below).
**No more atoms.** The remaining work is the frequency telescoping + recursion,
and the telescoping is the ONLY piece whose feasibility is in real doubt.

**Attack order (hardest-first):**

1. **`chain_orbit_equidist` — THE CRUX.** Abstract generic-chain frequency
   telescoping. Statement shape (draft against the real `CFCorrect` exports):
   given `w : ℕ → List ℕ`, each `w s` genuine (`≠[]`, digits `≥1`), a strict
   extension chain `w(s+1) = w s ++ app_s` with each appended block `app_s`
   carrying a freq-good sub-block `u_s` (a `CFDiscLt v u_s γv ε`-style guarantee
   for every pattern `v`, eventually in `s`) AND a DOMINANCE bound
   `|w s| ≤ C·|u_s|` (prefix + fillers negligible vs the freq-good tail), the
   unique limit point `y ∈ ⋂ cfCylinder (w s)` satisfies `CFOrbitEquidist y`.
   PORT `CFCorrect`'s `tailSched_cfDiscLt` (chain the `CFDiscLt` payloads via
   `CFDiscLt.append` + `cfDiscLt_short_append` to absorb fillers) →
   `xstar_cf_freq_tendsto`'s ε-split → the `blockCount .../p → gaussMeasure`
   limit, but with the `sched`-specific `uSched_spec`/`uSched_dominance`
   replaced by the abstract hypotheses. Copy-extend `CFCorrect` into
   `CFScheduleA` (or a new `CFChainFreq.lean`); NEVER edit `CFCorrect`.
   **The route-decisive test lives here** — see below.

2. **`exists_freq_good_extend_affine` (ψ-stage).** Recipe = lap-21 item 1
   (below). Compose the ready atoms; the NEW obligation vs the x-stage is to
   pick the block depth `L_s` large enough that `|u_s|` dominates the ACCUMULATED
   length (prefix + this stage's filler), so hypothesis (dominance) of (1) holds.

3. **`SchedStateA`/`schedStepA`/`schedA`/limit.** Joint recursion by choice
   (mirror `CFSchedule.sched`): a state carrying `wx`, `wz`, the interval
   invariant `cfCylinder wx ⊆ ψ⁻¹(Icc (lo wz) (hi wz))`, and the per-stream
   freq-good/dominance data; `schedStepA` alternates x/ψ by parity of the stage
   index; `xA :=` the limit of the wx-chain. Then: obligation (A) both sides via
   `irrational_mem_Ioo_of_mem_iInter_cfCylinder`; `ψ(xA)=ζ` (the wz-chain's
   irrational limit) via `eq_of_mem_iInter_Icc` + `cfCylinder_chain_volume_tendsto`;
   `CFOrbitEquidist xA` and `CFOrbitEquidist (ψ xA)=CFOrbitEquidist ζ` BOTH from
   (1) applied to the wx- and wz-chains respectively. ← this is the elegant part:
   we telescope the wz-chain's OWN limit ζ, then glue ζ=ψ(xA); no need to
   telescope ψ(xA)'s orbit directly.

**ROUTE-DECISIVE UNCERTAIN CASE (probe in step 1, before building 2–3):** B5′'s
telescoping (`CFCorrect`) appended a PURE freq-good block each stage with
built-in dominance (`uSched_dominance`). The interleaved schedule has TWO new
frictions: **(i) a per-stage filler** (from `exists_cfCylinder_subset_Ioo`,
placing the stream back into a shrinking target interval) whose length GROWS
like `log(1/|interval|)` as cylinders shrink — B5′ had none; **(ii) x/ψ
alternation**, so each stream's prefix also absorbs the OTHER stream's fillers.
Both are harmless IFF each stage picks `L_s` big enough that `|u_s|` dominates
the cumulative length. Smallest probe: draft `chain_orbit_equidist` and check
`tailSched_cfDiscLt`'s induction still closes with `cfDiscLt_short_append`
absorbing a filler of bounded-but-growing length between consecutive `u_s`. If
it abstracts cleanly, 2–3 are mechanical. If NOT, that is the real crux —
escalate (write ROUTE-ESCALATION), do not retreat to more atoms.

---

## B6 — lap 1 landed (2026-08-24): scaffold + single-cylinder bound ✅

New additive leaf `src/NormalNumbers/CFIntervalGood.lean` (imports `CFDigitLaw`;
frozen B5′ modules untouched). Build green (8752).

**Proved this lap** (axiom-clean, on-path leaf):
- `volume_cfCylinder_le_fib (w) (hw) (hpos) : volume (cfCylinder w) ≤
  ENNReal.ofReal (1/(fib (|w|+1))^2)` — the "cylinders shrink" driver. From
  `volume_cfCylinder` (`=1/(qₙ(qₙ+qₙ₋₁))`) + `fib_le_cfK` (`qₙ ≥ fib(n+1)`) +
  `qₙ₋₁ ≥ 0`.

**Aligned statement shapes** (recorded per directive — L1 FINAL, L2 provisional):
- `coveredByCyl a b n := ⋃ w ∈ {w ∈ genWords n | cfCylinder w ⊆ Ioo a b}, cfCylinder w`
  (index over `genWords n` = the CFDigitLaw partition index; avoids a Decidable
  instance on the `⊆` predicate).
- **L1** `volume_interval_sdiff_covered_le (a b) (0≤a) (a≤b) (b≤1) (n) :
  volume (Ioo a b \ coveredByCyl a b n) ≤ ENNReal.ofReal (2/(fib(n+1))^2)`.
- **L2** `volume_interval_good_ge` — PLACEHOLDER (`True`); pin to real
  `goodExtSet`/`goodC` exports once L1 lands.

## B6 — lap 2 landed (2026-08-24): L1 PROVED ✅

`volume_interval_sdiff_covered_le` discharged, axiom-clean (trust triple),
build green (8752). RHS relaxed from `2/fib²` to `4/fib²` — the **soft
M-neighborhood** proof (cleaner than the straddler-count route drafted below):
`M := 1/fib(n+1)²`; every rank-`n` cylinder that straddles `∂(a,b)` has diameter
`≤ M` (`cfCylinder_subset_Icc_length` + `volume_cfCylinder_le_fib`) and meets the
boundary, so it lies within `M` of `a` or `b`; hence uncovered `⊆ [a−M,a+M] ∪
[b−M,b+M]`, mass `≤ 4M`. `n=0` handled separately (mass ≤ 1 ≤ 4). No
disjointness/counting needed — the straddler-count plan was abandoned as
unnecessary.

## B6 — lap 3 landed (2026-08-24): L2 PROVED ✅

`length_le_two_mul_good_add_err` discharged, axiom-clean, build green (8752).
Both L1 and L2 now closed (ahead of the brief's lap plan).
- `goodInInterval a b n m := ⋃ w ∈ {w∈genWords n | cfCylinder w ⊆ Ioo a b},
  goodExtSet w goodC m` — good mass inside `(a,b)`.
- **L2**: `|b−a| ≤ 2·volume(goodInInterval a b n m) + 4/fib(n+1)²` (for `n≥1`, any
  `m`). ⇒ good mass inside any interval is `≥ (|b−a|−δ)/2` beyond a rank.
- Proof: `measure_biUnion` over the contained-cylinder index (disjoint via
  `cfCylinder_disjoint`, measurable) turns both covered/good masses into tsums;
  per-term `goodC_half` (`|I_w| ≤ 2|goodExtSet w goodC m|`) + `ENNReal.tsum_le_tsum`
  gives `covered ≤ 2·good`; `measure_inter_add_sdiff` + L1 close it. New helpers
  `goodExtSet_subset_cfCylinder`, `measurableSet_goodExtSet`.
- `goodExtSet`/`goodC`/`goodC_half` all live in `NormalNumbers` ns; import
  `NormalNumbers.CFSchedule` (done in `CFIntervalGood.lean`).

## B6 — lap 4 landed (2026-08-24): L3 PROVED ✅

`CFAffine.lean` (new additive module, axiom-clean, build green 8753). The affine
map `affineMap q r x = q*x+r` (q>0) as interval algebra:
- `preimage_affineMap_Ioo`: `ψ⁻¹(c,d) = ((c−r)/q, (d−r)/q)`
- `image_affineMap_Ioo`: `ψ''(a,b) = (q*a+r, q*b+r)`
- `volume_preimage_affineMap_Ioo`: `|ψ⁻¹(c,d)| = (d−c)/q`
- `good_mass_in_affine_preimage`: transports L2 through the pullback — target
  interval preimage length `≤ 2·good mass inside + 4/fib(n+1)²`.
q>0 only; general q≠0 via `x↦−x` at point of use.

**L1+L2+L3 all closed — the metric substrate of B6 is DONE.** What remains is
the genuine crux:

## B6 — lap 5 landed (2026-08-24): affine pullback measure + L4 ROUTE ANALYSIS ✅

Proved `volume_preimage_affineMap` (CFAffine.lean, axiom-clean): `volume(ψ⁻¹ s) =
|q⁻¹|·volume s` for any `q≠0,s` — the L4 union-bound ingredient. Build green (8753).

### ⚠️ ROUTE-DECISIVE FINDING (L4 is a REAL theorem, not "mechanical threading")

`IsCFNormal (ψ xstar)` is about the CF-digit **windows of the single real number
`ψ(xstar)`**, read off by iterating the Gauss map `T` on `ψ(xstar)` ITSELF
(`IsCFNormal`, `Headline.lean:71`: `T^k(ψ xstar) ∈ cfCylinder v` frequency → γ).
Crucially **`T` does NOT commute with `ψ`** — the CF expansion of `qx+r` has no
finite relation to that of `x` for general real `q`. (This is exactly why
Vandehey §7 restricts to `q,r` QUADRATIC: only then does `ψ` act nicely on CF
tails via the geodesic flow. For arbitrary real `q` the problem is likely open
or false.) So the B5′ trick — *prescribe* xstar's digit sequence to be
CF-normal, and windows-of-the-prefix = orbit-visits — does NOT directly give
`ψ(xstar)` CF-normal: we cannot independently prescribe both digit sequences.

**Consequence for the interval-transport insight (KHINCHIN.md §B6).** L1–L3
(ψ maps intervals to intervals, |ψ⁻¹(J)|=|J|/q, good density transports) are
NECESSARY but NOT SUFFICIENT. Interval nesting controls only the FIRST few CF
digits of `ψ(xstar)` per stage, not its whole orbit.

**The route that CAN work — INTERLEAVED (diagonal) schedule.** Build xstar as a
limit of nested x-intervals where stages ALTERNATE:
- **x-stages**: refine to a good x-cylinder (fixes next block of xstar's OWN CF
  digits with correct freq) — the existing B5′ mechanism.
- **ψ-stages** (per image system i): refine so `ψᵢ(xstar)` enters a prescribed
  GOOD ψ-cylinder = xstar enters `ψᵢ⁻¹(good ψ-cylinder)`, an x-INTERVAL. L1/L2/L3
  say that interval contains good x-cylinders of positive density, so the refine
  is feasible; `good_mass_in_affine_preimage` is exactly this density.
Over infinitely many alternating stages: xstar's digit seq is CF-normal (x-stages)
AND `ψᵢ(xstar)`'s digit seq is CF-normal (ψ-stages). The digits contributed by
the "other" stages must not spoil frequency — they do not, because every stage
selects a GOOD (correct-freq) block. This is a genuine but plausible multi-lap
construction; the density substrate (L1–L3) is now all proved.

### lap 6 landed (2026-08-24): L4 KERNEL `isCFNormal_of_orbit_freq` PROVED ✅

`CFOrbitFreq.lean` (axiom-clean, build green 8754). `x`-generic:
`IsCFNormal y ⟸ (∀j, Tʲy ∈ (0,1)) ∧ (∀ genuine v, blockCount(I_v) p y / p →
γ(I_v))`. Via the existing generic bridge `blockCount_sub_countOccurrences_bounds`
(`CFWordBridge`, orbit-count vs window-count differ by ≤|v|) + squeeze.
**Sub-obligation 1 is thus DONE** — the orbit⇔window machinery is `x`-generic and
already in the codebase (`iterate_mem_cfCylinder_iff`, `blockCount_eq_card_matches`,
`blockCount_sub_countOccurrences_bounds`, all take `y`/`x` free).

**REFINED L4 target.** `IsCFNormal (ψ xstar)` now reduces (via
`isCFNormal_of_orbit_freq` at `y := affineMap q r xstar`) to TWO obligations:
  (A) `∀ j, gaussMap^[j] (ψ xstar) ∈ (0,1)` — ψ(xstar) has a full Gauss orbit;
  (B) `∀ genuine v, blockCount (cfCylinder v) p (ψ xstar) / p → γ(I_v)` — the
      orbit of ψ(xstar) equidistributes (Birkhoff/orbit-frequency form).
(B) is the genuine crux. The interleaved schedule must make ψ(xstar) land in a
nested chain of GOOD ψ-cylinders (⇒ its digit sequence is prescribed CF-normal
⇒ orbit-freq → γ, exactly as `xstar_cf_freq_tendsto` gives it for xstar). L2/L3
(`good_mass_in_affine_preimage`) supply the density that makes each ψ-stage refine
feasible; `volume_preimage_affineMap` bounds the pullback bad zone.

### lap 7 landed (2026-08-24): CFScheduleA scaffold — target reduced to ONE crux sorry ✅

`CFScheduleA.lean` (build green 8755, one disclosed sorry). Also
`isCFNormal_of_irrational_orbit_freq` (CFOrbitFreq, axiom-clean).
- `CFOrbitEquidist y := ∀ genuine v, blockCount(I_v) p y/p → γ(I_v)`.
- **`exists_cfNormal_and_affine_cfNormal {q}(hq:0<q)(r) : ∃ x, IsCFNormal x ∧
  IsCFNormal (affineMap q r x)` is PROVED** modulo one crux — the assembly uses
  the orbit-frequency interface, real content.
- **THE ONE CRUX (`exists_interleaved_affine_witness`, sorry, CFScheduleA:56/61):**
  `∃ x, (Irrational x ∧ x∈(0,1) ∧ CFOrbitEquidist x) ∧ (Irrational (ψx) ∧
  ψx∈(0,1) ∧ CFOrbitEquidist (ψx))`. This is the interleaved schedule.

**src/ now carries exactly ONE active sorry** — the isolated B6 crux (correct
decomposition). All B6 substrate below it is axiom-clean.

### lap 8 landed (2026-08-24): feasibility core `goodInInterval_pos_of_lt` ✅

Axiom-clean, build green (8755). Beyond a rank (`4/fib(n+1)² < b−a`), good mass
inside any nondegenerate `(a,b)⊆(0,1)` is STRICTLY positive ⇒ `goodInInterval`
nonempty ⇒ a good CF-cylinder exists inside `(a,b)`. **This discharges the
per-stage feasibility of the interleaved schedule** — every refinement step
(x-stage on `cfCylinder wx`, ψ-stage on the pullback `((c−r)/q,(d−r)/q)`, or the
combined interval `cfCylinder wx ∩ ψ⁻¹(cfCylinder wz)`, all intervals) has a good
block to pick. The ψ-side needs NO separate lemma: apply `goodInInterval_pos_of_lt`
to the pullback endpoints (from `preimage_affineMap_Ioo`). Substrate for the
crux is now essentially complete; what remains is purely the schedule bookkeeping.

### lap 9 landed (2026-08-24): structural helper `take_eq_of_mem_cfCylinder` ✅

Axiom-clean, build green (8755). Nesting ⇒ prefix: a point in `cfCylinder w` ∩
`cfCylinder w'` with `|w|≤|w'|` forces `w'.take|w| = w`. So a deep good cylinder
inside `cfCylinder wx` (from `goodInInterval_pos_of_lt`) is a genuine EXTENSION of
`wx` — the bridge from "good geometric cylinder in the interval" to "appended
block", keeping x's prescribed digits consistent across ψ-stage refinements.

### lap 10 landed (2026-08-24): `eq_of_mem_cfCylinder_chain` ✅

Axiom-clean, build green (8755). Nested extending genuine cylinder chains pin a
UNIQUE point (diam ≤ 1/fib(len+1)² → 0). Obligation-(A) ingredient: the affine
image ψ(x) lies in the whole ψ-word chain, and (applying `exists_irrational_mem_
iInter_cfCylinder` to that ψ-chain to get an irrational in the same intersection)
this lemma forces ψ(x) = that irrational ⇒ **ψ(x) irrational in (0,1)**. Combined
with `take_eq_of_mem_cfCylinder` the (A) side is nearly mechanical.

### lap 11 landed (2026-08-24): obligation (A) discharged GENERICALLY ✅
`irrational_mem_Ioo_of_mem_iInter_cfCylinder` (CFScheduleA, axiom-clean, build
green 8745). For ANY extending chain of genuine CF words `w` and any point `y`
in every `cfCylinder (w s)`: `Irrational y ∧ y ∈ (0,1)`. Proof = 4 lines:
`exists_irrational_mem_iInter_cfCylinder` gives an irrational ξ in the ∩;
`eq_of_mem_cfCylinder_chain` forces `y = ξ`; `cfCylinder_subset_Ioo` gives the
box. **This closes BOTH `(A)`-side conjuncts of the crux** — apply it to `x`'s
own word chain (⇒ `Irrational x ∧ x∈(0,1)`) and to the ψ-word chain with `ψ(x)`
in each ψ-cylinder (⇒ `Irrational (ψx) ∧ ψx∈(0,1)`). What remains in the crux is
ONLY obligation (B) (orbit equidistribution of both streams) + producing the two
word chains from the interleaved schedule. Obligation (A) is now a one-liner
given the chains.

**NEXT ATTACK (obligation B, the genuine heart).** Build the light interleaved
`SchedState` (fields: x-word `wx`, ψ-word `wz`, invariant `cfCylinder wx ⊆
ψ⁻¹(cfCylinder wz)` nonempty). Alternate: x-stage appends a good block to `wx`
inside `cfCylinder wx` (feasible: `goodInInterval_pos_of_lt`); ψ-stage appends a
good block to `wz` after refining `wx` so `ψ(cfCylinder wx) ⊆ cfCylinder wz'`
(feasible: `good_mass_in_affine_preimage` gives good x-density in the pullback).
Then mirror `xstar_cf_freq_tendsto` (CFCorrect) for BOTH `wx` and `wz` streams.
KEY sub-question to settle first (cheap probe next lap): the "uncontrolled"
digits that x-stages force onto ψ(x) (and vice-versa) between good blocks must be
asymptotically negligible — pick block lengths so the good-block count dominates.
Verify the CFCorrect telescoping (`tailSched_cfDiscLt` + `exists_stage`) still
gives the freq limit when a positive-density fraction of appended digits is
"uncontrolled" — OR arrange the schedule so EVERY appended block (both streams)
is good (no uncontrolled digits: each stage's refinement is itself a good block
for the stream being extended, and the OTHER stream's cylinder is only refined
at ITS own stages). The latter is cleaner: `wz` only grows at ψ-stages, `wx`
only at x-stages, so each stream sees only good blocks — no uncontrolled digits.

### lap 11 (cont.) — ROUTE-DECISIVE finding on obligation (B)'s missing atom 🔍
Traced exactly what obligation (B) still needs and where it lives:
- `goodInInterval`/`goodExtSet` give only **DENSITY** (short-continuant ⇒
  positive relative length, `goodExtSet` = extensions with `cfK u ≤ e^{Cn}`),
  NOT **frequency** control. So `goodInInterval_pos_of_lt` alone cannot supply a
  CF-normal block — it keeps intervals fat but says nothing about digit-window
  frequencies.
- The FREQUENCY control lives in `TBrick.exists_refinement_uniform`
  (`TBrickRefine.lean:432`) — its conclusion bundles the `CFDiscLt`-style
  `∀ v∈F, |countOccurrences v u − γ(I_v)·n| < δn + |v|` payload TOGETHER with the
  base-`d` `daryCell` cell-nesting. `TBrick.exists_refinement` (line 554) wraps
  it but is still TBrick-bound.
- **THE single missing engine** for the light interleaved schedule =
  a **daryCell-free CF core** of `exists_refinement_uniform`: for genuine `w`,
  finite pattern family `F`, `δ>0`, produce arbitrarily long blocks `u` that are
  BOTH short-continuant (density) AND `F`-frequency-good, with `cfCylinder(w++u)`
  landing in a PRESCRIBED subinterval of `cfCylinder w` (needed so x-stage /
  ψ-stage refinements can target the combined interval `cfCylinder wx ∩
  ψ⁻¹(cfCylinder wz)`). Extract by re-running `exists_refinement_uniform`'s proof
  and DROPPING the `daryCell` conclusion (keep the badBlocks/half-mass density +
  the `wordFamily` count bound). This is additive (new file, e.g.
  `CFFreqBlock.lean`, imports `TBrickRefine` for the density lemmas; never edits
  it). Once it exists, the interleaved schedule is: maintain nonempty combined
  Ioo `J_n`; x-stage appends a freq-good block landing in `J_n` (feasible: `J_n`
  nondegenerate ⇒ engine gives block, `take_eq_of_mem_cfCylinder` ⇒ extends wx);
  ψ-stage appends a freq-good block to wz landing in `ψ(J_n)` (feasible via
  `good_mass_in_affine_preimage`+engine, then pull back). Each stream then sees
  ONLY freq-good blocks ⇒ mirror `xstar_cf_freq_tendsto` per stream ⇒ (B). Design
  verified sound this lap (x-stage keeps ψ(x)∈cfCylinder wz since J shrinks
  inside ψ⁻¹(cfCylinder wz); ψ-stage symmetric). **Next lap: build
  `exists_freq_good_block` (the daryCell-free core) — the whole crux funnels to
  it + the per-stream telescoping.**

### lap 12 landed (2026-08-24): the frequency engine `exists_freq_good_block` ✅
`CFFreqBlock.lean` (new additive module, axiom-clean trust-triple, build green
8756). The daryCell-free CF core of `TBrick.exists_refinement_uniform` is DONE:
for genuine `w`, finite family `F`, `δ>0`, ∃N ∀n≥N ∃ genuine block `u` (`|u|=n`)
that is `F`-frequency-good (`|countOccurrences v u − γ(I_v)·n| < δn+|v|` ∀v∈F)
with an irrational point in `cfCylinder(w++u)`. **Extraction trick**: instantiate
`exists_good_avoiding_bad_of_large` at level `t=1` (⇒ `Finset.Icc 2 1 = ∅`, the
whole d-ary bad-zone union vanishes) on a `trivBrick w` (vacuous cell obligations
since `2≤d≤1` is false); unpack the survivor's goodExtSet word + cfBadZone
avoidance exactly as the CF payload of `exists_refinement_uniform` does. **This is
THE atom obligation (B) funnels to.** No edits to any frozen module.

**NEXT ATTACK (the interleaved schedule itself).** With `exists_freq_good_block`
in hand, build the two-stream construction in `CFScheduleA` (or a new
`CFScheduleAImpl.lean`):
1. Joint state `⟨wx, wz, hx: genuine, hz: genuine, hJ: (cfCylinder wx ∩
   ψ⁻¹(cfCylinder wz)).Nonempty⟩`. Note `cfCylinder w` IS an open interval (its
   endpoints are `cfCylinder_endpoints`), so `J` is an Ioo — get its endpoints to
   apply the affine/good lemmas.
2. x-STAGE: `J` nondegenerate ⇒ (density via `goodInInterval_pos_of_lt`) a good
   x-cylinder sits in `J`; use `exists_freq_good_block` on `wx` with a large-`n`
   freq-good block, then INTERSECT the choice with landing in `J` — CAVEAT: the
   engine gives *a* freq-good block, not one whose cylinder ⊆ `J`. Bridge needed:
   either (a) a version of the engine RELATIVIZED to an interval (pick the
   surviving `x` inside `J` — feasible because `J∩goodExtSet` still has ≥ half of
   `J`'s mass by the same union bound, since the bad zones are measured against
   `cfCylinder wx ⊇ J`), or (b) show the freq-good block can be chosen with
   `cfCylinder(wx++u) ⊆ J` by taking `n` large enough that the cylinder is smaller
   than `J` AND lands in it (needs a placement argument). **(a) is the clean route
   — next lap: prove `exists_freq_good_block_in_interval`, the engine with the
   survivor confined to a subinterval `J ⊆ cfCylinder w` of positive measure.**
3. ψ-STAGE: symmetric, on `wz`, targeting `ψ(J)` (an interval via `CFAffine`
   image lemmas); pull the chosen point back through `ψ⁻¹`.
4. Take `x := ` unique point of `⋂ cfCylinder wx` (`eq_of_mem_cfCylinder_chain` +
   `exists_irrational_mem_iInter_cfCylinder`); obligation (A) via lap-11
   `irrational_mem_Ioo_of_mem_iInter_cfCylinder` on both chains; obligation (B)
   via per-stream telescoping mirroring `xstar_cf_freq_tendsto` (the freq-good
   blocks are exactly its `uSched`/`wordFamily` inputs).

### lap 13 landed (2026-08-24): placement primitive + INTERVAL-RELATIVIZED engine ✅
`CFScheduleA.lean` (axiom-clean trust-triple, build green 8756):
- `exists_cfCylinder_subset_Ioo` — every nondegenerate `(a,b)⊆(0,1)` contains a
  genuine CF cylinder (via `goodInInterval_pos_of_lt` nonempty + index unpack).
- **`exists_freq_good_block_in_Ioo`** — THE interval-relativized frequency engine
  (route (a) from lap 12): for family `F`, `δ>0`, and `(a,b)⊆(0,1)`, ∃ placement
  word `w` with `cfCylinder w ⊆ (a,b)` and ∃N ∀n≥N a freq-good block `u` (`∀v∈F,
  |countOccurrences v u − γ(I_v)·n|<δn+|v|`) with an irrational point of
  `cfCylinder(w++u)` INSIDE `(a,b)`. Composes the placement primitive with
  `exists_freq_good_block`. **This is exactly what each schedule stage consumes**:
  x-stage on `(a,b)=cfCylinder wx` (or `J`), ψ-stage on `(a,b)=ψ(cfCylinder wx)`
  (an interval via `CFAffine` image lemmas), then pull back through `ψ⁻¹`. The
  placement word `w` is the bounded per-stage "filler" (chosen once to enter the
  interval), `u` the long freq-good payload ⇒ filler asymptotically negligible.

**NEXT ATTACK — the interleaved schedule assembly (the crux itself).** All atoms
are now axiom-clean and in `src/`. Remaining is the recursive two-stream schedule
+ per-stream telescoping:
1. Joint `SchedStateA ⟨wx, wz, hx_gen, hz_gen, hψ : ψ(cfCylinder wx) ⊆
   cfCylinder wz⟩` (invariant makes `J = cfCylinder wx`, a cylinder).
2. `schedStepA`: alternate (parity on stage index).
   - x-stage: `exists_freq_good_block_in_Ioo` on `(a,b) := endpoints of cfCylinder
     wx` (`cfCylinder_endpoints`); the returned `w++u` extends wx
     (`take_eq_of_mem_cfCylinder`); new wx' = that word, wz unchanged; invariant
     preserved (cfCylinder wx' ⊆ cfCylinder wx ⇒ ψ-image still ⊆ cfCylinder wz).
   - ψ-stage: `(a,b) := endpoints of ψ(cfCylinder wx)` (`image_affineMap_Ioo`
     applied to wx's endpoints); engine gives `w_z'`=`wz''++u_z` with
     `cfCylinder w_z' ⊆ ψ(cfCylinder wx)`; set wz' = that word (extends wz via
     take_eq since ⊆ cfCylinder wz), and REFINE wx to wx'' = the pullback deep
     word so `ψ(cfCylinder wx'') ⊆ cfCylinder wz'` (feasible: pick wx'' with
     `cfCylinder wx'' ⊆ ψ⁻¹(cfCylinder w_z') ∩ cfCylinder wx`, nonempty interval,
     via `exists_cfCylinder_subset_Ioo` on that combined interval's endpoints).
3. `xA := ` unique point of `⋂ cfCylinder wx` (limit lemmas). (A) both sides via
   `irrational_mem_Ioo_of_mem_iInter_cfCylinder`; ψ(xA) lies in `⋂ cfCylinder wz`.
4. (B) per stream: mirror `CFCorrect.xstar_cf_freq_tendsto` — the appended
   segments are `exists_freq_good_block_in_Ioo`'s freq-good `u`'s (plus bounded
   fillers, absorbed by `cfDiscLt_short_append`). Needs a light re-derivation of
   `tailSched_cfDiscLt`/`uSched_dominance` for THIS schedule (copy-extend
   CFCorrect; never edit it). This is the multi-lap body — but now every
   analytic/geometric atom it calls is proved.
Faithfulness gate after any schedule work: re-`#print axioms
exists_absolutely_normal_cf_normal_khinchin` MUST stay trust-triple.

### lap 14 landed (2026-08-24): cylinder↔interval bridge ✅
`CFScheduleA.lean` (axiom-clean trust-triple, build green 8756):
- `exists_irrational_mem_cfCylinder` — every genuine cylinder has an irrational
  point (trivial `w++1ⁿ` extending chain + `exists_irrational_mem_iInter_cfCylinder`).
- **`exists_Ioo_irrational_subset_cfCylinder`** — `cfCylinder w ⊇` all irrationals
  of a fixed nondegenerate `(a,b)⊆(0,1)` (its convergent-endpoint interval
  `cfCylinder_endpoints`, clamped to `(0,1)`; strictness from an irrational
  witness strictly between the rational endpoints). **This is the bridge that
  lets the schedule feed `cfCylinder wx` to `exists_freq_good_block_in_Ioo`**:
  take `(a,b)` from this lemma, run the interval engine on it; the engine's
  returned cylinder ⊆ `(a,b)`, and its irrational points land in `cfCylinder wx`.
  Combined with `take_eq_of_mem_cfCylinder` (shared irrational point + length
  ordering) the new word EXTENDS wx — no separate "extends" lemma needed.

**NEXT ATTACK — assemble the schedule step `schedStepA` (still the crux).** Every
geometric atom is now proved. One remaining glue lemma to prove first, then the
recursion:
- `exists_freq_good_extend_cfCylinder (wx genuine) (F) (δ>0) (L : ℕ) : ∃ wx'
  genuine, wx'.take wx.length = wx ∧ wx.length < wx'.length ∧ L ≤ wx'.length ∧
  cfCylinder wx' ⊆ cfCylinder wx ∧ (∀v∈F, freq-good on wx'‑suffix within δ) ∧
  (cfCylinder wx').Nonempty`. Build it by: `(a,b) := exists_Ioo_irrational_subset_
  cfCylinder wx`; `⟨w,_,_,hsub,N,hN⟩ := exists_freq_good_block_in_Ioo F .. (a,b)`;
  pick `n := max N (max L wx.length) + 1`, get block `u` + irrational point `p ∈
  cfCylinder(w++u) ⊆ (a,b)`; `p ∈ cfCylinder wx` (bridge) ∧ `p ∈ cfCylinder(w++u)`
  with `|wx| ≤ |w++u|` ⇒ `take_eq_of_mem_cfCylinder` ⇒ `w++u` extends wx; set
  `wx' := w++u`. NB the freq-good property is on the block `u` (a SUFFIX of wx'),
  with the placement filler `w[|wx|:]` bounded — feed both to the telescoping.
- Then `SchedStateA` + `schedStepA` (x/ψ parity) + `schedA : ℕ → SchedStateA` by
  choice, `xA := ` limit point, and the per-stream freq telescoping (copy-extend
  `CFCorrect`). This is the multi-lap body; atoms all green.

### lap 15 landed (2026-08-24): single-stream stage `exists_freq_good_extend_cfCylinder` ✅
`CFScheduleA.lean` (axiom-clean trust-triple, build green 8756). The atomic
schedule refinement: given genuine `wx`, family `F`, `δ>0`, depth target `L`, ∃
strict genuine extension `wx'` (`wx'.take|wx|=wx`, `|wx|<|wx'|`, `L≤|wx'|`) with
`cfCylinder wx' ⊆ cfCylinder wx`, split `wx'=w++u` with the tail block `u`
`F`-frequency-good. Composes lap-14 bridge + lap-13 interval engine + `take_eq_of_
mem_cfCylinder` (shared irrational point ⇒ extension). **This is the x-stage in
one lemma** (and the ψ-stage after mapping through the affine image interval).

**NEXT ATTACK — the recursion + telescoping (crux body).** With the atomic stage
proved, remaining:
1. ψ-stage variant: `exists_freq_good_extend_affine` — same, but the new
   x-refinement `wx'` ALSO forces `ψ(cfCylinder wx') ⊆` a fresh good ψ-cylinder
   `wz'` extending `wz`. Build from `exists_freq_good_extend_cfCylinder` applied
   to the ψ-image interval `ψ(cfCylinder wx)` (via `image_affineMap_Ioo` on wx's
   endpoints from `exists_Ioo_irrational_subset_cfCylinder`) to get `wz'`, then
   refine wx into `ψ⁻¹(cfCylinder wz') ∩ cfCylinder wx` (nonempty interval;
   `exists_cfCylinder_subset_Ioo` on its endpoints) to get `wx'`.
2. `SchedStateA ⟨wx, wz, invariants⟩`; `schedStepA` alternates x/ψ by parity;
   `schedA : ℕ → SchedStateA` by choice (mirror `CFSchedule.sched`).
3. `xA := ` limit of `⋂ cfCylinder (schedA s).wx`; obligation (A) both sides via
   `irrational_mem_Ioo_of_mem_iInter_cfCylinder`.
4. Obligation (B): per-stream freq telescoping. The appended segments are the
   `u`'s of `exists_freq_good_extend_cfCylinder` (freq-good) plus bounded
   placement fillers `w[|wx|:]`; mirror `CFCorrect.xstar_cf_freq_tendsto`'s
   `cfDiscLt` telescoping (needs light re-derivation of `tailSched_cfDiscLt` /
   `uSched_dominance` analogues — copy-extend CFCorrect, never edit). This is the
   multi-lap analytic body; every atom it calls is now proved & axiom-clean.
Faithfulness gate after schedule work: `#print axioms
exists_absolutely_normal_cf_normal_khinchin` MUST stay trust-triple.

### lap 16 landed (2026-08-24): ψ-stage x-selection primitive ✅
`exists_cfCylinder_subset_affine_preimage` (CFScheduleA, axiom-clean, green
8756): for `q>0` and target `z`-interval `(c,d)` with `ψ`-preimage in `(0,1)`, a
genuine `x`-cylinder sits inside `ψ⁻¹(c,d)` (= `preimage_affineMap_Ioo` +
`exists_cfCylinder_subset_Ioo`). Places `x` so `ψ(x)` enters a prescribed good
`z`-cylinder — the ψ-stage counterpart of the x-stage's placement.

**NEXT — assemble the ψ-stage `exists_freq_good_extend_affine`** (the last atom
before the recursion). Given genuine `wx, wz` with invariant `cfCylinder wx ⊆
ψ⁻¹(cfCylinder wz)`, `F`, `δ`, depth `L`: produce `wz'` (extends wz, freq-good,
`cfCylinder wz'⊆cfCylinder wz`) and `wx'` (extends wx, `cfCylinder wx'⊆cfCylinder
wx`, `ψ(cfCylinder wx')⊆cfCylinder wz'`). Recipe (all atoms now proved):
  (i) wz-interval `(e,f)` via `exists_Ioo_irrational_subset_cfCylinder wz`;
      wx-interval `(a,b)` via same on wx; image `(qa+r,qb+r)` via
      `image_affineMap_Ioo`. Target `J_z := (max(qa+r) e ⊓ …, …)` = the z-interval
      inside BOTH `ψ(wx-interval)` and `(e,f)` — nonempty since ψ(irrational of
      (a,b)⊆cfCylinder wx)⊆cfCylinder wz gives a common point.
  (ii) `exists_freq_good_block_in_Ioo F .. J_z` ⇒ `wz'` freq-good, cfCylinder
      wz'⊆J_z⊆(e,f) ⇒ extends wz (irrational pt + take_eq).
  (iii) `wz'`'s interval `(c,d)` (its endpoints); `exists_cfCylinder_subset_
      affine_preimage` on `(c,d)` intersected with `(a,b)` ⇒ `wx'` with
      cfCylinder wx'⊆ψ⁻¹(cfCylinder wz')∩cfCylinder wx ⇒ ψ(cfCylinder wx')⊆
      cfCylinder wz' and nested in wx.
CAVEAT to handle: ψ does NOT preserve irrationality, so the "irrationals of
(c,d)⊆cfCylinder wz'" bridge can't transfer across ψ — that's why (iii) selects
the x-cylinder via the PREIMAGE interval directly (no irrational transfer
needed), and (ii) places wz' via the z-side interval bridge (`exists_Ioo_
irrational_subset_cfCylinder wz`), keeping all irrational-caveats on ONE side of
ψ each. Then the recursion (`SchedStateA`/`schedStepA`/limit/telescoping).

### lap 17 landed (2026-08-24): two-interval intersection placement ✅
`exists_cfCylinder_subset_Ioo_inter` (CFScheduleA, axiom-clean, green 8756): a
genuine cylinder inside `Ioo a b ∩ Ioo c d` whenever `(max a c, min b d)` is a
nondegenerate subinterval of `(0,1)`. Lets the ψ-stage place `x` in
`cfCylinder wx`'s interval AND a good z-cylinder's ψ-preimage at once.

**KEY REMAINING SUB-LEMMA for the ψ-stage (next lap): the image-inclusion**
`affine_image_wxInterval_subset_wzInterval`. Setup: wx,wz genuine, invariant
`cfCylinder wx ⊆ ψ⁻¹(cfCylinder wz)` (q>0); `(a,b)` the wx-interval (irr(a,b)⊆
cfCylinder wx), `(e,f)` the wz-interval (cfCylinder wz ⊆ Icc e f — use the uIcc
bound from `cfCylinder_endpoints`, NOT just the irr-subset). CLAIM: `ψ((a,b)) =
(qa+r,qb+r) ⊆ (e,f)` — hence the target z-interval `J_z := ψ((a,b))` is nonempty
and inside the wz-region, so the ψ-stage can run `exists_freq_good_block_in_Ioo`
on `J_z` (z-side, no ψ-transfer) and `exists_cfCylinder_subset_affine_preimage`
on the resulting good z-cylinder (x-side). PROOF of the claim: irr(a,b)⊆
cfCylinder wx ⇒ ψ(irr(a,b))⊆cfCylinder wz⊆Icc e f; irr(a,b) dense in (a,b), ψ
continuous+increasing ⇒ ψ((a,b))⊆closure(ψ(irr(a,b)))⊆Icc e f; ψ((a,b)) open ⇒
⊆(e,f). (Endpoints: `qa+r = ⨅ψ((a,b))≥e`, `qb+r≤f` — a `le_of_forall_lt` / inf
argument, or a direct sequential limit `x_n↑a` irrational with ψ(x_n)≥e.) This is
the one genuinely analytic step of the ψ-stage (~15-30 lines); everything else is
the composed atoms. Then assemble `exists_freq_good_extend_affine`, then the
recursion + telescoping.

### lap 18 landed (2026-08-24): ψ-image inclusion (the analytic step) ✅
`affine_image_Ioo_subset_Icc` (CFScheduleA, axiom-clean, green 8756): under the
invariant `cfCylinder wx ⊆ ψ⁻¹(cfCylinder wz)`, with irr(a,b)⊆cfCylinder wx and
cfCylinder wz⊆Icc e f, the ψ-image `ψ((a,b)) ⊆ Icc e f`. Proof = two symmetric
`exists_irrational_btwn` contradiction blocks (a boundary-violating image point
pulls back to an irrational of (a,b) whose image escapes Icc e f). **This is the
one genuinely analytic step of the ψ-stage** — no ψ-irrationality transfer, no
sequences. Every ψ-stage ingredient is now proved & axiom-clean.

### lap 19 (design-decisive) — the ψ-irrationality obstruction RESOLVED 🔑
Strengthened `exists_Ioo_irrational_subset_cfCylinder` to ALSO return
`cfCylinder w ⊆ Icc a b` (green, axiom-clean; caller updated). More importantly,
worked out the correct schedule INVARIANT that dodges the "ψ doesn't preserve
irrationality" wall:

**Problem.** The naive invariant `cfCylinder wx ⊆ ψ⁻¹(cfCylinder wz)` (set
inclusion) is NOT establishable: placing `wx'` needs `ψ(cfCylinder wx')⊆
cfCylinder wz'`, but `cfCylinder wz'` is only an interval FOR IRRATIONALS, and
`ψ` maps some irrationals to rationals — so the interval-placement gives only
`ψ(cfCylinder wx')⊆Ioo(wz'-endpoints)`, which does NOT imply ⊆cfCylinder wz'.
Symmetrically, even the limit `ψ(xA)` isn't obviously in `cfCylinder wz'` because
`ψ(xA)` may be rational.

**Resolution (interval invariant + irrational-by-nesting).** Maintain instead the
INTERVAL-preimage invariant
  `cfCylinder wx_s ⊆ ψ⁻¹(Ioo (E0 wz_t) (E1 wz_t))`   (a genuine interval preimage,
establishable via `exists_cfCylinder_subset_affine_preimage`/`_Ioo_inter`, where
`E0,E1` are `wz_t`'s convergent endpoints). Then:
  • the wz-endpoint intervals `Ioo(E0 wz_t)(E1 wz_t)` are NESTED with rational
    endpoints shrinking to a point (diam ≤ 1/fib² → 0, `cfCylinder_endpoints`);
  • `ψ(xA) ∈ ⋂_t Ioo(E0 wz_t)(E1 wz_t)` (from the invariant + `xA∈cfCylinder
    wx_s` all s);
  • a point in infinitely many shrinking RATIONAL-endpoint intervals is
    IRRATIONAL (same argument as `CFLimit`/`exists_irrational_mem_iInter_
    cfCylinder`) ⇒ `ψ(xA)` irrational;
  • `ψ(xA)` irrational ∈ Ioo(E0 wz_t)(E1 wz_t) ⇒ (the `hUIoo` clause of
    `cfCylinder_endpoints`) `ψ(xA) ∈ cfCylinder wz_t` — for EVERY t. Hence
    `ψ(xA)` is pinned into the whole wz-chain ⇒ CF-normal by the same
    freq-telescoping as xA.
So the ψ-side never needs ψ to preserve irrationality: irrationality of ψ(xA) is
RECOVERED at the limit from the nested rational-endpoint intervals, exactly as
for xA itself. This is the key that makes B6 provable for general real q>0
(NOT just quadratic). Record the invariant as the `SchedStateA` field; the
ψ-stage lemma below produces the interval-preimage nesting, not a cylinder
inclusion.

**NEXT — assemble `exists_freq_good_extend_affine` (the ψ-stage), then recursion.**
Recast with the interval invariant (mechanical from the atoms):
1. wx-interval (a,b) [`exists_Ioo_irrational_subset_cfCylinder wx`]; wz-endpoints
   (e,f) with cfCylinder wz⊆Icc e f AND irr(e,f)⊆cfCylinder wz [both from
   `cfCylinder_endpoints`/`exists_Ioo_irrational_subset_cfCylinder wz` — may need
   a small helper exposing the Icc bound alongside the irr-subset; `cfCylinder_
   endpoints` gives `cfCylinder wz ⊆ uIcc = Icc(min)(max)` directly].
2. `affine_image_Ioo_subset_Icc` ⇒ J_z:=ψ((a,b))=Ioo(qa+r)(qb+r) ⊆ Icc e f, so
   irr(J_z)⊆Ioo e f (irrationals dodge the rational endpoints) ⊆ cfCylinder wz.
3. `exists_freq_good_block_in_Ioo F .. J_z` ⇒ wz' freq-good, cfCylinder wz'⊆J_z
   ⇒ (irr pt) extends wz.
4. wz'-endpoints (c,d); the preimage interval ((c-r)/q,(d-r)/q)⊆(a,b); intersect
   with (a,b) [trivially ⊆] and use `exists_cfCylinder_subset_affine_preimage`
   (or `_Ioo_inter`) ⇒ wx' with cfCylinder wx'⊆ψ⁻¹(cfCylinder wz')∩cfCylinder wx,
   extends wx, ψ(cfCylinder wx')⊆cfCylinder wz'. New invariant holds.
5. `SchedStateA`/`schedStepA` (parity x/ψ) + `schedA` by choice + limit point +
   per-stream `cfDiscLt` telescoping (copy-extend `CFCorrect`). Multi-lap body;
   all atoms green.

### lap 20 landed (2026-08-24): squeeze-to-a-point `eq_of_mem_iInter_Icc` ✅
`CFScheduleA`, axiom-clean, green 8756: two reals in every member of a sequence
of closed intervals with diameters `→0` are equal (`|y−z|≤hi_s−lo_s→0`). The
abstract nesting-uniqueness for the lap-19 resolution: `ψ(xA)` and the wz-chain's
irrational point ζ both lie in every wz-endpoint interval (diam `1/(K(K+K'))→0`)
⇒ `ψ(xA)=ζ` ⇒ `ψ(xA)` irrational + `∈⋂cfCylinder wz_t`.

**NEXT — the wz-endpoint diameter `→0` fact + wire the limit.** To use
`eq_of_mem_iInter_Icc` at the wz-chain: need `lo_t,hi_t := ` wz_t endpoints (from
`cfCylinder_endpoints`) with `hi_t−lo_t = 1/(cfK(wz_t)·(cfK(wz_t)+cfK'))→0`
(cfK(wz_t)≥fib(|wz_t|+1)→∞ since the chain extends). Mirror the diameter bound
already inside `eq_of_mem_cfCylinder_chain`/`exists_irrational_mem_iInter_
cfCylinder` (they compute the same `→0`). Then the limit assembly:
  • ζ, Irrational ζ, ζ∈cfCylinder wz_t ∀t  [`exists_irrational_mem_iInter_
    cfCylinder` on wz-chain];
  • ψ(xA)∈Icc(lo_t)(hi_t) ∀t  [invariant + xA∈cfCylinder wx_s];
  • `eq_of_mem_iInter_Icc` ⇒ ψ(xA)=ζ ⇒ Irrational(ψ xA) ∧ ψ(xA)∈cfCylinder wz_t ∀t;
  • ⇒ CFOrbitEquidist(ψ xA) via `irrational_mem_Ioo_of_mem_iInter_cfCylinder`
    (obligation A for ψ side) + the freq telescoping (obligation B).
Still need: the ψ-stage `exists_freq_good_extend_affine` producing the interval
invariant + wz freq-good chain, and the per-stream freq telescoping (copy-extend
`CFCorrect`). Multi-lap; all atoms green.

### lap 21 landed (2026-08-24): chain volumes → 0 `cfCylinder_chain_volume_tendsto` ✅
`CFScheduleA`, axiom-clean, green 8756: along a strictly extending genuine chain,
`volume(cfCylinder(w s)).toReal → 0` (squeeze by `1/fib(|w_s|+1)² ≤ 1/fib(s+1)`,
`fib→∞`). Combined with `cfCylinder_subset_Icc_length` (Icc of diameter =
volume), this is the `hdiam` input to `eq_of_mem_iInter_Icc` for the wz-chain —
so the ψ(xA)=ζ squeeze is now fully powered. The LIMIT-side machinery (recover
ψ(xA) irrationality + membership in ⋂cfCylinder wz_t) is COMPLETE modulo wiring.

**NEXT — the ψ-stage `exists_freq_good_extend_affine` + the recursion.** The
limit toolkit (`eq_of_mem_iInter_Icc` + `cfCylinder_chain_volume_tendsto` +
`cfCylinder_subset_Icc_length` + `exists_irrational_mem_iInter_cfCylinder` +
`cfCylinder_endpoints`.hUIoo) can now close: given the schedule produces wx-chain
and wz-chain with interval invariant `cfCylinder wx_s ⊆ ψ⁻¹(Icc(lo_t)(hi_t))`
(lo,hi = wz_t Icc-endpoints), then ψ(xA)∈Icc(lo_t)(hi_t)∀t, ζ (irrational, ∈
cfCylinder wz_t) ∈Icc too ⇒ `eq_of_mem_iInter_Icc` ⇒ ψ(xA)=ζ ⇒ done. Still to
build: (a) `exists_freq_good_extend_affine` (ψ-stage, recipe above — produces the
interval invariant + wz freq-good extension); (b) `SchedStateA`/`schedStepA`/
`schedA`/limit; (c) per-stream freq telescoping (copy-extend `CFCorrect`). All
geometric/analytic atoms are now proved & axiom-clean; (a)–(c) are wiring + the
telescoping port.

### TOOLKIT NOW COMPLETE for the interleaved schedule (all axiom-clean):
- CHAIN→0 `cfCylinder_chain_volume_tendsto` — cylinder volumes vanish along a chain.
- SQUEEZE `eq_of_mem_iInter_Icc` — nesting-uniqueness (recovers ψ(xA) irrationality at the limit).
- ψ-IMAGE `affine_image_Ioo_subset_Icc` — ψ((a,b))⊆Icc e f under the invariant (analytic step).
- INTER `exists_cfCylinder_subset_Ioo_inter` — cylinder in the intersection of two intervals.
- ψ-SELECT `exists_cfCylinder_subset_affine_preimage` — x-cylinder in ψ⁻¹(target z-interval).
- STAGE `exists_freq_good_extend_cfCylinder` — one freq-good nested extension (the x-stage).
- CYL↔IOO `exists_Ioo_irrational_subset_cfCylinder` + `exists_irrational_mem_cfCylinder`.
- INTERVAL ENGINE `exists_freq_good_block_in_Ioo` — freq-good block landing in a target interval.
- `exists_cfCylinder_subset_Ioo` — placement: a genuine cylinder inside any nondegenerate interval.
- ENGINE `exists_freq_good_block` — daryCell-free freq-good CF block (obligation B atom).
- (A) `irrational_mem_Ioo_of_mem_iInter_cfCylinder` — irrationality+box from any word chain.
- L1 `volume_interval_sdiff_covered_le` — interval covered by cylinders up to 4/fib².
- L2 `length_le_two_mul_good_add_err` — good mass inside an interval.
- `goodInInterval_pos_of_lt` — good mass STRICTLY positive beyond a rank (feasibility).
- `take_eq_of_mem_cfCylinder` — good cylinder in `cfCylinder wx` = extension of wx.
- L3 `preimage_affineMap_Ioo` / `image_affineMap_Ioo` / `volume_preimage_affineMap`
  / `good_mass_in_affine_preimage` — ψ transports intervals & density; pullback mass.
- `isCFNormal_of_irrational_orbit_freq` — orbit-freq ⇒ IsCFNormal (final step).
What remains is PURELY the schedule bookkeeping (no new analytic content).

**NOTE for next session — Tier-1 needs only CF-normality**, NOT base-b/Khinchin.
So the interleaved schedule can be built LIGHT: control only CF-digit-window
freqs of x and ψ(x) (append good CF-blocks alternately), reusing the CF part of
`goodExtSet`/`CFDiscLt`/`CFCorrect` telescoping — NOT the full TBrick
(daryCell/khinchin) apparatus. Consider a fresh light `SchedState` (word wx +
ψ-word wz + nonempty combined interval invariant) rather than extending TBrick.

**Sub-obligations of the crux (next laps, copy-extend frozen modules into
`CFScheduleA`/new files, NEVER edit frozen):**
1. Orbit⇔window bridge for the IMAGE: `T^k(ψ xstar) ∈ cfCylinder v` ⇔ ψ(xstar)'s
   CF digits `k..k+|v|` = v — needed to turn "ψ(xstar) in prescribed ψ-cylinders"
   into window-frequency (mirror how `xstar_cf_freq_tendsto`/`CFCorrect.lean`
   turns the prescribed x-digit seq into orbit visits). **This is the crux
   sub-question**: does landing ψ(xstar) in a nested chain of ψ-cylinders control
   its whole orbit's visit frequencies? (For xstar it works because the chain IS
   the digit sequence; for ψ(xstar) the chain of ψ-cylinders likewise IS ψ(xstar)'s
   digit sequence — so YES, provided the ψ-stage refinements prescribe ψ(xstar)'s
   digits consecutively. Verify this consecutiveness is maintainable while also
   interleaving x-stages.)
2. Interleaved schedule def + the per-stage union bound: bad_x ∪ ψᵢ⁻¹(bad_ψ)
   has measure < brick mass (base zone via `cfBadZone`; image zone via
   `volume_preimage_affineMap` + L1/L2). Copy-extend `TBrick`/`TBrickRefine`;
   NEVER edit frozen modules.
3. L5 per-map assembly → `IsCFNormal (ψᵢ xstar)`.
Escape valve: Tier 1 (φ headline `x,φx,x+φ`) = 2-element family; Tier 2 general
family the stretch. Faithfulness gate after any work: `#print axioms
exists_absolutely_normal_cf_normal_khinchin` MUST stay trust-triple.

---
### (historical) original L3 plan
**NEXT ATTACK — L3 affine transport** (new module `CFAffine.lean`):
The map `ψ(x) = q·x + r` (`q ≠ 0`). Needed facts:
1. `ψ '' (Set.Ioo a b) = Set.Ioo (ψ a) (ψ b)` when `q>0` (reversed when `q<0`) —
   affine image of an interval is an interval; `volume (ψ '' I) = |q|·volume I`
   (`Real.volume` under affine map; mathlib `Real.volume_image_mul_left`/
   `MeasurePreserving`? or measure_image of `x↦q*x+r` = `|q|` scaling — check
   `Real.volume_preimage_mul` / `MeasureTheory.Measure.addHaar`).
2. CF-normality is invariant under `x ↦ x+integer` and `x↦1/x`-tail shift — the
   integer-part drift of `ψ(x)` absorbed (KHINCHIN.md L3 note: `CFDefs` tail
   lemmas; find the tail-shift invariance of `IsCFNormal` used for `xstar`).
3. GOAL of the B6 crux (L4): the schedule builds `xstar` so that for EACH image
   system `(q_i,r_i)`, the pullback intervals `ψ_i⁻¹(cylinder)` still capture a
   good density (L2 applied to `ψ_i(brick)` gives good mass, transported back).
Record the pinned L3 statements here before proving. L4 (schedule surgery,
`CFScheduleA.lean`) is the MODERATE-risk crux — do it after L3.
Faithfulness: after any work, re-`#print axioms
exists_absolutely_normal_cf_normal_khinchin` = trust triple (must stay locked).

---

# PENDING WORK — B5′ campaign

> **✅ COMPLETE (2026-08-24 — the whole B5′ expedition is PROVED, axiom-clean).**
> Both headlines `exists_absolutely_normal_cf_normal` (Tier 1 = Becher–Yuhjtman)
> and `exists_absolutely_normal_cf_normal_khinchin` (Tier 2 = + Khinchin-typical)
> are `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`). ZERO
> `sorry`/`admit` terms in `src/`; ZERO cited math axioms. All 10 headline
> theorems certified trust-triple this lap.
>
> This lap closed it in three steps: (1) `CFSchedule.lean` rewired to the
> summable-**family** refinement; (2) log-tail telescoping in `CFCorrect.lean`
> (`logTailMass`, `uSched_logTail_le`, `tailSched_logTail_le`,
> `xstar_logTail_prefix_bound`) + the crux `xstar_log_tail_uniform`, hence
> `xstar_khinchinTypical`; (3) route D′ — frozen defs relocated byte-identical to
> `KhinchinDefs.lean` to break the import cycle, headline discharged.
>
> **No open proof obligations remain.** Nice-to-have only: sweep stale "left
> `sorry` for the campaign" docstrings in a few CF modules (historical prose);
> the outward Track-A PR to ChampernowneNormality (needs host egress).

## Reflection — 2026-08-24 (deep reflection lap) 🧘

**Ground truth re-derived** (not taken from handoffs): `lake build` green (8750
jobs); `#print axioms exists_absolutely_normal_cf_normal` = trust triple (also
`xstar_cf_freq_tendsto`, `xstar_dary_freq_tendsto`, `pillai`); frozen headline
statements read faithfully vs source (khinchinK₀ tprod index alignment k↦k+1
verified via the in-file anchors; `KhinchinTypical`=geom-mean→K₀; `IsAbsolutelyNormal`
=full normality every base; `IsCFNormal`=window-freq→γ). Only two real `src/`
sorries: `Headline.lean:136` (Tier-2 headline) and `Khinchin.lean:527`
(`xstar_log_tail_uniform`, the crux). The rest are docstring mentions.

**DIRECTION CALL — CONTINUE route C′; the directive was STALE and is now fixed.**
The prior CURRENT DIRECTIVE still described the Chebyshev/variance bad-zone plan,
but the grind laps correctly pivoted to the simpler **Markov first-moment bound on
the nonnegative log-tail** and built the entire summable-family machinery
(`KhinchinBrick`, `KhinchinFamily`, `KhinchinRefineFamily`, `CFLogTail`) —
all axiom-clean. This is genuine forward motion, NOT a false summit: whole lemmas
close lap-over-lap (Lebesgue bridge → three-zone combine → refinement-family), the
crux keeps SHRINKING (whole log-average → one tail-mass bound → schedule wiring),
and this run's real design bug (level-tied cutoff `K_t→∞` can't transfer to a fixed
external `K`) was found AND fixed same-run via the fixed-cutoff summable family.
ROUTE VERDICT: **CONTINUE** — neither charter trigger fired (route uses
Markov+γ-mixing, explicitly Birkhoff-free; γ-mixing rate is proven geometric).

**KEEP doing**: the route C′ family graft; treating Tier 1 as banked/untouchable.

**STOP doing**: building MORE upstream Khinchin lemmas. That layer is COMPLETE
(handoff items 6–8 confirm `exists_good_avoiding_bad…_family` +
`exists_refinement_uniform_khinchin_family` are proved axiom-clean). Every further
lap that adds standalone machinery instead of WIRING is drift. The value is now
100% in the plumbing.

**HIGHEST-VALUE NEXT TARGET**: rewire `CFSchedule.lean` to the family refinement
(`tK := level`), then assemble `xstar_log_tail_uniform` from the schedule's family
payload. Reasoning: this is the route-DECISIVE test. The one genuinely uncertain
step is whether the per-stage family guarantee (each good block avoids all `j<t`
log zones) transfers to a **mid-stage prefix** of `xstar` — the exact analogue of
the CF/d-ary per-block→prefix-frequency transfer ALREADY solved via
`sched_dominance` + the `goodC`-telescope, so precedented and tractable, but the
last untested link. If it goes through, Tier 2 closes; if it walls, that wall is
the real obstacle to surface (and Tier 1 remains a complete standalone deliverable).
The crux's `∀K≥K₀` is handled by monotonicity of the nonnegative tail in `K`, so
controlling it at the single fixed cutoff `khinchinK j(ε)` suffices. Weaken
`xstar_log_tail_uniform` to `∃N,∀n≥N` — its only consumer works via
`Metric.tendsto_atTop`.

---

> **GRIND (2026-08-24 — value-count bridge PROVED; crux is now a pure
> tail-mass bound).** Landed three axiom-clean lemmas in `Khinchin.lean`:
> - `countOccurrences_singleton`: `countOccurrences [a] l = l.count a`.
> - `logTail_list_eq` (general list, by induction): for positive-digit `w`,
>   `(Σ_{x∈w} log x) − Σ_{a≤K} (w.count a)·log a = Σ_{x∈w} (if K<x then log x else 0)`.
> - `xstar_logTail_eq`: the difference INSIDE `xstar_log_tail_uniform` equals the
>   nonnegative empirical tail `Σ_{i<n} (if K < cfDigit xstar i then log(cfDigit
>   xstar i) else 0)`.
> **Consequence**: `xstar_log_tail_uniform` now reduces (via `xstar_logTail_eq`)
> to a pure **upper bound on the nonnegative empirical tail**: `∀ε>0 ∃K₀ ∀K≥K₀
> ∀n, (1/n)·Σ_{i<n, cfDigit xstar i>K} log(cfDigit xstar i) ≤ ε`. All the
> value-count/bookkeeping is discharged; what remains is exactly the schedule
> guarantee that each good block's large-digit log-mass is `≤ η·(block length)`,
> delivered by the Markov `logBadZone`. NEXT is unchanged (A′ first-moment
> integral → B′ bad zone → C′ union plumbing → D′ layering); the bridge means
> C′ can target the clean tail-mass form directly.

> **GRIND (2026-08-24 — route SIMPLIFIED to Markov; plumbing scoped).** Two
> route improvements that make `xstar_log_tail_uniform` markedly more tractable
> than the "variance/Chebyshev" framing:
>
> 1. **Markov, NOT Chebyshev — first moment suffices.** The tail
>    `Σ_{i<n, aᵢ>K} log aᵢ` is NONNEGATIVE and we only need an UPPER bound on it
>    (the `limsup ≤ log K₀` direction; `liminf ≥` is free from frequencies). So
>    the bad zone `logBadZone K n η := {x : Σ_{i<n, digit>K} log(digit) > η·n}`
>    (relative to the brick cylinder) is controlled by **Markov's inequality**:
>    `γ(logBadZone) ≤ (1/(η·n))·∫ tail dγ = (1/η)·Σ_{a>K} γ([a])·log a`, using
>    T-invariance + `integral_blockCount` (∫ blockCount(cfCylinder[a],n) dγ =
>    n·γ([a])) — **FIRST MOMENT ONLY**. No `Var(Σ log aᵢ)` bound, no covariance
>    double-sum, no L²-observable γ-mixing extension needed. `summable_gaussKuzmin_logsq`
>    (2nd moment) is therefore NOT on the critical path (still a correct lemma).
>    The `K`-selection input `Σ_{a>K} γ([a])·log a → 0` is now proved:
>    `gaussKuzmin_logtail_tendsto` (`Khinchin.lean`, axiom-clean).
> 2. **The general union lemma needs NO change.** `exists_mem_notMem_union_of_bounds`
>    (`TBrick.lean:244`) already takes TWO zones B₁,B₂ with `p+q<1/2`. Add the
>    Khinchin zone B₃ by **unioning it into B₂** (the d-ary group):
>    `vol(B₂∪B₃) ≤ ofReal(q+r)·vol0` by subadditivity, needing `p+q+r<1/2`. So
>    the only edits are: `exists_good_avoiding_bad` (union B₃ in, tighten the two
>    `<1/4` coeff thresholds so the three sum `<1/2` — e.g. `<1/6` each, larger
>    N/kmin), its `_of_large` corollary, `exists_refinement_uniform`, and the
>    schedule/`xstar` rederivation carrying the extra guarantee. All ADDITIVE
>    (new hypotheses + new conclusion conjunct); Tier-1 decls untouched.
>
> **CONCRETE NEXT (in order):**
> - (A′) First-moment integral: `∫ x, (Σ_{i<n} if cfDigit x i > K then
>   log(cfDigit x i) else 0) dγ = n·Σ_{a>K} γ([a])·log a`. Express the tail
>   observable via `blockCount (cfCylinder [a])` summed over `a>K` with `log a`
>   weights; interchange ∫ with the (Tonelli, nonneg) sum; apply
>   `integral_blockCount` per `a`. NEW file (`CFLogTail.lean`), no TBrick edit.
> - (B′) `logBadZone` def + Markov measure bound `≤ (1/η)Σ_{a>K}γ([a])log a`
>   (via `MeasureTheory.mul_meas_ge_le_integral`-style Markov on the nonneg tail).
> - (C′) Union B₃ into `exists_good_avoiding_bad`; tighten coeffs; thread through
>   `exists_refinement_uniform` + schedule; discharge `xstar_log_tail_uniform`.
> - (D′) Layering refactor: move frozen `KhinchinTypical`/`khinchinK₀` defs to an
>   upstream module so `Headline.lean:134` can close with `xstar_khinchinTypical`.

> **GRIND (2026-08-24, same lap follow-on — REDUCTION (C) COMPLETE, crux
> isolated to ONE schedule lemma).** The entire Tier-2 headline now provably
> rests on a single, precisely-stated lemma. Landed (all in `Khinchin.lean`):
> - `gaussKuzmin_logsum_hasSum` / `gaussKuzmin_logsum_tendsto` (axiom-clean):
>   the assembly's **target limit value** `Σ_a γ([a])·log a = log K₀` (HasSum +
>   `Icc 1 K` partial sums `→ log K₀`). Key identity: `γ([a])·log a` = the term
>   of `khinchinK₀`'s series (logb/log factors swap), reused verbatim.
> - `xstar_log_digit_avg_tendsto` — **PROVED** via a clean `3ε` interchange over
>   `xstar_log_digit_avg_truncated_tendsto` (fixed-K, proved) +
>   `gaussKuzmin_logsum_tendsto` (K→∞, proved) + the tail lemma. The value-count
>   identity is ABSORBED into the tail lemma (stated with `abs`, so no separate
>   nonneg/identity lemma needed).
> - `xstar_khinchinTypical : KhinchinTypical xstar` — **PROVED** via
>   `khinchinTypical_iff_log_tendsto` (digit positivity from `one_le_cfDigit`).
> `#print axioms` of both: `[propext, sorryAx, Classical.choice, Quot.sound]` —
> the ONLY non-trust-triple dependency is `sorryAx`, sourced entirely from:
>
> **THE SOLE REMAINING TIER-2 CRUX** — `xstar_log_tail_uniform` (disclosed
> `sorry`, `Khinchin.lean`): `∀ε>0 ∃K₀ ∀K≥K₀ ∀n, |(1/n)Σ_{i<n}log aᵢ −
> (1/n)Σ_{a≤K}count[a]·log a| ≤ ε`. This is the uniform log-tail control the
> schedule must deliver — exactly what the W6 log-concentration bad zone
> provides (variance bound via γ-mixing, moment input `summable_gaussKuzmin_logsq`).
>
> **NEXT**: the construction work, steps (A)+(B) from the review entry below —
> (A) `Var(Σ_{i<n} log aᵢ) ≤ C·n` under γ-mixing (adapt `CFBlockFreq`'s
> covariance machinery to the L² observable `log a₁`); (B) `logBadZone` +
> Chebyshev measure bound + additive union-bound wrapper; then instantiate at
> `xstar`'s schedule to discharge `xstar_log_tail_uniform`. Also a mechanical
> layering refactor is needed to close `Headline.lean:134` itself: the frozen
> `KhinchinTypical`/`khinchinK₀` defs live in `Headline.lean` (which `Khinchin.lean`
> imports), so the headline `sorry` can only be closed after moving those defs
> to an upstream module (verbatim — preserves the frozen statement) so the
> assembly + `xstar_khinchinTypical` become upstream of the headline.

> **REVIEW LAP (2026-08-24 — route DECISION + moment seed proved).** The last
> three laps (fc801ba/17dc2c9/7d6740f, all pure route-analysis) converged on
> "step-2 crux is operator-gated, need Trevor to authorize a schedule touch —
> stop." That is a **false stop**: this is an autonomous run, there is no
> operator, and the review lap owns exactly this call. DECISION (now binding in
> `DIRECTION.md`):
>
> 1. **The route is settled** — the diagnosis of the last laps is CORRECT and
>    ratified: frequencies + the `goodC` total-mass bound provably cannot give
>    the uniform tail control (`limsup(1/n)Σ_{aᵢ>K} log aᵢ ≤ goodC−log K₀ > 0`;
>    plus the frequencies-only counterexample). The ergodic route is a forbidden
>    import. So the ONLY route is the original `KHINCHIN.md` W6 log-concentration
>    bad zone. The `44fb8bb`/`e018429` "goodC suffices, no re-plumb" insight is
>    formally **REFUTED** (docstring in `Khinchin.lean` step-2 block records it).
> 2. **The schedule fence is RELAXED** — additive extension of `TBrick.lean`/
>    `TBrickRefine.lean`/`CFSchedule.lean` for the W6 graft is authorized. The old
>    blanket "don't touch the schedule" was over-broad; its real purpose is
>    protecting locked Tier-1, which an additive lemma cannot threaten (the JUDGE
>    froze witness-existence form precisely to permit a W6 rebuild). Hard
>    invariant: never edit/weaken an existing Tier-1 decl or frozen statement;
>    after any schedule edit re-run `#print axioms exists_absolutely_normal_cf_normal`
>    and confirm it stays the trust triple.
> 3. **Proof landed this lap**: `summable_gaussKuzmin_logsq` (`Khinchin.lean`,
>    axiom-clean) — the moment condition `E[(log a₁)²] = Σₐ γ([a])·(log a)² < ∞`
>    that the Chebyshev/variance bad-zone bound needs. Comparison with
>    `1/(k+1)^{3/2}` via `log(1+x)≤x` and `(log(k+1))²≤16√(k+1)`.
>
> **NEXT ATTACK (in order; start analytic, defer the invasive plumbing):**
> - (A) **Variance bound** `Var(Σ_{i<n} log aᵢ) ≤ C·n` under γ-mixing — adapt
>   `CFBlockFreq.lean`'s `variance_blockCount_le`/covariance machinery from a
>   cylinder-indicator observable to the unbounded L² observable `log a₁`. This
>   is the real new estimate; `summable_gaussKuzmin_logsq` is its moment input.
>   The γ-mixing covariance bound must be checked to hold for L² (not just
>   bounded) observables — likely the one genuine subtlety. NEW file
>   (`CFLogMoment.lean` or similar), no TBrick edit.
> - (B) **`logBadZone` + Chebyshev measure bound** `≤ C/(η²n)`; then the additive
>   union-bound wrapper (`exists_good_avoiding_bad_khinchin`), re-balancing the
>   coefficient budget in `exists_mem_notMem_union_of_bounds` from 2 zones to 3
>   (each `<1/6`, or keep `<1/4`+`<1/4` and add the log zone with the surplus of
>   a stronger half-mass — check the exact threshold the general lemma needs).
> - (C) **Elementary reduction (parallelizable, `Khinchin.lean`)**: reduce
>   `xstar_log_digit_avg_tendsto` to a single clean tail-control lemma
>   `xstar_log_tail_uniform : ∀ε>0, ∃K, ∀n, (1/n)Σ_{aᵢ>K} log aᵢ ≤ ε` via the 3ε
>   argument over `xstar_log_digit_avg_truncated_tendsto` (done) + the
>   value-count identity `Σ_{i<n} log aᵢ = Σ_a count[a]·log a`. This isolates
>   the schedule-dependent piece (the tail-control, delivered by A+B) from the
>   elementary analysis (wireable now).

> **ANALYSIS LAP (2026-08-24, part 2, no code — construction survey).**
> Traced the previous entry's option (1) (dig into `kminFn_spec`) down to
> the actual selection mechanism: `TBrick.exists_refinement_uniform`
> (`TBrickRefine.lean:432`) builds the extension word `u` by picking a
> point `x` that simultaneously **avoids a union of finitely many small-
> measure "bad zones"** — `exists_good_avoiding_bad_of_large` unions one
> `cfBadZone B.w v n δ` per `v ∈ F` (the frequency-deviation zones) plus
> the d-ary `daryBadZoneWide` zones, then a measure/counting argument
> (`goodExtSet`, the Markov good-length machinery) shows a point avoiding
> ALL of them exists. **The per-`v` error bound is a DIRECT consequence of
> which bad zones got unioned in** — `F = wordFamily t` only, so there is
> no log-weighted zone to inherit; option (1) as "just read harder" is a
> dead end confirmed — the existing construction genuinely does not carry
> the needed fact implicitly.
>
> **Concrete, additive next step (supersedes both prior options)**: this
> union-bound architecture is EXTENSIBLE without touching any frozen Tier-1
> statement — add ONE more bad zone to the union, a `logBadZone B.w n η`
> analogous to `cfBadZone`, defined so avoiding it bounds `|Σ_{i<n}
> log(digit_i) - n·log khinchinK₀| < η·n` (a large-deviation / concentration
> statement for the log-digit sum under `gaussMeasure`, needing an
> exponential-moment / Chernoff-type bound — `Σ_a γ([a])·a^θ < ∞` for small
> `θ` would give it via Markov's inequality on `exp(θ·Σlog a_i)`). Package
> this as a NEW theorem `TBrick.exists_refinement_uniform_khinchin` (or a
> `khinchinBadZone` variant of the existing union-bound lemma) that returns
> everything `exists_refinement_uniform` does PLUS this log-average
> guarantee — purely additive, doesn't reshape `IsAbsolutelyNormal`,
> `IsCFNormal`, `khinchinK₀`, or any Tier-1 theorem statement, so it does
> NOT violate `DIRECTION.md`'s "forbidden drift" (that clause bars
> RE-ATTACKING/reshaping Tier 1, not building a new corollary on top of its
> existing machinery). This is a genuine new measure-theory lemma (the
> concentration bound), not mechanical assembly — realistically the size of
> a fresh work package (comparable to W1-W6 in `KHINCHIN.md`), likely
> multiple laps just for the concentration estimate before even touching
> the union-bound plumbing. Record as the leading candidate; if the
> concentration estimate itself proves intractable, THAT is the point to
> escalate to an altitude/review lap for a route call, not before.

> **ANALYSIS LAP (2026-08-24, no code — route-refutation only).** Chased
> route (a) from the previous entry (escaping-mass argument from
> `uSched_spec`'s existing frequency bound) to a concrete numeric
> conclusion: **it does NOT work**, and the failure is quantitatively
> precise, not just a vague gap. Worked out by hand (not yet formalized):
> `uSched_spec`'s per-digit-value error bound is `|count[a] - γ([a])·n_s| <
> schedEps(t_{s+1})·n_s + 1` for every `a ≤ t_{s+1}`, i.e. `schedEps(t)·n +
> 1` with `schedEps(t) = 1/(t+1)`, **uniform in `a`** (not shrinking as `a`
> grows toward `t`). Summing the log-weighted error over `a = 1..t`:
> `Σ_{a≤t} |err_a|·log a ≤ (schedEps(t)·n + 1)·Σ_{a≤t} log a ≈ (n/t)·(t log
> t) = n·log t` (Stirling, `log(t!) ~ t log t`). As a FRACTION of the block
> length `n`, this error is `~ log t_{s+1} → ∞` as `s → ∞` (since
> `t_{s+1} → ∞` is required for Tier 1's own base-coverage) — the error
> does NOT vanish relative to `n`, for ANY choice of cutoff (fixed or
> growing with `s`). This kills the naive combination outright, not just
> weakly.
>
> **Also checked**: `goodC` (the `wSched_log_sum_le` total-mass cap) is an
> unrelated Markov constant from `half_mass_long_extensions`
> (`exists_C_half_le_volume_goodExtSet.choose`, `CFSchedule.lean:108`) —
> it has NO known relation to `khinchinK₀`/`log khinchinK₀` (not proven
> `= log khinchinK₀`, almost certainly strictly larger with real slack), so
> `Σ log(digit) ≤ goodC·n` cannot by itself pin the limit to exactly
> `log khinchinK₀` even before worrying about tails.
>
> **Conclusion — route-decisive**: the Tier-1 schedule's EXPOSED interface
> (`uSched_spec`/`nFn_spec`'s packaged frequency + total-mass facts) does
> not carry enough quantitative information for the Khinchin log-average
> limit; the per-word error bound was built for FIXED-length pattern
> frequency (Tier 1's `IsCFNormal`, no log-weighting) and is provably too
> weak once digit magnitude enters as a weight. Two live options for the
> NEXT lap, in order of preference:
> (1) **Dig into `kminFn_spec` / the underlying Lemma-13 refinement
>     construction** (`TBrickRefine.lean`) for a genuinely finer,
>     log-weighted quantitative estimate — e.g. does the actual
>     construction (not just its packaged `nFn_spec` corollary) support a
>     bound like `Σ_{a≤t} err_a·log a = o(n)` via cancellation the crude
>     triangle-inequality packaging discards? This is READING/extending
>     Tier-1 internals for a NEW corollary, not modifying the frozen
>     schedule or its statements — allowed under `DIRECTION.md`'s "forbidden
>     drift" clause (which bars re-attacking/reshaping Tier 1, not reading
>     it for a new Tier-2 fact). Needs real investment (Lemma-13's actual
>     proof, likely `TBrickRefine.lean`'s badBlocks/daryCell combinatorics)
>     — budget a full lap just to understand what's provable there before
>     attempting a new lemma.
> (2) If (1) turns up nothing usable: the honest conclusion is Tier 2
>     genuinely needs a schedule re-plumb (the ORIGINAL W6 assessment this
>     campaign's `44fb8bb` route-insight had set aside) — but that is a
>     `DIRECTION.md`-level call (touches locked Tier-1 machinery), not a
>     grind-lap decision; flag for an altitude/review lap rather than
>     unilaterally reopening the schedule.
> Do NOT retry route (a) as stated (fixed-or-growing cutoff `K` against the
> existing frequency bound) — it is refuted above with an explicit
> divergent-error computation, not merely "not yet tried."

> **GRIND LAP (2026-08-24, `76e042e`).** Continued the step-2 assembly
> (log-average crux). Two sub-lemmas landed, both axiom-clean, no `sorry`:
> `xstar_log_digit_avg_truncated_tendsto` (`Khinchin.lean`) — the `≤ K`
> finite-truncation slice of the empirical log-digit average converges to
> the matching finite Gauss–Kuzmin sum (direct from `xstar_cf_freq_tendsto`
> + `tendsto_finsetSum`); `getElem_le_cfK` (`CFCylinder.lean`) — every digit
> in a genuine word is `≤` the word's continuant.
>
> **Route-scoping insight this lap (important, changes the difficulty
> picture)**: chased whether `wSched_log_sum_le`'s total-mass bound
> (`Σ log(digit) ≤ goodC·n`) alone suffices for the K→∞ tail-vanishing that
> `xstar_log_digit_avg_tendsto` needs. It does **not**, obviously — a bounded
> total doesn't imply the mass concentrated on large digits shrinks as `K`
> grows; that needs a genuine per-magnitude decomposition. Checked whether
> `getElem_le_cfK` + `uSched_spec`'s `cfK(uSched s) ≤ exp(goodC·n_s)` gives
> that decomposition: it gives a per-block digit CAP `exp(goodC·n_s)`, but
> that cap is far LOOSER than the block's frequency-control threshold
> `t_{s+1}` (recall `t² < nFn t = n_s`, i.e. `t_{s+1} < √(n_s)`, while the
> continuant cap is exponential in `n_s`) — so `uSched_spec`'s per-word
> frequency bound (4th clause, only proven `∀ v ∈ wordFamily t_{s+1}`, i.e.
> digits `≤ t_{s+1}`) does NOT cover digits between `t_{s+1}` and
> `exp(goodC·n_s)`, which is exactly where "escaping mass" could hide.
> **This is the precise open question**, sharper than the handoff's vague
> "Markov/Chebyshev" framing: either (a) find a genuine escaping-mass bound
> — e.g. show the CONTRIBUTION of digits `> t_{s+1}` to the block's log-sum
> is itself `o(n_s)` (not just capped by the loose exponential bound), using
> `uSched_spec`'s frequency-control on the complementary low digits to
> squeeze the high-digit contribution via the SAME total (`wSched_log_sum_le`
> minus the low-digit part, itself estimated via the frequency bound) — this
> looks tractable and is the next thing to try; or (b) conclude the current
> schedule construction genuinely lacks the control needed and a tighter
> digit-cap re-plumb (the ORIGINAL W6 assessment, which this campaign's
> `44fb8bb`/`e018429` route insight had set aside) is unavoidable after all.
> Try (a) first — do NOT re-open the schedule construction (route (b))
> without exhausting (a); the frequency-bound-on-the-complement trick is a
> standard measure-theory move (bound the tail of a nonneg sum by
> total-minus-known-part) and hasn't been attempted yet.

> **GRIND LAP (2026-08-24, `42ec6a7`).** ✅ **Gauss-Kuzmin single-digit law
> PROVED** (step 1 of HANDOFF-2026-08-24-0123.md's Tier-2 NEXT list):
> `gaussMeasure_digit_cylinder` (`CFCylinder.lean`) — closed form
> `γ(cfCylinder [a]) = logb 2 (1 + 1/(a(a+2)))` for `a ≥ 1`, matching
> `khinchinK₀`'s tprod term exactly (`a(a+2)+1 = (a+1)²`), axiom-clean.
> Route: `gaussMeasure_cfCylinder` mirrors `volume_cfCylinder`'s
> `uIcc`/`uIoo` squeeze verbatim but for `gaussMeasure` — endpoints and the
> rational range are `gaussMeasure`-null via
> `MeasureTheory.withDensity_absolutelyContinuous` (`gaussMeasure ≪ volume`,
> so every Lebesgue-null set is `gaussMeasure`-null; no need for the
> one-directional `gaussMeasure_le_volume`/`volume_le_gaussMeasure` bounds
> the original plan cited). **Refactor gotcha**: `gaussMeasure_Ioo` had to
> move from `CFDigitLaw.lean` to `CFDefs.lean` (right after `gaussMeasure`'s
> def) — it's pure real analysis on the definition with no `cfCylinder`
> dependency, but `CFCylinder.lean` needed it and `CFDigitLaw.lean` imports
> `CFCylinder.lean` (not the reverse), so leaving it in place would have been
> circular. **Lean gotcha**: multi-line `calc` first-step terms
> (`calc ENNReal.ofReal\n  (long arg)\n  = ... := ...`) mis-parse in this pin
> — the continuation line reads as a new command, producing bogus "expected
> ℝ got ENNReal" / "left-hand side is true : Bool" errors far from the real
> bug. Fix: `set T := <the long RHS term>` once, then write the whole `calc`
> in terms of the short name `T` (no multi-line calc heads at all).
>
> **NEXT (step 2, the genuine remaining crux)**: assemble
> `xstar_cf_freq_tendsto [a]` (single-digit frequency, already proved,
> `CFCorrect.lean`) with `gaussMeasure_digit_cylinder`'s closed form and
> `wSched_log_sum_le`'s uniform tail bound (`CFCorrect.lean`, from the
> `goodC` schedule payload) into
> `Tendsto (fun n => (1/n)·Σ_{i<n} log(cfDigit xstar i)) atTop (nhds (log
> khinchinK₀))`. This is a dominated-convergence-style interchange: for each
> `ε`, truncate at digit `K` (using `Σ_a p_a·log a` convergence, i.e.
> `khinchinK₀_summable_log` in `Khinchin.lean`, to bound the tail
> `Σ_{a>K} p_a·log a`), get finite-truncation convergence of the empirical
> log-average from `xstar_cf_freq_tendsto` on each `a ≤ K`, and bound the
> empirical tail `(1/n)Σ_{i<n, cfDigit xstar i > K} log(cfDigit xstar i)`
> using `wSched_log_sum_le`'s `≤ goodC·n` mass bound plus a Chebyshev-style
> "few large digits" argument (or a cruder direct bound if the `goodC`
> bound alone suffices — check whether `uSched_log_sum_le`'s per-stage
> bound already gives what's needed without further partitioning). Likely
> the hardest remaining step; budget 2-3+ laps. Then
> `khinchinTypical_iff_log_tendsto` (`Khinchin.lean`, already proved)
> converts this limit to `KhinchinTypical xstar`, closing
> `exists_absolutely_normal_cf_normal_khinchin` (`Headline.lean:136`, the
> ONLY remaining `sorry` in `src/`).

> **GRIND LAP (2026-08-26, `44fb8bb`).** ✅ **TIER 1 LOCKED** —
> `exists_absolutely_normal_cf_normal` proved, axiom-clean (`b3bc2c4`; see
> HANDOFF-2026-08-24-0057.md for the full route). ✅ **Khinchin (Tier 2) seed
> landed**: `prod_le_cfK` (`CFDigitLaw.lean`, the missing continuant lower
> bound `∏aᵢ ≤ K(a₁…aₙ)`) + `uSched_log_sum_le` (`CFCorrect.lean`): each
> appended schedule block's total `log`-digit mass is `≤ goodC·(block
> length)`. **Route insight this lap**: KHINCHIN.md's W6 assessment expected
> a digit-cap re-plumb of the schedule for uniform-integrability control —
> but the existing `cfK(uSched s) ≤ exp(goodC·n)` payload (already proved for
> Tier 1) directly bounds the average `log`-digit per stage via
> `prod_le_cfK`, with **no construction change needed**. This significantly
> de-risks Tier 2: `xstar`'s *existing* schedule may already be
> Khinchin-typical.
>
> **NEXT (Tier 2, `Headline.lean:134`, `exists_absolutely_normal_cf_normal_khinchin`)**:
> assemble `uSched_log_sum_le` into the actual geometric-mean limit
> `KhinchinTypical xstar`:
> 1. Sum `uSched_log_sum_le` over stages `0..s-1` to bound `(wSched
>    s).map log |>.sum` (telescoping `nFn`/length identities already exist,
>    cf. `wSched_length_succ`) — gives an UPPER bound on the log-digit sum at
>    stage boundaries, matching the schedule's word length.
> 2. Need the MATCHING lower/limit bound: use `xstar_cf_freq_tendsto`
>    (already proved) to get, for every digit value `k` (or every `v = [k]`
>    cylinder), the frequency of digit `k` in the length-`p` prefix `→
>    γ(cfCylinder [k])` = the Gauss–Kuzmin law. The target sum `Σ log(cfDigit
>    xstar i)` should then match `p · Σ_k γ([k])·log k = p · log K₀` in the
>    limit, PROVIDED a uniform-integrability interchange (dominated/bounded
>    convergence style, using the `goodC` bound to truncate the tail) can be
>    justified — this interchange (finite-pattern convergence + bounded tail
>    ⇒ full log-average convergence) is now THE remaining crux, not a
>    digit-cap graft. Likely needs: (a) a truncation argument bounding
>    `Σ_{k>K} γ([k])·log k` uniformly small (from `Σ log k / k²  < ∞`,
>    `CFDigitLaw.lean`'s existing summability work may be reusable), (b) an
>    ε/δ argument combining finite-truncation convergence (from CF-normality)
>    with the tail bound (from `uSched_log_sum_le`/`goodC`).
> 3. Convert the log-average limit to `KhinchinTypical`'s geometric-mean form
>    (`(∏...)^(1/n) → K₀` ⟺ `(1/n)Σlog → log K₀`, via `Real.exp`/`Real.log`
>    continuity — should be short once the log-average limit is in hand).
> Prior Tier-1 material (Pillai, d-ary chain, CF normality, measure balance,
> schedule/Lemma-13) is CLOSED — do not reopen; see DIRECTION.md.

> **GRIND LAP (2026-08-26, `e7705ee`).** ✅ **PILLAI'S THEOREM PROVED** —
> `Pillai.lean` is now **sorry-free**. Chain landed this lap (all axiom-clean):
> `windowCount_eq_sum_phaseCount` → `phaseOccCount_{tendsto_atTop,div_tendsto}` →
> `phaseWindowFreq_div_N_tendsto` → `sum_{nonStrad,strad}_..._tendsto` →
> `windowCount_div_sandwich` → **`windowFreq_tendsto`** (THE double-limit crux,
> block freq → b^{-L} via ε-in-r squeeze) → **`pillai`** (`∀ r≥1 simple normal at
> b^r ⇒ IsNormalSequence b (digitOf b y)`; bridge via `countOccurrences_range_map`
> + `MatchesAt ↔ ofFn-window`). See HANDOFF-2026-08-24-0052.md for the full route
> + gotchas.
>
> **NEXT = Tier-1 headline conjunction** (`Headline.lean:93`, ONLY classical
> wiring): `∃ x, IsAbsolutelyNormal x ∧ IsCFNormal x`, witness `xstar`.
> (1) `IsAbsolutelyNormal xstar` = `∀ b≥2, IsNormal b xstar` = pillai (y :=
> Int.fract xstar) fed by `xstar_dary_freq_tendsto (b^r)`; FIRST check the exact
> form of `xstar_dary_freq_tendsto` vs pillai's `hsn`, and `digitOf d xstar =
> digitOf d (Int.fract xstar)`. (2) `IsCFNormal xstar` = wrapper of
> `xstar_cf_freq_tendsto` (JUDGE: not new math). (3) `refine ⟨xstar, ?_, ?_⟩`.
> Tier 2 (`:100`, Khinchin/W6) stays `sorry` — fenced.

> **REVIEW LAP (2026-08-24).** ✅ **`windowCount_eq_sum_phaseCount` PROVED**
> (axiom-clean) — the `Q`-scale↔`N`-scale phase-count identity, closing last
> lap's disclosed `sorry`. Winning move on the `r*(i/r)` vs `(i/r)*r` omega-atom
> trap: `Finset.card_nbij' (fun i => i/r) (fun q => r*q+s)`, anchoring EVERY
> decomposition on `Nat.div_add_mod i r` (canonical `r*(i/r)`); the ONLY place a
> `(i/r)*r` appears is right after `Nat.le_div_iff_mul_le`, where a single
> `rw [Nat.mul_comm]` normalizes it back BEFORE `omega`. Mod dir:
> `Nat.add_comm (r*q) s` → `Nat.add_mul_mod_self_left` + `Nat.mod_eq_of_lt hsr`.
> Div dir: `Nat.mul_add_div hrpos` + `Nat.div_eq_of_lt hsr`. (omega never has to
> reconcile the two factor orders — the rewrite does it first.)
>
> **NEXT (the new crux — the double-limit assembly)**: Pillai's phase→block
> frequency limit. `freq_w(N) = windowCount/N`. Route:
> (a) `windowCount_eq_sum_phaseCount / N = Σ_{s<r} phaseCount_s(N)/N`;
> (b) non-straddling `s ≤ r−L`: `phaseCount_s(N)/N =
>     (phaseCount_s/phaseOccCount_s)·(phaseOccCount_s/N)`; factor 1 → `b^{-L}` by
>     `phaseWindowFreq_tendsto` (a `Q→∞` limit — needs `phaseOccCount r L s N →∞`
>     as `N→∞`, then `Filter.Tendsto.comp`); factor 2 `phaseOccCount r L s N / N
>     → 1/r` (since `phaseOccCount ≈ (N−s−L)/r`);
> (c) straddling `s` (`r < s+L`, `L−1` of them by `card_straddling_phases`):
>     bound each `phaseCount_s(N)/N ≤ phaseOccCount/N → 1/r`, total ≤ `(L−1)/r`;
> (d) sum finite phases; then `r→∞` (ε-manage via `Metric.tendsto_atTop`: pick
>     `r` with `(L−1)/r < ε/2` and `|((r−L+1)/r − 1)·b^{-L}| < ε/2`, then `N`
>     large). Simpler than `xstar_dary_freq_tendsto`'s metric proof — no schedule.
>     Decompose into named sub-`sorry`s in `Pillai.lean` if not one lap.

> **LATEST LAP (2026-08-25/26, `674ff52`).** Pillai's theorem build-out,
> continuing from the digit-power foundation (`b537edd`). New in
> `Pillai.lean`, all axiom-clean:
> - `digitOf_pow_digitAt`: atomic single-digit phase correspondence.
> - `blockNatVal_slice`: pure list/nat lemma generalizing `blockNatVal_digit`
>   (L=1) to an arbitrary L-digit sub-block slice.
> - `digitOf_pow_slice_eq_blockNatVal`: the non-straddling window/slice
>   correspondence — a length-L window of y's base-b digits at phase s
>   equals w iff c_q's (=digitOf(b^r) y q) shifted+masked value equals
>   blockNatVal b w. This is the combinatorial core connecting simple
>   normality at b^r to block frequency at base b.
> - `card_matchingValues`: among c<b^r, exactly b^(r-L) have a fixed L-digit
>   slice value — proved via explicit bijection c ↔ (c/D/b^L, c%D).
> **Next**: combine `digitOf_pow_slice_eq_blockNatVal` + `card_matchingValues`
> into the phase-s window-frequency limit (via `tendsto_finsetSum` over the
> `b^(r-L)`-element matching set, using simple normality at base b^r), then
> the straddling-density bound (O(L/r)→0) and the double limit (r→∞ then
> N→∞) assembling the full Pillai theorem. See docstring route in
> `Pillai.lean`. GOTCHA: `List.getElem_ofFn` + `congr 1` on Fin-coerced
> indices needs an explicit `simp only [Fin.val_mk]` before `congr 1` —
> omitting it (even though the linter flags it "unused" in some
> elaborations) causes a nondeterministic omega failure on rebuild; keep it
> despite the lint warning. Also: `Nat.add_mul_div_right`/
> `Nat.add_mul_mod_self_right` need the term in `x + y*z` form with the
> VARIABLE first and the fixed multiplier as the LAST factor before the
> modulus/divisor — commute explicitly before rw, don't rely on `_left`
> variants when the target's factor order doesn't match.

> **CURRENT STATE (2026-08-25 grind lap, `e832d1d`).** Everything below the
> "── ARCHIVE ──" divider is the W3/W4/W5-input history, kept for the proven-lemma
> record but SUPERSEDED. Live state:
>
> - ✅ W1–W4 done. ✅ **W5 core done**: B–Y Lemma 13 (`TBrick.exists_refinement`),
>   THE SCHEDULE (`CFSchedule`), limit point `xstar` (irrational, in every
>   scheduled cylinder), **CF normality of `xstar`** (`xstar_cf_freq_tendsto`).
>   All axiom-clean.
> - ✅ **(c) THE d-ary `m`-growth CRUX IS CLOSED** (`9d8f265`): the interior
>   ratio `k_{s+1}/(m_d(s)−m_d(s₀)) → 0` is proved
>   (`tendsto_gain_div_mSched_sub`). This was the only genuinely-new-math
>   obligation for Tier 1.
> - ✅ **(d) THE d-ary CHAIN IS CLOSED** (`e832d1d`): `xstar_dary_freq_tendsto`
>   is proved axiom-clean — for every base `d ≥ 2` and digit `c < d`, the
>   frequency of `c` among the first `p` base-`d` digits of `xstar` tends to
>   `1/d`. This is **simple normality of `xstar` in every base simultaneously**,
>   the FIRST machine-checked formalization of the Becher–Yuhjtman d-ary
>   result. Built from: `dBlock`/`dBlock_spec` (per-stage good block via
>   choice), `dTailList` (tail decomposition), `dTailList_hasDiscLt` (chain),
>   `dFixedPrefix_append_dTailList_hasDiscLt` (boundary),
>   `dBlock_short_of_dTailList` + `dTailList_append_take_hasDiscLt` (interior),
>   `exists_mSched_stage` (locator), `count_map_val_eq` (Fin-d → ℕ digit count
>   bridge), assembled via a 3-way `List.range` split matched to the real
>   digit sequence.
> - 🔨 **Frontier = Tier 1 completion** (item 3 below): only classical labor
>   and statement-staging remain — no more genuinely-open math for Tier 1.
>   - **Pillai**: simple-normal-to-all-`b^k` ⇒ normal-to-`b`. NOT in
>     mathlib/repo — check `Sandwich`/`Counting`/`Wall` for reusable
>     window-frequency pieces before formalizing from scratch (classical,
>     self-contained; combines `xstar_dary_freq_tendsto` at every base `d`
>     with a block-frequency argument reducing general blocks to single-digit
>     frequencies at higher bases).
>   - **Headline conjunction**: stage `(∀ b≥2, IsNormal b xstar) ∧
>     CF-normal xstar` for JUDGE — note `Headline.lean` already has
>     witness-existence-form frozen statements
>     (`exists_absolutely_normal_cf_normal` etc.) with two `sorry`s (lines
>     91, 98) waiting for exactly this route to discharge them.
>   - `IsCFNormal`'s wrapper from `xstar_cf_freq_tendsto` and
>     `IsAbsolutelyNormal`'s wrapper from `xstar_dary_freq_tendsto`+Pillai
>     should both be short once Pillai lands.
>
> ## Attack path (hardest-first) — mirrors DIRECTION CURRENT DIRECTIVE
>
> 1. **(c) THE CRUX — the `m`-growth estimate** (interior condition; the only
>    genuinely-new-math left). Need: `k_{s+1}(d) ≤ ε·(m_d(s) − m_d(s₀))`
>    eventually. Route (source-verified): numerator `d^{k} ≤ 32d·cfK(u)²`
>    (good-length upper bound + brick containment); denominator
>    `Σ k_j ≳ (log2/(4 log d))·(L_s − L_{s₀})` via `two_pow_le_cfK`
>    (`cfK ≥ 2^{(n−1)/2}`, proved); ratio ≲ `goodC·n_{s+1}/L_s → 0` by
>    `sched_dominance`. It is the exact analogue of the CF interior condition
>    already closed by the schedule dominance — high confidence it closes.
>    - ✅ **FOUNDATION LANDED** (2026-08-23, `dpow_mSched_bracket`, axiom-clean):
>      per-stage bracket `cfK(wSched s)²/(2d) ≤ d^{mSched s d} ≤ 4·cfK(wSched s)²`,
>      straight from the brick ratio field + `≤2`-cell containment. Dividing the
>      bracket at `s+1` by the bracket at `s` (with `cfK_append_le` /
>      `cfK_mul_le_append`, both in `CFCylinder`) gives the per-stage
>      `cfK(uSched s)²/(8d) ≤ d^{k_{s+1}} ≤ 32d·cfK(uSched s)²`.
>    - ✅ **(c1) LANDED** (2026-08-23, `dpow_gain_bracket` + `uSched_pos`,
>      axiom-clean): per-stage gain, cleared/division-free form —
>      `cfK(uSched s)² ≤ 8d·d^k` and `d^k ≤ 32d·cfK(uSched s)²` where
>      `k = mSched(s+1)d − mSched s d`. Proof = quotient of `dpow_mSched_bracket`
>      at `s+1` over `s`, with `cfK_append_le`/`cfK_mul_le_append` along
>      `wSched_succ`. (Takes `hk : mSched(s+1)d = mSched s d + k` — supplied by
>      `xstar_dary_step`.)
>    - ✅ **(c2) LANDED** (2026-08-23, `log_gain_bracket`, axiom-clean): log of
>      (c1), division-free `k·log d` form —
>      `2 log cfK(u_s) − log(8d) ≤ k·log d ≤ 2 log cfK(u_s) + log(32d)`. Via
>      `Real.log_le_log`/`Real.log_pow`/`Real.log_mul`.
>    - ✅ **(c3a) LANDED** (`gain_le`, axiom-clean): numerator —
>      `k·log d ≤ 2·goodC·nFn(tSched(s+1)) + log(32d)`, via `uSched_spec`'s
>      good-length bound `cfK(uSched s) ≤ exp(goodC·nFn(tSched(s+1)))` + (c2).
>    - ✅ **(c3b) LANDED** (`le_mSched_mul_log`, axiom-clean): denominator
>      building block — `m_d(s)·log d ≥ 2·⌊L_s/2⌋·log2 − log(2d)` where
>      `L_s = |wSched s|`, via the bracket lower half + `two_pow_le_cfK` on
>      `wSched s`. (So `m_d(s) ≳ (log2/log d)·L_s`.)
>    - NEXT: **(c4) close the interior ratio → 0**. Assemble: for fixed `d, ε`,
>      ∃ s₁, ∀ s ≥ s₁, `(mSched(s+1)d − mSched s d) < ε·(mSched s d − mSched s₀ d)`.
>      Numerator ≤ `(2goodC·nFn(tSched(s+1)) + log32d)/log d` (c3a). Denominator
>      ≥ `(2⌊L_s/2⌋log2 − log2d)/log d − mSched s₀ d` (c3b), and `L_s → ∞`
>      (`sched_length_mono`/`wSched_length_ge`). Ratio ≲ `2goodC·n_{s+1}/(log2·L_s)`;
>      `n_{s+1}/L_s → 0` by `sched_dominance` (`t·nFn t ≤ L`) since `t → ∞`
>      (`sched_t_tendsto`). This is the `hshort` feeding `hasDiscLt_append_take`.
>      Then (d) the d-ary chain (mirror `xstar_cf_freq_tendsto`).
> 2. **(d) d-ary chain → `xstar_dary_freq_tendsto`**: TRANSCRIBE the proven
>    `xstar_cf_freq_tendsto` skeleton (chain via `tailSched_*` analogue,
>    boundary `hasDiscLt_short_append`, interior `hasDiscLt_append_take` + (c),
>    `exists_stage` locator, metric limit). Lemma 9 pieces are in `BaryConcat`.
>    Do NOT reinvent the chain — it is a 1:1 port with CFDiscLt→HasDiscLt.
> 3. **Pillai** (`simple normal to all b^k ⇒ normal to b`) + **headline
>    statement**. Pillai NOT in mathlib/repo. Then state + JUDGE-freeze the
>    conjunction `(∀ b≥2, IsNormal b xstar) ∧ CF-normal xstar` and add a
>    Statement/audit surface (currently NONE for Track B).
> 4. **(Tier 2, LATER) W6 Khinchin graft** — digit caps `D_t` in Def 11. Revisits
>    the construction; do only after Tier 1 is stated + axiom-clean.
>
> ## Reflection — 2026-08-23 (deep reflection lap)
>
> - **Direction call: CONTINUE the route; refresh the docs.** No abort/escalate
>   trigger fired. Both of B–Y's deep imports are discharged; the γ-mixing rate
>   is geometric (stronger than the summable trigger threshold); no forbidden
>   import (CLT/KPW/Birkhoff) has been reached. The route is not spinning — the
>   OPPOSITE: whole-lemma targets (Lemma 13, schedule, `xstar`, CF normality)
>   have been CLOSING lap over lap, and finishability has IMPROVED, not declined.
>   The prior reflection's "route-decisive crux" (measure balance) is proved.
> - **The one real defect this lap caught**: DIRECTION/STATUS/PENDING_WORK were
>   all stale — they still named the Lemma-13 assembly the untouched crux, work
>   the grind laps had already blown past. A grind lap literally obeying the old
>   directive would have redone finished work. FIXED: all three refreshed; the
>   binding directive now points at the d-ary `m`-growth estimate.
> - **KEEP**: hardest-first on the d-ary interior estimate; the `Statement.lean`-
>   style faithfulness discipline (10/10 headlines trust-triple, re-verified);
>   the discharge-not-cite ethos (both deep imports gone); mirroring proven
>   skeletons instead of re-deriving (the d-ary chain = the CF chain).
> - **STOP**: treating "abs-normal + CF-normal + Khinchin" as one monolithic
>   goal. Khinchin (W6) is NOT in the source paper — it is a campaign-original
>   graft that must revisit the schedule (digit caps in Def 11) and carries the
>   most feasibility risk of anything left. Fence it behind a LOCKED Tier 1.
>   Also STOP letting the docs lag the git state by a whole review cycle.
> - **Highest-value next target: (c) the `m`-growth estimate.** Reasoning: it is
>   the most uncertain route-decisive blocker for the absolute-normality leg — if
>   it fails, the entire d-ary correctness chain (hence Tier 1's abs-normal half)
>   needs a redesign of the schedule dominance. Everything downstream of it ((d),
>   Pillai) is transcription or classical labor. It is genuinely new math (the
>   log-arithmetic interior estimate), and all its tools (`two_pow_le_cfK`,
>   `sched_dominance`, the good-length upper bound) are already in the repo, so it
>   is both the hardest and the ripest. Expert note: the whole d-ary correctness
>   proof is a transcription of the proven CF proof with THIS as its single new
>   analytic input — spend the lap here, not on re-scaffolding the chain.

── ARCHIVE (pre-2026-08-23-reflection; W3/W4/W5-input history, superseded) ──

# PENDING WORK — B5′ campaign (updated 2026-08-23, post-W3)

**W3 ✅ COMPLETE** (2026-08-23, 8 laps): all four frozen `CFMixing.lean`
statements proved, axiom-clean — `measurePreserving_gaussMap` (B1),
`volume_inter_preimage_eq_integral`, `cylinder_mixing` (C = 8 log 2,
ρ = 9/10, geometric — escape valve unused), `gauss_kuzmin` (B4).
`src/` is sorry-free.  See `HANDOFF-2026-08-23-1749.md`.

**W4 groundwork STARTED (this lap)**: `CFGammaMixing.lean` proves the
KPW-Lemma-6 substitute — the W4 correlation-decay engine — axiom-clean:

- `setIntegral_inter_preimage`: the s-started conditional density
  identity `∫_{I_w ∩ T^{-|w|}B} h_s = (∫_B h_{tChain s w})·(∫_{I_w} h_s)`
  (generalizes aux from `h_0 = 1` to any `h_s`, s ∈ [0,1]).
- `gaussMeasure_cylinder_mixing` (**γ-mixing, geometric rate**):
  `|γ(I_v ∩ T^{-(|v|+g)}A) − γ(I_v)γ(A)| ≤ (9/10)^g·4|A|·γ(I_v)`.
  Route: mixture Fubini γ = ∫₀¹ h_s·Leb dλ(s) + the pin bound, which is
  uniform in the start t — no new analysis was needed.

**W4 frontier — `CFBlockFreq.lean` (lap-authored groundwork).**
`S_n x = blockCount A n x = Σ_{k<n} 1_A(Tᵏx)` (Birkhoff sum). Route DE-RISKED:
γ-mixing is geometric ⇒ covariances summable ⇒ Var(S_n)=O(n).

DONE this lap (all axiom-clean, `#print axioms` = trust triple):
  ✅ `integral_blockCount` — first moment `∫ S_n dγ = n·γ(A)`.
  ✅ `gaussMeasureReal_pair_shift` — `γ(T^{-j}A ∩ T^{-(j+m)}A) = γ(A ∩ T^{-m}A)`.
  ✅ `integral_blockCount_sq` — second moment
     `∫ S_n² dγ = Σ_{j,j'<n} γ(T^{-j}A ∩ T^{-j'}A)`.
  ✅ `abs_cov_le` — **per-pair covariance bound** (the γ-mixing consumer):
     `|γ(I_v∩T^{-m}I_v) − γ(I_v)²| ≤ (9/10)^{m−|v|}·4|I_v|·γ(I_v)` (m≥|v|),
     `≤ 2γ(I_v)` (m<|v|).  ← the route-decisive step; mixing→covariance done.

  ✅ `abs_cov_pair_le` — per-pair bound at gap `|j−j'|`, uniform geometric
     dominator `4γ(I_v)·(9/10)^{|j−j'|∸|v|}` (absorbs the overlap case).
  ✅ `sum_range_dist_le` / `geom_trunc_sum_le` — the Finset gap-count reindex
     (`Σ_{j'} g(dist j j') ≤ 2Σ_d g(d)`) + truncated geometric tail (`≤ L+10`).
  ✅ `variance_blockCount_le` — `Var(S_n) ≤ (8|v|+80)·n·γ(I_v)`.  DONE this lap,
     axiom-clean.  (Constant `8|v|+80` not `4|v|+80`: the clean uniform
     dominator trades a factor 2 for a much shorter proof; harmless — any
     `n`-independent `K(v)` suffices for the construction.)

  ✅ `chebyshev_blockCount` — `γ{|S_n/n − γ(I_v)| ≥ δ} ≤ (8|v|+80)γ(I_v)/(δ²n)`.
     PROVED 2026-08-24 (@2ac0e83), axiom-clean.  Route exactly as planned:
     `MemLp.of_bound` (0 ≤ S_n ≤ n), `variance_eq_sub` + `Pi.pow_apply`,
     set rescale via `abs_div`/`le_div_iff₀`, `meas_ge_le_variance_div_sq`,
     `ENNReal.toReal_mono`/`toReal_ofReal`, final arithmetic by
     `gcongr` + `field_simp`.  **src/ is sorry-free — W4 core COMPLETE.**

  ✅ conditioned-on-brick version — PROVED 2026-08-24 (@c598d81), axiom-clean:
     `gaussMeasure_brick_inter_le` (γ(I_w ∩ T^{-|w|}A) ≤ 7·γ(A)·γ(I_w), via
     g=0 mixing + density window `volume_toReal_le_gaussMeasure`) and
     `chebyshev_blockCount_brick` (bad set inside a brick ≤
     7·(8|v|+80)·γ(I_v)/(δ²n)·γ(I_w)).  Note: much simpler than the planned
     s-started-identity route — the already-proved mixing theorem at gap 0
     absorbs the conditioning.

  ✅ **B–Y Lemma 8 PROVED** 2026-08-24 (@5142f84, `BaryBlockCount.lean`),
     axiom-clean: `card_baryDiscrepancy_ge_le` — #(length-k base-b blocks
     with simple discrepancy ≥ ε) ≤ 2·b^(k+1)·e^{−bε²k/6} for 0 ≤ ε ≤ 1/b.
     Purely combinatorial Chernoff: generating identity
     `sum_exp_digitCount` (Σ_u e^{λ·count} = (e^λ+b−1)^k via
     `Finset.sum_prod_piFinset`), tilt λ = ±bε/2, per-symbol bases from
     `Real.exp_bound` (order 2) + `add_one_le_exp` — both tails give exactly
     −bε²/6 per symbol; no calculus, no measure theory, and B–Y's extra
     hypothesis 6/k ≤ ε is NOT needed.

  ✅ **B–Y Lemma 9 PROVED** 2026-08-24 (`BaryConcat.lean`), axiom-clean:
     `HasDiscLt` (deviation-form simple discrepancy on `List (Fin b)`),
     parts 1/2a/2b as `HasDiscLt.append` / `hasDiscLt_append_take` /
     `hasDiscLt_short_append` (all triangle-inequality counting), plus
     `digitCount_eq_count_ofFn` bridging to Lemma 8's `Fin k → Fin b`
     blocks.  **The W4 b-ary side is now COMPLETE.**

  ✅ **B–Y Lemma 7 PROVED** 2026-08-24 (`CFConcat.lean`), axiom-clean:
     window-count calculus for `countOccurrences` (cons recursion,
     superadditivity, seam bound `count(x++u) ≤ count x + count u + (k−1)`
     by index-set split fit-in-x / shifted-in-u / ≤(k−1) straddle), then
     `CFDiscLt` deviation-form discrepancy and parts 1/2a/2b
     (`CFDiscLt.append`, `cfDiscLt_append_take`, `cfDiscLt_short_append`).
     Parts 2a/2b use hypothesis `|u|+(k−1) < ε|x|` (marginally stronger
     than paper's `|u|/|x| < ε`, absorbs the straddle; trivial for the W5
     schedule).  **All of B–Y Lemmas 7/8/9 are now formalized.**

  ✅ **B–Y Prop 12 PROVED** 2026-08-24 (`TBrickDefs.lean`), axiom-clean:
     `daryCell d m j r` (r consecutive order-m cells), `volume_daryCell`
     (= r/d^m), `interval_subset_daryCell_two` (any interval of length
     < d^{−m} sits inside the 2-cell at ⌊a·d^m⌋).

NEXT ATTACK: W5 t-brick structure (Defs 10–11) + Lemma 13 (main lemma).
Plan sketched from the paper (see scratch/by.txt §2, extracted 2026-08-24):
- Brick: CF word w (σcf = cfCylinder w) + per-base (m_d, j_d, r_d ∈ {1,2})
  with cfCylinder w ⊆ daryCell d m_d j_d r_d and relative length
  ≥ 1/(C·d) (B–Y C = 16e^{4c}; repo distortion constant differs — pick
  concrete C during Lemma 13, keep it a structure field or parameter).
- Lemma 13 inputs already in repo: good-length collection (W2 Markov
  substitute for B–Y Lemma 5 in CFDigitLaw), γ-Chebyshev brick bound
  (`chebyshev_blockCount_brick`, replaces B–Y Lemma 6/KPW — note 1/n
  decay beats the K/√n good mass, so the balance still works), Lemma 8
  (`card_baryDiscrepancy_ge_le`) for the d-ary bad zones.
  ✅ d-ary bad-zone bound PROVED 2026-08-24 (`volume_daryBadZone_le`,
  axiom-clean): inside an order-m0 cell, the union of order-(m0+k)
  sub-cells with ε-bad new blocks has measure ≤ 2d·e^{−dε²k/6}·d^{−m0}
  (`badBlocks` Finset + `card_badBlocks_le` = Lemma 8 restated).
- KEY ROUTE DECISION (recorded 2026-08-24): B–Y's uniform-m_d bookkeeping
  (their tight two-sided length window J_n, constant 16e^{4c}) does NOT
  match the repo's Lemma-5 substitute (`half_mass_long_extensions`, which
  bounds cfK only above; individual lengths spread exponentially).  Fix:
  choose m_d PER CHOSEN cylinder J maximal with |J| ≤ d^{−m_d} (Prop 12
  ⇒ ratio > 1/(2d)), and make the chosen J avoid the union of bad zones
  over ALL orders m ≥ m_min(n) — the geometric sum over m of
  `volume_daryBadZone_le` is still exponentially small vs the ≥ |I_w|/2
  good mass.  Brick ratio constant becomes 1/(2d) (not 16e^{4c}d).
  ✅ (a) sum-over-orders corollary PROVED 2026-08-24 (@6742fb7,
  `volume_iUnion_daryBadZone_le`): ⋃_{k≥kmin} daryBadZone has measure
  ≤ (2d/d^m0)·ρ^kmin/(1−ρ), ρ = e^{−dε²/6}.
  ✅ (c) digit-semantics bridge PROVED 2026-08-24, axiom-clean:
  `exists_block_of_lt` (blockNatVal surjective onto [0,d^k)),
  `floor_subCell_bounds` (a point's own order-(m0+k) sub-cell sits at
  index j0·d^k + v, v < d^k), `exists_goodBlock_of_notMem_badZone`
  (avoiding daryBadZone ⇒ the point's sub-cell carries a GOOD block).
  ✅ neighbor-widened zone PROVED 2026-08-24, axiom-clean:
  `daryBadZoneWide` (+ measure ≤ 6d e^{−dε²k/6}/d^m0, summed version via
  new generic `volume_iUnion_geom_le`), `badBlock_cell_far` (avoiding the
  wide zone puts every bad cell at distance ≥ 2 from x's own cell).
  ✅ CF word bridge PROVED 2026-08-24 (`CFWordBridge.lean`), axiom-clean:
  `iterate_mem_cfCylinder_iff` (cylinder membership = digit-window match),
  `blockCount_eq_card_matches`, `blockCount_sub_countOccurrences_bounds`
  (orbit count vs fitting-window count of the digit word differ ≤ |v|) —
  connects `chebyshev_blockCount_brick` to `CFDiscLt` of the new word.
- ✅ (b) BRICK STRUCTURE + d-ARY SIDE OF THE BALANCE PROVED 2026-08-24
  (review lap, `TBrick.lean`, axiom-clean):
  * `structure TBrick (t)` = Defs 10–11: genuine CF word `w`, per base
    `2 ≤ d ≤ t` an order-`m d` cell block of `r d ∈ {1,2}` cells with
    `cfCylinder w ⊆ daryCell d (m d) (j d) (r d)`, brick-ratio field
    `hratio : d^{-m d} ≤ 2d·|I_w|` (the repo's Prop-12 `1/(2d)` route,
    replacing B–Y's `1/(16 e^{4c} d)`).
  * `volume_aggregate_daryBadZoneWide_le`: ⋃_{2≤d≤t} ⋃_{k≥kmin}
    daryBadZoneWide ≤ Σ_d 6d·d^{-m0 d}·ρ_d^kmin/(1−ρ_d), ρ_d = e^{−dε²/6}
    (via `measure_biUnion_finset_le` + the summed-zone lemma; needs only
    `dε ≤ tε ≤ 1`).
  * `TBrick.volume_aggregate_bad_le`: **the d-ary half of the Lemma-13
    balance** — that aggregate bad zone ≤ (Σ_d 12d²ρ_d^kmin/(1−ρ_d))·|I_w|,
    using `hratio` to turn each `d^{-m0 d}` into `2d|I_w|`.  The constant is
    a finite sum of geometric-in-kmin terms ⇒ →0 as kmin→∞, so the d-ary bad
    mass is eventually an arbitrarily small fraction of |I_w|. ✅ d-ary side
    of the measure balance CLOSED.

- ✅ (i) CF SIDE OF THE BALANCE PROVED 2026-08-24 (review lap, `TBrick.lean`,
  axiom-clean): `cfBadZone w v n δ` (the set `chebyshev_blockCount_brick`
  controls) + `gaussMeasure_aggregate_cfBadZone_le` — for a FINITE family `F`
  of genuine CF words, `γ(⋃_{v∈F} cfBadZone w v n δ) ≤ Σ_{v∈F} 7(8|v|+80)
  γ(I_v)/(δ²n)·γ(I_w)` = O(1/n)·γ(I_w).  Resolves the "infinite alphabet"
  worry: the construction needs only finitely many blocks good per stage
  (length ≤ t, digits ≤ t), so a finite `measure_biUnion_finset_le` aggregate
  suffices — no `CFDiscLt` weighted sum needed for the measure step.
  (`CFDiscLt`/`CFWordBridge` still used later to turn "good frequency for all
  v ∈ F" into the refinement predicate of Def 11.)

- ✅ (ii) GOOD-MASS SIDE + COMBINE CORE PROVED 2026-08-24 (review lap,
  `TBrick.lean`, axiom-clean):
  * `goodExtSet w C n` (biUnion of good-length order-n extensions, bad ones
    sent to ∅) + `volume_goodExtSet` (= the `half_mass` tsum verbatim, via
    `measure_biUnion` + `cfCylinder_disjoint`; the `if..else ∅` trick avoids
    all subtype reindexing) + `exists_C_half_le_volume_goodExtSet`:
    `|I_w| ≤ 2·volume(goodExtSet)`, i.e. good mass ≥ ½|I_w|.
  * `exists_mem_notMem_of_measure_lt` (the COMBINE CORE): if `M ≤ μG`,
    `μB ≤ a`, `a < M`, then `∃ x ∈ G, x ∉ B`.  The logical backbone of
    "balance ⇒ surviving refinement".
  ALL FOUR ingredients of the Lemma-13 measure balance are now proved:
  good mass ≥ ½|I_w|, d-ary bad ≤ (→0)|I_w|, CF bad ≤ O(1/n)γ(I_w), and the
  combine core.  What remains is the ARITHMETIC WIRING (below).

- NEXT concrete step (WIRE THE BALANCE — mechanical, no new deep facts):
  ✅ (α) DONE 2026-08-24 (`TBrick.lean`, axiom-clean): `volume_iUnion_cfBadZone_le`
      — volume(⋃ CF bad) ≤ ofReal(2log2·Σ_v 7(8|v|+80)γ(I_v)/(δ²n)·γ(I_w)),
      i.e. the CF bad zone in LEBESGUE, still O(1/n).  Helpers:
      `volume_le_ofReal_mul_gaussMeasure` (vol s ≤ ofReal(2log2)·γ s on Ioo 0 1)
      + `measurableSet_cfBadZone` (via `measurable_blockCount`).  Still to do
      for the balance: bound Σ_v ... by (const/n)·volume(I_w) via γ(I_v)≤1 and
      γ(I_w) ≤ ofReal((log2)⁻¹)·volume(I_w) (gaussMeasure_le_volume).
  ✅ (β) **kmin(n) link** DONE 2026-08-24 late lap (@10a8c6e,
      `TBrickRefine.lean`, axiom-clean), LOG-FREE form: `4·d^kmin <
      fib(n+1)²` ⇒ `|I_{w++u}| < d^{−(m_d+kmin)}`
      (`TBrick.volume_append_lt_dpow`, via `volume_append_mul_fib_le` +
      brick containment `|I_w| ≤ 2d^{−m_d}`); threshold
      `exists_fib_threshold` (fib(n+1)² → ∞, via `Nat.le_fib_self`).
      Same commit: bad zones now cover BOTH possible base cells
      (j_d, j_d+1; coefficient 24d²), survivors are IRRATIONAL
      (rationals absorbed as a null set), `volume_cfCylinder_ne_zero`
      discharges hpos, and the survivor-unpacking toolkit is proved:
      `exists_word_of_mem_goodExtSet`, `range_map_cfDigit_eq` (digit word
      = u), `abs_blockCount_lt_of_notMem_cfBadZone` (CF side),
      `TBrick.exists_goodBlock_of_avoid` (x's own new d-ary block good at
      every k ≥ kmin, in x's definite cell).
  ✅ (γ-COMBINE) DONE 2026-08-24 (`TBrick.lean`, axiom-clean): the measure
      core is assembled.  `exists_mem_notMem_union_of_bounds` (abstract:
      good ≥ ½vol0, bads ≤ p·vol0, q·vol0, p+q<½ ⇒ ∃ x∈G avoiding both) +
      `exists_good_avoiding_bad` (concrete Lemma-13 core): GIVEN the two
      coefficient thresholds `14ΣL/(δ²n) < ¼` and `Σ_d 12d²ρ^kmin/(1−ρ) < ¼`
      (and `vol(I_w) ≠ 0`), ∃ good-length order-n extension of I_w avoiding
      BOTH the CF bad zone (all v∈F) AND the wide d-ary bad zone (all d≤t,
      k≥kmin).  This is the measure-theoretic heart of Lemma 13.
  ✅ (γ-leftover) DONE 2026-08-24 (`TBrick.lean`, axiom-clean): the two
      coefficient thresholds hold eventually — `exists_N_cfCoeff_lt`
      (14SL/(δ²n) < ¼ for n ≥ N, archimedean), `tendsto_daryCoeff` +
      `exists_kmin_daryCoeff_lt` (Σ_d 12d²ρ^kmin/(1−ρ) < ¼ for kmin ≥ kmin₀,
      finite geometric decay).  `exists_good_avoiding_bad_of_large` bundles
      them: ∃ N kmin₀, ∀ n≥N ∀ kmin≥kmin₀, the surviving good extension
      exists.  **The entire measure side of Lemma 13 is now UNCONDITIONAL.**
  (γ-OLDtext) **choose n₀**: both bad bounds are `< ¼·volume(I_w)` for n ≥ n₀(t,ε)
      (d-ary: geometric in kmin(n)→0; CF: O(1/n)→0).  Then
      `exists_mem_notMem_of_measure_lt` with M = ½vol(I_w) via
      `exists_C_half_le_volume_goodExtSet`, a = ¼+¼ < ½, gives x ∈ goodExtSet
      avoiding all bad zones.
  (δ) **Lemma 13 proper** (NEXT ATTACK — assembly only, all inputs proved):
      from the irrational survivor x (exists_good_avoiding_bad_of_large +
      the TBrickRefine toolkit): (1) extract u (exists_word_of_mem_goodExtSet);
      (2) NEW BRICK: for each d ≤ t (or t+1) choose m'_d maximal with
      |I_{w++u}| < d^{−m'_d} (nonempty by (β) with k := m'_d − m_d ≥ kmin;
      well-defined since |I_{w++u}| > 0); Prop 12
      (`interval_subset_daryCell_two`, needs I_{w++u} ⊆ an interval of that
      length — use `cfCylinder_subset_uIcc` + `volume_cfCylinder`) gives the
      ≤2-cell block + ratio 1/(2d); (3) GOODNESS: x's own new block is good
      (`TBrick.exists_goodBlock_of_avoid` at k) — check the Prop-12 block's
      cells sit within distance 1 of x's cell so `badBlock_cell_far`
      covers the second cell; (4) CF goodness of u: bridge
      `abs_blockCount_lt_of_notMem_cfBadZone` +
      `blockCount_sub_countOccurrences_bounds` + `range_map_cfDigit_eq`
      → countOccurrences bound on u for each v ∈ F (→ `CFDiscLt` form).
      Package as `TBrick.exists_refinement` (statement = repo Lemma 13).
      t→t+1: extra base via Prop 12 alone (no goodness needed at stage 1).

- (OLD framing, superseded by (α)-(δ)):
  (ii) **kmin(n) link**: good-length extensions J have |J| ≤ 2φ^{-2(n-1)}|I_w|
      (Fibonacci upper bound), so for each base d the "new digits" count
      k_d(J) ≥ kmin(n) with kmin(n)→∞; hence the wide-zone union avoided is
      exactly ⋃_{k≥kmin(n)} and `TBrick.volume_aggregate_bad_le` applies.
  (iii) **combine** (Leb↔γ, factor-2 window): ½|I_w| good (Lemma-5 subst)
      minus O(1/n)|I_w| CF minus (→0)|I_w| d-ary is > 0 for n ≥ n₀(t,ε) ⇒
      a surviving good extension J.  Then Lemma 13 proper: J is an
      ε-refinement; t→t+1 via Prop 12 (ratio 1/(2(t+1))).

Tools confirmed: `measurePreserving_gaussMap`, `gaussMeasure_univ`=1 (⇒
`IsProbabilityMeasure gaussMeasure` instance added in CFBlockFreq),
`gaussMeasure_cylinder_mixing`, `measureReal_preimage`, mathlib
`meas_ge_le_variance_div_sq` (Probability/Moments/Variance.lean).
2. Conditioned version on a base cylinder I_w (B–Y need per-stage bad
   measure < ¼ *given the current brick*): same computation under the
   conditional measure — the s-started identity makes every conditional
   a tailDensity mixture, so the same pin applies.  Alternatively work
   with Leb-conditionals directly via `volume_inter_preimage_horizon`.
3. b-ary side: Lemma 8 (Hardy–Wright Thm 148 Chernoff block counting)
   + Lemma 9 (BHS 3.1 concatenation) — check overlap with
   `Counting.lean`/`Visits.lean` first.
4. DRAFT frozen W4 statements for judge ratification (do NOT put
   unratified "frozen" statements in a scaffold file claiming authority;
   put proposals in drafts/).

**Judge attention requested**: ratify W4 statement shapes; note the
γ-mixing bonus (stronger than the planned Leb-only route: it is exact
γ-correlation decay, geometric, multiplicative in γ(I_v)).

> **GRIND (2026-08-24 lap N — route C′ core lemmas PROVED).** Two green
> commits: (1) `volume_logBadZone_le_vol` (new file `KhinchinBrick.lean`) —
> bridges `markov_logBadZone_brick`'s `gaussMeasure` bound into Lebesgue
> `volume` via the same `2 log 2` density-window factor `TBrick.lean` uses
> for the CF bad zone, giving the matching `14·(∫ logTailFn K dγ)/η`
> coefficient form. (2) `exists_good_avoiding_bad_khinchin` — mirrors
> `exists_good_avoiding_bad` (`TBrick.lean:470`) with `logBadZone` folded
> into the d-ary union via `measure_union_le`; NO `TBrick.lean` edits needed
> (as the prior handoff predicted). Coefficients tightened `<¼`→`<⅙` each so
> CF+d-ary+log sum `<½`. Both axiom-clean.
> **NEXT**: thread `exists_good_avoiding_bad_khinchin` through
> `exists_refinement_uniform` (`TBrickRefine.lean`/`CFSchedule.lean`) and the
> `xstar` schedule rederivation — this needs reading how `xstar`'s schedule
> currently invokes `exists_good_avoiding_bad`/`_of_large` (likely in
> `CFSchedule.lean` or `Headline.lean`) and adding the parallel K/η-indexed
> log-zone-avoidance guarantee, choosing `K` via `integral_logTailFn_tendsto`
> to satisfy `hlog`. This is the remaining mechanical (but nontrivial)
> plumbing to close `xstar_log_tail_uniform`.

## 2026-08-29 (lane-2 lap): PiBBP discharged
`piBBP_proved : PiBBP` is sorry-free, trust triple `[propext, Classical.choice, Quot.sound]`
(HEAD 1e228a2). Route: no integrals — roots-of-unity filter through
`Complex.hasSum_taylorSeries_neg_log` at 1/√2, −1/√2, (1±i)/2 with weights −2, −2, 2∓2i;
log values reassemble to π; mod-8 fibers (`Nat.divModEquiv` + `HasSum.prod_fiberwise`)
reproduce `bbpTerm` exactly. Scoped objective `sorry-free:src/NormalNumbers/PiBBPProof.lean`
is MET. Next (per operator brief, if resumed): target 2 `oneRun_le_of_sliverEscape`, then
target 3 Glaisher/Sun congruence.

## 2026-08-29 (lane-2 lap): twin edge `oneRun_le_of_sliverEscape` closed
Sorry-free, trust triple (KickDynamicsOneRun.lean). Width-mismatch DECISION: the one-run
dichotomy only certifies the WIDE sliver `1 − 2/(n+j+1)` (no-wraparound branch gives
`x ≥ 1 − 1/2ᵏ − τ` with tail bound only `τ ≤ 1/(n+1)`), so the frozen narrow node
`SliverEscape` cannot serve as hypothesis. Per the draft docstring's mandate, froze the
wide-sliver variant node `SliverEscapeWide` in KickDynamicsOneRun.lean (provenance docstring
there) and proved the edge from it, mirroring `zeroRun_le_of_sliverEscape` (constant
tightened +3 → +2). Bonus edge `sliverEscape_of_wide : SliverEscapeWide → SliverEscape`
records that wide is the stronger node. Frozen `SliverEscape` untouched. Next (per operator
brief): target 3 Glaisher/Sun congruence.

## 2026-08-29 (lane-2 lap): target 3 `lnTwoNum_modEq_fermatQuotient` closed
Sorry-free, trust triple `[propext, Classical.choice, Quot.sound]` (LnTwoFermatBridge.lean,
HEAD 5b7fc49). The Glaisher/Z.-H. Sun Fermat-quotient bridge in the frozen probe shape:
`lnTwoNum (p−1) ≡ lcmRange (p−1) · fermatQuotient2 p [MOD p]` for odd primes. Proof all in
`ZMod p`: `C(p−1,k) ≡ (−1)^k` by induction; the exact quotient `C(p,k+1)/p ≡ (−1)^k/(k+1)`
via `Nat.add_one_mul_choose_eq`; binomial theorem at `x = −2` over ℤ gives the exact
identity `Σ C(p,k+1)(−2)^{k+1} = 2^p − 2 = 2p·q′`, divide by `p` and cast to get Sun's
congruence `Σ 2^j/j ≡ −2 q_p(2)`; `Finset.sum_range_reflect` on the surrogate sum plus
`(p−1−j) ≡ −(j+1)` closes `A_{p−1} ≡ L·q_p(2)`. All three lane-2 targets of the
2026-08-29 treadmill brief are now DONE.

## 2026-08-29 (lane-2 lap): target 4 `lnTwoExpSep_holds` PROVED (β = 26)
Sorry-free, trust triple `[propext, Classical.choice, Quot.sound]` — Tier-1
LnTwoExpSep discharged IN-HOUSE via shifted-Legendre linear forms. Route:
vendored collatz-moonshot FrontA `Legendre.lean`/`Gelfond.lean` (→
`LegendreShifted.lean`, `LcmUptoGrowth.lean`, provenance headers, same pin);
closed both honest gaps in `LegendreHeight.lean` — height `|Q| ≤ (ℓ+1)·8^ℓ·lcm ℓ`
(explicit coeffs `(−1)^k C(ℓ,k)C(ℓ+k,ℓ)`, each ≤ 8^ℓ) and lower bound
`|P+Q·log2| ≥ lcm ℓ·(1/6)(1/12)^ℓ` (remainder integral on [1/4,1/2]) — then the
pairing at `ℓ = 4n` in `LnTwoExpSepProof.lean`: `N = P·2ⁿ+Q·p`; nonzero case
`1 ≤ 1/2 + H·d`, zero case `|Q|d = 2ⁿ|form|` with lcm cancelling. One master
limit (geometric beats `(4n+1)e^{2√(4n)log(4n)}`) powers all three eventual
inequalities. β DECISION: draft's 4 raised to 26 per the DRAFT clause — honest
crude constants give height `≲ 2^{20n}` (nonzero case) and `2^{n−25.34n}` (zero
case, `2²⁷ > 96⁴`); the Alladi–Robinson rate 3.63 would need sharp `P_ℓ(3)`
coefficient asymptotics + two-sided remainder, not attempted. Consequence:
`run_le_of_expSep` now caps every zero/one run of binary `ln 2` at `26n+O(1)`
unconditionally. Scoped objective `sorry-free:LnTwoExpSepProof.lean` MET.

## 2026-08-29 (lane-2 lap): target 5 `LogTwoSqKicked.lean` DONE (dessert)
Summed-kick machine instantiated for a second constant, `log² 2` (base 2,
kicks `r m = 2·H_{m−1}/m`). Probe `experiments/logtwosq_series.py` PASSES
(identity to 70 digits, exact rationals; cap checked at n=1,2,6,10,50).
Headlines sorry-free, trust triple, node `LogTwoSqSeries` stays CITED
(hypothesis-not-axiom): `logTwoSq_top_sliver_of_zeroRun` (sliver
`1 − 2(1+log(n+1))/(n+1)`; the draft's `6 ≤ n` dropped — `hk` forces
`H_n > 0`), maxRun twin conditional on `hhalf`, discharged for `n ≥ 56` by
`logTwoSqCap_le_half` (log x ≤ 2(√x−1) route; numerically true from n=14 —
lossy but elementary). Machinery: position-dependent cap via mathlib
`harmonic_le_one_add_log` + antitonicity of `(1+log x)/x` on `[1,∞)`
(`one_add_log_div_le_of_le`). OWED LATER (per brief, not this run): discharge
the `LogTwoSqSeries` node in-house (Cauchy product / integrated harmonic
generating function at `x = 1/2`).

## G4 lap 11 — the §5 schedule, made explicit (design record, 2026-09-14)

**Structural decision.** `ScheduleWitness ℓ w` is a bundle of inequalities at ONE `X`.  For
each omitted word `ℓ` we may choose `K` first and then `X` — `K = 4·8464·ℓ²·16^ℓ` (so `hB`
holds by `gridParams_hB`, `8ℓM = K`, `2ℓM = K/4`), then `N = 100K²`, then
`m₁ = 100·8^K·K^{2K+1}`, `R = 2^{2^{m₁}}`, `Mc = 3·10⁴·T·m₁`, `Y = 2^{2^m}`, `X = Y^{100}`,
`m = m₁ + 8K²`.  This is NOT "freezing `K` and sending `X → ∞`": `K → ∞` with `ℓ`, and `X`
is a finite function of `K`.  `K` sits at the upper edge of the two-sided window
(`log L ≈ 2K log K`), the lower edge `K ≳ 0.58 log log L ≈ log(2K log K)` is trivial.  No
`scheduleK`/floor asymptotics are needed; `schedule_budget` is superseded by the explicit
choice of `m₁`.

**Two crude bounds that FAIL (recorded so nobody retries them).**
* `∑_{p∈sm} 1/p ≤ log R + 1` (from `sum_inv_le_log_card_add_one`) is too weak for the
  `hbudget` error terms (b),(c): `Mc` would have to exceed `T·log R = T·2^{m₁}`, and then
  `hbig`'s `log(log Y/log R) ≈ log Mc ≈ 2^{m₁}` destroys `hbig`.  Must use the dyadic
  Chebyshev `sum_inv_primes_Ioc_le` (constant 4): `∑ ≤ 4(1 + m₁ log 2) + 1/2`.  With constant
  4 the brief's `Mc = 10⁴TL` becomes `Mc = 3·10⁴·T·m₁` (`lam = 13/2`, `e^{lam} ≤ e^7 ≤ 1097`,
  `log(4e/13) ≤ −0.163`).
* `ω(P₀) ≤ P₀` for the excluded-prime harmonic mass is too weak (`log P₀ ≫ m₁`); use
  `2^{ω(P₀)} ≤ P₀` (`two_pow_omega_le_card_divisors`), giving `log ω(P₀) ≤ log(2 log P₀)`.
* `card{T' ⊆ sm : |T'| ≤ Mc} ≤ 2^{|sm|}` is too weak for term (a) (`2^R ≫ X`); use
  `≤ Mc·R^{Mc}` via `powerset_card_disjiUnion` + `choose ≤ n^k`.

**Size ladder (ℕ, `K ≥ 100`)**: `N ≤ K³`, `J ≤ K⁴`, `B ≤ K⁷`, `U ≤ K^{7K+3}`, `W ≤ K^{7K+4}`,
`H ≤ K^{3K}`, `T ≤ K^{3K+3}`, `logP₀Nat ≤ K^{20K+17}`, `m₁ ≤ K^{3K+3}`, `Mc ≤ K^{6K+9}`;
and `K^{cK} ≤ 2^{cK²}`, `4^N = 2^{200K²} ≥ K^{40K}`.

## Entropy expedition — the 18:20 RE-TARGET override, both verdicts in (2026-09-14)

**A0 — verdict NO, obstruction proved.**  `G4EntropyXCeiling.lean`.  `X` enters the whole E0
cone through exactly one field of `gridFrame` (`P := apSample X G.P₀ G.b₀`); everything else —
`θ, γ, S, A, d, t, η, ε, D`, hence `goodSets`, `pieceCube`, `res`, the cover sum, and E0's target
`M = k₄(K²+1)^K` — is literally `X`-free.  Of the five `X`-sensitive terms three are monotone,
`hfar`'s `log log X` is a never-binding ceiling (`X ≲ 2^{2^{2^{200K²}}}`), and
**`hbig`'s `(log Mx / log Y)` binds** (`hMx` forces `Mx ≥ X − P₀`).
`ScheduleWitness.X_lt_X_step` : any witness at the implemented allowances has `X < Sched.X (K+4)`.
Raising `Y` with `X` does not rescue it: `hbig`'s dyadic summand allows `m − m₁ ≲ 2^{5K/2}`,
one rung costs `m₁(K+4) − m₁(K) ≥ 4095·1000·8^K·K^{2K+1}`.  Ladder jump = SMALL-prime budget;
fixed-`K` headroom = MEDIUM-prime dyadic factor.  Incommensurable.

**A — stopped** per the override (A0 = NO ⟹ name the obstruction and stop).

**B — verdict NO, refutation proved.**  `G4EntropyResidueProbe.lean`.  The per-declaration audit
is *all-YES on the estimates* (two structural re-basings — `kIdx → kIdxOf`, `θ`'s offset — and no
constant moves; only `kIdx_pos`, a non-vacuity lemma, fails off `b₀`).  But the payoff fails:
`exists_kIdxOf_eq` shows `d_α ∣ kIdxOf G b n α` in EVERY class (it needs only `d_α² ∣ P₀`), so
`Sched.not_dense_of_any_residue` — the union over ANY finset of classes misses more than half of
every prefix `L ≥ 2·dmin i`.  Class-side companion of `G4EntropyFamily.not_dense_of_scale`.

**The named gap, for the record**: it is not an estimate.  It is `d_α² ∣ P₀` — exactly what
`PropA` consumes to make the transport exact.  Exactness and density are in direct tension; the
sample must freeze the multiplier residues to transport, and freezing them confines the read to
`⋃_α (2 d_α ℕ + [0, m_K))`, of density `≤ 2^{−(i+3)}`.  Neither moving `X` (A0) nor moving the
class (B) trades that.

**Next attack, for `fullReal` as a number in its own right** (Trevor's call in DIRECTION):
1. ✅ `Sched.tendsto_density_fullPos` (`G4EntropyFullDensity.lean`) — the read visits a
   density-zero set, stated about `fullPos` itself.  (Wrap next-step 2.)
2. ⏳ Port the mid-band refinements (`abs_midRead_freq_sub_le`, `tendsto_midRead_freq_of_depth`,
   `abs_freq_sub_freq_mid`, stated for `bandPos`) to `fullPos`, carrying the multiplicity term
   through `overhang_frac_le`.  (Wrap next-step 1.)  This is the only remaining on-path work the
   wall permits; `IsNormal 2 fullReal` itself is blocked by `wall_at_zero_deficit` plus A0.

## 2026-09-20 — sparse-subset lap (`src/NormalNumbers/G4WiringSparse.lean`)

Leaves 1–5, 7 and all `BlockData` bookkeeping + `exists_block` are proved.  Two sorries remain.

**`exists_relDensityZero_divergent` (leaf 6) — PNT wall, refuted three ways this lap.**
Not a tactic problem.  Relative density `0` is tested at the *top* of each block, forcing
`#Bᵢ = o(π(vᵢ))`; combined with a lower bound on `δᵢ = ∑_{Bᵢ} 1/p` this needs either
`π(x) ~ x/log x` + primes in short intervals, or Mertens/Chebyshev in arithmetic progressions.
Mathlib has only constant-factor Chebyshev (`Chebyshev.pi_ge`, `Chebyshev.pi_le_log4_mul_div`)
and the repo only the one-sided `G4Mertens.log_log_le_sum_inv_primesBelow`.  The residue-class
dodge (count `≤ v/q + 1` for free, so `q ≫ log v` gives density) is *provably* insufficient: the
mass rate becomes `d(log log v)/log v`, whose integral `∫ dL/L²` converges, so `∑ δᵢ < ∞` always.
General form of the obstruction (this is the sharp statement): the only free count bound is
"a fraction of the integers", off by `log x` from `π(x)`; so any free-count construction has
integer-density `≤ 1/log v`, mass rate `≤ dL/L²`, and `∫dL/L² < ∞` — **every** such construction
has a convergent reciprocal sum.

**The construction that does work** (found this lap, matches the `π_S ≍ π/log log x` hint):
blocks `Bᵢ` = primes of `(yᵢ, vᵢ]`, `log vᵢ = Lᵢ + εᵢ`, gaps `ΔLᵢ = εᵢ gᵢ` with `gᵢ = log Lᵢ`.
Count fraction `≈ 1 − e^{-εᵢ} → 0`; accumulated density `≈ 1/gᵢ = 1/log log yᵢ → 0`; total mass
`∑ (ΔLᵢ/Lᵢ)/gᵢ = ∫ dL/(L log L) = ∞`.  Sandwich closes with room.

**Exact inputs needed** (both absent): `π(x) ~ x/log x`, and Mertens *with its constant*
`∑_{p≤x} 1/p = log log x + M + o(1)`.  The repo's one-sided `log log N ≤ ∑_{p<N} 1/p + 1` cannot
substitute: the block mass is a difference of two such sums and the `±1` swamps `εᵢ/Lᵢ → 0`.
**Elementary Mertens is NOT a way around it — do not chase it.**  Mertens' second theorem is
elementary but its error is `O(1/log x) = O(1/L)`, and the block mass is `εᵢ/Lᵢ` with `εᵢ → 0`:
the error swamps the mass.  Raising `εᵢ` to a constant to clear the error makes the block a
`1 − e^{-A}` fraction of `π(v)`, killing the density.  The regimes are exclusive; short blocks
need the PNT error term `π(x) = Li(x) + O(x e^{-c√log x})`.  A Brun–Titchmarsh sieve does not help
either (it bounds the count from above; the binding constraint is the mass from below).

**Next attack:** wait for PNT-with-error-term in mathlib (or upstream `PrimeNumberTheoremAnd`),
then formalize the recursion above; the `L`-coordinate parameterization is the part that was
missing, and the sandwich `∫dL/(L log L) = ∞` vs density `1/log L → 0` closes with room.

**`exists_good` — the sandwich; out of scope for this lap by operator instruction.**
All its consumers are now proved, so it is the single remaining obligation of
`exists_sparse_normal_of_KMT_quant`.  Explicit choices are in its docstring; `exists_block` (now
proved) supplies the blocks.

## 2026-09-21 — `phaseOscillation` chain: the three `MomentChain` obligations are reduced, and they are in TENSION

`src/NormalNumbers/PrimeLambertIndepChar.lean` (new, sorry-free) reduces all three obligations of
`MomentChain` → `SmallPrimeDecay` → `phaseOscillation` to elementary numeric conditions on the
chain's own parameters (see `HANDOFF-2026-09-21-indepchar.md` for the lemma list):

* `IndepCharDecay`   ⟸ `∑_{p ∈ Good N} sin²(π q c(a₀) 2^{−(i₀+1)}) / p → ∞`
* `IndepMomentSmall` ⟸ `(2π|q|)^{M_N}/M_N! · B_N^{M_N} → 0`
* `MomentComparison` ⟸ `max(1, B_N)^{M_N} · sampleDiscrepancy_N → 0`

where `B_N` is any uniform bound on `|S_N|` over the residues.

### The tension (the real finding of the lap — check this before building a chain)

Write `y` for the sieve cutoff, so `#small ≈ π(y)` and `modulus ≈ e^y`.

1. `MomentComparison` is only affordable when **`B_N ≤ 1`** — otherwise it demands
   `sampleDiscrepancy ≤ B_N^{−M_N}`, exponentially small, while the discrepancy is `≳ 1` unless
   `|P_N| ≫ modulus ≈ e^y` (most residue classes are empty otherwise).  With `B_N ≤ 1`,
   `momentComparison_of_le_one` needs only `sampleDiscrepancy → 0`, and `IndepMomentSmall` is free.
2. `IndepCharDecay` pushes the other way: `i₀ ≥ K`, so the site defect is
   `sin²(π q c(a₀) 2^{−(i₀+1)}) ≈ 4^{−K}`, and the sum is `≈ 4^{−K} log log y`.  Divergence needs
   **`log log y ≫ 4^K`**, i.e. `y ≈ exp(exp(4^K))`.
3. But the COARSE bound `momentBound = #small · ‖c‖₁ / 2^K ≈ π(y)‖c‖₁/2^K ≤ 1` forces
   **`y ≲ 2^K`** — flatly contradicting (2).

So the route **cannot close with the coarse bound**.  This is not a defect of the reduction: the
coarse bound charges every small prime, whereas `X_p(n) ≠ 0` only for primes actually dividing one
of the `|support|·(J−K)` arguments (`activePrimes`, `abs_classSum_le_card`).  The sharp bound is
`#activePrimes · ‖c‖₁ 2^{−K} ≲ |support|(J−K) · log₂(max arg) · ‖c‖₁ 2^{−K}` — **independent of `y`**,
which removes the contradiction entirely.

### Next attack (in order)

1. **Formalize the sharp bound.**  `activeBound C N := sup_{n} #activePrimes(n) · ‖c‖₁/2^K`, and
   `∀ r, |smallSum C N r| ≤ activeBound C N`.  The moment obligations already accept an arbitrary
   `B_N` (`indepMomentSmall_of_bound`, `momentComparison_of_bound`,
   `momentComparison_of_le_one`), so this plugs straight in.  Bound `#activePrimes` by
   `∑_{a,i} ω(n + (i+1)d_a − s_a) ≤ |support|(J−K)·log₂(max arg)` via `omegaR_le_log`.
2. Then `B_N ≤ 1` becomes `2^K ≳ |support|(J−K)‖c‖₁ log₂(max arg)` — a condition on `K` alone,
   compatible with `y ≈ exp(exp(4^K))`.
3. The only genuinely arithmetic obligation left is then `sampleDiscrepancy_N → 0`: the progression
   sample must equidistribute in `L¹` modulo `∏_{p small} p`.  Since that modulus is `≈ e^y` with
   `y ≈ exp(exp(4^K))`, the sample must be *at least* that long — this is the real cost of the route
   and the number to check against the draft's `N^{−9/10+o(1)}` claim before going further.

### CORRECTION (same lap, commit `9c5b9cd`): the tension above is RESOLVED, the route survives

Step 1 of the "next attack" is done.  `card_activePrimes_le` / `abs_smallSum_le_active` /
`abs_smallSum_le_one_of_pow_le` give the sharp bound

  `|S_N(n)| ≤ (∑_{a,i} log₂|n+(i+1)d_a−s_a|) · ‖c‖₁ 2^{−K}`,  provided no argument vanishes,

which is **independent of `y`**.  So `|S_N| ≤ 1` is a condition on `K` and the configuration alone
(`2^K ≳ (window log₂-mass)·‖c‖₁`) and is compatible with `y ≈ exp(exp(4^K))`.  The contradiction
`y ≲ 2^K` was an artifact of the coarse `momentBound` charging every small prime instead of the
`O(log)` that actually divide an argument.  Net:

| obligation | cost with the sharp bound |
|---|---|
| `MomentComparison` | `sampleDiscrepancy_N → 0` only (via `momentComparison_of_le_one`) |
| `IndepMomentSmall` | free |
| `IndepCharDecay` | free to demand `y ≈ exp(exp(4^K))` |

**The one arithmetic obligation left in the whole `phaseOscillation` chain is
`sampleDiscrepancy_N → 0`.**  Next lap starts there.  Note the scale it forces: a sample shorter
than the modulus has discrepancy `≳ 1` (most classes empty), and the modulus is `∏_{p small} p ≈ e^y`
with `y ≈ exp(exp(4^K))`, so `|P_N| ≫ exp(exp(exp(4^K)))`.  **Check that tower against the draft's
`δ_N = N^{−9/10+o(1)}` claim before building a chain** — if the draft's sample is polynomial in `N`
while the modulus is a tower, the route has a second, more serious gap and `IndepCharDecay`'s
`y ≈ exp(exp(4^K))` demand is where to look.  The remaining side condition to discharge along the
way: no argument `n+(i+1)d_a−s_a` vanishes, for `n` ranging over the sample AND over the residues
`0 ≤ r < modulus` (the latter is where it can fail, at `≤ |support|(J−K)` residues).

## 2026-09-23 — Theorem C′ audit surface LANDED

`src/NormalNumbers/PrimeModelGradedStatement.lean`:
`audit_isNormal_subsetLambert_of_sqrtFreshMassZero` restates the headline with every
abbreviation unwound (`IsNormal`/`IsNormalSequence`/`digitOf`, `subsetLambert`/`omegaS`,
`SqrtFreshMassZero`/`recipSumIoc`, `DivergentRecip`) — the bridge is `rfl` on the tsum.
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.  This closes item 1 of
`HANDOFF-2026-09-23-theoremC-COMPLETE.md`'s "next steps"; the campaign's hygiene is now
complete.  Remaining next steps there: (2) Astra §10 abstract consumer
`F_N = ∑_j 4^{−j} S_P(y_j, 2N) → 0`; (3) the two off-campaign designated-open `sorry`s.

## Lap 61 (2026-09-25) — `progression_log_rung_class_mult`: the new anchor reaches lap 59's conclusion

**Advance on the crux.** The merely-multiplicative route (lap 60's ESCALATE) now delivers the
SAME conclusion as `progression_log_rung_class` — the log-averaged `K`-point correlation of
`ζ^ω` over a residue class — resting on `KPointLogElliottMult K` +
`TwistedPrimeSumSavingAllLevels` alone.  `src/NormalNumbers/C3MrtMultChase.lean`,
`[propext, Classical.choice, Quot.sound]`.

The "ONE brick" named in the lap-60 handoff is discharged, and it turned out to need **no new
mathematics at all**: `class_sum_reindex` (lap 53) + `filter_linear_lt_eq_range` +
`progression_sum_bound_generic` (lap 46, deliberately generic in the modulus) compose directly.
The `ε`-budget is a single rescale `ε ↦ ε·M₀`, because the transferred weight carries `M₀⁻¹`.
Old brick 4b as stated was never needed: `weight_transfer` already sits inside
`progression_sum_bound_generic`.

**What the new route does NOT use** (and the old chase does): `truncB`/`truncA`, the `ε/2` split,
`K^{K²}`, `sqfWMass`, `multi_full_sum_bound`, `exists_common_threshold` — i.e. the whole of
`C3MrtOmegaBridge → MultiForms → MultiMass → MultiTupleMass → MultiTrunc → MultiInner →
ProgForms → ProgTrunc → ProgInner`.  The old chain stays in `src/`, sorry-free, as the
completely-multiplicative route; nothing was weakened, renamed or deleted, except the hygiene
rename `omegaNat_mul_coprime → omegaNat_mul_coprime_pos` in `C3MrtMultElliott` (it collided with
`SwingC1Katai.omegaNat_mul_coprime` once both files sat in one import closure).

**Next attack (trigger C3-T2, 5 laps left).** `TwoPointNaturalCorrelation` — Tao–Teräväinen
arXiv 2512.01739 Thm 3.1(ii) stated faithfully (1-bounded multiplicative, natural dyadic
averaging `∑_{N<n≤2N}`, `L^{-c}` saving with `1 ≤ L ≤ log X`, progression `1_{n≡b (W)}` with
`W ≤ L^c`, exceptional set `E ⊂ [√X,X]` of log-density `≪ L^{-c}`) — and the `D = 2`
**natural-density** rung derived from it, which is what discharges `LogToNaturalCorrelation`
at `K = 2`.

## Lap 62 (2026-09-25) — TT Thm 3.1(ii) stated faithfully; and the exceptional set is DECISIVE

`src/NormalNumbers/C3MrtTTThm31.lean`, sorry-free, `[propext, Classical.choice, Quot.sound]`.

* `TwoPointNaturalCorrelation` — Tao–Teräväinen arXiv 2512.01739 **Theorem 3.1(ii)** verbatim:
  1-bounded multiplicative `g₁,g₂`; `2 ≤ X`, `1 ≤ L ≤ log X`; `δ_N = 0`; the non-pretentiousness
  hypothesis (3.3) as `TTNonPretentious` (built on `ttPretentiousSum`, TT's
  `M(g; X², log^{1/125} X)`); conclusion an exceptional set `E ⊆ [√X, X]`, measurable, with the
  logarithmic density bound written as a genuine integral `∫_E t⁻¹ ≤ Cst·L^{-c}·log X`, and
  `(W/N)·∑_{N<n≤2N, n≡b (W)} g₁(n+h₁)g₂(n+h₂) ≪ L^{-c}` for `N ∈ [√X,X] \ E`,
  `W, h₁, h₂ ≤ L^c`, `h₁ ≠ h₂`.
* `c3_two_point_natural_of_TT` — the instantiation the route wants: `g_i = z_i^ω` (admissible by
  `isCoprimeMultiplicativeNat_zOmegaNat`), `h₁ = 1`, `h₂ = 2`, `W = M₀`, `b = r`.  Output: a
  **natural**-density `L^{-c}` bound on the C3 two-point correlation over a dyadic window along
  the class of `r` mod `M₀` — in the original variable, weight `1`.

### The route-decisive finding (🚦 C3-T2 verdict)

**TT Thm 3.1 does NOT discharge `LogToNaturalCorrelation 2` as that predicate is stated.**
`LogToNaturalCorrelation K` demands `Tendsto … atTop (𝓝 0)`: a bound at **every** scale.
Thm 3.1 gives it only off `E`, and a set of logarithmic density `o(1)` can contain a whole
block `[A, A^{1+δ}]` — log-mass `δ log A`, a positive proportion of `log X` at `A = X^{1/2}`.
Concretely, `E = ⋃_k [2^{k³}, 2^{k³+k}]` has logarithmic density `→ 0` while containing blocks
of ratio `2^k → ∞`; a sequence supported there tends to `0` off `E` and not at all.  This
matches TT in print (`:2997`): removing the exceptional set is out of reach.

**Consequence for the ledger — an improvement, not a defeat.**  The `D = 2` row must be split:

* `LogToNaturalCorrelationExc 2` (scale-exceptional natural-density two-point rung) — a
  **published theorem**, now formalised as `TwoPointNaturalCorrelation` and wired to the C3
  summand.  🟡.
* `LogToNaturalCorrelation 2` (every scale) — 🔴, and now *named as open in the literature*
  rather than merely unproved here.

### Next attack

1. Formalise the counterexample above as a Lean theorem (`exceptional_scales_not_tendsto`):
   a sequence `a : ℕ → ℝ`, `0 ≤ a ≤ 1`, with an exceptional exponent set of density `0`, such
   that `a → 0` off it but `¬ Tendsto a atTop (𝓝 0)`.  This turns the prose above into a
   machine-checked obstruction and is the correct way to record a refutation.
2. Then ask the *right* question: does the downstream consumer
   (`depthAvg_tendsto_of_transfer` → `weylLambertTwist_holds`) actually need every scale, or
   does a log-density-one set of scales suffice?  `weylLambertTwist_holds` is a Weyl-sum
   statement along `N → ∞`; if the reduction can be re-run over a density-one scale sequence,
   the `D = 2` layer becomes unconditional on a published theorem.  That is the highest-value
   open question on this route and it has never been asked.

## Lap 63 (2026-09-25) — the exceptional set is a THEOREM, not a worry

`src/NormalNumbers/C3MrtExcScales.lean`, sorry-free, `[propext, Classical.choice, Quot.sound]`.

`exceptional_scales_not_tendsto`: there is a set `E ⊆ ℕ` of scale-indices and a `[0,1]`-valued
sequence `a` with `a = 0` off `E`, `E` of **density zero**, `E` containing **arbitrarily long
runs**, and `¬ Tendsto a atTop (𝓝 0)`.  Witness `E = ⋃_{j≥1} [j⁴, j⁴+j)`; the counting map
`k ↦ (⌊k^{1/4}⌋, k − ⌊k^{1/4}⌋⁴)` is injective because `⌊k^{1/4}⌋ = √(√k)` recovers the block
index (`excScales_index`), giving `|E ∩ [0,K)| ≤ (√(√K)+1)² ≤ 4√K`.

So the lap-62 prose is now machine-checked: **no bound valid only off a density-zero set of
scales can produce the `Tendsto` that `LogToNaturalCorrelation K` demands**, and the long runs
kill the "interpolate between two good scales" rescue as well (a run of length `j` in the
exponent is a multiplicative block of ratio `2^j → ∞`).

**Refuted this lap — the Fubini rescue.**  For a fixed scale `N`, vary `X` over `[N, N²]` and
hope `N ∉ E(X)` for some admissible `X`.  Swapping the order in `∫_N^{N²}∫_{E(X)} dt/t · dX/X`
bounds the `X`-measure of bad `X` only *for almost every `t`*, not for the given `t`; the
exceptional set simply reappears one level up.  TT Thm 3.1 is a black box in `X`, so the
statement alone offers nothing stronger.

### Next attack — the question this route has never asked

Does the consumer actually need every scale?  `depthAvg_tendsto_of_transfer` feeds
`weylLambertTwist_holds`, a Weyl-sum statement along `N → ∞`.  Two sub-questions, in order:

1. Is `weylLambertTwist_holds` (or the normality statement above it) stable under replacing
   "for all `N`" by "for `N` in a set of scales of logarithmic density one"?  For *normality*
   the answer is expected NO (digit frequencies need every prefix), but the Weyl sum feeding it
   may be averaged, in which case a density-one scale set is enough.  **Read `SwingC3Leaf.lean`
   and the reduction above it before assuming either way.**
2. If NO: the `D = 2` row stays 🔴 and the honest ledger entry is "equivalent to removing the
   exceptional set from TT Thm 3.1", which TT state is out of reach — i.e. the C3 `D ≥ 2` route
   is pinned to a *named* open problem, which is the ratified deliverable.

## Lap 64 (2026-09-25) — the `D = 2` layer pinned to a NAMED OPEN PROBLEM; crux decomposed

`src/NormalNumbers/C3MrtNoExc.lean`.  Two proved, four disclosed `sorry`s **in `src/`** — the
crux decomposition, not a regression.

**Proved.**
* `exceptional_set_can_pin_a_scale` — the black box cannot be pushed: `{N}` is a legitimate
  exceptional set at *every* `X` (measurable, inside `[√X,X]`, logarithmic measure `0`).  So no
  argument using only the *statement* of TT Thm 3.1 — varying `X`, intersecting over `X`,
  Fubini — can produce a bound at a prescribed scale.  Together with lap 63's
  `exceptional_scales_not_tendsto` this closes the question from both sides.
* `TwoPointNaturalCorrelationNoExc` — TT Thm 3.1(ii) with `E = ∅`, i.e. **the named open
  problem** (TT `:2997`: removing the exceptional set is not within current technology) — and
  `twoPointNatural_of_noExc`, confirming it really is a strengthening.

**The ledger claim now being built** (`logToNatural_two_of_noExc`):
`TwoPointNaturalCorrelationNoExc → LogToNaturalCorrelation 2`.  If it lands, the `D = 2` layer
of `ConjC3` is *implied by* removing the exceptional set from a published theorem and by nothing
else — an equivalence with a named open problem, which is the ratified deliverable.

**The four named sub-goals** (all `sorry`-disclosed in `src/`, attack in this order):
1. `dyadic_window_bound_of_noExc` — one dyadic window at `X = N²`, `L = log X = 2 log N`
   (`N = √X` is exactly the left endpoint, so the instantiation is legal).  Bookkeeping.
2. `dyadic_decomposition` — the class below `M·J` as a disjoint union of dyadic windows plus a
   bounded head.  Bookkeeping; the stated form may need adjusting at the endpoints.
3. **`dyadic_sum_geometric`** — `∑_{i<I} 2^i (log 2^i)^{-c} ≤ D · 2^I (log 2^I)^{-c}`: the
   geometric weight concentrates the stack on its top window, so the saving survives the sum
   with only a constant loss.  The ONLY quantitative step; attack this first, it is the one that
   could fail.
4. Divide by `J`, let `J → ∞`, and note `L^{-c} → 0` because `L = 2 log N → ∞`.

**Refuted / settled, do not re-chase.**  Deriving `LogToNaturalCorrelation 2` from
`TwoPointNaturalCorrelation` *with* its exceptional set (laps 62–64: three independent
arguments — the density-zero counterexample, the long-run counterexample, and the singleton
pinning).

## Lap 65 (2026-09-25) — sub-goal 3 PROVED: the quantitative step survives

`dyadic_sum_geometric` is closed, `[propext, Classical.choice, Quot.sound]`.  This was the one
sub-goal of `logToNatural_two_of_noExc` that could genuinely have failed, so the decomposition
is now de-risked: **the `L^{-c}` saving does survive summation over the dyadic stack.**

The right statement turned out to be a limit, not a constant:

    Tendsto (fun I => (∑_{i<I} 2^i · (2 log 2^i)^{-c}) / 2^I) atTop (𝓝 0)

which is exactly what the chase needs after dividing by `J ≈ 2^I/M`, and which avoids ever
naming the constant `D`.  It is an instance of a general lemma proved this lap,
`tendsto_geom_weighted_avg`: for `a ≥ 0` with `a i → 0`, the geometrically weighted averages
`(∑_{i<I} 2^i a i)/2^I` tend to `0` — a Toeplitz kernel argument (split at `m`, head `≤ C/2^I`,
tail `≤ (ε/2)·∑2^i ≤ (ε/2)2^I`).  The kernel is reusable anywhere a dyadic stack with a
per-window saving has to be summed.

**Remaining sorries in `src/` on this crux (3):** `dyadic_window_bound_of_noExc` (one window at
`X = N²`, `L = 2 log N` — instantiation bookkeeping), `dyadic_decomposition` (the class below
`M·J` as a stack of windows; the stated endpoint form may need adjusting), and the assembly
`logToNatural_two_of_noExc`.  Both remaining sub-goals are bookkeeping; attack
`dyadic_decomposition` next, since the assembly's exact shape depends on it.

## Lap 66 (2026-09-25) — `class_sum_split` proved: sub-goal 2 down, two left

`class_sum_split` replaces the lap-64 stub `dyadic_decomposition` with the statement the
assembly actually needs, and it is proved (`[propext, Classical.choice, Quot.sound]`):

    ∑_{n < M·J + r, n ≡ r (M)} F n  =  (∑_{n < r, n ≡ r (M)} F n)  +  ∑_{m<J} F(M m + r)

i.e. the progression sum is the class sum below `M·J + r` minus a head that does not depend on
`J`, so the head dies under the `1/J` normalisation.  The bijection is `n ↦ (n−r)/M` with
inverse `m ↦ M m + r`; `M ∣ n − r` comes from `Nat.modEq_iff_dvd'`, which is the step `omega`
cannot do (truncated subtraction under a modulus).

**Remaining on this crux (2 sorries in `src/`):**
* `dyadic_window_bound_of_noExc` — instantiate `TwoPointNaturalCorrelationNoExc` at `X = N²`,
  `L = log X = 2 log N`, `W = M`, `b = r`, `h₁ = 1`, `h₂ = 2`.  `N = √X` is exactly the left
  endpoint of the admissible range, so the instantiation is legal; the work is the
  `TTNonPretentious` side condition and the `(W/N) •` normalisation.
* `logToNatural_two_of_noExc` — the assembly.  All three ingredients now exist:
  `class_sum_split` (lap 66), `sum_Ioc_pow_decomp` at `A = 2` (`C3MrtRungTwo:181`) for the
  dyadic stack, and `dyadic_sum_geometric` / `tendsto_geom_weighted_avg` (lap 65) for the sum.

Once those two land, `ConjC3`'s `D = 2` layer is implied by removing the exceptional set from
TT Theorem 3.1 — a named open problem — and by nothing else.

## Lap 67 (2026-09-25) — `dyadic_window_bound_of_noExc` proved: ONE sorry left on the crux

Sub-goal 1 is closed, `[propext, Classical.choice, Quot.sound]`.  The instantiation is legal
exactly as designed: at `X = N²` one has `√X = N` (the *left endpoint* of TT's admissible
range) and `log X = 2 log N =: L`, so `L ≤ log X` holds with **equality** — the strongest
admissible `L`, which is what makes the saving `L^{-c} = (2 log N)^{-c}` as large as the
theorem permits.  `N₀` exists only to force `L^c ≥ 2`, i.e. to make `h₂ = 2` admissible; that
is a `tendsto_rpow_atTop` one-liner.  (`Real.log_two_gt_d9` is needed for `1 ≤ 2 log N` at
`N = 2` — `nlinarith` cannot see `log 2 > 1/2` on its own.)

**The crux is now ONE `sorry`:** `logToNatural_two_of_noExc`, pure assembly, with all four
ingredients proved and in the file:

1. `class_sum_split` (lap 66) — progression sum = class sum below `M·J + r` − a `J`-independent
   head.
2. `sum_Ioc_pow_decomp` at `A = 2` (`C3MrtRungTwo:181`) — the class sum below `2^I` as the point
   `1` plus the stack of windows `(2^{i−1}, 2^i]`.
3. `dyadic_window_bound_of_noExc` (lap 67) — each window `≤ Cst·(2 log 2^i)^{-c}·2^i/M`.
4. `dyadic_sum_geometric` (lap 65) — `(∑_{i<I} 2^i (2 log 2^i)^{-c})/2^I → 0`.

Remaining care: choose `I = ⌈log₂(M J + r)⌉` so `2^I ≥ M J + r`, absorb the finitely many
windows below `N₀` into a `J`-independent constant, and note `J ≍ 2^I/M` so dividing by `J`
converts item 4's normalisation `/2^I` into `/J` up to the factor `M`, which is fixed.

## Lap 68 (2026-09-25) — the bottom-up stack is WRONG; the top-down halving stack, proved

**Design correction, found while assembling.**  The lap-64 plan said "dyadic windows
`(2^{i−1}, 2^i]`".  That is wrong, and would have wasted the next several laps.
`TwoPointNaturalCorrelation*` bounds a **full** window `(N, 2N]` and never a sub-interval, so
in a bottom-up decomposition of `[1, Y]` the top window is only partially inside `[1, Y]` and
has to be bounded trivially — at cost `≍ Y`, which destroys the entire estimate.  There is no
way to patch this while decomposing from the bottom.

**The fix: halve from the top.**  Put `N_k = Y / 2^k` and use the levels `(N_{k+1}, N_k]`.
Each level *is* a full window up to at most one point, because
`2·N_{k+1} ≤ N_k ≤ 2·N_{k+1} + 1` — a `Nat.div_div_eq_div_mul` fact.  The stray point costs `1`
per level, i.e. `≪ log Y` in total, which is `o(Y)` and therefore free.

Proved this lap (all `[propext, Classical.choice, Quot.sound]`):
* `sum_Ioc_halving_stack` — `∑_{(0,N]} F = ∑_{(0, N/2^K]} F + ∑_{k<K} ∑_{(N/2^{k+1}, N/2^k]} F`.
* `double_le_level` — `2·(N/2^{k+1}) ≤ N/2^k`.
* `level_le_double_succ` — `N/2^k ≤ 2·(N/2^{k+1}) + 1`.
* `norm_sum_level_le` — a window bound `B` plus one stray point gives `B + 1` on the level.

**Still one `sorry`:** `logToNatural_two_of_noExc`.  Revised recipe, now that the geometry is
right: with `Y = M·J + r`, take `K ≈ log₂ Y` levels down to a head `Y/2^K = O(1)`; bound level
`k` by `dyadic_window_bound_of_noExc` at `N = N_{k+1}` (legal once `N_{k+1} ≥ N₀`, and the
finitely many levels with `N_{k+1} < N₀` have total length `≤ 2N₀`, a `J`-independent constant)
plus `1`; then `dyadic_sum_geometric` sums the stack after the reindex `i = K − k`.

**Also to note:** `LogToNaturalCorrelation K` carries no `z 0 ≠ 1`, and is *false* without it
(take `z ≡ 1`), so it is only ever usable through its log hypothesis.  The theorem being built
therefore takes `z 0 ≠ 1` explicitly — which the consumer `depthAvg_tendsto_of_transfer`
already has in hand as `hζ`.  A `LogToNaturalCorrelationNZ` predicate plus the one-line
re-wiring of that consumer is a follow-up item, deliberately deferred until the analytic
content lands.

## Lap 69 (2026-09-25) — `top_down_weighted_tendsto`: the analytic heart of the assembly, proved

The one genuinely analytic ingredient the top-down stack needs is now in, sorry-free:

    Φ ≥ 0 bounded, Φ a → 0  ⟹  Tendsto (fun Y => (∑_{k<K Y} Φ(Y/2^{k+1})·(Y/2^{k+1}))/Y) (𝓝 0)

**for an arbitrary level count `K : ℕ → ℕ`** — the level count drops out entirely, because
`Y/2^{k+1} ≤ Y·2^{-(k+1)}` turns the normalised stack into a geometric average of `Φ` along
scales that all tend to `∞`.  Not having to pin `K` to `log₂ Y` removes what would have been
the fiddliest part of the instantiation.

Proof: cut at `k₀` with `G·2^{-k₀} < ε/2` (tail), and use `Φ < ε/2` on the first `k₀` levels,
legitimate once `Y ≥ A·2^{k₀}` since then `Y/2^{k+1} ≥ A` for `k < k₀`.  Supporting lemma
`geom_half_Ico` / `geom_half_Ico_le`: `∑_{k∈[a,b)} 2^{-(k+1)} = 2^{-a} − 2^{-b} ≤ 2^{-a}`.

**Inventory for the last `sorry` (`logToNatural_two_of_noExc`).**  Every ingredient is proved:
`class_sum_split` (66) · `sum_Ioc_halving_stack` + `double_le_level` + `level_le_double_succ` +
`norm_sum_level_le` (68) · `dyadic_window_bound_of_noExc` (67) · `top_down_weighted_tendsto` (69).
What remains is purely the glue: define
`Φ a = if N₀ ≤ a ∧ (M:ℝ) ≤ (2 log a)^c then Cst·(2 log a)^{-c}/M else 1`, check `Φ ≥ 0`,
`Φ ≤ max 1 (Cst·(2 log N₀)^{-c}/M)` and `Φ → 0`, take `K Y = Nat.log 2 Y + 1` so the head
`(0, Y/2^K]` is empty, and add the `K Y` stray points (`≍ log Y`, so `/Y → 0`).

## Lap 70 (2026-09-25) — `class_sum_tendsto_of_noExc`: the assembly LANDS

The analytic content of the `D = 2` layer is now proved end to end, sorry-free and trust-triple
clean.  On `TwoPointNaturalCorrelationNoExc` (TT Thm 3.1(ii) without its exceptional set), for
every modulus `M > 0` and residue `r`,

    ‖∑_{0 < n ≤ Y,  n ≡ r (M)}  z₀^{ω(n+1)} z₁^{ω(n+2)}‖ / Y  →  0

— a **natural**-density statement, not a logarithmic one.  Assembly: the halving stack
(lap 68) → the per-level window bound `Φ(a)·a` with
`Φ a = if N₀' ≤ a ∧ M ≤ (2 log a)^c then Cst(2 log a)^{-c}/M else 1` → the top-down Toeplitz
estimate (lap 69).  `Φ` is nonnegative, bounded by `1 + Cst(2 log 2)^{-c}/M` (antitonicity of
`x ↦ x^{-c}`, since every admissible `a ≥ 2`), and tends to `0`; the `≍ log₂ Y` stray points
cost `(log₂ Y + 1)/Y → 0`, via `Real.isLittleO_log_id_atTop`.

**One `sorry` left in the whole crux:** `logToNatural_two_of_noExc`, and it is now only
index bookkeeping:

    ‖∑_{m<J} F(M m + r)‖ / J  ≤  (r + 1)/J  +  (‖∑_{0<n≤Y} F'‖ / Y) · (M + r),   Y = M J + r − 1

using `class_sum_split` (lap 66) for the head, `range Y = {0} ⊔ Ioc 0 (Y−1)` for the single
extra point, `Y/J ≤ M + r`, and composing `class_sum_tendsto_of_noExc` with `J ↦ M J + r − 1`
(which tends to `atTop`).  No analysis remains.

## Lap 71 (2026-09-25) — **THE CRUX IS CLOSED.**  `logToNatural_two_of_noExc` is a theorem

`src/NormalNumbers/C3MrtNoExc.lean` is **sorry-free**.  `logToNatural_two_of_noExc` depends on
`[propext, Classical.choice, Quot.sound]` and states:

> On `TwoPointNaturalCorrelationNoExc` — Tao–Teräväinen arXiv 2512.01739 Theorem 3.1(ii) with
> its exceptional set of scales removed — together with the non-pretentiousness of `z₀^ω` in
> TT's own sense, for every `M > 0` and `r`,
>
>     (∑_{m<J} ∏_{i<2} z_i^{ω(M m + r + i + 1)}) / J  →  0.

That is the `K = 2` **natural-density** transfer: the last open obligation of the `D = 2` layer
of `ConjC3`, and precisely what the log-averaged chain provably cannot deliver.

### The deliverable, stated plainly

The `D = 2` layer of the C3/MRT route is now **equivalent to a named open problem**: removing
the exceptional set of scales from TT Theorem 3.1.  Both directions are machine-checked:

* `logToNatural_two_of_noExc` — no exceptional set ⟹ the transfer holds.
* `exceptional_scales_not_tendsto` (63) + `exceptional_set_can_pin_a_scale` (64) — with the
  exceptional set, no argument that uses only the statement can reach a pointwise limit.

And TT say in print (`:2997`) that removing it is not within current technology.

### Route ledger after this lap

* 🟢 everything from `weylLambertTwist_holds`'s reduction down to the `K`-point correlation.
* 🟢 `progression_log_rung_class_mult` (61) — the log layer, on merely-multiplicative Elliott.
* 🟡 `TwoPointNaturalCorrelation` (62) — a published theorem, stated faithfully, wired to the
  C3 summand (`c3_two_point_natural_of_TT`).
* 🔴 `TwoPointNaturalCorrelationNoExc` — the single named open problem the `D = 2` layer needs.
* 🔴 generational: `K ≥ 3` correlations (TT: "does not appear to be within current technology").

### Next

1. `TTNonPretentious (zOmegaNat z) X L` for `‖z‖ = 1`, `z ≠ 1` — bridge laps 18–21's archimedean
   certificate (in `Erdos67b.pretentiousDistSqToTwist`) to TT's `M(g; X², log^{1/125} X)`.  This
   is the last *hypothesis* of `logToNatural_two_of_noExc` not yet discharged from the repo's own
   inputs, and it is a genuine (but bounded) piece of work: matching two pretentious metrics.
2. `LogToNaturalCorrelationNZ 2` + the one-line rewiring of `depthAvg_tendsto_of_transfer`, so
   the new theorem plugs into the existing chain rather than sitting beside it.

## Lap 72 (2026-09-25) — TTNonPretentious discharged to one resonance-mass input; D=2 wired in

**Correction (item 1 of the lap-71 NEXT list).**  `TTNonPretentious (zOmegaNat z) X L` for
`1 ≤ L ≤ log X` is **FALSE**, not merely unproved.  `ttPretentiousSum (z^ω) X t =
∑_{p ≤ X²}(1 − cos(arg z − t log p))/p`, so at `t = 0` it is `(1−cos θ)(log log X + O(1))` and
`exp(M) ≍ (log X)^{1−cos θ}`.  For small `arg z` this is `≪ log X`.  The admissible range is
`L ≤ (log X)^{κ(z)}`, `κ(z) = (1−cos ε)(1 − (126/125)(ε/π))`, `ε = |arg z|/2`.

**Done.**
* `C3MrtTTPretentious.lean` (new): `ttPretentiousSum_eq_primes`, `ttPretentiousSum_ge`
  (TT's `M(g;X²,·)` IS the `q = 1` archimedean pretentious distance — the lap-18..21 resonance
  machinery applies verbatim), `ttExponent`, `ttExponent_pos`, `ttExponent_le_one`,
  `ttNonPretentious_of_uniformResonantMass`.
* `C3MrtNoExc`: the three assembly theorems now take `0 < κ ≤ 1` and `L ≤ (log X)^κ`.  The
  assembly only ever needed `L → ∞`; the consumer-visible exponent is `κ·c`.
* `C3MrtNatural`: `LogToNaturalCorrelationNZ` (the `z 0 ≠ 1` variant),
  `depthAvg_tendsto_of_classSums` (shared core), `depthAvg_tendsto_of_transfer_nz`.
  `depthAvg_tendsto_of_transfer` is unchanged as a statement and now a two-line corollary.
* `logToNaturalCorrelationNZ_two_of_noExc` and `depthAvg_two_tendsto_of_named`: the `D = 2`
  depth rung, natural density, from **exactly three** named inputs —
  `TwoPointNaturalCorrelationNoExc`, `UniformResonantMass`, `ProgressionLogRung 2`.

**The new named input, and why it is the right one.**
`UniformResonantMass`: for `‖z‖=1, z ≠ 1`, `resonantMass z t Y ≤ (ε/π)(log log Y + log(2+|t|))
+ O_z(1)`, uniformly in `t`.  `resonant_mass_le` (lap 20) proves this with the lossy
per-window bound `windowMassBound` in place of the sharp `log((γ_m+ε)/(γ_m−ε)) ≈ 2ε/γ_m`, which
is fine for the `O(T)` windows of the range `|t| ≤ T/log X` but not for TT's
`|t| ≤ (log X)^{1/125}`, where there are `≈ |t| log X` windows.

**Refuted this lap — DO NOT RETRY.**
* Summing `reciprocalPrimeInterval_le_log_ratio` per window: the dependency's Mertens error is a
  FIXED constant `2·mertensBound` with no `1/log u` decay, so `K` windows cost `K·const`.  A
  decaying-error Mertens, or Brun–Titchmarsh in short multiplicative windows, is required.
* Grouping windows dyadically in `m` (blocks `m ∈ [2^j, 2^{j+1})` sit in a single ratio-4
  interval): gives resonant mass `≤ (log 4 + 2·mertensBound)·log K`, which EXCEEDS the total
  mass `log log Y`.  Useless.
* `TwistedPrimeSumSaving` / Vinogradov–Korobov is **not** the missing input: it yields a
  constant saving, and TT's `L → ∞` needs one growing like `κ log log X`.  (Also DIRECTION-
  forbidden; not attacked.)

**Next attack on the crux.**  Either (a) prove `UniformResonantMass` from Brun–Titchmarsh —
window `m` has `p ∈ (U, U·e^{2ε/γ_m}]`, so BT gives count `≤ 2y/log y` with
`y ≈ 2εU/γ_m`, mass `≤ 4ε/(γ_m log U)`; summing over `m ≤ K` reproduces `(ε/π) log K` — or
(b) restrict the `t`-range: if the assembly can tolerate `L ≤ exp((log X)^{...})`-free small
`L`, then `|t| ≤ T/log X` suffices and `resonant_mass_le` closes it outright.  (b) is the
cheaper probe and should be tried first: check whether TT's `(3.3)` can be run with the
infimum over `|t| ≤ T/log X` only — it cannot, TT need the full range, but the *derived*
hypothesis in `dyadic_window_bound_of_noExc` might.

## Lap 74 (2026-09-25) — the crux is formalizable: Brun–Titchmarsh is already in the build

**The unlock.**  `PrimeNumberTheoremAnd.BrunTitchmarsh` is present in `.lake/packages`,
importable from a `C3Mrt*` file, and **sorry-free / axiom-clean**:

    `BrunTitchmarsh.primesBetween_le : 0 < x → 0 < y → 1 < z →
       primesBetween x (x+y) ≤ 2y/log z + 6z(1+log z)³`

This is the exact shape the resonance argument needs and the dependency's Mertens cannot give
(error proportional to the window WIDTH, not a flat additive constant).  So
`UniformResonantMass` is a formalization target, not an axiom.

**Landed.**  `C3MrtWindowMass.lean`: `window_subset_primesBetween`, and

    `short_interval_mass_le` : `2 ≤ P`, `0 < w`, `G ⊆ primes ∩ (P, P(1+w)]`
        `⟹ ∑_{p∈G} 1/p ≤ 4w/log P + 6(1 + log P)³/√P`

(Brun–Titchmarsh at level `z = √P`, divided by `P`.)  Axiom-clean.

**The remaining plan for `UniformResonantMass`** (window half-width `δ`, `γ_m = |arg z − 2πm|`,
`a_m = (γ_m−δ)/|t|`, `b_m = (γ_m+δ)/|t|`):

1. Split the resonant primes at `P₁ = max(4, |t|^4)`.
2. *Small primes* `p ≤ P₁`: mass `≤ log log P₁ + mertensBound ≤ 4 log log(2+|t|) + O(1)`, and
   `log log s ≤ c log s + O_c(1)` absorbs this into the `(2δ/π) log(2+|t|)` term for any `c>0`.
   No window structure needed — just `abs_primeReciprocals_sub_log_log_le`.
3. *Large primes* `p > P₁`: each lies in exactly one window (`windowIndex` is a function), the
   window sits in `(P, P(1+w)]` with `P = e^{a_m}`, `w = e^{b_m−a_m} − 1 ≤ 2·(2δ/|t|)`, and
   `log P = a_m ≥ (γ_m − δ)/|t|`.  `short_interval_mass_le` gives mass
   `≤ 16δ/γ_m + 6(1+a_m)³ e^{−a_m/2}`.
4. `∑_{1 ≤ |m| ≤ K} 1/γ_m ≤ (1/π)(1 + log K)` via `γ_m ≥ 2π|m| − π` and mathlib's
   `harmonic_le_one_add_log`; `K ≈ |t| log Y` gives the `(2δ/π)(log log Y + log(2+|t|))`.
5. The tail `∑_m (1+a_m)³ e^{−a_m/2}` is a geometric-type sum over `a_m ≈ 2πm/|t|`, bounded by
   `C|t|` — which again absorbs into `(2δ/π) log(2+|t|)`?  **NO** — `C|t|` is far too big.
   Handle it instead by grouping the windows into dyadic blocks in `log p`: block `j` covers
   `log p ∈ [2^j, 2^{j+1})`, holds `≤ |t|·2^j/π + 1` windows each with the SAME `P ≥ e^{2^j}`,
   so the block's tail contributes `≤ (|t| 2^j/π + 1)·6(1+2^{j+1})³ e^{−2^j/2}`, and
   `∑_j` of that is `≤ C·|t|` — still `|t|`, but `|t|·e^{−2^j/2}` summed from the FIRST block
   with `2^j ≥ 4 log(2+|t|)` is `≤ 1`, and the earlier blocks are all inside `p ≤ P₁` and so
   already counted in step 2.  This is why the split point is `P₁ = |t|^4`.

Next lap: step 2 (self-contained, `log log s ≤ c log s + O_c(1)`), then step 4 (harmonic),
then the window bookkeeping of step 3.

### Lap 75 — constant retune (forced by Brun–Titchmarsh's factor 2) + two bricks

**Constant retune.**  The BT route cannot deliver the ideal coefficient `2δ/π`: BT at level
`z = √P` costs a factor `4`, the window width bound `w ≤ 2(b−a)` another `2`, and the gap
estimate `γ_m − δ ≥ (π/2)m` another `4/π`.  The honest coefficient is `≈ 20δ`.
`UniformResonantMass` is therefore restated with the round constant **`100·δ`**, and
`ttEps z := min (resEps z) (1/256)` so that `(126/125)·100·δ ≤ 0.394 < 1` and
`κ = ttExponent z = (1 − cos δ)(1 − (126/125)·100δ) ≥ 0.6(1 − cos δ) > 0` with margin.
Everything downstream is unchanged.

**Bricks landed** (`C3MrtWindowMass`, both axiom-clean):
* `log_le_mul_sub` / `log_log_le_mul_log` — `log u ≤ c·u − 1 − log c`, the tangent-line bound
  with free slope.  This is step 2's absorption of the small-prime mass `log log P₁` into the
  `log(2+|t|)` budget.
* `sum_inv_gap_le` — `∑_{m=1}^{K} (2πm − π − δ)⁻¹ ≤ (2/π)(1 + log K)` for `0 ≤ δ ≤ π/2`, via
  `2πm − π − δ ≥ (π/2)m` and mathlib's `harmonic_le_one_add_log`.  This is step 4.

Remaining for `UniformResonantMass`: the window bookkeeping of step 3 (map each resonant prime
`p > P₁` to its `windowIndex`, fit the fibre into `(P, P(1+w)]` with `P = exp((γ_m−δ)/|t|)`,
apply `short_interval_mass_le`), then the dyadic-block treatment of the BT error tail (step 5).

### Lap 76 — step 3: `resonant_window_mass_le`

A set of primes confined to a window of length `2δ/|t|` in `log p`, starting at height
`a ≥ log 2`, carries reciprocal mass at most `16δ/(|t|·a) + 6(1+a)³·exp(−a/2)`.  Proved from
`short_interval_mass_le` plus `exp_sub_one_le_two_mul` (`exp x − 1 ≤ 2x` on `[0,1]`, from
mathlib's `Real.exp_bound` at `n = 1`) — the conversion from an additive window in `log p` to a
multiplicative window `(P, P(1+w)]` with `w ≤ 2·(2δ/|t|)`.  Hypothesis `2δ ≤ |t|` keeps `w`
in the linear regime; the complementary range `|t| < 2δ` carries `O(1)` windows and is the
existing `resonant_mass_le` (Range 1).

At `a = (γ_m − δ)/|t|` the first term is `16δ/(γ_m − δ)`, which `sum_inv_gap_le` sums to
`(32δ/π)(1 + log K)` over `1 ≤ m ≤ K` — inside the `100δ` budget with room for the `m = 0`
window and both signs of `m`.

Remaining: the window PARTITION (fibre the resonant primes over `windowIndex`, check each
fibre satisfies the `hGw` of `resonant_window_mass_le` with `a = (γ_m−δ)/|t|`), the small-prime
split at `P₁ = |t|^4`, and the dyadic-block sum of the BT error `6(1+a)³e^{−a/2}`.

### Lap 77 — the `δ`-covering

`exists_window_of_resonant_width`, `windowIndexW`, `windowIndexW_spec`, `abs_windowIndexW_le`:
the `C3MrtArchimedean` covering redone at a free half-width `δ ≤ resEps z` (forced by lap 73).
The gap `2δ ≤ |arg z − 2πm|` still comes from `two_resEps_le_abs_shift`; only the resonance
threshold moves.  Each resonant prime now has a well-defined window index, bounded by
`⌈(T + δ + π)/(2π)⌉` when `|t| log p ≤ T`.

All four pieces of the assembly are now in place:
  (i)  `resonant_window_mass_le`  — one fibre's mass,
  (ii) `windowIndexW` + `abs_windowIndexW_le` — the fibration and its index range,
  (iii) `sum_inv_gap_le` — the harmonic sum of the main terms,
  (iv) `log_log_le_mul_log` — the small-prime absorption.
Next lap: `Finset.sum_fiberwise_of_maps_to` over `Icc (−K) K`, checking the `hGw` of (i) with
`a = (γ_m − δ)/|t|` on each fibre, plus the two side conditions (`a ≥ log 2` — this is exactly
the small-prime split, since `a < log 2` forces `p ≤ exp((γ_m+δ)/|t|)` small; and the BT error
tail).

### Lap 78 — the two summation bricks

* `window_err_le` — `6(1+a)³/√(exp a) ≤ 10⁵·exp(−a/8)` for `a ≥ 0`.  The Brun–Titchmarsh error
  of `resonant_window_mass_le` decays exponentially in the window HEIGHT.  Proved from
  `exp x ≥ (1 + x/4)⁴` (four `Real.add_one_le_exp`s), no factorials.
* `sum_Icc_symm_le` — `∑_{m ∈ [−K,K] ⊆ ℤ} f|m| ≤ 2 ∑_{j ≤ K} f j` for `f ≥ 0`, by fibering
  over `Int.natAbs` (each fibre has ≤ 2 points).  This is the reindexing both the harmonic
  main-term sum (`sum_inv_gap_le`, stated over `Icc 1 K ⊆ ℕ`) and the error sum need.

**Design note recorded for the assembly.**  The small-prime cutoff is NOT `p ≥ 7`.  With
`2δ ≤ |t|` one does get `a_m ≥ log 2` as soon as `p ≥ 7`, so `resonant_window_mass_le` applies;
but its BT error term `≈ 10⁵ e^{−a/8}` summed over the `≈ |t| log Y` windows is `≈ C|t|`, which
is NOT `O(δ log(2+|t|))`.  The cutoff must be at height `A₁ ≈ 8 log(C(1+|t|))`, i.e.
`P₁ ≈ (C(1+|t|))⁸`:
* windows below `A₁`: bound their total by the mass of ALL primes `p ≤ exp(A₁+1)`, which is
  `log(A₁+1) + mertensBound ≈ log log|t|`, absorbed by `log_log_le_mul_log`;
* windows above `A₁`: `∑ e^{−a_m/8} ≤ e^{−A₁/16}·∑ e^{−a_m/16}` and the second factor is a
  geometric sum with ratio `e^{−π/(16|t|)}`, hence `≤ 1 + 32|t|/π`; `A₁ = 16 log(C(1+|t|))`
  then makes the whole error `≤ 1`.

### Lap 79 — the last two leaves before the assembly

* `sum_exp_neg_le` — `∑_{j<n} exp(−cj) ≤ 1 + 1/c` for `c > 0`, from `exp(−c) ≤ 1/(1+c)` and
  `geom_sum_eq`.  Applied with `c = π/(32|t|)` (the window spacing in the height variable)
  it gives the `1 + 32|t|/π` cost of the Brun–Titchmarsh error tail.
* `small_prime_mass_le` — any set of primes `≤ B` has mass `≤ log log B + mertensBound`.

**Everything `UniformResonantMass` needs is now proved.**  The assembly is:

    resonantMass z t Y δ
      = ∑_{m ∈ Icc(−K,K)} (mass of the fibre windowIndexW = m)          [sum_fiberwise_of_maps_to,
                                                                          abs_windowIndexW_le]
      ≤ (fibres with a_m < A₁ : all primes ≤ exp(A₁+1))                  [small_prime_mass_le]
        + ∑_{a_m ≥ A₁} (16δ/(|t| a_m) + 6(1+a_m)³/√(exp a_m))            [resonant_window_mass_le]
      ≤ log(A₁+1) + mertensBound                                          [absorbed: log_log_le_mul_log]
        + 2·(32δ/π)(1 + log K)                                            [sum_inv_gap_le, sum_Icc_symm_le]
        + 10⁵ e^{−A₁/16}·2(1 + 32|t|/π)                                   [window_err_le, sum_exp_neg_le,
                                                                           sum_Icc_symm_le]

with `A₁ := 16 log(10⁵(1 + 32|t|/π) + 2)` making the last line `≤ 2`, and
`K := ⌈(|t| log Y + δ + π)/(2π)⌉` so `log K ≤ log log Y + log(2+|t|) + O(1)`.
Regime split: `2δ ≤ |t|` for the above; `|t| < 2δ` is `resonant_mass_le` (Range 1, lap 20),
where `T = |t| log Y` is not bounded — **CHECK THIS**: for `|t| < 2δ` the windows are spaced
`2π/|t|` apart in `a`, so only `O(1 + |t| log Y)` of them meet `[2, Y]`; the honest statement is
that this branch needs the same treatment with `w = exp(2δ/|t|) − 1` no longer `≤ 2·(2δ/|t|)`.
Simplest fix: for `|t| < 2δ` use `a_m ≥ (2π|m| − π − δ)/|t| ≥ (π/2)|m|/|t| ≥ (π/4)|m|/δ`, so
only `m = 0` can have `a_m ≤ log Y` once `|t| ≤ 2δ/log Y`; the intermediate range
`2δ/log Y < |t| < 2δ` still has `≤ 1 + (2/π)|t| log Y ≤ 1 + (4δ/π) log Y` windows — and a
FLAT per-window bound (`windowMassBound`) there costs `O(δ log Y)`, which is too big.
So the `|t| < 2δ` branch must ALSO use Brun–Titchmarsh, with `w = exp(2δ/|t|) − 1` bounded by
`exp(2δ/|t|)` and the main term `4w/a_m` compared against `a_m ≥ (γ_m − δ)/|t|`.  Deferred to
the assembly lap; it is the one genuinely unresolved corner.

### Lap 80 — ARCHITECTURE CHANGE: unit blocks, not whole windows (supersedes lap 74 step 3/5)

Analysing the `|t| < 2δ` corner flagged in lap 79 shows the per-window architecture is wrong
in BOTH directions, and one architecture fixes both:

* For `|t| < 2δ` the windows are multiplicatively **wide** (`ℓ = 2δ/|t| > 1`).  Brun–Titchmarsh
  on the whole window gives `4(e^ℓ − 1)/a`, exponentially worse than the truth `log(1 + ℓ/a)`;
  the dependency's Mertens gives the truth but with a flat `2·mertensBound` per window, and
  that range can hold `≈ (δ/π) log Y` windows, costing `O(δ log Y)` — fatal.
* For `|t|` large the per-window Brun–Titchmarsh error summed over `≈ |t| log Y` windows costs
  `O(|t|)` unless the cutoff height `A₁` grows with `|t|`.

**The fix: cut every window into unit pieces in `log p`.**  Pieces are then always narrow, so
Brun–Titchmarsh is sharp on each; and their errors sit at heights spaced `≥ 1` apart, so they
sum geometrically with **no factor of `|t|`**.  Also note the resonant mass is honestly
`O_δ(1)`-bounded in the wide case: `2δ/(|t| a_m) ≤ 2δ/(γ_m − δ) ≤ 2` for `m = 0`, since
`γ_m ≥ 2δ` — the "every prime `≤ Y` is resonant" configuration really does occur (for
`log Y ≲ 2.2/δ`) and is absorbed by the `δ`-dependent constant `C`.

**Landed:** `interval_mass_le` — primes in `log p ∈ (a, a+ℓ)` with `a ≥ log 2`, `0 < ℓ ≤ 1`
carry mass `≤ 8ℓ/a + 10⁵·exp(−a/8)`.  This is `resonant_window_mass_le` with the length a free
parameter, with `window_err_le` already folded in; it is the block brick.

Revised assembly:
1. Fibre the resonant primes `p` with `log p ≥ A₁` by the pair (window index `m`, block index
   `k = ⌊log p⌋`).  Each fibre sits in an interval of length `min(1, 2δ/|t|)` at height `≥ k`.
2. Main terms: `∑ 8·len/k`, a Riemann sum for the log-log measure of the resonant set, bounded
   via `sum_inv_gap_le` after grouping the blocks of one window.
3. Errors: `∑_k n_k·10⁵e^{−k/8}` with `n_k ≤ 1 + |t|/(2π)` sub-intervals per block, summed by
   `sum_exp_neg_le` at `c = 1/8`; the `(1 + |t|/2π)` factor is killed by `A₁ ≈ 8 log(C(1+|t|))`.
4. `log p < A₁`: `small_prime_mass_le` at `B = exp A₁`, cost `log A₁ + O(1) ≈ log log|t|`,
   absorbed by `log_log_le_mul_log`.

## lap 94 (2026-09-25) — the open input cut to ONE EXPLICIT SEQUENCE

`src/NormalNumbers/C3MrtDepthInput.lean` (new, green, `[propext, Classical.choice, Quot.sound]`).

Advance on the crux: the single open statement the headline rests on is narrowed a fourth time.

    lap 90  KPointNoExcWith  cK CstK K   — every coprime-mult. bounded family, every inj. shift
    lap 93  KPointNoExcRoots cK CstK K   — ω-powers of arbitrary unimodular z, shifts i+1
    lap 94  KPointNoExcDepth b h' cK CstK K  — z i = e(h'/b^{i+1}), ¬(b:ℤ)∣h'

`KPointNoExcAt z cK CstK K` peels the `∀ z` off `KPointNoExcRoots` (`kPointNoExcRoots_iff_at`
is `Iff.rfl`), every proof of the lap-93 chain is verbatim with `h z hz` ⟶ `h`, and
`KPointNoExcDepth b h' := KPointNoExcAt (depthRoot b h')`.  Chain rethreaded:
`dyadic_window_bound_at`, `windowPhi_hwin_at`, `depthAvg_le_depth`,
`depthAvg_gen_tendsto_of_unif_depth`, `depthAvg_gen_tendsto_of_geom_slow_depth`,
`depthDiagonalSlow_of_geom_depth`, `weylLambertTwist_of_geom_input_depth`,
`conjC3_of_geom_input_depth`.  Nothing is given up: `kPointNoExcDepth_of_roots` and
`conjC3_of_geom_input_roots'` recover the lap-93 form.

FREE, for the lap-93 reason and not the lap-92 one: the consumer discharges nothing new.  The
`¬(b:ℤ)∣h'` side condition is exactly what `exists_pow_mul_not_dvd` already hands the chain, and
the archimedean certificate is still `ttNonPretentious_zOmegaNat` at `i = 0` (κ = ttExponent of
the LEADING root only — lap 92's refutation stands, and is why the input is asked at `∃ i`).

Ledger reading now: `ConjC3` holds if, for every base `b ≥ 3`, every primitive level `h'`, and
every `K`, the ONE correlation sum

    (W/N) ∑_{N<n≤2N, n≡r (W)} ∏_{i<K} e(h'/b^{i+1})^{ω(n+i+1)}

is `≤ CstKdeg m K · L^{-cKgeom c₀ θ b K}` under TT's hypotheses minus the exceptional set.  Still
🔴 at every `K` (K = 2 included) — strictly stronger than published, disclosed.

NEXT: (1) `∀ᶠ K` instead of `∀ K` — `KN N = max 1 (depthSlow b N - v) → ∞`, so add
`hKNtop.eventually hin` to the `filter_upwards` in `depthAvg_gen_tendsto_of_unif_depth` and
thread up.  (2) then the `Statement.lean` audit surface + ledger writeup (trigger C3-T6).

## lap 95 (2026-09-25) — the input needed only at LARGE `K`

`src/NormalNumbers/C3MrtEvtInput.lean` (new, `lake build NormalNumbers.C3MrtEvtInput` green at
9010 jobs, `lake build` green at 9257; all new declarations `[propext, Classical.choice, Quot.sound]`).

Fifth narrowing of the one open statement:

    lap 94  ∀ K,            KPointNoExcDepth b h' cK CstK K
    lap 95  ∀ᶠ K in atTop,  KPointNoExcDepth b h' cK CstK K

`conjC3_of_geom_input_evt` is the headline.  Mechanism: the chain evaluates the input only at
`K = KN N = max 1 (depthSlow b N - v)`, and `tendsto_KNslow_atTop` shows `KN → ∞`; in
`depthAvg_gen_tendsto_of_unif_evt` the input is already applied inside a `filter_upwards`, so
`hKNtop.eventually hin` simply joins that list.  A `Tendsto … (𝓝 0)` conclusion cannot see
finitely many `N`, so every fixed `K` is dispensable.  `conjC3_of_geom_input_depth'`
(`Filter.Eventually.of_forall`) confirms nothing is given up.

Ledger consequence: **no small-`K` rung is assumed at all** — in particular `K = 2`, the only
rung anywhere near the literature (TT Thm 3.1(ii)), is now unused by the headline.  The open
statement is purely asymptotic in the number of correlation points, on one explicit family.
This also sharpens the honest disclosure: the gap to print is not "we assume a published rung
without its exceptional set" but "we assume the large-`K` regime, which print does not reach at
all" (TT: triple correlations "not within current technology").

NEXT: the `Statement.lean` audit surface + ledger writeup (trigger C3-T6 — five narrowings in
laps 90–95, so the reduction is at or near FINAL).

## lap 96 (2026-09-25) — the open input is now ONE EXPLICIT INEQUALITY

`src/NormalNumbers/C3MrtDyadicInput.lean` (new; `lake build NormalNumbers.C3MrtDyadicInput`
green at 9011 jobs, `lake build` green at 9257; all new declarations
`[propext, Classical.choice, Quot.sound]`).

Sixth narrowing, and the one that removes the last analytic quantification.  `KPointNoExcDepth`
still carried TT Thm 3.1 machinery the consumer was choosing itself: the scale `X`, the cutoff
`L`, the range `√X ≤ N ≤ X`, and the hypothesis `∃ i, TTNonPretentious (zOmegaNat (z i)) X L`.
`dyadic_window_bound_at` always picks `X = N²`, `L = (2 log N)^κ`, and discharges the archimedean
hypothesis itself at `i = 0` (`ttNonPretentious_zOmegaNat`, unconditional).  So all of it peels:

    DepthDyadicBound b h' κ cK CstK K :=
      ∀ N ≥ 2, max 2 (K+1) ≤ (2 log N)^{κ·cK K} → ∀ M r, 0 < M → M ≤ (2 log N)^{κ·cK K} →
        ‖∑_{N<n≤2N, n≡r (M)} ∏_{i<K} e(h'/b^{i+1})^{ω(n+i+1)}‖
            ≤ CstK K · (2 log N)^{-κ·cK K} · N / M

Headline `conjC3_of_dyadic_input`, with `κ = ttExponent (depthRoot b h' 0)` — not a free
parameter but the archimedean saving of the LEADING root, exactly the quantity lap 92 proved
cannot be shared across factors.  `depthDyadicBound_of_depth` IS `dyadic_window_bound_at`, and
`conjC3_of_geom_input_evt'` recovers lap 95, so nothing is given up.

The full reduction, laps 90→96:

    ConjC3 ⇐ ∀ b ≥ 3, ∀ h' with ¬(b:ℤ)∣h', ∀ᶠ K in atTop,
               DepthDyadicBound b h' (ttExponent (depthRoot b h' 0)) (cKgeom c₀ θ b) (CstKdeg m) K

for every 0 < θ < 1.  No multiplicative function, character, pretentiousness notion, auxiliary
scale, threshold, schedule or budget layer remains in the hypothesis — one explicit
exponential-sum bound, indexed by (b, h', K).

Still 🔴 and still strictly stronger than print (large-`K` regime; TT: triple correlations "not
within current technology").

NEXT: `Statement.lean` audit surface + ledger writeup (trigger C3-T6; six narrowings in laps
90–96, so the reduction is FINAL unless the audit pass finds slack).

## lap 97 (2026-09-25) — the AUDIT SURFACE (trigger C3-T6 served)

`src/NormalNumbers/C3MrtStatement.lean` (new; tip green at 9014 jobs, `lake build` green at
9257; both declarations `[propext, Classical.choice, Quot.sound]`).

`audit_conjC3_of_dyadic_input` restates the lap-96 headline with EVERY abbreviation of the chain
unwound — no `ConjC3`, `IsRich`, `WeylLambertTwist`, `DepthDyadicBound`, `depthRoot`, `ee`,
`omegaNat`, `cKgeom`, `CstKdeg` or `Filter.Eventually`.  An auditor reads only
`Nat.primeFactors`, `Complex.exp`, `Real.log`, `Real.exp`, an rpow, a `tsum`, `⌊·⌋`,
`Int.fract` and a `Finset.card` density.  It went green first try, which is itself the
faithfulness check: Lean accepted `exact hK₀ …` against `DepthDyadicBound` and the conclusion
against `ConjC3` BY DEFEQ, so the unwinding is not a paraphrase.

One honest gap is documented in the file: the audit form quantifies `∀ κ ∈ (0,1]` where the sharp
theorem needs only `κ = ttExponent (depthRoot b h' 0)`.  That assumes strictly MORE, and is done
only to keep `ttEps` / `resEps` off the audit surface.  `conjC3_of_dyadic_input` remains the
sharp statement.

`dyadic_threshold_satisfiable` checks the surface is not vacuous: for every `K` and every `s > 0`
the threshold `max 2 (K+1) ≤ (2 log N)^s` holds for all large `N`, so the bound is asserted about
genuinely many sums, not an empty range of `N`.

Ledger text written into the file header: 🔴 OPEN, strictly stronger than print at every `K`
(`K = 2` included), needed only in the large-`K` regime which print does not reach at all.

STATE: the reduction is FINAL in the sense of C3-T6 — laps 90–97 produced six successive
narrowings plus the audit surface.  Remaining honest work on the crux is to attack
`DepthDyadicBound` itself (an explicit exponential-sum bound, now in a form where it can be
attacked or refuted), not to narrow it further.

## lap 98 (2026-09-25) — WHERE the crux has content, and where it is free

`src/NormalNumbers/C3MrtDyadicContent.lean` (new; tip green at 9012, `lake build` green at 9257;
all three declarations `[propext, Classical.choice, Quot.sound]`, no new sorry).

First lap ATTACKING `DepthDyadicBound` rather than narrowing it.  Before trying to prove it, map
which instances are assumptions and which are already theorems.  Write the saving factor
`dyadicFactor cK CstK κ K N = CstK K · (2 log N)^{-κ·cK K}`.

1. `dyadic_ineq_of_trivial` — **PROVED**: if `M ≤ dyadicFactor` the asserted inequality holds
   unconditionally, from `‖∑‖ ≤ #(Ioc N (2N)) = N` alone.  So the content of the crux lives
   entirely in `dyadicFactor < M ≤ (2 log N)^{κ·cK K}`; everything else is free.  (This is the
   lemma to keep in mind before believing any future "proof" of the crux: it must engage
   `M > dyadicFactor`.)
2. `dyadicFactor_ge_one_of_small_scale` — **PROVED**: whenever `(2 log N)^{κ·cK K} ≤ CstK K` the
   factor is `≥ 1`, so (as `M ≥ 1`) the instance is free.  The threshold hypothesis does NOT
   exclude this: it only demands `K+1 ≤ (2 log N)^{κ·cK K}`, and `CstKdeg m K = exp((K+1)^m)`
   dwarfs `K+1`.  So `DepthDyadicBound` at a fixed `K` is trivial on an initial stretch of its
   admissible `N` and content-bearing only for `log(2 log N) > (K+1)^m b^{θK}/(κ c₀)`.
3. `dyadicFactor_tendsto_zero_at_diagonal` — **PROVED**: along the diagonal
   `K = KN N ≤ depthSlow b N`, geometric profile, `θ < 1`, the factor `→ 0`.  So the reduction
   consumes the crux precisely in its content-bearing range and is NOT extracting `ConjC3` from
   free instances.

Ledger consequence (honest, and new): the assumption is neither vacuous (lap 97
`dyadic_threshold_satisfiable`) nor trivially true where used (3), but it IS trivially true on
part of its stated range (1,2).  A sharper future form could restrict `DepthDyadicBound` to
`M > dyadicFactor` — a seventh free narrowing, cheap given (1).

NEXT on the crux: (a) restrict the input to `M > dyadicFactor` (free, from `dyadic_ineq_of_trivial`);
(b) the real attack — the truncation structure.  `∏_{i<K} e(h'/b^{i+1})^{ω(n+i+1)}` has deep
factors within `O(b^{-i})` of 1, so for `i₀ ≍ δ·log log N` the tail product is `1 + O((log N)^{-δ})`
on average; the K-point sum reduces to an `i₀`-point sum.  This does NOT collapse to bounded `K`
(i₀ still grows), which is exactly lap 87's finding, but it may reduce the needed `K`-range to
`K ≲ log_b log log N` — worth formalizing as the next narrowing, and it is the structural reason
the route needs uniformity in `K` at all.

## lap 99 (2026-09-25) — the TRUNCATION route, made quantitative and REFUTED

`src/NormalNumbers/C3MrtTruncate.lean` (new; tip green at 9013, `lake build` green at 9257;
all six declarations `[propext, Classical.choice, Quot.sound]`, no sorry).

The hope after lap 92 ("the deep depth roots are almost pretentious, i.e. within `O(b^{-i})` of
1") is that the deep factors of `∏_{i<K} e(h'/b^{i+1})^{ω(n+i+1)}` can be DISCARDED, truncating
the `K`-point problem to an `i₀`-point one with `i₀ ≪ K`.  This lap makes that quantitative and
the numbers refute it.

PROVED this lap:
* `norm_ee_sub_one_le` — `‖e(y) − 1‖ ≤ 4π|y|` for all real `y`, unconditionally (the large-`|y|`
  branch via `‖e(y) − 1‖ ≤ 2`).
* `depth_prod_eq_ee` — the depth product IS one additive character:
  `∏_{i<K} e(h/b^{i+1})^{ω(n+i+1)} = e(∑_{i<K} ω(n+i+1)·h/b^{i+1})`.
* `depth_prod_truncate_norm_le` — per `n`, truncating at `i₀ ≤ K` costs
  `≤ 4π|h| ∑_{i₀≤i<K} ω(n+i+1)/b^{i+1}`.
* `norm_sum_le_norm_sum_add`, `truncate_sum_le` — the same over any index set, symbolically.
* `truncate_sum_explicit_le` — geometric tail collapsed, `ω ≤ log₂`:
  cost `≤ 8π|h|·#S·log₂W·b^{−(i₀+1)}` when `n + K ≤ W` on `S`.
* `dyadic_truncate_explicit_le` — the dyadic-window instance: cost
  `≤ 8π|h|·N·log₂(2N+K)·b^{−(i₀+1)}`.

**REFUTATION (do not retry).**  At the diagonal the target saving is
`(2 log N)^{-κ c₀ b^{-θK}}`; with `b^K ≍ Λ := log log N` that is `≍ exp(−κc₀Λ^{1−θ})`.  The
truncation cost above is `≍ N·(log log N)·b^{−i₀}`, which drops below the target only once
`i₀ ≳ Λ^{1−θ}/log b`.  But the diagonal has `K ≍ log_b Λ`, and `Λ^{1−θ} ≫ log Λ` for EVERY
`θ < 1`.  So the required truncation depth EXCEEDS `K` itself, exponentially.  The deep factors
cannot be dropped at any depth below `K`, in either direction (the same estimate bounds
`‖S_K − S_{i₀}‖` both ways).  Hence:
 - lap 92's "the deep digits are almost pretentious" does NOT give "the deep digits are
   negligible" — those are different statements, and only the first is true;
 - the `K`-point problem does not reduce to a shallower one, which is the quantitative mechanism
   behind lap 87's finding that fixed-`K` limits cannot reach the diagonal;
 - genuine uniformity in `K` is not a convenience of this route but forced.

NEXT on the crux: with truncation refuted, the remaining honest attacks on `DepthDyadicBound` are
(a) the free narrowing to `M > dyadicFactor` (lap 98 item 1), and (b) the `K`-fold Halász/Elliott
input itself — i.e. accept that the open statement is a genuine large-`K` correlation bound and
work on the ledger/writeup rather than expecting a reduction to collapse it.

## lap 100 (2026-09-25) — the crux is ONE WEYL SUM, and its sharp (content-bearing) form

`src/NormalNumbers/C3MrtPhaseForm.lean` (new; tip green at 9014, `lake build` green at 9257; all
four declarations `[propext, Classical.choice, Quot.sound]`, no sorry).

**(a) Reformulation — a second attack surface.**  `depthPhase b K n := ∑_{i<K} ω(n+i+1)/b^{i+1}`
and `depth_prod_eq_ee_phase` give `∏_{i<K} e(h'/b^{i+1})^{ω(n+i+1)} = e(h'·depthPhase b K n)`.
Hence `depthDyadicBound_iff_phase`:

    DepthDyadicBound b h' κ cK CstK K  ↔  DepthPhaseBound b h' κ cK CstK K

an **IFF**, not an implication.  So the open statement is NOT intrinsically a `K`-fold Elliott
correlation: it is exactly the quantitative equidistribution mod 1 of the single real sequence
`n ↦ h' · depthPhase b K n` along dyadic windows in arithmetic progressions.  The `K`-fold
correlation shape is one route to it (TT's), and lap 99 showed that route cannot be shortened by
truncation.  The Weyl form is a genuinely different attack surface: classical exponential-sum
technology applies to it without any correlation decomposition.  Worth noting what `depthPhase`
IS — the base-`b` digit tail weight of the prime Lambert constant, i.e. the very object
`C3MrtShape.ee_tailDepth_eq_prod` introduced from the other direction.  The crux and the
conjecture are the same equidistribution statement seen at two scales.

**(b) Seventh free narrowing — the sharp form.**  `DepthDyadicBoundNT` adds the hypothesis
`dyadicFactor cK CstK κ K N < M`, i.e. asks the bound only where lap 98 did not already prove it.
`depthDyadicBound_of_nt` recovers the full statement by case split on
`dyadic_ineq_of_trivial`; `conjC3_of_dyadic_input_nt` is the headline.  Every remaining instance
now asserts cancellation strictly beyond the trivial estimate — the crux carries no free
instances at all.

Narrowing ledger, laps 90→100: threshold discharged → ω-powers → one explicit sequence →
primitive levels → large `K` only → one explicit inequality → content-bearing range only, plus
the Weyl-sum reformulation.  Refuted along the way: the `∀ i` weakening (92) and truncation (99).

NEXT on the crux: attack `DepthPhaseBound` by exponential-sum methods (the point of (a)).  The
first concrete probe: `depthPhase b K n` is a positive-coefficient linear form in
`ω(n+1),…,ω(n+K)` with geometrically decaying weights, so its distribution is governed by the
joint distribution of `ω` at consecutive shifts — the same wall, but now approachable by a
van-der-Corput / Weyl-differencing argument on the PHASE rather than a correlation bound on the
product.  Test whether one differencing step reduces the `K`-shift phase to a shorter one; if it
does, that is the first genuine crack.

## lap 101 (2026-09-25) — the depth phase is a PERTURBED ×b ORBIT (exact identity)

`src/NormalNumbers/C3MrtPhaseDynamics.lean` (new; tip green at 9015, `lake build` green at 9257;
both declarations `[propext, Classical.choice, Quot.sound]`, no sorry).

Following lap 100's Weyl-sum reformulation, the dynamics of the phase sequence turn out to be
EXACT, not approximate.  `depthPhase_succ`, valid for every `K` including `K = 0`:

    depthPhase b K (n+1) = b · depthPhase b K n − ω(n+1) + ω(n+K+1)/b^K

`depthPhase` reads the string `ω(n+1),…,ω(n+K)` as a base-`1/b` expansion, so `n ↦ n+1` is the
base-`b` SHIFT on that string: multiply by `b`, drop the leading digit `ω(n+1)`, feed the new deep
digit `ω(n+K+1)` in at weight `b^{-K}`.  The dropped digit is an integer times `h'`, hence
invisible to the character (`ee_depthPhase_succ`):

    e(h'·depthPhase b K (n+1)) = e(b·h'·depthPhase b K n + h'·ω(n+K+1)/b^K)

**Content.**  Mod 1 the phase sequence is an orbit of the EXPANDING map `x ↦ b·x`, perturbed at
each step by `≤ |h'|·ω(n+K+1)/b^K`.  So the C3 crux is not an arbitrary equidistribution
question: it asks that a perturbed `×b` orbit equidistribute.  That is exactly the "casting out"
dynamics this namespace is named for, now reached from the correlation side — and it explains
structurally why the depth schedule must satisfy `b^K ≍ log log N`: the per-step perturbation is
`≍ ω/b^K`, and the route lives or dies on that against the target saving.

Caution recorded: the perturbation is NOT negligible in lap 99's refuted sense — summed over a
window of length `N` it is `≍ N·log log N/b^K`, which at the diagonal is `≍ N`, not `o(N)`.  The
recursion is a structural identity to EXPLOIT, not an error term to discard.  Any future argument
that treats it as small is repeating lap 99's refuted move.

NEXT on the crux: exploit the recursion rather than bound it.
(i) The `×b` self-similarity relates the Weyl sum at scale `N` to one at scale `N` with phase
    multiplied by `b` — i.e. a relation between `DepthPhaseBound` at `h'` and at `b·h'`, since
    `e(b·h'·x) = e(h'·x)^b` is the character at the SHIFTED level.  Test whether iterating gives a
    closed relation on the family `{h' , b h', b² h', …}` — note `b^v h'` is exactly the
    non-primitive level the chain strips via `exists_pow_mul_not_dvd`, so this may connect the
    primitivity reduction to the dynamics.
(ii) Failing that, van der Corput on the phase, using the recursion to compute the differenced
    phase `depthPhase b K (n+h) − depthPhase b K n` in closed form.
