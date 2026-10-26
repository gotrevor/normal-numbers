# ON-LINE-FINDINGS 2026-10-26 — DFI restricted to the cutoff-six Chebotarev set

**Request** (`ON-LINE-REQUEST.md`, 2026-10-26, route 2): a published equidistribution theorem for
roots ν/p of x²+64x+4096 to prime moduli, restricted to p ≡ 1 mod 120 with 2 not a sixth power
mod p; candidates Tóth (IMRN 2000) and Duke–Friedlander–Iwaniec (Annals 1995).

**Sources read** (PDFs symlinked under `papers/`, stored in `~/personal/papers/`):
- W. Duke, J. B. Friedlander, H. Iwaniec, *Equidistribution of roots of a quadratic congruence to
  prime moduli*, Ann. of Math. 141 (1995), 423–441
  (`papers/duke-friedlander-iwaniec-1995-roots-quadratic-congruence-prime-moduli.pdf`).
  Read: §1 (statement, remarks, Propositions 1–2), and the text searched for any restriction remark.
- H. T. Ngo, *On roots of quadratic congruences*, arXiv:2107.13301 (Bull. LMS 2024), §1 literature review
  (`papers/ngo-2024-roots-quadratic-congruences.pdf`).
- E. Musicantov, S. Zehavi, *Sectorial equidistribution of the roots of x²+1 modulo primes*,
  arXiv:2112.07494v2 (2022), abstract + §1 (`papers/musicantov-zehavi-2022-sectorial-roots-x2plus1.pdf`).
- Web searches for ray-class / Chebotarev / arithmetic-progression / Hecke-character restrictions of
  DFI (several phrasings, 2026-10-26).  No hit.

## Answer: no citable theorem found.  `RestrictedRootFar` stays a conjecture node.

1. **DFI 1995 covers our polynomial over ALL primes, with no restriction.**  Their Theorem (p. 424):
   for f(X) = aX² + 2bX + c ∈ ℤ[X] with D = ac − b² > 0 ("positive determinant", i.e. negative
   discriminant) and each fixed h ≠ 0,
   Σ_{p≤x} Σ_{ν mod p, f(ν)≡0 (mod p)} e(hν/p) = o(π(x)), hence the fractions ν/p are equidistributed.
   For x² + 64x + 4096: a = 1, b = 32, c = 4096, D = 4096 − 1024 = 3072 > 0.  So `DFIWeak` is a
   faithful weakening of DFI (the "Transcription: faithful-or-weaker" label in
   `ReservoirCutoffSixDFI.lean` is correct).  The paper has no remark about primes in arithmetic
   progressions, ideal/ray classes, or Chebotarev sets.  The method does already use Γ₀(q) for the
   linear forms of Proposition 1 (p. 427: "generalization to Γ₀(q) goes straight along the lines of
   [DI]"), which is why a congruence-restricted version is *plausibly within the method*.  That is a
   judgement, not a source.
2. **Tóth, IMRN 2000(14), 719–739 is the positive-discriminant analogue** (Ngo §1: "Tóth [19] …
   established the analogous theorem for an irreducible quadratic polynomial of positive
   discriminant").  It does not apply here.
3. **Closest published restriction:** Musicantov–Zehavi prove DFI equidistribution for x²+1
   restricted to primes p = a² + b² whose lattice point (a, b) lies in an angular *sector* (via
   Poincaré series on Γ\SL₂(ℝ)).  That is a restriction on the prime's representation, but by angle,
   not by congruence class, and only for disc −4.  Not citable for our set.
4. **DFI over all primes does not imply the restricted statement by counting.**  Among primes with
   roots (p ≡ 1 mod 3) the target set S = {p ≡ 1 mod 120, 2 not a cube} has relative density
   (1/16)·(2/3) = 1/24, while DFI only says the far set has density ~1/2.  Both are consistent with
   S avoiding it.

## A reformulation the box can formalize (host-checked numerically, derivation below)

Write p = a² + 3b² (a, b > 0, unique since p ≡ 1 mod 3).  Then:

- **Gauss's cubic criterion in these coordinates:** 2 is a cube mod p ⇔ p = x² + 27y² ⇔ 3 | b.  So
  S = {p = a² + 3b² prime : p ≡ 1 mod 120, 3 ∤ b}, i.e. **congruence conditions on (a, b) only**
  (a ray-class condition in ℚ(√−3)).
- **The exit root in lattice coordinates:** with ā the inverse of a mod b, and for one of the two
  roots ν ∈ {64ω, 64ω²} mod p,
  ν/p ≡ −32·ā/b + 32(a − b)/(b·p)  (mod 1),  so  | ‖ν/p‖ℤ − ‖32ā/b‖ℤ | ≤ 32/(b√p) + 32/p.
  (The other root is −64 − ν, whose ‖·‖ℤ differs by at most 64/p.)
  Derivation: a² ≡ −3b² gives √−3 ≡ a·b̄, so 64ω ≡ 32(a − b)·b̄ (mod p).  Reciprocity
  b̄_p/p + p̄_b/b ≡ 1/(bp) (mod 1), together with p ≡ a² (mod b) (so p̄_b ≡ ā²) and
  (a − b)ā² ≡ ā (mod b), gives the display.
- **Hence a sufficient, purely lattice-point node** (suggested name `LatticeRootFar`): for every N
  there is a prime p = a² + 3b² > N with p ≡ 1 mod 120, 3 ∤ b, b ≥ 2, and ‖32·ā/b‖ℤ ≥ 3/8.  For p
  large the error is < 1/8, so this gives `RestrictedRootFar`.  It makes the content explicit:
  primes represented by a² + 3b² with (a, b) in a Kloosterman-twisted set of density ~1/2 in each
  fibre.  That is exactly the bilinear-form problem DFI solve without congruence conditions.  The
  reformulation clarifies the node; it does not make it easier.

**Finite evidence, not proof** (`scripts/pi_route2_dfi_reduction_probe.py`, primes p = 120t+1 < 4.8·10⁶):
- 6953 primes with 2 not a cube;
- 0 mismatches with Gauss's criterion;
- 0 exits that fail to be a root;
- the maximum observed error, normalised by 32/(b√p), is 0.996, so the bound holds;
- 3358 (48.3%) have ‖exit‖ℤ ≥ 1/4, consistent with equidistribution.

## Recommendation for the lane

- Keep `RestrictedRootFar` as an **open conjecture node**: true with ~97% confidence (heuristic plus
  finite evidence).  It must not become a cited literature `Prop`: no source states it.  Label it
  "expected from DFI's method with congruence-subgroup twists; not found in print (2026-10-26
  search)."
- My confidence that a published proof exists and this search missed it: ~25%.  The most likely
  form would be an ideal-class or ray-class version of DFI for imaginary quadratic fields, or a
  thesis chapter.  A search result named a 1997 Rutgers thesis by Á. Tóth under Duke, titled
  "Equidistribution of Roots of Quadratic Congruences".  That is unverified (the genealogy page
  returned 404) and unread.
- `DFIWeak` stays as stated: a faithful weakening of DFI 1995, Theorem (p. 424).
- Optional Lean work: the `LatticeRootFar → RestrictedRootFar` edge and the Gauss-criterion step.
  Gauss's cubic criterion is classical, so enter it as a named hypothesis `Prop` unless an edge
  forces a proof.
- None of this touches π's digits.  As the brief notes, the exits move R − S only.
