# HANDOFF 2026-10-10 — operator gate 4, lap 4

Branch `proof/uniformbad-threshold`.

## Done
- **Operator blocker (h) fixed**: `binLo`/`binHi` outward ownership in all four float kernels; the review
  TODO in `shared3_lap2_review_test.js` is a real passing test (`CC=leanc node --test ...`: 3/3; box has no `cc`).
- **Exact integer certificate** (`scripts/cstar_models/exact3.c`, new kernel, supersedes the float ones):
  fixed point 2^-90 (__int128), delta3 enclosure [dlo,dhi] checked exactly against 3^-449/100, dyadic rho-bin
  edges (`exact3_edges449.txt`), Good449 semantics (closed windows, strict zones, ambiguous resolution = min of
  both interpretations), SFT sft449 (= minimal forbidden words of Forb2 exactly, `forb2_check.js`).
  growth 9/5, c=4.49, D=6, N=128, M=24: certificate, 74431/76800 positive. Frozen weights
  `W449_N128_M24_D6.txt.gz`; read-only `exact3 128 24 6 16 check W` PASSED (5.9 s), mutation control FAILS.
  Control growth 37/20 decays. Root entry weight 1 (`entry_exact.py`); cells k=1..4 can take weight 0.
- Lean: `acc2_succ` (Acc2 is a suffix condition). Crux confidence raised to 75%.

## Next (crux = `cleanCertificate449`)
1. Lean classify: k=0 root state; k=1..4 zero state; k>=5 Good cells -> (SFT state, floor(N frac(3^n a/2^k)),
   rho-bin via exact3 edges); non-Good -> zero state. Weight = W/maxW.
2. SFT soundness: SFT-run alive => Acc2 (via acc2_succ + decide on 25 states x suffixes).
3. Port exact3's `go`/`bb` to Lean over Int (computable), prove `go` is a lower bound for the sum over Good
   descendants (the main soundness lemma), then native_decide the check over 76800 bins (C: 3.9M boxes).
4. Root: Good level-6 cells, direct computation.
