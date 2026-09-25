import NormalNumbers.ElliottZetaModerate

/-!
# Audit surface for the moderate-band `ζ'/ζ` bound

**Why this is a separate audit file.**  `NormalNumbers.ElliottAxiomAudit` transitively imports
`PrimeNumberTheoremAnd.Sobolev` (through the `Erdos67b` tree), which declares `CS.deriv`; so does
`PNTPort.Sobolev`, which `PNTPort.ZetaBounds` needs.  The two cannot sit in one environment
(`import PNTPort.Sobolev failed, environment already contains 'CS.deriv'`).  Everything reachable
from `PNTPort.ZetaBounds` is therefore audited here instead.

Green for this repo now means THREE builds:
`lake build`, `lake build NormalNumbers.ElliottAxiomAudit`, `lake build
NormalNumbers.ElliottZetaModerateAudit`.
-/

#print axioms NormalNumbers.ElliottZetaModerate.exists_midband_bound
#print axioms NormalNumbers.ElliottZetaModerate.exists_highband_bound
#print axioms NormalNumbers.ElliottZetaModerate.exists_moderate_logDeriv_bound

-- the upstream inputs, for provenance
#print axioms LogDerivZetaBndUnif99
#print axioms ZetaZeroFree9
