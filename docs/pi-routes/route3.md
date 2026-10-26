# Route 3 (disk residues): answer and false starts

**Answer (Lean, `DiskResidueCostume.lean`):** the route premise is sandwiched between two pure π-orbit
window covers differing only in target margin:
`PiOrbitWindowCover → DiskResidueCover → PiOrbitWindowCoverWide`
(`diskResidueCover_of_piOrbitWindowCover`, `piOrbitWindowCoverWide_of_diskResidueCover`).
The lattice enters only through the vanishing shadow error (`diskPhase_sub_le`, constant 5).

## False starts
| Idea | Why promising | Why it fails | Witness |
|---|---|---|---|
| Quadratic boundary of the disk gives arithmetic beyond π's digits | lane brief; square-count control behaves differently | residue/8^n is fract(2^nπ) up to 5/2^n; the boundary is only error | `diskPhase_sub_le`, sandwich theorems; probe `scripts/pi_route3_residue.py` (scaled error 0.002 at n=11) |
| Small-d part of the χ₄ divisor identity is explicit and analysable | finite, explicit floors ⌊16^n/d⌋ | it is the orbit of 2^n·4L_D, L_D a rational Leibniz partial sum: periodic, no π content; π lives in the tail d > D, which is the digits of π again | `diskSmallPart_orbit` |

Reopen condition: an estimate on the tail floor errors Σ_{d>D} χ₄(d){16^n/d} mod 8^n that is not a
restatement of 2^n·π mod 1 (none known).
