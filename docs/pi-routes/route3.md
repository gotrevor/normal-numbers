# Route 3 (disk residues): answer and false starts

**Answer (Lean, `DiskResidueCostume.lean`):** the route premise is sandwiched between two pure π-orbit
window covers differing only in target margin:
`PiOrbitWindowCover → DiskResidueCover → PiOrbitWindowCoverWide`
(`diskResidueCover_of_piOrbitWindowCover`, `piOrbitWindowCoverWide_of_diskResidueCover`).
The lattice enters only through the vanishing shadow error (`diskPhase_sub_le`, constant 5).

**Review, 2026-10-26:** this sandwich certifies the intended quantitative
reformulation; it is not a no-go theorem for estimating the integer counts.
The accurate status is "no new arithmetic estimate obtained."  In particular,
the periodic-orbit observation below fixes D first; it does not establish a
uniform obstruction to choosing D as a function of n.  The mathematical
difficulty remains, but these implications do not prove that a new estimate
on the explicit floor sums cannot help.

Independent axiom checks of the shadow, transfer, both sandwich edges, and
`diskSmallPart_orbit` returned only `propext`, `Classical.choice`, and `Quot.sound`;
an intentional sorry control returned `sorryAx`.

## False starts
| Idea | Why promising | Why it fails | Witness |
|---|---|---|---|
| Area/perimeter control alone gives digit coverage | lane brief; square-count control behaves differently | residue/8^n shadows fract(2^nπ), so the area estimate transfers a cover but supplies none | `diskPhase_sub_le`, sandwich theorems; probe `scripts/pi_route3_residue.py` (scaled error 0.002 at n=11) |
| Small-d part of the χ₄ divisor identity is explicit and analysable | finite, explicit floors ⌊16^n/d⌋ | it is the orbit of 2^n·4L_D, L_D a rational Leibniz partial sum: periodic, no π content; π lives in the tail d > D, which is the digits of π again | `diskSmallPart_orbit` |

Reopen condition: an estimate on the tail floor errors Σ_{d>D} χ₄(d){16^n/d} mod 8^n that is not a
restatement of 2^n·π mod 1 (none known).
