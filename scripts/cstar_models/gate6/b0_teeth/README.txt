exact5b0 teeth (2026-10-12, small instance 128 24 3 0 6 3 W181, MAXB5=3, 4 threads)
1. ROOT ACCEPTANCE.  RESUME from an all-zero PHI (20800 zeros, no exceptions):
   exact5z  -> "iter 1: failing pairs 0 ... max phi 0" then "EXACT PRODUCT+EXCEPTION CERTIFICATE growth 9/5" (exit 0)  [the bug]
   exact5b0 -> "root: ... positive weight 0 ... RS 0" then "REJECTED: no failing pair but root weight 0" (exit 3)
   exact5b0 check zero.phi -> "CHECK REJECTED: root weight 0" (exit 3)
   control: exact5b0 check (all PHI = 2^20) -> root good cells 2554/4096, positive 2508, RS 1.953e21 > 0.
   independent count: good12.py (exact Fractions, same dyadic delta enclosure) -> 2554 good level-12 cells.
2. MODE EQUIVALENCE.  Full pass 0 with CKPT, z mode and B0=1: iter line, phi.0.txt, ex.0.txt byte-identical
   to exact5z3's teethz/A (checksum a67146f092c00f52).
