# desc ratios for non-Good level-12 cells (Good449 not hereditary; charged ancestors may be non-Good)
import sys; sys.argv=['x','none']; sys.path.insert(0,'.')
import tail5_measure as T
from tail5_ratio_lib import descs
for a in (302,303,304,451,458,605,606,906):
    o=descs(12,a,3)
    print(a,[float(x) for x in o],"R1",float(o[2]/o[1]) if o[1] else None,"R2",float(o[3]/o[2]) if o[2] else None,flush=True)
