# Iterated-descendant ratio probe: R_d = max over Good (k,a) of desc_{d+1}/desc_d (block = 6 levels).
import sys; sys.argv=['x','none']; sys.path.insert(0,'.')
import tail5_measure as T
def descs(k,a,D):
    # Good descendants at block levels; NO pruning at intermediate non-Good cells (Good449 is not
    # hereditary), only the base-2 automaton prune (sft == 99 kills all descendants).
    out=[0]*(D+1); out[0]=T.weight(k,a)
    def go(kk,aa):
        if T.sft(kk,aa)==99: return
        if kk>k and (kk-k)%6==0:
            d=(kk-k)//6
            if T.good(kk,aa): out[d]+=T.weight(kk,aa)
            if d==D: return
        go(kk+1,2*aa); go(kk+1,2*aa+1)
    go(k,a); return out
