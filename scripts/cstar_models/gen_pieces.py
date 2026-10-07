from fractions import Fraction as Fr
import sys
def pieces(P, lo, hi):
    # greedy: from a, largest b on grid of 1/200 with 2b-1 < P(a)
    out=[]; a=lo
    while a<hi:
        b=a
        step=Fr(1,400)
        while b<hi and 2*(b+step)-1 < P(a): b+=step
        if b>=hi: b=hi
        if b==a: raise Exception("stuck at %s"%a)
        if not (2*b-1 < P(a)): raise Exception("bad")
        out.append((a,b)); a=b
    return out
c2=Fr(100,361); c3=Fr(1000,6859)
Ps={'U':(lambda y:y**5+y**7+y**8+4*y**6, Fr(1)),
    'L1':(lambda y:y**5+y**7+y**8, Fr(10,19)),
    'L2':(lambda y:c2*y**3+c3*y**4+c3*y**5+4*c2*y**4, Fr(1))}
for k,(P,hi) in Ps.items():
    ps=pieces(P,Fr(1,2),hi); print(k,len(ps),[str(b) for a,b in ps])

def lean(name, Pstr, hi, hyps):
    P,_h=Ps[name]; ps=pieces(P,Fr(1,2),_h)
    E=lambda v: Pstr.replace('Y',v)
    s=f"theorem poly_{name} (y : ℝ) (h0 : 0 < y) (h1 : y ≤ {hi}) :\n    2 * y - 1 < {E('y')} := by\n"
    s+=f"  have hm : ∀ u v : ℝ, 0 ≤ u → u ≤ v → {E('u')} ≤ {E('v')} := by\n    intro u v hu huv; gcongr\n"
    s+=f"  have hp : 0 < {E('y')} := by positivity\n"
    s+="  rcases le_or_gt y (1 / 2) with h | g0\n  · linarith\n"
    for i,(a,b) in enumerate(ps):
        last = i==len(ps)-1
        if not last:
            s+=f"  rcases le_or_gt y ({b.numerator} / {b.denominator}) with l{i+1} | g{i+1}\n  · "
        else:
            s+="  · "
        s+=f"have := hm ({a.numerator} / {a.denominator}) y (by norm_num) g{i}.le; norm_num at this ⊢; linarith\n"
    return s
print(lean('U','Y ^ 5 + Y ^ 7 + Y ^ 8 + 4 * Y ^ 6','1',None))
print(lean('L1','Y ^ 5 + Y ^ 7 + Y ^ 8','10 / 19',None))
print(lean('L2','100 / 361 * Y ^ 3 + 1000 / 6859 * Y ^ 4 + 1000 / 6859 * Y ^ 5 + 400 / 361 * Y ^ 4','1',None))
