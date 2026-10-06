from fractions import Fraction as F
import random, math, sys
def simplest(lo,hi):  # simplest fraction in open (lo,hi), lo<hi
    fl=math.floor(lo)
    if fl+1<hi: return F(fl+1)
    if lo==fl: pass
    # lo, hi in (fl, fl+1]
    a=lo-fl; b=hi-fl
    if a==0: a=F(0)
    r=simplest(1/b,1/a) if a>0 else None
    if a==0:
        # (0,b): simplest is 1/ceil(1/b) ish
        n=math.floor(1/b)+1; return fl+F(1,n)
    return fl+1/r
def fracs(lo,hi,Q,out):
    if hi<=lo: return
    m=simplest(lo,hi)
    if m.denominator>Q: return
    out.append(m); fracs(lo,m,Q,out); fracs(m,hi,Q,out)
c0=F(1,4*3**16)
def cylL(w): return sum(F(2 if b else 0,3**(i+1)) for i,b in enumerate(w))
def dead(w,u,obs):
    L=len(w)+10; a=cylL(w+u); b=a+F(1,3**L)
    for p in obs:
        q=p.denominator; r=2*c0/q**2
        if not (b < p-r or a > p+r): return True
    return False
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 0)
S=int(sys.argv[2]) if len(sys.argv)>2 else 5
ST={}
tot=0;dd=0;nobs=0
for trial in range(int(sys.argv[3]) if len(sys.argv)>3 else 20):
    w=[]
    for s in range(S):
        L=len(w); a=cylL(w); b=a+F(1,3**L); out=[]
        Q=math.isqrt(3**(L+5)//3**5*3**5)  # q^2*3^5<3^{L+10} -> q^2<3^{L+5}
        Q=math.isqrt(3**(L+5))
        fracs(a-F(1,3**L),b+F(1,3**L),Q,out)
        obs=[p for p in out if 3**L<=p.denominator**2*3**5]
        nobs+=len(obs)
        u=[random.random()<.5 for _ in range(10)]
        tot+=1; ST.setdefault(s,[0,0]); ST[s][0]+=1
        if dead(w,u,obs):
            dd+=1; ST[s][1]+=1; 
            while dead(w,u,obs): u=[random.random()<.5 for _ in range(10)]
        w=w+u
print("stages",tot,"dead",dd,"obs/stage",nobs/tot)
print(ST)
