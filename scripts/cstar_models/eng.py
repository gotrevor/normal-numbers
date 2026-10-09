import math, itertools
def runfree_min(L,R=3):
    # min over states (last run length 1..R) of number of length-L continuations with no run > R
    best=None
    for s in range(1,R+1):
        # dp over (run length of current digit) ; continuing same digit increases run
        dp={s:1}  # state run length of last digit
        for _ in range(L):
            nd={}
            for r,c in dp.items():
                if r+1<=R: nd[r+1]=nd.get(r+1,0)+c
                nd[1]=nd.get(1,0)+c
            dp=nd
        t=sum(dp.values()); best=t if best is None else min(best,t)
    return best
def cost_b(b,c,K,al,gam):
    d=b**(-c); worst=0
    for th in [1-i/50 for i in range(50)]:
        # v values gamma*th*b^-j in (gam/K, gam]
        s=0; v=gam*th
        while v>gam/K:
            u=d/v
            s+=(K*v+1)*(2*u+2)*u**al
            v/=b
        worst=max(worst,s)
    return worst
def pow2(b): return b&(b-1)==0
def test(c,L,al,rho,B=3000):
    K=2**L; Kp=runfree_min(L)
    budget=Kp*rho**al-(2*K*rho+2)*K**al*rho**al
    if budget<=0: return None
    g=0
    for b in range(3,B):
        if pow2(b): continue
        d=b**(-c)
        # choose gamma: need u_max = K d/gam < rho  => gam > K d/rho ; search
        best=float('inf')
        for e in range(0,60):
            gam=K*d/rho*1.15**e
            best=min(best,cost_b(b,c,K,al,gam))
        g+=best
        if b>200 and best<1e-9: break
    return Kp,K,budget,g
import sys
if __name__=="__main__":
  c=float(sys.argv[1])
  res=[]
  for L in range(1,9):
    for al in [0.1,0.2,0.3,0.4,0.5,0.6,0.7]:
      for rho in [2**-i for i in range(1,14)]:
        r=test(c,L,al,rho,B=400)
        if r and r[3]<r[2]: res.append((r[2]-r[3],L,al,rho,r))
  res.sort(reverse=True); print(res[:5])
  