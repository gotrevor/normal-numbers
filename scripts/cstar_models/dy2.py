import sys
from eng import runfree_min
def met(u,c):  # cores met by obstacle of child-relative radius u
    return 1.0 if u < 2**(-c) else 2*u+2
def cost_b(b,c,K,Kp,al,rb):
    worst=0
    for i in range(16):
        u=rb*b**(-i/16); sm=0
        while u>=rb/K:
            v=b**(-c)/u
            percnt=(v+1+2*b**(-c))*u**al
            sumcnt=(K*v+1)*met(u,c)*u**al/Kp
            sm+=min(percnt,sumcnt); u/=b
        worst=max(worst,sm)
    return worst
def run(c,B0,R,alist):
  best=None
  for L in range(2,15):
    K=2**L; Kp=runfree_min(L,R)
    for al in alist:
      rho=2**(-c)/K*0.999
      F=K**al/Kp
      if F>=1: continue
      g=0
      for b in range(B0,200):
        if b&(b-1)==0: continue
        g+=min(cost_b(b,c,K,Kp,al,rho*2**(-e/2)) for e in range(0,2*L+12))
      sl=((1-F)*rho**al-g)/rho**al
      if best is None or sl>best[0]: best=(round(sl,3),L,al,round(F,3))
  return best
if __name__=="__main__":
  c=float(sys.argv[1]);B0=int(sys.argv[2]);R=int(sys.argv[3])
  print(c,B0,R,run(c,B0,R,[0.3,0.35,0.4,0.45,0.5,0.55,0.6,0.65,0.7,0.75]),flush=True)
