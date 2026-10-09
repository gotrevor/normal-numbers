import mu, sys
c=float(sys.argv[1]); C=float(sys.argv[2]); B0=int(sys.argv[3]); mu.s=float(sys.argv[4])
s=mu.s
best=None
for L in range(3,10):
  be=2.0**-L
  for al in [0.3,0.4,0.5,0.6,0.7,0.75,0.8]:
    if al>=s: continue
    for rho in [2**-i for i in range(1,8)]:
      F=C*(be+2*rho*be)**s*be**(-al)
      if F>=1: continue
      g=sum(min(mu.cost_b(b,c,be,al,rho*2**(-e/2),C) for e in range(0,30)) for b in range(B0,120) if b&(b-1) and b not in (9,27,81))
      sl=((1-F)*rho**al-g)/rho**al
      if best is None or sl>best[0]: best=(round(sl,3),L,al,rho,round(F,3))
print(sys.argv[1:],best,flush=True)
