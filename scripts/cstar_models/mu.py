import sys
s=0.8791
def term(u,b,c,be,al,C):
    # A: many obstacles; B: proximity
    A=C*(be**(s-1))*(1+2*u/1)**s*u**(al-1)*b**(-c)*(1+2*u*be)
    B=C*(be+2*u*be)**s*u**al
    return A+B
def cost_b(b,c,be,al,rb,C):
    worst=0
    for i in range(24):
        th=b**(-i/24); sm=0; u=rb*th
        while u>=be*rb:
            sm+=term(u,b,c,be,al,C); u/=b
        worst=max(worst,sm)
    return worst
def run(c,C,B0=3):
  best=None
  for be in [1/2,1/4,1/8,1/16,1/32]:
    for al in [0.3,0.4,0.5,0.6,0.7]:
      for rho in [2**-i for i in range(1,12)]:
        F=C*(be+2*rho*be)**s*be**(-al)
        if F>=1: continue
        g=0
        for b in range(B0,150):
          if b&(b-1)==0: continue
          g+=min(cost_b(b,c,be,al,rho*2**(-e/2),C) for e in range(0,30))
        sl=((1-F)*rho**al-g)/rho**al
        if best is None or sl>best[0]: best=(round(sl,3),be,al,rho,round(F,3))
  return best
if __name__=="__main__":
 for c in [4,5,6]:
   for C in [1,2]:
     for B0 in [3,5,16]:
       print(c,C,B0,run(c,C,B0),flush=True)
 