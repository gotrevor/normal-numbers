import math,sys
def term(u,b,c,be,al):
    A=(1+2*u*be)*(1+2*u)*u**(al-1)*b**(-c)/(1-be)
    B=be*(1+2*u)*u**al/(1-be)
    return A+B
def cost_b(b,c,be,al,rb):
    worst=0
    for i in range(40):
        th=b**(-i/40)        # top of alignment
        s=0;u=rb*th
        while u>=be*rb:
            s+=term(u,b,c,be,al); u/=b
        worst=max(worst,s)
    return worst
def g_total(c,be,al,rho,B=4000):
    g=0
    for b in range(2,B):
        best=min(cost_b(b,c,be,al,rho*2**(-e/4)) for e in range(0,80))
        g+=best
    # tail ~ integral
    return g
if __name__=="__main__":
 c=float(sys.argv[1])
 best=None
 for be in [1/2,1/3,1/4,1/6,1/8,1/12,1/16]:
   for al in [0.3,0.35,0.4,0.5,0.6,0.7]:
     for rho in [2**-i for i in range(1,12)]:
       F=(be+2*rho)*be**(-al)/(1-be)
       if F>=1: continue
       g=g_total(c,be,al,rho,B=300)
       slack=(1-F)*rho**al-g
       if best is None or slack/rho**al>best[0]: best=(slack/rho**al,be,al,rho,F,g)
 print(best)
 