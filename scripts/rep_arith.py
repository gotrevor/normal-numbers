# Probe of RepPairArith: per-pair min over repBound options, normalized by N^2.
import sys, math
def runs(lim):
    a=4;k=0;R=[]
    while a<lim: R.append((k,a)); a=2*(k+2)*a; k+=1
    return R
def isfree(i,R): return not any(a<=i<(k+2)*a for k,a in R)
def main(b,N,h=1):
    M=int(N*math.log(b,3))+40
    R=runs(M+10); free=[p for p in range(M) if isfree(p,R)]
    P3=[3**(p+1) for p in range(M+1)]
    tot=0.0; dia=0
    for n in range(N):
        for m in range(N):
            xi=h*(b**n-b**m)
            if xi==0: tot+=1; continue
            # free bound
            v=1.0
            for p in free:
                r=(xi % P3[p])/P3[p]; v*=abs(math.cos(2*math.pi*r))
                if v<1e-6: break
            best=v
            for k,a in R:
                Q=3**((k+2)*a)*(3**a-1); num=xi*(3**((k+1)*a)-1)
                w=1.0
                for i in range(a):
                    r=((num*3**i) % Q)/Q; w*=abs(math.cos(2*math.pi*r))
                    if w<1e-9: break
                best=min(best,w)
            tot+=best
    return tot/N**2
if __name__=="__main__":
  for b in map(int,sys.argv[1].split(',')):
    print(b,[round(main(b,N),4) for N in map(int,sys.argv[2].split(','))],flush=True)
