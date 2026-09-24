import cmath, math
N=10**6
# smallest prime factor sieve
spf=list(range(N+1))
for i in range(2,int(N**0.5)+1):
    if spf[i]==i:
        for j in range(i*i,N+1,i):
            if spf[j]==j: spf[j]=i
def omega_large(m,P):
    c=0; last=0
    while m>1:
        p=spf[m]
        if p!=last and p>P: c+=1
        last=p; m//=p
    return c
primes=[p for p in range(2,N+1) if spf[p]==p]
def pred(z,P,X):
    r=1+0j
    for p in primes:
        if p>P and p<=X: r*= (1+(z-1)/p)
    return r
for P in (1,5,100):
    for th in (math.pi, math.pi/2, 0.3):
        z=cmath.exp(1j*th)
        S=0j
        for m in range(1,N+1): S+= z**omega_large(m,P)
        S/=N
        pr=pred(z,P,N)
        print(f"P={P} theta={th:.3f} mean={abs(S):.5f} arg={cmath.phase(S):+.3f}  pred|.|={abs(pr):.5f} argp={cmath.phase(pr):+.3f}  ratio={abs(S)/abs(pr):.3f}")

print("--- twisted ---")
for (P,Q,j,th) in ((1,5,1,math.pi),(5,12,5,math.pi/2),(100,7,3,math.pi),(1,2,1,2.0),(5,6,1,0.8)):
    z=cmath.exp(1j*th); S=0j
    for m in range(1,N+1):
        S+= cmath.exp(2j*math.pi*j*m/Q) * z**omega_large(m,P)
    S/=N
    print(f"P={P} Q={Q} j={j} th={th:.2f}  |twisted mean|={abs(S):.5f}")
