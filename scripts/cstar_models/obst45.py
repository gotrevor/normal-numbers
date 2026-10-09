import math
# base-3 kill levels at c=4.5 with K3=140: L(n)=clog2(3*3^n*140)-2
L=[]
for n in range(0,3000):
    P=3**n*140; c=(3*P-1).bit_length(); L.append(c-2)
S=set(L); K=L[-1]
def cnt(l):
    mn,mx=99,0
    for j in range(20,K-l):
        m=sum(1 for i in range(j,j+l) if i in S); mn=min(mn,m); mx=max(mx,m)
    return mn,mx
mm={l:cnt(l) for l in range(1,9)}
print(mm)
best=-9
for i in range(1000,2001,5):
  gA=i/1000
  for j in range(1000,2001,5):
    gB=j/1000
    def F(l):
        mn,mx=mm[l]
        return gA**(l-mn)*gB**mn if gB<=gA else gA**(l-mx)*gB**mx
    base2=1/F(4)+1/F(6)+1/F(7)
    s=min(2-gA-base2, 2-gB-base2-4/F(5))
    best=max(best,s)
print("best slack",best)
