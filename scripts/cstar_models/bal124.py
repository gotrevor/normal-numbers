from fractions import Fraction as Fr
def Kb(b):
    if b>=100: return b**4
    lo,hi=1,b**5
    while hi>lo+1:
        m=(lo+hi)//2
        if m**25<=b**124: lo=m
        else: hi=m
    return lo
def lag(b): return ((3*(Kb(b)-2))//4).bit_length()-1
gA=Fr(181,100); import sys; gB=Fr(sys.argv[1])
F=lambda l:(gA*gB*gB)**(l//3)*gB**(l%3)
Ts=sum(Fr(4)/F(lag(b)-1) for b in range(4,100) if b not in (4,8,9))
tb=4*Fr(1156,1089)*Fr(4757,1000)/100/99
off=1/F(4)+1/F(9)
print("K3",Kb(3),"lag3",lag(3),"Ts",float(Ts),"tailbd",float(tb))
print("off", float(off+Ts+tb), "<=", float(2-gA))
print("on", float(off+Fr(4)/F(6)+Ts+tb), "<=", float(2-gB))
print([Kb(b) for b in range(3,12)])
