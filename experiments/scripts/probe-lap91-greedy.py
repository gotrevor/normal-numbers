import random
exec(open('experiments/scripts/probe-lap91-transducer.py').read().split('rng=random.Random')[0])
N=8000
for label,Phi0 in [("z/phi",(( 1,0),(0,0),(0,0),(0,1))),("(z+1)/3",((1,0),(1,0),(0,0),(3,0)))]:
    for seed in (1,2):
        rng=random.Random(seed)
        digits=[gauss_digit(rng) for _ in range(N)]
        s=St(*[tuple(c) for c in Phi0]); out=0; stalls=0; traj=[]; maxemit=0
        for i,a in enumerate(digits):
            t=comp(s,readMap(a)); s=t; e=0
            while True:
                k=emit_digit(s)
                if k is None: break
                s=St(sub(s.c,smul(k,s.a)), sub(s.d,smul(k,s.b)), s.a, s.b); out+=1; e+=1
            maxemit=max(maxemit,e)
            if e==0: stalls+=1
            if (i+1)%1000==0: traj.append((i+1,-logwidth(s)))
        print(f"{label} seed{seed}: reads={N} emits={out} stalls={stalls} maxburst={maxemit}")
        print("   slack:", [f"{n}:{v:.1f}" for n,v in traj])
