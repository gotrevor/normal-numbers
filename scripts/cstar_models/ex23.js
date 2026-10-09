// exact joint {2,3} tree at exponent C: a dyadic cell dies when it lies inside a bad set
// (base 2: 2^n x mod 1 within 2^-C of Z; base 3 likewise). usage: node ex23.js C K [D]
// prints growth per level, then the spread of D-level descendant counts of level K-D cells.
const C=+process.argv[2], K=+process.argv[3], D=+(process.argv[4]||8);
const t2=Math.pow(2,-C), t3=Math.pow(3,-C);
let lev=[0]; const ALL=[[0]];
for(let k=1;k<=K;k++){const out=[]; const pk=Math.pow(2,k);
  for(const p of lev) for(let d=0;d<2;d++){const a=2*p+d; let dead=false;
    for(let L=1;L<=k&&!dead;L++){const s=Math.pow(2,L), u=a%s; if((u+1)/s<=t2||u/s>=1-t2) dead=true;}
    if(!dead){ for(let n=0;;n++){const w=t3/Math.pow(3,n); if(2*w<1/pk)break; const x0=a/pk, x1=(a+1)/pk;
        const A=Math.round(x0*Math.pow(3,n)); for(const B of [A-1,A,A+1]){const c=B/Math.pow(3,n); if(x0>=c-w&&x1<=c+w){dead=true;break;}} if(dead)break;}}
    if(!dead) out.push(a);}
  ALL.push(out); if(k>K-4) console.log(k,out.length,(out.length/lev.length).toFixed(4)); lev=out;}
const j=K-D; const m=new Map(); for(const a of ALL[j]) m.set(a,0);
for(const a of ALL[K]){const p=Math.floor(a/Math.pow(2,D)); m.set(p,m.get(p)+1);}
const v=[...m.values()].sort((x,y)=>x-y); const mean=ALL[K].length/ALL[j].length;
console.log("D",D,"mean",mean.toFixed(2),"min",v[0],"p1",v[Math.floor(v.length*.01)],"p10",v[Math.floor(v.length*.1)],"zeros",v.filter(x=>x==0).length,"of",v.length);
