// exact joint {2,3} alive binary tree at exponent C (runs: last 4 digits equal killed; base-3 windows killed at lv)
const [K,D,C]=process.argv.slice(2).map(Number);
const win={}; for(let n=0;n<40;n++){const k=Math.ceil((n+C)*Math.log2(3)-1e-12); if(k<=K) win[k]=n;}
const R=C; const M=(1<<R)-1;
let levels=[new Float64Array([0])];
for(let k=1;k<=K;k++){
  const prev=levels[k-1]; const out=new Float64Array(prev.length*2); let m=0; const pk=Math.pow(2,k);
  const n=win[k]; const N= n!==undefined? Math.pow(3,n+C):0, p=n!==undefined?Math.pow(3,n):0;
  for(let i=0;i<prev.length;i++){ for(let d=0;d<2;d++){ const a=2*prev[i]+d;
    if(k>=R){const t=a%(M+1); if(t==0||t==M) continue;}
    if(n!==undefined){ const A0=Math.floor(a*p/pk); let dead=false;
      for(let A=A0-1;A<=A0+2;A++){ if(A<0)continue; const c=Math.pow(3,C)*A;
        if(a*N < (c+1)*pk && (a+1)*N > (c-1)*pk){dead=true;break;} }
      if(dead)continue; }
    out[m++]=a; } }
  levels.push(out.subarray(0,m));
}
for(let k=1;k<=K;k++) console.log(k,levels[k].length,(levels[k].length/levels[k-1].length).toFixed(4));
const j=K-D-1, base=levels[j];
const idx=new Map(); base.forEach((a,i)=>idx.set(a,i));
const nd=new Float64Array(base.length), nd1=new Float64Array(base.length);
for(const a of levels[j+D]) nd[idx.get(Math.floor(a/Math.pow(2,D)))]++;
for(const a of levels[j+D+1]) nd1[idx.get(Math.floor(a/Math.pow(2,D+1)))]++;
let mean=levels[j+D].length/base.length, mn=1e18,mx=0,rmn=1e9,rmx=0,z=0;
const bins=[0,.1,.2,.4,.6,.8,1,1.2,1.4,1.6,2,3,99], h=new Array(bins.length).fill(0);
for(let i=0;i<base.length;i++){const v=nd[i]/mean; mn=Math.min(mn,v); mx=Math.max(mx,v); if(nd[i]==0)z++; else {const r=nd1[i]/nd[i]; rmn=Math.min(rmn,r); rmx=Math.max(rmx,r);}
  let b=0; while(v>=bins[b+1])b++; h[b]++;}
console.log(`j=${j} D=${D} N_D/mean in [${mn.toFixed(4)},${mx.toFixed(4)}] zeros=${z} per-cell growth [${rmn.toFixed(4)},${rmx.toFixed(4)}]`);
console.log(bins.map((b,i)=>b+':'+h[i]).join(' '));
