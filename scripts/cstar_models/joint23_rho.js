const [K,C,KMAX,BMAX]=process.argv.slice(2).map(Number);
const win={}; for(let n=0;n<40;n++){const k=Math.ceil((n+C)*Math.log2(3)-1e-12); if(k<=K) win[k]=n;}
const M=(1<<C)-1;
let levels=[new Float64Array([0])], par=[null];
for(let k=1;k<=K;k++){
  const prev=levels[k-1]; const out=new Float64Array(prev.length*2); const pp=new Int32Array(prev.length*2); let m=0; const pk=Math.pow(2,k);
  const n=win[k]; const N= n!==undefined? Math.pow(3,n+C):0, p=n!==undefined?Math.pow(3,n):0;
  for(let i=0;i<prev.length;i++){ for(let d=0;d<2;d++){ const a=2*prev[i]+d;
    if(k>=C){const t=a%(M+1); if(t==0||t==M) continue;}
    if(n!==undefined){ const A0=Math.floor(a*p/pk); let dead=false;
      for(let A=A0-1;A<=A0+2;A++){ if(A<0)continue; const c=Math.pow(3,C)*A;
        if(a*N < (c+1)*pk && (a+1)*N > (c-1)*pk){dead=true;break;} }
      if(dead)continue; }
    pp[m]=i; out[m++]=a; } }
  levels.push(out.subarray(0,m)); par.push(pp.subarray(0,m));
}
const W=[]; W[K]=new Float64Array(levels[K].length).fill(1);
for(let k=K;k>=1;k--){ const w=new Float64Array(levels[k-1].length); const pp=par[k]; for(let i=0;i<pp.length;i++) w[pp[i]]+=W[k][i]; W[k-1]=w; }
function find(k,a){ const L=levels[k]; let lo=0,hi=L.length-1; while(lo<=hi){const mid=(lo+hi)>>1; if(L[mid]===a)return mid; if(L[mid]<a)lo=mid+1; else hi=mid-1;} return -1; }
const isPP=b=>{for(let r=2;r<b;r++){let x=r*r; while(x<b)x*=r; if(x==b)return true;} return false;};
for(let b=5;b<=BMAX;b++){ if(isPP(b))continue;
  const lagb=Math.floor(Math.log2(0.75*(Math.pow(b,C)-2)));
  let worst=0, info='', nw=0, ratios=[];
  for(let n=0;;n++){ const lv=Math.ceil((n+C)*Math.log2(b)-1e-12); if(lv>KMAX)break;
    const pk=Math.pow(2,lv), bn=Math.pow(b,n), r=Math.pow(b,-(n+C)); const j=lv-lagb; if(j<0)continue;
    const kills=new Map(); const L=levels[lv];
    for(let i=0;i<L.length;i++){ const a=L[i]; const lo=a/pk, hi=(a+1)/pk; const A0=Math.floor(lo*bn);
      for(let A=A0;A<=A0+1;A++){ const p=A/bn; if(lo<p+r&&hi>p-r) kills.set(A,(kills.get(A)||0)+W[lv][i]); } }
    for(const [A,km] of kills){ const x=A/bn*Math.pow(2,j); let wA=0;
      for(const anc of [Math.floor(x), Math.ceil(x)-1]){ const id=find(j,anc); if(id>=0) wA=Math.max(wA,W[j][id]); }
      const ratio=km/wA; nw++; ratios.push(ratio);
      if(ratio>worst){worst=ratio; info=`n=${n} lv=${lv} j=${j}`;} } }
  ratios.sort((x,y)=>y-x);
  console.log(`b=${b} lag=${lagb} windows=${nw} rho_max=${worst.toFixed(5)} q99=${(ratios[Math.floor(nw/100)]||0).toFixed(5)} median=${(ratios[nw>>1]||0).toFixed(5)} 4/1.8^lag=${(4/Math.pow(1.8,lagb)).toFixed(5)} ${info}`);
}
