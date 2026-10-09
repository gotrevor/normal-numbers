// alive binary cells: run-free (runs<R) + open windows of given bases, radius b^{-n-c}, assigned level ceil((n+c)log2 b)
const [c,R,K,...bs]=process.argv.slice(2).map(Number);
let cur=new Float64Array([0]); let prev=1;
for(let k=1;k<=K;k++){
  const h=Math.pow(2,-k); const out=new Float64Array(cur.length*2); let nn=0;
  // windows assigned to level k for each base
  const wins=[];
  for(const b of bs){ const lb=Math.log2(b); for(let n=0;;n++){ const kk=Math.ceil((n+c)*lb-1e-12); if(kk>k)break; if(kk==k){wins.push([b,n,Math.pow(b,-(n+c)),Math.pow(b,n)]);break;} } }
  const m=Math.pow(2,R)-1;
  for(let i=0;i<cur.length;i++){ const a0=cur[i];
    for(let d=0;d<2;d++){ const a=2*a0+d;
      if(k>=R){ const t=a%(m+1); if(t==0||t==m) continue; }
      const lo=a*h,hi=(a+1)*h; let dead=false;
      for(const [b,n,r,bn] of wins){ const A0=Math.floor(lo*bn)-1; for(let A=A0;A<=A0+3;A++){const p=A/bn; if(lo<p+r&&hi>p-r){dead=true;break;}} if(dead)break; }
      if(!dead) out[nn++]=a; } }
  cur=out.subarray(0,nn); console.log(`k=${k} N=${nn} ratio=${(nn/prev).toFixed(4)} ${wins.map(w=>w[0]+':'+w[1]).join(',')}`); prev=nn; if(nn==0)break;
}
