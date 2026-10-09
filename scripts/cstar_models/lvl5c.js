// Engine check, base 2 exact (multiplicity-1 runs, lag R), bases b>=3 (non perfect powers)
// charged per window (b,n): lv = ceil(log2 b^{n+c}), r = 2^{lv+1}/b^{n+c} in [2,4).
//   r < 3 : kill at level lv,   m = 4, lag lagA = floor(log2(b^c-2))
//   r >= 3: kill at level lv-1, m = 3, lag lagB = floor(log2(0.75 (b^c-2)))
// growth g_k two-valued: gB if level k+1 carries a base-3 kill, else gA.
// usage: node lvl5c.js c R [K] [B]
const [c,R,K0,B0]=process.argv.slice(2).map(Number);
const K=K0||800, BMAX=B0||400;
function ispp(b){for(let m=2;m<b;m++){let a=m;while(a<b)a*=m;if(a===b)return true;}return false;}
function pw(b,e){let x=1n;const B=BigInt(b);for(let i=0;i<e;i++)x*=B;return x;}
function clog2(x){let k=0,p=1n;while(p<x){p*=2n;k++;}return k;}
function flog2(x){return x.toString(2).length-1;}
// per level: list of [lag, m]
const kills=Array.from({length:K+2},()=>[]);
const res3=new Uint8Array(K+2);
for(let b=3;b<BMAX;b++){ if(ispp(b))continue;
  const bc=pw(b,c); const lagA=flog2(bc-2n); const lagB=flog2((3n*(bc-2n))/4n);
  for(let n=0;;n++){ const P=pw(b,n+c); const lv=clog2(P); if(lv-1>K)break;
    // r>=3 iff 2^{lv+1} >= 3P
    const big=(2n**BigInt(lv+1))>=3n*P;
    const L= big? lv-1 : lv; if(L>K) break; if(L<1) continue;
    kills[L].push(big?[lagB,3]:[lagA,4]); if(b===3) res3[L]=1; }
}
function worst(gA,gB){
  const g=new Float64Array(K); for(let k=0;k<K;k++) g[k]=res3[k+1]?gB:gA;
  const pre=new Float64Array(K+1); for(let k=0;k<K;k++) pre[k+1]=pre[k]+Math.log(g[k]);
  const inv=(lag,k)=>{const j=k+1-lag; if(j<0)return 0; return Math.exp(-(pre[k]-pre[j]));};
  let w=1e9, at=-1;
  for(let k=R+20;k<K-1;k++){
    let kill=inv(R,k);
    for(const [lg,m] of kills[k+1]) kill+=m*inv(lg,k);
    const s=(2-g[k])-kill; if(s<w){w=s;at=k;}
  }
  return [w,at];
}
let best=null;
for(let gA=1.3;gA<1.99;gA+=0.005) for(let gB=1.0;gB<1.99;gB+=0.01){const [w]=worst(gA,gB); if(!best||w>best[0])best=[w,gA,gB];}
console.log(`c=${c} R=${R} K=${K}: two-valued best slack ${best[0].toFixed(4)} gA=${best[1].toFixed(3)} gB=${best[2].toFixed(3)} worst at k=${worst(best[1],best[2])[1]}`);
let bu=null; for(let gA=1.3;gA<1.99;gA+=0.0025){const [w]=worst(gA,gA); if(!bu||w>bu[0])bu=[w,gA];}
console.log(`  uniform best slack ${bu[0].toFixed(4)} g=${bu[1].toFixed(4)}`);
