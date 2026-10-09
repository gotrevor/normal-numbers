// generalized engine: base-2 forbidden pattern lengths (each charged 1 per ancestor at lag len),
// bases b>=3 non-pp: window radius b^-n / K_b, K_b = b^4 * floor(b^e) (e in (0,1]) integer.
// usage: node gen.js e "5,9" [K] [B]
const e=Number(process.argv[2]); const pats=process.argv[3].split(',').map(Number);
const K=Number(process.argv[4]||800), BMAX=Number(process.argv[5]||400);
function ispp(b){for(let m=2;m<b;m++){let a=m;while(a<b)a*=m;if(a===b)return true;}return false;}
function pw(b,x){let r=1n;const B=BigInt(b);for(let i=0;i<x;i++)r*=B;return r;}
function clog2(x){let k=0,p=1n;while(p<x){p*=2n;k++;}return k;}
function flog2(x){return x.toString(2).length-1;}
const kills=Array.from({length:K+2},()=>[]); const res3=new Uint8Array(K+2);
for(let b=3;b<BMAX;b++){ if(ispp(b))continue;
  const Kb=BigInt(Math.floor(Math.pow(b,4+e)));
  const lagA=flog2(Kb-2n), lagB=flog2((3n*(Kb-2n))/4n);
  for(let n=0;;n++){const P=pw(b,n)*Kb; const lv=clog2(P); if(lv-1>K)break;
    const big=(2n**BigInt(lv+1))>=3n*P; const L=big?lv-1:lv; if(L>K)break; if(L<1)continue;
    kills[L].push(big?[lagB,3]:[lagA,4]); if(b===3)res3[L]=1;}}
function worst(gA,gB){const g=new Float64Array(K);for(let k=0;k<K;k++)g[k]=res3[k+1]?gB:gA;
  const pre=new Float64Array(K+1);for(let k=0;k<K;k++)pre[k+1]=pre[k]+Math.log(g[k]);
  const inv=(lag,k)=>{const j=k+1-lag;if(j<0)return 0;return Math.exp(-(pre[k]-pre[j]));};
  let w=1e9;for(let k=40;k<K-1;k++){let kill=0;for(const p of pats)kill+=inv(p,k);
    for(const [lg,m] of kills[k+1])kill+=m*inv(lg,k);const s=(2-g[k])-kill;if(s<w)w=s;}return w;}
let best=null;for(let gA=1.5;gA<1.99;gA+=0.005)for(let gB=1.3;gB<1.99;gB+=0.005){const w=worst(gA,gB);if(!best||w>best[0])best=[w,gA,gB];}
console.log(`e=${e} pats=${pats}: slack ${best[0].toFixed(4)} gA=${best[1].toFixed(3)} gB=${best[2].toFixed(3)}`);
