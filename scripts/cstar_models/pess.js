// pessimistic two-valued check: products over a window of length l replaced by gA^{l-cm(l)} gB^{cm(l)},
// cm(l) = max # base-3 kill levels in l consecutive levels (from the actual sequence over KK levels).
const [c,R]=process.argv.slice(2).map(Number);
function ispp(b){for(let m=2;m<b;m++){let a=m;while(a<b)a*=m;if(a===b)return true;}return false;}
function pw(b,e){let x=1n;const B=BigInt(b);for(let i=0;i<e;i++)x*=B;return x;}
function clog2(x){let k=0,p=1n;while(p<x){p*=2n;k++;}return k;}
function flog2(x){return x.toString(2).length-1;}
const KK=20000; const res=new Uint8Array(KK+2); let maxPer=0;
for(let n=0;;n++){const P=pw(3,n+c);const lv=clog2(P); if(lv>KK)break; const big=(2n**BigInt(lv+1))>=3n*P; const L=big?lv-1:lv; if(L>=1){res[L]++; maxPer=Math.max(maxPer,res[L]);}}
const pre=[0];for(let k=1;k<=KK;k++)pre.push(pre[k-1]+(res[k]?1:0));
const cm=[0];for(let l=1;l<=200;l++){let m=0;for(let j=1;j+l-1<=KK;j++)m=Math.max(m,pre[j+l-1]-pre[j-1]);cm.push(m);}
console.log('maxPerLevel',maxPer,'cm[1..16]',cm.slice(1,17).join(','));
const bc3=pw(3,c); const lag3A=flog2(bc3-2n), lag3B=flog2((3n*(bc3-2n))/4n);
const tail=[];for(let b=5;b<400;b++){if(ispp(b))continue;const bc=pw(b,c);tail.push(flog2((3n*(bc-2n))/4n));}
function Pinv(l,gA,gB){ if(l<=0) return 1; const L=Math.min(l,200); const m=cm[L]+ (l>200? Math.ceil((l-200)/1.58)+1:0); return 1/(Math.pow(gA,l-m)*Math.pow(gB,m)); }
function slack(gA,gB){
  const t=tail.reduce((s,lg)=>s+4*Pinv(lg-1,gA,gB),0);
  const sA=(2-gA)-Pinv(R-1,gA,gB)-t;
  const sB=(2-gB)-Pinv(R-1,gA,gB)-Math.max(4*Pinv(lag3A-1,gA,gB),3*Pinv(lag3B-1,gA,gB))-t;
  return Math.min(sA,sB);
}
let best=null;
for(let gA=1.3;gA<1.99;gA+=0.005)for(let gB=1.0;gB<1.99;gB+=0.005){const s=slack(gA,gB);if(!best||s>best[0])best=[s,gA,gB];}
console.log(`c=${c}: pessimistic two-valued slack ${best[0].toFixed(4)} gA=${best[1].toFixed(3)} gB=${best[2].toFixed(3)} lag3=${lag3A}/${lag3B}`);
