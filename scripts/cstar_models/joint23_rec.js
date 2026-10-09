const C=+(process.argv[4]||4), scale=+process.argv[2]||1;
const rho={5:.05479,6:.02984,7:.01239,10:.00343,11:.00223,12:.00123,13:.00102,14:.00112,15:.00047};
const isPP=b=>{for(let r=2;r<b;r++){let x=r*r; while(x<b)x*=r; if(x==b)return true;} return false;};
const bases=[]; for(let b=+(process.argv[5]||5);b<=+(process.argv[3]||3000);b++) if(!isPP(b)){const lag=Math.floor(Math.log2(0.75*(Math.pow(b,C)-2)));
  const r=((C==4&&rho[b])||1.5*4/Math.pow(1.8,lag))*scale; bases.push([b,lag,r]);}
const Kmax=3000; const kill=Array.from({length:Kmax+2},()=>[]);
for(const [b,lag,r] of bases){ for(let n=0;;n++){const lv=Math.ceil((n+C)*Math.log2(b)-1e-12); if(lv>Kmax)break; kill[lv].push([lag,r]);}}
let M=[1]; let minratio=1;
for(let k=0;k<Kmax;k++){ let x=M[k]; for(const [lag,r] of kill[k+1]){ const j=k+1-lag; if(j>=0) x-=r*M[j]; } M.push(x); if(x<=0){console.log('dies at',k+1);process.exit();} minratio=Math.min(minratio,x/M[k]); }
console.log('alive; per-level decay rate',Math.pow(M[Kmax]/M[Kmax-500],1/500).toFixed(5),'min step ratio',minratio.toFixed(4));
