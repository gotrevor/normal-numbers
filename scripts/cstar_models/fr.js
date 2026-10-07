const [N,s,...bs]=process.argv.slice(2).map(Number); const c=4;
const M=2**N; const al=new Uint8Array(M).fill(1);
for(let i=0;i<M;i++){let run=1;for(let t=1;t<N;t++){const a=(i>>(N-t))&1,b=(i>>(N-1-t))&1;if(a===b){run++;if(run>=4){al[i]=0;break;}}else run=1;}}
const rmin=2**-N/4;
for(const b of bs){for(let n=0;;n++){const r=b**(-n-c);if(r<rmin)break;const q=b**n;
 for(let k=0;k<=q;k++){const z=k/q;let lo=Math.floor((z-r)*M),hi=Math.floor((z+r)*M);if(lo<0)lo=0;if(hi>M-1)hi=M-1;for(let x=lo;x<=hi;x++)al[x]=0;}}}
const cs=new Float64Array(M+1);for(let i=0;i<M;i++)cs[i+1]=cs[i]+al[i];
console.log('survivors',cs[M],'dim',(Math.log2(cs[M])/N).toFixed(4));
let worst=0,arg;
for(let j=1;j<=N-6;j++){const size=2**(N-j);
 for(let Q=0;Q<M;Q+=size){const mQ=cs[Q+size]-cs[Q];if(mQ===0)continue;
  for(let t=1;t<=N-j-4;t++)for(let kk=1;kk<=3;kk++){const ln=(size>>t)*kk;const st=Math.max(1,ln>>2);let m=0;
   for(let x=Q;x+ln<=Q+size;x+=st){const v=cs[x+ln]-cs[x];if(v>m)m=v;}
   const ratio=m/mQ/Math.pow(ln/size,s);if(ratio>worst){worst=ratio;arg=[j,t,kk];}}}}
console.log('worst C at s',s,worst.toFixed(3),arg);
