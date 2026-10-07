const [N,s,eta,...bs]=process.argv.slice(2).map(Number); const c=4;
const M=2**N;
function aliveAt(J){ // fine-resolution mask: run-free digits up to J, obstacles radius >= eta*2^-J
 const al=new Uint8Array(M).fill(1);
 for(let i=0;i<M;i++){let run=1;for(let t=1;t<Math.min(J,N);t++){const a=(i>>(N-t))&1,b=(i>>(N-1-t))&1;if(a===b){run++;if(run>=4){al[i]=0;break;}}else run=1;}}
 const rmin=eta*2**-J;
 for(const b of bs){for(let n=0;;n++){const r=b**(-n-c);if(r<rmin)break;const q=b**n;
  for(let k=0;k<=q;k++){const z=k/q;let lo=Math.floor((z-r)*M),hi=Math.floor((z+r)*M);if(lo<0)lo=0;if(hi>M-1)hi=M-1;for(let x=lo;x<=hi;x++)al[x]=0;}}}
 return al;}
const fin=aliveAt(N); const cs=new Float64Array(M+1);for(let i=0;i<M;i++)cs[i+1]=cs[i]+fin[i];
console.log('survivors',cs[M]);
let worst=0,arg;
for(let j=2;j<=N-7;j++){const A=aliveAt(j);const size=2**(N-j);
 for(let Q=0;Q<M;Q+=size){ // components of A within dyadic cell
  let x=Q; while(x<Q+size){ if(!A[x]){x++;continue;} let y=x; while(y<Q+size&&A[y])y++;
   const L=y-x, mQ=cs[y]-cs[x];
   if(mQ>0&&L>=64){ for(let ln=Math.max(1,L>>10);ln<L;ln*=2){const st=Math.max(1,ln>>2);let m=0;
      for(let u=x;u+ln<=y;u+=st){const v=cs[u+ln]-cs[u];if(v>m)m=v;}
      const r=m/mQ/Math.pow(ln/L,s); if(r>worst){worst=r;arg=[j,L,ln];}}}
   x=y;}}}
console.log('worst C(components) s',s,'eta',eta,worst.toFixed(3),arg);
