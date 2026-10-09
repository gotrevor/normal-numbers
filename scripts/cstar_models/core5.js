const K=+process.argv[2], C=+process.argv[3], S=process.argv[4].split(',').map(Number);
function inside(lo,hi){for(const b of S){const d=Math.pow(b,-C);for(let p=1;(hi-lo)*p<=2*d;p*=b){const x=lo*p,y=hi*p,k=Math.round(x);if(x>=k-d&&y<=k+d)return true;}}return false;}
let cur=new Float64Array([0]),n=1;
for(let k=1;k<=K;k++){const w=Math.pow(2,-k);const nx=new Float64Array(2*n);let m=0;
 for(let i=0;i<n;i++)for(let t=0;t<2;t++){const lo=cur[i]+t*w;if(!inside(lo,lo+w))nx[m++]=lo;}
 console.log(k,m,(m/n).toFixed(4));cur=nx;n=m;if(m>4e7)break;}
