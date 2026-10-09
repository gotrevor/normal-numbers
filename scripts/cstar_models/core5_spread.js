const C=+process.argv[2], S=process.argv[3].split(',').map(Number), K0=+process.argv[4], D=+process.argv[5];
function inside(lo,hi){for(const b of S){const d=Math.pow(b,-C);for(let p=1;(hi-lo)*p<=2*d;p*=b){const x=lo*p,y=hi*p,k=Math.round(x);if(x>=k-d&&y<=k+d)return true;}}return false;}
function grow(cells,k0,D){let cur=cells;for(let k=k0+1;k<=k0+D;k++){const w=Math.pow(2,-k),nx=[];for(const lo of cur)for(const t of [0,1]){const l=lo+t*w;if(!inside(l,l+w))nx.push(l);}cur=nx;}return cur;}
const base=grow([0],0,K0); let mn=1e9,mx=0,zero=0;
const arr=base.map(c=>grow([c],K0,D).length).filter(n=>n>0).sort((a,b)=>a-b); const q=f=>Math.pow(arr[Math.floor(f*(arr.length-1))],1/D).toFixed(3); console.log("nonzero",arr.length,"quantiles 0,.001,.01,.1,.5",q(0),q(.001),q(.01),q(.1),q(.5)); process.exit();
console.log('cells',base.length,'dead-end',zero,'min rate',Math.pow(mn,1/D).toFixed(3),'max',Math.pow(mx,1/D).toFixed(3));
