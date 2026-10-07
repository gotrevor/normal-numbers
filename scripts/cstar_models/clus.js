const [smin,lam,B0,B1]=process.argv.slice(2).map(Number);
let W=[];
for(let b=B0;b<=B1;b++){const d=1/(b**4-1);for(let n=0;2*d*b**(-n)>=smin;n++){const bn=b**n,r=d/bn;for(let A=0;A<=bn;A++){const c=A/bn;W.push([c-r*(1+2*lam),c+r*(1+2*lam),2*r,b]);}}}
W.sort((x,y)=>x[0]-y[0]);
let comps=[];let cur=null;
for(const w of W){if(cur&&w[0]<=cur.e){cur.e=Math.max(cur.e,w[1]);cur.big=Math.max(cur.big,w[2]);cur.n++;cur.bs.add(w[3]);}else{cur={s:w[0],e:w[1],big:w[2],n:1,bs:new Set([w[3]])};comps.push(cur);}}
comps=comps.filter(c=>c.s>0.001&&c.e<0.999);
for(const c of comps)c.ratio=(c.e-c.s)/(c.big*(1+2*lam));
comps.sort((a,b)=>b.ratio-a.ratio);
console.log("windows",W.length,"comps",comps.length);
for(const c of comps.slice(0,10))console.log(c.ratio.toFixed(3),c.n,c.s.toFixed(10),c.big.toExponential(2),[...c.bs].join(","));
