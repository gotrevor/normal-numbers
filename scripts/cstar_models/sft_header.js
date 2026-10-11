// node sft_header.js in.json out.h : C header for exactinf3.c (S, T, R, LAM)
const fs = require('fs'); const d = JSON.parse(fs.readFileSync(process.argv[2]));
// drop dead states? keep indices; dead rows are all -1 and get weight 0
fs.writeFileSync(process.argv[3], `#define S ${d.T.length}\nstatic const int T[S][2] = {${d.T.map(t => `{${t[0]},${t[1]}}`).join(',')}};\nstatic const double R[S] = {${d.r.map(x => x.toPrecision(17)).join(',')}};\nstatic const double LAM = ${d.lam.toPrecision(17)};\n`);
