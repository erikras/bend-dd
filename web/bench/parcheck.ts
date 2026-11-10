// Checks the page's par (web/src/bridge.ts) against DDS's, from web/bench/par.py.
//
//   bun web/bench/parcheck.ts dd-output.txt par.txt
import { readFileSync } from "node:fs";
import { par, Vul } from "../src/bridge";

const [ddFile, parFile] = process.argv.slice(2);
const tables = readFileSync(ddFile, "utf8").trim().split("\n").map((l) => {
  const xs = l.split(" ").map(Number);
  return [0, 1, 2, 3, 4].map((s) => xs.slice(s * 4, s * 4 + 4));
});
const want = readFileSync(parFile, "utf8").trim().split("\n").map((l) => l.split(" ").map(Number));
const vuls: Vul[] = ["None", "NS", "EW", "All"];
let bad = 0, n = 0;
tables.forEach((t, i) => {
  for (let d = 0; d < 4; d++) for (let v = 0; v < 4; v++) {
    n++;
    const got = par(t, vuls[v], d);
    if (got.score !== want[i][d * 4 + v]) {
      bad++;
      if (bad <= 10) console.log(`deal ${i + 1}, dealer ${"NESW"[d]}, vul ${vuls[v]}: ${got.text} but DDS says ${want[i][d * 4 + v]}`);
    }
  }
});
console.log(`par: ${n} cases, ${bad} differ from DDS`);
process.exit(bad ? 1 : 0);
