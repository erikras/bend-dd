// Checks api.sim run in chunks against the sim binary, number for number.
//
//   node web/bench/simcheck.mjs [chunk]
import { execFileSync } from "node:child_process";
const api = (await import(new URL("../build/api.mjs", import.meta.url))).default;
const chunk = +(process.argv[2] || 16);
const args = ["deal=N:- - - T952.T2.JT754.97", "contract=4H", "by=S", "S.hcp=15-19", "S.H=5+", "N.hcp=8-11", "N.H=3+"];
const n = 200, seed = 11;
const setup = args.join("\n");
const t0 = performance.now();
let tot = null;
for (let first = 0; first < n; first += chunk) {
  const r = JSON.parse(api.sim(setup, seed, first, Math.min(chunk, n - first)));
  if (r.error) throw new Error(r.error);
  if (!tot) tot = r;
  else {
    tot.deals += r.deals; tot.tries += r.tries;
    tot.sums = tot.sums.map((x, i) => x + r.sums[i]);
    tot.makes = tot.makes.map((x, i) => x + r.makes[i]);
  }
}
const ms = performance.now() - t0;
// Format as sim does: ratio to two places, percent to one, rounding half up.
const ratio = (x, d) => { const v = Math.floor((x * 100 + Math.floor(d / 2)) / Math.max(d, 1)); return `${Math.floor(v / 100)}.${String(v % 100).padStart(2, "0")}`; };
const pct = (x, d) => { const v = Math.floor((x * 1000 + Math.floor(d / 2)) / Math.max(d, 1)); return `${Math.floor(v / 10)}.${v % 10}%`; };
const mine = {};
tot.cards.forEach(([c, name, run], i) => { mine[name.slice(0, -1) + run] = `${ratio(tot.sums[i], tot.deals)} ${pct(tot.makes[i], tot.deals)}`; });
const out = execFileSync(new URL("../../sim", import.meta.url).pathname, [...args, `n=${n}`, `seed=${seed}`], { encoding: "utf8" });
const theirs = {};
const kept = out.match(/Dealt (\d+) layouts and kept (\d+)/);
for (const line of out.split("\n")) {
  const m = line.match(/^(\S+)\s+(\d+\.\d\d)\s+(\d+\.\d%)$/);
  if (m) theirs[m[1]] = `${m[2]} ${m[3]}`;
}
let bad = +kept[1] !== tot.tries || +kept[2] !== tot.deals ? 1 : 0;
for (const k of Object.keys(theirs)) if (theirs[k] !== mine[k]) { bad++; console.log("MISMATCH", k, theirs[k], mine[k]); }
if (Object.keys(theirs).length !== Object.keys(mine).length) { bad++; console.log("cards differ", Object.keys(theirs), Object.keys(mine)); }
console.log(`sim in chunks of ${chunk}: ${tot.deals} kept of ${tot.tries}, ${Object.keys(mine).length} cards, ${(ms / 1000).toFixed(1)} s in one JS thread, ${bad ? bad + " differences" : "same as sim"}`);
process.exit(bad ? 1 : 0);
