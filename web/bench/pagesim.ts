// Checks the page's simulator against sim: the README's example and one after some
// play, run as the page runs it (web/src/sim.ts: the chunks for 8 workers, merged and
// formatted) through the WebAssembly build, row for row against the sim binary.
//
//   bun web/bench/pagesim.ts
import { readFileSync } from "node:fs";
import { execFileSync } from "node:child_process";
import { parsePbn, Deal } from "../src/bridge";
import { chunks, merge, percent, ratio, rows, setupText, visible, SimOut } from "../src/sim";

const root = new URL("../../", import.meta.url).pathname;
const build = root + "web/build/";
const create = (await import(build + "solver.mjs")).default;
const mod = await WebAssembly.compile(readFileSync(build + "solver.wasm"));
async function solve(args: string[]): Promise<string> {
  let out = "";
  await create({ arguments: args, print: (s: string) => { out += s; }, printErr: () => {},
    instantiateWasm: (imports: any, ok: any) => { WebAssembly.instantiate(mod, imports).then((i) => ok(i, mod)); return {}; } });
  return out.trim();
}

// A full deal with the README's West hand; only West is seen, so the rest is any.
const deal = parsePbn("N:AJ4.K94.KQ8.T862 KQ86.873.A62.KJ5 73.AQJ65.93.AQ43 T952.T2.JT754.97") as Deal;
const cases = [
  { name: "README example", view: "leader" as const, plays: [] as string[], rules: ["S.hcp=15-19", "S.H=5+", "N.hcp=8-11", "N.H=3+"], n: 200, seed: 11 },
  { name: "declarer after the first trick", view: "declarer" as const, plays: ["DJ", "DK", "D2", "D3"], rules: ["W.hcp=0-10"], n: 60, seed: 5 },
];
let bad = 0;
for (const c of cases) {
  const seen = visible(c.view, 2, c.plays.length);
  const setup = setupText(deal, seen, "4H", 2, c.plays, c.rules);
  const t0 = performance.now();
  let out: SimOut | null = null;
  const parts = chunks(c.n, 8);
  const results = await Promise.all(parts.map(([f, k]) => solve(["--sim", setup, String(c.seed), String(f), String(k)])));
  for (const r of results) {
    const j = JSON.parse(r);
    if (j.error) { bad++; console.log(`${c.name}: ${j.error}`); break; }
    out = merge(out, j);
  }
  if (!out) continue;
  const mine = rows(out).map((r) => `${r.key} ${ratio(r.sum, out!.deals)} ${percent(r.makes, out!.deals)}`);
  const args = setup.split("\n").filter((l) => !l.endsWith("=")).concat([`n=${c.n}`, `seed=${c.seed}`]);
  const txt = execFileSync(root + "sim", args, { encoding: "utf8" });
  const theirs = txt.split("\n").map((l) => l.match(/^(\S+)\s+(\d+\.\d\d)\s+(\d+\.\d%)$/)).filter(Boolean).map((m) => `${m![1]} ${m![2]} ${m![3]}`);
  const kept = txt.match(/Dealt (\d+) layouts and kept (\d+)/)!;
  const same = JSON.stringify(mine) === JSON.stringify(theirs) && +kept[1] === out.tries && +kept[2] === out.deals;
  if (!same) { bad++; console.log(`${c.name}: page\n${mine.join("\n")}\nsim\n${theirs.join("\n")}`); }
  console.log(`${c.name}: ${parts.length} chunks, ${out.deals} kept of ${out.tries}, ${mine.length} rows, ${((performance.now() - t0) / 1000).toFixed(1)} s, ${same ? "same as sim, row for row" : "DIFFERENT"}`);
}
process.exit(bad ? 1 : 0);
