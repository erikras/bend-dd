// Checks the play-through: api.cards (through the page's WebAssembly build) and the
// page's rules of play (web/src/play.ts) against the double dummy table.
//
//   bun web/bench/playcheck.ts deals.pbn dd-output.txt [deals]
//
// For each deal and a contract, at every point of a play where each side always plays
// a best card, the best card must keep declarer's tricks at the table's value, and the
// tricks won at the end must equal it. Then a random card at each step: declarer's
// tricks can only move against the side that played it.
import { readFileSync } from "node:fs";
import { parsePbn, Deal } from "../src/bridge";
import { replay, options, cardText, Cands } from "../src/play";

const build = new URL("../build/", import.meta.url);
const create = (await import(new URL("solver.mjs", build).href)).default;
const mod = await WebAssembly.compile(readFileSync(new URL("solver.wasm", build)));

async function solve(args: string[]): Promise<string> {
  let out = "";
  await create({
    arguments: args,
    print: (s: string) => { out += s; },
    printErr: () => {},
    instantiateWasm: (imports: any, ok: any) => { WebAssembly.instantiate(mod, imports).then((i) => ok(i, mod)); return {}; },
  });
  return out.trim();
}

const [file, ddFile, count = "3"] = process.argv.slice(2);
const deals = readFileSync(file, "utf8").trim().split("\n");
const tables = readFileSync(ddFile, "utf8").trim().split("\n").map((l) => l.split(" ").map(Number));
const STRAIN = ["S", "H", "D", "C", "NT"];
let bad = 0, positions = 0;
let seed = 7;
const rand = (n: number) => { seed = (seed * 1103515245 + 12345) >>> 0; return (seed >>> 8) % n; };
const t0 = performance.now();

async function walk(i: number, deal: Deal, pbn: string, t: number, decl: number, random: boolean) {
  const want = tables[i][t * 4 + decl];
  const plays: string[] = [];
  let expect = want;
  for (;;) {
    const p = replay(deal, t, decl, plays);
    if (p.error) { bad++; console.log(`deal ${i + 1}: ${p.error}`); return; }
    if (p.over) {
      if (p.won[0] !== expect) { bad++; console.log(`deal ${i + 1} ${STRAIN[t]} by ${"NESW"[decl]}: took ${p.won[0]}, expected ${expect}`); }
      return;
    }
    const r = JSON.parse(await solve(["--cards", pbn, STRAIN[t], "NESW"[decl], plays.join(" ")]));
    if (r.error) { bad++; console.log(`deal ${i + 1}: ${r.error}`); return; }
    positions++;
    const os = options(p, r as Cands);
    const best = os.find((o) => o.best)!;
    if (best.tricks !== expect) { bad++; console.log(`deal ${i + 1} after ${plays.join(" ")}: best ${best.tricks}, expected ${expect}`); return; }
    if (os.some((o) => o.group < 0)) { bad++; console.log(`deal ${i + 1}: a legal card has no value`); return; }
    const o = random ? os[rand(os.length)] : best;
    expect = o.tricks;
    plays.push(cardText(o.card));
  }
}

for (let i = 0; i < +count; i++) {
  const deal = parsePbn(deals[i]) as Deal;
  const t = i % 5, decl = (i * 3) % 4;
  await walk(i, deal, deals[i], t, decl, false);
  await walk(i, deal, deals[i], (t + 2) % 5, (decl + 1) % 4, true);
}
console.log(`play: ${positions} positions in ${((performance.now() - t0) / 1000).toFixed(1)} s, ${bad ? bad + " wrong" : "all consistent with dd"}`);
process.exit(bad ? 1 : 0);
