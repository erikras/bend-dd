// Times a solver route on a file of PBN deals and checks every table against dd.
//
//   node web/bench/bench.mjs <js|wasm> <one|strains> deals.pbn dd-output.txt [limit]
//
// js:   Bend's JavaScript target, web/build/api.mjs.
// wasm: Bend's C built by Emscripten without threads, web/build/solver.mjs, with a
//       new instance of the compiled module for every call, as the page runs it.
// one:  every strain in turn on this thread. strains: five worker threads, one per
//       strain, each deal's five strains at once, as the page runs them.
import { readFileSync } from "node:fs";
import { Worker, isMainThread, parentPort, workerData } from "node:worker_threads";

const build = new URL("../build/", import.meta.url);

async function solver(route) {
  if (route === "js") {
    const api = (await import(new URL("api.mjs", build))).default;
    return (pbn, t) => api.strain(pbn, t);
  }
  const create = (await import(new URL("solver.mjs", build))).default;
  const mod = await WebAssembly.compile(readFileSync(new URL("solver.wasm", build)));
  return async (pbn, t) => {
    let out = "";
    await create({
      arguments: ["--strain", String(t), pbn],
      print: (s) => { out += s; },
      printErr: () => {},
      instantiateWasm: (imports, ok) => { WebAssembly.instantiate(mod, imports).then((i) => ok(i, mod)); return {}; },
    });
    return out.trim();
  };
}

if (!isMainThread) {
  const { route, t } = workerData;
  const strain = await solver(route);
  parentPort.on("message", async (pbn) => parentPort.postMessage(await strain(pbn, t)));
  parentPort.postMessage("ready");
} else {
  const [route, mode, file, ddFile, limit] = process.argv.slice(2);
  let deals = readFileSync(file, "utf8").split("\n").filter((l) => l.trim());
  const want = readFileSync(ddFile, "utf8").split("\n").filter((l) => l.trim()).map((l) => l.split(" ").slice(0, 20).join(" "));
  if (limit) deals = deals.slice(0, +limit);
  let bad = 0;
  const times = [];
  let solve;
  let workers = [];
  if (mode === "one") {
    const strain = await solver(route);
    solve = async (pbn) => { const p = []; for (let t = 0; t < 5; t++) p.push(await strain(pbn, t)); return p; };
  } else {
    workers = [0, 1, 2, 3, 4].map((t) => new Worker(new URL(import.meta.url), { workerData: { route, t } }));
    await Promise.all(workers.map((w) => new Promise((r) => w.once("message", r))));
    const ask = (w, pbn) => new Promise((r) => { w.once("message", r); w.postMessage(pbn); });
    solve = (pbn) => Promise.all(workers.map((w) => ask(w, pbn)));
  }
  const t0 = performance.now();
  for (let i = 0; i < deals.length; i++) {
    const s = performance.now();
    const got = (await solve(deals[i])).join(" ");
    times.push(performance.now() - s);
    if (got !== want[i]) { bad++; console.log("MISMATCH", i, got, want[i]); }
  }
  const total = performance.now() - t0;
  workers.forEach((w) => w.terminate());
  times.sort((a, b) => a - b);
  console.log(`${route} ${mode}: ${deals.length} deals in ${(total / 1000).toFixed(1)} s, ${(total / deals.length).toFixed(0)} ms a deal, median ${times[times.length >> 1].toFixed(0)} ms, worst ${times[times.length - 1].toFixed(0)} ms, ${bad} wrong`);
  process.exit(bad ? 1 : 0);
}
