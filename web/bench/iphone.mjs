// Runs the page in WebKit, the engine of Safari, with iPhone 15 emulation: a table
// against dd, the README's simulation against sim, and a simulation after a trick
// (a link that crashed mobile Safari when each worker took 615 MB). Logs the
// memory the pool's workers report (peak per worker, and all at once) and the peak
// footprint of WebKit's web content processes, sampled while it runs.
//
//   NODE_PATH=<node_modules with playwright> node web/bench/iphone.mjs [url]
import { createRequire } from "node:module";
import { execFileSync } from "node:child_process";

const require = createRequire(import.meta.url);
const { webkit, devices } = require("playwright");
const url = process.argv[2] || "http://localhost:8642/";
const root = new URL("../../", import.meta.url).pathname;
const MB = (b) => (b / 1048576).toFixed(0) + " MB";

// The resident memory of Playwright's WebKit content processes, in bytes.
function contentRss() {
  const out = execFileSync("ps", ["-axo", "rss=,command="], { encoding: "utf8" });
  return out.split("\n").filter((l) => l.includes("ms-playwright/webkit") && l.includes("WebContent")).reduce((t, l) => t + 1024 * +l.trim().split(/\s+/)[0], 0);
}

const browser = await webkit.launch();
let bad = 0;
const ok = (name, good, note = "") => { if (!good) bad++; console.log(`${name}: ${good ? "ok" : "FAILED"}${note ? " " + note : ""}`); };

async function page(hash, fn) {
  const ctx = await browser.newContext({ ...devices["iPhone 15"] });
  const p = await ctx.newPage();
  const errors = [];
  p.on("pageerror", (e) => errors.push(String(e)));
  p.on("crash", () => errors.push("the page crashed"));
  let peak = 0;
  const timer = setInterval(() => { peak = Math.max(peak, contentRss()); }, 250);
  await p.goto(url + hash);
  const t0 = Date.now();
  await fn(p);
  clearInterval(timer);
  peak = Math.max(peak, contentRss());
  const s = await p.evaluate(() => ({ perWorker: 0, total: 0, workers: 0, size: "?", ...(globalThis.ddPool?.stats || {}), ...(globalThis.ddPool ? { size: globalThis.ddPool.size } : {}), notice: document.querySelector(".notice")?.textContent || "" }));
  console.log(`  ${Date.now() - t0} ms; pool of ${s.size} workers (most at once ${s.workers}); wasm memory: ${MB(s.perWorker)} per worker at most, ${MB(s.total)} at most all at once; WebKit content process at most ${MB(peak)}${s.notice ? "; notice: " + s.notice : ""}`);
  if (errors.length) console.log("  errors:", errors.join("; "));
  ok("  no crash or page error", !errors.length);
  await ctx.close();
}

const simDone = (p) => p.waitForFunction(() => {
  const s = document.querySelector(".stats"), e = document.querySelector(".results .error");
  return e || (s && !s.textContent.includes("running"));
}, null, { timeout: 300000 });

console.log("Table, seed 11:");
await page("#seed=11", async (p) => {
  await p.waitForFunction(() => document.querySelector(".par strong"), null, { timeout: 120000 });
  const got = await p.$$eval("table.dd tbody tr", (rows) => rows.map((r) => [...r.querySelectorAll("td")].map((td) => +td.textContent)));
  const pbn = (await p.textContent(".pbn-out code")).trim();
  const xs = execFileSync(root + "dd", [pbn], { encoding: "utf8", stdio: ["ignore", "pipe", "ignore"] }).trim().split(" ").map(Number);
  const want = [0, 2, 1, 3].map((d) => [4, 0, 1, 2, 3].map((s) => xs[s * 4 + d]));
  ok("  table matches dd", JSON.stringify(got) === JSON.stringify(want));
});

for (const [name, hash] of [
  ["Erik's link: 4S by E after a trick, the leader's view", "#seed=931856&c=4S&by=E&play=DA,D2,D3,D4&tab=sim&view=leader&n=200&sseed=1"],
  ["README simulation", "#deal=N:AJ4.K94.KQ8.T862+KQ86.873.A62.KJ5+73.AQJ65.93.AQ43+T952.T2.JT754.97&c=4H&by=S&tab=sim&view=leader&rule=S.hcp=15-19&rule=S.H=5%2B&rule=N.hcp=8-11&rule=N.H=3%2B&n=200&sseed=11"],
]) {
  console.log(`${name}:`);
  await page(hash, async (p) => {
    await p.waitForSelector("button.run");
    await p.click("button.run");
    await simDone(p);
    const err = await p.$eval(".results", (r) => r.querySelector(".error")?.textContent || "");
    const stats = await p.$eval(".results", (r) => r.querySelector(".stats")?.textContent || "");
    ok("  simulation finished", !err && /kept 200/.test(stats), err || stats.replace(/\s+/g, " ").slice(0, 90));
    if (name.startsWith("README")) {
      const simText = execFileSync(root + "sim", ["deal=N:- - - T952.T2.JT754.97", "contract=4H", "by=S", "S.hcp=15-19", "S.H=5+", "N.hcp=8-11", "N.H=3+", "n=200", "seed=11"], { encoding: "utf8" });
      const want = simText.split("\n").map((l) => l.match(/^(\S+)\s+(\d+\.\d\d)\s+(\d+\.\d%)$/)).filter(Boolean).map((m) => `${m[1]} ${m[2]} ${m[3]}`);
      const got = await p.$$eval("table.simrows tbody tr", (rs) => rs.map((r) => `${r.dataset.key} ${r.dataset.tricks} ${r.dataset.makes}`));
      ok("  rows match sim", JSON.stringify(got) === JSON.stringify(want));
    }
  });
}
await browser.close();
console.log(bad ? `${bad} iPhone checks failed` : "all iPhone checks passed");
process.exit(bad ? 1 : 0);
