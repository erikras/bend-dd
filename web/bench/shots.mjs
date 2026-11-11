// Opens the page in Chromium and checks it: a random deal and a pasted one against
// dd, a play-through of best cards against the table, and the README's simulation
// against sim row for row. Saves screenshots to web/shots/. Needs Playwright; with it installed elsewhere, run
// as NODE_PATH=<its node_modules> node web/bench/shots.mjs [url]. CHROMIUM=<binary>
// launches that Chromium instead of Playwright's own.
import { createRequire } from "node:module";
import { execFileSync } from "node:child_process";
import { mkdirSync } from "node:fs";

const require = createRequire(import.meta.url);
const { chromium } = require("playwright");
const url = process.argv[2] || "http://localhost:8642/";
const root = new URL("../../", import.meta.url).pathname;
const shots = root + "web/shots/";
mkdirSync(shots, { recursive: true });

// The table as the page shows it, N S E W by NT ♠ ♥ ♦ ♣, against dd's line.
const COLS = [4, 0, 1, 2, 3], ROWS = [0, 2, 1, 3];
function want(pbn) {
  const xs = execFileSync(root + "dd", [pbn], { encoding: "utf8", stdio: ["ignore", "pipe", "ignore"] }).trim().split(" ").map(Number);
  return ROWS.map((d) => COLS.map((s) => xs[s * 4 + d]));
}
async function table(page) {
  await page.waitForFunction(() => document.querySelector(".par strong"), null, { timeout: 60000 });
  return page.$$eval("table.dd tbody tr", (rows) => rows.map((r) => [...r.querySelectorAll("td")].map((td) => +td.textContent)));
}

const browser = await chromium.launch(process.env.CHROMIUM ? { executablePath: process.env.CHROMIUM } : {});
let bad = 0;
const check = (name, got, exp) => {
  const ok = JSON.stringify(got) === JSON.stringify(exp);
  if (!ok) bad++;
  console.log(`${name}: ${ok ? "ok" : "DIFFERENT " + JSON.stringify(got) + " vs " + JSON.stringify(exp)}`);
};

for (const [name, viewport, hash] of [
  ["desktop", { width: 1100, height: 760 }, "#seed=11&dealer=S&vul=EW"],
  ["phone", { width: 390, height: 844 }, "#seed=11&dealer=S&vul=EW"],
]) {
  const page = await browser.newPage({ viewport, deviceScaleFactor: 2 });
  const t0 = Date.now();
  await page.goto(url + hash);
  const got = await table(page);
  const pbn = await page.textContent(".pbn-out code");
  console.log(`${name}: seed 11 solved in ${Date.now() - t0} ms including the page load; ${await page.textContent(".par")}`);
  check(`${name} table`, got, want(pbn.trim()));
  // The solve times: no row under the table, and a details toggle that names them.
  check(`${name}: no time row under the table`, await page.$$eval("table.dd tfoot", (x) => x.length), 0);
  await page.click("details.meta summary");
  const tm = await page.textContent("details.meta .times");
  check(`${name}: details show each strain's time`, /NT \d+\.\d\d s, ♠ \d+\.\d\d s, ♥ \d+\.\d\d s, ♦ \d+\.\d\d s, ♣ \d+\.\d\d s/.test(tm), true);
  await page.screenshot({ path: `${shots}${name}.png`, fullPage: true });
  await page.close();
}

// A pasted deal, starting from East.
const page = await browser.newPage({ viewport: { width: 1100, height: 760 }, deviceScaleFactor: 2 });
await page.goto(url + "#seed=5");
await table(page);
await page.fill("input.pbn", "E:8763.Q6.JT753.75 Q9.AT92.AQ82.AT9 KJ42.874.K4.J862 AT5.KJ53.96.KQ43");
await page.click("form:has(input.pbn) button");
await page.waitForFunction(() => location.hash.includes("deal="));
const got = await table(page);
check("pasted deal table", got, want("N:AT5.KJ53.96.KQ43 8763.Q6.JT753.75 Q9.AT92.AQ82.AT9 KJ42.874.K4.J862"));
console.log(`pasted deal: ${await page.textContent(".par")}, link ${page.url().replace(/^.*#/, "#")}`);
await page.screenshot({ path: `${shots}pasted.png`, fullPage: true });

await page.close();

// Play: pick 4H by West from the table, play the best card four times, step back.
const SIM_URL = "#deal=N:AJ4.K94.KQ8.T862+KQ86.873.A62.KJ5+73.AQJ65.93.AQ43+T952.T2.JT754.97&c=4H&by=S&tab=sim&view=leader&rule=S.hcp=15-19&rule=S.H=5%2B&rule=N.hcp=8-11&rule=N.H=3%2B&n=200&sseed=11";
const bestValue = (p) => p.waitForSelector(".group.best .val", { timeout: 60000 }).then((e) => e.textContent()).then((t) => +t.replace(/−.*/, ""));
for (const [name, viewport] of [["play", { width: 1100, height: 900 }], ["play-phone", { width: 390, height: 844 }]]) {
  const p = await browser.newPage({ viewport, deviceScaleFactor: 2 });
  await p.goto(url + "#seed=11");
  await table(p);
  // The diagram: North at the top until a contract is picked, then declarer at the
  // bottom, dummy at the top, and the defenders in order round the table.
  const where = () => p.evaluate(() => [0, 1, 2, 3].map((i) => document.querySelector(`.hand.pos${i}`).dataset.seat + document.querySelector(`.compass .c${i}`).textContent.slice(0, 1)).join(" "));
  check(`${name}: North at the top with no contract (top right bottom left)`, await where(), "NN EE SS WW");
  await p.click('button[aria-label="play ♥ by West"]');
  await p.waitForFunction(() => location.hash.includes("c=4H&by=W"));
  check(`${name}: West declaring is at the bottom`, await where(), "EE SS WW NN");
  const first = await bestValue(p);
  check(`${name}: best lead keeps declarer to the table's 10`, first, 10);
  for (let i = 0; i < 4; i++) {
    const n = await p.evaluate(() => (location.hash.match(/play=([^&]*)/)?.[1] || "").split(",").filter(Boolean).length);
    const v = await bestValue(p);
    if (v !== 10) check(`${name}: best card after ${n} cards`, v, 10);
    await p.click(".group.best button.card");
    await p.waitForFunction((k) => (location.hash.match(/play=([^&]*)/)?.[1] || "").split(",").filter(Boolean).length === k, n + 1);
  }
  const tricks = await p.$$eval("ol.tricks li", (x) => x.length);
  check(`${name}: one trick in the list`, tricks, 1);
  await p.click(".group.best button.card");
  await bestValue(p);
  await p.keyboard.press("ArrowLeft");
  await p.waitForFunction(() => location.hash.includes("at=4"));
  await p.keyboard.press("ArrowRight");
  await p.waitForFunction(() => !location.hash.includes("at="));
  await bestValue(p);
  console.log(`${name}: ${await p.textContent(".count")}, link ${p.url().replace(/^.*#/, "#")}`);
  await p.screenshot({ path: `${shots}${name}.png`, fullPage: true });
  await p.close();
}

// Simulate: the README example, against sim row for row.
const simText = execFileSync(root + "sim", ["deal=N:- - - T952.T2.JT754.97", "contract=4H", "by=S", "S.hcp=15-19", "S.H=5+", "N.hcp=8-11", "N.H=3+", "n=200", "seed=11"], { encoding: "utf8" });
const simRows = simText.split("\n").map((l) => l.match(/^(\S+)\s+(\d+\.\d\d)\s+(\d+\.\d%)$/)).filter(Boolean).map((m) => `${m[1]} ${m[2]} ${m[3]}`);
const simKept = simText.match(/Dealt \d+ layouts and kept \d+/)[0];
for (const [name, viewport] of [["sim", { width: 1100, height: 900 }], ["sim-phone", { width: 390, height: 844 }]]) {
  const p = await browser.newPage({ viewport, deviceScaleFactor: 2 });
  await p.goto(url + SIM_URL);
  await p.waitForSelector("button.run");
  const t = Date.now();
  await p.click("button.run");
  await p.waitForFunction(() => document.querySelector(".stats") && !document.querySelector(".stats").textContent.includes("running"), null, { timeout: 120000 });
  const ms = Date.now() - t;
  const got = await p.$$eval("table.simrows tbody tr", (rs) => rs.map((r) => `${r.dataset.key} ${r.dataset.tricks} ${r.dataset.makes}`));
  const kept = (await p.textContent(".stats")).match(/Dealt \d+ layouts and kept \d+/)[0];
  check(`${name}: README simulation rows`, got, simRows);
  check(`${name}: layouts dealt and kept`, kept, simKept);
  console.log(`${name}: ${ms} ms in the page; hidden hands shown: ${await p.$$eval(".hand.hidden", (x) => x.length)}`);
  // Nothing on the page gives the hidden hands away until asked.
  const leaks = await p.evaluate(() => [!!document.querySelector("table.dd"), !!document.querySelector(".par"), !!document.querySelector(".pbn-out"), document.body.innerText.includes("AJ4.K94")]);
  check(`${name}: table, par and deal hidden`, leaks, [false, false, false, false]);
  await p.screenshot({ path: `${shots}${name}.png`, fullPage: true });
  await p.click("button.reveal");
  const shown = await p.evaluate(() => [!!document.querySelector("table.dd"), !!document.querySelector(".par"), !!document.querySelector(".pbn-out"), document.querySelectorAll(".hand.hidden").length]);
  check(`${name}: "Show the full deal" shows them`, shown, [true, true, true, 0]);
  await p.close();
}

await browser.close();
console.log(bad ? `${bad} checks failed` : "all page checks passed");
process.exit(bad ? 1 : 0);
