// Opens the page in Chromium, checks a random deal and a pasted one against dd, and
// saves screenshots to web/shots/. Needs Playwright; with it installed elsewhere, run
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
  console.log(`${name}: ${ok ? "same as dd" : "DIFFERENT " + JSON.stringify(got) + " vs " + JSON.stringify(exp)}`);
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

await browser.close();
process.exit(bad ? 1 : 0);
