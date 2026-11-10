// Checks the hand diagram's layout in Chromium: West and East the same distance from
// the compass, North and South centred on it, and nothing wider than its card, for
// long hands (a 7-card suit with a 10), the play-through's card boxes and the
// rotated diagram, at desktop, medium and phone widths. The page is light only:
// under an emulated dark system setting it must stay light, with black spades and
// clubs and red hearts and diamonds. Saves web/shots/layout-<case>-<width>-<scheme>.png. Run as web/bench/shots.mjs is.
import { createRequire } from "node:module";
import { mkdirSync } from "node:fs";

const require = createRequire(import.meta.url);
const { chromium } = require("playwright");
const url = process.argv[2] || "http://localhost:8642/";
const shots = new URL("../shots/", import.meta.url).pathname;
mkdirSync(shots, { recursive: true });

const LONG = "deal=N:AJ5.KQJT9.AK.T98+432.876.QJT98.76+.A5432.765432.AK+KQT9876...QJ5432";
const cases = [
  ["long", `#${LONG}`],
  ["long-play", `#${LONG}&c=4S&by=W`],
  ["seed11-4HW", "#seed=11&c=4H&by=W&play=S7"],
];
const widths = [["desktop", 1100], ["medium", 582], ["phone", 390]];
const browser = await chromium.launch(process.env.CHROMIUM ? { executablePath: process.env.CHROMIUM } : {});
let bad = 0;
for (const [name, hash] of cases) for (const [wname, w] of widths) for (const scheme of ["light", "dark"]) {
  const p = await browser.newPage({ viewport: { width: w, height: 900 }, deviceScaleFactor: 2, colorScheme: scheme });
  await p.goto(url + hash);
  await p.waitForSelector(".hand");
  if (name.includes("play")) await p.waitForSelector(".group .val", { timeout: 60000 });
  else await p.waitForFunction(() => document.querySelector(".par strong") || document.querySelector(".secret"), null, { timeout: 60000 });
  const m = await p.evaluate(() => {
    const r = (e) => e && e.getBoundingClientRect();
    const card = r(document.querySelector(".diagram"));
    const box = (pos) => {
      const h = document.querySelector(`.hand.pos${pos}`);
      // The hand's content, not its grid cell.
      const kids = [...h.querySelectorAll(".who, .suit")].map(r);
      return { left: Math.min(...kids.map((k) => k.left)), right: Math.max(...kids.map((k) => k.right)) };
    };
    const c = document.querySelector(".compass");
    const cv = c && getComputedStyle(c).display !== "none" ? r(c) : null;
    const [t, rt, b, l] = [0, 1, 2, 3].map(box);
    return { card: { left: card.left, right: card.right }, cv: cv && { left: cv.left, right: cv.right, mid: (cv.left + cv.right) / 2 }, t, rt, b, l, overflow: document.documentElement.scrollWidth > innerWidth + 1 };
  });
  const notes = [];
  // Light whatever the system says, with the suits in their colours everywhere.
  const look = await p.evaluate(() => {
    const lum = (c) => { const [r, g, b] = c.match(/\d+/g).map(Number); return (r + g + b) / 3; };
    const red = (c) => { const [r, g, b] = c.match(/\d+/g).map(Number); return r > 150 && g < 80 && b < 80; };
    const syms = [...document.querySelectorAll(".s0, .s1, .s2, .s3")].map((e) => [e.classList.contains("s0") || e.classList.contains("s3"), getComputedStyle(e).color]);
    return {
      bg: lum(getComputedStyle(document.body).backgroundColor),
      card: lum(getComputedStyle(document.querySelector(".diagram")).backgroundColor),
      black: syms.filter(([b]) => b).every(([, c]) => lum(c) < 60),
      red: syms.filter(([b]) => !b).every(([, c]) => red(c)),
      n: syms.length,
    };
  });
  if (look.bg < 230 || look.card < 230) notes.push(`not light: background ${look.bg.toFixed(0)}, card ${look.card.toFixed(0)}`);
  if (!look.black || !look.red || look.n < 16) notes.push(`suit colours wrong (black ${look.black}, red ${look.red}, ${look.n} symbols)`);
  if (m.overflow) notes.push("page scrolls sideways");
  for (const h of [m.t, m.rt, m.b, m.l]) if (h.left < m.card.left - 1 || h.right > m.card.right + 1) notes.push("a hand spills out of the card");
  if (m.cv && wname !== "phone") {
    for (const [nm, h] of [["north", m.t], ["south", m.b]]) {
      const mid = (h.left + h.right) / 2;
      // A hand's text is left-aligned, so its centre sits within half a card width.
      if (Math.abs(mid - m.cv.mid) > 12) notes.push(`${nm} is ${(mid - m.cv.mid).toFixed(0)} px off the compass's centre`);
    }
    const gl = m.cv.left - m.l.right, gr = m.rt.left - m.cv.right;
    if (Math.abs(gl - gr) > 1.5) notes.push(`gaps differ: west ${gl.toFixed(1)}, east ${gr.toFixed(1)}`);
    if (gl > 40) notes.push(`west is ${gl.toFixed(0)} px from the compass`);
  }
  const sideGap = [m.l.left - m.card.left, m.card.right - m.rt.right];
  const cardMid = (m.card.left + m.card.right) / 2;
  if (m.cv && wname !== "phone") {
    if (Math.abs(m.cv.mid - cardMid) > 2) notes.push(`the compass is ${(m.cv.mid - cardMid).toFixed(0)} px off the card's centre`);
  } else if (Math.abs(sideGap[0] - sideGap[1]) > 40) notes.push(`not centred in the card: ${sideGap.map((x) => x.toFixed(0)).join(" vs ")}`);
  const ok = !notes.length;
  if (!ok) bad++;
  console.log(`${name} ${wname} ${scheme}: ${ok ? "ok" : notes.join("; ")}`);
  await p.locator(".diagram").screenshot({ path: `${shots}layout-${name}-${wname}-${scheme}.png` });
  if (name === "seed11-4HW" && wname === "medium" && scheme === "dark") await p.screenshot({ path: `${shots}medium-system-dark.png`, fullPage: true });
  await p.close();
}
await browser.close();
console.log(bad ? `${bad} layouts wrong` : "all layouts ok");
process.exit(bad ? 1 : 0);
