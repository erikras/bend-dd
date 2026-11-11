import { render } from "preact";
import { useEffect, useMemo, useRef, useState } from "preact/hooks";
import { Deal, Hand, Par, SEATS, SEAT_NAMES, STRAINS, SUITS, SUIT_NAMES, Table, Vul, hcp, par, parsePbn, printPbn } from "./bridge";
import { Pool, poolSize } from "./pool";
import { Cands, Card, Option, Play, cardText, options, parseCard, replay } from "./play";
import { SimOut, View, chunks, merge, percent, ratio, rows, setupText, visible } from "./sim";

const pool = new Pool(poolSize());
(globalThis as any).ddPool = pool; // for the tests: pool.stats and pool.size
const STRAIN_LETTERS = ["S", "H", "D", "C", "NT"];

// ---------------------------------------------------------------------------
// The state, all of it in the URL fragment:
//   seed=11 or deal=N:…, dealer=N, vul=None,
//   c=4H&by=S for the contract, play=DJ,D2,…&at=5 for the cards played and where
//   the view is, tab=sim&view=leader&rule=S.hcp=15-19&n=200&sseed=11 for the simulator.

type Tab = "play" | "sim";
type State = {
  seed?: number; pbn?: string; dealer: number; vul: Vul;
  level?: number; strain?: number; by?: number; plays: string[]; at: number;
  tab: Tab; view: View; rules: string[]; n: number; simSeed: number;
};

function readHash(): State {
  const p = new URLSearchParams(location.hash.slice(1));
  const dealer = Math.max(0, SEATS.indexOf((p.get("dealer") || "N").toUpperCase()));
  const v = p.get("vul") as Vul;
  const vul: Vul = ["None", "NS", "EW", "All"].includes(v) ? v : "None";
  const seed = p.get("seed");
  const s: State = {
    dealer, vul, plays: [], at: 0, tab: p.get("tab") === "sim" ? "sim" : "play",
    view: p.get("view") === "declarer" ? "declarer" : "leader",
    rules: p.getAll("rule").filter((r) => r.includes("=")),
    n: Math.max(1, Math.min(10000, +(p.get("n") || 200) || 200)),
    simSeed: +(p.get("sseed") || 1) || 1,
  };
  const pbn = p.get("deal");
  if (pbn) s.pbn = pbn;
  else if (seed && /^\d+$/.test(seed)) s.seed = +seed;
  else s.seed = 1 + Math.floor(Math.random() * 1000000);
  const c = (p.get("c") || "").toUpperCase().match(/^([1-7])(NT|[SHDC])$/);
  const by = SEATS.indexOf((p.get("by") || "").toUpperCase());
  if (c && by >= 0) {
    s.level = +c[1];
    s.strain = STRAIN_LETTERS.indexOf(c[2]);
    s.by = by;
    s.plays = (p.get("play") || "").split(/[ ,]+/).filter((x) => parseCard(x));
    const at = p.get("at");
    s.at = at !== null && /^\d+$/.test(at) ? Math.min(+at, s.plays.length) : s.plays.length;
  }
  return s;
}

function writeHash(s: State) {
  const p = new URLSearchParams();
  if (s.pbn) p.set("deal", s.pbn);
  else if (s.seed !== undefined) p.set("seed", String(s.seed));
  if (s.dealer !== 0) p.set("dealer", SEATS[s.dealer]);
  if (s.vul !== "None") p.set("vul", s.vul);
  if (s.strain !== undefined && s.by !== undefined) {
    p.set("c", `${s.level}${STRAIN_LETTERS[s.strain]}`);
    p.set("by", SEATS[s.by]);
    if (s.plays.length) p.set("play", s.plays.join(","));
    if (s.at !== s.plays.length) p.set("at", String(s.at));
    if (s.tab === "sim") {
      p.set("tab", "sim");
      p.set("view", s.view);
      for (const r of s.rules) p.append("rule", r);
      p.set("n", String(s.n));
      p.set("sseed", String(s.simSeed));
    }
  }
  const h = "#" + p.toString().replace(/%3A/g, ":").replace(/%2C/g, ",").replace(/%3D/g, "=");
  if (location.hash !== h) history.replaceState(null, "", h);
}

const rankText = (r: string) => (r === "T" ? "10" : r);
const cardLabel = (c: Card) => SUITS[c.s] + rankText(c.r);

// Text with each suit symbol in its colour: black spades and clubs, red hearts and
// diamonds.
function suited(text: string) {
  return text.split(/([♠♥♦♣])/).map((x) => {
    const s = SUITS.indexOf(x);
    return s >= 0 ? <span class={`s${s}`}>{x}</span> : x;
  });
}

// ---------------------------------------------------------------------------
// The diagram

type HandMode = { kind: "view" } | { kind: "hidden" } | { kind: "play"; left: Hand; opts: Option[] | null; onPlay: (c: Card) => void };

// One suit's ranks in play: the cards still held, the ones played greyed, and for the
// player to move each legal card as a button with declarer's tricks. Cards that play
// the same sit in one group with one label.
function PlaySuit({ s, ranks, left, opts, onPlay }: { s: number; ranks: string; left: string; opts: Option[] | null; onPlay: (c: Card) => void }) {
  const items = [...ranks].map((r) => ({ r, gone: !left.includes(r), opt: opts?.find((o) => o.card.s === s && o.card.r === r) }));
  const parts: { group?: number; items: typeof items }[] = [];
  for (let i = 0; i < items.length; i++) {
    const it = items[i];
    if (!it.opt) { parts.push({ items: [it] }); continue; }
    const g = it.opt.group;
    let j = i + 1;
    while (j < items.length && (items[j].gone || items[j].opt?.group === g)) j++;
    while (j > i + 1 && items[j - 1].gone) j--;
    parts.push({ group: g, items: items.slice(i, j) });
    i = j - 1;
  }
  return (
    <div class="suit">
      <span class={`sym s${s}`} aria-label={SUIT_NAMES[s]}>{SUITS[s]}</span>
      <span class="ranks">
        {ranks === "" && "—"}
        {parts.map((part) => {
          if (part.group === undefined) {
            const it = part.items[0];
            return <span class={it.gone ? "rank gone" : "rank"}>{rankText(it.r)}</span>;
          }
          const o = part.items.find((x) => x.opt)!.opt!;
          return (
            <span class={`group${o.best ? " best" : " worse"}`} title={`Declarer takes ${o.tricks}`}>
              <span class="cards">
                {part.items.map((it) => it.gone ? <span class="rank gone">{rankText(it.r)}</span> : (
                  <button class="card" aria-label={`play ${SUIT_NAMES[s]} ${rankText(it.r)}, declarer takes ${o.tricks}`} onClick={() => onPlay({ s, r: it.r })}>{rankText(it.r)}</button>
                ))}
              </span>
              <span class="val">{o.tricks}{o.cost > 0 && <span class="cost">−{o.cost}</span>}</span>
            </span>
          );
        })}
      </span>
    </div>
  );
}

// Where a seat sits in the diagram: 0 top, 1 right, 2 bottom, 3 left. With a
// declarer, declarer is at the bottom and dummy at the top; otherwise North is.
const place = (seat: number, bottom: number) => (seat - bottom + 6) % 4;

function HandView({ seat, pos, hand, dealer, vul, mode, mover }: { seat: number; pos: number; hand: Hand; dealer: number; vul: Vul; mode: HandMode; mover: boolean }) {
  const red = vul === "All" || (vul === "NS" && seat % 2 === 0) || (vul === "EW" && seat % 2 === 1);
  return (
    <div data-seat={SEATS[seat]} class={`hand pos${pos}${mover ? " mover" : ""}${mode.kind === "hidden" ? " hidden" : ""}`}>
      <div class="who">
        <span class={red ? "name vul" : "name"}>{SEAT_NAMES[seat]}</span>
        {dealer === seat && <span class="dealer" title="dealer">D</span>}
        {mode.kind !== "hidden" && <span class="hcp">{hcp(hand)}</span>}
      </div>
      {mode.kind === "hidden" ? <div class="unseen">hidden</div>
        : mode.kind === "play" ? hand.map((r, s) => <PlaySuit s={s} ranks={r} left={mode.left[s]} opts={mover ? mode.opts : null} onPlay={mode.onPlay} />)
        : hand.map((r, s) => (
          <div class="suit">
            <span class={`sym s${s}`} aria-label={SUIT_NAMES[s]}>{SUITS[s]}</span>
            <span class="ranks">{r ? [...r].map((x) => <span class="rank">{rankText(x)}</span>) : "—"}</span>
          </div>
        ))}
    </div>
  );
}

// The compass, with the trick in progress (or the last one, faded) during play.
function Compass({ play, bottom }: { play: Play | null; bottom: number }) {
  const shown = play ? (play.current.length || !play.tricks.length ? play.current : play.tricks[play.tricks.length - 1].cards) : [];
  const last = play && !play.current.length && play.tricks.length > 0;
  return (
    <div class={`compass${play ? " playing" : ""}`}>
      {SEATS.map((s, i) => {
        const c = shown.find((x) => x.seat === i);
        return <span class={`c${place(i, bottom)}${c ? " played" : ""}${last ? " last" : ""}${play?.mover === i && !play.over ? " turn" : ""}`}>
          {c ? <b class={`s${c.card.s}`}>{cardLabel(c.card)}</b> : s}
        </span>;
      })}
      {play && <span class="mid">{play.over ? "done" : `trick ${play.tricks.length + 1}`}</span>}
    </div>
  );
}

function Diagram({ deal, dealer, vul, modes, play, bottom }: { deal: Deal; dealer: number; vul: Vul; modes: HandMode[]; play: Play | null; bottom: number }) {
  return (
    <div class="diagram"><div class="dgrid">
      {deal.map((h, seat) => <HandView seat={seat} pos={place(seat, bottom)} hand={h} dealer={dealer} vul={vul} mode={modes[seat]} mover={!!play && !play.over && play.mover === seat && modes[seat].kind === "play"} />)}
      <Compass play={play} bottom={bottom} />
    </div></div>
  );
}

// ---------------------------------------------------------------------------
// The table: declarers down, strains across, as dd --random prints it. A cell
// picks that contract and declarer.

const ROWS = [0, 2, 1, 3]; // N S E W
const COLS = [4, 0, 1, 2, 3]; // NT ♠ ♥ ♦ ♣

function TableView({ table, pick, chosen }: { table: Table; pick: (s: number, seat: number, tricks: number) => void; chosen?: [number, number] }) {
  return (
    <table class="dd">
      <thead>
        <tr>
          <th></th>
          {COLS.map((s) => <th class={`st s${s}`}>{STRAINS[s]}</th>)}
        </tr>
      </thead>
      <tbody>
        {ROWS.map((seat) => (
          <tr>
            <th>{SEATS[seat]}</th>
            {COLS.map((s) => {
              const v = table[s]?.[seat];
              const on = chosen && chosen[0] === s && chosen[1] === seat;
              return <td class={`${v === undefined ? "wait" : v >= 7 ? "make" : ""}${on ? " chosen" : ""}`}>
                {v === undefined ? "·" : <button class="cell" aria-label={`play ${STRAINS[s]} by ${SEAT_NAMES[seat]}`} onClick={() => pick(s, seat, v)}>{v}</button>}
              </td>;
            })}
          </tr>
        ))}
      </tbody>
    </table>
  );
}

// ---------------------------------------------------------------------------
// The play pane

function PlayPane({ state, play, set, pending }: { state: State; play: Play; set: (s: Partial<State>) => void; pending: boolean }) {
  const decl = state.by!;
  const back = () => set({ at: Math.max(0, state.at - 1) });
  const fwd = () => set({ at: Math.min(state.plays.length, state.at + 1) });
  const undo = () => set({ plays: state.plays.slice(0, Math.max(0, state.at - 1)), at: Math.max(0, state.at - 1) });
  const status = play.over ? "Every card has been played."
    : `${SEAT_NAMES[play.mover]} to ${play.current.length ? "play" : "lead"}${play.mover === (decl + 2) % 4 ? " (dummy)" : ""}.`;
  const need = state.level! + 6;
  return (
    <div class="pane play">
      <div class="row between">
        <div>
          <strong>{state.level}{suited(STRAINS[state.strain!])}</strong> by {SEAT_NAMES[decl]}
          <select aria-label="level" value={state.level} onChange={(e) => set({ level: +(e.target as HTMLSelectElement).value })}>
            {[1, 2, 3, 4, 5, 6, 7].map((l) => <option value={l}>{l}</option>)}
          </select>
        </div>
        <div class="count" aria-live="polite">Declarer <b>{play.won[0]}</b> · Defenders <b>{play.won[1]}</b> <span class="muted">(needs {need})</span></div>
      </div>
      <p class="status">{status} {pending && <span class="wait">Solving…</span>}</p>
      <div class="row">
        <button type="button" onClick={undo} disabled={state.at === 0} title="Undo the last card">Undo</button>
        <button type="button" onClick={() => set({ at: 0 })} disabled={state.at === 0} title="Home">⏮</button>
        <button type="button" onClick={back} disabled={state.at === 0} title="Back (←)">◀ Back</button>
        <button type="button" onClick={fwd} disabled={state.at === state.plays.length} title="Forward (→)">Forward ▶</button>
        <button type="button" onClick={() => set({ at: state.plays.length })} disabled={state.at === state.plays.length} title="End">⏭</button>
      </div>
      <p class="muted small">The numbers under the cards of the player to move are declarer's tricks with each; green is best, and −1, −2 is what a card costs. Cards that play the same share a box. Arrow keys step through the play.</p>
      {play.tricks.length > 0 && (
        <ol class="tricks">
          {play.tricks.map((t) => (
            <li>{t.cards.map((x) => <span class={x.seat === t.winner ? "won" : ""}>{SEATS[x.seat]} <b class={`s${x.card.s}`}>{cardLabel(x.card)}</b></span>)}</li>
          ))}
        </ol>
      )}
    </div>
  );
}

// ---------------------------------------------------------------------------
// The simulate pane

const WHATS = ["hcp", "S", "H", "D", "C"];
const WHAT_LABEL: Record<string, string> = { hcp: "points", S: "♠", H: "♥", D: "♦", C: "♣" };

type SimRun = { setup: string; n: number; seed: number; out: SimOut | null; done: number; total: number; ms: number; error: string; running: boolean };

function SimPane({ state, deal, set, run, start, stop, hidden }: { state: State; deal: Deal; set: (s: Partial<State>) => void; run: SimRun | null; start: () => void; stop: () => void; hidden: number[] }) {
  const parsed = state.rules.map((r) => { const m = r.match(/^([NESW])\.([^=]+)=(.*)$/); return m ? { seat: m[1], what: m[2], range: m[3] } : { seat: SEATS[hidden[0] ?? 0], what: "hcp", range: "" }; });
  const write = (xs: typeof parsed) => set({ rules: xs.map((x) => `${x.seat}.${x.what}=${x.range}`) });
  const out = run?.out;
  let sbar = (_: number) => 0, mbar = (_: number) => 0;
  return (
    <div class="pane sim">
      <div class="row">
        <span class="muted">Whose view:</span>
        <label><input type="radio" name="view" checked={state.view === "leader"} onChange={() => set({ view: "leader" })} /> opening leader</label>
        <label><input type="radio" name="view" checked={state.view === "declarer"} onChange={() => set({ view: "declarer" })} /> declarer and dummy</label>
      </div>
      <div class="rules">
        <div class="muted small">Rules from the auction, for hidden hands (as sim takes them: 11-15, 5+, -3, 4):</div>
        {parsed.map((x, i) => (
          <div class="row rule">
            <select aria-label="seat" value={x.seat} onChange={(e) => { const y = parsed.slice(); y[i] = { ...x, seat: (e.target as HTMLSelectElement).value }; write(y); }}>
              {hidden.map((s) => <option value={SEATS[s]}>{SEAT_NAMES[s]}</option>)}
            </select>
            <select aria-label="what" value={x.what} onChange={(e) => { const y = parsed.slice(); y[i] = { ...x, what: (e.target as HTMLSelectElement).value }; write(y); }}>
              {WHATS.map((w) => <option value={w}>{WHAT_LABEL[w]}</option>)}
            </select>
            <input aria-label="range" size={6} value={x.range} placeholder="11-15" onChange={(e) => { const y = parsed.slice(); y[i] = { ...x, range: (e.target as HTMLInputElement).value.trim() }; write(y); }} />
            <button type="button" aria-label="remove rule" onClick={() => write(parsed.filter((_, j) => j !== i))}>✕</button>
          </div>
        ))}
        <button type="button" onClick={() => write([...parsed, { seat: SEATS[hidden[0] ?? 0], what: "hcp", range: "" }])} disabled={!hidden.length}>Add a rule</button>
      </div>
      <div class="row">
        <label>Layouts <input aria-label="layouts" inputMode="numeric" size={5} value={state.n} onChange={(e) => set({ n: Math.max(1, Math.min(10000, +(e.target as HTMLInputElement).value || 200)) })} /></label>
        <label>Seed <input aria-label="sim seed" inputMode="numeric" size={8} value={state.simSeed} onChange={(e) => set({ simSeed: +(e.target as HTMLInputElement).value || 1 })} /></label>
        <button type="button" onClick={() => set({ simSeed: 1 + Math.floor(Math.random() * 1000000) })} title="a new seed">🎲</button>
        {run?.running ? <button type="button" class="stop" onClick={stop}>Stop</button> : <button class="run" onClick={start}>Simulate</button>}
      </div>
      {run && (
        <div class="results">
          <div class="progress" role="progressbar" aria-valuemin={0} aria-valuemax={run.total} aria-valuenow={run.done}><div style={{ width: run.running ? `${(100 * run.done) / Math.max(1, run.total)}%` : "100%" }} /></div>
          {run.error && <p class="error">{run.error}</p>}
          {out && (
            <>
              <p class="stats">
                Dealt <span class="tries">{out.tries}</span> layouts and kept <span class="kept">{out.deals}</span> ({percent(out.deals, out.tries)}), {(run.ms / 1000).toFixed(1)} s{run.running ? ", running" : ""} with {pool.size} workers.
                {!run.running && out.deals < run.n && ` Only ${out.deals} of the ${run.n} fit before the tries ran out.`}
              </p>
              {(() => { const rs = rows(out); const span = (xs: number[]) => { const lo = Math.min(...xs), hi = Math.max(...xs); return (v: number) => (hi === lo ? 100 : 10 + (90 * (v - lo)) / (hi - lo)); }; sbar = span(rs.map((r) => r.sum)); mbar = span(rs.map((r) => r.makes)); return null; })()}
              <table class="simrows">
                <thead><tr><th>Card</th><th>Tricks</th><th></th><th>Makes</th><th></th></tr></thead>
                <tbody>
                  {rows(out).map((r) => (
                    <tr data-key={r.key} data-tricks={ratio(r.sum, out.deals)} data-makes={percent(r.makes, out.deals)}>
                      <th class={`s${r.card >> 4}`}>{SUITS[r.card >> 4]}{[...r.run].map(rankText).join("")}</th>
                      <td class="num">{ratio(r.sum, out.deals)}</td>
                      <td class="bar"><div style={{ width: `${sbar(r.sum)}%` }} /></td>
                      <td class="num">{percent(r.makes, out.deals)}</td>
                      <td class="bar makes"><div style={{ width: `${mbar(r.makes)}%` }} /></td>
                    </tr>
                  ))}
                </tbody>
              </table>
              <p class="muted small">Tricks are declarer's, on average. Makes is how often declarer takes {out.goal} or more. The bars run from the lowest row to the highest. Best for {SEAT_NAMES[out.mover]} first. Same as <code>sim</code> with seed={run.seed} n={run.n}.</p>
            </>
          )}
        </div>
      )}
    </div>
  );
}

// ---------------------------------------------------------------------------
// The page

function App() {
  const [state, setState] = useState<State>(readHash);
  const [deal, setDeal] = useState<Deal | null>(null);
  const [error, setError] = useState("");
  const [table, setTable] = useState<Table>([null, null, null, null, null]);
  const [times, setTimes] = useState<(number | null)[]>([null, null, null, null, null]);
  const [total, setTotal] = useState<number | null>(null);
  const [paste, setPaste] = useState("");
  const [seedText, setSeedText] = useState("");
  const [cands, setCands] = useState<Map<string, Cands>>(new Map());
  const [simRun, setSimRun] = useState<SimRun | null>(null);
  const [reveal, setReveal] = useState(false);
  const run = useRef(0);
  const simId = useRef(0);
  const set = (s: Partial<State>) => setState((old) => ({ ...old, ...s }));

  useEffect(() => {
    const on = () => setState(readHash());
    addEventListener("hashchange", on);
    return () => removeEventListener("hashchange", on);
  }, []);

  useEffect(() => writeHash(state), [state]);

  // The deal from the state: from the solver for a seed, or read from PBN.
  useEffect(() => {
    const me = ++run.current;
    setError("");
    if (state.pbn) {
      const d = parsePbn(state.pbn);
      if (typeof d === "string") { setError(d); setDeal(null); }
      else setDeal(d);
    } else if (state.seed !== undefined) {
      setSeedText(String(state.seed));
      pool.run(["--random", String(state.seed)]).then((pbn) => {
        if (run.current !== me) return;
        const d = parsePbn(pbn);
        if (typeof d === "string") setError(d);
        else setDeal(d);
      }, (e) => run.current === me && setError(e.message));
    }
  }, [state.seed, state.pbn]);

  // Solve it strain by strain, each in a worker of its own.
  const pbn = deal ? printPbn(deal) : "";
  useEffect(() => {
    if (!deal) return;
    const me = run.current;
    pool.clear();
    setCands(new Map());
    setTable([null, null, null, null, null]);
    setTimes([null, null, null, null, null]);
    setTotal(null);
    const t0 = performance.now();
    let left = 5;
    for (const s of [4, 0, 1, 2, 3]) {
      pool.run(["--strain", String(s), pbn]).then((out) => {
        if (run.current !== me) return;
        if (out.startsWith("error")) { setError(out); return; }
        const xs = out.split(" ").map(Number);
        const ms = performance.now() - t0;
        setTable((t) => { const u = t.slice(); u[s] = xs; return u; });
        setTimes((t) => { const u = t.slice(); u[s] = ms; return u; });
        if (--left === 0) setTotal(ms);
      }, (e) => { if (run.current === me && e.message !== "cancelled") setError(e.message); });
    }
  }, [pbn]);

  const done = table.every((x) => x);
  const parResult: Par | null = useMemo(
    () => (done ? par(table as number[][], state.vul, state.dealer) : null),
    [done, table, state.vul, state.dealer]
  );

  // The play so far, up to where the view is.
  const playing = deal && state.strain !== undefined && state.by !== undefined;
  const sofar = state.plays.slice(0, state.at);
  const play: Play | null = useMemo(
    () => (playing ? replay(deal!, state.strain!, state.by!, sofar) : null),
    [pbn, state.strain, state.by, sofar.join(",")]
  );
  const posKey = playing ? `${pbn}|${state.strain}|${state.by}|${sofar.join(" ")}` : "";
  const here = cands.get(posKey);
  useEffect(() => {
    if (!play || play.over || play.error || cands.has(posKey)) return;
    const key = posKey;
    pool.run(["--cards", pbn, STRAIN_LETTERS[state.strain!], SEATS[state.by!], sofar.join(" ")]).then((out) => {
      const r = JSON.parse(out);
      if (r.error) { setError(r.error); return; }
      setCands((m) => new Map(m).set(key, r));
    }, (e) => { if (e.message !== "cancelled") setError(e.message); });
  }, [posKey]);

  const playCard = (c: Card) => {
    const t = cardText(c);
    set({ plays: [...state.plays.slice(0, state.at), t], at: state.at + 1 });
  };

  // Arrow keys step through the play.
  useEffect(() => {
    const on = (e: KeyboardEvent) => {
      if (!playing || (e.target as HTMLElement).closest?.("input, select, textarea")) return;
      if (e.key === "ArrowLeft") setState((s) => ({ ...s, at: Math.max(0, s.at - 1) }));
      else if (e.key === "ArrowRight") setState((s) => ({ ...s, at: Math.min(s.plays.length, s.at + 1) }));
      else if (e.key === "Home") setState((s) => ({ ...s, at: 0 }));
      else if (e.key === "End") setState((s) => ({ ...s, at: s.plays.length }));
      else return;
      e.preventDefault();
    };
    addEventListener("keydown", on);
    return () => removeEventListener("keydown", on);
  }, [playing]);

  // The simulator: the seats in view, sim's options, and a run in chunks.
  const seen = playing ? visible(state.view, state.by!, sofar.length) : [0, 1, 2, 3];
  const hidden = [0, 1, 2, 3].filter((s) => !seen.includes(s));
  const setup = playing ? setupText(deal!, seen, `${state.level}${STRAIN_LETTERS[state.strain!]}`, state.by!, sofar, state.rules) : "";
  const stopSim = () => { simId.current++; pool.clear("sim"); setSimRun((r) => (r ? { ...r, running: false } : r)); };
  const startSim = () => {
    const me = ++simId.current;
    const parts = chunks(state.n, pool.size);
    const seed = state.simSeed;
    const t0 = performance.now();
    let out: SimOut | null = null;
    let doneN = 0;
    setSimRun({ setup, n: state.n, seed, out: null, done: 0, total: parts.length, ms: 0, error: "", running: true });
    for (const [first, count] of parts) {
      pool.run(["--sim", setup, String(seed), String(first), String(count)], "sim").then((txt) => {
        if (simId.current !== me) return;
        const r = JSON.parse(txt);
        if (r.error) { simId.current++; pool.clear("sim"); setSimRun((x) => x && { ...x, error: "sim: " + r.error, running: false }); return; }
        out = merge(out, r);
        doneN++;
        const o = out;
        setSimRun((x) => x && { ...x, out: o, done: doneN, ms: performance.now() - t0, running: doneN < parts.length });
      }, (e) => { if (simId.current === me && e.message !== "cancelled") setSimRun((x) => x && { ...x, error: e.message, running: false }); });
    }
  };
  // A result belongs to its setup; a change to the deal, the play or the rules drops it.
  useEffect(() => { if (simRun && simRun.setup !== setup) { stopSim(); setSimRun(null); } }, [setup]);

  const newSeed = () => setState({ ...state, pbn: undefined, seed: 1 + Math.floor(Math.random() * 1000000), strain: undefined, by: undefined, plays: [], at: 0 });
  const goSeed = (e: Event) => {
    e.preventDefault();
    if (/^\d+$/.test(seedText.trim())) setState({ ...state, pbn: undefined, seed: +seedText.trim(), strain: undefined, by: undefined, plays: [], at: 0 });
  };
  const goPaste = (e: Event) => {
    e.preventDefault();
    const d = parsePbn(paste);
    if (typeof d === "string") { setError(d); return; }
    setState({ ...state, seed: undefined, pbn: printPbn(d), strain: undefined, by: undefined, plays: [], at: 0 });
  };
  const pick = (s: number, seat: number, tricks: number) =>
    set({ strain: s, by: seat, level: Math.max(1, Math.min(7, tricks - 6)), plays: [], at: 0 });

  const simMode = playing && state.tab === "sim";
  // While the simulation hides hands, the table, par and the deal would show them.
  const secret = !!simMode && hidden.length > 0 && !reveal;
  const modes: HandMode[] = [0, 1, 2, 3].map((s) =>
    simMode && hidden.includes(s) && !reveal ? { kind: "hidden" }
      : play && !play.error ? { kind: "play", left: play.hands[s], opts: here ? options(play, here) : null, onPlay: playCard }
      : { kind: "view" });

  return (
    <main>
      <header>
        <h1>Double dummy</h1>
        <p class="sub">A bridge solver written in Bend, running {(globalThis as any).ddNative ? "on this device" : "in your browser"}.</p>
      </header>

      <section class="controls">
        <form onSubmit={goSeed} class="row">
          <button type="button" onClick={newSeed}>Random deal</button>
          <label>Seed <input inputMode="numeric" value={seedText} onInput={(e) => setSeedText((e.target as HTMLInputElement).value)} size={8} /></label>
          <button type="submit">Deal</button>
        </form>
        <form onSubmit={goPaste} class="row">
          <input class="pbn" placeholder="Paste a deal in PBN: N:AKQ2.K73.A84.Q52 …" value={paste} onInput={(e) => setPaste((e.target as HTMLInputElement).value)} />
          <button type="submit">Solve</button>
        </form>
        <div class="row">
          <label>Dealer <select value={SEATS[state.dealer]} onChange={(e) => set({ dealer: SEATS.indexOf((e.target as HTMLSelectElement).value) })}>
            {SEATS.map((s) => <option>{s}</option>)}
          </select></label>
          <label>Vulnerable <select value={state.vul} onChange={(e) => set({ vul: (e.target as HTMLSelectElement).value as Vul })}>
            {["None", "NS", "EW", "All"].map((v) => <option>{v}</option>)}
          </select></label>
        </div>
      </section>

      {error && <p class="error" role="alert">{error}</p>}

      {deal && (
        <section class="board">
          <div class="left">
            <Diagram deal={deal} dealer={state.dealer} vul={state.vul} modes={modes} play={play && !play.error && !simMode ? play : null} bottom={playing ? state.by! : 2} />
            {playing && play && (
              <>
                <div class="tabs" role="tablist">
                  <button type="button" role="tab" aria-selected={state.tab === "play"} class={state.tab === "play" ? "on" : ""} onClick={() => set({ tab: "play" })}>Play</button>
                  <button type="button" role="tab" aria-selected={state.tab === "sim"} class={state.tab === "sim" ? "on" : ""} onClick={() => set({ tab: "sim" })}>Simulate</button>
                </div>
                {state.tab === "play"
                  ? <PlayPane state={state} play={play} set={set} pending={!here && !play.over} />
                  : <SimPane state={state} deal={deal} set={set} run={simRun} start={startSim} stop={stopSim} hidden={hidden} />}
              </>
            )}
          </div>
          <div class="analysis">
            {secret ? (
              <div class="secret">
                <h2>Double dummy tricks</h2>
                <p class="muted">The table, par and deal are hidden while the simulation hides {hidden.map((x) => SEAT_NAMES[x]).join(", ")}, since they would give the hidden hands away.</p>
                <button type="button" class="reveal" onClick={() => setReveal(true)}>Show the full deal</button>
              </div>
            ) : (
              <>
              <h2>Double dummy tricks</h2>
              <TableView table={table} pick={pick} chosen={playing ? [state.strain!, state.by!] : undefined} />
              <p class="par">
                {parResult ? <>Par: <strong>{suited(parResult.text)}</strong></> : <span class="wait">Solving…</span>}
              </p>
              {total != null ? (
                <details class="meta">
                  <summary>Solved in {(total / 1000).toFixed(2)} s with {pool.size} workers. <span class="more">details</span></summary>
                  <p class="times">Each strain in a worker of its own, all started together; each finished after:{" "}
                    {COLS.map((s, i) => <span class="t">{i > 0 && ", "}{STRAINS[s]} {(times[s]! / 1000).toFixed(2)} s</span>)}.
                  </p>
                </details>
              ) : <p class="meta">{pool.size} workers, one strain each.</p>}
              {state.seed !== undefined && !state.pbn && <p class="meta">Same deal as <code>dd --random {state.seed}</code>.</p>}
              {!playing && done && <p class="hint">Click a number to play that contract.</p>}
              <p class="pbn-out"><code>{pbn}</code></p>
                {simMode && hidden.length > 0 && <button type="button" class="reveal" onClick={() => setReveal(false)}>Hide the full deal</button>}
              </>
            )}
          </div>
        </section>
      )}
    </main>
  );
}

render(<App />, document.getElementById("app")!);
