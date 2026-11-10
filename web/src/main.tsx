import { render } from "preact";
import { useEffect, useMemo, useRef, useState } from "preact/hooks";
import { Deal, Hand, Par, SEATS, SEAT_NAMES, STRAINS, SUITS, SUIT_NAMES, Table, Vul, hcp, par, parsePbn, printPbn } from "./bridge";
import { Pool, poolSize } from "./pool";

const pool = new Pool(poolSize());

// ---------------------------------------------------------------------------
// The state in the URL fragment: #seed=11 or #deal=N:…, with &dealer=N&vul=None.

type State = { seed?: number; pbn?: string; dealer: number; vul: Vul };

function readHash(): State {
  const p = new URLSearchParams(location.hash.slice(1));
  const dealer = Math.max(0, SEATS.indexOf((p.get("dealer") || "N").toUpperCase()));
  const v = p.get("vul") as Vul;
  const vul: Vul = ["None", "NS", "EW", "All"].includes(v) ? v : "None";
  const seed = p.get("seed");
  const pbn = p.get("deal");
  if (pbn) return { pbn, dealer, vul };
  if (seed && /^\d+$/.test(seed)) return { seed: +seed, dealer, vul };
  return { seed: 1 + Math.floor(Math.random() * 1000000), dealer, vul };
}

function writeHash(s: State) {
  const p = new URLSearchParams();
  if (s.pbn) p.set("deal", s.pbn);
  else if (s.seed !== undefined) p.set("seed", String(s.seed));
  if (s.dealer !== 0) p.set("dealer", SEATS[s.dealer]);
  if (s.vul !== "None") p.set("vul", s.vul);
  const h = "#" + p.toString().replace(/%3A/g, ":").replace(/%2C/g, ",");
  if (location.hash !== h) history.replaceState(null, "", h);
}

// ---------------------------------------------------------------------------
// The diagram

function Suit({ s, ranks }: { s: number; ranks: string }) {
  return (
    <div class="suit">
      <span class={`sym s${s}`} aria-label={SUIT_NAMES[s]}>{SUITS[s]}</span>
      <span class="ranks">{ranks ? ranks.replace(/T/g, "10").split("").join(" ").replace(/1 0/g, "10") : "—"}</span>
    </div>
  );
}

function HandView({ seat, hand, dealer, vul }: { seat: number; hand: Hand; dealer: number; vul: Vul }) {
  const red = vul === "All" || (vul === "NS" && seat % 2 === 0) || (vul === "EW" && seat % 2 === 1);
  return (
    <div class={`hand seat${seat}`}>
      <div class="who">
        <span class={red ? "name vul" : "name"}>{SEAT_NAMES[seat]}</span>
        {dealer === seat && <span class="dealer" title="dealer">D</span>}
        <span class="hcp">{hcp(hand)}</span>
      </div>
      {hand.map((r, s) => <Suit s={s} ranks={r} />)}
    </div>
  );
}

function Diagram({ deal, dealer, vul }: { deal: Deal; dealer: number; vul: Vul }) {
  return (
    <div class="diagram">
      {deal.map((h, seat) => <HandView seat={seat} hand={h} dealer={dealer} vul={vul} />)}
      <div class="compass" aria-hidden="true">
        {SEATS.map((s, i) => <span class={`c${i}`}>{s}</span>)}
      </div>
    </div>
  );
}

// ---------------------------------------------------------------------------
// The table: declarers down, strains across, as dd --random prints it.

const ROWS = [0, 2, 1, 3]; // N S E W
const COLS = [4, 0, 1, 2, 3]; // NT ♠ ♥ ♦ ♣

function TableView({ table, times }: { table: Table; times: (number | null)[] }) {
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
              return <td class={v === undefined ? "wait" : v >= 7 ? "make" : ""}>{v === undefined ? "·" : v}</td>;
            })}
          </tr>
        ))}
      </tbody>
      <tfoot>
        <tr>
          <th></th>
          {COLS.map((s) => <td class="ms">{times[s] == null ? "" : (times[s]! / 1000).toFixed(2)}</td>)}
        </tr>
      </tfoot>
    </table>
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
  const run = useRef(0);

  useEffect(() => {
    const on = () => setState(readHash());
    addEventListener("hashchange", on);
    return () => removeEventListener("hashchange", on);
  }, []);

  // The deal from the state: from the solver for a seed, or read from PBN.
  useEffect(() => {
    writeHash(state);
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

  useEffect(() => writeHash(state), [state.dealer, state.vul]);

  // Solve it strain by strain, each in a worker of its own.
  const pbn = deal ? printPbn(deal) : "";
  useEffect(() => {
    if (!deal) return;
    const me = run.current;
    pool.clear();
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

  const newSeed = () => setState({ ...state, pbn: undefined, seed: 1 + Math.floor(Math.random() * 1000000) });
  const goSeed = (e: Event) => {
    e.preventDefault();
    if (/^\d+$/.test(seedText.trim())) setState({ ...state, pbn: undefined, seed: +seedText.trim() });
  };
  const goPaste = (e: Event) => {
    e.preventDefault();
    const d = parsePbn(paste);
    if (typeof d === "string") { setError(d); return; }
    setState({ ...state, seed: undefined, pbn: printPbn(d) });
  };

  return (
    <main>
      <header>
        <h1>Double dummy</h1>
        <p class="sub">A bridge solver written in Bend, running in your browser.</p>
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
          <label>Dealer <select value={SEATS[state.dealer]} onChange={(e) => setState({ ...state, dealer: SEATS.indexOf((e.target as HTMLSelectElement).value) })}>
            {SEATS.map((s) => <option>{s}</option>)}
          </select></label>
          <label>Vulnerable <select value={state.vul} onChange={(e) => setState({ ...state, vul: (e.target as HTMLSelectElement).value as Vul })}>
            {["None", "NS", "EW", "All"].map((v) => <option>{v}</option>)}
          </select></label>
        </div>
      </section>

      {error && <p class="error" role="alert">{error}</p>}

      {deal && (
        <section class="board">
          <Diagram deal={deal} dealer={state.dealer} vul={state.vul} />
          <div class="analysis">
            <h2>Double dummy tricks</h2>
            <TableView table={table} times={times} />
            <p class="par">
              {parResult ? <>Par: <strong>{parResult.text}</strong></> : <span class="wait">Solving…</span>}
            </p>
            <p class="meta">
              {total != null ? `Solved in ${(total / 1000).toFixed(2)} s with ${pool.size} workers.` : `${pool.size} workers, one strain each.`}
              {state.seed !== undefined && !state.pbn && <> Same deal as <code>dd --random {state.seed}</code>.</>}
            </p>
            <p class="pbn-out"><code>{pbn}</code></p>
          </div>
        </section>
      )}
    </main>
  );
}

render(<App />, document.getElementById("app")!);
