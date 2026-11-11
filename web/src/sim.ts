// The simulator's side of the page: sim's options from the page's state, a result
// added up from chunks, and sim's own formatting.

import { Deal, SEATS } from "./bridge";

export type View = "leader" | "declarer";

// The seats a player can see: the opening leader sees their own hand, and dummy once
// the lead is made; declarer sees their hand and dummy.
export function visible(view: View, declarer: number, played: number): number[] {
  const dummy = (declarer + 2) % 4;
  if (view === "declarer") return [declarer, dummy];
  return played > 0 ? [(declarer + 1) % 4, dummy] : [(declarer + 1) % 4];
}

export function setupText(deal: Deal, seen: number[], contract: string, declarer: number, plays: string[], rules: string[]): string {
  const hands = deal.map((h, s) => (seen.includes(s) ? h.join(".") : "-")).join(" ");
  return [`deal=N:${hands}`, `contract=${contract}`, `by=${SEATS[declarer]}`, `play=${plays.join(" ")}`, ...rules].join("\n");
}

// One chunk's answer, or the sum of several (api.sim).
export type SimOut = {
  deals: number; tries: number; nodes: number; goal: number; declns: boolean; mover: number;
  cards: [number, string, string][]; sums: number[]; makes: number[];
};

export function merge(a: SimOut | null, b: SimOut): SimOut {
  if (!a) return { ...b, sums: b.sums.slice(), makes: b.makes.slice() };
  return {
    ...a,
    deals: a.deals + b.deals, tries: a.tries + b.tries, nodes: a.nodes + b.nodes,
    sums: a.sums.map((x, i) => x + b.sums[i]), makes: a.makes.map((x, i) => x + b.makes[i]),
  };
}

// x / d to two places and as a percentage to one, rounding as sim does.
export function ratio(x: number, d: number): string {
  const v = Math.floor((x * 100 + Math.floor(d / 2)) / Math.max(d, 1));
  return `${Math.floor(v / 100)}.${String(v % 100).padStart(2, "0")}`;
}
export function percent(x: number, d: number): string {
  const v = Math.floor((x * 1000 + Math.floor(d / 2)) / Math.max(d, 1));
  return `${Math.floor(v / 10)}.${v % 10}%`;
}

export type Row = { key: string; card: number; run: string; sum: number; makes: number };

// The rows best first for the side to play, as sim sorts them: for declarer's side the
// most makes and then the most tricks, for the defenders the fewest.
export function rows(o: SimOut): Row[] {
  const rs = o.cards.map(([card, name, run], i) => ({ key: name.slice(0, -1) + run, card, run, sum: o.sums[i], makes: o.makes[i] }));
  const mine = o.declns === (o.mover % 2 === 0);
  return rs.sort((a, b) => (mine ? b.makes - a.makes || b.sum - a.sum : a.makes - b.makes || a.sum - b.sum));
}

// The chunks for n layouts: about two for each worker, so that one unlucky chunk
// doesn't hold the rest up for long, and at most 40 layouts each, so the bars move.
// Each chunk sets up a transposition table of its own, about 0.3 s, so not smaller.
export function chunks(n: number, workers: number): [number, number][] {
  const size = Math.max(1, Math.min(40, Math.ceil(n / (workers * 2))));
  const out: [number, number][] = [];
  for (let first = 0; first < n; first += size) out.push([first, Math.min(size, n - first)]);
  return out;
}
