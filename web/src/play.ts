// The play of a deal: the cards left, the trick in progress, the tricks won and the
// legal cards, worked out from the deal, the contract and the cards played so far.
// Cards are written suit first, as sim reads them: SK, H2, DT.

import { Deal } from "./bridge";

export const RANKS = "AKQJT98765432";
const SUIT_LETTERS = "SHDC";

export type Card = { s: number; r: string };

export function cardText(c: Card): string {
  return SUIT_LETTERS[c.s] + c.r;
}

export function parseCard(t: string): Card | null {
  const m = t.toUpperCase().match(/^([SHDC])([AKQJT2-9])$/);
  return m ? { s: SUIT_LETTERS.indexOf(m[1]), r: m[2] } : null;
}

// The solver's number for a card: suit * 16 + rank, the deuce 0 and the ace 12.
export function cardNum(c: Card): number {
  return c.s * 16 + (12 - RANKS.indexOf(c.r));
}

const higher = (a: string, b: string) => RANKS.indexOf(a) < RANKS.indexOf(b);

export type Trick = { leader: number; cards: { seat: number; card: Card }[]; winner: number };

export type Play = {
  hands: Deal; // the cards still held
  tricks: Trick[]; // finished
  current: { seat: number; card: Card }[]; // the trick in progress
  mover: number; // the seat to play
  declarer: number;
  won: [number, number]; // tricks for declarer's side and the defenders
  total: number; // cards in each hand at the start
  over: boolean;
  error?: string;
};

function winner(cards: { seat: number; card: Card }[], strain: number): number {
  let best = cards[0];
  for (const x of cards.slice(1)) {
    const trumps = strain < 4 && x.card.s === strain;
    if (trumps && best.card.s !== strain) best = x;
    else if (x.card.s === best.card.s && higher(x.card.r, best.card.r)) best = x;
  }
  return best.seat;
}

export function legal(p: Play): Card[] {
  if (p.over) return [];
  const hand = p.hands[p.mover];
  const lead = p.current[0]?.card.s;
  const follow = lead !== undefined && hand[lead].length > 0;
  const out: Card[] = [];
  hand.forEach((ranks, s) => {
    if (follow && s !== lead) return;
    for (const r of ranks) out.push({ s, r });
  });
  return out;
}

export function replay(deal: Deal, strain: number, declarer: number, plays: string[]): Play {
  const hands = deal.map((h) => h.slice()) as Deal;
  const total = deal[0].join("").length;
  const p: Play = { hands, tricks: [], current: [], mover: (declarer + 1) % 4, declarer, won: [0, 0], total, over: false };
  for (const t of plays) {
    const c = parseCard(t);
    if (!c) return { ...p, error: `can't read the card ${t}` };
    if (!legal(p).some((x) => x.s === c.s && x.r === c.r)) return { ...p, error: `${t} can't be played now` };
    hands[p.mover][c.s] = hands[p.mover][c.s].replace(c.r, "");
    p.current.push({ seat: p.mover, card: c });
    if (p.current.length === 4) {
      const w = winner(p.current, strain);
      p.tricks.push({ leader: p.current[0].seat, cards: p.current, winner: w });
      p.current = [];
      p.won[(w + 4 - declarer) % 2 === 0 ? 0 : 1]++;
      p.mover = w;
    } else {
      p.mover = (p.mover + 1) % 4;
    }
    p.over = p.tricks.length === total;
  }
  return p;
}

// The solver's answer for a position (api.cards): the cards to try, each with the
// run of cards that play the same, and North-South's tricks with each.
export type Cands = { cards: [number, string, string][]; ns: number[] };

export type Option = { card: Card; group: number; tricks: number; cost: number; best: boolean };

// Each legal card with declarer's tricks, its group of equal cards, and what it costs
// the side to move against the best card.
export function options(p: Play, cands: Cands): Option[] {
  const mine = (p.mover + 4 - p.declarer) % 2 === 0;
  const decl = (ns: number) => (p.declarer % 2 === 0 ? ns : p.total - ns);
  const vals = cands.ns.map(decl);
  const best = mine ? Math.max(...vals) : Math.min(...vals);
  return legal(p).map((card) => {
    const g = cands.cards.findIndex(([c, , run]) => c >> 4 === card.s && run.includes(card.r));
    const tricks = vals[g];
    return { card, group: g, tricks, cost: Math.abs(tricks - best), best: tricks === best };
  });
}
