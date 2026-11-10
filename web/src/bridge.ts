// Deals, the table and par, for the page. Seats are 0 N, 1 E, 2 S, 3 W. Strains are
// numbered as the solver numbers them: 0 spades, 1 hearts, 2 diamonds, 3 clubs, 4 NT.

export const SEATS = ["N", "E", "S", "W"];
export const SEAT_NAMES = ["North", "East", "South", "West"];
export const SUITS = ["♠", "♥", "♦", "♣"];
export const SUIT_NAMES = ["spades", "hearts", "diamonds", "clubs"];
export const STRAINS = ["♠", "♥", "♦", "♣", "NT"];
const RANKS = "AKQJT98765432";

// A hand is four strings of ranks, spades first, highest first.
export type Hand = [string, string, string, string];
export type Deal = [Hand, Hand, Hand, Hand]; // by seat, North first

// Reads "N:AT5.KJ53.96.KQ43 8763.Q6.JT753.75 ..." with the hands in seat order from
// the first seat named. Returns an error message for anything else.
export function parsePbn(text: string): Deal | string {
  const s = text.trim().replace(/^\[Deal\s+"(.*)"\]$/i, "$1").trim();
  const m = s.match(/^([NESW]):\s*(.*)$/i);
  if (!m) return "A deal starts with the first seat and a colon, as in N:AKQ.…";
  const first = SEATS.indexOf(m[1].toUpperCase());
  const hands = m[2].trim().split(/\s+/);
  if (hands.length !== 4) return "A deal has four hands, separated by spaces.";
  const deal: Hand[] = [];
  const seen = new Set<string>();
  for (let i = 0; i < 4; i++) {
    const suits = hands[i].toUpperCase().replace(/10/g, "T").split(".");
    if (suits.length !== 4) return `Hand ${i + 1} needs four suits separated by dots.`;
    const hand: string[] = [];
    for (let s = 0; s < 4; s++) {
      const ranks = [...suits[s]];
      for (const r of ranks) {
        if (!RANKS.includes(r)) return `"${r}" is not a rank.`;
        const card = SUITS[s] + r;
        if (seen.has(card)) return `${card} is in two hands.`;
        seen.add(card);
      }
      hand.push(ranks.sort((a, b) => RANKS.indexOf(a) - RANKS.indexOf(b)).join(""));
    }
    deal[(first + i) % 4] = hand as Hand;
  }
  const n = deal.map((h) => h.join("").length);
  if (n.some((x) => x !== n[0])) return "The hands must have the same number of cards.";
  if (n[0] === 0) return "The hands are empty.";
  return deal as Deal;
}

export function printPbn(deal: Deal): string {
  return "N:" + deal.map((h) => h.join(".")).join(" ");
}

export function hcp(h: Hand): number {
  const v: Record<string, number> = { A: 4, K: 3, Q: 2, J: 1 };
  return h.join("").split("").reduce((t, r) => t + (v[r] || 0), 0);
}

// ---------------------------------------------------------------------------
// The table: tricks[strain][seat], the tricks that seat takes as declarer.

export type Table = (number[] | null)[];

// ---------------------------------------------------------------------------
// Scores

export type Vul = "None" | "NS" | "EW" | "All";

export function vulnerable(vul: Vul, seat: number): boolean {
  return vul === "All" || (vul === "NS" && seat % 2 === 0) || (vul === "EW" && seat % 2 === 1);
}

// The score for declarer's side of a contract at this level and strain with this
// many tricks, doubled when it goes down (as par assumes) and not when it makes.
export function score(level: number, strain: number, tricks: number, vul: boolean): number {
  const need = level + 6;
  if (tricks < need) {
    const down = need - tricks;
    if (vul) return -(200 + 300 * (down - 1));
    return -[100, 300, 500][Math.min(down, 3) - 1] - 300 * Math.max(0, down - 3);
  }
  const per = strain === 4 ? 30 : strain <= 1 ? 30 : 20;
  const first = strain === 4 ? 40 : per;
  const points = first + per * (level - 1);
  let s = points + per * (tricks - need);
  s += points >= 100 ? (vul ? 500 : 300) : 50;
  if (level === 6) s += vul ? 750 : 500;
  if (level === 7) s += vul ? 1500 : 1000;
  return s;
}

// ---------------------------------------------------------------------------
// Par: the result when both sides bid perfectly, knowing the table. Contracts that
// make are played undoubled and those that go down doubled. Found by working back
// through the auction: for each bid and the side that made it, the other side
// either passes or bids higher, whichever is better for it.

export type Par = { score: number; contract: string; text: string };

// A bid is 0 for 1♣ up to 34 for 7NT, in the order of the auction.
const AUCTION_STRAINS = [3, 2, 1, 0, 4]; // clubs, diamonds, hearts, spades, NT
function bidLevel(b: number) { return Math.floor(b / 5) + 1; }
function bidStrain(b: number) { return AUCTION_STRAINS[b % 5]; }

export function par(t: number[][], vul: Vul, dealer: number): Par {
  // best[side][strain]: the most tricks either player of the side takes.
  const best = [0, 1].map((side) => [0, 1, 2, 3, 4].map((s) => Math.max(t[s][side], t[s][side + 2])));
  // NS's score when side plays bid b.
  const final = (b: number, side: number) => {
    const sc = score(bidLevel(b), bidStrain(b), best[side][bidStrain(b)], vulnerable(vul, side));
    return side === 0 ? sc : -sc;
  };
  // v[b][side]: NS's score when side has just bid b and the other side is to act.
  // choice[b][side]: what the other side does: -1 to pass, or its bid.
  const v: number[][] = [];
  const choice: number[][] = [];
  for (let b = 34; b >= 0; b--) {
    v[b] = [0, 0];
    choice[b] = [-1, -1];
    for (const side of [0, 1]) {
      const other = 1 - side;
      let val = final(b, side);
      let pick = -1;
      for (let c = b + 1; c < 35; c++) {
        const x = v[c][other];
        if (other === 0 ? x > val : x < val) { val = x; pick = c; }
      }
      v[b][side] = val;
      choice[b][side] = pick;
    }
  }
  // At the start the dealer's side acts first, then the other side; passing out is 0.
  const start = (side: number, passed: boolean): [number, number, number] => {
    // [score, bid, side that bid], bid -1 for passed out
    let val = passed ? 0 : start(1 - side, true)[0];
    let pick: [number, number, number] = passed ? [0, -1, -1] : start(1 - side, true);
    for (let b = 0; b < 35; b++) {
      const x = v[b][side];
      if (side === 0 ? x > val : x < val) { val = x; pick = [x, b, side]; }
    }
    return pick;
  };
  let [sc, b, side] = start(dealer % 2, false);
  if (b < 0) return { score: 0, contract: "Pass", text: "Passed out" };
  // Follow the auction to its last bid.
  for (;;) {
    const c = choice[b][side];
    if (c < 0) break;
    b = c;
    side = 1 - side;
  }
  const level = bidLevel(b);
  const strain = bidStrain(b);
  const tricks = best[side][strain];
  const who = [side, side + 2].filter((s) => t[strain][s] === tricks).map((s) => SEATS[s]).join("");
  const made = tricks - level - 6;
  const result = made === 0 ? "=" : made > 0 ? "+" + made : String(made);
  const contract = `${level}${STRAINS[strain]}${made < 0 ? "x" : ""} ${who}${result}`;
  const scoreText = sc === 0 ? "0" : sc > 0 ? `NS +${sc}` : `EW +${-sc}`;
  return { score: sc, contract, text: `${contract}, ${scoreText}` };
}
