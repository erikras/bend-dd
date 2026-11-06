# search.bend: the zero-window search and the target driver.
#
# search answers one question, "can North-South finish with at least target
# tricks?", in the style of DDS (docs/PLAN.md, 2.1 and 4). A driver asks it again
# and again, moving a lower and an upper bound until they meet.
#
# Against plain minimax this adds:
#   - stopping at the first move that settles a node;
#   - target too low or too high: at the start of a trick, the tricks won and
#     the tricks left may already decide the answer;
#   - card equivalence: of the cards in one hand that are adjacent among the cards
#     in play, only the top one is tried;
#   - move ordering: cards that win the trick first, and high cards on lead.

import Base
import ./cards.bend as C
import ./rules.bend as R
import ./brute.bend as B

# A true or false answer with the positions visited so far. Nat counts them: it
# is a machine word at run time, and it stops the program at 2^48 instead of
# wrapping, which takes days at this solver's rates.
type Res is Data:
  Res{ok: Bool, nodes: Nat}

# ---------------------------------------------------------------------------
# Card equivalence

# Walks the cards of m from the lowest up, keeping a card when the next card in
# play above it is not in m. rest is what is left to look at, and n bounds the
# loop: a holding has at most 13 cards.
def tops.go(n: Nat, z: Bool, +m: U32, +live: U32, +rest: U32, +acc: U32) -> U32:
  match n z:
    case 0n _:
      acc
    case 1n+p True{}:
      acc
    case 1n+p False{}:
      +b = (rest .&. (0 - rest) : U32)
      +more = (rest .^. b : U32)
      +above = (live .&. (0 - (b << 1n)) : U32)
      +next = (above .&. (0 - above) : U32)
      tops.go(p, U32.is_zero(more), m, live, more, R.sel(U32.is_zero((next .&. m : U32)), (acc .|. b : U32), acc))

# The cards of holding m worth trying, where live is every card in play in that
# suit at the start of the trick, m included. Cards with no other card in play
# between them win and lose to exactly the same cards, so only the top one of
# each run counts. A card already on the table in this trick is in live, since
# it still splits a run: with Q on the table, K and J are different.
def tops(+m: U32, +live: U32) -> U32:
  tops.go(13n, U32.is_zero(m), m, live, m, 0)

# ---------------------------------------------------------------------------
# Move ordering

# The cards of k that win straight away. On lead, that is the top card in play.
# Later in the trick, it is a higher card of the suit of the card winning so far,
# or any trump over a card that is not one. Agrees with R.beats, see LAWS.bend.
def wins.later(same: Bool, +trump: Bool, +k: U32, +best: U32) -> U32:
  match same:
    case True{}:
      (k .&. (0 - (C.card.bit(best) << 1n)) : U32)
    case False{}:
      R.sel(trump, k, 0)

def wins(first: Bool, +s: U32, +k: U32, +live: U32, +t: U32, +best: U32) -> U32:
  match first:
    case True{}:
      (k .&. (1 << U32.log2(live)) : U32)
    case False{}:
      wins.later(U32.is_eq(s, C.card.suit(best)), U32.is_eq(s, t), k, best)

# Pushes the cards of a holding onto acc, highest first, as R.moves.suit does, or
# lowest first.
def push.low(n: Nat, z: Bool, +suit: U32, +m: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n z:
    case 0n _:
      acc
    case 1n+p True{}:
      acc
    case 1n+p False{}:
      +r = U32.log2(m)
      +rest = (m .^. (1 << r) : U32)
      push.low(p, U32.is_zero(rest), suit, rest, C.card.make(suit, U32.from_nat(r)) <> acc)

def push(high: Bool, +suit: U32, +m: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match high:
    case True{}:
      R.moves.suit(suit, m, acc)
    case False{}:
      push.low(13n, U32.is_zero(m), suit, m, acc)

def push.all(+high: Bool, +a: U32, +b: U32, +c: U32, +d: U32, acc: List<&2, U32>) -> List<&2, U32>:
  push(high, 0, a, push(high, 1, b, push(high, 2, c, push(high, 3, d, acc))))

# The moves to try from the holdings k, of which w win straight away. On lead:
# winners, then the rest, high cards first in each suit. When partner is winning the trick,
# the cheapest cards first and any that overtake last. Otherwise the cheapest
# winner first, then the cheapest of the rest.
def order(+first: Bool, +mine: Bool, +k0: U32, +k1: U32, +k2: U32, +k3: U32, +w0: U32, +w1: U32, +w2: U32, +w3: U32) -> List<&2, U32>:
  +front = Bool.or(first, Bool.not(mine))
  +a0 = R.sel(front, w0, (k0 .^. w0 : U32))
  +a1 = R.sel(front, w1, (k1 .^. w1 : U32))
  +a2 = R.sel(front, w2, (k2 .^. w2 : U32))
  +a3 = R.sel(front, w3, (k3 .^. w3 : U32))
  push.all(first, a0, a1, a2, a3,
    push.all(first, (k0 .^. a0 : U32), (k1 .^. a1 : U32), (k2 .^. a2 : U32), (k3 .^. a3 : U32), Nil{}))

# ---------------------------------------------------------------------------
# Move generation

# The holding of suit s that may be played: all of it when free to play anything,
# otherwise only the suit led.
def legal(+free: Bool, +s: U32, +lead: U32, +m: U32) -> U32:
  R.sel(free || U32.is_eq(s, lead), m, 0)

def gen.go(+t: U32, +l01: U32, +l23: U32, +h01: U32, +h23: U32, +tr: U32) -> List<&2, U32>:
  +lead = R.trick.lead(tr)
  +seat = R.trick.seat(tr)
  +best = R.trick.best(tr)
  +played = R.trick.played(tr)
  +first = U32.is_zero(played)
  +mine = U32.is_zero(((seat .^. R.trick.owner(tr)) .&. 1 : U32))
  +free = U32.is_zero(R.suit.mask(U32.to_nat(lead), h01, h23))
  +l0 = (l01 >> 16n : U32)
  +l1 = (l01 .&. 65535 : U32)
  +l2 = (l23 >> 16n : U32)
  +l3 = (l23 .&. 65535 : U32)
  +k0 = tops(legal(free, 0, lead, (h01 >> 16n : U32)), l0)
  +k1 = tops(legal(free, 1, lead, (h01 .&. 65535 : U32)), l1)
  +k2 = tops(legal(free, 2, lead, (h23 >> 16n : U32)), l2)
  +k3 = tops(legal(free, 3, lead, (h23 .&. 65535 : U32)), l3)
  order(first, mine, k0, k1, k2, k3,
    wins(first, 0, k0, l0, t, best), wins(first, 1, k1, l1, t, best),
    wins(first, 2, k2, l2, t, best), wins(first, 3, k3, l3, t, best))

# The moves to try in a position, where l01 and l23 are the cards in play at the
# start of this trick. The trick word starts with no cards played.
def gen(+t: U32, pos: R.Pos, +l01: U32, +l23: U32) -> List<&2, U32>:
  match pos:
    case R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, +tr, won}:
      +seat = U32.to_nat(R.trick.seat(tr))
      gen.go(t, l01, l23, R.pick(seat, n01, e01, s01, w01), R.pick(seat, n23, e23, s23, w23), tr)

# ---------------------------------------------------------------------------
# Target cutoffs

# What the tricks alone say about reaching target: 0 nothing, 1 North-South have
# it already, 2 they cannot get there even if they win every trick left.
def cut(+won: U32, +left: U32, +target: U32) -> U32:
  R.sel(U32.is_ge(won, target), 1, R.sel(U32.is_lt((won + left : U32), target), 2, 0))

# ---------------------------------------------------------------------------
# Quick tricks

# How many top cards in play are in m, where all is every card in play in the suit.
def run(+m: U32, +all: U32) -> U32:
  +rest = (all .^. m : U32)
  R.sel(U32.is_zero(rest), C.bits.count(m), C.bits.count((m >> 1n+U32.log2(rest) : U32)))

# How many of k winners in a side suit are safe from a ruff: an opponent who still
# has a trump must follow as long as he has cards of the suit. He never gets to
# discard from it either, since he follows on every round of every safe suit.
def safe(+k: U32, +ha: Bool, +la: U32, +hb: Bool, +lb: U32) -> U32:
  U32.min(k, U32.min(R.sel(ha, la, 13), R.sel(hb, lb, 13)))

# One suit's part of the count: the leader's safe winners in the low byte, partner's
# next, and whether the suit is an entry to partner above that. ha1 and hb1 say an
# opponent has a trump left after the leader's top trumps, ha2 and hb2 after
# partner's as well.
def quick.suit(trump: Bool, +m: U32, +p: U32, +a: U32, +b: U32, +ha1: Bool, +hb1: Bool, +ha2: Bool, +hb2: Bool) -> U32:
  match trump:
    case True{}:
      0
    case False{}:
      +all = (m .|. p .|. a .|. b : U32)
      +la = C.bits.count(a)
      +lb = C.bits.count(b)
      +kp = run(p, all)
      +enter = U32.is_ne(m, 0) && U32.is_ne(safe(kp, ha1, la, hb1, lb), 0)
      (safe(run(m, all), ha1, la, hb1, lb) .|. (safe(kp, ha2, la, hb2, lb) << 8n) .|. (Bool.to_u32(enter) << 16n) : U32)

# The tricks the side on lead is sure of, from the start of a trick with left
# tricks to go. The leader cashes top trumps, which also draws trumps, then safe
# winners elsewhere, and then crosses on a card kept for it to partner, who does the
# same. Partner keeps his winners on the way unless he runs out of other cards,
# which is why the total is capped at left. On a card of a suit an opponent can ruff
# there is no entry. With no trumps against them, the side also gets a trick for
# every trump of its longer trump hand.
#
# Each mN, pN, aN and bN is the holding of suit N: leader, partner, left and right.
def quick(+s: Nat, +left: U32, +m0: U32, +m1: U32, +m2: U32, +m3: U32, +p0: U32, +p1: U32, +p2: U32, +p3: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +b0: U32, +b1: U32, +b2: U32, +b3: U32) -> U32:
  +mt = R.pick5(s, m0, m1, m2, m3)
  +pt = R.pick5(s, p0, p1, p2, p3)
  +at = R.pick5(s, a0, a1, a2, a3)
  +bt = R.pick5(s, b0, b1, b2, b3)
  +allt = (mt .|. pt .|. at .|. bt : U32)
  +tl = run(mt, allt)
  +tp = run(pt, allt)
  +la = C.bits.count(at)
  +lb = C.bits.count(bt)
  +ha1 = U32.is_gt(la, tl)
  +hb1 = U32.is_gt(lb, tl)
  +ha2 = U32.is_gt(la, (tl + tp : U32))
  +hb2 = U32.is_gt(lb, (tl + tp : U32))
  +sum = (quick.suit(Nat.is_eq(s, 0n), m0, p0, a0, b0, ha1, hb1, ha2, hb2) + quick.suit(Nat.is_eq(s, 1n), m1, p1, a1, b1, ha1, hb1, ha2, hb2) + quick.suit(Nat.is_eq(s, 2n), m2, p2, a2, b2, ha1, hb1, ha2, hb2) + quick.suit(Nat.is_eq(s, 3n), m3, p3, a3, b3, ha1, hb1, ha2, hb2) : U32)
  +enter = U32.is_ne((sum >> 16n : U32), 0) || (U32.is_ne(tp, 0) && U32.is_ne(mt, 0))
  +wl = (tl + (sum .&. 255) : U32)
  +wp = (tp + ((sum >> 8n) .&. 255) : U32)
  +total = U32.min(left, (wl + R.sel(enter, wp, 0) : U32))
  +clear = U32.is_zero((at .|. bt : U32))
  U32.max(total, R.sel(clear, U32.max(C.bits.count(mt), C.bits.count(pt)), 0))

# ---------------------------------------------------------------------------
# Later tricks

# One suit for later.nt: bit 0 says the leader has a card where the side does not
# hold the top, bit 1 that he has any card, and above that the most tricks the suit
# can give the side, the longer of its hands when it does hold the top.
def later.suit(+m: U32, +p: U32, +a: U32, +b: U32) -> U32:
  +side = (m .|. p : U32)
  +opps = (a .|. b : U32)
  +top = U32.is_gt(side, opps)
  +most = R.sel(top, U32.max(C.bits.count(m), C.bits.count(p)), 0)
  (Bool.to_u32(top && U32.is_ne(m, 0)) .|. (most << 2n) : U32)

# At no trumps the opponents are sure of a trick if the leader has to give up the
# lead at once, because the side holds no top card in any suit he has, or if the
# suits where the side holds the top cannot make up all the tricks left.
def later.nt(+left: U32, +s0: U32, +s1: U32, +s2: U32, +s3: U32) -> U32:
  +any = ((s0 .|. s1 .|. s2 .|. s3) .&. 1 : U32)
  +most = ((s0 >> 2n) + (s1 >> 2n) + (s2 >> 2n) + (s3 >> 2n) : U32)
  Bool.to_u32(U32.is_zero(any) || U32.is_lt(most, left))

# With trumps. If the side has no trump, every trump of the opponents' longer trump
# hand makes a trick. Otherwise, the top trump is a trick, and so is the second
# when they hold it as well, unless both are alone and can fall together. And the
# second trump with one more behind the top one is a trick, since it can wait for
# the top one to be played.
def later.trump(+m: U32, +p: U32, +a: U32, +b: U32) -> U32:
  +side = (m .|. p : U32)
  +opps = (a .|. b : U32)
  +la = C.bits.count(a)
  +lb = C.bits.count(b)
  +top = (1 << U32.log2((side .|. opps : U32)) : U32)
  +rest = ((side .|. opps) .^. top : U32)
  +next = (1 << U32.log2(rest) : U32)
  +next_opp = U32.is_ne(rest, 0) && U32.is_ne((opps .&. next : U32), 0)
  +top_opp = U32.is_ne((opps .&. top : U32), 0)
  +long = U32.is_ge(la, 2) || U32.is_ge(lb, 2)
  # The hand behind the top card: left of the leader, right of partner.
  +behind = (U32.is_ne((m .&. top : U32), 0) && U32.is_ne((a .&. next : U32), 0) && U32.is_ge(la, 2)) || (U32.is_ne((p .&. top : U32), 0) && U32.is_ne((b .&. next : U32), 0) && U32.is_ge(lb, 2))
  +held = R.sel(top_opp, R.sel(next_opp && long, 2, 1), R.sel(next_opp && behind, 1, 0))
  R.sel(U32.is_zero(side), U32.max(la, lb), held)

# ---------------------------------------------------------------------------
# Cutoffs at the start of a trick

def boundary.side(ns: Bool, +q: U32, +l: U32, +won: U32, +left: U32, +target: U32) -> U32:
  match ns:
    case True{}:
      R.sel(U32.is_ge((won + q : U32), target), 1, R.sel(U32.is_lt((won + left - l : U32), target), 2, 0))
    case False{}:
      R.sel(U32.is_lt((won + left - q : U32), target), 2, R.sel(U32.is_ge((won + l : U32), target), 1, 0))

def boundary.go(+t: U32, +seat: U32, +won: U32, +left: U32, +target: U32, +n01: U32, +n23: U32, +e01: U32, +e23: U32, +s01: U32, +s23: U32, +w01: U32, +w23: U32) -> U32:
  +i = U32.to_nat(seat)
  +j = U32.to_nat(((seat + 1) .&. 3 : U32))
  +k = U32.to_nat(((seat + 2) .&. 3 : U32))
  +o = U32.to_nat(((seat + 3) .&. 3 : U32))
  +m01 = R.pick(i, n01, e01, s01, w01)
  +m23 = R.pick(i, n23, e23, s23, w23)
  +p01 = R.pick(k, n01, e01, s01, w01)
  +p23 = R.pick(k, n23, e23, s23, w23)
  +a01 = R.pick(j, n01, e01, s01, w01)
  +a23 = R.pick(j, n23, e23, s23, w23)
  +b01 = R.pick(o, n01, e01, s01, w01)
  +b23 = R.pick(o, n23, e23, s23, w23)
  +m0 = (m01 >> 16n : U32)
  +m1 = (m01 .&. 65535 : U32)
  +m2 = (m23 >> 16n : U32)
  +m3 = (m23 .&. 65535 : U32)
  +p0 = (p01 >> 16n : U32)
  +p1 = (p01 .&. 65535 : U32)
  +p2 = (p23 >> 16n : U32)
  +p3 = (p23 .&. 65535 : U32)
  +a0 = (a01 >> 16n : U32)
  +a1 = (a01 .&. 65535 : U32)
  +a2 = (a23 >> 16n : U32)
  +a3 = (a23 .&. 65535 : U32)
  +b0 = (b01 >> 16n : U32)
  +b1 = (b01 .&. 65535 : U32)
  +b2 = (b23 >> 16n : U32)
  +b3 = (b23 .&. 65535 : U32)
  +st = U32.to_nat(t)
  +l = R.sel(U32.is_eq(t, 4),
    later.nt(left, later.suit(m0, p0, a0, b0), later.suit(m1, p1, a1, b1), later.suit(m2, p2, a2, b2), later.suit(m3, p3, a3, b3)),
    later.trump(R.pick5(st, m0, m1, m2, m3), R.pick5(st, p0, p1, p2, p3), R.pick5(st, a0, a1, a2, a3), R.pick5(st, b0, b1, b2, b3)))
  boundary.side(U32.is_zero((seat .&. 1 : U32)),
    quick(st, left, m0, m1, m2, m3, p0, p1, p2, p3, a0, a1, a2, a3, b0, b1, b2, b3), l, won, left, target)

def boundary.pos(+t: U32, pos: R.Pos, +won: U32, +left: U32, +target: U32) -> U32:
  match pos:
    case R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, +tr, _}:
      boundary.go(t, R.trick.seat(tr), won, left, target, n01, n23, e01, e23, s01, s23, w01, w23)

def boundary.more(open: Bool, +t: U32, +pos: R.Pos, +won: U32, +left: U32, +target: U32, +code: U32) -> U32:
  match open:
    case True{}:
      boundary.pos(t, pos, won, left, target)
    case False{}:
      code

# Every check at the start of a trick, the cheapest first.
def boundary(+t: U32, +pos: R.Pos, +won: U32, +left: U32, +target: U32) -> U32:
  +code = cut(won, left, target)
  boundary.more(U32.is_zero(code), t, pos, won, left, target, code)

# ---------------------------------------------------------------------------
# After the lead

# The best a hand can do in this trick: its top card of the suit led if it has one,
# otherwise its top trump, otherwise nothing.
def power(+f: U32, +x: U32) -> U32:
  R.sel(U32.is_ne(f, 0), (16 + U32.from_nat(U32.log2(f)) : U32), R.sel(U32.is_ne(x, 0), (32 + U32.from_nat(U32.log2(x)) : U32), 0))

def second.power(+l: Nat, +t: Nat, +h01: U32, +h23: U32) -> U32:
  power(R.suit.mask(l, h01, h23), R.suit.mask(t, h01, h23))

# Once a card is led, the side with the hand of highest power is sure of this trick:
# that hand plays its best and nothing beats it. So left counts this trick.
def second.go(+t: U32, +tr: U32, +won: U32, +left: U32, +target: U32, +n01: U32, +n23: U32, +e01: U32, +e23: U32, +s01: U32, +s23: U32, +w01: U32, +w23: U32) -> U32:
  +seat = R.trick.seat(tr)
  +best = R.trick.best(tr)
  +l = U32.to_nat(R.trick.lead(tr))
  +st = U32.to_nat(t)
  +i = U32.to_nat(seat)
  +j = U32.to_nat(((seat + 1) .&. 3 : U32))
  +k = U32.to_nat(((seat + 2) .&. 3 : U32))
  +mine = U32.max(second.power(l, st, R.pick(i, n01, e01, s01, w01), R.pick(i, n23, e23, s23, w23)), second.power(l, st, R.pick(k, n01, e01, s01, w01), R.pick(k, n23, e23, s23, w23)))
  +led = (16 + C.card.rank(best) : U32)
  +theirs = U32.max(led, second.power(l, st, R.pick(j, n01, e01, s01, w01), R.pick(j, n23, e23, s23, w23)))
  # The leader's side is the seat before this one, whose parity differs.
  +ns = Bool.xor(U32.is_gt(mine, theirs), U32.is_ne((seat .&. 1 : U32), 0))
  R.sel(ns, R.sel(U32.is_ge((won + 1 : U32), target), 1, 0), R.sel(U32.is_lt((won + left - 1 : U32), target), 2, 0))

def second.pos(+t: U32, pos: R.Pos, +won: U32, +left: U32, +target: U32) -> U32:
  match pos:
    case R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, +tr, _}:
      second.go(t, tr, won, left, target, n01, n23, e01, e23, s01, s23, w01, w23)

# It can only cut when one trick would settle things.
def second.more(tight: Bool, +t: U32, +pos: R.Pos, +won: U32, +left: U32, +target: U32) -> U32:
  match tight:
    case True{}:
      second.pos(t, pos, won, left, target)
    case False{}:
      0

def second(+t: U32, +pos: R.Pos, +won: U32, +left: U32, +target: U32) -> U32:
  second.more(U32.is_eq((won + 1 : U32), target) || U32.is_eq((won + left : U32), target), t, pos, won, left, target)

# The cut for a position with d cards left, by how many are on the table.
def cut.at(played: Nat, +t: U32, +pos: R.Pos, +won: U32, +d: U32, +target: U32) -> U32:
  match played:
    case 0n:
      boundary(t, pos, won, (d >> 2n : U32), target)
    case 1n:
      second(t, pos, won, ((d + 3) >> 2n : U32), target)
    case _:
      0

# The moves to try after a cut: none when it settled the position.
def enter.go(go: Bool, +t: U32, +pos: R.Pos, +l01: U32, +l23: U32) -> List<&2, U32>:
  match go:
    case True{}:
      gen(t, pos, l01, l23)
    case False{}:
      Nil{}

# The answer a node starts from. With no cut, it is the one that does not settle
# the node yet: false when North-South choose, true when East-West choose.
def enter.ok(+code: U32, +ns: Bool) -> Bool:
  (U32.is_zero(code) && Bool.not(ns)) || U32.is_eq(code, 1)

def live.at(bound: Bool, +x: U32, +old: U32) -> U32:
  match bound:
    case True{}:
      x
    case False{}:
      old

# ---------------------------------------------------------------------------
# The search

# Tries the moves ms of a position with d cards left. r is the answer so far: a
# call cannot be destructured in place, so a child's answer rides into the next
# sibling as an argument. The answer settles a node once it says true for
# North-South or false for East-West, and otherwise the node goes on to the next
# move; with no moves left, the answer stands.
#
# A child has one card fewer, and a sibling has one move fewer with the same d.
def search(+d: Nat, ms: List<&2, U32>, ns: Bool, r: Res, +t: U32, +target: U32, +l01: U32, +l23: U32, +pos: R.Pos) -> Res:
  match d ms ns r:
    case 0n _ _ x:
      x
    case 1n+p Nil{} _ x:
      x
    case 1n+p _ True{} Res{True{}, n}:
      Res{True{}, n}
    case 1n+p _ False{} Res{False{}, n}:
      Res{False{}, n}
    case 1n+p Con{c, rest} True{} Res{False{}, n}:
      +child = R.play(t, pos, c)
      +cns = R.pos.ns(child)
      +tr = R.pos.trick(child)
      +bound = U32.is_zero(R.trick.played(tr))
      +code = cut.at(U32.to_nat(R.trick.played(tr)), t, child, R.pos.won(child), U32.from_nat(p), target)
      +c01 = live.at(bound, R.pos.live01(child), l01)
      +c23 = live.at(bound, R.pos.live23(child), l23)
      search(1n+p, rest, True{},
        search(p, enter.go(U32.is_zero(code), t, child, c01, c23), cns, Res{enter.ok(code, cns), 1n+n}, t, target, c01, c23, child),
        t, target, l01, l23, pos)
    case 1n+p Con{c, rest} False{} Res{True{}, n}:
      +child = R.play(t, pos, c)
      +cns = R.pos.ns(child)
      +tr = R.pos.trick(child)
      +bound = U32.is_zero(R.trick.played(tr))
      +code = cut.at(U32.to_nat(R.trick.played(tr)), t, child, R.pos.won(child), U32.from_nat(p), target)
      +c01 = live.at(bound, R.pos.live01(child), l01)
      +c23 = live.at(bound, R.pos.live23(child), l23)
      search(1n+p, rest, False{},
        search(p, enter.go(U32.is_zero(code), t, child, c01, c23), cns, Res{enter.ok(code, cns), 1n+n}, t, target, c01, c23, child),
        t, target, l01, l23, pos)

# Runs one search from the start of a trick, unless told there is nothing to ask.
def ask(stop: Bool, +d: Nat, +t: U32, +pos: R.Pos, +target: U32, n: Nat) -> Res:
  match stop:
    case True{}:
      Res{False{}, n}
    case False{}:
      +ns = R.pos.ns(pos)
      +l01 = R.pos.live01(pos)
      +l23 = R.pos.live23(pos)
      search(d, gen(t, pos, l01, l23), ns, Res{Bool.not(ns), n}, t, target, l01, l23, pos)

# ---------------------------------------------------------------------------
# The driver

# The bounds after asking about target: true raises the lower bound to it, and
# false lowers the upper bound to just below it.
def driver.lo(+ok: Bool, +target: U32, +lo: U32) -> U32:
  R.sel(ok, target, lo)

def driver.hi(+ok: Bool, +target: U32, +hi: U32) -> U32:
  R.sel(ok, hi, (target - 1 : U32))

# What to ask next: one step on from where the last answer left the bounds, since
# a value tends to be close to the guess it was found from.
def driver.next(+ok: Bool, +lo: U32, +hi: U32) -> U32:
  R.sel(ok, (lo + 1 : U32), hi)

# What to ask first: the guess, moved into the range where the answer is unknown.
def driver.first(+g: U32, +lo: U32, +hi: U32) -> U32:
  U32.max((lo + 1 : U32), U32.min(g, hi))

# Moves the bounds until they meet. done says they already had before this step,
# and r is the answer about target. Each step closes the gap by at least one, so
# the fuel only has to be more than the tricks left.
def narrow(fuel: Nat, done: Bool, r: Res, +target: U32, +d: Nat, +t: U32, +pos: R.Pos, +lo: U32, +hi: U32) -> B.Res:
  match fuel done r:
    case 0n _ Res{_, n}:
      B.Res{lo, n}
    case 1n+p True{} Res{_, n}:
      B.Res{lo, n}
    case 1n+p False{} Res{+ok, n}:
      +lo2 = driver.lo(ok, target, lo)
      +hi2 = driver.hi(ok, target, hi)
      +stop = U32.is_ge(lo2, hi2)
      +next = driver.next(ok, lo2, hi2)
      narrow(p, stop, ask(stop, d, t, pos, next, n), next, d, t, pos, lo2, hi2)

# North-South's tricks from the start of a trick with d cards left, starting from
# a guess at the answer.
def solve(+d: Nat, +t: U32, +pos: R.Pos, +guess: U32, n: Nat) -> B.Res:
  +lo = R.pos.won(pos)
  +hi = (lo + (U32.from_nat(d) >> 2n) : U32)
  +stop = U32.is_ge(lo, hi)
  +target = driver.first(guess, lo, hi)
  narrow(14n, stop, ask(stop, d, t, pos, target, n), target, d, t, pos, lo, hi)

# ---------------------------------------------------------------------------
# The table

# Fills the table from its last entry to its first, so that it comes out in the
# order of B.table. r is the result for entry i + 1, and it feeds the guess for
# entry i: moving the lead by one seat rarely changes the result by much.
def table.go(k: Nat, r: B.Res, +i: U32, +d: Nat, +left: U32, +deal: C.Deal, acc: List<&2, U32>) -> B.Table:
  match k r:
    case 0n B.Res{+v, n}:
      B.Table{B.table.entry(U32.is_zero(((i + 1) .&. 1 : U32)), left, v) <> acc, n}
    case 1n+p B.Res{+v, n}:
      +t = (i >> 2n : U32)
      +decl = (i .&. 3 : U32)
      +leader = ((decl + 1) .&. 3 : U32)
      table.go(p, solve(d, t, R.pos.start(deal, leader), v, n), (i - 1 : U32), d, left, deal,
        B.table.entry(U32.is_zero(((i + 1) .&. 1 : U32)), left, v) <> acc)

# The double dummy table of a deal, as B.table gives it.
def table(+deal: C.Deal) -> B.Table:
  +cards = B.deal.cards(deal)
  +d = U32.to_nat(cards)
  +left = (cards / 4 : U32)
  table.go(19n, solve(d, 4, R.pos.start(deal, 0), ((left + 1) / 2 : U32), 0n), 18, d, left, deal, Nil{})
