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
#   - quick tricks and later tricks: at the start of a trick, tricks either side is
#     already sure of may settle it, and so may the trick in progress after the lead;
#   - DDS's move weights for each place in the trick, and a memory of best moves.

import Base
import ./cards.bend as C
import ./rules.bend as R
import ./brute.bend as B

# A true or false answer with the positions visited so far, and the memory of best
# moves. Nat counts the positions: it is a machine word at run time, and it stops
# the program at 2^48 instead of wrapping, which takes days at this solver's rates.
#
# The memory holds, for each number of cards left, the card that last settled a node
# with that many left. It has one owner, so it is updated in place as it is handed
# along, including through every search for a deal. A call cannot be destructured
# in place, so reading it inside the search has to happen in a helper: each Res comes
# with memo, what the memory holds for the next child of the node it goes to.
type Res is Type:
  Res{ok: Bool, nodes: Nat, mem: Array<U32>, memo: U32}

# A driver's result, with the same counters.
type Val is Type:
  Val{value: U32, nodes: Nat, mem: Array<U32>}

# The memory slot written when there is nothing to remember, and what memory starts
# with: a card code that is never in a holding.
def mem.none() -> U32:
  63

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
# Power in a trick

# The best a hand can do in this trick: its top card of the suit led if it has one,
# otherwise its top trump, otherwise nothing.
def power(+f: U32, +x: U32) -> U32:
  R.sel(U32.is_ne(f, 0), (16 + U32.from_nat(U32.log2(f)) : U32), R.sel(U32.is_ne(x, 0), (32 + U32.from_nat(U32.log2(x)) : U32), 0))

def second.power(+l: Nat, +t: Nat, +h01: U32, +h23: U32) -> U32:
  power(R.suit.mask(l, h01, h23), R.suit.mask(t, h01, h23))

# ---------------------------------------------------------------------------
# DDS's move weights
#
# These follow chapter 5 of DDS's algorithm notes, with one set for each place in the
# trick. A weight can go negative there, so here they all start from 512. A move's
# key is its weight above its card code, and lists of keys run from the biggest down.

def key(+w: U32, +c: U32) -> U32:
  ((w << 6n) .|. c : U32)

def key.insert(xs: List<&2, U32>, +k: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      [k]
    case Con{+h, t}:
      U32.max(k, h) <> key.insert(t, U32.min(k, h))

# Adds a suit's keys to acc, where the top key of each suit gets ahead of every other
# card, which makes for a good mix of suits at the front of the list.
def key.merge(xs: List<&2, U32>, +bonus: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{+h, t}:
      key.merge(t, 0, key.insert(acc, (h + bonus : U32)))

def keys.cards(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      (h .&. 63 : U32) <> keys.cards(t)

def bit.top(+x: U32) -> U32:
  (1 << U32.log2(x) : U32)

def bit.low(+x: U32) -> U32:
  (x .&. (0 - x) : U32)

# Whether the card just below b in play is also in m.
def equivalent(+b: U32, +m: U32, +all: U32) -> Bool:
  +below = (all .&. (b - 1) : U32)
  U32.is_ne(below, 0) && U32.is_ne((m .&. bit.top(below) : U32), 0)

def rank.of(+b: U32) -> U32:
  (U32.from_nat(U32.ctz(b)) + 2 : U32)

# What a weight needs to know about the suit and the trick. x0 to x3 depend on the
# place in the trick.
type Ctx is Data:
  Ctx{s: U32, t: U32, l: U32, me: U32, all: U32, add: U32, mine: U32, theirs: U32, x0: U32, x1: U32, x2: U32, x3: U32}

def ctx.s(c: Ctx) -> U32:
  match c:
    case Ctx{s, _, _, _, _, _, _, _, _, _, _, _}:
      s

# Keys for the cards rest of a holding, walking from the lowest up.
def walk(~f: @+c:Ctx -> @+b:U32 -> U32, n: Nat, z: Bool, +c: Ctx, +rest: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n z:
    case 0n _:
      acc
    case 1n+p True{}:
      acc
    case 1n+p False{}:
      +b = bit.low(rest)
      +more = (rest .^. b : U32)
      walk(~f, p, U32.is_zero(more), c, more, key.insert(acc, key(f(c, b), C.card.make(ctx.s(c), U32.from_nat(U32.ctz(b))))))

# The power of card b of suit s in this trick.
def card.power(+s: U32, +l: U32, +t: U32, +b: U32) -> U32:
  +r = U32.from_nat(U32.ctz(b))
  R.sel(U32.is_eq(s, l), (16 + r : U32), R.sel(U32.is_eq(s, t), (32 + r : U32), 0))

# On lead. x0 is the base of the suit, x1 is the right-hand opponent's holding in it,
# mine and theirs are partner's holding and the left-hand opponent's, x2 packs what
# kind of holding it is, and x3 is the card from the memory of best moves.
def w.lead(+c: Ctx, +b: U32) -> U32:
  match c:
    case Ctx{+s, _, _, +me, +all, +add, +p, +a, +base, +o, +kind, +memo}:
      +r = rank.of(b)
      +top = bit.top(all)
      +win = U32.is_gt(U32.max(b, p), (a .|. o : U32)) && U32.is_zero(add)
      +low = Bool.not(win)
      +hit = U32.is_eq(C.card.make(s, U32.from_nat(U32.ctz(b))), memo)
      +extra = R.sel(hit, R.sel(win, 52, 20), 0)
      +v0 = R.sel(win, (40 - r : U32), (29 - r : U32))
      +v1 = R.sel(win, (50 - r : U32), (44 - r : U32))
      +v2 = R.sel(U32.is_eq(b, top), R.sel(win, 31, 25), R.sel(win, (19 - r : U32), (13 - r : U32)))
      +v3 = R.sel(win, (35 - r : U32), (29 - r : U32))
      +v4 = R.sel(win, 40, 29)
      +v5 = R.sel(win, (30 - r : U32), (13 - r : U32))
      +v = R.pick6(U32.to_nat(kind), v0, v1, v2, v3, v4, v5)
      (base + v + extra : U32)

# The cards of one suit on lead, as keys added to acc.
def lead.suit(+s: U32, +t: U32, +d: U32, +memo: U32, +m: U32, +p: U32, +a: U32, +o: U32, +mt: U32, +at: U32, +bt: U32, acc: List<&2, U32>) -> List<&2, U32>:
  +all = (m .|. p .|. a .|. o : U32)
  +top = bit.top(all)
  +rest = (all .^. top : U32)
  +second = R.sel(U32.is_zero(rest), 0, bit.top(rest))
  +la = C.bits.count(a)
  +lb = C.bits.count(o)
  +side = U32.is_ne(s, t)
  +ruff = side && ((U32.is_zero(a) && U32.is_ne(at, 0)) || (U32.is_zero(o) && U32.is_ne(bt, 0)))
  +own = U32.is_ne((m .&. top : U32), 0)
  +par = U32.is_ne((p .&. top : U32), 0)
  +cl = R.sel(U32.is_zero(a), (d + 4 : U32), (la * 4 : U32))
  +cr = R.sel(U32.is_zero(o), (d + 4 : U32), (lb * 4 : U32))
  +up = R.sel(side && U32.is_eq(C.bits.count(m), 1) && U32.is_ne(mt, 0) && par && U32.is_ge(C.bits.count(p), 2), 16, 0)
  +down = (R.sel(ruff, 10, 0) + R.sel(U32.is_ne((o .&. (top .|. second) : U32), 0), 18, 0) : U32)
  +base = (512 + up - down - ((cl + cr) * 32) / 15 : U32)
  +single = U32.is_eq(a, top) || U32.is_eq(o, top)
  +own2 = U32.is_ne((m .&. second : U32), 0)
  +par2 = U32.is_ne((p .&. second : U32), 0)
  +eq2 = own2 && equivalent(second, m, all)
  +kind = R.sel(single, 0, R.sel(own, R.sel(par2, 1, 2), R.sel(par, R.sel(own2, 1, 3), R.sel(eq2, 4, 5))))
  key.merge(walk(~w.lead, 13n, U32.is_zero(m), Ctx{s, t, s, m, all, Bool.to_u32(ruff), p, a, base, o, kind, memo}, tops(m, all), Nil{}), 1048576, acc)

def gen.lead(+t: U32, +d: U32, +memo: U32, +m01: U32, +m23: U32, +a01: U32, +a23: U32, +p01: U32, +p23: U32, +b01: U32, +b23: U32) -> List<&2, U32>:
  +st = U32.to_nat(t)
  +mt = R.suit.mask(st, m01, m23)
  +at = R.suit.mask(st, a01, a23)
  +bt = R.suit.mask(st, b01, b23)
  keys.cards(
    lead.suit(0, t, d, memo, (m01 >> 16n : U32), (p01 >> 16n : U32), (a01 >> 16n : U32), (b01 >> 16n : U32), mt, at, bt,
      lead.suit(1, t, d, memo, (m01 .&. 65535 : U32), (p01 .&. 65535 : U32), (a01 .&. 65535 : U32), (b01 .&. 65535 : U32), mt, at, bt,
        lead.suit(2, t, d, memo, (m23 >> 16n : U32), (p23 >> 16n : U32), (a23 >> 16n : U32), (b23 >> 16n : U32), mt, at, bt,
          lead.suit(3, t, d, memo, (m23 .&. 65535 : U32), (p23 .&. 65535 : U32), (a23 .&. 65535 : U32), (b23 .&. 65535 : U32), mt, at, bt, Nil{})))))

# Second to play. mine is partner's power and theirs is the best of the rest; x0 and
# x1 are the holdings in the suit led of the leader's partner and of my partner, x2
# the leader's, and x3 the card led as a bit.
def w.second(+c: Ctx, +b: U32) -> U32:
  match c:
    case Ctx{+s, +t, +l, +me, +all, +add, +mine, +theirs, +f3, +f4, +lm, +c0}:
      +r = rank.of(b)
      +win = U32.is_gt(U32.max(card.power(s, l, t, b), mine), theirs)
      +eq = equivalent(b, me, all)
      +low3 = U32.is_ne(f3, 0) && U32.is_gt(bit.low(f3), b)
      +low4 = U32.is_ne(f4, 0) && U32.is_gt(bit.low(f4), b)
      +over = U32.is_gt(b, c0)
      +mid = U32.is_ne(lm, 0) && U32.is_ne((f4 .&. (0 - (c0 << 1n)) .&. (bit.top(lm) - 1) : U32), 0)
      +top_lead = U32.is_zero(lm) || U32.is_gt(b, bit.top(lm))
      +follow_win = R.sel(low3, 45, R.sel(mid, 60, R.sel(over, R.sel(low4, 75, R.sel(top_lead, 70, R.sel(eq, 60, 45))), R.sel(U32.is_ne(f4, 0), R.sel(eq, 50, 45), 45))))
      +follow_lose = R.sel(low3 || low4, 0, R.sel(over, R.sel(eq, 20, 10), 0))
      +trump = U32.is_eq(s, t)
      +void_v = R.sel(win, R.sel(trump, 30, 60), R.sel(trump, 15, 0))
      +v = R.sel(U32.is_eq(s, l), R.sel(win, follow_win, follow_lose), (void_v + add : U32))
      (512 + v - r : U32)

# Third to play. mine is the power of the card winning if it is partner's, otherwise
# 0, and theirs is the power of the rest. x0 is the power of the card winning.
def w.third(+c: Ctx, +b: U32) -> U32:
  match c:
    case Ctx{+s, +t, +l, +me, +all, +add, +mine, +theirs, +pb, _, _, _}:
      +r = rank.of(b)
      +px = card.power(s, l, t, b)
      +win = U32.is_gt(U32.max(px, mine), theirs)
      +trump = U32.is_eq(s, t)
      +top = U32.is_gt(px, pb)
      +pard = U32.is_ne(mine, 0)
      +eq = equivalent(b, me, all)
      +rest = (all .^. bit.top(all) : U32)
      +is2 = U32.is_ne(rest, 0) && U32.is_eq(bit.top(rest), b)
      +void_win = R.sel(pard, R.sel(trump && U32.is_ne(l, t), 30, 60), R.sel(trump && top, 70, R.sel(trump, 15, 30)))
      +void_lose = R.sel(trump && top, 40, 0)
      +under = trump && Bool.not(top)
      +void_v = (R.sel(win, void_win, void_lose) + add - R.sel(under && Bool.not(win), 15, 0) : U32)
      +follow_lose = R.sel(top, R.sel(is2, (25 + r : U32), R.sel(eq, 20, 10)), (0 - 10 : U32))
      +v = R.sel(U32.is_eq(s, l), R.sel(win, 60, follow_lose), void_v)
      (512 + v - r : U32)

# Last to play. mine says partner is winning the trick, and theirs is the power of
# the card winning.
def w.fourth(+c: Ctx, +b: U32) -> U32:
  match c:
    case Ctx{+s, +t, +l, _, _, +add, +mine, +theirs, _, _, _, _}:
      +r = rank.of(b)
      +px = card.power(s, l, t, b)
      +trump = U32.is_eq(s, t)
      +pard = U32.is_ne(mine, 0)
      +void_v = R.sel(pard, (R.sel(trump, 14, 30) + add : U32), R.sel(trump, R.sel(U32.is_gt(px, theirs), (30 + add : U32), 0), (14 + add : U32)))
      +follow = R.sel(pard || U32.is_gt(px, theirs), 30, 14)
      (512 + R.sel(U32.is_eq(s, l), follow, void_v) - r : U32)

# The bonus a suit gets when a hand is void in the suit led.
def discard.add(+m: U32, +all: U32) -> U32:
  +n = C.bits.count(m)
  +rest = (all .^. bit.top(all) : U32)
  +has2 = U32.is_ne(rest, 0) && U32.is_ne((m .&. bit.top(rest) : U32), 0)
  ((n * 64) / 36 - R.sel(U32.is_eq(n, 2) && has2, 2, 0) : U32)

# The cards of one suit when void in the suit led, with the top one of each suit
# ahead of the rest, as keys added to acc.
def void.suit(~f: @+c:Ctx -> @+b:U32 -> U32, +s: U32, +t: U32, +l: U32, +m: U32, +all: U32, +mine: U32, +theirs: U32, +x0: U32, +x1: U32, +x2: U32, +x3: U32, acc: List<&2, U32>) -> List<&2, U32>:
  key.merge(walk(~f, 13n, U32.is_zero(m), Ctx{s, t, l, m, all, discard.add(m, all), mine, theirs, x0, x1, x2, x3}, tops(m, all), Nil{}), 1048576, acc)

# The moves of a hand following suit or not, where the holdings of the suit led are
# f, and so on for a void, all weighed by f.
def gen.follow(~f: @+c:Ctx -> @+b:U32 -> U32, follows: Bool, +t: U32, +l: U32, +m01: U32, +m23: U32, +l01: U32, +l23: U32, +mine: U32, +theirs: U32, +x0: U32, +x1: U32, +x2: U32, +x3: U32) -> List<&2, U32>:
  match follows:
    case True{}:
      +ln = U32.to_nat(l)
      +ma = R.suit.mask(ln, m01, m23)
      +al = R.suit.mask(ln, l01, l23)
      keys.cards(walk(~f, 13n, U32.is_zero(ma), Ctx{l, t, l, ma, al, 0, mine, theirs, x0, x1, x2, x3}, tops(ma, al), Nil{}))
    case False{}:
      keys.cards(
        void.suit(~f, 0, t, l, (m01 >> 16n : U32), (l01 >> 16n : U32), mine, theirs, x0, x1, x2, x3,
          void.suit(~f, 1, t, l, (m01 .&. 65535 : U32), (l01 .&. 65535 : U32), mine, theirs, x0, x1, x2, x3,
            void.suit(~f, 2, t, l, (m23 >> 16n : U32), (l23 >> 16n : U32), mine, theirs, x0, x1, x2, x3,
              void.suit(~f, 3, t, l, (m23 .&. 65535 : U32), (l23 .&. 65535 : U32), mine, theirs, x0, x1, x2, x3, Nil{})))))

# The power of the card winning the trick: a card of the suit led, or else a trump.
def best.power(+best: U32, +l: U32) -> U32:
  (R.sel(U32.is_eq(C.card.suit(best), l), 16, 32) + C.card.rank(best) : U32)

# Whether partner is winning the trick.
def best.pard(+tr: U32) -> Bool:
  U32.is_zero(((R.trick.seat(tr) .^. R.trick.owner(tr)) .&. 1 : U32))

# Dispatches on the number of cards on the table. a is the hand after this one, p
# is partner, and b is the hand before it.
def gen.at(played: Nat, +t: U32, +tr: U32, +d: U32, +memo: U32, +l01: U32, +l23: U32, +m01: U32, +m23: U32, +a01: U32, +a23: U32, +p01: U32, +p23: U32, +b01: U32, +b23: U32) -> List<&2, U32>:
  match played:
    case 0n:
      gen.lead(t, d, memo, m01, m23, a01, a23, p01, p23, b01, b23)
    case 1n:
      +st = U32.to_nat(t)
      +l = R.trick.lead(tr)
      +ln = U32.to_nat(l)
      +best = R.trick.best(tr)
      gen.follow(~w.second, U32.is_ne(R.suit.mask(ln, m01, m23), 0), t, l, m01, m23, l01, l23,
        second.power(ln, st, p01, p23), U32.max(best.power(best, l), second.power(ln, st, a01, a23)),
        R.suit.mask(ln, a01, a23), R.suit.mask(ln, p01, p23), R.suit.mask(ln, b01, b23), C.card.bit(best))
    case 2n:
      +st = U32.to_nat(t)
      +l = R.trick.lead(tr)
      +ln = U32.to_nat(l)
      +pb = best.power(R.trick.best(tr), l)
      +pard = best.pard(tr)
      gen.follow(~w.third, U32.is_ne(R.suit.mask(ln, m01, m23), 0), t, l, m01, m23, l01, l23,
        R.sel(pard, pb, 0), U32.max(R.sel(pard, 0, pb), second.power(ln, st, a01, a23)), pb, 0, 0, 0)
    case _:
      +l = R.trick.lead(tr)
      +ln = U32.to_nat(l)
      gen.follow(~w.fourth, U32.is_ne(R.suit.mask(ln, m01, m23), 0), t, l, m01, m23, l01, l23,
        R.sel(best.pard(tr), 1, 0), best.power(R.trick.best(tr), l), 0, 0, 0, 0)

# The moves to try in a position with d cards left, where l01 and l23 are the cards
# in play at the start of this trick, and memo is the card from the memory.
def gen(+t: U32, pos: R.Pos, +l01: U32, +l23: U32, +memo: U32, +d: U32) -> List<&2, U32>:
  match pos:
    case R.Pos{+n01, +n23, +e01, +e23, +s01, +s23, +w01, +w23, +tr, _}:
      +seat = R.trick.seat(tr)
      +i = U32.to_nat(seat)
      +j = U32.to_nat(((seat + 1) .&. 3 : U32))
      +k = U32.to_nat(((seat + 2) .&. 3 : U32))
      +o = U32.to_nat(((seat + 3) .&. 3 : U32))
      gen.at(U32.to_nat(R.trick.played(tr)), t, tr, d, memo, l01, l23,
        R.pick(i, n01, e01, s01, w01), R.pick(i, n23, e23, s23, w23),
        R.pick(j, n01, e01, s01, w01), R.pick(j, n23, e23, s23, w23),
        R.pick(k, n01, e01, s01, w01), R.pick(k, n23, e23, s23, w23),
        R.pick(o, n01, e01, s01, w01), R.pick(o, n23, e23, s23, w23))

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

# The sure tricks from the start of a trick: for the side on lead in the low byte,
# and for its opponents above that.
def counts.go(+t: U32, +seat: U32, +left: U32, +n01: U32, +n23: U32, +e01: U32, +e23: U32, +s01: U32, +s23: U32, +w01: U32, +w23: U32) -> U32:
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
  (quick(st, left, m0, m1, m2, m3, p0, p1, p2, p3, a0, a1, a2, a3, b0, b1, b2, b3) .|. (l << 8n) : U32)

def counts(+t: U32, pos: R.Pos, +left: U32) -> U32:
  match pos:
    case R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, +tr, _}:
      counts.go(t, R.trick.seat(tr), left, n01, n23, e01, e23, s01, s23, w01, w23)

def boundary.pos(+t: U32, +pos: R.Pos, +won: U32, +left: U32, +target: U32) -> U32:
  +both = counts(t, pos, left)
  boundary.side(R.pos.ns(pos), (both .&. 255 : U32), (both >> 8n : U32), won, left, target)

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
def enter.go(go: Bool, +t: U32, +pos: R.Pos, +l01: U32, +l23: U32, +memo: U32, +d: U32) -> List<&2, U32>:
  match go:
    case True{}:
      gen(t, pos, l01, l23, memo, d)
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

# A Res whose memo is slot i of the memory.
def peek.go(ok: Bool, n: Nat, pair: Array<U32> & U32) -> Res:
  match pair:
    case (m, memo):
      Res{ok, n, m, memo}

def peek(ok: Bool, n: Nat, m: Array<U32>, +i: U32) -> Res:
  peek.go(ok, n, Array.get(U32, m, i))

def peek.res(r: Res, +i: U32) -> Res:
  match r:
    case Res{ok, n, m, _}:
      peek(ok, n, m, i)

# Tries the moves ms of a position with d cards left. r is the answer so far: a
# call cannot be destructured in place, so a child's answer rides into the next
# sibling as an argument. The answer settles a node once it says true for
# North-South or false for East-West, and otherwise the node goes on to the next
# move; with no moves left, the answer stands. A move that settles the node goes
# into the memory, at slot, and last is that move.
#
# A child has one card fewer, and a sibling has one move fewer with the same d.
def search(+d: Nat, ms: List<&2, U32>, ns: Bool, r: Res, +slot: U32, +last: U32, +t: U32, +target: U32, +l01: U32, +l23: U32, +pos: R.Pos) -> Res:
  match d ms ns r:
    case 0n _ _ x:
      x
    case 1n+p _ True{} Res{True{}, n, m, _}:
      Res{True{}, n, Array.set(U32, m, slot, last), 0}
    case 1n+p _ False{} Res{False{}, n, m, _}:
      Res{False{}, n, Array.set(U32, m, slot, last), 0}
    case 1n+p Nil{} _ x:
      x
    case 1n+p Con{+c, rest} True{} Res{False{}, n, m, +memo}:
      +child = R.play(t, pos, c)
      +cns = R.pos.ns(child)
      +tr = R.pos.trick(child)
      +bound = U32.is_zero(R.trick.played(tr))
      +code = cut.at(U32.to_nat(R.trick.played(tr)), t, child, R.pos.won(child), U32.from_nat(p), target)
      +c01 = live.at(bound, R.pos.live01(child), l01)
      +c23 = live.at(bound, R.pos.live23(child), l23)
      +here = U32.from_nat(p)
      search(1n+p, rest, True{},
        peek.res(search(p, enter.go(U32.is_zero(code), t, child, c01, c23, memo, here), cns, peek(enter.ok(code, cns), 1n+n, m, (here - 1 : U32)), mem.none(), 0, t, target, c01, c23, child), here),
        U32.from_nat(1n+p), c, t, target, l01, l23, pos)
    case 1n+p Con{+c, rest} False{} Res{True{}, n, m, +memo}:
      +child = R.play(t, pos, c)
      +cns = R.pos.ns(child)
      +tr = R.pos.trick(child)
      +bound = U32.is_zero(R.trick.played(tr))
      +code = cut.at(U32.to_nat(R.trick.played(tr)), t, child, R.pos.won(child), U32.from_nat(p), target)
      +c01 = live.at(bound, R.pos.live01(child), l01)
      +c23 = live.at(bound, R.pos.live23(child), l23)
      +here = U32.from_nat(p)
      search(1n+p, rest, False{},
        peek.res(search(p, enter.go(U32.is_zero(code), t, child, c01, c23, memo, here), cns, peek(enter.ok(code, cns), 1n+n, m, (here - 1 : U32)), mem.none(), 0, t, target, c01, c23, child), here),
        U32.from_nat(1n+p), c, t, target, l01, l23, pos)

# Runs one search from the start of a trick.
def ask.go(+d: Nat, +t: U32, +pos: R.Pos, +target: U32, r: Res) -> Res:
  match r:
    case Res{_, n, m, +memo}:
      +ns = R.pos.ns(pos)
      +l01 = R.pos.live01(pos)
      +l23 = R.pos.live23(pos)
      search(d, gen(t, pos, l01, l23, memo, U32.from_nat(d)), ns, peek(Bool.not(ns), n, m, (U32.from_nat(d) - 1 : U32)), mem.none(), 0, t, target, l01, l23, pos)

# Runs one search, unless told there is nothing to ask.
def ask(stop: Bool, +d: Nat, +t: U32, +pos: R.Pos, +target: U32, n: Nat, m: Array<U32>) -> Res:
  match stop:
    case True{}:
      Res{False{}, n, m, 0}
    case False{}:
      ask.go(d, t, pos, target, peek(False{}, n, m, U32.from_nat(d)))

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
def narrow(fuel: Nat, done: Bool, r: Res, +target: U32, +d: Nat, +t: U32, +pos: R.Pos, +lo: U32, +hi: U32) -> Val:
  match fuel done r:
    case 0n _ Res{_, n, m, _}:
      Val{lo, n, m}
    case 1n+p True{} Res{_, n, m, _}:
      Val{lo, n, m}
    case 1n+p False{} Res{+ok, n, m, _}:
      +lo2 = driver.lo(ok, target, lo)
      +hi2 = driver.hi(ok, target, hi)
      +stop = U32.is_ge(lo2, hi2)
      +next = driver.next(ok, lo2, hi2)
      narrow(p, stop, ask(stop, d, t, pos, next, n, m), next, d, t, pos, lo2, hi2)

# North-South's tricks from the start of a trick with d cards left, starting from
# a guess at the answer.
def solve(+d: Nat, +t: U32, +pos: R.Pos, +guess: U32, n: Nat, m: Array<U32>) -> Val:
  +lo = R.pos.won(pos)
  +hi = (lo + (U32.from_nat(d) >> 2n) : U32)
  +stop = U32.is_ge(lo, hi)
  +target = driver.first(guess, lo, hi)
  narrow(14n, stop, ask(stop, d, t, pos, target, n, m), target, d, t, pos, lo, hi)

# ---------------------------------------------------------------------------
# The table

# Fills the table from its last entry to its first, so that it comes out in the
# order of B.table. r is the result for entry i + 1, and it feeds the guess for
# entry i: moving the lead by one seat rarely changes the result by much.
def table.go(k: Nat, r: Val, +i: U32, +d: Nat, +left: U32, +deal: C.Deal, acc: List<&2, U32>) -> B.Table:
  match k r:
    case 0n Val{+v, n, _}:
      B.Table{B.table.entry(U32.is_zero(((i + 1) .&. 1 : U32)), left, v) <> acc, n}
    case 1n+p Val{+v, n, m}:
      +t = (i >> 2n : U32)
      +decl = (i .&. 3 : U32)
      +leader = ((decl + 1) .&. 3 : U32)
      table.go(p, solve(d, t, R.pos.start(deal, leader), v, n, m), (i - 1 : U32), d, left, deal,
        B.table.entry(U32.is_zero(((i + 1) .&. 1 : U32)), left, v) <> acc)

# The double dummy table of a deal, as B.table gives it.
def table(+deal: C.Deal) -> B.Table:
  +cards = B.deal.cards(deal)
  +d = U32.to_nat(cards)
  +left = (cards / 4 : U32)
  table.go(19n, solve(d, 4, R.pos.start(deal, 0), ((left + 1) / 2 : U32), 0n, [mem.none() : U32*64n]), 18, d, left, deal, Nil{})

# ---------------------------------------------------------------------------
# Sure tricks, for checking

def bounds.go(k: Nat, +i: U32, +left: U32, +deal: C.Deal, acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      acc
    case 1n+p:
      +both = counts((i >> 2n : U32), R.pos.start(deal, ((i + 1) .&. 3 : U32)), left)
      bounds.go(p, (i - 1 : U32), left, deal, (both .&. 255 : U32) <> ((both >> 8n : U32) <> acc))

# For each entry of the table in turn, with the seat on declarer's left on lead: the
# tricks the search is sure of for that seat's side, then for declarer's side.
def bounds(+deal: C.Deal) -> B.Table:
  B.Table{bounds.go(20n, 19, (B.deal.cards(deal) / 4 : U32), deal, Nil{}), 0n}
