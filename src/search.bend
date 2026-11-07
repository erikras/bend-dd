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
#   - DDS's move weights for each place in the trick, and a memory of best moves;
#   - a transposition table with partition search, from the start of a trick: an
#     answer also says which cards it rested on, so it holds for every position
#     that agrees on them;
#   - the small card filter: a small card is not tried if another that the answers so
#     far don't rest on has been tried in its suit.

import Base
import ./cards.bend as C
import ./rules.bend as R
import ./brute.bend as B

# The moves of a position, as a list of its own. Reference counts are per type at run
# time, so a list that is shared anywhere in the program would count every cell of
# these as well, and a node builds and takes apart a lot of them.
type Moves is Type:
  MNil{}
  MCon{head: U32, tail: Moves}

# A true or false answer with the positions visited so far, and the memory of best
# moves. Nat counts the positions: it is a machine word at run time, and it stops
# the program at 2^48 instead of wrapping, which takes days at this solver's rates.
#
# The memory holds, for each number of cards left, the card that last settled a node
# with that many left. It has one owner, so it is updated in place as it is handed
# along, including through every search for a deal. A call cannot be destructured
# in place, so reading it inside the search has to happen in a helper: each Res comes
# with memo, what the memory holds for the next child of the node it goes to.
#
# Going into a node, moves holds its moves. Coming out, w01 and w23 are its winning
# ranks, packed as a hand is: the answer holds for every position that has the same
# suit lengths and the same owners for each card down to the lowest of these in its
# suit. The top bit of w01 says that the answer came from a cut or from the table, so
# it isn't worth storing.
type Res is Type:
  Res{ok: Bool, nodes: Nat, mem: Array<U32>, memo: U32, moves: Moves, w01: U32, w23: U32}

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

def key.insert(xs: Moves, +k: U32) -> Moves:
  match xs:
    case MNil{}:
      MCon{k, MNil{}}
    case MCon{+h, t}:
      MCon{U32.max(k, h), key.insert(t, U32.min(k, h))}

# Adds a suit's keys to acc, where the top key of each suit gets ahead of every other
# card, which makes for a good mix of suits at the front of the list.
def key.merge(xs: Moves, +bonus: U32, acc: Moves) -> Moves:
  match xs:
    case MNil{}:
      acc
    case MCon{+h, t}:
      key.merge(t, 0, key.insert(acc, (h + bonus : U32)))

def keys.cards(xs: Moves) -> Moves:
  match xs:
    case MNil{}:
      MNil{}
    case MCon{+h, t}:
      MCon{(h .&. 63 : U32), keys.cards(t)}

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
def walk(~f: @+c:Ctx -> @+b:U32 -> U32, n: Nat, z: Bool, +c: Ctx, +rest: U32, acc: Moves) -> Moves:
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
def lead.suit(+s: U32, +t: U32, +d: U32, +memo: U32, +m: U32, +p: U32, +a: U32, +o: U32, +mt: U32, +at: U32, +bt: U32, acc: Moves) -> Moves:
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
  key.merge(walk(~w.lead, 13n, U32.is_zero(m), Ctx{s, t, s, m, all, Bool.to_u32(ruff), p, a, base, o, kind, memo}, tops(m, all), MNil{}), 1048576, acc)

def gen.lead(+t: U32, +d: U32, +memo: U32, +m01: U32, +m23: U32, +a01: U32, +a23: U32, +p01: U32, +p23: U32, +b01: U32, +b23: U32) -> Moves:
  +st = U32.to_nat(t)
  +mt = R.suit.mask(st, m01, m23)
  +at = R.suit.mask(st, a01, a23)
  +bt = R.suit.mask(st, b01, b23)
  keys.cards(
    lead.suit(0, t, d, memo, (m01 >> 16n : U32), (p01 >> 16n : U32), (a01 >> 16n : U32), (b01 >> 16n : U32), mt, at, bt,
      lead.suit(1, t, d, memo, (m01 .&. 65535 : U32), (p01 .&. 65535 : U32), (a01 .&. 65535 : U32), (b01 .&. 65535 : U32), mt, at, bt,
        lead.suit(2, t, d, memo, (m23 >> 16n : U32), (p23 >> 16n : U32), (a23 >> 16n : U32), (b23 >> 16n : U32), mt, at, bt,
          lead.suit(3, t, d, memo, (m23 .&. 65535 : U32), (p23 .&. 65535 : U32), (a23 .&. 65535 : U32), (b23 .&. 65535 : U32), mt, at, bt, MNil{})))))

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
def void.suit(~f: @+c:Ctx -> @+b:U32 -> U32, +s: U32, +t: U32, +l: U32, +m: U32, +all: U32, +mine: U32, +theirs: U32, +x0: U32, +x1: U32, +x2: U32, +x3: U32, acc: Moves) -> Moves:
  key.merge(walk(~f, 13n, U32.is_zero(m), Ctx{s, t, l, m, all, discard.add(m, all), mine, theirs, x0, x1, x2, x3}, tops(m, all), MNil{}), 1048576, acc)

# The moves of a hand following suit: if only one card is worth trying, it needs no
# weighing.
def gen.one(~f: @+c:Ctx -> @+b:U32 -> U32, one: Bool, +ts: U32, +t: U32, +l: U32, +ma: U32, +al: U32, +mine: U32, +theirs: U32, +x0: U32, +x1: U32, +x2: U32, +x3: U32) -> Moves:
  match one:
    case True{}:
      MCon{C.card.make(l, U32.from_nat(U32.ctz(ts))), MNil{}}
    case False{}:
      keys.cards(walk(~f, 13n, U32.is_zero(ma), Ctx{l, t, l, ma, al, 0, mine, theirs, x0, x1, x2, x3}, ts, MNil{}))

# The moves of a hand following suit or not, where the holdings of the suit led are
# f, and so on for a void, all weighed by f.
def gen.follow(~f: @+c:Ctx -> @+b:U32 -> U32, follows: Bool, +t: U32, +l: U32, +m01: U32, +m23: U32, +l01: U32, +l23: U32, +mine: U32, +theirs: U32, +x0: U32, +x1: U32, +x2: U32, +x3: U32) -> Moves:
  match follows:
    case True{}:
      +ln = U32.to_nat(l)
      +ma = R.suit.mask(ln, m01, m23)
      +al = R.suit.mask(ln, l01, l23)
      +ts = tops(ma, al)
      gen.one(~f, U32.is_eq(ts, bit.low(ts)), ts, t, l, ma, al, mine, theirs, x0, x1, x2, x3)
    case False{}:
      keys.cards(
        void.suit(~f, 0, t, l, (m01 >> 16n : U32), (l01 >> 16n : U32), mine, theirs, x0, x1, x2, x3,
          void.suit(~f, 1, t, l, (m01 .&. 65535 : U32), (l01 .&. 65535 : U32), mine, theirs, x0, x1, x2, x3,
            void.suit(~f, 2, t, l, (m23 >> 16n : U32), (l23 >> 16n : U32), mine, theirs, x0, x1, x2, x3,
              void.suit(~f, 3, t, l, (m23 .&. 65535 : U32), (l23 .&. 65535 : U32), mine, theirs, x0, x1, x2, x3, MNil{})))))

# The power of the card winning the trick: a card of the suit led, or else a trump.
def best.power(+best: U32, +l: U32) -> U32:
  (R.sel(U32.is_eq(C.card.suit(best), l), 16, 32) + C.card.rank(best) : U32)

# Whether partner is winning the trick.
def best.pard(+tr: U32) -> Bool:
  U32.is_zero(((R.trick.seat(tr) .^. R.trick.owner(tr)) .&. 1 : U32))

# Dispatches on the number of cards on the table. a is the hand after this one, p
# is partner, and b is the hand before it.
def gen.at(played: Nat, +t: U32, +tr: U32, +d: U32, +memo: U32, +l01: U32, +l23: U32, +m01: U32, +m23: U32, +a01: U32, +a23: U32, +p01: U32, +p23: U32, +b01: U32, +b23: U32) -> Moves:
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
def gen(+t: U32, pos: R.Pos, +l01: U32, +l23: U32, +memo: U32, +d: U32) -> Moves:
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

def moves.length(xs: Moves) -> Nat:
  match xs:
    case MNil{}:
      0n
    case MCon{_, t}:
      1n+moves.length(t)

def moves.list(xs: Moves) -> List<&2, U32>:
  match xs:
    case MNil{}:
      Nil{}
    case MCon{+h, t}:
      h <> moves.list(t)

# The moves as a plain list, for tests.
def gen.list(+t: U32, pos: R.Pos, +l01: U32, +l23: U32, +memo: U32, +d: U32) -> List<&2, U32>:
  moves.list(gen(t, pos, l01, l23, memo, d))

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

# A cut's code is its answer, as in cut, plus why above that: see why.
def why.target() -> U32:
  4

def why.quick() -> U32:
  8

def why.later() -> U32:
  12

def why.after() -> U32:
  16

# An answer from the transposition table.
def why.table() -> U32:
  20

def boundary.side(ns: Bool, +q: U32, +l: U32, +won: U32, +left: U32, +target: U32) -> U32:
  match ns:
    case True{}:
      R.sel(U32.is_ge((won + q : U32), target), (1 + why.quick() : U32), R.sel(U32.is_lt((won + left - l : U32), target), (2 + why.later() : U32), 0))
    case False{}:
      R.sel(U32.is_lt((won + left - q : U32), target), (2 + why.quick() : U32), R.sel(U32.is_ge((won + l : U32), target), (1 + why.later() : U32), 0))

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
      (code + why.target() : U32)

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
  R.sel(ns, R.sel(U32.is_ge((won + 1 : U32), target), (1 + why.after() : U32), 0), R.sel(U32.is_lt((won + left - 1 : U32), target), (2 + why.after() : U32), 0))

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

# The answer a node starts from. With no cut, it is the one that does not settle
# the node yet: false when North-South choose, true when East-West choose.
def enter.ok(+code: U32, +ns: Bool) -> Bool:
  (U32.is_zero(code) && Bool.not(ns)) || U32.is_eq((code .&. 3 : U32), 1)

def live.at(bound: Bool, +x: U32, +old: U32) -> U32:
  match bound:
    case True{}:
      x
    case False{}:
      old

# ---------------------------------------------------------------------------
# Statistics
#
# The search takes three hooks as templates, so each set of hooks compiles to its own
# copy of it and the plain copy has nothing in it to pay for. The counting copy uses
# the rest of the memory array: each table entry has 32 slots from 64 + 32 * entry,
# which hold counters of two words each, low word first, and then a log of targets.

def stat.nodes() -> U32:
  0

def stat.searches() -> U32:
  2

# The cuts follow in the order of why, target first, two slots each, with answers
# from the table last.
def stat.cuts() -> U32:
  4

def stat.moves() -> U32:
  14

def stat.kept() -> U32:
  16

def stat.log() -> U32:
  18

# The slot of the memory array holding the base of the current entry.
def stat.current() -> U32:
  60

def stat.carry(c: Bool, p: Array<U32> & U32, +i: U32) -> Array<U32>:
  match c:
    case True{}:
      match p:
        case (m, +v):
          Array.set(U32, m, i, (v + 1 : U32))
    case False{}:
      match p:
        case (m, _):
          m

def stat.add.go(p: Array<U32> & U32, +i: U32, +by: U32) -> Array<U32>:
  match p:
    case (m, +lo):
      +x = (lo + by : U32)
      stat.carry(U32.is_lt(x, lo), Array.get(U32, Array.set(U32, m, i, x), (i + 1 : U32)), (i + 1 : U32))

def stat.add(m: Array<U32>, +i: U32, +by: U32) -> Array<U32>:
  stat.add.go(Array.get(U32, m, i), i, by)

def stat.moves.at(go: Bool, m: Array<U32>, +base: U32, +t: U32, +pos: R.Pos, +l01: U32, +l23: U32) -> Array<U32>:
  match go:
    case True{}:
      +legal = U32.from_nat(List.length(&2, U32, R.moves(pos)))
      +kept = U32.from_nat(moves.length(gen(t, pos, l01, l23, mem.none(), 0)))
      stat.add(stat.add(m, (base + stat.moves() : U32), legal), (base + stat.kept() : U32), kept)
    case False{}:
      m

def stat.cut.at(go: Bool, m: Array<U32>, +base: U32, +code: U32) -> Array<U32>:
  match go:
    case True{}:
      m
    case False{}:
      # A reason of 1 is the first cut, two slots each.
      stat.add(m, (base + stat.cuts() + (((code >> 2n) - 1) * 2) : U32), 1)

def stat.node.go(p: Array<U32> & U32, +t: U32, +pos: R.Pos, +code: U32, +l01: U32, +l23: U32) -> Array<U32>:
  match p:
    case (m, +base):
      +go = U32.is_zero(code)
      stat.moves.at(go, stat.cut.at(go, stat.add(m, (base + stat.nodes() : U32), 1), base, code), base, t, pos, l01, l23)

# Counts a position reached, how it was cut if it was, and its moves if it was not.
def stat.node(+t: U32, m: Array<U32>, +pos: R.Pos, +code: U32, +l01: U32, +l23: U32) -> Array<U32>:
  stat.node.go(Array.get(U32, m, stat.current()), t, pos, code, l01, l23)

def stat.log.go(p: Array<U32> & U32, +i: U32, +base: U32, +x: U32) -> Array<U32>:
  match p:
    case (m, +v):
      stat.add(Array.set(U32, m, i, (v .|. x : U32)), (base + stat.searches() : U32), 1)

# Counts a search, and logs its target in the next four bits, up to 16 targets.
def stat.ask.n(p: Array<U32> & U32, +base: U32, +target: U32) -> Array<U32>:
  match p:
    case (m, +n):
      +i = (base + stat.log() + ((n >> 3n) .&. 1) : U32)
      +x = (target << U32.to_nat(((n .&. 7) * 4 : U32)) : U32)
      stat.log.go(Array.get(U32, m, i), i, base, x)

def stat.ask.go(p: Array<U32> & U32, +target: U32) -> Array<U32>:
  match p:
    case (m, +base):
      stat.ask.n(Array.get(U32, m, (base + stat.searches() : U32)), base, target)

def stat.ask(m: Array<U32>, +target: U32) -> Array<U32>:
  stat.ask.go(Array.get(U32, m, stat.current()), target)

# Starts counting for table entry i.
def stat.begin(m: Array<U32>, +i: U32) -> Array<U32>:
  Array.set(U32, m, stat.current(), (64 + 32 * i : U32))

# ---------------------------------------------------------------------------
# The search

# ---------------------------------------------------------------------------
# Winning ranks

# Two words, packed as a hand is: one mask per suit.
type Ranks is Data:
  Ranks{r01: U32, r23: U32}

def ranks.none() -> Ranks:
  Ranks{0, 0}

def ranks.sel(b: Bool, x: Ranks, y: Ranks) -> Ranks:
  match b:
    case True{}:
      x
    case False{}:
      y

# The mask of a suit as two words.
def ranks.of(+s: U32, +m: U32) -> Ranks:
  +x = R.sel(U32.is_zero((s .&. 1 : U32)), (m << 16n : U32), m)
  ranks.sel(U32.is_lt(s, 2), Ranks{x, 0}, Ranks{0, x})

# The cards below b in holding h that are next to it among the cards in play. The
# search only tries the top card of such a run, so whatever the top card proved has
# to be true of all of them.
def run.below(+b: U32, +h: U32, +live: U32) -> U32:
  +below = (live .&. (b - 1) : U32)
  +other = (below .&. U32.not(h) : U32)
  +mine = (below .&. h : U32)
  R.sel(U32.is_zero(other), mine, (mine .&. (0 - (2 << U32.log2(other))) : U32))

# The holdings of a position by the seats from the one given, in a suit.
def hand.suit(+i: U32, +s: Nat, +n01: U32, +n23: U32, +e01: U32, +e23: U32, +s01: U32, +s23: U32, +w01: U32, +w23: U32) -> U32:
  +k = U32.to_nat((i .&. 3 : U32))
  R.suit.mask(s, R.pick(k, n01, e01, s01, w01), R.pick(k, n23, e23, s23, w23))

# Why the fourth card of a trick leaves winning ranks. A trick won over another card
# of the suit was won by rank, and that is all the search compares.
def trick.ranks.go(+s: U32, +b: U32, pos: R.Pos, +l01: U32, +l23: U32) -> Ranks:
  match pos:
    case R.Pos{+n01, +n23, +e01, +e23, +s01, +s23, +w01, +w23, +tr, _}:
      +sn = U32.to_nat(s)
      +h = hand.suit(R.trick.seat(tr), sn, n01, n23, e01, e23, s01, s23, w01, w23)
      ranks.of(s, (b .|. run.below(b, h, R.suit.mask(sn, l01, l23)) : U32))

# The ranks from a trick that ended with card c, where pos is the position before c
# and child the one after it, whose seat to play won the trick.
def trick.ranks(bound: Bool, +t: U32, pos: R.Pos, +c: U32, +child: R.Pos, +l01: U32, +l23: U32) -> Ranks:
  match bound:
    case False{}:
      ranks.none()
    case True{}:
      +tr = R.pos.trick(pos)
      +best = R.trick.best(tr)
      +win = R.beats(t, best, c)
      +card = R.sel(win, c, best)
      +same = U32.is_eq(C.card.suit(c), C.card.suit(best))
      +rank = same || (R.trick.rank(tr) && Bool.not(win))
      ranks.sel(rank, trick.ranks.go(C.card.suit(card), C.card.bit(card), child, l01, l23), ranks.none())

# The cards of side above the best card of the rest of the suit.
def top.run(+side: U32, +all: U32) -> U32:
  +rest = (all .^. side : U32)
  R.sel(U32.is_zero(rest), side, (side .&. (0 - (2 << U32.log2(rest))) : U32))

# Quick tricks count how many top cards of each suit the side on lead holds. Given
# the same lengths, they only rise with these.
def quick.ranks(+tr: U32, pos: R.Pos) -> Ranks:
  match pos:
    case R.Pos{+n01, +n23, +e01, +e23, +s01, +s23, +w01, +w23, _, _}:
      +k = U32.to_nat((R.trick.seat(tr) .&. 1 : U32))
      +a01 = R.pick(k, (n01 .|. s01 : U32), (e01 .|. w01 : U32), 0, 0)
      +a23 = R.pick(k, (n23 .|. s23 : U32), (e23 .|. w23 : U32), 0, 0)
      +l01 = (n01 .|. e01 .|. s01 .|. w01 : U32)
      +l23 = (n23 .|. e23 .|. s23 .|. w23 : U32)
      Ranks{
        ((top.run((a01 >> 16n : U32), (l01 >> 16n : U32)) << 16n) .|. top.run((a01 .&. 65535 : U32), (l01 .&. 65535 : U32)) : U32),
        ((top.run((a23 >> 16n : U32), (l23 >> 16n : U32)) << 16n) .|. top.run((a23 .&. 65535 : U32), (l23 .&. 65535 : U32)) : U32)}

def bit.top.or0(+x: U32) -> U32:
  R.sel(U32.is_zero(x), 0, bit.top(x))

# Later tricks look at who holds the top card of each suit at no trumps, and the top
# two trumps otherwise, and otherwise only at lengths.
def later.ranks(+t: U32, +l01: U32, +l23: U32) -> Ranks:
  +tm = R.suit.mask(U32.to_nat(t), l01, l23)
  +top2 = (bit.top.or0(tm) .|. bit.top.or0((tm .^. bit.top.or0(tm) : U32)) : U32)
  ranks.sel(U32.is_eq(t, 4),
    Ranks{
      ((bit.top.or0((l01 >> 16n : U32)) << 16n) .|. bit.top.or0((l01 .&. 65535 : U32)) : U32),
      ((bit.top.or0((l23 >> 16n : U32)) << 16n) .|. bit.top.or0((l23 .&. 65535 : U32)) : U32)},
    ranks.of(t, top2))

# The check after the lead rests on the card that wins the trick for sure. If it is
# still in a hand, it plays that card, so its run counts. If it is the card led, the
# run of the leader counts.
def after.ranks.go(+t: U32, +tr: U32, +l01: U32, +l23: U32, +n01: U32, +n23: U32, +e01: U32, +e23: U32, +s01: U32, +s23: U32, +w01: U32, +w23: U32) -> Ranks:
  +seat = R.trick.seat(tr)
  +best = R.trick.best(tr)
  +l = R.trick.lead(tr)
  +ln = U32.to_nat(l)
  +st = U32.to_nat(t)
  +hi = U32.max(U32.max((16 + C.card.rank(best) : U32), second.power(ln, st, R.pick(U32.to_nat(seat), n01, e01, s01, w01), R.pick(U32.to_nat(seat), n23, e23, s23, w23))),
    U32.max(second.power(ln, st, R.pick(U32.to_nat(((seat + 1) .&. 3 : U32)), n01, e01, s01, w01), R.pick(U32.to_nat(((seat + 1) .&. 3 : U32)), n23, e23, s23, w23)),
      second.power(ln, st, R.pick(U32.to_nat(((seat + 2) .&. 3 : U32)), n01, e01, s01, w01), R.pick(U32.to_nat(((seat + 2) .&. 3 : U32)), n23, e23, s23, w23))))
  +s = R.sel(U32.is_ge(hi, 32), t, l)
  +sn = U32.to_nat(s)
  +b = (1 << U32.to_nat((hi .&. 15 : U32)) : U32)
  +live = R.suit.mask(sn, l01, l23)
  +h0 = hand.suit((seat + 3 : U32), sn, n01, n23, e01, e23, s01, s23, w01, w23)
  +h1 = hand.suit(seat, sn, n01, n23, e01, e23, s01, s23, w01, w23)
  +h2 = hand.suit((seat + 1 : U32), sn, n01, n23, e01, e23, s01, s23, w01, w23)
  +h3 = hand.suit((seat + 2 : U32), sn, n01, n23, e01, e23, s01, s23, w01, w23)
  +h = R.sel(U32.is_ne((h1 .&. b : U32), 0), h1, R.sel(U32.is_ne((h2 .&. b : U32), 0), h2, R.sel(U32.is_ne((h3 .&. b : U32), 0), h3, h0)))
  ranks.of(s, (b .|. run.below(b, h, live) : U32))

def after.ranks(+t: U32, pos: R.Pos, +l01: U32, +l23: U32) -> Ranks:
  match pos:
    case R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, +tr, _}:
      after.ranks.go(t, tr, l01, l23, n01, n23, e01, e23, s01, s23, w01, w23)

# What a cut rests on, by its reason.
def cut.ranks(why: Nat, +t: U32, +pos: R.Pos) -> Ranks:
  match why:
    case 1n:
      ranks.none()
    case 2n:
      quick.ranks(R.pos.trick(pos), pos)
    case 3n:
      later.ranks(t, R.pos.live01(pos), R.pos.live23(pos))
    case _:
      ranks.none()

# ---------------------------------------------------------------------------
# The transposition table
#
# The table is the rest of the memory array, from slot 1024: buckets of 8 entries of
# 8 words each, so a bucket is 64 words. Slot 61 of the array holds the number of
# buckets less one. The whole array has one owner and is handed along, so it is
# updated in place. Entries of the 5 strains share it.
#
# An entry can only be hashed on what every position it matches has in common, and
# late in a deal many positions have the same lengths. So an entry goes in a bucket by
# its pattern, the suits where its top 3 cards all matter (or all of a shorter suit),
# and the hash takes in the owners of those cards. A lookup tries each pattern that
# has been stored with these lengths, which a directory word says: slot 15 of the
# bucket for the lengths and no pattern, as 16 bits. An entry is:
#
#   0: a set top bit, the strain, the leader, and the suit lengths of North and East
#   1: the tricks left, and the suit lengths of South and West
#   2: the fewest and the most tricks North-South take from here (4 bits each), then
#      for each suit how many of the top cards in play matter (4 bits each)
#   3 to 6: for each suit the owners of the cards in play, 2 bits each, the top card
#      highest. Only as many as the top cards that matter are compared.
#   7: unused, except in the first entry of a bucket, where it counts stores, and the
#      second, which is the directory word.
#
# The lengths of three suits and the tricks left give the lengths of the fourth, as
# in DDS, so equal lengths give each hand the same voids.

type TtKey is Data:
  TtKey{k0: U32, k1: U32, o0: U32, o1: U32, o2: U32, o3: U32, lens: U32}

# Whether to use the table at a position with this many tricks left.
def tt.on(+left: U32) -> Bool:
  U32.is_ge(left, 3)

# How big a memory array to make for a deal of this many tricks: a depth, so 2^d
# slots. An array that small has no room for the table, and tt.on keeps away from it.
def tt.depth(+left: U32) -> Nat:
  U32.to_nat(R.sel(U32.is_lt(left, 4), 10, R.sel(U32.is_lt(left, 6), 14, R.sel(U32.is_lt(left, 9), 18, 23))))

def tt.mask.slot() -> U32:
  61

def tt.ready(+d: Nat, m: Array<U32>) -> Array<U32>:
  Array.set(U32, m, tt.mask.slot(), ((1 << U32.to_nat(R.sel(U32.is_ge(U32.from_nat(d), 6), (U32.from_nat(d) - 6 : U32), 0))) - 1 : U32))

def own.go(n: Nat, z: Bool, +rest: U32, +a: U32, +b: U32, +at: U32, +acc: U32) -> U32:
  match n z:
    case 0n _:
      acc
    case 1n+p True{}:
      acc
    case 1n+p False{}:
      +low = bit.low(rest)
      +r = U32.ctz(low)
      +o = (((a >> r) .&. 1) .|. (((b >> r) .&. 1) << 1n) : U32)
      +more = (rest .^. low : U32)
      own.go(p, U32.is_zero(more), more, a, b, (at + 2 : U32), (acc .|. (o << U32.to_nat(at)) : U32))

# The owners of the cards in play in a suit, 2 bits each and the top card highest,
# as 0 for North to 3 for West.
def own(+n: U32, +e: U32, +s: U32, +w: U32) -> U32:
  +live = (n .|. e .|. s .|. w : U32)
  own.go(13n, U32.is_zero(live), live, (e .|. w : U32), (s .|. w : U32), 0, 0)

def lens3(+a: U32, +b: U32, +c: U32) -> U32:
  (C.bits.count(a) .|. (C.bits.count(b) << 4n) .|. (C.bits.count(c) << 8n) : U32)

def tt.key.go(+t: U32, +seat: U32, +left: U32, +n01: U32, +n23: U32, +e01: U32, +e23: U32, +s01: U32, +s23: U32, +w01: U32, +w23: U32) -> TtKey:
  +n0 = (n01 >> 16n : U32)
  +n1 = (n01 .&. 65535 : U32)
  +n2 = (n23 >> 16n : U32)
  +n3 = (n23 .&. 65535 : U32)
  +e0 = (e01 >> 16n : U32)
  +e1 = (e01 .&. 65535 : U32)
  +e2 = (e23 >> 16n : U32)
  +e3 = (e23 .&. 65535 : U32)
  +s0 = (s01 >> 16n : U32)
  +s1 = (s01 .&. 65535 : U32)
  +s2 = (s23 >> 16n : U32)
  +s3 = (s23 .&. 65535 : U32)
  +w0 = (w01 >> 16n : U32)
  +w1 = (w01 .&. 65535 : U32)
  +w2 = (w23 >> 16n : U32)
  +w3 = (w23 .&. 65535 : U32)
  TtKey{
    ((1 << 31n) .|. (t << 26n) .|. (seat << 24n) .|. (lens3(n0, n1, n2) << 12n) .|. lens3(e0, e1, e2) : U32),
    ((left << 24n) .|. (lens3(s0, s1, s2) << 12n) .|. lens3(w0, w1, w2) : U32),
    own(n0, e0, s0, w0), own(n1, e1, s1, w1), own(n2, e2, s2, w2), own(n3, e3, s3, w3),
    (C.bits.count((n0 .|. e0 .|. s0 .|. w0 : U32)) .|. (C.bits.count((n1 .|. e1 .|. s1 .|. w1 : U32)) << 4n) .|. (C.bits.count((n2 .|. e2 .|. s2 .|. w2 : U32)) << 8n) .|. (C.bits.count((n3 .|. e3 .|. s3 .|. w3 : U32)) << 12n) : U32)}

def tt.key.pos(+t: U32, +left: U32, pos: R.Pos) -> TtKey:
  match pos:
    case R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, +tr, _}:
      tt.key.go(t, R.trick.seat(tr), left, n01, n23, e01, e23, s01, s23, w01, w23)

# The key of a position, or nothing to go on when the table isn't in use there.
def tt.key(go: Bool, +t: U32, +left: U32, +pos: R.Pos) -> TtKey:
  match go:
    case True{}:
      tt.key.pos(t, left, pos)
    case False{}:
      TtKey{0, 0, 0, 0, 0, 0, 0}

def key.own(+i: U32, key: TtKey) -> U32:
  match key:
    case TtKey{_, _, a, b, c, d, _}:
      R.pick(U32.to_nat(i), a, b, c, d)

def key.k0(key: TtKey) -> U32:
  match key:
    case TtKey{k, _, _, _, _, _, _}:
      k

def key.k1(key: TtKey) -> U32:
  match key:
    case TtKey{_, k, _, _, _, _, _}:
      k

def key.lens(key: TtKey) -> U32:
  match key:
    case TtKey{_, _, _, _, _, _, l}:
      l

# The 4 bits of suit i in a packed word.
def nib(+x: U32, +i: U32) -> U32:
  ((x >> U32.to_nat((i * 4 : U32))) .&. 15 : U32)

# The owners of the top 3 cards of suit i, or of all of them if it has fewer, if the
# pattern has the suit.
def tt.top(+i: U32, +key: TtKey, +pat: U32) -> U32:
  +l = nib(key.lens(key), i)
  R.sel(U32.is_zero(((pat >> U32.to_nat(i)) .&. 1 : U32)), 0, (key.own(i, key) >> U32.to_nat(((U32.max(l, 3) - 3) * 2 : U32)) : U32))

# The first slot of the bucket of a key with a pattern, where mask is the number of
# buckets less one. The first 16 buckets' worth of slots hold the memory and the
# statistics.
def tt.bucket(+key: TtKey, +mask: U32, +pat: U32) -> U32:
  +a = ((key.k0(key) * 2654435761) .^. (key.k1(key) * 2246822519) .^. (pat * 40503) : U32)
  +b = ((((((a * 31) .^. tt.top(0, key, pat)) * 2654435761) .^. tt.top(1, key, pat)) * 2246822519) .^. (tt.top(2, key, pat) * 3266489917) .^. (tt.top(3, key, pat) * 668265263) : U32)
  +h = ((b .^. (b >> 15n)) .&. mask : U32)
  (R.sel(U32.is_lt(h, 16), (h + 16 : U32), h) * 64 : U32)

# Whether suit i, with w of its l cards mattering, goes in the pattern.
def pat.suit(+w: U32, +l: U32, +i: U32) -> U32:
  (Bool.to_u32(U32.is_ge(w, U32.min(l, 3)) && U32.is_ne(l, 0)) << U32.to_nat(i) : U32)

# The pattern of an entry.
def tt.pattern(+ws: U32, +lens: U32) -> U32:
  (pat.suit(nib(ws, 0), nib(lens, 0), 0) .|. pat.suit(nib(ws, 1), nib(lens, 1), 1) .|. pat.suit(nib(ws, 2), nib(lens, 2), 2) .|. pat.suit(nib(ws, 3), nib(lens, 3), 3) : U32)

# Whether two owner words agree on the top w of their l cards.
def own.agree(+a: U32, +b: U32, +l: U32, +w: U32) -> Bool:
  U32.is_zero(((a .^. b) >> U32.to_nat(((l - w) * 2 : U32)) : U32))

def tt.read(go: Bool, m: Array<U32>, +i: U32) -> Array<U32> & U32:
  match go:
    case True{}:
      Array.get(U32, m, i)
    case False{}:
      (m, 0)

# Compares the owner words of an entry with the key, for suit i on, where p holds the
# one at slot at. Answers v if they all agree on the top cards that ws asks for, and
# 0 if not.
def tt.owners(k: Nat, ok: Bool, p: Array<U32> & U32, +at: U32, +i: U32, +key: TtKey, +ws: U32, +v: U32) -> Array<U32> & U32:
  match k ok:
    case _ False{}:
      match p:
        case (m, _):
          (m, 0)
    case 0n True{}:
      match p:
        case (m, _):
          (m, v)
    case 1n+q True{}:
      match p:
        case (m, +o):
          +same = own.agree(o, key.own(i, key), nib(key.lens(key), i), nib(ws, i))
          tt.owners(q, same, tt.read(same && U32.is_lt(i, 3), m, (at + 1 : U32)), (at + 1 : U32), (i + 1 : U32), key, ws, v)

# What an entry's bounds say about reaching need more tricks: 1 yes, 2 no, 0 nothing.
def tt.says(+b: U32, +need: U32) -> U32:
  R.sel(U32.is_ge((b >> 28n : U32), need), 1, R.sel(U32.is_lt(((b >> 24n) .&. 15 : U32), need), 2, 0))

def tt.probe.b(p: Array<U32> & U32, +i: U32, +key: TtKey, +need: U32) -> Array<U32> & U32:
  match p:
    case (m, +b):
      +says = tt.says(b, need)
      +ws = (b .&. 65535 : U32)
      tt.owners(4n, U32.is_ne(says, 0), tt.read(U32.is_ne(says, 0), m, (i + 3 : U32)), (i + 3 : U32), 0, key, ws, (says .|. (ws << 8n) : U32))

def tt.probe.k1.go(same: Bool, m: Array<U32>, +i: U32, +key: TtKey, +need: U32) -> Array<U32> & U32:
  match same:
    case True{}:
      tt.probe.b(Array.get(U32, m, (i + 2 : U32)), i, key, need)
    case False{}:
      (m, 0)

def tt.probe.k1(p: Array<U32> & U32, +i: U32, +key: TtKey, +need: U32) -> Array<U32> & U32:
  match p:
    case (m, +k):
      tt.probe.k1.go(U32.is_eq(k, key.k1(key)), m, i, key, need)

def tt.probe.k0.go(same: Bool, m: Array<U32>, +i: U32, +key: TtKey, +need: U32) -> Array<U32> & U32:
  match same:
    case True{}:
      tt.probe.k1(Array.get(U32, m, (i + 1 : U32)), i, key, need)
    case False{}:
      (m, 0)

def tt.probe.k0(p: Array<U32> & U32, +i: U32, +key: TtKey, +need: U32) -> Array<U32> & U32:
  match p:
    case (m, +k):
      tt.probe.k0.go(U32.is_eq(k, key.k0(key)), m, i, key, need)

def tt.probe.step(miss: Bool, m: Array<U32>, +i: U32, +v: U32, +key: TtKey, +need: U32) -> Array<U32> & U32:
  match miss:
    case True{}:
      tt.probe.k0(Array.get(U32, m, i), i, key, need)
    case False{}:
      (m, v)

def tt.probe.scan(n: Nat, p: Array<U32> & U32, +i: U32, +key: TtKey, +need: U32) -> Array<U32> & U32:
  match n:
    case 0n:
      p
    case 1n+q:
      match p:
        case (m, +v):
          tt.probe.scan(q, tt.probe.step(U32.is_zero(v), m, i, v, key, need), (i + 8 : U32), key, need)

def tt.probe.bucket(miss: Bool, m: Array<U32>, +v: U32, +i: U32, +key: TtKey, +need: U32) -> Array<U32> & U32:
  match miss:
    case True{}:
      tt.probe.scan(8n, (m, 0), i, key, need)
    case False{}:
      (m, v)

def tt.probe.try(go: Bool, m: Array<U32>, +v: U32, +pat: U32, +mask: U32, +key: TtKey, +need: U32) -> Array<U32> & U32:
  match go:
    case True{}:
      tt.probe.scan(8n, (m, v), tt.bucket(key, mask, pat), key, need)
    case False{}:
      (m, v)

# Tries each pattern left in dir, from the highest.
def tt.probe.pats(n: Nat, stop: Bool, p: Array<U32> & U32, +dir: U32, +mask: U32, +key: TtKey, +need: U32) -> Array<U32> & U32:
  match n stop:
    case 0n _:
      p
    case 1n+q True{}:
      p
    case 1n+q False{}:
      match p:
        case (m, +v):
          +pat = U32.log2(dir)
          +more = (dir .^. (1 << pat) : U32)
          tt.probe.pats(q, U32.is_zero(more), tt.probe.try(U32.is_zero(v), m, v, U32.from_nat(pat), mask, key, need), more, mask, key, need)

# A slot not yet written says nothing: bit 16 marks a directory word as written.
def dir.of(+d: U32) -> U32:
  R.sel(U32.is_zero(((d >> 16n) .&. 1 : U32)), 0, (d .&. 65535 : U32))

def tt.probe.dir(p: Array<U32> & U32, +mask: U32, +key: TtKey, +need: U32) -> Array<U32> & U32:
  match p:
    case (m, +d):
      tt.probe.pats(16n, U32.is_zero(dir.of(d)), (m, 0), dir.of(d), mask, key, need)

def tt.probe.go(p: Array<U32> & U32, +key: TtKey, +need: U32) -> Array<U32> & U32:
  match p:
    case (m, +mask):
      tt.probe.dir(Array.get(U32, m, (tt.bucket(key, mask, 0) + 15 : U32)), mask, key, need)

# Looks a position up: 0 if the table doesn't settle whether North-South reach need
# more tricks, and otherwise 1 for yes or 2 for no, with above that the number of top
# cards that matter in each suit.
def tt.probe(m: Array<U32>, +key: TtKey, +need: U32) -> Array<U32> & U32:
  tt.probe.go(Array.get(U32, m, tt.mask.slot()), key, need)

# The number of top cards in holding l, down to the lowest card of w.
def ws.suit(+w: U32, +l: U32) -> U32:
  R.sel(U32.is_zero(w), 0, C.bits.count((l .&. (0 - bit.low(w)) : U32)))

def ws.of(+w01: U32, +w23: U32, +l01: U32, +l23: U32) -> U32:
  (ws.suit((w01 >> 16n : U32), (l01 >> 16n : U32)) .|. (ws.suit((w01 .&. 65535 : U32), (l01 .&. 65535 : U32)) << 4n) .|. (ws.suit((w23 >> 16n : U32), (l23 >> 16n : U32)) << 8n) .|. (ws.suit((w23 .&. 65535 : U32), (l23 .&. 65535 : U32)) << 12n) : U32)

# A store: first look for an entry with the same cards that matter, and tighten its
# bounds. Failing that, replace the next entry of the bucket in turn.
def tt.find.b.go(+same: Bool, m: Array<U32>, +i: U32, +key: TtKey, +ws: U32) -> Array<U32> & U32:
  tt.owners(4n, same, tt.read(same, m, (i + 3 : U32)), (i + 3 : U32), 0, key, ws, i)

def tt.find.b(p: Array<U32> & U32, +i: U32, +key: TtKey, +ws: U32) -> Array<U32> & U32:
  match p:
    case (m, +b):
      tt.find.b.go(U32.is_eq((b .&. 65535 : U32), ws), m, i, key, ws)

def tt.find.k1.go(same: Bool, m: Array<U32>, +i: U32, +key: TtKey, +ws: U32) -> Array<U32> & U32:
  match same:
    case True{}:
      tt.find.b(Array.get(U32, m, (i + 2 : U32)), i, key, ws)
    case False{}:
      (m, 0)

def tt.find.k1(p: Array<U32> & U32, +i: U32, +key: TtKey, +ws: U32) -> Array<U32> & U32:
  match p:
    case (m, +k):
      tt.find.k1.go(U32.is_eq(k, key.k1(key)), m, i, key, ws)

def tt.find.k0.go(same: Bool, m: Array<U32>, +i: U32, +key: TtKey, +ws: U32) -> Array<U32> & U32:
  match same:
    case True{}:
      tt.find.k1(Array.get(U32, m, (i + 1 : U32)), i, key, ws)
    case False{}:
      (m, 0)

def tt.find.k0(p: Array<U32> & U32, +i: U32, +key: TtKey, +ws: U32) -> Array<U32> & U32:
  match p:
    case (m, +k):
      tt.find.k0.go(U32.is_eq(k, key.k0(key)), m, i, key, ws)

def tt.find.step(miss: Bool, m: Array<U32>, +i: U32, +v: U32, +key: TtKey, +ws: U32) -> Array<U32> & U32:
  match miss:
    case True{}:
      tt.find.k0(Array.get(U32, m, i), i, key, ws)
    case False{}:
      (m, v)

def tt.find.scan(n: Nat, p: Array<U32> & U32, +i: U32, +key: TtKey, +ws: U32) -> Array<U32> & U32:
  match n:
    case 0n:
      p
    case 1n+q:
      match p:
        case (m, +v):
          tt.find.scan(q, tt.find.step(U32.is_zero(v), m, i, v, key, ws), (i + 8 : U32), key, ws)

# The bounds word after learning ok about need more tricks, from the word before.
def bounds.word(ok: Bool, +lo: U32, +hi: U32, +need: U32, +ws: U32) -> U32:
  match ok:
    case True{}:
      ((U32.max(lo, need) << 28n) .|. (hi << 24n) .|. ws : U32)
    case False{}:
      ((lo << 28n) .|. (U32.min(hi, (need - 1 : U32)) << 24n) .|. ws : U32)

def tt.tighten(p: Array<U32> & U32, +i: U32, ok: Bool, +need: U32, +ws: U32) -> Array<U32>:
  match p:
    case (m, +b):
      Array.set(U32, m, (i + 2 : U32), bounds.word(ok, (b >> 28n : U32), ((b >> 24n) .&. 15 : U32), need, ws))

def tt.write(p: Array<U32> & U32, +base: U32, +key: TtKey, ok: Bool, +need: U32, +left: U32, +ws: U32) -> Array<U32>:
  match p:
    case (m, +n):
      +i = (base + ((n .&. 7) * 8) : U32)
      Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, m, (base + 7 : U32), (n + 1 : U32)),
        i, key.k0(key)), (i + 1 : U32), key.k1(key)), (i + 2 : U32), bounds.word(ok, 0, left, need, ws)),
        (i + 3 : U32), key.own(0, key)), (i + 4 : U32), key.own(1, key)), (i + 5 : U32), key.own(2, key)), (i + 6 : U32), key.own(3, key))

def tt.store.go(found: Bool, m: Array<U32>, +at: U32, +base: U32, +key: TtKey, ok: Bool, +need: U32, +left: U32, +ws: U32) -> Array<U32>:
  match found:
    case True{}:
      tt.tighten(Array.get(U32, m, (at + 2 : U32)), at, ok, need, ws)
    case False{}:
      tt.write(Array.get(U32, m, (base + 7 : U32)), base, key, ok, need, left, ws)

def tt.store.at(p: Array<U32> & U32, +base: U32, +key: TtKey, ok: Bool, +need: U32, +left: U32, +ws: U32) -> Array<U32>:
  match p:
    case (m, +at):
      tt.store.go(U32.is_ne(at, 0), m, at, base, key, ok, need, left, ws)

# Marks a pattern in the directory, and starts a scan with nothing found.
def tt.dir.add(p: Array<U32> & U32, +i: U32, +pat: U32) -> Array<U32> & U32:
  match p:
    case (m, +d):
      (Array.set(U32, m, i, (dir.of(d) .|. 65536 .|. (1 << U32.to_nat(pat)) : U32)), 0)

def tt.store.mask(p: Array<U32> & U32, +key: TtKey, ok: Bool, +need: U32, +left: U32, +ws: U32) -> Array<U32>:
  match p:
    case (m, +mask):
      +pat = tt.pattern(ws, key.lens(key))
      +base = tt.bucket(key, mask, pat)
      tt.store.at(tt.find.scan(8n, tt.dir.add(Array.get(U32, m, (tt.bucket(key, mask, 0) + 15 : U32)), (tt.bucket(key, mask, 0) + 15 : U32), pat), base, key, ws), base, key, ok, need, left, ws)

# Stores what a search found, if go says to.
def tt.save(go: Bool, m: Array<U32>, +key: TtKey, ok: Bool, +need: U32, +left: U32, +w01: U32, +w23: U32, +l01: U32, +l23: U32) -> Array<U32>:
  match go:
    case True{}:
      tt.store.mask(Array.get(U32, m, tt.mask.slot()), key, ok, need, left, ws.of(w01, w23, l01, l23))
    case False{}:
      m

# The kth of the top cards in holding l, counting from 1, or nothing for k = 0.
def kth.go(k: Nat, +l: U32) -> U32:
  match k:
    case 0n:
      bit.top.or0(l)
    case 1n+p:
      kth.go(p, (l .^. bit.top.or0(l) : U32))

def kth(k: Nat, +l: U32) -> U32:
  match k:
    case 0n:
      0
    case 1n+p:
      kth.go(p, l)

# The winning ranks of a table entry, in a position it matches: the lowest card that
# matters in each suit, which stands for the ones above it.
def ranks.of.ws(+ws: U32, +l01: U32, +l23: U32) -> Ranks:
  Ranks{
    ((kth(U32.to_nat(nib(ws, 0)), (l01 >> 16n : U32)) << 16n) .|. kth(U32.to_nat(nib(ws, 1)), (l01 .&. 65535 : U32)) : U32),
    ((kth(U32.to_nat(nib(ws, 2)), (l23 >> 16n : U32)) << 16n) .|. kth(U32.to_nat(nib(ws, 3)), (l23 .&. 65535 : U32)) : U32)}

# ---------------------------------------------------------------------------
# Going into a node

# A Res with no moves, whose memo is slot i of the memory.
def peek.go(ok: Bool, n: Nat, pair: Array<U32> & U32, moves: Moves) -> Res:
  match pair:
    case (m, memo):
      Res{ok, n, m, memo, moves, 0, 0}

def peek(ok: Bool, n: Nat, m: Array<U32>, +i: U32) -> Res:
  peek.go(ok, n, Array.get(U32, m, i), MNil{})

def peek.moves(ok: Bool, n: Nat, m: Array<U32>, +i: U32, moves: Moves) -> Res:
  peek.go(ok, n, Array.get(U32, m, i), moves)

def peek.keep(ok: Bool, n: Nat, pair: Array<U32> & U32, +a: U32, +b: U32) -> Res:
  match pair:
    case (m, memo):
      Res{ok, n, m, memo, MNil{}, a, b}

# An answer that needs no moves, resting on these ranks.
def settled(ok: Bool, n: Nat, m: Array<U32>, ranks: Ranks) -> Res:
  match ranks:
    case Ranks{+a, +b}:
      Res{ok, n, m, 0, MNil{}, (a .|. (1 << 31n) : U32), b}

def node.open(~st: @+t:U32 -> @m:Array<U32> -> @+pos:R.Pos -> @+code:U32 -> @+l01:U32 -> @+l23:U32 -> Array<U32>, +t: U32, +child: R.Pos, +c01: U32, +c23: U32, +memo: U32, +here: U32, +ns: Bool, n: Nat, m: Array<U32>) -> Res:
  peek.moves(Bool.not(ns), 1n+n, st(t, m, child, 0, c01, c23), (here - 1 : U32), gen(t, child, c01, c23, memo, here))

def node.table.hit(~st: @+t:U32 -> @m:Array<U32> -> @+pos:R.Pos -> @+code:U32 -> @+l01:U32 -> @+l23:U32 -> Array<U32>, miss: Bool, +v: U32, +t: U32, +child: R.Pos, +c01: U32, +c23: U32, +memo: U32, +here: U32, +ns: Bool, n: Nat, m: Array<U32>) -> Res:
  match miss:
    case True{}:
      node.open(~st, t, child, c01, c23, memo, here, ns, n, m)
    case False{}:
      +ans = (v .&. 3 : U32)
      settled(U32.is_eq(ans, 1), 1n+n, st(t, m, child, (ans + why.table() : U32), c01, c23), ranks.of.ws((v >> 8n : U32), c01, c23))

def node.table(~st: @+t:U32 -> @m:Array<U32> -> @+pos:R.Pos -> @+code:U32 -> @+l01:U32 -> @+l23:U32 -> Array<U32>, p: Array<U32> & U32, +t: U32, +child: R.Pos, +c01: U32, +c23: U32, +memo: U32, +here: U32, +ns: Bool, n: Nat) -> Res:
  match p:
    case (m, +v):
      node.table.hit(~st, U32.is_zero(v), v, t, child, c01, c23, memo, here, ns, n, m)

def node.try(~st: @+t:U32 -> @m:Array<U32> -> @+pos:R.Pos -> @+code:U32 -> @+l01:U32 -> @+l23:U32 -> Array<U32>, use: Bool, +key: TtKey, +need: U32, +t: U32, +child: R.Pos, +c01: U32, +c23: U32, +memo: U32, +here: U32, +ns: Bool, n: Nat, m: Array<U32>) -> Res:
  match use:
    case True{}:
      node.table(~st, tt.probe(m, key, need), t, child, c01, c23, memo, here, ns, n)
    case False{}:
      node.open(~st, t, child, c01, c23, memo, here, ns, n, m)

# How many top cards of a suit a quick trick count has to keep. c is what the suit
# adds to the count, and of that it only has to keep what the count can't spare,
# except that a suit used as the way across to partner keeps one.
def qk.keep(+c: U32, +slack: U32, +entry: Bool) -> U32:
  U32.max((c - U32.min(c, slack) : U32), Bool.to_u32(entry))

def qk.slack(+c: U32, +slack: U32) -> U32:
  (slack - U32.min(c, slack) : U32)

# What a side suit adds to the count: it mirrors quick.suit.
def qk.adds(+m: U32, +p: U32, +a: U32, +b: U32, +ha1: Bool, +hb1: Bool, +ha2: Bool, +hb2: Bool, +across: Bool) -> U32:
  +all = (m .|. p .|. a .|. b : U32)
  +la = C.bits.count(a)
  +lb = C.bits.count(b)
  (safe(run(m, all), ha1, la, hb1, lb) + R.sel(across, safe(run(p, all), ha2, la, hb2, lb), 0) : U32)

def qk.way(+m: U32, +p: U32, +a: U32, +b: U32, +ha1: Bool, +hb1: Bool) -> Bool:
  U32.is_ne(m, 0) && U32.is_ne(safe(run(p, (m .|. p .|. a .|. b : U32)), ha1, C.bits.count(a), hb1, C.bits.count(b)), 0)

def qk.top(+k: U32, +all: U32) -> U32:
  kth(U32.to_nat(k), all)

# The cards a quick trick count of at least need rests on. Given the same lengths, the
# count only rises with the top cards it counts. So each suit has to keep only as many
# of its top cards as the count can't do without, the rest of the suit standing for
# nothing. Trumps stay whole if the opponents have any, as they also decide which suits
# are safe. If no opponent has a trump and the longer trump hand is enough, lengths
# alone do it.
def quick.tight.go(+s: Nat, +need: U32, +m0: U32, +m1: U32, +m2: U32, +m3: U32, +p0: U32, +p1: U32, +p2: U32, +p3: U32, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +b0: U32, +b1: U32, +b2: U32, +b3: U32) -> Ranks:
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
  +t0 = Nat.is_eq(s, 0n)
  +t1 = Nat.is_eq(s, 1n)
  +t2 = Nat.is_eq(s, 2n)
  +t3 = Nat.is_eq(s, 3n)
  +w0 = Bool.not(t0) && qk.way(m0, p0, a0, b0, ha1, hb1)
  +w1 = Bool.not(t1) && qk.way(m1, p1, a1, b1, ha1, hb1)
  +w2 = Bool.not(t2) && qk.way(m2, p2, a2, b2, ha1, hb1)
  +w3 = Bool.not(t3) && qk.way(m3, p3, a3, b3, ha1, hb1)
  +viat = U32.is_ne(tp, 0) && U32.is_ne(mt, 0)
  +across = viat || w0 || w1 || w2 || w3
  # The one suit that stays as the way across, if trumps aren't it.
  +e0 = Bool.not(viat) && w0
  +e1 = Bool.not(viat) && Bool.not(w0) && w1
  +e2 = Bool.not(viat) && Bool.not(w0) && Bool.not(w1) && w2
  +e3 = Bool.not(viat) && Bool.not(w0) && Bool.not(w1) && Bool.not(w2) && w3
  +c0 = R.sel(t0, 0, qk.adds(m0, p0, a0, b0, ha1, hb1, ha2, hb2, across))
  +c1 = R.sel(t1, 0, qk.adds(m1, p1, a1, b1, ha1, hb1, ha2, hb2, across))
  +c2 = R.sel(t2, 0, qk.adds(m2, p2, a2, b2, ha1, hb1, ha2, hb2, across))
  +c3 = R.sel(t3, 0, qk.adds(m3, p3, a3, b3, ha1, hb1, ha2, hb2, across))
  +total = (tl + R.sel(across, tp, 0) + c0 + c1 + c2 + c3 : U32)
  +s0 = (total - U32.min(total, need) : U32)
  +s1 = qk.slack(c0, s0)
  +s2 = qk.slack(c1, s1)
  +s3 = qk.slack(c2, s2)
  +s4 = qk.slack(c3, s3)
  +clear = U32.is_zero((at .|. bt : U32))
  +tm = R.sel(clear, qk.top(qk.keep((tl + R.sel(across, tp, 0) : U32), s4, viat), allt), top.run((mt .|. pt : U32), allt))
  +r0 = R.sel(t0, tm, qk.top(qk.keep(c0, s0, e0), (m0 .|. p0 .|. a0 .|. b0 : U32)))
  +r1 = R.sel(t1, tm, qk.top(qk.keep(c1, s1, e1), (m1 .|. p1 .|. a1 .|. b1 : U32)))
  +r2 = R.sel(t2, tm, qk.top(qk.keep(c2, s2, e2), (m2 .|. p2 .|. a2 .|. b2 : U32)))
  +r3 = R.sel(t3, tm, qk.top(qk.keep(c3, s3, e3), (m3 .|. p3 .|. a3 .|. b3 : U32)))
  +longer = U32.is_zero((at .|. bt : U32)) && U32.is_ge(U32.max(C.bits.count(mt), C.bits.count(pt)), need)
  ranks.sel(longer, ranks.none(), Ranks{((r0 << 16n) .|. r1 : U32), ((r2 << 16n) .|. r3 : U32)})

def quick.tight.hands(+t: U32, +seat: U32, +need: U32, +n01: U32, +n23: U32, +e01: U32, +e23: U32, +s01: U32, +s23: U32, +w01: U32, +w23: U32) -> Ranks:
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
  quick.tight.go(U32.to_nat(t), need, (m01 >> 16n : U32), (m01 .&. 65535 : U32), (m23 >> 16n : U32), (m23 .&. 65535 : U32), (p01 >> 16n : U32), (p01 .&. 65535 : U32), (p23 >> 16n : U32), (p23 .&. 65535 : U32), (a01 >> 16n : U32), (a01 .&. 65535 : U32), (a23 >> 16n : U32), (a23 .&. 65535 : U32), (b01 >> 16n : U32), (b01 .&. 65535 : U32), (b23 >> 16n : U32), (b23 .&. 65535 : U32))

# need is what North-South have to reach. The side on lead is short of it by that, or
# if it is East-West, they have to stop it, by taking all but need - 1 of what is left.
def quick.tight(+t: U32, pos: R.Pos, +need: U32, +left: U32) -> Ranks:
  match pos:
    case R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, +tr, _}:
      +seat = R.trick.seat(tr)
      quick.tight.hands(t, seat, R.sel(U32.is_zero((seat .&. 1 : U32)), need, (left - need + 1 : U32)), n01, n23, e01, e23, s01, s23, w01, w23)

# 1 if the leader, holding m of a suit, has a suit whose top card his side holds.
def lead.top(+m: U32, +l: U32, +o: U32) -> U32:
  Bool.to_u32(U32.is_ne(m, 0) && U32.is_zero((o .&. bit.top.or0(l) : U32)))

# The opponents' hold on a suit at no trumps: the top card, if it is theirs and isn't
# alone in the suit. If the side's top card were lower, it would only make it easier
# to claim a trick for them, and lengths already say a card is alone.
def opp.top(+l: U32, +o: U32) -> U32:
  +top = bit.top.or0(l)
  R.sel(U32.is_ne((o .&. top : U32), 0) && U32.is_ne(l, top), top, 0)

# The cards later tricks rest on. At no trumps, if the leader can't keep the lead, only
# the top card of each suit he has matters. Otherwise it is the opponents' top cards.
# With trumps and with the side on lead out of them, only lengths matter. If one trick
# is enough and the opponents hold the top trump, it alone matters.
def later.tight.go(+t: U32, +wanted: U32, +m01: U32, +m23: U32, +o01: U32, +o23: U32, +l01: U32, +l23: U32) -> Ranks:
  +st = U32.to_nat(t)
  +any = (lead.top((m01 >> 16n : U32), (l01 >> 16n : U32), (o01 >> 16n : U32)) .|. lead.top((m01 .&. 65535 : U32), (l01 .&. 65535 : U32), (o01 .&. 65535 : U32)) .|. lead.top((m23 >> 16n : U32), (l23 >> 16n : U32), (o23 >> 16n : U32)) .|. lead.top((m23 .&. 65535 : U32), (l23 .&. 65535 : U32), (o23 .&. 65535 : U32)) : U32)
  +tm = R.suit.mask(st, l01, l23)
  +ot = R.suit.mask(st, o01, o23)
  +side = (tm .^. ot : U32)
  +top = bit.top.or0(tm)
  +one = U32.is_le(wanted, 1) && U32.is_ne((ot .&. top : U32), 0)
  ranks.sel(U32.is_eq(t, 4),
    ranks.sel(U32.is_zero(any),
      Ranks{
        ((R.sel(U32.is_zero((m01 >> 16n : U32)), 0, bit.top.or0((l01 >> 16n : U32))) << 16n) .|. R.sel(U32.is_zero((m01 .&. 65535 : U32)), 0, bit.top.or0((l01 .&. 65535 : U32))) : U32),
        ((R.sel(U32.is_zero((m23 >> 16n : U32)), 0, bit.top.or0((l23 >> 16n : U32))) << 16n) .|. R.sel(U32.is_zero((m23 .&. 65535 : U32)), 0, bit.top.or0((l23 .&. 65535 : U32))) : U32)},
      Ranks{
        ((opp.top((l01 >> 16n : U32), (o01 >> 16n : U32)) << 16n) .|. opp.top((l01 .&. 65535 : U32), (o01 .&. 65535 : U32)) : U32),
        ((opp.top((l23 >> 16n : U32), (o23 >> 16n : U32)) << 16n) .|. opp.top((l23 .&. 65535 : U32), (o23 .&. 65535 : U32)) : U32)}),
    ranks.sel(U32.is_zero(side), ranks.none(), ranks.sel(one, ranks.of(t, top), later.ranks(t, l01, l23))))

def later.tight(+t: U32, pos: R.Pos, +need: U32, +left: U32) -> Ranks:
  match pos:
    case R.Pos{+n01, +n23, +e01, +e23, +s01, +s23, +w01, +w23, +tr, _}:
      +seat = R.trick.seat(tr)
      +i = U32.to_nat(seat)
      +ns = U32.is_zero((seat .&. 1 : U32))
      later.tight.go(t, R.sel(ns, (left - need + 1 : U32), need), R.pick(i, n01, e01, s01, w01), R.pick(i, n23, e23, s23, w23),
        R.sel(ns, (e01 .|. w01 : U32), (n01 .|. s01 : U32)), R.sel(ns, (e23 .|. w23 : U32), (n23 .|. s23 : U32)),
        (n01 .|. e01 .|. s01 .|. w01 : U32), (n23 .|. e23 .|. s23 .|. w23 : U32))

def after.or.cut(why: Nat, +t: U32, +pos: R.Pos, +l01: U32, +l23: U32, +need: U32, +left: U32) -> Ranks:
  match why:
    case 2n:
      quick.tight(t, pos, need, left)
    case 3n:
      later.tight(t, pos, need, left)
    case 4n:
      after.ranks(t, pos, l01, l23)
    case _:
      cut.ranks(why, t, pos)

# Enters a node: a cut settles it, or the table does, or else it gets its moves.
def node(~st: @+t:U32 -> @m:Array<U32> -> @+pos:R.Pos -> @+code:U32 -> @+l01:U32 -> @+l23:U32 -> Array<U32>, open: Bool, +code: U32, use: Bool, +key: TtKey, +need: U32, +t: U32, +child: R.Pos, +c01: U32, +c23: U32, +memo: U32, +here: U32, +ns: Bool, n: Nat, m: Array<U32>) -> Res:
  match open:
    case True{}:
      node.try(~st, use, key, need, t, child, c01, c23, memo, here, ns, n, m)
    case False{}:
      settled(enter.ok(code, ns), 1n+n, st(t, m, child, code, c01, c23), after.or.cut(U32.to_nat((code >> 2n : U32)), t, child, c01, c23, need, (here >> 2n : U32)))

# The small card filter. A move that didn't settle a node rests on no card below the
# lowest of the ranks so far in its suit. So if a card below that has been tried, and
# this one is below it too, this one comes out the same and isn't worth trying.
def small.mask(+c: U32, +x01: U32, +x23: U32) -> U32:
  R.suit.mask(U32.to_nat(C.card.suit(c)), x01, x23)

def small.skip(+c: U32, +x01: U32, +x23: U32, +a01: U32, +a23: U32) -> Bool:
  +w = small.mask(c, (a01 .&. 2147483647 : U32), a23)
  +low = R.sel(U32.is_zero(w), 8192, bit.low(w))
  U32.is_lt(C.card.bit(c), low) && U32.is_ne((small.mask(c, x01, x23) .&. (low - 1) : U32), 0)

# The set of cards tried: first says whether this is the word of suits 0 and 1.
def tried.add(+first: Bool, +c: U32, +x: U32) -> U32:
  +s = C.card.suit(c)
  +b = C.card.bit(c)
  (x .|. R.sel(first, R.sel(U32.is_eq(s, 0), (b << 16n : U32), R.sel(U32.is_eq(s, 1), b, 0)), R.sel(U32.is_eq(s, 2), (b << 16n : U32), R.sel(U32.is_eq(s, 3), b, 0))) : U32)

# Enters a child, unless the small card filter drops it. pns says who chooses at the
# parent, and an answer that doesn't settle the parent goes on to its next move. Bits
# 30 and 31 of its ranks say this child wasn't tried.
def node.in(~st: @+t:U32 -> @m:Array<U32> -> @+pos:R.Pos -> @+code:U32 -> @+l01:U32 -> @+l23:U32 -> Array<U32>, skip: Bool, +pns: Bool, +t: U32, +target: U32, +child: R.Pos, +c01: U32, +c23: U32, +memo: U32, +here: U32, n: Nat, m: Array<U32>) -> Res:
  match skip:
    case True{}:
      Res{Bool.not(pns), n, m, 0, MNil{}, (3 << 30n : U32), 0}
    case False{}:
      +played = R.trick.played(R.pos.trick(child))
      +won = R.pos.won(child)
      +code = cut.at(U32.to_nat(played), t, child, won, here, target)
      +left = (here >> 2n : U32)
      +use = U32.is_zero(played) && U32.is_zero(code) && tt.on(left)
      node(~st, U32.is_zero(code), code, use, tt.key(use, t, left, child), (target - won : U32), t, child, c01, c23, memo, here, R.pos.ns(child), n, m)

# ---------------------------------------------------------------------------
# Coming out of a node

def back.go(ok: Bool, n: Nat, m: Array<U32>, +here: U32, +a: U32, +b: U32, ranks: Ranks) -> Res:
  match ranks:
    case Ranks{+x, +y}:
      peek.keep(ok, n, Array.get(U32, m, here), (a .|. x : U32), (b .|. y : U32))

# After the fourth card of a trick: stores the child's answer if it was searched for,
# and adds what the trick itself rests on. Nothing about the child is kept across the
# call, since most children aren't stored, so it is worked out again here.
def back.trick(+flag: U32, +ok: Bool, n: Nat, m: Array<U32>, +a: U32, +b: U32, +here: U32, +c: U32, +t: U32, +target: U32, +l01: U32, +l23: U32, +pos: R.Pos) -> Res:
  +child = R.play(t, pos, c)
  +left = (here >> 2n : U32)
  +save = U32.is_zero(flag) && tt.on(left)
  +c01 = R.pos.live01(child)
  +c23 = R.pos.live23(child)
  back.go(ok, n, tt.save(save, m, tt.key(save, t, left, child), ok, (target - R.pos.won(child) : U32), left, a, b, c01, c23), here, a, b, trick.ranks(U32.is_ne(flag, 3), t, pos, c, child, l01, l23))

# A child's answer as its parent takes it, with the memo for the next child.
def back.at(last: Bool, +flag: U32, ok: Bool, n: Nat, m: Array<U32>, +a: U32, +b: U32, +here: U32, +c: U32, +t: U32, +target: U32, +l01: U32, +l23: U32, +pos: R.Pos) -> Res:
  match last:
    case True{}:
      back.trick(flag, ok, n, m, a, b, here, c, t, target, l01, l23, pos)
    case False{}:
      peek.keep(ok, n, Array.get(U32, m, here), a, b)

def back(r: Res, +here: U32, +c: U32, +t: U32, +target: U32, +l01: U32, +l23: U32, +pos: R.Pos) -> Res:
  match r:
    case Res{ok, n, m, _, _, +w01, +w23}:
      back.at(U32.is_eq(R.trick.played(R.pos.trick(pos)), 3), (w01 >> 30n : U32), ok, n, m, (w01 .&. 1073741823 : U32), w23, here, c, t, target, l01, l23, pos)

# ---------------------------------------------------------------------------
# The search

# Tries the moves ms of a position with d cards left. r is the answer so far: a
# call cannot be destructured in place, so a child's answer rides into the next
# sibling as an argument. The answer settles a node once it says true for
# North-South or false for East-West, and otherwise the node goes on to the next
# move; with no moves left, the answer stands. A move that settles the node goes
# into the memory, at slot, and last is that move.
#
# A node that settles rests on the ranks of the child that settled it. One that
# doesn't rests on the ranks of all its children: a01 and a23 hold those of the
# children before the last.
#
# A child has one card fewer, and a sibling has one move fewer with the same d. The
# table is read going into a child, which also decides its moves, and a call can't
# be destructured in place. So a child starts with first as 1n and takes its moves
# from r.
def search(~st: @+t:U32 -> @m:Array<U32> -> @+pos:R.Pos -> @+code:U32 -> @+l01:U32 -> @+l23:U32 -> Array<U32>, +d: Nat, first: Nat, ms: Moves, ns: Bool, r: Res, +slot: U32, +last: U32, +a01: U32, +a23: U32, +x01: U32, +x23: U32, +t: U32, +target: U32, +l01: U32, +l23: U32, +pos: R.Pos) -> Res:
  match d first ms ns r:
    case 0n _ _ _ x:
      x
    case 1n+p 1n+q _ _ Res{ok, n, m, memo, moves, +w01, +w23}:
      search(~st, 1n+p, q, moves, ns, Res{ok, n, m, memo, MNil{}, w01, w23}, slot, last, a01, a23, x01, x23, t, target, l01, l23, pos)
    case 1n+p 0n _ True{} Res{True{}, n, m, _, _, +w01, +w23}:
      Res{True{}, n, Array.set(U32, m, slot, last), 0, MNil{}, w01, w23}
    case 1n+p 0n _ False{} Res{False{}, n, m, _, _, +w01, +w23}:
      Res{False{}, n, Array.set(U32, m, slot, last), 0, MNil{}, w01, w23}
    case 1n+p 0n MNil{} _ Res{ok, n, m, _, _, +w01, +w23}:
      Res{ok, n, m, 0, MNil{}, (a01 .|. w01 : U32), (a23 .|. w23 : U32)}
    case 1n+p 0n MCon{+c, rest} True{} Res{False{}, n, m, +memo, _, +w01, +w23}:
      +child = R.play(t, pos, c)
      +bound = U32.is_zero(R.trick.played(R.pos.trick(child)))
      +c01 = live.at(bound, R.pos.live01(child), l01)
      +c23 = live.at(bound, R.pos.live23(child), l23)
      +here = U32.from_nat(p)
      search(~st, 1n+p, 0n, rest, True{},
        back(search(~st, p, 1n, MNil{}, R.pos.ns(child), node.in(~st, small.skip(c, x01, x23, (a01 .|. w01 : U32), (a23 .|. w23 : U32)), ns, t, target, child, c01, c23, memo, here, n, m), mem.none(), 0, 0, 0, 0, 0, t, target, c01, c23, child), here, c, t, target, l01, l23, pos),
        U32.from_nat(1n+p), c, (a01 .|. w01 : U32), (a23 .|. w23 : U32), tried.add(True{}, c, x01), tried.add(False{}, c, x23), t, target, l01, l23, pos)
    case 1n+p 0n MCon{+c, rest} False{} Res{True{}, n, m, +memo, _, +w01, +w23}:
      +child = R.play(t, pos, c)
      +bound = U32.is_zero(R.trick.played(R.pos.trick(child)))
      +c01 = live.at(bound, R.pos.live01(child), l01)
      +c23 = live.at(bound, R.pos.live23(child), l23)
      +here = U32.from_nat(p)
      search(~st, 1n+p, 0n, rest, False{},
        back(search(~st, p, 1n, MNil{}, R.pos.ns(child), node.in(~st, small.skip(c, x01, x23, (a01 .|. w01 : U32), (a23 .|. w23 : U32)), ns, t, target, child, c01, c23, memo, here, n, m), mem.none(), 0, 0, 0, 0, 0, t, target, c01, c23, child), here, c, t, target, l01, l23, pos),
        U32.from_nat(1n+p), c, (a01 .|. w01 : U32), (a23 .|. w23 : U32), tried.add(True{}, c, x01), tried.add(False{}, c, x23), t, target, l01, l23, pos)

# Runs one search from the start of a trick.
def ask.go(~st: @+t:U32 -> @m:Array<U32> -> @+pos:R.Pos -> @+code:U32 -> @+l01:U32 -> @+l23:U32 -> Array<U32>, +d: Nat, +t: U32, +pos: R.Pos, +target: U32, r: Res) -> Res:
  match r:
    case Res{_, n, m, +memo, _, _, _}:
      +ns = R.pos.ns(pos)
      +l01 = R.pos.live01(pos)
      +l23 = R.pos.live23(pos)
      search(~st, d, 0n, gen(t, pos, l01, l23, memo, U32.from_nat(d)), ns, peek(Bool.not(ns), n, m, (U32.from_nat(d) - 1 : U32)), mem.none(), 0, 0, 0, 0, 0, t, target, l01, l23, pos)

# Runs one search, unless told there is nothing to ask.
def ask(~st: @+t:U32 -> @m:Array<U32> -> @+pos:R.Pos -> @+code:U32 -> @+l01:U32 -> @+l23:U32 -> Array<U32>, ~sa: @m:Array<U32> -> @+target:U32 -> Array<U32>, stop: Bool, +d: Nat, +t: U32, +pos: R.Pos, +target: U32, n: Nat, m: Array<U32>) -> Res:
  match stop:
    case True{}:
      Res{False{}, n, m, 0, MNil{}, 0, 0}
    case False{}:
      ask.go(~st, d, t, pos, target, peek(False{}, n, sa(m, target), U32.from_nat(d)))

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
def narrow(~st: @+t:U32 -> @m:Array<U32> -> @+pos:R.Pos -> @+code:U32 -> @+l01:U32 -> @+l23:U32 -> Array<U32>, ~sa: @m:Array<U32> -> @+target:U32 -> Array<U32>, fuel: Nat, done: Bool, r: Res, +target: U32, +d: Nat, +t: U32, +pos: R.Pos, +lo: U32, +hi: U32) -> Val:
  match fuel done r:
    case 0n _ Res{_, n, m, _, _, _, _}:
      Val{lo, n, m}
    case 1n+p True{} Res{_, n, m, _, _, _, _}:
      Val{lo, n, m}
    case 1n+p False{} Res{+ok, n, m, _, _, _, _}:
      +lo2 = driver.lo(ok, target, lo)
      +hi2 = driver.hi(ok, target, hi)
      +stop = U32.is_ge(lo2, hi2)
      +next = driver.next(ok, lo2, hi2)
      narrow(~st, ~sa, p, stop, ask(~st, ~sa, stop, d, t, pos, next, n, m), next, d, t, pos, lo2, hi2)

# The fewest tricks North-South are sure of at the start of a trick, from both as
# counts gives it, and the most they can still take. The target cuts don't run on
# the first card of a search, so without these the driver would search for answers
# that the counts already give. With no cards left the counts mean nothing.
def sure.both(+t: U32, +pos: R.Pos, +left: U32) -> U32:
  R.sel(U32.is_zero(left), 0, counts(t, pos, left))

def sure.lo(+pos: R.Pos, +both: U32) -> U32:
  (R.pos.won(pos) + R.sel(R.pos.ns(pos), (both .&. 255 : U32), (both >> 8n : U32)) : U32)

def sure.hi(+pos: R.Pos, +both: U32, +left: U32) -> U32:
  (R.pos.won(pos) + left - R.sel(R.pos.ns(pos), (both >> 8n : U32), (both .&. 255 : U32)) : U32)

# North-South's tricks from the start of a trick with d cards left, starting from
# a guess at the answer.
def solve(~st: @+t:U32 -> @m:Array<U32> -> @+pos:R.Pos -> @+code:U32 -> @+l01:U32 -> @+l23:U32 -> Array<U32>, ~sa: @m:Array<U32> -> @+target:U32 -> Array<U32>, +d: Nat, +t: U32, +pos: R.Pos, +guess: U32, n: Nat, m: Array<U32>) -> Val:
  +left = (U32.from_nat(d) >> 2n : U32)
  +both = sure.both(t, pos, left)
  +lo = sure.lo(pos, both)
  +hi = sure.hi(pos, both, left)
  +stop = U32.is_ge(lo, hi)
  +target = driver.first(guess, lo, hi)
  narrow(~st, ~sa, 14n, stop, ask(~st, ~sa, stop, d, t, pos, target, n, m), target, d, t, pos, lo, hi)

# The first guess for a strain: the middle of what isn't already sure. The result of
# another strain says little, since the trumps can change who has the long suit.
def guess.fresh(+t: U32, +pos: R.Pos, +left: U32) -> U32:
  +both = sure.both(t, pos, left)
  ((sure.lo(pos, both) + sure.hi(pos, both, left) + 1 : U32) / 2 : U32)

# ---------------------------------------------------------------------------
# The table

# A finished table with the memory array, which holds any statistics.
type Solved is Type:
  Solved{tricks: List<&2, U32>, nodes: Nat, mem: Array<U32>}

# Fills a strain's part of the table from its last entry to its first, so that it
# comes out in the order of B.table. r is the result for entry i + 1, and it feeds the
# guess for entry i: moving the lead by one seat rarely changes the result by much.
def table.go(~st: @+t:U32 -> @m:Array<U32> -> @+pos:R.Pos -> @+code:U32 -> @+l01:U32 -> @+l23:U32 -> Array<U32>, ~sa: @m:Array<U32> -> @+target:U32 -> Array<U32>, ~sb: @m:Array<U32> -> @+i:U32 -> Array<U32>, k: Nat, r: Val, +i: U32, +d: Nat, +left: U32, +deal: C.Deal, acc: List<&2, U32>) -> Solved:
  match k r:
    case 0n Val{+v, n, m}:
      Solved{B.table.entry(U32.is_zero(((i + 1) .&. 1 : U32)), left, v) <> acc, n, m}
    case 1n+p Val{+v, n, m}:
      +t = (i >> 2n : U32)
      +decl = (i .&. 3 : U32)
      +pos = R.pos.start(deal, ((decl + 1) .&. 3 : U32))
      table.go(~st, ~sa, ~sb, p, solve(~st, ~sa, d, t, pos, v, n, sb(m, i)), (i - 1 : U32), d, left, deal,
        B.table.entry(U32.is_zero(((i + 1) .&. 1 : U32)), left, v) <> acc)

# The 4 entries of one strain, as table.go leaves them, from the entry for West down.
def strain.run(~st: @+t:U32 -> @m:Array<U32> -> @+pos:R.Pos -> @+code:U32 -> @+l01:U32 -> @+l23:U32 -> Array<U32>, ~sa: @m:Array<U32> -> @+target:U32 -> Array<U32>, ~sb: @m:Array<U32> -> @+i:U32 -> Array<U32>, +t: U32, +deal: C.Deal, m: Array<U32>) -> Solved:
  +cards = B.deal.cards(deal)
  +d = U32.to_nat(cards)
  +left = (cards / 4 : U32)
  +i = (t * 4 + 3 : U32)
  +pos = R.pos.start(deal, 0)
  table.go(~st, ~sa, ~sb, 3n, solve(~st, ~sa, d, t, pos, guess.fresh(t, pos, left), 0n, sb(m, i)), (i - 1 : U32), d, left, deal, Nil{})

def done.table(r: Solved) -> B.Table:
  match r:
    case Solved{ts, n, _}:
      B.Table{ts, n}

# One strain's part of the table, with a transposition table of its own.
def strain.table(+t: U32, +deal: C.Deal) -> B.Table:
  +d = tt.depth((B.deal.cards(deal) / 4 : U32))
  done.table(strain.run(~(+t => m => +p => +c => +a => +b => m), ~(m => +x => m), ~(m => +x => m), t, deal, tt.ready(d, [mem.none() : U32^d])))

def table.join(a: B.Table, b: B.Table) -> B.Table:
  match a b:
    case B.Table{xs, +n} B.Table{ys, +k}:
      B.Table{List.append(&2, U32, xs, ys), Nat.add(n, k)}

# The double dummy table of a deal, as B.table gives it. Each strain is its own
# search with its own table, as an entry from one strain says nothing about another.
# So they can run on threads of their own: dd forks over them.
def table(+deal: C.Deal) -> B.Table:
  table.join(strain.table(0, deal), table.join(strain.table(1, deal), table.join(strain.table(2, deal), table.join(strain.table(3, deal), strain.table(4, deal)))))

# The counters of a table, slots 64 to 703 of the array, in order.
def stats.list(k: Nat, +i: U32, p: Array<U32> & U32, acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      acc
    case 1n+q:
      match p:
        case (m, v):
          stats.list(q, (i - 1 : U32), Array.get(U32, m, (i - 1 : U32)), v <> acc)

# A table with its statistics, as plain data.
type Report is Data:
  Report{tricks: List<&2, U32>, nodes: Nat, stats: List<&2, U32>}

def report.go(r: Solved) -> Report:
  match r:
    case Solved{ts, n, m}:
      Report{ts, n, stats.list(640n, 703, Array.get(U32, m, 703), Nil{})}

# Clears the counters, from slot i on, since the array starts as empty memory.
def stats.clear(k: Nat, +i: U32, m: Array<U32>) -> Array<U32>:
  match k:
    case 0n:
      m
    case 1n+p:
      stats.clear(p, (i + 1 : U32), Array.set(U32, m, i, 0))

def stats.sum(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs ys:
    case Con{+x, a} Con{+y, b}:
      (x + y : U32) <> stats.sum(a, b)
    case _ _:
      Nil{}

def report.join(a: Report, b: Report) -> Report:
  match a b:
    case Report{xs, +n, sx} Report{ys, +k, sy}:
      Report{List.append(&2, U32, xs, ys), Nat.add(n, k), stats.sum(sx, sy)}

def strain.report(+t: U32, +deal: C.Deal) -> Report:
  +d = tt.depth((B.deal.cards(deal) / 4 : U32))
  report.go(strain.run(~stat.node, ~stat.ask, ~stat.begin, t, deal, stats.clear(640n, 64, tt.ready(d, [mem.none() : U32^d]))))

# The same search, counting, with one strain after another. Each entry only writes to
# its own counters, so adding them up puts them together.
def table.report(+deal: C.Deal) -> Report:
  report.join(strain.report(0, deal), report.join(strain.report(1, deal), report.join(strain.report(2, deal), report.join(strain.report(3, deal), strain.report(4, deal)))))

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
