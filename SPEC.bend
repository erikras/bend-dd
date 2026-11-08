# SPEC.bend: plain statements of the rules, used by LAWS.bend.

import Base
import ./src/cards.bend as C
import ./src/pbn.bend as P
import ./src/rules.bend as R
import ./src/brute.bend as B
import ./src/search.bend as Z
import ./src/deal.bend as D

# ---------------------------------------------------------------------------
# PBN

# Whether a string is free of a separator, as a type: one proof per character.
def Free(+sep: Char, s: String) -> Type:
  match s:
    case SNil{}:
      Unit
    case SCon{c, t}:
      {Char.is_eq(c, sep) == False{} : Bool} & Free(sep, t)

# A holding whose printed form parses back to it.
def Good(+m: U32) -> Type:
  {P.suit.parse(P.suit.print(m)) == Some{m} : Maybe<&2, U32>}

def Good.hand(+h: C.Hand) -> Type:
  match h:
    case C.Hand{+s, +x, +d, +c}:
      Good(s) & Good(x) & Good(d) & Good(c)

def holding.ok.go(a: Maybe<&2, U32>, +m: U32) -> Bool:
  match a:
    case None{}:
      False{}
    case Some{x}:
      U32.is_eq(x, m)

def holding.ok(+m: U32) -> Bool:
  holding.ok.go(P.suit.parse(P.suit.print(m)), m)

# The exhaustive check, walking with U32.inc so it lines up with U32.from_nat.
def holdings.ok(n: Nat, +m: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(holding.ok(m), holdings.ok(p, U32.inc(m)))

# ---------------------------------------------------------------------------
# Tricks

# How a card ranks in a trick with trumps t once suit l has been led: any trump
# beats any card of the suit led, and any other card cannot win.
def power.go(trump: Bool, led: Bool, +r: U32) -> U32:
  match trump led:
    case True{} _:
      (r + 32 : U32)
    case False{} True{}:
      (r + 16 : U32)
    case False{} False{}:
      0

def power(+t: U32, +l: U32, +c: U32) -> U32:
  +s = C.card.suit(c)
  power.go(U32.is_eq(s, t), U32.is_eq(s, l), C.card.rank(c))

def bool.eq(a: Bool, b: Bool) -> Bool:
  Bool.not(Bool.xor(a, b))

# beats agrees with power, when best is winning a trick led in suit l (so it is
# either of suit l or a trump) and c is any other card. Equal powers mean the
# same card, which never happens, so the spec needs no tie-break.
def beats.ok(+t: U32, +l: U32, +best: U32, +c: U32) -> Bool:
  bool.eq(R.beats(t, best, c), U32.is_gt(power(t, l, c), power(t, l, best)))

# ---------------------------------------------------------------------------
# Legal plays

# Whether a list of cards is exactly holding m in suit s: every card is of suit
# s and in m, each one is lower than the one before (so none repeats), and they
# use up m.
def moves.exact(xs: List<&2, U32>, +s: U32, +prev: U32, +m: U32) -> Bool:
  match xs:
    case Nil{}:
      U32.is_eq(m, 0)
    case Con{+c, t}:
      +bit = C.card.bit(c)
      U32.is_eq(C.card.suit(c), s) && U32.is_lt(c, prev) && U32.is_ne((m .&. bit : U32), 0) && moves.exact(t, s, c, (m .^. bit : U32))

def moves.holding.ok(+s: U32, +m: U32) -> Bool:
  moves.exact(R.moves.suit(s, m, Nil{}), s, 1000, m)

def moves.holdings.ok(n: Nat, +s: U32, +m: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(moves.holding.ok(s, m), moves.holdings.ok(p, s, (m + 1 : U32)))

# ---------------------------------------------------------------------------
# Whole tricks

# Runs four cards through the trick word.
def trick.run(+t: U32, +leader: U32, +a: U32, +b: U32, +c: U32, +d: U32) -> U32:
  +t1 = R.trick.next(R.trick.start(leader), t, a)
  +t2 = R.trick.next(t1, t, b)
  +t3 = R.trick.next(t2, t, c)
  R.trick.next(t3, t, d)

# The position in the trick (0..3) of the card with the most power, where the
# earlier of two equal cards stays ahead.
def trick.top(+pa: U32, +pb: U32, +pc: U32, +pd: U32) -> U32:
  +ab = U32.max(pa, pb)
  +abc = U32.max(ab, pc)
  +i2 = R.sel(U32.is_gt(pb, pa), 1, 0)
  +i3 = R.sel(U32.is_gt(pc, ab), 2, i2)
  R.sel(U32.is_gt(pd, abc), 3, i3)

# The seat that wins a trick, directly from the rules of bridge.
def trick.winner(+t: U32, +leader: U32, +a: U32, +b: U32, +c: U32, +d: U32) -> U32:
  +l = C.card.suit(a)
  ((leader + trick.top(power(t, l, a), power(t, l, b), power(t, l, c), power(t, l, d))) .&. 3 : U32)

# The trick word must have moved to a new trick led by the winner.
def trick.ok(+t: U32, +leader: U32, +a: U32, +b: U32, +c: U32, +d: U32) -> Bool:
  +w = trick.run(t, leader, a, b, c, d)
  U32.is_eq(w, R.trick.start(trick.winner(t, leader, a, b, c, d)))

# The sample pool of cards a law walks: the ace and deuce of spades and hearts,
# and the ace of clubs.
def pool() -> List<&2, U32>:
  [C.card.make(0, 12), C.card.make(0, 0), C.card.make(1, 12), C.card.make(1, 0), C.card.make(3, 12)]

def walk.d(ds: List<&2, U32>, +t: U32, +leader: U32, +a: U32, +b: U32, +c: U32) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{+d, r}:
      Bool.and(trick.ok(t, leader, a, b, c, d), walk.d(r, t, leader, a, b, c))

def walk.c(cs: List<&2, U32>, +t: U32, +leader: U32, +a: U32, +b: U32) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+c, r}:
      Bool.and(walk.d(pool(), t, leader, a, b, c), walk.c(r, t, leader, a, b))

def walk.b(bs: List<&2, U32>, +t: U32, +leader: U32, +a: U32) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{+b, r}:
      Bool.and(walk.c(pool(), t, leader, a, b), walk.b(r, t, leader, a))

def walk.a(xs: List<&2, U32>, +t: U32, +leader: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+a, r}:
      Bool.and(walk.b(pool(), t, leader, a), walk.a(r, t, leader))

# ---------------------------------------------------------------------------
# beats, over every card

def beats.c.rank(n: Nat, +t: U32, +l: U32, +best: U32, +s: U32, +r: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(beats.ok(t, l, best, C.card.make(s, r)), beats.c.rank(p, t, l, best, s, (r + 1 : U32)))

def beats.c.suit(n: Nat, +t: U32, +l: U32, +best: U32, +s: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(beats.c.rank(13n, t, l, best, s, 0), beats.c.suit(p, t, l, best, (s + 1 : U32)))

def beats.best(n: Nat, +t: U32, +l: U32, +s: U32, +r: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(beats.c.suit(4n, t, l, C.card.make(s, r), 0), beats.best(p, t, l, s, (r + 1 : U32)))

# Best is any card of the suit led or, if there is a trump suit, any trump.
def beats.lead(n: Nat, +t: U32, +l: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(Bool.and(beats.best(13n, t, l, l, 0), beats.best(13n, t, l, t, 0)), beats.lead(p, t, (l + 1 : U32)))

def beats.all(n: Nat, +t: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(beats.lead(4n, t, 0), beats.all(p, (t + 1 : U32)))

# ---------------------------------------------------------------------------
# Card equivalence

# What a rank may look like. A card in the hand is in play, and k holds it only at
# the top of a run, so it is dropped only when the card in play just above it is
# also in the hand. Any other rank must stay out of k.
def tops.step.ok(in_m: Bool, in_live: Bool, in_k: Bool, run: Bool) -> Bool:
  match in_m in_live:
    case True{} True{}:
      bool.eq(in_k, Bool.not(run))
    case True{} False{}:
      False{}
    case False{} _:
      Bool.not(in_k)

# run says the last card in play above this rank was in the hand. A rank with no
# card in play leaves it alone, so gaps do not split a run.
def tops.step.run(in_m: Bool, in_live: Bool, run: Bool) -> Bool:
  match in_live:
    case True{}:
      in_m
    case False{}:
      run

def bit.in(+m: U32, +bit: U32) -> Bool:
  U32.is_ne((m .&. bit : U32), 0)

# Whether k is exactly the top card of each run of holding m, where a run is a
# stretch of cards of m with no other card in play between them. Walks the ranks
# from the ace down.
def tops.exact(n: Nat, +bit: U32, +m: U32, +live: U32, +k: U32, +run: Bool) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      +im = bit.in(m, bit)
      +il = bit.in(live, bit)
      Bool.and(tops.step.ok(im, il, bit.in(k, bit), run),
        tops.exact(p, (bit >> 1n : U32), m, live, k, tops.step.run(im, il, run)))

def tops.ok(+m: U32, +live: U32) -> Bool:
  tops.exact(13n, 4096, m, live, Z.tops(m, live), False{})

# Every way to split n ranks, from this bit up, into not in play, in play
# elsewhere, and in the hand.
def tops.walk(+n: Nat, +bit: U32, +m: U32, +live: U32) -> Bool:
  match n:
    case 0n:
      tops.ok(m, live)
    case 1n+p:
      +up = (bit << 1n : U32)
      Bool.and(tops.walk(p, up, m, live),
        Bool.and(tops.walk(p, up, m, (live .|. bit : U32)),
          tops.walk(p, up, (m .|. bit : U32), (live .|. bit : U32))))

# Every holding, with all 13 cards in play.
def tops.all(n: Nat, +m: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(tops.ok(m, 8191), tops.all(p, (m + 1 : U32)))

# ---------------------------------------------------------------------------
# Target cutoffs

def cut.claim(+code: U32, +v: U32, +target: U32) -> Bool:
  (U32.is_ne(code, 1) || U32.is_ge(v, target)) && (U32.is_ne(code, 2) || U32.is_lt(v, target))

# For each final result v from won to won + left: what the cut says about the
# target holds for v.
def cut.v(n: Nat, +v: U32, +won: U32, +left: U32, +target: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(cut.claim(Z.cut(won, left, target), v, target), cut.v(p, (v + 1 : U32), won, left, target))

def cut.targets(n: Nat, +target: U32, +won: U32, +left: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(cut.v(1n+U32.to_nat(left), won, won, left, target), cut.targets(p, (target + 1 : U32), won, left))

def cut.lefts(n: Nat, +left: U32, +won: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(cut.targets(15n, 0, won, left), cut.lefts(p, (left + 1 : U32), won))

# Every won and left with won + left at most 13, and every target from 0 to 14.
def cut.all(+n: Nat, +won: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(cut.lefts(1n+p, 0, won), cut.all(p, (won + 1 : U32)))

# ---------------------------------------------------------------------------
# The driver

# Z.narrow, with the search replaced by what it must answer when the true result
# is v: whether target is at most v.
def driver.run(fuel: Nat, done: Bool, +target: U32, +v: U32, +lo: U32, +hi: U32) -> U32:
  match fuel done:
    case 0n _:
      lo
    case 1n+p True{}:
      lo
    case 1n+p False{}:
      +ok = U32.is_le(target, v)
      +lo2 = Z.driver.lo(ok, target, lo)
      +hi2 = Z.driver.hi(ok, target, hi)
      driver.run(p, U32.is_ge(lo2, hi2), Z.driver.next(ok, lo2, hi2), v, lo2, hi2)

# Z.solve in the same way: the driver finds v with Z.solve's fuel.
def driver.ok(+g: U32, +v: U32, +lo: U32, +hi: U32) -> Bool:
  U32.is_eq(driver.run(14n, U32.is_ge(lo, hi), Z.driver.first(g, lo, hi), v, lo, hi), v)

def driver.guess(n: Nat, +g: U32, +v: U32, +lo: U32, +hi: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(driver.ok(g, v, lo, hi), driver.guess(p, (g + 1 : U32), v, lo, hi))

def driver.v(n: Nat, +v: U32, +lo: U32, +hi: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(driver.guess(14n, 0, v, lo, hi), driver.v(p, (v + 1 : U32), lo, hi))

def driver.hi(n: Nat, +width: U32, +lo: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(driver.v(1n+U32.to_nat(width), lo, lo, (lo + width : U32)), driver.hi(p, (width + 1 : U32), lo))

# Every lo <= v <= hi up to 13, and every guess from 0 to 13.
def driver.all(+n: Nat, +lo: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(driver.hi(1n+p, 0, lo), driver.all(p, (lo + 1 : U32)))

# ---------------------------------------------------------------------------
# Move generation

# Whether a list holds each card of these four holdings exactly once.
def gen.exact(xs: List<&2, U32>, +k0: U32, +k1: U32, +k2: U32, +k3: U32) -> Bool:
  match xs:
    case Nil{}:
      U32.is_zero((k0 .|. k1 .|. k2 .|. k3 : U32))
    case Con{+c, t}:
      +s = C.card.suit(c)
      +bit = C.card.bit(c)
      bit.in(R.pick(U32.to_nat(s), k0, k1, k2, k3), bit) &&
        gen.exact(t, (k0 .^. R.sel(U32.is_eq(s, 0), bit, 0) : U32), (k1 .^. R.sel(U32.is_eq(s, 1), bit, 0) : U32), (k2 .^. R.sel(U32.is_eq(s, 2), bit, 0) : U32), (k3 .^. R.sel(U32.is_eq(s, 3), bit, 0) : U32))

# The holding of suit s that may be played: all of it when free to play anything,
# otherwise only the suit led.
def legal(+free: Bool, +s: U32, +lead: U32, +m: U32) -> U32:
  R.sel(free || U32.is_eq(s, lead), m, 0)

# Whether the moves in a position are the top card of each run among the legal plays.
def gen.ok(+t: U32, pos: R.Pos, +l01: U32, +l23: U32, +d: U32) -> Bool:
  match pos:
    case R.Pos{+n01, +n23, +e01, +e23, +s01, +s23, +w01, +w23, +tr, +won}:
      +seat = U32.to_nat(R.trick.seat(tr))
      +h01 = R.pick(seat, n01, e01, s01, w01)
      +h23 = R.pick(seat, n23, e23, s23, w23)
      +lead = R.trick.lead(tr)
      +free = U32.is_zero(R.suit.mask(U32.to_nat(lead), h01, h23))
      gen.exact(Z.gen.list(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, l01, l23, Z.mem.none(), d),
        Z.tops(legal(free, 0, lead, (h01 >> 16n : U32)), (l01 >> 16n : U32)),
        Z.tops(legal(free, 1, lead, (h01 .&. 65535 : U32)), (l01 .&. 65535 : U32)),
        Z.tops(legal(free, 2, lead, (h23 >> 16n : U32)), (l23 >> 16n : U32)),
        Z.tops(legal(free, 3, lead, (h23 .&. 65535 : U32)), (l23 .&. 65535 : U32)))

def first.card(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{c, _}:
      c

# Checks the moves at each of the four places in a trick, playing the top legal card
# each time.
def gen.trick(n: Nat, +t: U32, +pos: R.Pos, +l01: U32, +l23: U32, +d: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(gen.ok(t, pos, l01, l23, d),
        gen.trick(p, t, R.play(t, pos, first.card(R.moves(pos))), l01, l23, (d - 1 : U32)))

def gen.strains(n: Nat, +t: U32, +deal: C.Deal, +d: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      +pos = R.pos.start(deal, (t .&. 3 : U32))
      Bool.and(gen.trick(4n, t, pos, R.pos.live01(pos), R.pos.live23(pos), d), gen.strains(p, (t + 1 : U32), deal, d))

def gen.all(n: Nat, +seed: U32, +k: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(gen.strains(5n, 0, D.ending(seed, k), (4 * k : U32)), gen.all(p, (seed + 1 : U32), k))

# ---------------------------------------------------------------------------
# Runs

# Whether n is how many cards in play from the top down are in m.
def run.count(k: Nat, +bit: U32, +m: U32, +live: U32, +going: Bool, +n: U32) -> U32:
  match k:
    case 0n:
      n
    case 1n+p:
      +il = bit.in(live, bit)
      +im = bit.in(m, bit)
      +still = going && (Bool.not(il) || im)
      run.count(p, (bit >> 1n : U32), m, live, still, (n + Bool.to_u32(still && il) : U32))

def run.ok(+m: U32, +live: U32) -> Bool:
  U32.is_eq(Z.run(m, live), run.count(13n, 4096, m, live, True{}, 0))

# Every way to split n ranks, from this bit up, as tops.walk does.
def run.walk(+n: Nat, +bit: U32, +m: U32, +live: U32) -> Bool:
  match n:
    case 0n:
      run.ok(m, live)
    case 1n+p:
      +up = (bit << 1n : U32)
      Bool.and(run.walk(p, up, m, live),
        Bool.and(run.walk(p, up, m, (live .|. bit : U32)),
          run.walk(p, up, (m .|. bit : U32), (live .|. bit : U32))))

# ---------------------------------------------------------------------------
# The search against brute force

def tables.eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, s} Con{y, t}:
      Bool.and(U32.is_eq(x, y), tables.eq(s, t))
    case _ _:
      False{}

def table.tricks(t: B.Table) -> List<&2, U32>:
  match t:
    case B.Table{ts, _}:
      ts

def oracle.ok(+deal: C.Deal) -> Bool:
  tables.eq(table.tricks(Z.table(deal)), table.tricks(B.table(deal)))

# Whole tables of the endings from these seeds with k cards in each hand.
def oracle.all(n: Nat, +seed: U32, +k: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(oracle.ok(D.ending(seed, k)), oracle.all(p, (seed + 1 : U32), k))

def res.value(r: B.Res) -> U32:
  match r:
    case B.Res{v, _}:
      v

# Whether what the search counts as sure fits the true result, for one strain and
# leader of a deal with left tricks.
def sure.ok(+t: U32, +leader: U32, +left: U32, +deal: C.Deal) -> Bool:
  +pos = R.pos.start(deal, leader)
  +both = Z.counts(t, pos, left)
  +v = res.value(B.solve(U32.to_nat((left * 4 : U32)), t, pos, 0n))
  +side = R.sel(U32.is_zero((leader .&. 1 : U32)), v, (left - v : U32))
  U32.is_le((both .&. 255 : U32), side) && U32.is_le((both >> 8n : U32), (left - side : U32))

def sure.leaders(n: Nat, +leader: U32, +t: U32, +left: U32, +deal: C.Deal) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(sure.ok(t, leader, left, deal), sure.leaders(p, (leader + 1 : U32), t, left, deal))

def sure.strains(n: Nat, +t: U32, +left: U32, +deal: C.Deal) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(sure.leaders(4n, 0, t, left, deal), sure.strains(p, (t + 1 : U32), left, deal))

# Every strain and leader of the endings from these seeds.
def sure.all(n: Nat, +seed: U32, +k: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(sure.strains(5n, 0, k, D.ending(seed, k)), sure.all(p, (seed + 1 : U32), k))

# ---------------------------------------------------------------------------
# The transposition table

# Z.kth finds the card that Z.ws.suit counts down to, for every number of top cards.
def ws.kth.k(n: Nat, +k: U32, +l: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(U32.is_eq(Z.ws.suit(Z.kth(U32.to_nat(k), l), l), k), ws.kth.k(p, (k + 1 : U32), l))

def ws.kth.all(n: Nat, +l: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(ws.kth.k(1n+U32.popcount(l), 0, l), ws.kth.all(p, (l + 1 : U32)))

# Walks down the ranks from x, adding the cards of h, skipping cards not in play, and
# stopping at a card in play that isn't in h.
def run.walk.more(n: Nat, in: Bool, +x: U32, +h: U32, +live: U32, +acc: U32) -> U32:
  match n in:
    case 0n _:
      acc
    case 1n+p False{}:
      acc
    case 1n+p True{}:
      run.walk.more(p, U32.is_ne(((x >> 1n) .&. h : U32), 0) || U32.is_zero(((x >> 1n) .&. live : U32)), (x >> 1n : U32), h, live, (acc .|. (x .&. h .&. live) : U32))

def run.spec(+b: U32, +h: U32, +live: U32) -> U32:
  run.walk.more(13n, U32.is_ne(((b >> 1n) .&. h : U32), 0) || U32.is_zero(((b >> 1n) .&. live : U32)), (b >> 1n : U32), h, live, 0)

def run.below.bits(n: Nat, +b: U32, +h: U32, +live: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(U32.is_eq(Z.run.below(b, h, live), run.spec(b, h, live)), run.below.bits(p, (b << 1n : U32), h, live))

# Every holding h of the low 7 ranks, for each card of them, with these in play.
def run.below.all(n: Nat, +h: U32, +live: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(run.below.bits(7n, 1, (h .&. live : U32), live), run.below.all(p, (h + 1 : U32), live))

# Bounds tightened by an answer about need settle need that way.
def bounds.need(n: Nat, +need: U32, +lo: U32, +hi: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(
        Bool.and(U32.is_eq(Z.tt.says(Z.bounds.word(True{}, lo, hi, need, 0), need), 1), U32.is_eq(Z.tt.says(Z.bounds.word(False{}, lo, hi, need, 0), need), 2)),
        bounds.need(p, (need + 1 : U32), lo, hi))

# Every lo < need <= hi up to 13: an answer about need is only asked for between
# the bounds, since others are settled already.
def bounds.hi(n: Nat, +hi: U32, +lo: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(bounds.need(U32.to_nat((hi - lo : U32)), (lo + 1 : U32), lo, hi), bounds.hi(p, (hi + 1 : U32), lo))

def bounds.all(+n: Nat, +lo: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(bounds.hi(1n+p, lo, lo), bounds.all(p, (lo + 1 : U32)))

def bool.same(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

# Owner words agree exactly on the top cards asked for, here with two cards each.
def agree.b(n: Nat, +a: U32, +b: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(
        Bool.and(Z.own.agree(a, b, 2, 0),
          Bool.and(bool.same(Z.own.agree(a, b, 2, 1), U32.is_eq((a >> 2n : U32), (b >> 2n : U32))), bool.same(Z.own.agree(a, b, 2, 2), U32.is_eq(a, b)))),
        agree.b(p, a, (b + 1 : U32)))

def agree.all(n: Nat, +a: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(agree.b(16n, a, 0), agree.all(p, (a + 1 : U32)))

# ---------------------------------------------------------------------------
# The proof foundation: counting cards

# The number of set bits of a word, walking it one bit at a time: the plain statement
# that U32.popcount computes by bit tricks.
def word.count(n: Nat, w: Word(n)) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          word.count(p, t)
        case WCon{True{}, t}:
          1n+word.count(p, t)

def bits(u: U32) -> Nat:
  match u:
    case U32{w}:
      word.count(32n, w)

# What the laws about holdings and words are stated with.

def pow2(j: Nat) -> Nat:
  match j:
    case 0n:
      1n
    case 1n+i:
      Nat.double(pow2(i))

# The word of width n whose first j bits are set.
def ones(n: Nat, +j: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match j:
        case 0n:
          WCon{False{}, ones(p, 0n)}
        case 1n+i:
          WCon{True{}, ones(p, i)}

def w.tail(-p: Nat, w: Word(1n+p)) -> Word(p):
  match w:
    case WCon{_, t}:
      t

def w.head(-p: Nat, w: Word(1n+p)) -> Bool:
  match w:
    case WCon{h, _}:
      h

def u.word(u: U32) -> Word(32n):
  match u:
    case U32{w}:
      w

# What every holding m satisfies, about its lowest card b: popcount counts it, b is in
# it, and if it isn't empty, b is one card below the 13th whose rank ctz finds, and
# taking it leaves a holding with one card fewer.
def facts(+m: U32) -> Bool:
  +b = (m .&. (0 - m) : U32)
  +z = U32.is_eq(m, 0)
  +rest = (m .^. b : U32)
  Bool.and(Nat.is_eq(U32.popcount(m), bits(m)),
    Bool.and(U32.is_eq((b .&. m : U32), b),
      Bool.or(Bool.and(z, U32.is_eq(b, 0)),
        Bool.and(Bool.not(z),
          Bool.and(Nat.is_lt(U32.ctz(b), 13n),
            Bool.and(U32.is_eq((1 << U32.ctz(b) : U32), b),
              Bool.and(Nat.is_eq(U32.popcount(rest), Nat.sub(U32.popcount(m), 1n)), U32.is_eq((rest .&. 8191 : U32), rest))))))))

def facts.all(n: Nat, +m: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(facts(m), facts.all(p, U32.inc(m)))

# What a card's code says: its suit and its rank come back out.
def code.ok(+s: Nat, +r: Nat) -> Bool:
  +c = C.card.make(U32.from_nat(s), U32.from_nat(r))
  Bool.and(U32.is_eq(C.card.suit(c), U32.from_nat(s)), U32.is_eq(C.card.rank(c), U32.from_nat(r)))

# The word for number k, by counting up from zero as U32.from_nat does.
def W.from(+n: Nat, k: Nat) -> Word(n):
  match k:
    case 0n:
      Word.zero(n)
    case 1n+j:
      Word.inc(n, W.from(n, j))

# Words as sets of bits, for the laws below.

# a is a subset of b: every bit of a is in b.
def Sub(n: Nat, a: Word(n), b: Word(n)) -> Data:
  {Word.and(n, a, b) == a : Word(n)}


def Sub32(a: U32, b: U32) -> Data:
  {U32.and(a, b) == a : U32}


# A valid hand word: its two holdings are 13 bits each. Its holdings are holdings.
def valid.mask() -> U32:
  536813567


def Sub32.ones(a: U32, +j: Nat) -> Data:
  match a:
    case U32{w}:
      Sub(32n, w, ones(32n, j))

