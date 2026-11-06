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
# Move ordering

# Whether a list holds each card of these four holdings exactly once.
def order.exact(xs: List<&2, U32>, +k0: U32, +k1: U32, +k2: U32, +k3: U32) -> Bool:
  match xs:
    case Nil{}:
      U32.is_zero((k0 .|. k1 .|. k2 .|. k3 : U32))
    case Con{+c, t}:
      +s = C.card.suit(c)
      +bit = C.card.bit(c)
      +is0 = U32.is_eq(s, 0)
      +is1 = U32.is_eq(s, 1)
      +is2 = U32.is_eq(s, 2)
      +is3 = U32.is_eq(s, 3)
      bit.in(R.pick(U32.to_nat(s), k0, k1, k2, k3), bit) &&
        order.exact(t, (k0 .^. R.sel(is0, bit, 0) : U32), (k1 .^. R.sel(is1, bit, 0) : U32), (k2 .^. R.sel(is2, bit, 0) : U32), (k3 .^. R.sel(is3, bit, 0) : U32))

def order.ok(+first: Bool, +mine: Bool, +k0: U32, +k1: U32, +k2: U32, +k3: U32, +w0: U32, +w1: U32, +w2: U32, +w3: U32) -> Bool:
  order.exact(Z.order(first, mine, k0, k1, k2, k3, w0, w1, w2, w3, Z.mem.none()), k0, k1, k2, k3)

def order.modes(+k0: U32, +k1: U32, +k2: U32, +k3: U32, +w0: U32, +w1: U32, +w2: U32, +w3: U32) -> Bool:
  order.ok(True{}, True{}, k0, k1, k2, k3, w0, w1, w2, w3) &&
    order.ok(True{}, False{}, k0, k1, k2, k3, w0, w1, w2, w3) &&
    order.ok(False{}, True{}, k0, k1, k2, k3, w0, w1, w2, w3) &&
    order.ok(False{}, False{}, k0, k1, k2, k3, w0, w1, w2, w3)

# Each subset w of k, in a suit, walking down from k: w takes each subset once.
def order.subsets(n: Nat, +k: U32, +w: U32, +k1: U32, +w1: U32) -> Bool:
  match n:
    case 0n:
      order.modes(k, k1, 4097, 8191, w, w1, 1, 4096)
    case 1n+p:
      Bool.and(order.subsets(p, k, ((w - 1) .&. k : U32), k1, w1), order.modes(k, k1, 4097, 8191, w, w1, 1, 4096))

# ---------------------------------------------------------------------------
# Winners

# Whether a card counts as a winner exactly when it beats the card winning.
def wins.ok(+t: U32, +best: U32, +c: U32) -> Bool:
  bool.eq(U32.is_ne(Z.wins(False{}, C.card.suit(c), C.card.bit(c), 8191, t, best), 0), R.beats(t, best, c))

def wins.c.rank(n: Nat, +t: U32, +best: U32, +s: U32, +r: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(wins.ok(t, best, C.card.make(s, r)), wins.c.rank(p, t, best, s, (r + 1 : U32)))

def wins.c.suit(n: Nat, +t: U32, +best: U32, +s: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(wins.c.rank(13n, t, best, s, 0), wins.c.suit(p, t, best, (s + 1 : U32)))

# Best is any card of suit s: the suit led, or a trump on top of it.
def wins.best(n: Nat, +t: U32, +s: U32, +r: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(wins.c.suit(4n, t, C.card.make(s, r), 0), wins.best(p, t, s, (r + 1 : U32)))

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
