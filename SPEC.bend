# SPEC.bend: plain statements of the rules, used by LAWS.bend.

import Base
import ./src/cards.bend as C
import ./src/rules.bend as R

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

def later(+x: U32, +y: U32, +i: U32, other: U32) -> U32:
  R.sel(U32.is_gt(y, x), i, other)

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
