# pbn.bend: print and parse deals in PBN form.
#
#   N:A8.J94.KQ62.KT86 K64.873.A3.Q5432 QJ73.AKQ65.98.AJ T952.T2.JT754.97
#
# The first letter names the seat of the first hand, the rest follow clockwise.
# Each hand lists spades, hearts, diamonds and clubs, separated by dots, and an
# empty holding is a void. Endings work too, as long as every hand is written.

import Base
import ./cards.bend as C

# ---------------------------------------------------------------------------
# Printing

def ranks() -> String:
  "AKQJT98765432"

def suit.emit(keep: Bool, c: Char, rest: String) -> String:
  match keep:
    case True{}:
      SCon{c, rest}
    case False{}:
      rest

def suit.print.go(table: String, +bit: U32, +m: U32) -> String:
  match table:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      suit.emit(U32.is_ne((m .&. bit : U32), 0), c, suit.print.go(t, (bit >> 1n : U32), m))

# A holding, highest card first, such as "AQT4".
def suit.print(+m: U32) -> String:
  suit.print.go(ranks(), 4096, m)

def hand.print(h: C.Hand) -> String:
  match h:
    case C.Hand{s, x, d, c}:
      suit.print(s) ++ "." ++ suit.print(x) ++ "." ++ suit.print(d) ++ "." ++ suit.print(c)

# The whole deal, starting from North.
def print(d: C.Deal) -> String:
  match d:
    case C.Deal{n, e, s, w}:
      "N:" ++ hand.print(n) ++ " " ++ hand.print(e) ++ " " ++ hand.print(s) ++ " " ++ hand.print(w)

# ---------------------------------------------------------------------------
# Parsing

def rank.pick(hit: Bool, +bit: U32, other: U32) -> U32:
  match hit:
    case True{}:
      bit
    case False{}:
      other

def rank.scan(table: String, +c: U32, +bit: U32) -> U32:
  match table:
    case SNil{}:
      0
    case SCon{Chr{x}, t}:
      rank.pick(U32.is_eq(x, c), bit, rank.scan(t, c, (bit >> 1n : U32)))

# The one-bit holding of a rank letter, or 0 when it is not a rank.
def rank.bit(+c: U32) -> U32:
  rank.scan(ranks(), c, 4096)

# Reads the letters of a holding on top of the mask m. Answers None for
# anything that is not a rank, and for a rank seen twice. bad says the letter
# before this one was one of those.
def suit.parse.go(s: String, bad: Bool, +m: U32) -> Maybe<&2, U32>:
  match s bad:
    case _ True{}:
      None{}
    case SNil{} False{}:
      Some{m}
    case SCon{Chr{+c}, t} False{}:
      +bit = rank.bit(c)
      +dup = U32.is_eq(bit, 0) || U32.is_ne((bit .&. m : U32), 0)
      suit.parse.go(t, dup, (m .|. bit : U32))

def suit.parse(s: String) -> Maybe<&2, U32>:
  suit.parse.go(s, False{}, 0)

def hand.parse.make(a: Maybe<&2, U32>, b: Maybe<&2, U32>, c: Maybe<&2, U32>, d: Maybe<&2, U32>) -> Maybe<&2, C.Hand>:
  match a b c d:
    case Some{s} Some{x} Some{y} Some{z}:
      Some{C.Hand{s, x, y, z}}
    case _ _ _ _:
      None{}

def hand.parse.list(xs: List<&2, String>) -> Maybe<&2, C.Hand>:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}:
      hand.parse.make(suit.parse(a), suit.parse(b), suit.parse(c), suit.parse(d))
    case _:
      None{}

# One hand: exactly four holdings separated by dots.
def hand.parse(s: String) -> Maybe<&2, C.Hand>:
  hand.parse.list(String.split(s, '.'))

def seat.pick(hit: Bool, +i: U32, other: U32) -> U32:
  match hit:
    case True{}:
      i
    case False{}:
      other

def seat.scan(table: String, +c: U32, +i: U32) -> U32:
  match table:
    case SNil{}:
      4
    case SCon{Chr{x}, t}:
      seat.pick(U32.is_eq(x, c), i, seat.scan(t, c, (i + 1 : U32)))

# The seat a PBN seat letter names, or 4 when it is not a seat letter.
def seat.parse(c: Char) -> U32:
  seat.scan("NESW", Char.to_u32(c), 0)

# The deal from four hands listed clockwise from a first seat.
def deal.place(first: Nat, a: C.Hand, b: C.Hand, c: C.Hand, d: C.Hand) -> C.Deal:
  match first:
    case 0n:
      C.Deal{a, b, c, d}
    case 1n:
      C.Deal{d, a, b, c}
    case 2n:
      C.Deal{c, d, a, b}
    case _:
      C.Deal{b, c, d, a}

# Whether no card appears in two hands.
def deal.disjoint(+a: C.Hand, +b: C.Hand, +c: C.Hand, +d: C.Hand) -> Bool:
  +ab = C.hand.overlap(a, b)
  +ac = C.hand.overlap(a, c)
  +ad = C.hand.overlap(a, d)
  +bc = C.hand.overlap(b, c)
  +bd = C.hand.overlap(b, d)
  +cd = C.hand.overlap(c, d)
  U32.is_eq((ab .|. ac .|. ad .|. bc .|. bd .|. cd : U32), 0)

def deal.check(ok: Bool, first: Nat, a: C.Hand, b: C.Hand, c: C.Hand, d: C.Hand) -> Maybe<&2, C.Deal>:
  match ok:
    case True{}:
      Some{deal.place(first, a, b, c, d)}
    case False{}:
      None{}

def deal.make(first: Nat, a: Maybe<&2, C.Hand>, b: Maybe<&2, C.Hand>, c: Maybe<&2, C.Hand>, d: Maybe<&2, C.Hand>) -> Maybe<&2, C.Deal>:
  match a b c d:
    case Some{+w} Some{+x} Some{+y} Some{+z}:
      deal.check(deal.disjoint(w, x, y, z), first, w, x, y, z)
    case _ _ _ _:
      None{}

def deal.list(first: Nat, xs: List<&2, String>) -> Maybe<&2, C.Deal>:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}:
      deal.make(first, hand.parse(a), hand.parse(b), hand.parse(c), hand.parse(d))
    case _:
      None{}

def deal.body(known: Bool, first: U32, rest: String) -> Maybe<&2, C.Deal>:
  match known:
    case True{}:
      deal.list(U32.to_nat(first), String.split(rest, ' '))
    case False{}:
      None{}

def deal.head(s: String) -> Maybe<&2, C.Deal>:
  match s:
    case SCon{f, SCon{Chr{colon}, rest}}:
      +seat = seat.parse(f)
      deal.body(U32.is_lt(seat, 4) && U32.is_eq(colon, 58), seat, rest)
    case _:
      None{}

# A whole deal. Answers None for anything malformed: an unknown seat letter, a
# hand count other than four, a suit count other than four, a letter that is
# not a rank, or a card written twice.
def parse(s: String) -> Maybe<&2, C.Deal>:
  deal.head(s)
