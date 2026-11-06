# hand.bend: deal a random bridge hand and print it.
#
#   bend hand.bend [deal-number]
#
# The deal number seeds a small LCG, so the same number always gives the
# same deal. Seats are 0=North 1=East 2=South 3=West. Suits are
# 0=spades 1=hearts 2=diamonds 3=clubs. Card c (0..51) has suit c / 13
# and rank c % 13, where rank 0 is the ace and rank 12 is the two.

import Base

# ---------------------------------------------------------------------------
# Strings

# Drops the first n characters of s.
def str.drop(n: Nat, s: String) -> String:
  match n:
    case 0n:
      s
    case 1n+p:
      match s:
        case SNil{}:
          SNil{}
        case SCon{h, t}:
          str.drop(p, t)

# The first character of s, as a String.
def str.first(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{h, t}:
      SCon{h, SNil{}}

# The i-th character of s, as a String.
def str.at(i: U32, s: String) -> String:
  str.first(str.drop(U32.to_nat(i), s))

# Pads s with spaces on the right to w characters.
def str.pad(+s: String, +w: U32) -> String:
  +len = U32.from_nat(String.length(s))
  +gap = (w - len : U32)
  s ++ String.repeat(" ", U32.to_nat(gap))

# ---------------------------------------------------------------------------
# Random numbers

# One step of a 32-bit linear congruential generator.
def lcg(x: U32) -> U32:
  (x * 1664525 + 1013904223 : U32)

# ---------------------------------------------------------------------------
# Dealing

# Which seat a draw r lands on, given the cards still owed to N, E and S.
def pick.c(lt: Bool) -> U32:
  match lt:
    case True{}:
      2
    case False{}:
      3

def pick.b(lt: Bool, +r: U32, +ab: U32, +c: U32) -> U32:
  match lt:
    case True{}:
      1
    case False{}:
      pick.c(U32.is_lt(r, (ab + c : U32)))

def pick.a(lt: Bool, +r: U32, +a: U32, +b: U32, +c: U32) -> U32:
  match lt:
    case True{}:
      0
    case False{}:
      pick.b(U32.is_lt(r, (a + b : U32)), r, (a + b : U32), c)

def pick(+r: U32, +a: U32, +b: U32, +c: U32) -> U32:
  pick.a(U32.is_lt(r, a), r, a, b, c)

# Takes one card off a seat's count when that seat was picked.
def dec(hit: Bool, a: U32) -> U32:
  match hit:
    case True{}:
      (a - 1 : U32)
    case False{}:
      a

# Deals the remaining n cards, in card order, to seats that still need
# cards (a, b, c, d for N, E, S, W). Each card goes to a seat with
# probability proportional to the cards that seat still needs, which gives
# every deal the same chance. Answers the seat of each card.
def deal(n: Nat, +seed: U32, +a: U32, +b: U32, +c: U32, +d: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      +x = lcg(seed)
      +hi = (x >> 16n : U32)
      +tot = (a + b + c + d : U32)
      +r = (hi % tot : U32)
      +seat = pick(r, a, b, c)
      na = dec(U32.is_eq(seat, 0), a)
      nb = dec(U32.is_eq(seat, 1), b)
      nc = dec(U32.is_eq(seat, 2), c)
      nd = dec(U32.is_eq(seat, 3), d)
      seat <> deal(p, x, na, nb, nc, nd)

# ---------------------------------------------------------------------------
# Printing

# The rank letter of card i.
def rank(+i: U32) -> String:
  str.at((i % 13 : U32), "AKQJT98765432")

# Some terminal fonts draw U+2665 and U+2666 hollow, so the heart is U+2764
# followed by U+FE0E (an invisible text-style selector) and the diamond is
# U+25C6. The selector counts as a character for str.pad but takes up no
# column on screen.
def suit.selector(heart: Bool) -> String:
  match heart:
    case True{}:
      "︎"
    case False{}:
      ""

# The symbol of a suit.
def suit.symbol(+s: U32) -> String:
  str.at(s, "♠❤◆♣") ++ suit.selector(U32.is_eq(s, 1))

def emit(keep: Bool, +i: U32, rest: String) -> String:
  match keep:
    case True{}:
      rank(i) ++ rest
    case False{}:
      rest

# The cards of one seat in one suit, highest first, e.g. "AQT4".
def holding(seats: List<&2, U32>, +i: U32, +seat: U32, +suit: U32) -> String:
  match seats:
    case Nil{}:
      ""
    case Con{s, t}:
      +mine = U32.is_eq(s, seat)
      +in_suit = U32.is_eq((i / 13 : U32), suit)
      emit(mine && in_suit, i, holding(t, (i + 1 : U32), seat, suit))

def dash(void: Bool, h: String) -> String:
  match void:
    case True{}:
      "-"
    case False{}:
      h

# One line of a hand diagram, e.g. "♠ AQT4", with "-" for a void.
def line(seats: List<&2, U32>, +seat: U32, +suit: U32) -> String:
  +h = holding(seats, 0, seat, suit)
  suit.symbol(suit) ++ " " ++ dash(String.is_empty(h), h)

# A seat's hand in PBN order, e.g. "AQT4.K32.J9.8765".
def pbn.hand(+seats: List<&2, U32>, +seat: U32) -> String:
  String.join([
    holding(seats, 0, seat, 0),
    holding(seats, 0, seat, 1),
    holding(seats, 0, seat, 2),
    holding(seats, 0, seat, 3)
  ], ".")

# The whole deal in PBN, starting from North.
def pbn(+seats: List<&2, U32>) -> String:
  "N:" ++ String.join([
    pbn.hand(seats, 0),
    pbn.hand(seats, 1),
    pbn.hand(seats, 2),
    pbn.hand(seats, 3)
  ], " ")

# The classic four-hand diagram: North on top, West and East in the
# middle, South at the bottom.
def diagram(+seats: List<&2, U32>) -> String:
  +sp : String = "            "
  String.join([
    sp ++ "North",
    sp ++ line(seats, 0, 0),
    sp ++ line(seats, 0, 1),
    sp ++ line(seats, 0, 2),
    sp ++ line(seats, 0, 3),
    str.pad("West", 24) ++ "East",
    str.pad(line(seats, 3, 0), 24) ++ line(seats, 1, 0),
    str.pad(line(seats, 3, 1), 25) ++ line(seats, 1, 1),
    str.pad(line(seats, 3, 2), 24) ++ line(seats, 1, 2),
    str.pad(line(seats, 3, 3), 24) ++ line(seats, 1, 3),
    sp ++ "South",
    sp ++ line(seats, 2, 0),
    sp ++ line(seats, 2, 1),
    sp ++ line(seats, 2, 2),
    sp ++ line(seats, 2, 3)
  ], "\n")

# ---------------------------------------------------------------------------
# Command line

def seed.read(m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}:
      1
    case Some{v}:
      v

def seed.arg(args: List<String>) -> U32:
  match args:
    case Nil{}:
      1
    case Con{a, rest}:
      seed.read(U32.read(a))

# The deal number: the first argument, or 1.
def seed(args: List<String>) -> U32:
  match args:
    case Nil{}:
      1
    case Con{prog, rest}:
      seed.arg(rest)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    +n : U32 = seed(args)
    +seats : List<&2, U32> = deal(52n, n, 13, 13, 13, 13)
    IO.print("Deal " ++ U32.show(n))
    IO.print("")
    IO.print(diagram(seats))
    IO.print("")
    IO.print(pbn(seats))
