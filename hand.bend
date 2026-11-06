# hand.bend: deal a random bridge hand and print it.
#
#   bend hand.bend [deal-number]
#
# The deal number seeds the dealer, so the same number always gives the same
# deal. See src/cards.bend for the seats, the suits and the card encoding.

import Base
import ./src/cards.bend as C
import ./src/deal.bend as D
import ./src/pbn.bend as P

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
# Printing

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

def dash(void: Bool, h: String) -> String:
  match void:
    case True{}:
      "-"
    case False{}:
      h

# One line of a hand diagram, e.g. "♠ AQT4", with "-" for a void.
def line(+deal: C.Deal, +seat: U32, +suit: U32) -> String:
  +h = P.suit.print(C.hand.suit(U32.to_nat(suit), C.deal.hand(U32.to_nat(seat), deal)))
  suit.symbol(suit) ++ " " ++ dash(String.is_empty(h), h)

# The classic four-hand diagram: North on top, West and East in the
# middle, South at the bottom.
def diagram(+deal: C.Deal) -> String:
  +sp : String = "            "
  String.join([
    sp ++ "North",
    sp ++ line(deal, 0, 0),
    sp ++ line(deal, 0, 1),
    sp ++ line(deal, 0, 2),
    sp ++ line(deal, 0, 3),
    str.pad("West", 24) ++ "East",
    str.pad(line(deal, 3, 0), 24) ++ line(deal, 1, 0),
    str.pad(line(deal, 3, 1), 25) ++ line(deal, 1, 1),
    str.pad(line(deal, 3, 2), 24) ++ line(deal, 1, 2),
    str.pad(line(deal, 3, 3), 24) ++ line(deal, 1, 3),
    sp ++ "South",
    sp ++ line(deal, 2, 0),
    sp ++ line(deal, 2, 1),
    sp ++ line(deal, 2, 2),
    sp ++ line(deal, 2, 3)
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
    +deal : C.Deal = D.random(n)
    IO.print("Deal " ++ U32.show(n))
    IO.print("")
    IO.print(diagram(deal))
    IO.print("")
    IO.print(P.print(deal))
