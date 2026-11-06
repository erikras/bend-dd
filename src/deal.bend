# deal.bend: deal a random bridge hand from a seed.
#
# The seed drives a small LCG, so the same number always gives the same deal.
# Card i of the deal order (0..51) has suit i / 13 and rank 12 - i % 13, so the
# ace of spades comes first and the deuce of clubs last.

import Base
import ./cards.bend as C

# One step of a 32-bit linear congruential generator.
def lcg(x: U32) -> U32:
  (x * 1664525 + 1013904223 : U32)

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

# Deals the remaining n cards, in card order, to seats that still need cards
# (a, b, c, d for N, E, S, W). Each card goes to a seat with probability
# proportional to the cards that seat still needs, which gives every deal the
# same chance. Answers the seat of each card.
def seats(n: Nat, +seed: U32, +a: U32, +b: U32, +c: U32, +d: U32) -> List<&2, U32>:
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
      seat <> seats(p, x, na, nb, nc, nd)

# Turns the seat of each card into a deal, starting from card number i.
def from_seats(xs: List<&2, U32>, +i: U32, d: C.Deal) -> C.Deal:
  match xs:
    case Nil{}:
      d
    case Con{seat, t}:
      +suit = U32.to_nat((i / 13 : U32))
      +rank = U32.to_nat((12 - i % 13 : U32))
      +bit = (1 << rank : U32)
      from_seats(t, (i + 1 : U32), C.deal.add(U32.to_nat(seat), suit, bit, d))

# The deal for one seed.
def random(+seed: U32) -> C.Deal:
  from_seats(seats(52n, seed, 13, 13, 13, 13), 0, C.deal.empty())
