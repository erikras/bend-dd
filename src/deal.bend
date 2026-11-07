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

# Spreads a seed out: LCG outputs from nearby seeds start out close together.
def mix(+seed: U32) -> U32:
  lcg(lcg((seed * 2654435761 .^. (seed >> 15n) : U32)))

def ending.add(keep: Bool, +seat: U32, +i: U32, d: C.Deal) -> C.Deal:
  match keep:
    case True{}:
      C.deal.add(U32.to_nat(seat), U32.to_nat((i / 13 : U32)), (1 << U32.to_nat((12 - i % 13 : U32)) : U32), d)
    case False{}:
      d

# Deals the remaining n cards of the deck, from card number i. Each card goes to a
# seat or stays out, with probability proportional to the places each still has.
def ending.go(n: Nat, +i: U32, +seed: U32, +a: U32, +b: U32, +c: U32, +e: U32, +out: U32, d: C.Deal) -> C.Deal:
  match n:
    case 0n:
      d
    case 1n+p:
      +x = lcg(seed)
      +r = ((x >> 16n) % (a + b + c + e + out) : U32)
      +keep = U32.is_ge(r, out)
      +seat = pick((r - out : U32), a, b, c)
      +in0 = keep && U32.is_eq(seat, 0)
      +in1 = keep && U32.is_eq(seat, 1)
      +in2 = keep && U32.is_eq(seat, 2)
      +in3 = keep && U32.is_eq(seat, 3)
      ending.go(p, (i + 1 : U32), x, dec(in0, a), dec(in1, b), dec(in2, c), dec(in3, e), dec(Bool.not(keep), out),
        ending.add(keep, seat, i, d))

# A random ending with k cards in each hand from the first few suits, which makes
# long runs and voids common.
def ending.in(+suits: U32, +seed: U32, +k: U32) -> C.Deal:
  +cards = (13 * suits : U32)
  ending.go(U32.to_nat(cards), 0, mix(seed), k, k, k, k, (cards - 4 * k : U32), C.deal.empty())

# A random ending for one seed, with k cards in each hand.
def ending(+seed: U32, +k: U32) -> C.Deal:
  ending.in(4, seed, k)
