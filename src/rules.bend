# rules.bend: positions, legal plays and tricks.
#
# A position holds the cards left in each hand and the state of the current
# trick. Hands are packed into two words each: spades << 16 | hearts and
# diamonds << 16 | clubs, as 13-bit masks (see cards.bend). Nothing is mutated:
# playing a card builds the next position.

import Base
import ./cards.bend as C

# The strain with no trump suit. No card has this suit, so trump checks need no
# special case for it. As a lead suit it means nobody has led yet.
def none() -> U32:
  4

# won counts the tricks taken so far by North-South. trick packs the state of
# the current trick, see trick.make.
type Pos is Data:
  Pos{
    n01: U32, n23: U32,
    e01: U32, e23: U32,
    s01: U32, s23: U32,
    w01: U32, w23: U32,
    trick: U32,
    won: U32
  }

# ---------------------------------------------------------------------------
# The trick word

# seat: the seat to play (2 bits). played: cards on the table (2 bits). lead:
# the suit led, or none() (3 bits). owner: the seat winning so far (2 bits).
# best: the card winning so far (6 bits).
def trick.make(+seat: U32, +played: U32, +lead: U32, +owner: U32, +best: U32) -> U32:
  (seat .|. (played << 2n) .|. (lead << 4n) .|. (owner << 7n) .|. (best << 9n) : U32)

def trick.seat(+t: U32) -> U32:
  (t .&. 3 : U32)

def trick.played(+t: U32) -> U32:
  ((t >> 2n) .&. 3 : U32)

def trick.lead(+t: U32) -> U32:
  ((t >> 4n) .&. 7 : U32)

def trick.owner(+t: U32) -> U32:
  ((t >> 7n) .&. 3 : U32)

def trick.best(+t: U32) -> U32:
  ((t >> 9n) .&. 63 : U32)

# A new trick with this seat on lead.
def trick.start(+seat: U32) -> U32:
  trick.make(seat, 0, none(), 0, 0)

# ---------------------------------------------------------------------------
# Trick winner

# Whether card c beats the card now winning the trick, with strain t as trumps:
# a higher card of the same suit, or a trump over a card that is not one.
def beats(+t: U32, +best: U32, +c: U32) -> Bool:
  +cs = C.card.suit(c)
  +bs = C.card.suit(best)
  (U32.is_eq(cs, bs) && U32.is_gt(c, best)) || (U32.is_eq(cs, t) && U32.is_ne(bs, t))

def sel(b: Bool, x: U32, y: U32) -> U32:
  match b:
    case True{}:
      x
    case False{}:
      y

def trick.next.go(first: Bool, last: Bool, +win: Bool, +seat: U32, +played: U32, +lead: U32, +owner: U32, +best: U32, +c: U32) -> U32:
  match first last:
    case True{} _:
      trick.make(((seat + 1) .&. 3 : U32), 1, C.card.suit(c), seat, c)
    case False{} True{}:
      trick.start(sel(win, seat, owner))
    case False{} False{}:
      trick.make(((seat + 1) .&. 3 : U32), (played + 1 : U32), lead, sel(win, seat, owner), sel(win, c, best))

# The trick word after the seat to play plays card c. The fourth card of a
# trick starts a new one, led by the seat that won.
def trick.next(+tr: U32, +t: U32, +c: U32) -> U32:
  +played = trick.played(tr)
  +best = trick.best(tr)
  trick.next.go(U32.is_eq(played, 0), U32.is_eq(played, 3), beats(t, best, c),
    trick.seat(tr), played, trick.lead(tr), trick.owner(tr), best, c)

# North-South's trick count after moving to trick word tr. A word with no cards
# played means a trick has just ended, and its leader is the seat that won it.
def won.next(+tr: U32, +won: U32) -> U32:
  sel(U32.is_eq(trick.played(tr), 0), (won + Bool.to_u32(U32.is_eq((tr .&. 1 : U32), 0)) : U32), won)

# ---------------------------------------------------------------------------
# Legal plays

def pick(seat: Nat, a: U32, b: U32, c: U32, d: U32) -> U32:
  match seat:
    case 0n:
      a
    case 1n:
      b
    case 2n:
      c
    case _:
      d

# The holding of a suit, from a hand's two words. Any other number, such as
# none(), answers an empty holding.
def suit.mask(suit: Nat, +h01: U32, +h23: U32) -> U32:
  match suit:
    case 0n:
      (h01 >> 16n : U32)
    case 1n:
      (h01 .&. 65535 : U32)
    case 2n:
      (h23 >> 16n : U32)
    case 3n:
      (h23 .&. 65535 : U32)
    case _:
      0

# Pushes the cards of a holding onto acc, lowest first, so the highest ends up
# at the head. n bounds the loop: a holding has at most 13 cards.
def moves.peel(n: Nat, z: Bool, +suit: U32, +m: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n z:
    case 0n _:
      acc
    case 1n+p True{}:
      acc
    case 1n+p False{}:
      +b = (m .&. (0 - m) : U32)
      +rest = (m .^. b : U32)
      moves.peel(p, U32.is_zero(rest), suit, rest, C.card.make(suit, U32.from_nat(U32.ctz(b))) <> acc)

def moves.suit(+suit: U32, +m: U32, acc: List<&2, U32>) -> List<&2, U32>:
  moves.peel(13n, U32.is_zero(m), suit, m, acc)

# Every card of a hand: spades first, highest first within a suit.
def moves.all(+h01: U32, +h23: U32) -> List<&2, U32>:
  moves.suit(0, (h01 >> 16n : U32),
    moves.suit(1, (h01 .&. 65535 : U32),
      moves.suit(2, (h23 >> 16n : U32),
        moves.suit(3, (h23 .&. 65535 : U32), Nil{}))))

def moves.pick(free: Bool, +lead: U32, +f: U32, +h01: U32, +h23: U32) -> List<&2, U32>:
  match free:
    case True{}:
      moves.all(h01, h23)
    case False{}:
      moves.suit(lead, f, Nil{})

# The legal plays from a hand: cards of the suit led if it has any (following
# suit), otherwise anything. On lead, none() has no holding, so anything goes.
def moves.of(+lead: U32, +h01: U32, +h23: U32) -> List<&2, U32>:
  +f = suit.mask(U32.to_nat(lead), h01, h23)
  moves.pick(U32.is_zero(f), lead, f, h01, h23)

# The legal plays in a position.
def moves(pos: Pos) -> List<&2, U32>:
  match pos:
    case Pos{n01, n23, e01, e23, s01, s23, w01, w23, +tr, won}:
      +seat = U32.to_nat(trick.seat(tr))
      moves.of(trick.lead(tr), pick(seat, n01, e01, s01, w01), pick(seat, n23, e23, s23, w23))

# ---------------------------------------------------------------------------
# Playing a card

# Rebuilds a position with one seat's words flipped by the masks a and b.
def play.go(seat: Nat, +a: U32, +b: U32, n01: U32, n23: U32, e01: U32, e23: U32, s01: U32, s23: U32, w01: U32, w23: U32, tr: U32, won: U32) -> Pos:
  match seat:
    case 0n:
      Pos{(n01 .^. a : U32), (n23 .^. b : U32), e01, e23, s01, s23, w01, w23, tr, won}
    case 1n:
      Pos{n01, n23, (e01 .^. a : U32), (e23 .^. b : U32), s01, s23, w01, w23, tr, won}
    case 2n:
      Pos{n01, n23, e01, e23, (s01 .^. a : U32), (s23 .^. b : U32), w01, w23, tr, won}
    case _:
      Pos{n01, n23, e01, e23, s01, s23, (w01 .^. a : U32), (w23 .^. b : U32), tr, won}

# The position after the seat to play plays card c, with strain t as trumps.
# The card must be in that seat's hand.
def play(+t: U32, pos: Pos, +c: U32) -> Pos:
  match pos:
    case Pos{n01, n23, e01, e23, s01, s23, w01, w23, +tr, +won}:
      +cs = C.card.suit(c)
      +m = C.card.bit(c)
      +x = sel(U32.is_zero((cs .&. 1 : U32)), (m << 16n : U32), m)
      +low = U32.is_lt(cs, 2)
      +tr2 = trick.next(tr, t, c)
      play.go(U32.to_nat(trick.seat(tr)), sel(low, x, 0), sel(low, 0, x),
        n01, n23, e01, e23, s01, s23, w01, w23, tr2, won.next(tr2, won))

# Whether North-South are to play.
def pos.ns(pos: Pos) -> Bool:
  match pos:
    case Pos{_, _, _, _, _, _, _, _, tr, _}:
      U32.is_zero((tr .&. 1 : U32))

def pos.won(pos: Pos) -> U32:
  match pos:
    case Pos{_, _, _, _, _, _, _, _, _, won}:
      won

def hand.pack01(h: C.Hand) -> U32:
  match h:
    case C.Hand{s, x, _, _}:
      ((s << 16n) .|. x : U32)

def hand.pack23(h: C.Hand) -> U32:
  match h:
    case C.Hand{_, _, d, c}:
      ((d << 16n) .|. c : U32)

# The starting position for a deal with this seat on lead.
def pos.start(d: C.Deal, +leader: U32) -> Pos:
  match d:
    case C.Deal{+n, +e, +s, +w}:
      Pos{hand.pack01(n), hand.pack23(n), hand.pack01(e), hand.pack23(e),
          hand.pack01(s), hand.pack23(s), hand.pack01(w), hand.pack23(w),
          trick.start(leader), 0}
