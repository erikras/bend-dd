# cards.bend: the card encoding shared by the whole solver.
#
# Seats are 0=North 1=East 2=South 3=West. Suits are 0=spades 1=hearts
# 2=diamonds 3=clubs, and strain 4 is no trumps, the order DDS uses for strains.
# A holding is a 13-bit mask of ranks: bit 12 is the ace and bit 0 is the deuce,
# so a higher bit is a higher card. A single card is one U32, suit << 4 | rank,
# so two cards of one suit compare as plain numbers.

import Base

type Hand is Data:
  Hand{s: U32, h: U32, d: U32, c: U32}

type Deal is Data:
  Deal{n: Hand, e: Hand, s: Hand, w: Hand}

def hand.empty() -> Hand:
  Hand{0, 0, 0, 0}

# The holding of one suit. A suit past 3 reads as clubs.
def hand.suit(suit: Nat, h: Hand) -> U32:
  match suit h:
    case 0n Hand{s, _, _, _}:
      s
    case 1n Hand{_, x, _, _}:
      x
    case 2n Hand{_, _, d, _}:
      d
    case _ Hand{_, _, _, c}:
      c

# Adds a mask of cards to one suit of a hand.
def hand.add(suit: Nat, +bits: U32, h: Hand) -> Hand:
  match suit h:
    case 0n Hand{s, x, d, c}:
      Hand{(s .|. bits : U32), x, d, c}
    case 1n Hand{s, x, d, c}:
      Hand{s, (x .|. bits : U32), d, c}
    case 2n Hand{s, x, d, c}:
      Hand{s, x, (d .|. bits : U32), c}
    case _ Hand{s, x, d, c}:
      Hand{s, x, d, (c .|. bits : U32)}

def deal.empty() -> Deal:
  Deal{hand.empty(), hand.empty(), hand.empty(), hand.empty()}

# The hand of one seat. A seat past 3 reads as West.
def deal.hand(seat: Nat, d: Deal) -> Hand:
  match seat d:
    case 0n Deal{n, _, _, _}:
      n
    case 1n Deal{_, e, _, _}:
      e
    case 2n Deal{_, _, s, _}:
      s
    case _ Deal{_, _, _, w}:
      w

# Adds a mask of cards to one suit of one seat.
def deal.add(seat: Nat, suit: Nat, +bits: U32, d: Deal) -> Deal:
  match seat d:
    case 0n Deal{n, e, s, w}:
      Deal{hand.add(suit, bits, n), e, s, w}
    case 1n Deal{n, e, s, w}:
      Deal{n, hand.add(suit, bits, e), s, w}
    case 2n Deal{n, e, s, w}:
      Deal{n, e, hand.add(suit, bits, s), w}
    case _ Deal{n, e, s, w}:
      Deal{n, e, s, hand.add(suit, bits, w)}

# The number of cards in a holding, as a U32.
def bits.count(m: U32) -> U32:
  U32.from_nat(U32.popcount(m))

def hand.count(h: Hand) -> U32:
  match h:
    case Hand{s, x, d, c}:
      (bits.count(s) + bits.count(x) + bits.count(d) + bits.count(c) : U32)

# The cards two hands share, suit by suit, as one number that is 0 when the
# hands are disjoint.
def hand.overlap(a: Hand, b: Hand) -> U32:
  match a b:
    case Hand{s1, h1, d1, c1} Hand{s2, h2, d2, c2}:
      ((s1 .&. s2 : U32) .|. (h1 .&. h2 : U32) .|. (d1 .&. d2 : U32) .|. (c1 .&. c2 : U32) : U32)

# ---------------------------------------------------------------------------
# Single cards

def card.make(+suit: U32, +rank: U32) -> U32:
  ((suit << 4n : U32) .|. rank : U32)

def card.suit(+c: U32) -> U32:
  (c >> 4n : U32)

def card.rank(+c: U32) -> U32:
  (c .&. 15 : U32)

# The card as a one-bit holding.
def card.bit(+c: U32) -> U32:
  (1 << U32.to_nat((c .&. 15 : U32)) : U32)
