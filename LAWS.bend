# LAWS.bend: what the solver promises. PROOF.bend proves each law.
#
# Many laws here are finite: they walk a whole domain with a decision procedure,
# such as "every 13-bit holding", and say that it answers True. The checker runs
# the procedure when it checks the proof, so the law holds for every value in
# that domain, not just for a sample of tests. Each comment says what the domain
# is, and calls it a sample when it is not the whole space.

import Base
import ./src/cards.bend as C
import ./src/pbn.bend as P
import ./src/rules.bend as R
import ./SPEC.bend as S

# ---------------------------------------------------------------------------
# PBN

def holding.ok.go(a: Maybe<&2, U32>, +m: U32) -> Bool:
  match a:
    case None{}:
      False{}
    case Some{x}:
      U32.is_eq(x, m)

def holding.ok(+m: U32) -> Bool:
  holding.ok.go(P.suit.parse(P.suit.print(m)), m)

def holdings.ok(n: Nat, +m: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(holding.ok(m), holdings.ok(p, (m + 1 : U32)))

# LAW: parsing a printed holding gives it back, for each of the 8192 holdings.
law holding_roundtrip:
  {holdings.ok(8192n, 0) == True{} : Bool}

# LAW: the deal's first hand goes to the seat its PBN letter names, and the rest
# follow clockwise.
law place_north:
  for +a: C.Hand
  for +b: C.Hand
  for +c: C.Hand
  for +d: C.Hand
  {P.deal.place(0n, a, b, c, d) == C.Deal{a, b, c, d} : C.Deal}

law place_east:
  for +a: C.Hand
  for +b: C.Hand
  for +c: C.Hand
  for +d: C.Hand
  {P.deal.place(1n, a, b, c, d) == C.Deal{d, a, b, c} : C.Deal}

law place_south:
  for +a: C.Hand
  for +b: C.Hand
  for +c: C.Hand
  for +d: C.Hand
  {P.deal.place(2n, a, b, c, d) == C.Deal{c, d, a, b} : C.Deal}

law place_west:
  for +a: C.Hand
  for +b: C.Hand
  for +c: C.Hand
  for +d: C.Hand
  {P.deal.place(3n, a, b, c, d) == C.Deal{b, c, d, a} : C.Deal}

# LAW: the seat letters read as 0..3 in clockwise order from North.
law seat_letters:
  {[P.seat.parse('N'), P.seat.parse('E'), P.seat.parse('S'), P.seat.parse('W'), P.seat.parse('X')] == [0, 1, 2, 3, 4] : List<&2, U32>}

# ---------------------------------------------------------------------------
# Cards

def card.ok(+s: U32, +r: U32) -> Bool:
  +c = C.card.make(s, r)
  U32.is_eq(C.card.suit(c), s) && U32.is_eq(C.card.rank(c), r) && U32.is_eq(C.card.bit(c), (1 << U32.to_nat(r) : U32))

def card.rank.ok(n: Nat, +s: U32, +r: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(card.ok(s, r), card.rank.ok(p, s, (r + 1 : U32)))

def card.suit.ok(n: Nat, +s: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(card.rank.ok(13n, s, 0), card.suit.ok(p, (s + 1 : U32)))

# LAW: a card code gives back its suit and rank, for each of the 52 cards.
law card_codes:
  {card.suit.ok(4n, 0) == True{} : Bool}

# ---------------------------------------------------------------------------
# Trick winner

# ---------------------------------------------------------------------------
# Trick winner

# LAW: beats agrees with the rules: a card beats the one winning the trick
# exactly when it has more power, where any trump outranks any card of the suit
# led and any other card has none. This covers every strain, every suit led,
# every card winning (of the suit led or a trump) and every card played.
law beats_rules:
  {S.beats.all(5n, 0) == True{} : Bool}

# LAW: after four cards the next trick is led by the seat the rules say won.
# This walks a sample of the 52^4 possible tricks: every way to play five cards
# (AS 2S AH 2H AC) with spades, clubs and no trumps, led by North.
law trick_winner_spades:
  {S.walk.a(S.pool(), 0, 0) == True{} : Bool}

law trick_winner_clubs:
  {S.walk.a(S.pool(), 3, 0) == True{} : Bool}

law trick_winner_nt:
  {S.walk.a(S.pool(), 4, 0) == True{} : Bool}

# ---------------------------------------------------------------------------
# Legal plays

# LAW: moves of a holding lists each of its cards once, highest first, for each
# of the 8192 holdings. Suit is a label here, so the law checks spades.
law moves_holding:
  {S.moves.holdings.ok(8192n, 0, 0) == True{} : Bool}

# LAW: on lead, every card of a hand is legal, for any hand.
law moves_on_lead:
  for +h01: U32
  for +h23: U32
  {R.moves.of(R.none(), h01, h23) == R.moves.all(h01, h23) : List<&2, U32>}

# LAW: with a card of the suit led, only that suit is legal, for any hand.
law moves_follow_spades:
  for +h01: U32
  for +h23: U32
  for e: {U32.is_zero((h01 >> 16n : U32)) == False{} : Bool}
  {R.moves.of(0, h01, h23) == R.moves.suit(0, (h01 >> 16n : U32), Nil{}) : List<&2, U32>}

law moves_follow_hearts:
  for +h01: U32
  for +h23: U32
  for e: {U32.is_zero((h01 .&. 65535 : U32)) == False{} : Bool}
  {R.moves.of(1, h01, h23) == R.moves.suit(1, (h01 .&. 65535 : U32), Nil{}) : List<&2, U32>}

law moves_follow_diamonds:
  for +h01: U32
  for +h23: U32
  for e: {U32.is_zero((h23 >> 16n : U32)) == False{} : Bool}
  {R.moves.of(2, h01, h23) == R.moves.suit(2, (h23 >> 16n : U32), Nil{}) : List<&2, U32>}

law moves_follow_clubs:
  for +h01: U32
  for +h23: U32
  for e: {U32.is_zero((h23 .&. 65535 : U32)) == False{} : Bool}
  {R.moves.of(3, h01, h23) == R.moves.suit(3, (h23 .&. 65535 : U32), Nil{}) : List<&2, U32>}

# LAW: void in the suit led, every card is legal, for any hand.
law moves_void_spades:
  for +h01: U32
  for +h23: U32
  for e: {U32.is_zero((h01 >> 16n : U32)) == True{} : Bool}
  {R.moves.of(0, h01, h23) == R.moves.all(h01, h23) : List<&2, U32>}

law moves_void_hearts:
  for +h01: U32
  for +h23: U32
  for e: {U32.is_zero((h01 .&. 65535 : U32)) == True{} : Bool}
  {R.moves.of(1, h01, h23) == R.moves.all(h01, h23) : List<&2, U32>}

law moves_void_diamonds:
  for +h01: U32
  for +h23: U32
  for e: {U32.is_zero((h23 >> 16n : U32)) == True{} : Bool}
  {R.moves.of(2, h01, h23) == R.moves.all(h01, h23) : List<&2, U32>}

law moves_void_clubs:
  for +h01: U32
  for +h23: U32
  for e: {U32.is_zero((h23 .&. 65535 : U32)) == True{} : Bool}
  {R.moves.of(3, h01, h23) == R.moves.all(h01, h23) : List<&2, U32>}
