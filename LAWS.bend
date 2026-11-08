# LAWS.bend: what the solver promises. PROOF.bend proves each law.
#
# Some laws hold for all values by induction. Others are finite: they walk a whole
# domain with a decision procedure, such as "every 13-bit holding", and say that
# it answers True. The checker runs the procedure when it checks the proof, so
# the law holds for every value in that domain, not just for a sample of tests.
# Each comment says what the domain is, and calls it a sample when it is not the
# whole space. The specs and procedures are in SPEC.bend.

import Base
import ./src/cards.bend as C
import ./src/pbn.bend as P
import ./src/rules.bend as R
import ./src/search.bend as Z
import ./SPEC.bend as S

# ---------------------------------------------------------------------------
# PBN

# LAW: parsing a printed holding gives it back, for each of the 8192 holdings.
law holding_roundtrip:
  {S.holdings.ok(8192n, 0) == True{} : Bool}

# LAW: the same, as an equality for any holding number below 8192.
law holding_good:
  for +k: Nat
  for lt: {Nat.is_lt(k, 8192n) == True{} : Bool}
  S.Good(U32.from_nat(k))

# LAW: any four holdings below 8192 make a hand that round-trips.
law hand_good:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for la: {Nat.is_lt(a, 8192n) == True{} : Bool}
  for lb: {Nat.is_lt(b, 8192n) == True{} : Bool}
  for lc: {Nat.is_lt(c, 8192n) == True{} : Bool}
  for ld: {Nat.is_lt(d, 8192n) == True{} : Bool}
  S.Good.hand(C.Hand{U32.from_nat(a), U32.from_nat(b), U32.from_nat(c), U32.from_nat(d)})

# LAW: parsing a printed deal gives it back, for any deal whose hands round-trip
# (hand_good gives that for any real hand) and share no card.
law deal_roundtrip:
  for +n: C.Hand
  for +e: C.Hand
  for +s: C.Hand
  for +w: C.Hand
  for gn: S.Good.hand(n)
  for ge: S.Good.hand(e)
  for gs: S.Good.hand(s)
  for gw: S.Good.hand(w)
  for dj: {P.deal.disjoint(n, e, s, w) == True{} : Bool}
  {P.parse(P.print(C.Deal{n, e, s, w})) == Some{C.Deal{n, e, s, w}} : Maybe<&2, C.Deal>}

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

# ---------------------------------------------------------------------------
# Card equivalence

# LAW: the collapse keeps exactly the top card of each run of a hand's cards,
# where a run has no other card in play between its cards. So it drops only cards
# in the hand with a higher card of theirs next above, and adds nothing. This walks
# each of the 2187 ways to split the seven low ranks into out of play, in play
# elsewhere and in the hand, and the same for the seven high ranks.
law tops_low_ranks:
  {S.tops.walk(7n, 1, 0, 0) == True{} : Bool}

law tops_high_ranks:
  {S.tops.walk(7n, 64, 0, 0) == True{} : Bool}

# LAW: the same for each of the 8192 holdings with all 13 cards in play.
law tops_all_in_play:
  {S.tops.all(8192n, 0) == True{} : Bool}

# LAW: a hand with no cards in the suit tries none, for any cards in play.
law tops_void:
  for +live: U32
  {Z.tops(0, live) == 0 : U32}

# ---------------------------------------------------------------------------
# Target cutoffs

# LAW: the target cutoffs are sound. If the result will be somewhere from won to
# won + left, then a cut of 1 means it reaches the target and a cut of 2 means it
# does not. This covers every won and left adding up to at most 13, every target
# from 0 to 14, and every result in that range.
law cut_sound:
  {S.cut.all(14n, 0) == True{} : Bool}

# ---------------------------------------------------------------------------
# The driver

# LAW: the driver finds the result. Given answers that are true for targets up to
# v and false above it, it ends at v within the fuel Z.solve gives it. This covers
# every lo <= v <= hi up to 13 and every guess from 0 to 13.
law driver_finds:
  {S.driver.all(14n, 0) == True{} : Bool}

# ---------------------------------------------------------------------------
# Move generation

# LAW: the search tries exactly the top card of each run of the legal plays, each
# once, whatever order the weights put them in. This is a sample: all 5 strains, at
# each of the four places in a trick, on 20 random 3-card endings.
law gen_keeps_moves:
  {S.gen.all(20n, 1, 3) == True{} : Bool}

# ---------------------------------------------------------------------------
# Sure tricks

# LAW: the run behind quick tricks is the number of top cards in play that are in
# the hand, walking the ranks from the ace down. This covers each of the 2187 ways
# to split the seven low ranks, and the same for the seven high ranks.
law run_low_ranks:
  {S.run.walk(7n, 1, 0, 0) == True{} : Bool}

law run_high_ranks:
  {S.run.walk(7n, 64, 0, 0) == True{} : Bool}

# LAW: quick tricks never exceed the tricks the side on lead takes, and later tricks
# never exceed what its opponents take, by brute force. Only a sample, since the
# checker is slow at this: all 5 strains and 4 leaders of 4 random 2-card endings.
# tests/oracle and tools/check.py sure cover thousands more, up to whole deals.
law sure_never_exceeds:
  {S.sure.all(4n, 100, 2) == True{} : Bool}

# LAW: the same, for the rules taken from DDS that need more than two cards to come
# up: long suits, second cards across the partnership, voids and partner's ruff. Also
# only a sample, of 3-card endings.
law sure_three_cards:
  {S.sure.all(2n, 300, 3) == True{} : Bool}

# ---------------------------------------------------------------------------
# The search

# LAW: the search gives the same whole table as brute-force minimax, in all 5
# strains with all 4 leaders. Only a sample so far: the checker is slow at this, so
# it covers four random 2-card endings. tests/oracle.bend and tools/check.py cover
# thousands of larger ones.
law search_is_brute:
  {S.oracle.all(4n, 1, 2) == True{} : Bool}

# ---------------------------------------------------------------------------
# The transposition table

# LAW: an entry's count of top cards and the card it stands for are inverses: the
# ranks it gives back when it is found are the ones it would store. For every holding
# of the low 7 ranks and every count.
law ws_kth_inverse:
  {S.ws.kth.all(128n, 0) == True{} : Bool}

# LAW: run.below is the run of cards under a card, walking the cards in play, for
# every holding of the low 7 ranks with all of them in play, and with some gaps.
law run_below_all_live:
  {S.run.below.all(128n, 0, 127) == True{} : Bool}

law run_below_gaps:
  {S.run.below.all(128n, 0, 91) == True{} : Bool}

# LAW: tightening an entry's bounds with an answer makes it give that answer back,
# for every lo < need <= hi up to 13.
law bounds_give_back:
  {S.bounds.all(14n, 0) == True{} : Bool}

# LAW: owner words agree exactly on the top cards asked for, for every pair of two
# cards each, and for none, one or both of the cards.
law owners_agree:
  {S.agree.all(16n, 0) == True{} : Bool}

# ---------------------------------------------------------------------------
# The proof foundation

# LAW: the facts about holdings that the proofs need: popcount counts a holding, and
# its lowest card is in it, is one card that ctz finds, and taking it leaves a holding
# with one card fewer. Checked for each of the 8192 holdings, then for any number
# below 8192, then, by the laws below about words and numbers, for any holding.

law lt_dbl:
  for +x: Nat
  for +y: Nat
  for e: {Nat.is_lt(x, y) == True{} : Bool}
  {Nat.is_lt(Nat.double(x), Nat.double(y)) == True{} : Bool}

law lt_dbl1:
  for +x: Nat
  for +y: Nat
  for e: {Nat.is_lt(x, y) == True{} : Bool}
  {Nat.is_lt(1n+Nat.double(x), Nat.double(y)) == True{} : Bool}

law lt_one:
  for +x: Nat
  for e: {Nat.is_lt(x, 1n) == True{} : Bool}
  {Nat.is_lt(Nat.double(x), 1n) == True{} : Bool}

law pow2_pos:
  for +j: Nat
  {Nat.is_lt(0n, S.pow2(j)) == True{} : Bool}

law bound:
  for +n: Nat
  for +j: Nat
  for +w: Word(n)
  for e: {Word.and(n, w, S.ones(n, j)) == w : Word(n)}
  {Nat.is_lt(Word.to_nat(n, w), S.pow2(j)) == True{} : Bool}

law mask_ones:
  {(8191 : U32) == U32{S.ones(32n, 13n)} : U32}

law holding_lt:
  for +u: U32
  for h: {(u .&. 8191 : U32) == u : U32}
  {Nat.is_lt(U32.to_nat(u), 8192n) == True{} : Bool}

law facts_all:
  {S.facts.all(8192n, 0) == True{} : Bool}

law facts_nat:
  for +k: Nat
  for lt: {Nat.is_lt(k, 8192n) == True{} : Bool}
  {S.facts(U32.from_nat(k)) == True{} : Bool}

law facts_holding:
  for +u: U32
  for h: {(u .&. 8191 : U32) == u : U32}
  {S.facts(u) == True{} : Bool}

law card_code:
  for +s: Nat
  for +r: Nat
  for ls: {Nat.is_lt(s, 4n) == True{} : Bool}
  for lr: {Nat.is_lt(r, 13n) == True{} : Bool}
  {S.code.ok(s, r) == True{} : Bool}

# LAW: the word for a number, counted up from zero, is the word whose number it is:
# for words of any width, and so for every U32. Facts proved for holding numbers carry
# over to holdings this way.

law from_double:
  for +p: Nat
  for +k: Nat
  {S.W.from(1n+p, Nat.double(k)) == WCon{False{}, S.W.from(p, k)} : Word(1n+p)}

law from_odd:
  for +p: Nat
  for +k: Nat
  {S.W.from(1n+p, 1n+Nat.double(k)) == WCon{True{}, S.W.from(p, k)} : Word(1n+p)}

law from_zero_width:
  for +k: Nat
  {S.W.from(0n, k) == WNil{} : Word(0n)}

law from_to:
  for +n: Nat
  for w: Word(n)
  {S.W.from(n, Word.to_nat(n, w)) == w : Word(n)}

law u32_from:
  for +k: Nat
  {U32.from_nat(k) == U32{S.W.from(32n, k)} : U32}

law u32_roundtrip:
  for +u: U32
  {U32.from_nat(U32.to_nat(u)) == u : U32}
