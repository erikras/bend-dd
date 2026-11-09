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
import ./src/brute.bend as B
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

# ---------------------------------------------------------------------------
# Words as sets of bits
#
# Sub(a, b) says every bit of a is in b. These carry a card from a holding to the word
# of a hand, count the cards left when one is taken, and keep hands valid.

# The bits of a and k are in a.
law and_sub_left:
  for +n: Nat
  for +a: Word(n)
  for +k: Word(n)
  S.Sub(n, Word.and(n, a, k), a)


law sub_trans:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Word(n)
  for +ab: S.Sub(n, a, b)
  for +bc: S.Sub(n, b, c)
  S.Sub(n, a, c)


law count0_zero:
  for +n: Nat
  for +x: Word(n)
  for e: {S.word.count(n, x) == 0n : Nat}
  {x == Word.zero(n) : Word(n)}


law xor_zero:
  for +n: Nat
  for +w: Word(n)
  {Word.xor(n, w, Word.zero(n)) == w : Word(n)}


# Taking one bit that is in w leaves one fewer.
law count_xor:
  for +n: Nat
  for +x: Word(n)
  for +w: Word(n)
  for s: S.Sub(n, x, w)
  for one: {S.word.count(n, x) == 1n : Nat}
  {S.word.count(n, w) == 1n+S.word.count(n, Word.xor(n, w, x)) : Nat}


# If a is under w shifted down, a shifted up is under w.
law shl_sub:
  for +n: Nat
  for +a: Word(n)
  for +w: Word(n)
  for h: S.Sub(n, a, Word.shr(n, w))
  S.Sub(n, Word.shl(n, a), w)


law shl_sub32:
  for +a: U32
  for +w: U32
  for h: S.Sub32(a, U32.shr(w))
  S.Sub32(U32.shl(a), w)


law shln_comm:
  for +a: U32
  for +k: Nat
  {U32.shln(U32.shl(a), k) == U32.shl(U32.shln(a, k)) : U32}


# If a is under w shifted down k times, a shifted up k times is under w.
law shln_sub:
  for +k: Nat
  for +a: U32
  for +w: U32
  for h: S.Sub32(a, U32.shrn(w, k))
  S.Sub32(U32.shln(a, k), w)


# LAW: >> by 16 is U32.shrn, as the code writes it.
law shr_op:
  for +x: U32
  {(x >> 16n : U32) == U32.shrn(x, 16n) : U32}


# Taking bits of w out of w keeps it under m.
law xor_sub:
  for +n: Nat
  for +w: Word(n)
  for +x: Word(n)
  for +m: Word(n)
  for +wm: S.Sub(n, w, m)
  for +xw: S.Sub(n, x, w)
  S.Sub(n, Word.xor(n, w, x), m)


law and_mono:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +k: Word(n)
  for +h: S.Sub(n, a, b)
  S.Sub(n, Word.and(n, a, k), Word.and(n, b, k))


law pad_mono:
  for +p: Nat
  for +a: Word(p)
  for +b: Word(p)
  for +h: S.Sub(p, a, b)
  S.Sub(1n+p, Word.shr.pad(p, a), Word.shr.pad(p, b))


law shr_mono:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +h: S.Sub(n, a, b)
  S.Sub(n, Word.shr(n, a), Word.shr(n, b))


law shrn_mono:
  for +k: Nat
  for +a: U32
  for +b: U32
  for +h: S.Sub32(a, b)
  S.Sub32(U32.shrn(a, k), U32.shrn(b, k))


law and_mono32:
  for +a: U32
  for +b: U32
  for +k: U32
  for +h: S.Sub32(a, b)
  S.Sub32(U32.and(a, k), U32.and(b, k))


law hi_holding:
  for +w: U32
  for +h: S.Sub32(w, S.valid.mask())
  S.Sub32(U32.shrn(w, 16n), 8191)


law lo_holding:
  for +w: U32
  for +h: S.Sub32(w, S.valid.mask())
  S.Sub32(U32.and(w, 65535), 8191)


law pad_ones:
  for +p: Nat
  for +x: Word(p)
  for +j: Nat
  {Word.and(1n+p, Word.shr.pad(p, x), S.ones(1n+p, j)) == Word.shr.pad(p, Word.and(p, x, S.ones(p, j))) : Word(1n+p)}


law pad_inj:
  for +p: Nat
  for +x: Word(p)
  for +y: Word(p)
  for +e: {Word.shr.pad(p, x) == Word.shr.pad(p, y) : Word(1n+p)}
  {x == y : Word(p)}


# With w shifted down under the first j bits, w is under the first j + 1.
law shr_ones:
  for +n: Nat
  for +w: Word(n)
  for +j: Nat
  for +h: S.Sub(n, Word.shr(n, w), S.ones(n, j))
  S.Sub(n, w, S.ones(n, 1n+j))


# A zero word is under anything, here under no bits at all.
law zero_ones:
  for +n: Nat
  for +w: Word(n)
  for +z: {w == Word.zero(n) : Word(n)}
  S.Sub(n, w, S.ones(n, 0n))


law shrn_comm:
  for +a: U32
  for +k: Nat
  {U32.shrn(U32.shr(a), k) == U32.shr(U32.shrn(a, k)) : U32}


law shrn_zero:
  for +k: Nat
  for +w: U32
  for +z: {U32.shrn(w, k) == 0 : U32}
  S.Sub32.ones(w, k)


# A word with nothing in its low 16 bits and nothing above them is zero.
law split_zero:
  for +w: U32
  for +z1: {U32.shrn(w, 16n) == 0 : U32}
  for +z2: {U32.and(w, 65535) == 0 : U32}
  {w == 0 : U32}


# Words that compare as equal are equal.
law cmp_eq:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +e: {Word.cmp(n, a, b) == EQ{} : Cmp}
  {a == b : Word(n)}


# U32.is_eq saying yes means the words are the same.
law u32_eq:
  for +a: U32
  for +b: U32
  for e: {U32.is_eq(a, b) == True{} : Bool}
  {a == b : U32}


law and_sub32:
  for +a: U32
  for +k: U32
  S.Sub32(U32.and(a, k), a)


law sub_trans32:
  for +a: U32
  for +b: U32
  for +c: U32
  for +ab: S.Sub32(a, b)
  for +bc: S.Sub32(b, c)
  S.Sub32(a, c)


law count_xor32:
  for +x: U32
  for +w: U32
  for +s: S.Sub32(x, w)
  for +one: {S.bits(x) == 1n : Nat}
  {S.bits(w) == 1n+S.bits(U32.xor(w, x)) : Nat}


law xor_sub32:
  for +w: U32
  for +x: U32
  for +m: U32
  for +wm: S.Sub32(w, m)
  for +xw: S.Sub32(x, w)
  S.Sub32(U32.xor(w, x), m)


# ---------------------------------------------------------------------------
# Moves
#
# Every legal move from a valid hand is a card in it, where R.play takes it from, and
# a hand with a card has a legal move, whatever was led.

law and_self:
  for +n: Nat
  for +w: Word(n)
  S.Sub(n, w, w)


law card_bit:
  for +s: Nat
  for +r: Nat
  for ls: {Nat.is_lt(s, 4n) == True{} : Bool}
  for lr: {Nat.is_lt(r, 13n) == True{} : Bool}
  {S.cb.ok(s, r) == True{} : Bool}


law one_bit:
  for +r: Nat
  for lr: {Nat.is_lt(r, 13n) == True{} : Bool}
  {S.one.ok(r) == True{} : Bool}


# Every card the peel gives, beyond those of acc, is of suit s and in the holding.
law peel_sound:
  for n: Nat
  for z: Bool
  for +s: Nat
  for +m: U32
  for acc: List<&2, U32>
  for +m0: U32
  for +ls: {Nat.is_lt(s, 4n) == True{} : Bool}
  for +zf: {z == U32.is_eq(m, 0) : Bool}
  for +hm: S.Sub32(m, 8191)
  for +sm: S.Sub32(m, m0)
  for ok: S.All(acc, U32.from_nat(s), m0)
  S.All(R.moves.peel(n, z, U32.from_nat(s), m, acc), U32.from_nat(s), m0)


# The same, for the hand: every card the peel gives is in the hand, as play takes it.
law peel_hand:
  for n: Nat
  for z: Bool
  for +s: Nat
  for +m: U32
  for acc: List<&2, U32>
  for +h01: U32
  for +h23: U32
  for +ls: {Nat.is_lt(s, 4n) == True{} : Bool}
  for +zf: {z == U32.is_eq(m, 0) : Bool}
  for +hm: S.Sub32(m, 8191)
  for +sm: S.Sub32(m, R.suit.mask(s, h01, h23))
  for ok: S.AllH(acc, h01, h23)
  S.AllH(R.moves.peel(n, z, U32.from_nat(s), m, acc), h01, h23)


# Every card of a valid hand that moves.all gives is in the hand.
law all_hand:
  for +h01: U32
  for +h23: U32
  for +v01: S.Sub32(h01, S.valid.mask())
  for +v23: S.Sub32(h23, S.valid.mask())
  S.AllH(R.moves.all(h01, h23), h01, h23)


# Every legal move from a valid hand is a card in it, whatever was led.
law moves_hand:
  for +lead: U32
  for +h01: U32
  for +h23: U32
  for +v01: S.Sub32(h01, S.valid.mask())
  for +v23: S.Sub32(h23, S.valid.mask())
  S.AllH(R.moves.of(lead, h01, h23), h01, h23)


law peel_ne_acc:
  for n: Nat
  for z: Bool
  for +s: U32
  for +m: U32
  for acc: List<&2, U32>
  for ne: S.NE(acc)
  S.NE(R.moves.peel(n, z, s, m, acc))


# A suit with a card gives a move.
law suit_ne:
  for +s: U32
  for +m: U32
  for acc: List<&2, U32>
  for +e: {U32.is_zero(m) == False{} : Bool}
  S.NE(R.moves.suit(s, m, acc))


# A hand with a card has a move, whatever was led.
law moves_ne01:
  for +lead: U32
  for +h01: U32
  for +h23: U32
  for +e: {U32.is_zero(h01) == False{} : Bool}
  S.NE(R.moves.of(lead, h01, h23))


law moves_ne23:
  for +lead: U32
  for +h01: U32
  for +h23: U32
  for +e: {U32.is_zero(h23) == False{} : Bool}
  S.NE(R.moves.of(lead, h01, h23))


# ---------------------------------------------------------------------------
# The trick word

law and_assoc:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Word(n)
  {Word.and(n, Word.and(n, a, b), c) == Word.and(n, a, Word.and(n, b, c)) : Word(n)}

law and_assoc32:
  for +a: U32
  for +b: U32
  for +c: U32
  {U32.and(U32.and(a, b), c) == U32.and(a, U32.and(b, c)) : U32}

law pad_and:
  for +p: Nat
  for +a: Word(p)
  for +b: Word(p)
  {Word.shr.pad(p, Word.and(p, a, b)) == Word.and(1n+p, Word.shr.pad(p, a), Word.shr.pad(p, b)) : Word(1n+p)}

law shr_and:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.shr(n, Word.and(n, a, b)) == Word.and(n, Word.shr(n, a), Word.shr(n, b)) : Word(n)}

law shrn_and:
  for +k: Nat
  for +a: U32
  for +b: U32
  {U32.shrn(U32.and(a, b), k) == U32.and(U32.shrn(a, k), U32.shrn(b, k)) : U32}

law seat_low:
  for +x: U32
  {R.trick.seat(x) == R.trick.seat((x .&. 15 : U32)) : U32}

law played_low:
  for +x: U32
  {R.trick.played(x) == R.trick.played((x .&. 15 : U32)) : U32}

law put_and:
  for +p: Nat
  for +c: Bool
  for +at: Word(p)
  for +kt: Word(p)
  {Word.and(p, Word.shl.put(p, c, at), kt) == Word.shl.put(p, Bool.and(c, S.w0(p, kt)), Word.and(p, at, Word.shr(p, kt))) : Word(p)}

law shl_and:
  for +n: Nat
  for +z: Word(n)
  for +k: Word(n)
  {Word.and(n, Word.shl(n, z), k) == Word.shl(n, Word.and(n, z, Word.shr(n, k))) : Word(n)}

law or_and:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +k: Word(n)
  {Word.and(n, Word.or(n, a, b), k) == Word.or(n, Word.and(n, a, k), Word.and(n, b, k)) : Word(n)}

law or_zero:
  for +n: Nat
  for +a: Word(n)
  {Word.or(n, a, Word.zero(n)) == a : Word(n)}

law shl2_low:
  for +z: U32
  {U32.and(U32.shl(U32.shl(z)), 3) == 0 : U32}

law shl4_low:
  for +z: U32
  {U32.and(U32.shl(U32.shl(U32.shl(U32.shl(z)))), 15) == 0 : U32}

law kill4:
  for +x: U32
  for +z: U32
  {U32.and(U32.or(x, U32.shl(U32.shl(U32.shl(U32.shl(z))))), 15) == U32.and(x, 15) : U32}

law low4_make:
  for +s: U32
  for +p: U32
  for +l: U32
  for +o: U32
  for +b: U32
  {U32.and(R.trick.make(s, p, l, o, b), 15) == U32.and(U32.or(s, U32.shl(U32.shl(p))), 15) : U32}

law seat_make:
  for +s: U32
  for +p: U32
  for +l: U32
  for +o: U32
  for +b: U32
  {R.trick.seat(R.trick.make(s, p, l, o, b)) == U32.and(s, 3) : U32}

law played_make:
  for +k: Nat
  for +lk: {Nat.is_lt(k, 4n) == True{} : Bool}
  for +y: U32
  for +l: U32
  for +o: U32
  for +b: U32
  {R.trick.played(R.trick.make(U32.and(y, 3), U32.from_nat(k), l, o, b)) == U32.from_nat(k) : U32}

law seat_make_r:
  for +s: U32
  for +p: U32
  for +l: U32
  for +o: U32
  for +b: U32
  for +r: U32
  {R.trick.seat(U32.or(R.trick.make(s, p, l, o, b), (r << 15n : U32))) == U32.and(s, 3) : U32}

law played_make_r:
  for +k: Nat
  for +lk: {Nat.is_lt(k, 4n) == True{} : Bool}
  for +y: U32
  for +l: U32
  for +o: U32
  for +b: U32
  for +r: U32
  {R.trick.played(U32.or(R.trick.make(U32.and(y, 3), U32.from_nat(k), l, o, b), (r << 15n : U32))) == U32.from_nat(k) : U32}

law next_seat:
  for +k: Nat
  for +lk: {Nat.is_lt(k, 3n) == True{} : Bool}
  for +win: Bool
  for +rank: Bool
  for +seat: U32
  for +lead: U32
  for +owner: U32
  for +best: U32
  for +c: U32
  {R.trick.seat(R.trick.next.go(U32.is_eq(U32.from_nat(k), 0), U32.is_eq(U32.from_nat(k), 3), win, rank, seat, U32.from_nat(k), lead, owner, best, c)) == U32.and((seat + 1 : U32), 3) : U32}

law next_played:
  for +k: Nat
  for +lk: {Nat.is_lt(k, 3n) == True{} : Bool}
  for +win: Bool
  for +rank: Bool
  for +seat: U32
  for +lead: U32
  for +owner: U32
  for +best: U32
  for +c: U32
  {R.trick.played(R.trick.next.go(U32.is_eq(U32.from_nat(k), 0), U32.is_eq(U32.from_nat(k), 3), win, rank, seat, U32.from_nat(k), lead, owner, best, c)) == U32.from_nat(1n+k) : U32}

law next_end:
  for +win: Bool
  for +rank: Bool
  for +y1: U32
  for +lead: U32
  for +y2: U32
  for +best: U32
  for +c: U32
  {R.trick.played(R.trick.next.go(False{}, True{}, win, rank, U32.and(y1, 3), 3, lead, U32.and(y2, 3), best, c)) == 0 : U32}

law cmp_dbl:
  for +a: Bool
  for +b: Bool
  for +x: Nat
  for +y: Nat
  {Nat.cmp(S.bitnat(a, x), S.bitnat(b, y)) == Word.cmp.fin(a, b, Nat.cmp(x, y)) : Cmp}

law cmp_nat:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.cmp(n, a, b) == Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) : Cmp}

law u32_cmp_nat:
  for +a: U32
  for +b: U32
  {U32.cmp(a, b) == Nat.cmp(U32.to_nat(a), U32.to_nat(b)) : Cmp}

law adc00:
  for +n: Nat
  for +w: Word(n)
  {Word.adc(n, w, Word.zero(n), False{}, False{}) == w : Word(n)}

law adc01:
  for +n: Nat
  for +w: Word(n)
  {Word.adc(n, w, Word.zero(n), False{}, True{}) == Word.inc(n, w) : Word(n)}

law add_one:
  for +u: U32
  {U32.add(u, 1) == U32.inc(u) : U32}

law add_zero32:
  for +u: U32
  {U32.add(u, 0) == u : U32}

law side_seat:
  for +x: U32
  {U32.and(x, 1) == U32.and(R.trick.seat(x), 1) : U32}


# ---------------------------------------------------------------------------
# Hands stay even, and the value bounds

law le_refl:
  for +a: Nat
  {Nat.is_le(a, a) == True{} : Bool}

law le_zero:
  for +a: Nat
  {Nat.is_le(0n, a) == True{} : Bool}

law le_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for x: {Nat.is_le(a, b) == True{} : Bool}
  for y: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_le(a, c) == True{} : Bool}

law le_succ:
  for +a: Nat
  for +b: Nat
  for x: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(a, 1n+b) == True{} : Bool}

law le_add:
  for +a: Nat
  for +b: Nat
  {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}

law add_zero:
  for +a: Nat
  {Nat.add(a, 0n) == a : Nat}

law add_succ:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

law lt_le:
  for +m: Nat
  for +n: Nat
  for e: {Cmp.is_lt(Nat.cmp(m, n)) == True{} : Bool}
  {Nat.is_le(m, n) == True{} : Bool}

law nlt_le:
  for +m: Nat
  for +n: Nat
  for e: {Cmp.is_lt(Nat.cmp(m, n)) == False{} : Bool}
  {Nat.is_le(n, m) == True{} : Bool}

law max_le:
  for +a: U32
  for +b: U32
  for +hi: Nat
  for +ha: {Nat.is_le(U32.to_nat(a), hi) == True{} : Bool}
  for +hb: {Nat.is_le(U32.to_nat(b), hi) == True{} : Bool}
  {Nat.is_le(U32.to_nat(U32.max(a, b)), hi) == True{} : Bool} & {Nat.is_le(U32.to_nat(b), U32.to_nat(U32.max(a, b))) == True{} : Bool}

law min_ge:
  for +a: U32
  for +b: U32
  for +lo: Nat
  for +la: {Nat.is_le(lo, U32.to_nat(a)) == True{} : Bool}
  for +lb: {Nat.is_le(lo, U32.to_nat(b)) == True{} : Bool}
  {Nat.is_le(lo, U32.to_nat(U32.min(a, b))) == True{} : Bool} & {Nat.is_le(U32.to_nat(U32.min(a, b)), U32.to_nat(b)) == True{} : Bool}

law ok_in:
  for +ns: Bool
  for +v: U32
  for +w: Nat
  for +L: Nat
  for +i: S.InR(v, w, L)
  S.Ok(ns, v, w, L)

law ok_better:
  for +ns: Bool
  for +a: U32
  for +b: U32
  for +w: Nat
  for +L: Nat
  for oa: S.Ok(ns, a, w, L)
  for ob: S.Ok(ns, b, w, L)
  S.Ok(ns, B.better(ns, a, b), w, L)

law in_better:
  for +ns: Bool
  for +a: U32
  for +b: U32
  for +w: Nat
  for +L: Nat
  for +oa: S.Ok(ns, a, w, L)
  for +ib: S.InR(b, w, L)
  S.InR(B.better(ns, a, b), w, L)

law ok_seed:
  for +ns: Bool
  for +w: Nat
  for +L: Nat
  for +h: {Nat.is_le(Nat.add(w, L), 13n) == True{} : Bool}
  S.Ok(ns, B.seed(ns), w, L)

law xor0:
  for +h: U32
  {U32.xor(h, 0) == h : U32}

law one_bit16:
  for +r: Nat
  for lr: {Nat.is_lt(r, 13n) == True{} : Bool}
  {S.one16.ok(r) == True{} : Bool}

law x_one:
  for +c: U32
  for +s: Nat
  for +r: Nat
  for +ls: {Nat.is_lt(s, 4n) == True{} : Bool}
  for +lr: {Nat.is_lt(r, 13n) == True{} : Bool}
  for +es: {C.card.suit(c) == U32.from_nat(s) : U32}
  for +eb: {C.card.bit(c) == (1 << r : U32) : U32}
  {S.bits(S.play.x(c)) == 1n : Nat}

law and3_lt:
  for +x: U32
  {Nat.is_lt(U32.to_nat(U32.and(x, 3)), 4n) == True{} : Bool}

law seat_mid:
  for +k: Nat
  for +lk: {Nat.is_lt(k, 3n) == True{} : Bool}
  for +tr: U32
  for +t: U32
  for +c: U32
  for +ep: {R.trick.played(tr) == U32.from_nat(k) : U32}
  {R.trick.seat(R.trick.next(tr, t, c)) == U32.and((R.trick.seat(tr) + 1 : U32), 3) : U32}

law played_mid:
  for +k: Nat
  for +lk: {Nat.is_lt(k, 3n) == True{} : Bool}
  for +tr: U32
  for +t: U32
  for +c: U32
  for +ep: {R.trick.played(tr) == U32.from_nat(k) : U32}
  {R.trick.played(R.trick.next(tr, t, c)) == U32.from_nat(1n+k) : U32}

law played_end:
  for +tr: U32
  for +t: U32
  for +c: U32
  for +ep: {R.trick.played(tr) == 3 : U32}
  {R.trick.played(R.trick.next(tr, t, c)) == 0 : U32}

law won_mid:
  for +k: Nat
  for +lk: {Nat.is_lt(k, 3n) == True{} : Bool}
  for +x: U32
  for +won: U32
  for +e: {R.trick.played(x) == U32.from_nat(1n+k) : U32}
  {R.won.next(x, won) == won : U32}

law tn14:
  for +n: Nat
  for lt: {Nat.is_lt(n, 14n) == True{} : Bool}
  {U32.to_nat(U32.from_nat(n)) == n : Nat}

law add_bit:
  for +u: U32
  for +b: Bool
  for +lt: {Nat.is_lt(U32.to_nat(u), 13n) == True{} : Bool}
  {U32.to_nat((u + Bool.to_u32(b) : U32)) == Nat.add(S.b2n(b), U32.to_nat(u)) : Nat}

law won_end:
  for +x: U32
  for +won: U32
  for +e: {R.trick.played(x) == 0 : U32}
  for +lt: {Nat.is_lt(U32.to_nat(won), 13n) == True{} : Bool}
  {U32.to_nat(R.won.next(x, won)) == Nat.add(S.b2n(U32.is_eq((x .&. 1 : U32), 0)), U32.to_nat(won)) : Nat}

law le_lt:
  for +a: Nat
  for +b: Nat
  for e: {Nat.is_le(1n+a, b) == True{} : Bool}
  {Nat.is_lt(a, b) == True{} : Bool}

law le_lt_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for x: {Nat.is_le(a, b) == True{} : Bool}
  for y: {Nat.is_lt(b, c) == True{} : Bool}
  {Nat.is_lt(a, c) == True{} : Bool}

law d_end:
  for +p: Nat
  for +L: Nat
  for +x: Nat
  for +e1: {1n+x == L : Nat}
  for +ed: {4n+p == S.r4(L) : Nat}
  {p == S.r4(S.pred(L)) : Nat}

law w_end:
  for +bb: Bool
  for +w: Nat
  for +L: Nat
  for +x: Nat
  for +e1: {1n+x == L : Nat}
  for +h: {Nat.is_le(Nat.add(w, L), 13n) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.add(S.b2n(bb), w), S.pred(L)), 13n) == True{} : Bool}

law w_lt:
  for +w: Nat
  for +L: Nat
  for +x: Nat
  for +e1: {1n+x == L : Nat}
  for +h: {Nat.is_le(Nat.add(w, L), 13n) == True{} : Bool}
  {Nat.is_lt(w, 13n) == True{} : Bool}

law play_inv:
  for +t: U32
  for +c: U32
  for +p: Nat
  for +L: Nat
  for +n01: U32
  for +n23: U32
  for +e01: U32
  for +e23: U32
  for +s01: U32
  for +s23: U32
  for +w01: U32
  for +w23: U32
  for +tr: U32
  for +won: U32
  for +inv: S.Inv.go(n01, n23, e01, e23, s01, s23, w01, w23, U32.to_nat(R.trick.seat(tr)), U32.to_nat(R.trick.played(tr)), U32.to_nat(won), 1n+p, L)
  for +i1: S.Sub32(S.play.a(c), R.pick(U32.to_nat(R.trick.seat(tr)), n01, e01, s01, w01))
  for +i2: S.Sub32(S.play.b(c), R.pick(U32.to_nat(R.trick.seat(tr)), n23, e23, s23, w23))
  for +one: {S.bits(S.play.x(c)) == 1n : Nat}
  S.Inv(R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c), p, S.lnext(U32.to_nat(R.trick.played(tr)), L))

law even_self:
  for +s: Nat
  for +k: Nat
  for +L: Nat
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for +ev: S.Even(s, k, L, a, b, c, d)
  for +ls: {Nat.is_lt(s, 4n) == True{} : Bool}
  for +lk: {Nat.is_lt(k, 4n) == True{} : Bool}
  {S.pickn(s, a, b, c, d) == L : Nat}

law ne_cnt:
  for +lead: U32
  for +h01: U32
  for +h23: U32
  for +x: Nat
  for +e: {S.cnt(h01, h23) == 1n+x : Nat}
  S.NE(R.moves.of(lead, h01, h23))

law kid_hand:
  for +pos: R.Pos
  for +p: Nat
  for +L: Nat
  for +ci: S.Inv(pos, p, L)
  S.AllH(R.moves(pos), S.hand01(pos), S.hand23(pos))

law kid_h:
  for +pos: R.Pos
  for +p: Nat
  for +L: Nat
  for +ci: S.Inv(pos, p, L)
  {Nat.is_le(Nat.add(S.wN(pos), L), 13n) == True{} : Bool}

law kid_vin:
  for +pos: R.Pos
  for +p: Nat
  for +L: Nat
  for +ns: Bool
  for +ci: S.Inv(pos, p, L)
  S.NeIn(p, R.moves(pos), ns, B.seed(ns), S.wN(pos), L)

law widen_end:
  for +x: U32
  for +bb: Bool
  for +w: Nat
  for +L: Nat
  for +y: Nat
  for +e1: {1n+y == L : Nat}
  for +i: S.InR(x, Nat.add(S.b2n(bb), w), S.pred(L))
  S.InR(x, w, L)

law search_in:
  for +d: Nat
  for ms: List<&2, U32>
  for +t: U32
  for +pos: R.Pos
  for +ns: Bool
  for +best: U32
  for r: B.Res
  for +L: Nat
  for +inv: S.Inv(pos, d, L)
  for hand: S.AllH(ms, S.hand01(pos), S.hand23(pos))
  for +bok: S.Ok(ns, best, S.wN(pos), L)
  for vin: S.NeIn(d, ms, ns, S.rv(r), S.wN(pos), L)
  S.InR(S.rv(B.search(d, ms, t, pos, ns, best, r)), S.wN(pos), L)

law solve_in:
  for +d: Nat
  for +t: U32
  for +pos: R.Pos
  for +nodes: Nat
  for +L: Nat
  for +inv: S.Inv(pos, d, L)
  S.InR(S.rv(B.solve(d, t, pos, nodes)), S.wN(pos), L)

law start_inv:
  for +deal: C.Deal
  for +leader: U32
  for +L: Nat
  for +ok: S.DealOk(deal, L)
  for +el: {U32.and(leader, 3) == leader : U32}
  for +lL: {Nat.is_le(L, 13n) == True{} : Bool}
  S.Inv(R.pos.start(deal, leader), S.r4(L), L)

law solve_deal:
  for +deal: C.Deal
  for +leader: U32
  for +L: Nat
  for +t: U32
  for +nodes: Nat
  for +ok: S.DealOk(deal, L)
  for +el: {U32.and(leader, 3) == leader : U32}
  for +lL: {Nat.is_le(L, 13n) == True{} : Bool}
  S.InR(S.rv(B.solve(S.r4(L), t, R.pos.start(deal, leader), nodes)), 0n, L)


# ---------------------------------------------------------------------------
# The lowest card of a holding, by induction
#
# These replace the pass over every holding for the laws about moves, so they and
# the value bounds on top of them can go through the kernel.

law sub_not:
  for +n: Nat
  for +w: Word(n)
  {Word.adc(n, Word.zero(n), w, True{}, False{}) == Word.not(n, w) : Word(n)}

law and_not:
  for +n: Nat
  for +w: Word(n)
  {Word.and(n, w, Word.not(n, w)) == Word.zero(n) : Word(n)}

law low_unit:
  for +n: Nat
  for +w: Word(n)
  {Word.and(n, w, Word.adc(n, Word.zero(n), w, True{}, True{})) == S.unit(n, S.lsb(n, w)) : Word(n)}

law lsb_lt:
  for +n: Nat
  for +j: Nat
  for +w: Word(n)
  for +h: S.Sub(n, w, S.ones(n, j))
  Either<&2, &2, {w == Word.zero(n) : Word(n)}, {Nat.is_lt(S.lsb(n, w), j) == True{} : Bool}>

law unit_shl:
  for +j: Nat
  for +lj: {Nat.is_lt(j, 13n) == True{} : Bool}
  {U32{S.unit(32n, j)} == (1 << j : U32) : U32}

law ctz_shl:
  for +j: Nat
  for +lj: {Nat.is_lt(j, 13n) == True{} : Bool}
  {U32.ctz((1 << j : U32)) == j : Nat}

law lsb_hold:
  for +w: Word(32n)
  for +hm: S.Sub32(U32{w}, 8191)
  for +nz: {U32.is_eq(U32{w}, 0) == False{} : Bool}
  {Nat.is_lt(S.lsb(32n, w), 13n) == True{} : Bool}


# ---------------------------------------------------------------------------
# Toward the sure tricks: lower bounds through the search, and every card a move

law max_ge:
  for +a: U32
  for +b: U32
  S.And({Nat.is_le(U32.to_nat(a), U32.to_nat(U32.max(a, b))) == True{} : Bool}, {Nat.is_le(U32.to_nat(b), U32.to_nat(U32.max(a, b))) == True{} : Bool})

law max_keep:
  for +p: Nat
  for ms: List<&2, U32>
  for +t: U32
  for +pos: R.Pos
  for +best: U32
  for r: B.Res
  for +lb: Nat
  for +h: Either<&2, &2, S.GE(lb, best), S.GE(lb, S.rv(r))>
  S.GE(lb, S.rv(B.search(1n+p, ms, t, pos, True{}, best, r)))

law max_ex:
  for +p: Nat
  for ms: List<&2, U32>
  for +t: U32
  for +pos: R.Pos
  for +best: U32
  for r: B.Res
  for +lb: Nat
  for ex: S.ExK(lb, p, t, pos, ms)
  S.GE(lb, S.rv(B.search(1n+p, ms, t, pos, True{}, best, r)))

law min_all:
  for +p: Nat
  for ms: List<&2, U32>
  for +t: U32
  for +pos: R.Pos
  for +best: U32
  for r: B.Res
  for +lb: Nat
  for all: S.AllK(lb, p, t, pos, ms)
  for +hb: S.GE(lb, best)
  for +hr: S.GE(lb, S.rv(r))
  S.GE(lb, S.rv(B.search(1n+p, ms, t, pos, False{}, best, r)))

law count_none:
  for +n: Nat
  for +w: Word(n)
  for +h: S.Sub(n, w, S.ones(n, 0n))
  {S.word.count(n, w) == 0n : Nat}

law count_le:
  for +n: Nat
  for +j: Nat
  for +w: Word(n)
  for +h: S.Sub(n, w, S.ones(n, j))
  {Nat.is_le(S.word.count(n, w), j) == True{} : Bool}

law unit_split:
  for +n: Nat
  for +r: Nat
  for +w: Word(n)
  for +h: S.Sub(n, S.unit(n, r), w)
  Either<&2, &2, {r == S.lsb(n, w) : Nat}, S.Sub(n, S.unit(n, r), Word.xor(n, w, S.unit(n, S.lsb(n, w))))>

law mem_acc:
  for n: Nat
  for z: Bool
  for +s: U32
  for +m: U32
  for acc: List<&2, U32>
  for +c: U32
  for mem: S.Mem(c, acc)
  S.Mem(c, R.moves.peel(n, z, s, m, acc))

law mem_peel:
  for n: Nat
  for z: Bool
  for +s: U32
  for +w: Word(32n)
  for acc: List<&2, U32>
  for +c: U32
  for +r: Nat
  for +ec: {c == C.card.make(s, U32.from_nat(r)) : U32}
  for +lr: {Nat.is_lt(r, 13n) == True{} : Bool}
  for +zf: {z == U32.is_eq(U32{w}, 0) : Bool}
  for +hm: S.Sub32(U32{w}, 8191)
  for +xm: S.Sub32((1 << r : U32), U32{w})
  for +cn: {Nat.is_le(S.bits(U32{w}), n) == True{} : Bool}
  for sp: Either<&2, &2, {r == S.lsb(32n, w) : Nat}, S.Sub(32n, S.unit(32n, r), Word.xor(32n, w, S.unit(32n, S.lsb(32n, w))))>
  S.Mem(c, R.moves.peel(n, z, s, U32{w}, acc))

law mem_lead:
  for +j: Nat
  for +r: Nat
  for +h01: U32
  for +h23: U32
  for +v01: S.Sub32(h01, S.valid.mask())
  for +v23: S.Sub32(h23, S.valid.mask())
  for +lj: {Nat.is_lt(j, 4n) == True{} : Bool}
  for +lr: {Nat.is_lt(r, 13n) == True{} : Bool}
  for +xm: S.Sub32((1 << r : U32), R.suit.mask(j, h01, h23))
  S.Mem(C.card.make(U32.from_nat(j), U32.from_nat(r)), R.moves.of(4, h01, h23))

law ex_mem:
  for +lb: Nat
  for +p: Nat
  for +t: U32
  for +pos: R.Pos
  for ms: List<&2, U32>
  for +c: U32
  for mem: S.Mem(c, ms)
  for k: S.Kid(lb, p, t, pos, c)
  S.ExK(lb, p, t, pos, ms)


# ---------------------------------------------------------------------------
# The winning card in the trick word: owner, best and lead read back out, and
# kept by a card that does not win

law shrn_or:
  for +k: Nat
  for +a: U32
  for +b: U32
  {U32.shrn(U32.or(a, b), k) == U32.or(U32.shrn(a, k), U32.shrn(b, k)) : U32}

law field_or:
  for +k: Nat
  for +m: U32
  for +a: U32
  for +b: U32
  {U32.and(U32.shrn(U32.or(a, b), k), m) == U32.or(U32.and(U32.shrn(a, k), m), U32.and(U32.shrn(b, k), m)) : U32}

law field_mask:
  for +x: U32
  for +kk: U32
  for +k: Nat
  for +m: U32
  for +h: S.Sub32(x, kk)
  {U32.and(U32.shrn(x, k), m) == U32.and(U32.shrn(x, k), U32.and(U32.shrn(kk, k), m)) : U32}

law shr_shl_w:
  for +p: Nat
  for +b: Bool
  for +t: Word(p)
  {Word.shr.pad(p, Word.shl.put(p, b, t)) == Word.and(1n+p, WCon{b, t}, S.ones(1n+p, p)) : Word(1n+p)}

law shr_shl:
  for +x: U32
  {U32.shr(U32.shl(x)) == U32.and(x, 2147483647) : U32}

law and_all_w:
  for +n: Nat
  for +w: Word(n)
  {Word.and(n, w, S.ones(n, n)) == w : Word(n)}

law shrn_shln:
  for +k: Nat
  for +x: U32
  {U32.shrn(U32.shln(x, k), k) == U32.and(x, S.keep(k)) : U32}

law owner_make:
  for +s: U32
  for +p: U32
  for +l: U32
  for +o: U32
  for +b: U32
  for +hs: S.Sub32(s, 3)
  for +hp: S.Sub32(p, 3)
  for +hl: S.Sub32(l, 7)
  for +ho: S.Sub32(o, 3)
  for +hb: S.Sub32(b, 63)
  {R.trick.owner(R.trick.make(s, p, l, o, b)) == o : U32}

law owner_make_r:
  for +s: U32
  for +p: U32
  for +l: U32
  for +o: U32
  for +b: U32
  for +r: U32
  for +hs: S.Sub32(s, 3)
  for +hp: S.Sub32(p, 3)
  for +hl: S.Sub32(l, 7)
  for +ho: S.Sub32(o, 3)
  for +hb: S.Sub32(b, 63)
  for +hr: S.Sub32(r, 1)
  {R.trick.owner(U32.or(R.trick.make(s, p, l, o, b), U32.shln(r, 15n))) == o : U32}

law best_make:
  for +s: U32
  for +p: U32
  for +l: U32
  for +o: U32
  for +b: U32
  for +hs: S.Sub32(s, 3)
  for +hp: S.Sub32(p, 3)
  for +hl: S.Sub32(l, 7)
  for +ho: S.Sub32(o, 3)
  for +hb: S.Sub32(b, 63)
  {R.trick.best(R.trick.make(s, p, l, o, b)) == b : U32}

law best_make_r:
  for +s: U32
  for +p: U32
  for +l: U32
  for +o: U32
  for +b: U32
  for +r: U32
  for +hs: S.Sub32(s, 3)
  for +hp: S.Sub32(p, 3)
  for +hl: S.Sub32(l, 7)
  for +ho: S.Sub32(o, 3)
  for +hb: S.Sub32(b, 63)
  for +hr: S.Sub32(r, 1)
  {R.trick.best(U32.or(R.trick.make(s, p, l, o, b), U32.shln(r, 15n))) == b : U32}

law lead_make:
  for +s: U32
  for +p: U32
  for +l: U32
  for +o: U32
  for +b: U32
  for +hs: S.Sub32(s, 3)
  for +hp: S.Sub32(p, 3)
  for +hl: S.Sub32(l, 7)
  for +ho: S.Sub32(o, 3)
  for +hb: S.Sub32(b, 63)
  {R.trick.lead(R.trick.make(s, p, l, o, b)) == l : U32}

law lead_make_r:
  for +s: U32
  for +p: U32
  for +l: U32
  for +o: U32
  for +b: U32
  for +r: U32
  for +hs: S.Sub32(s, 3)
  for +hp: S.Sub32(p, 3)
  for +hl: S.Sub32(l, 7)
  for +ho: S.Sub32(o, 3)
  for +hb: S.Sub32(b, 63)
  for +hr: S.Sub32(r, 1)
  {R.trick.lead(U32.or(R.trick.make(s, p, l, o, b), U32.shln(r, 15n))) == l : U32}

law first_win:
  for +win: Bool
  for +rank: Bool
  for +seat: U32
  for +played: U32
  for +lead: U32
  for +owner: U32
  for +best: U32
  for +c: U32
  for +ep: {played == 0 : U32}
  for +hs: S.Sub32(seat, 3)
  for +hu: S.Sub32(C.card.suit(c), 7)
  for +hc: S.Sub32(c, 63)
  S.And({R.trick.owner(R.trick.next.go(U32.is_eq(played, 0), U32.is_eq(played, 3), win, rank, seat, played, lead, owner, best, c)) == seat : U32},
    S.And({R.trick.best(R.trick.next.go(U32.is_eq(played, 0), U32.is_eq(played, 3), win, rank, seat, played, lead, owner, best, c)) == c : U32},
      {R.trick.lead(R.trick.next.go(U32.is_eq(played, 0), U32.is_eq(played, 3), win, rank, seat, played, lead, owner, best, c)) == C.card.suit(c) : U32}))

law mid_keep:
  for +k: Nat
  for +lk: {Nat.is_lt(k, 3n) == True{} : Bool}
  for +nk: {Nat.is_eq(k, 0n) == False{} : Bool}
  for +win: Bool
  for +rank: Bool
  for +seat: U32
  for +played: U32
  for +lead: U32
  for +owner: U32
  for +best: U32
  for +c: U32
  for +ep: {played == U32.from_nat(k) : U32}
  for +ew: {win == False{} : Bool}
  for +hl: S.Sub32(lead, 7)
  for +ho: S.Sub32(owner, 3)
  for +hb: S.Sub32(best, 63)
  S.And({R.trick.owner(R.trick.next.go(U32.is_eq(played, 0), U32.is_eq(played, 3), win, rank, seat, played, lead, owner, best, c)) == owner : U32},
    S.And({R.trick.best(R.trick.next.go(U32.is_eq(played, 0), U32.is_eq(played, 3), win, rank, seat, played, lead, owner, best, c)) == best : U32},
      {R.trick.lead(R.trick.next.go(U32.is_eq(played, 0), U32.is_eq(played, 3), win, rank, seat, played, lead, owner, best, c)) == lead : U32}))


# ---------------------------------------------------------------------------
# Nothing beats the top card at no trumps

law card_shape:
  for +s: Nat
  for +r: Nat
  for +ls: {Nat.is_lt(s, 4n) == True{} : Bool}
  for +lr: {Nat.is_lt(r, 13n) == True{} : Bool}
  {S.card.shape(C.card.make(U32.from_nat(s), U32.from_nat(r))) == True{} : Bool}

law code_at:
  for +s: Nat
  for +r: Nat
  for +ls: {Nat.is_lt(s, 4n) == True{} : Bool}
  for +lr: {Nat.is_lt(r, 13n) == True{} : Bool}
  {S.code.at(s, r) == True{} : Bool}

law lt_ne:
  for +n: Nat
  for +m: Nat
  for +e: {Nat.is_lt(n, m) == True{} : Bool}
  {Cmp.is_eq(Nat.cmp(n, m)) == False{} : Bool}

law lt_ngt:
  for +n: Nat
  for +m: Nat
  for +e: {Nat.is_lt(n, m) == True{} : Bool}
  {Cmp.is_gt(Nat.cmp(n, m)) == False{} : Bool}

law cmp_add:
  for +a: Nat
  for +b: Nat
  for +x: Nat
  {Nat.cmp(Nat.add(a, x), Nat.add(b, x)) == Nat.cmp(a, b) : Cmp}

law beats_top:
  for +j: Nat
  for +r: Nat
  for +c: U32
  for +lj: {Nat.is_lt(j, 4n) == True{} : Bool}
  for +lr: {Nat.is_lt(r, 13n) == True{} : Bool}
  for +ok: {S.card.shape(c) == True{} : Bool}
  for lo: Either<&2, &2, {U32.is_eq(C.card.suit(c), U32.from_nat(j)) == False{} : Bool}, S.And({C.card.suit(c) == U32.from_nat(j) : U32}, {Nat.is_lt(U32.to_nat(C.card.rank(c)), r) == True{} : Bool})>
  {R.beats(4, C.card.make(U32.from_nat(j), U32.from_nat(r)), c) == False{} : Bool}

law unit_lt:
  for +n: Nat
  for +q: Nat
  for +r: Nat
  for +lq: {Nat.is_lt(q, n) == True{} : Bool}
  for +h: S.Sub(n, S.unit(n, q), S.ones(n, r))
  {Nat.is_lt(q, r) == True{} : Bool}

law below_top:
  for +c: U32
  for +j: Nat
  for +r: Nat
  for +h01: U32
  for +h23: U32
  for +ok: {S.card.shape(c) == True{} : Bool}
  for +i1: S.Sub32(S.play.a(c), h01)
  for +i2: S.Sub32(S.play.b(c), h23)
  for +top: S.Sub32(R.suit.mask(j, h01, h23), U32{S.ones(32n, r)})
  for +lj: {Nat.is_lt(j, 4n) == True{} : Bool}
  Either<&2, &2, {U32.is_eq(C.card.suit(c), U32.from_nat(j)) == False{} : Bool}, S.And({C.card.suit(c) == U32.from_nat(j) : U32}, {Nat.is_lt(U32.to_nat(C.card.rank(c)), r) == True{} : Bool})>


# ---------------------------------------------------------------------------
# The first sure trick rule for every position: the top card at no trumps
law top_nt_north:
  for +p: Nat
  for +j: Nat
  for +r: Nat
  for +lj: {Nat.is_lt(j, 4n) == True{} : Bool}
  for +lr: {Nat.is_lt(r, 13n) == True{} : Bool}
  for +L: Nat
  for +n01: U32
  for +n23: U32
  for +e01: U32
  for +e23: U32
  for +s01: U32
  for +s23: U32
  for +w01: U32
  for +w23: U32
  for +tr: U32
  for +won: U32
  for +inv: S.Inv(R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, 1n+p, L)
  for +es: {U32.to_nat(R.trick.seat(tr)) == 0n : Nat}
  for +ek: {U32.to_nat(R.trick.played(tr)) == 0n : Nat}
  for +el: {R.trick.lead(tr) == 4 : U32}
  for +hold: S.Sub32((1 << r : U32), R.suit.mask(j, n01, n23))
  for +tps: S.Tops(0n, j, r, n01, n23, e01, e23, s01, s23, w01, w23)
  for +n: Nat
  S.GE(1n+U32.to_nat(won), S.rv(B.solve(1n+p, 4, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, n)))

law top_nt_south:
  for +p: Nat
  for +j: Nat
  for +r: Nat
  for +lj: {Nat.is_lt(j, 4n) == True{} : Bool}
  for +lr: {Nat.is_lt(r, 13n) == True{} : Bool}
  for +L: Nat
  for +n01: U32
  for +n23: U32
  for +e01: U32
  for +e23: U32
  for +s01: U32
  for +s23: U32
  for +w01: U32
  for +w23: U32
  for +tr: U32
  for +won: U32
  for +inv: S.Inv(R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, 1n+p, L)
  for +es: {U32.to_nat(R.trick.seat(tr)) == 2n : Nat}
  for +ek: {U32.to_nat(R.trick.played(tr)) == 0n : Nat}
  for +el: {R.trick.lead(tr) == 4 : U32}
  for +hold: S.Sub32((1 << r : U32), R.suit.mask(j, s01, s23))
  for +tps: S.Tops(2n, j, r, n01, n23, e01, e23, s01, s23, w01, w23)
  for +n: Nat
  S.GE(1n+U32.to_nat(won), S.rv(B.solve(1n+p, 4, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, n)))


# ---------------------------------------------------------------------------
# Witnesses in the search: the min is one of its values, the max is above each

law min_is:
  for +a: U32
  for +b: U32
  Either<&2, &2, {U32.min(a, b) == a : U32}, {U32.min(a, b) == b : U32}>

law min_wit:
  for +p: Nat
  for ms: List<&2, U32>
  for +t: U32
  for +pos: R.Pos
  for +best: U32
  for +r: B.Res
  S.MinWit(S.rv(B.search(1n+p, ms, t, pos, False{}, best, r)), best, S.rv(r), p, t, pos, ms)

law keep_le:
  for +p: Nat
  for ms: List<&2, U32>
  for +t: U32
  for +pos: R.Pos
  for +best: U32
  for +r: B.Res
  S.And({Nat.is_le(U32.to_nat(best), U32.to_nat(S.rv(B.search(1n+p, ms, t, pos, True{}, best, r)))) == True{} : Bool}, {Nat.is_le(U32.to_nat(S.rv(r)), U32.to_nat(S.rv(B.search(1n+p, ms, t, pos, True{}, best, r)))) == True{} : Bool})

law max_child:
  for +p: Nat
  for ms: List<&2, U32>
  for +t: U32
  for +pos: R.Pos
  for +best: U32
  for +r: B.Res
  for +c: U32
  for mem: S.Mem(c, ms)
  S.AtLeast(p, t, pos, c, S.rv(B.search(1n+p, ms, t, pos, True{}, best, r)))
