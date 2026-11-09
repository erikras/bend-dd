# sim.bend: simulation, double dummy over the layouts a player can't see.
#
# At the table a player sees their own hand and dummy, and the cards played so far.
# The rest are hidden, but not entirely unknown: the auction says things like "West
# has 11 to 15 points and five spades", and a player who failed to follow suit has
# no more of it. A simulation deals the hidden cards at random many times, keeps the
# layouts that fit all of that, solves each one double dummy, and says for each card
# the player could play now how many tricks it takes on average and how often the
# contract makes.
#
# Every layout that fits is equally likely: the hidden cards are dealt uniformly, and
# the ones that don't fit are thrown away.

import Base
import ./cards.bend as C
import ./rules.bend as R
import ./deal.bend as D
import ./search.bend as Z
import ./play.bend as P
import ./show.bend as V
import ./pbn.bend as N

# ---------------------------------------------------------------------------
# What the auction says

# A seat's count of something lies between lo and hi. what is 0 to 3 for the length
# of that suit and 4 for high card points.
type Rule is Data:
  Rule{seat: U32, what: U32, lo: U32, hi: U32}

def hcp.suit(+m: U32) -> U32:
  ((((m >> 12n) .&. 1) * 4) + (((m >> 11n) .&. 1) * 3) + (((m >> 10n) .&. 1) * 2) + ((m >> 9n) .&. 1) : U32)

# High card points: 4 for an ace, 3 for a king, 2 for a queen and 1 for a jack.
def hcp(h: C.Hand) -> U32:
  match h:
    case C.Hand{s, x, d, c}:
      (hcp.suit(s) + hcp.suit(x) + hcp.suit(d) + hcp.suit(c) : U32)

def maybe.rule(ok: Bool, +r: Rule) -> Maybe<&2, Rule>:
  match ok:
    case True{}:
      Some{r}
    case False{}:
      None{}

def rule.count(+what: U32, +h: C.Hand) -> U32:
  R.sel(U32.is_eq(what, 4), hcp(h), C.bits.count(C.hand.suit(U32.to_nat(what), h)))

def rule.ok(r: Rule, +deal: C.Deal) -> Bool:
  match r:
    case Rule{+seat, +what, +lo, +hi}:
      +v = rule.count(what, C.deal.hand(U32.to_nat(seat), deal))
      U32.is_ge(v, lo) && U32.is_le(v, hi)

def rules.ok(rs: List<&2, Rule>, +deal: C.Deal) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, t}:
      rule.ok(r, deal) && rules.ok(t, deal)

# ---------------------------------------------------------------------------
# Hands as sets of cards

def hand.minus(a: C.Hand, b: C.Hand) -> C.Hand:
  match a b:
    case C.Hand{s1, h1, d1, c1} C.Hand{s2, h2, d2, c2}:
      C.Hand{(s1 .&. (s2 .^. 8191) : U32), (h1 .&. (h2 .^. 8191) : U32), (d1 .&. (d2 .^. 8191) : U32), (c1 .&. (c2 .^. 8191) : U32)}

def hand.union(a: C.Hand, b: C.Hand) -> C.Hand:
  match a b:
    case C.Hand{s1, h1, d1, c1} C.Hand{s2, h2, d2, c2}:
      C.Hand{(s1 .|. s2 : U32), (h1 .|. h2 : U32), (d1 .|. d2 : U32), (c1 .|. c2 : U32)}

def deal.all(d: C.Deal) -> C.Hand:
  match d:
    case C.Deal{n, e, s, w}:
      hand.union(n, hand.union(e, hand.union(s, w)))

def hand.full() -> C.Hand:
  C.Hand{8191, 8191, 8191, 8191}

def hand.has(+c: U32, h: C.Hand) -> Bool:
  U32.is_ne((C.hand.suit(U32.to_nat(C.card.suit(c)), h) .&. C.card.bit(c) : U32), 0)

# Takes a whole suit out of a hand.
def hand.drop.suit(suit: Nat, h: C.Hand) -> C.Hand:
  match suit h:
    case 0n C.Hand{_, x, d, c}:
      C.Hand{0, x, d, c}
    case 1n C.Hand{s, _, d, c}:
      C.Hand{s, 0, d, c}
    case 2n C.Hand{s, x, _, c}:
      C.Hand{s, x, 0, c}
    case _ C.Hand{s, x, d, _}:
      C.Hand{s, x, d, 0}

# ---------------------------------------------------------------------------
# The position

# Everything a simulation needs, worked out once from what the player sees.
#
#   known   for each seat, the cards known to have been in its hand at the start:
#           a visible hand whole, and for a hidden seat the cards it has played and
#           any it must hold because the other hidden seats are void in their suit
#   pool    the cards still to deal to the hidden seats
#   need    how many each seat still needs, 8 bits each, North lowest
#   played  every card played so far
#   voids   bit 4 * seat + suit: that seat showed out of that suit
#   hidden  bit seat: that seat's hand is hidden
#   pos     the position now, with the hidden hands empty
#   l01 l23 the cards in play at the start of the current trick
#   d       the cards in the four hands now
type Setup is Data:
  Setup{known: C.Deal, pool: C.Hand, need: U32, played: C.Hand, voids: U32, hidden: U32, pos: R.Pos, l01: U32, l23: U32, d: U32}

def bit.at(+x: U32, +i: U32) -> Bool:
  U32.is_ne(((x >> U32.to_nat(i)) .&. 1 : U32), 0)

def need.of(+need: U32, +seat: U32) -> U32:
  ((need >> U32.to_nat((seat * 8 : U32))) .&. 255 : U32)

# ---------------------------------------------------------------------------
# Dealing the hidden cards

type Dealt is Data:
  Dealt{deal: C.Deal, seed: U32}

# Deals the cards of the pool, in card order from card i, to seats that still need
# cards (a, b, c, e for N, E, S, W), as D.seats does: each card goes to a seat with
# probability proportional to the cards that seat still needs, which gives every
# deal the same chance. Cards not in the pool take no randomness.
def deal.pool(n: Nat, +i: U32, +seed: U32, +pool: C.Hand, +a: U32, +b: U32, +c: U32, +e: U32, d: C.Deal) -> Dealt:
  match n:
    case 0n:
      Dealt{d, seed}
    case 1n+p:
      +suit = U32.to_nat((i / 13 : U32))
      +bit = (1 << U32.to_nat((12 - i % 13 : U32)) : U32)
      +here = U32.is_ne((C.hand.suit(suit, pool) .&. bit : U32), 0)
      +x = D.lcg(seed)
      +tot = U32.max((a + b + c + e : U32), 1)
      +seat = D.pick(((x >> 16n) % tot : U32), a, b, c)
      deal.pool(p, (i + 1 : U32), R.sel(here, x, seed), pool,
        D.dec(here && U32.is_eq(seat, 0), a), D.dec(here && U32.is_eq(seat, 1), b),
        D.dec(here && U32.is_eq(seat, 2), c), D.dec(here && U32.is_eq(seat, 3), e),
        D.ending.add(here, seat, i, d))

# One random layout: the known cards with the pool dealt on top.
def sample(+s: Setup, +seed: U32) -> Dealt:
  match s:
    case Setup{+known, +pool, +need, _, _, _, _, _, _, _}:
      deal.pool(52n, 0, seed, pool, need.of(need, 0), need.of(need, 1), need.of(need, 2), need.of(need, 3), known)

# Whether a seat that showed out of a suit has none of it left in this layout.
def void.ok(+voids: U32, +i: U32, +deal: C.Deal, +played: C.Hand) -> Bool:
  +seat = U32.to_nat((i >> 2n : U32))
  +suit = U32.to_nat((i .&. 3 : U32))
  +left = C.hand.suit(suit, hand.minus(C.deal.hand(seat, deal), played))
  Bool.not(bit.at(voids, i)) || U32.is_zero(left)

def voids.ok(k: Nat, +i: U32, +voids: U32, +deal: C.Deal, +played: C.Hand) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+p:
      void.ok(voids, i, deal, played) && voids.ok(p, (i + 1 : U32), voids, deal, played)

# Whether a layout fits the auction and the play.
def fits(+s: Setup, +rules: List<&2, Rule>, +deal: C.Deal) -> Bool:
  match s:
    case Setup{_, _, _, +played, +voids, _, _, _, _, _}:
      voids.ok(16n, 0, voids, deal, played) && rules.ok(rules, deal)

# Adds cards to one seat of a position, as words packed as R.Pos packs them.
def pos.add(+seat: Nat, +a: U32, +b: U32, pos: R.Pos) -> R.Pos:
  match pos:
    case R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}:
      R.play.go(seat, a, b, n01, n23, e01, e23, s01, s23, w01, w23, tr, won)

# The cards a hidden seat holds now in a layout, packed; nothing for a seat in view,
# whose cards the position already has.
def seat.now.go(hid: Bool, +s: U32, +deal: C.Deal, +played: C.Hand) -> C.Hand:
  match hid:
    case True{}:
      hand.minus(C.deal.hand(U32.to_nat(s), deal), played)
    case False{}:
      C.hand.empty()

def seat.now(+s: U32, +hidden: U32, +deal: C.Deal, +played: C.Hand) -> C.Hand:
  seat.now.go(bit.at(hidden, s), s, deal, played)

def pos.give(+s: U32, +hidden: U32, +deal: C.Deal, +played: C.Hand, pos: R.Pos) -> R.Pos:
  +h = seat.now(s, hidden, deal, played)
  pos.add(U32.to_nat(s), R.hand.pack01(h), R.hand.pack23(h), pos)

# The position now in a layout: the position with the hidden hands filled in.
def pos.of(+s: Setup, +deal: C.Deal) -> R.Pos:
  match s:
    case Setup{_, _, _, +played, _, +hidden, +pos, _, _, _}:
      pos.give(3, hidden, deal, played, pos.give(2, hidden, deal, played, pos.give(1, hidden, deal, played, pos.give(0, hidden, deal, played, pos))))

# ---------------------------------------------------------------------------
# Replaying the cards played so far

# The state of a replay. err is empty while every card has been fine. done is the
# cards of the tricks already finished.
type Replay is Data:
  Replay{err: String, known: C.Deal, played: C.Hand, done: C.Hand, voids: U32, pos: R.Pos}

def sel.hand(b: Bool, x: C.Hand, y: C.Hand) -> C.Hand:
  match b:
    case True{}:
      x
    case False{}:
      y

def sel.str(b: Bool, x: String, y: String) -> String:
  match b:
    case True{}:
      x
    case False{}:
      y

def seat.name(s: Nat) -> String:
  match s:
    case 0n:
      "North"
    case 1n:
      "East"
    case 2n:
      "South"
    case _:
      "West"

# A card as people write it: the suit symbol, then the rank.
def card.name(+c: U32) -> String:
  V.suit.symbol(C.card.suit(c)) ++ V.str.at(C.card.rank(c), "23456789TJQKA")

def has.card(xs: List<&2, U32>, +c: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      U32.is_eq(h, c) || has.card(t, c)

# The card c as a one-card hand.
def card.hand(+c: U32) -> C.Hand:
  C.hand.add(U32.to_nat(C.card.suit(c)), C.card.bit(c), C.hand.empty())

def replay.next(good: Bool, +msg: String, +c: U32, +t: U32, +hid: Bool, +seat: U32, +lead: U32, +known: C.Deal, +played: C.Hand, +done: C.Hand, +voids: U32, +pos: R.Pos) -> Replay:
  match good:
    case False{}:
      Replay{msg, known, played, done, voids, pos}
    case True{}:
      +h = sel.hand(hid, card.hand(c), C.hand.empty())
      +known2 = C.deal.add(U32.to_nat(seat), U32.to_nat(C.card.suit(c)), R.sel(hid, C.card.bit(c), 0), known)
      +pos2 = R.play(t, pos.add(U32.to_nat(seat), R.hand.pack01(h), R.hand.pack23(h), pos), c)
      +out = hid && U32.is_ne(lead, R.none()) && U32.is_ne(C.card.suit(c), lead)
      +voids2 = (voids .|. R.sel(out, (1 << U32.to_nat((seat * 4 + lead : U32)) : U32), 0) : U32)
      +played2 = hand.union(played, card.hand(c))
      +ended = U32.is_zero(R.trick.played(R.pos.trick(pos2)))
      Replay{"", known2, played2, sel.hand(ended, played2, done), voids2, pos2}

# One card of the play. A card from a hand in view must be a legal play from it. A
# card from a hidden seat must not be one that is known to be elsewhere, and must not
# be of a suit that seat has shown out of; it is then known to have been in that
# hand, and a card of another suit than the one led shows that seat out of it.
def replay.card(+c: U32, +t: U32, +hidden: U32, r: Replay) -> Replay:
  match r:
    case Replay{+err, +known, +played, +done, +voids, +pos}:
      +tr = R.pos.trick(pos)
      +seat = R.trick.seat(tr)
      +lead = R.trick.lead(tr)
      +hid = bit.at(hidden, seat)
      +fresh = Bool.not(hand.has(c, deal.all(known)))
      +shown = bit.at(voids, (seat * 4 + C.card.suit(c) : U32))
      +legal = has.card(R.moves(pos), c)
      +fine = (hid && fresh && Bool.not(shown)) || (Bool.not(hid) && legal)
      +msg = sel.str(String.is_empty(err), card.name(c) ++ " can't be played by " ++ seat.name(U32.to_nat(seat)) ++ " here", err)
      replay.next(String.is_empty(err) && fine, msg, c, t, hid, seat, lead, known, played, done, voids, pos)

def replay(xs: List<&2, U32>, +t: U32, +hidden: U32, r: Replay) -> Replay:
  match xs:
    case Nil{}:
      r
    case Con{+c, rest}:
      replay(rest, t, hidden, replay.card(c, t, hidden, r))

# ---------------------------------------------------------------------------
# From the replay to the setup

type Kp is Data:
  Kp{known: C.Deal, pool: C.Hand}

# The hidden seats that may still hold cards of a suit, as a mask of seats.
def eligible(+suit: U32, +hidden: U32, +voids: U32) -> U32:
  +a = Bool.to_u32(bit.at(hidden, 0) && Bool.not(bit.at(voids, suit)))
  +b = Bool.to_u32(bit.at(hidden, 1) && Bool.not(bit.at(voids, (4 + suit : U32))))
  +c = Bool.to_u32(bit.at(hidden, 2) && Bool.not(bit.at(voids, (8 + suit : U32))))
  +e = Bool.to_u32(bit.at(hidden, 3) && Bool.not(bit.at(voids, (12 + suit : U32))))
  (a .|. (b << 1n) .|. (c << 2n) .|. (e << 3n) : U32)

def force.go(one: Bool, +suit: Nat, +seat: U32, known: C.Deal, +pool: C.Hand) -> Kp:
  match one:
    case True{}:
      Kp{C.deal.add(U32.to_nat(seat), suit, C.hand.suit(suit, pool), known), hand.drop.suit(suit, pool)}
    case False{}:
      Kp{known, pool}

# When only one hidden seat can hold a suit, the rest of that suit is in its hand.
def force(+suit: U32, +hidden: U32, +voids: U32, k: Kp) -> Kp:
  match k:
    case Kp{known, +pool}:
      +el = eligible(suit, hidden, voids)
      force.go(U32.is_eq(C.bits.count(el), 1), U32.to_nat(suit), U32.from_nat(U32.log2(el)), known, pool)

# What each seat still needs: 13 less what it is known to have held, for a hidden
# seat, packed 8 bits each. A seat known to have held more than 13 shows as 255.
def need.seat(+s: U32, +hidden: U32, +known: C.Deal) -> U32:
  +k = C.hand.count(C.deal.hand(U32.to_nat(s), known))
  +n = R.sel(U32.is_le(k, 13), (13 - k : U32), 255)
  (R.sel(bit.at(hidden, s), n, 0) << U32.to_nat((s * 8 : U32)) : U32)

def need.all(+hidden: U32, +known: C.Deal) -> U32:
  (need.seat(0, hidden, known) .|. need.seat(1, hidden, known) .|. need.seat(2, hidden, known) .|. need.seat(3, hidden, known) : U32)

def need.sum(+need: U32) -> U32:
  (need.of(need, 0) + need.of(need, 1) + need.of(need, 2) + need.of(need, 3) : U32)

# A setup, or why there can't be one.
type Made is Data:
  Made{err: String, s: Setup}

def setup.check(+pool: C.Hand, +need: U32) -> String:
  +bad = U32.is_eq(need.of(need, 0), 255) || U32.is_eq(need.of(need, 1), 255) || U32.is_eq(need.of(need, 2), 255) || U32.is_eq(need.of(need, 3), 255)
  sel.str(bad || U32.is_ne(need.sum(need), C.hand.count(pool)), "the play doesn't fit the hands in view", "")

def setup.go(k: Kp, +err: String, +played: C.Hand, +done: C.Hand, +voids: U32, +hidden: U32, +pos: R.Pos) -> Made:
  match k:
    case Kp{+known, +pool}:
      +need = need.all(hidden, known)
      +live = hand.minus(hand.full(), done)
      +e2 = sel.str(String.is_empty(err), setup.check(pool, need), err)
      Made{e2, Setup{known, pool, need, played, voids, hidden, pos, R.hand.pack01(live), R.hand.pack23(live), (52 - C.hand.count(played) : U32)}}

def setup.of(r: Replay, +hidden: U32) -> Made:
  match r:
    case Replay{+err, +known, +played, +done, +voids, +pos}:
      +pool = hand.minus(hand.full(), deal.all(known))
      setup.go(force(3, hidden, voids, force(2, hidden, voids, force(1, hidden, voids, force(0, hidden, voids, Kp{known, pool})))), err, played, done, voids, hidden, pos)

# The setup for a deal with some hands hidden (empty in view), a strain, a declarer
# and the cards played so far, in order.
def setup(+view: C.Deal, +hidden: U32, +t: U32, +decl: U32, +plays: List<&2, U32>) -> Made:
  +start = R.pos.start(view, ((decl + 1) .&. 3 : U32))
  setup.of(replay(plays, t, hidden, Replay{"", view, C.hand.empty(), C.hand.empty(), 0, start}), hidden)

# ---------------------------------------------------------------------------
# The cards to try

# The top of the run that card bit b is in: going up through the cards in play, as
# long as the next one up is in the same hand h, they are all the same card.
def run.top(n: Nat, +b: U32, +h: U32, +l: U32) -> U32:
  match n:
    case 0n:
      b
    case 1n+p:
      +above = (l .&. (0 - (b << 1n)) : U32)
      +next = (above .&. (0 - above) : U32)
      +up = U32.is_ne(next, 0) && U32.is_ne((next .&. h : U32), 0)
      R.sel(up, run.top(p, next, h, l), b)

# The cards of the run whose top is bit b, as a mask.
def run.down(n: Nat, +b: U32, +h: U32, +l: U32, +acc: U32) -> U32:
  match n:
    case 0n:
      acc
    case 1n+p:
      +below = (l .&. (b - 1) : U32)
      +next = R.sel(U32.is_zero(below), 0, (1 << U32.log2(below) : U32))
      +down = U32.is_ne(next, 0) && U32.is_ne((next .&. h : U32), 0)
      R.sel(down, run.down(p, next, h, l, (acc .|. next : U32)), acc)

# A card to try, and the run of cards that play the same as it.
type Cand is Data:
  Cand{card: U32, run: U32}

def hand.word01(pos: R.Pos, +seat: Nat) -> U32:
  match pos:
    case R.Pos{n01, _, e01, _, s01, _, w01, _, _, _}:
      R.pick(seat, n01, e01, s01, w01)

def hand.word23(pos: R.Pos, +seat: Nat) -> U32:
  match pos:
    case R.Pos{_, n23, _, e23, _, s23, _, w23, _, _}:
      R.pick(seat, n23, e23, s23, w23)

def cands.keep(keep: Bool, +x: Cand, rest: List<&2, Cand>) -> List<&2, Cand>:
  match keep:
    case True{}:
      x <> rest
    case False{}:
      rest

def cands.go(xs: List<&2, U32>, +h01: U32, +h23: U32, +l01: U32, +l23: U32) -> List<&2, Cand>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+c, rest}:
      +suit = U32.to_nat(C.card.suit(c))
      +h = R.suit.mask(suit, h01, h23)
      +l = R.suit.mask(suit, l01, l23)
      +b = C.card.bit(c)
      +top = U32.is_eq(run.top(13n, b, h, l), b)
      cands.keep(top, Cand{c, run.down(13n, b, h, l, b)}, cands.go(rest, h01, h23, l01, l23))


# The cards the player to move should try: one from each run.
def cands(+s: Setup) -> List<&2, Cand>:
  match s:
    case Setup{_, _, _, _, _, _, +pos, +l01, +l23, _}:
      +seat = U32.to_nat(R.trick.seat(R.pos.trick(pos)))
      cands.go(R.moves(pos), hand.word01(pos, seat), hand.word23(pos, seat), l01, l23)

def cands.cards(xs: List<&2, Cand>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{Cand{c, _}, t}:
      c <> cands.cards(t)

# ---------------------------------------------------------------------------
# Solving the layouts

# A simulation's question: the setup, the auction's rules, the cards to try, the
# strain, whether declarer is North or South, and the tricks the contract needs.
type Job is Data:
  Job{s: Setup, rules: List<&2, Rule>, cards: List<&2, U32>, t: U32, declns: Bool, goal: U32}

# The values of a list of cards in one layout, North-South's tricks, with the nodes and
# the memory.
type Vals is Type:
  Vals{vs: List<&2, U32>, nodes: Nat, m: Array<U32>}

def push(has: Bool, +v: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match has:
    case True{}:
      v <> acc
    case False{}:
      acc

# Solves each card in turn. r is the answer for the card before, if has says there
# was one, and its value is the guess for the next: cards often take the same.
def cards.solve(cs: List<&2, U32>, r: Z.Val, has: Bool, +d: Nat, +t: U32, +pos: R.Pos, +l01: U32, +l23: U32, acc: List<&2, U32>) -> Vals:
  match cs r:
    case Nil{} Z.Val{+v, n, m}:
      Vals{List.reverse(&2, U32, push(has, v, acc)), n, m}
    case Con{+c, rest} Z.Val{+v, n, m}:
      cards.solve(rest, P.card(d, t, pos, c, l01, l23, v, n, m), True{}, d, t, pos, l01, l23, push(has, v, acc))

# The tally of a run of layouts: for each card, declarer's tricks added up and the
# layouts where the contract makes.
type Tally is Data:
  Tally{sums: List<&2, U32>, makes: List<&2, U32>}

def tally.cons(+s: U32, +k: U32, t: Tally) -> Tally:
  match t:
    case Tally{ss, ks}:
      Tally{s <> ss, k <> ks}

def tally(vs: List<&2, U32>, sums: List<&2, U32>, makes: List<&2, U32>, +declns: Bool, +goal: U32) -> Tally:
  match vs sums makes:
    case Con{+v, a} Con{+s, b} Con{+k, c}:
      +mine = R.sel(declns, v, (13 - v : U32))
      tally.cons((s + mine : U32), (k + Bool.to_u32(U32.is_ge(mine, goal)) : U32), tally(a, b, c, declns, goal))
    case _ _ _:
      Tally{Nil{}, Nil{}}


# A layout that fits, found by dealing until one does: ok says one did before the
# fuel ran out, and tries counts the deals so far.
type Found is Data:
  Found{ok: Bool, deal: C.Deal, tries: U32}

def fits.dealt(+s: Setup, +rules: List<&2, Rule>, dl: Dealt) -> Bool:
  match dl:
    case Dealt{+deal, _}:
      fits(s, rules, deal)

# Deals until a layout fits. done says the layout in dl does.
def find(fuel: Nat, done: Bool, dl: Dealt, +tries: U32, +s: Setup, +rules: List<&2, Rule>) -> Found:
  match fuel done dl:
    case _ True{} Dealt{+deal, _}:
      Found{True{}, deal, tries}
    case 0n False{} Dealt{+deal, _}:
      Found{False{}, deal, tries}
    case 1n+p False{} Dealt{_, +seed}:
      +next = sample(s, seed)
      find(p, fits.dealt(s, rules, next), next, (tries + 1 : U32), s, rules)

# The random state for layout j of a simulation. Each layout has its own, so the
# layouts don't depend on how the work is split between threads.
def layout.seed(+seed: U32, +j: U32) -> U32:
  D.mix((D.mix(seed) + j * 2654435761 : U32))

# Looks for layout j: up to cap deals, from its own random state.
def find.layout(+job: Job, +seed: U32, +j: U32, +cap: U32, +tries: U32) -> Found:
  match job:
    case Job{+s, +rules, _, _, _, _}:
      find(U32.to_nat(cap), False{}, Dealt{C.deal.empty(), layout.seed(seed, j)}, tries, s, rules)

# A run of layouts in progress: the memory, the layouts kept and dealt, the nodes
# and the tally.
type Acc is Type:
  Acc{m: Array<U32>, deals: U32, tries: U32, nodes: Nat, sums: List<&2, U32>, makes: List<&2, U32>}

def acc.add(t: Tally, m: Array<U32>, +deals: U32, +tries: U32, n: Nat) -> Acc:
  match t:
    case Tally{ss, ks}:
      Acc{m, deals, tries, n, ss, ks}

def acc.solved(v: Vals, +deals: U32, +tries: U32, sums: List<&2, U32>, makes: List<&2, U32>, +declns: Bool, +goal: U32) -> Acc:
  match v:
    case Vals{vs, n, m}:
      acc.add(tally(vs, sums, makes, declns, goal), m, deals, tries, n)

# The first guess in a layout: the middle of what North-South can still get.
def guess(+s: Setup) -> U32:
  match s:
    case Setup{_, _, _, _, _, _, +pos, _, _, +d}:
      (R.pos.won(pos) + (d + 7) / 8 : U32)

def setup.d(+s: Setup) -> Nat:
  match s:
    case Setup{_, _, _, _, _, _, _, _, _, +d}:
      U32.to_nat(d)

def setup.l01(+s: Setup) -> U32:
  match s:
    case Setup{_, _, _, _, _, _, _, +l, _, _}:
      l

def setup.l23(+s: Setup) -> U32:
  match s:
    case Setup{_, _, _, _, _, _, _, _, +l, _}:
      l

def job.setup(+job: Job) -> Setup:
  match job:
    case Job{+s, _, _, _, _, _}:
      s

# The values of the cards to try in one layout.
def solve.layout(+job: Job, +deal: C.Deal, n: Nat, m: Array<U32>) -> Vals:
  match job:
    case Job{+s, _, +cs, +t, _, _}:
      cards.solve(cs, Z.Val{guess(s), n, m}, False{}, setup.d(s), t, pos.of(s, deal), setup.l01(s), setup.l23(s), Nil{})

# Solves a layout that was found and adds it to the tally.
def leaf.keep(ok: Bool, +deal: C.Deal, m: Array<U32>, +deals: U32, +tries: U32, n: Nat, sums: List<&2, U32>, makes: List<&2, U32>, +job: Job) -> Acc:
  match ok job:
    case False{} _:
      Acc{m, deals, tries, n, sums, makes}
    case True{} Job{_, _, _, _, +declns, +goal}:
      acc.solved(solve.layout(job, deal, n, m), (deals + 1 : U32), tries, sums, makes, declns, goal)

def leaf.found(f: Found, m: Array<U32>, +deals: U32, n: Nat, sums: List<&2, U32>, makes: List<&2, U32>, +job: Job) -> Acc:
  match f:
    case Found{+ok, +deal, +tries}:
      leaf.keep(ok, deal, m, deals, tries, n, sums, makes, job)

# Layouts j to j + k - 1, one after another with one memory.
def leaf(k: Nat, a: Acc, +j: U32, +seed: U32, +cap: U32, +job: Job) -> Acc:
  match k a:
    case 0n x:
      x
    case 1n+p Acc{m, +deals, +tries, n, sums, makes}:
      leaf(p, leaf.found(find.layout(job, seed, j, cap, tries), m, deals, n, sums, makes, job), (j + 1 : U32), seed, cap, job)

# The result of a simulation, or of part of one.
type Out is Data:
  Out{deals: U32, tries: U32, nodes: Nat, sums: List<&2, U32>, makes: List<&2, U32>}

def acc.out(a: Acc) -> Out:
  match a:
    case Acc{_, deals, tries, n, sums, makes}:
      Out{deals, tries, n, sums, makes}

def ints.add(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs ys:
    case Con{+x, a} Con{+y, b}:
      (x + y : U32) <> ints.add(a, b)
    case _ _:
      Nil{}

def out.join(a: Out, b: Out) -> Out:
  match a b:
    case Out{+d1, +t1, +n1, s1, k1} Out{+d2, +t2, +n2, s2, k2}:
      Out{(d1 + d2 : U32), (t1 + t2 : U32), Nat.add(n1, n2), ints.add(s1, s2), ints.add(k1, k2)}

def job.width(+job: Job) -> Nat:
  match job:
    case Job{_, _, +cs, _, _, _}:
      List.length(&2, U32, cs)

def zeros(+job: Job) -> List<&2, U32>:
  List.replicate(U32, job.width(job), 0)

# One leaf of the fork tree: layouts j to j + k - 1.
def leaf.run(none: Bool, +k: U32, +j: U32, +seed: U32, +cap: U32, +job: Job) -> Out:
  match none:
    case True{}:
      Out{0, 0, 0n, zeros(job), zeros(job)}
    case False{}:
      acc.out(leaf(U32.to_nat(k), Acc{P.memory(setup.d(job.setup(job))), 0, 0, 0n, zeros(job), zeros(job)}, j, seed, cap, job))

# Splits layouts j to j + n - 1 over a fork tree of the given depth.
def fork(+depth: Nat, +n: U32, +j: U32, +seed: U32, +cap: U32, +job: Job) -> Out:
  match depth:
    case 0n:
      leaf.run(U32.is_zero(n), n, j, seed, cap, job)
    case 1n+p:
      +half = (n / 2 : U32)
      a b = fork(p, half, j, seed, cap, job) fork(p, (n - half : U32), (j + half : U32), seed, cap, job)
      out.join(a, b)

# How deep to fork: about four leaves for each thread, so that a leaf that is
# unlucky with its layouts doesn't hold the rest up for long, and never more leaves
# than layouts. Each leaf makes a memory of its own, which takes some time at the
# start of a deal, so not too many either.
def fork.depth(+threads: U32, +n: U32) -> Nat:
  +wide = (U32.from_nat(U32.log2(U32.max(threads, 1))) + 2 : U32)
  U32.to_nat(U32.min(wide, U32.from_nat(U32.log2(U32.max(n, 1)))))

# Simulates n layouts, giving each at most cap deals to find one that fits.
def run(+job: Job, +n: U32, +seed: U32, +cap: U32, +threads: U32) -> Out:
  fork(fork.depth(threads, n), n, 0, seed, cap, job)

# ---------------------------------------------------------------------------
# Layouts one by one, for checking

# The first few layouts of a simulation, each as its deal in PBN and North-South's
# tricks with each card to try, in order, solved as a simulation solves them.
type Lay is Type:
  Lay{m: Array<U32>, lines: List<&2, String>}

def ints.text(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+x, t}:
      " " ++ U32.show(x) ++ ints.text(t)

def lay.line(v: Vals, +deal: C.Deal, lines: List<&2, String>) -> Lay:
  match v:
    case Vals{vs, _, m}:
      Lay{m, (N.print(deal) ++ " |" ++ ints.text(vs)) <> lines}

def lay.keep(ok: Bool, +deal: C.Deal, m: Array<U32>, lines: List<&2, String>, +job: Job) -> Lay:
  match ok:
    case False{}:
      Lay{m, lines}
    case True{}:
      lay.line(solve.layout(job, deal, 0n, m), deal, lines)

def lay.found(f: Found, m: Array<U32>, lines: List<&2, String>, +job: Job) -> Lay:
  match f:
    case Found{+ok, +deal, _}:
      lay.keep(ok, deal, m, lines, job)

def lay(k: Nat, a: Lay, +j: U32, +seed: U32, +cap: U32, +job: Job) -> Lay:
  match k a:
    case 0n x:
      x
    case 1n+p Lay{m, lines}:
      lay(p, lay.found(find.layout(job, seed, j, cap, 0), m, lines, job), (j + 1 : U32), seed, cap, job)

def lay.lines(a: Lay) -> List<&2, String>:
  match a:
    case Lay{_, lines}:
      List.reverse(&2, String, lines)

def layouts(+job: Job, +k: U32, +seed: U32, +cap: U32) -> List<&2, String>:
  lay.lines(lay(U32.to_nat(k), Lay{P.memory(setup.d(job.setup(job))), Nil{}}, 0, seed, cap, job))
