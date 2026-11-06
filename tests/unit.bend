# tests/unit.bend: unit tests. Prints each failure and exits non-zero if any.

import Base
import ../src/cards.bend as C
import ../src/pbn.bend as P
import ../src/rules.bend as R
import ../src/brute.bend as B
import ../src/search.bend as Z
import ../src/deal.bend as D

type Check is Data:
  Check{name: String, good: Bool}

def ints.eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, s} Con{y, t}:
      Bool.and(U32.is_eq(x, y), ints.eq(s, t))
    case _ _:
      False{}

# ---------------------------------------------------------------------------
# PBN

def print.of(d: Maybe<&2, C.Deal>) -> String:
  match d:
    case None{}:
      "none"
    case Some{x}:
      P.print(x)

def parses(+s: String, +want: String) -> Bool:
  String.eq(print.of(P.parse(s)), want)

def rejects(+s: String) -> Bool:
  String.eq(print.of(P.parse(s)), "none")

def full() -> String:
  "N:A8.J94.KQ62.KT86 K64.873.A3.Q5432 QJ73.AKQ65.98.AJ T952.T2.JT754.97"

def pbn.checks() -> List<&2, Check>:
  [
    Check{"parse full deal", parses(full(), full())},
    Check{"parse from east", parses("E:K64.873.A3.Q5432 QJ73.AKQ65.98.AJ T952.T2.JT754.97 A8.J94.KQ62.KT86", full())},
    Check{"parse from south", parses("S:QJ73.AKQ65.98.AJ T952.T2.JT754.97 A8.J94.KQ62.KT86 K64.873.A3.Q5432", full())},
    Check{"parse from west", parses("W:T952.T2.JT754.97 A8.J94.KQ62.KT86 K64.873.A3.Q5432 QJ73.AKQ65.98.AJ", full())},
    Check{"parse voids", parses("N:AK... Q.J.. J..A. T..K.", "N:AK... Q.J.. J..A. T..K.")},
    Check{"parse rank order is free", parses("N:KA... ... ... ...", "N:AK... ... ... ...")},
    Check{"reject bad seat", rejects("X:A... K... Q... J...")},
    Check{"reject no colon", rejects("NA... K... Q... J...")},
    Check{"reject three hands", rejects("N:A... K... Q...")},
    Check{"reject five hands", rejects("N:A... K... Q... J... T...")},
    Check{"reject three suits", rejects("N:A.. K... Q... J...")},
    Check{"reject five suits", rejects("N:A.... K... Q... J...")},
    Check{"reject bad rank", rejects("N:1... K... Q... J...")},
    Check{"reject repeat in a hand", rejects("N:AA... K... Q... J...")},
    Check{"reject repeat across hands", rejects("N:A... A... Q... J...")},
    Check{"reject empty", rejects("")}
  ]

# ---------------------------------------------------------------------------
# Rules

def s(+r: U32) -> U32:
  C.card.make(0, r)

def h(+r: U32) -> U32:
  C.card.make(1, r)

def d(+r: U32) -> U32:
  C.card.make(2, r)

def c(+r: U32) -> U32:
  C.card.make(3, r)

# A hand's two words from its four holdings.
def w01(+sp: U32, +ht: U32) -> U32:
  ((sp << 16n) .|. ht : U32)

def moves.checks() -> List<&2, Check>:
  +h01 = w01(4097, 6)
  +h23 = w01(0, 16)
  [
    Check{"on lead: all cards, spades and high first",
      ints.eq(R.moves.of(4, h01, h23), [s(12), s(0), h(2), h(1), c(4)])},
    Check{"follow spades", ints.eq(R.moves.of(0, h01, h23), [s(12), s(0)])},
    Check{"follow hearts", ints.eq(R.moves.of(1, h01, h23), [h(2), h(1)])},
    Check{"follow clubs", ints.eq(R.moves.of(3, h01, h23), [c(4)])},
    Check{"void in diamonds: all cards",
      ints.eq(R.moves.of(2, h01, h23), [s(12), s(0), h(2), h(1), c(4)])},
    Check{"empty hand", ints.eq(R.moves.of(4, 0, 0), Nil{})}
  ]

def beats.checks() -> List<&2, Check>:
  [
    Check{"higher in suit wins", R.beats(4, s(3), s(4))},
    Check{"lower in suit loses", Bool.not(R.beats(4, s(4), s(3)))},
    Check{"discard loses at NT", Bool.not(R.beats(4, s(0), h(12)))},
    Check{"trump beats side suit", R.beats(1, s(12), h(0))},
    Check{"side suit loses to trump", Bool.not(R.beats(1, h(0), s(12)))},
    Check{"higher trump wins", R.beats(1, h(0), h(1))},
    Check{"lower trump loses", Bool.not(R.beats(1, h(1), h(0)))},
    Check{"off-suit discard loses in a suit contract", Bool.not(R.beats(1, s(0), d(12)))}
  ]

def run(+t: U32, +leader: U32, +a: U32, +b: U32, +x: U32, +y: U32) -> U32:
  +t1 = R.trick.next(R.trick.start(leader), t, a)
  +t2 = R.trick.next(t1, t, b)
  +t3 = R.trick.next(t2, t, x)
  R.trick.seat(R.trick.next(t3, t, y))

def trick.checks() -> List<&2, Check>:
  [
    Check{"highest of the suit led wins", U32.is_eq(run(4, 0, s(3), s(7), s(5), s(1)), 1)},
    Check{"leader wins when nobody beats it", U32.is_eq(run(4, 2, s(9), s(7), h(12), d(12)), 2)},
    Check{"ruff wins", U32.is_eq(run(1, 0, s(12), h(0), s(3), s(4)), 1)},
    Check{"overruff wins", U32.is_eq(run(1, 3, s(12), h(0), h(5), s(4)), 1)},
    Check{"fourth hand wins", U32.is_eq(run(4, 1, c(1), c(2), c(3), c(4)), 0)}
  ]

# ---------------------------------------------------------------------------
# Brute force

def table.tricks(t: B.Table) -> List<&2, U32>:
  match t:
    case B.Table{ts, _}:
      ts

def table.of(d: Maybe<&2, C.Deal>) -> List<&2, U32>:
  match d:
    case None{}:
      Nil{}
    case Some{+x}:
      table.tricks(B.table(x))

def table.is(+pbn: String, want: List<&2, U32>) -> Bool:
  ints.eq(table.of(P.parse(pbn)), want)

# Hand-worked endings, as strain then declarer N E S W.
def brute.checks() -> List<&2, Check>:
  [
    # North holds the top spade: spades win whoever leads, so N-S always take it.
    Check{"one trick",
      table.is("N:A... K... Q... J...", [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0])},
    # Everyone holds a different suit. The holder of the trump takes the trick,
    # and at NT the leader does, who is always on the defending side.
    Check{"four suits",
      table.is("N:A... .A.. ..A. ...A", [1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0])},
    Check{"no cards",
      table.is("N:... ... ... ...", [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])}
  ]

# ---------------------------------------------------------------------------
# Search

def search.of(d: Maybe<&2, C.Deal>) -> List<&2, U32>:
  match d:
    case None{}:
      Nil{}
    case Some{+x}:
      table.tricks(Z.table(x))

def search.is(+pbn: String, want: List<&2, U32>) -> Bool:
  ints.eq(search.of(P.parse(pbn)), want)

# Spots by rank, with bit 12 the ace: A 4096, K 2048, Q 1024, J 512, T 256.
def tops.checks() -> List<&2, Check>:
  [
    Check{"AK in play together is one move", U32.is_eq(Z.tops(6144, 6144), 4096)},
    Check{"AQ with the K gone is one move", U32.is_eq(Z.tops(5120, 5120), 4096)},
    Check{"AQ with the K elsewhere is two", U32.is_eq(Z.tops(5120, 7168), 5120)},
    Check{"K and J with the Q on the table is two", U32.is_eq(Z.tops(2560, 3584), 2560)},
    Check{"K and J with the Q played earlier is one", U32.is_eq(Z.tops(2560, 2560), 2048)},
    Check{"a run and a split", U32.is_eq(Z.tops((4096 .|. 2048 .|. 512 .|. 1 : U32), 8191), (4096 .|. 512 .|. 1 : U32))},
    Check{"the low card of a gap run goes", U32.is_eq(Z.tops((256 .|. 1 : U32), (256 .|. 1 : U32)), 256)},
    Check{"void", U32.is_eq(Z.tops(0, 8191), 0)}
  ]

def cut.checks() -> List<&2, Check>:
  [
    Check{"already there", U32.is_eq(Z.cut(3, 2, 3), 1)},
    Check{"out of reach", U32.is_eq(Z.cut(3, 2, 6), 2)},
    Check{"just in reach is open", U32.is_eq(Z.cut(3, 2, 5), 0)},
    Check{"one more is open", U32.is_eq(Z.cut(3, 2, 4), 0)},
    Check{"nothing left decides", U32.is_eq(Z.cut(3, 0, 4), 2)}
  ]

def after.go(+t: U32, xs: List<&2, U32>, pos: R.Pos) -> R.Pos:
  match xs:
    case Nil{}:
      pos
    case Con{c, r}:
      after.go(t, r, R.play(t, pos, c))

# A position from a deal led by North, where a list of cards has been played.
def after(+t: U32, d: Maybe<&2, C.Deal>, xs: List<&2, U32>) -> R.Pos:
  match d:
    case None{}:
      R.pos.start(C.deal.empty(), 0)
    case Some{x}:
      after.go(t, xs, R.pos.start(x, 0))

# The cards of a list as one mask, ignoring suits.
def list.mask(xs: List<&2, U32>, +acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{+c, t}:
      list.mask(t, (acc .|. C.card.bit(c) : U32))

def counts.of(+t: U32, +leader: U32, d: Maybe<&2, C.Deal>, +left: U32) -> U32:
  match d:
    case None{}:
      99999
    case Some{x}:
      Z.counts(t, R.pos.start(x, leader), left)

# What the search is sure of: quick tricks in the low byte, later tricks above that.
def sure.is(+pbn: String, +t: U32, +left: U32, +q: U32, +l: U32) -> Bool:
  U32.is_eq(counts.of(t, 0, P.parse(pbn), left), (q .|. (l << 8n) : U32))

# Hand-worked, with North on lead.
def sure.checks() -> List<&2, Check>:
  [
    # Two top spades, then a heart across to South's two top hearts, capped at 3.
    Check{"quick: cash, cross and cap", sure.is("N:AK.2.. QJ.3.. 3.A5.. T9.4..", 4, 3, 3, 0)},
    # In hearts, the spades still stand up, since each opponent has two.
    Check{"quick: safe from ruffs, trump entry", sure.is("N:AK.2.. QJ.3.. 3.A5.. T9.4..", 1, 3, 3, 0)},
    # East ruffs at once, so the top hearts are worth nothing. East and West each have
    # two trumps against none.
    Check{"later: all the trumps", sure.is("N:.AK.. A2... .QJ.. KQ...", 0, 2, 0, 2)},
    # The top two trumps are alone and can fall together.
    Check{"later: two singleton top trumps are one trick", sure.is("N:2.A.. A.2.. 3.K.. K.3..", 0, 2, 1, 1)},
    # East's K can wait behind North's A.
    Check{"later: a second trump behind the top one", sure.is("N:A2... K3... T9... 87...", 0, 2, 1, 1)},
    Check{"later: not when it is in front", sure.is("N:A2... 87... T9... K3...", 0, 2, 1, 0)},
    # No trumps: North can only lead to the opposing top card.
    Check{"later: no top card in any suit the leader has", sure.is("N:2... A... 3... 4...", 4, 1, 0, 1)}
  ]

def lead.then(+t: U32, d: Maybe<&2, C.Deal>, +c: U32, +won: U32, +left: U32, +target: U32) -> U32:
  match d:
    case None{}:
      99
    case Some{x}:
      Z.second(t, R.play(t, R.pos.start(x, 0), c), won, left, target)

# After the lead: the side with the best hand left for this trick is sure of it.
def second.checks() -> List<&2, Check>:
  [
    Check{"after the lead: East's ace beats it", U32.is_eq(lead.then(4, P.parse("N:2... A... 3... 4..."), s(0), 0, 1, 1), 2)},
    Check{"after the lead: North's ace holds", U32.is_eq(lead.then(4, P.parse("N:A... 2... 3... 4..."), s(12), 0, 1, 1), 1)},
    Check{"after the lead: East ruffs", U32.is_eq(lead.then(1, P.parse("N:A... .2.. 3... 4..."), s(12), 0, 1, 1), 2)},
    Check{"after the lead: a trick does not reach the target", U32.is_eq(lead.then(4, P.parse("N:AK... 23... 45... 67..."), s(12), 0, 2, 2), 0)}
  ]

def order.checks() -> List<&2, Check>:
  # Hand-worked: East is second to play on the spade Q led by North, holding K J 2,
  # with the A and T elsewhere. The Q on the table still splits K from J.
  +p = after(4, P.parse("N:Q.A32.. KJ2.5.. A.KQJ.. T.T98.."), [s(10)])
  +live01 = R.pos.live01(p)
  +l01 = (live01 .|. (1024 << 16n) : U32)
  [
    Check{"second hand keeps K, J and 2 apart, with the Q on the table",
      U32.is_eq(C.bits.count(list.mask(Z.gen(4, p, l01, 0, Z.mem.none(), 7), 0)), 3)},
    Check{"without the Q on the table, K and J are one move",
      U32.is_eq(C.bits.count(list.mask(Z.gen(4, p, live01, 0, Z.mem.none(), 7), 0)), 2)}
  ]

def search.checks() -> List<&2, Check>:
  [
    Check{"search: one trick",
      search.is("N:A... K... Q... J...", [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0])},
    Check{"search: four suits",
      search.is("N:A... .A.. ..A. ...A", [1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0])},
    Check{"search: no cards",
      search.is("N:... ... ... ...", [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])},
    # Two cards each, where the second trick depends on the first.
    Check{"search: agrees with brute on a two-card ending",
      ints.eq(search.of(P.parse("N:AK... Q.J.. J..A. T..K.")), table.of(P.parse("N:AK... Q.J.. J..A. T..K.")))}
  ]

# ---------------------------------------------------------------------------
# Dealer

def dealer.checks() -> List<&2, Check>:
  [
    Check{"deal 42", String.eq(P.print(D.random(42)), full())},
    Check{"a deal has 13 cards each", B.deal.even(D.random(7)) && U32.is_eq(B.deal.cards(D.random(7)), 52)},
    Check{"an ending has k cards each", B.deal.even(D.ending(7, 5)) && U32.is_eq(B.deal.cards(D.ending(7, 5)), 20)},
    Check{"a 13-card ending is a whole deal", B.deal.even(D.ending(7, 13)) && U32.is_eq(B.deal.cards(D.ending(7, 13)), 52)}
  ]

# ---------------------------------------------------------------------------
# Running

def count(good: Bool, +fails: U32) -> U32:
  match good:
    case True{}:
      fails
    case False{}:
      (fails + 1 : U32)

def say(good: Bool, name: String) -> IO(Unit):
  match good:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.print("FAILED: " ++ name)

def report(checks: List<&2, Check>, +fails: U32) -> IO(U32):
  match checks:
    case Nil{}:
      IO.pure(U32, fails)
    case Con{Check{name, +good}, t}:
      do IO<U32>:
        say(good, name)
        report(t, count(good, fails))

def finish(ok: Bool, +fails: U32) -> IO(Unit):
  match ok:
    case True{}:
      IO.print("OK: unit tests")
    case False{}:
      IO.die(Unit, 1, U32.show(fails) ++ " unit tests failed")

def checks() -> List<&2, Check>:
  List.append(&2, Check, pbn.checks(),
    List.append(&2, Check, moves.checks(),
      List.append(&2, Check, beats.checks(),
        List.append(&2, Check, trick.checks(),
          List.append(&2, Check, brute.checks(),
            List.append(&2, Check, tops.checks(),
              List.append(&2, Check, cut.checks(),
                List.append(&2, Check, sure.checks(),
                  List.append(&2, Check, second.checks(),
                    List.append(&2, Check, order.checks(),
                      List.append(&2, Check, search.checks(), dealer.checks())))))))))))

def main() -> IO(Unit):
  do IO<Unit>:
    +fails : U32 <- report(checks(), 0)
    finish(U32.is_zero(fails), fails)
