# tests/unit.bend: unit tests. Prints each failure and exits non-zero if any.

import Base
import ../src/cards.bend as C
import ../src/pbn.bend as P
import ../src/rules.bend as R
import ../src/brute.bend as B
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
# Dealer

def dealer.checks() -> List<&2, Check>:
  [
    Check{"deal 42", String.eq(P.print(D.random(42)), full())},
    Check{"a deal has 13 cards each", B.deal.even(D.random(7)) && U32.is_eq(B.deal.cards(D.random(7)), 52)}
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
          List.append(&2, Check, brute.checks(), dealer.checks())))))

def main() -> IO(Unit):
  do IO<Unit>:
    +fails : U32 <- report(checks(), 0)
    finish(U32.is_zero(fails), fails)
