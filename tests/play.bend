# tests/play.bend: checks the value of single cards against brute force.
#
#   tests/play [count] [cards] [seed]
#
# Deals count random endings with this many cards in each hand, picks a strain and a
# leader, plays a random number of random legal cards, so that the position is as
# often in the middle of a trick as at its start, and then compares, for every legal
# card of the player to move, the tricks src/play.bend gives it against plain minimax.

import Base
import ../src/cards.bend as C
import ../src/rules.bend as R
import ../src/brute.bend as B
import ../src/deal.bend as D
import ../src/search.bend as Z
import ../src/play.bend as P

type Sum is Data:
  Sum{bad: U32, first: U32, cards: U32}

def nth(xs: List<&2, U32>, n: Nat) -> U32:
  match xs n:
    case Nil{} _:
      0
    case Con{h, _} 0n:
      h
    case Con{_, t} 1n+p:
      nth(t, p)

# Plays k random legal cards, each picked by the next step of the generator.
def wander(k: Nat, +seed: U32, +t: U32, +pos: R.Pos, acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      List.reverse(&2, U32, acc)
    case 1n+p:
      +x = D.lcg(seed)
      +ms = R.moves(pos)
      +n = U32.from_nat(List.length(&2, U32, ms))
      +c = nth(ms, U32.to_nat(((x >> 16n) % n : U32)))
      wander(p, x, t, R.play(t, pos, c), c <> acc)

def brute.value(r: B.Res) -> U32:
  match r:
    case B.Res{v, _}:
      v

def brute(+d: Nat, +t: U32, +pos: R.Pos, +c: U32) -> U32:
  brute.value(B.solve(Nat.sub(d, 1n), t, R.play(t, pos, c), 0n))

# Compares every legal card. r is the answer for the card before, which should be
# want, and its memory goes on to the next card, as in a simulation.
def cards.check(xs: List<&2, U32>, r: Z.Val, +want: U32, +d: Nat, +t: U32, +pos: R.Pos, +l01: U32, +l23: U32, +bad: U32, +n: U32) -> U32 & U32:
  match xs r:
    case Nil{} Z.Val{+v, _, _}:
      ((bad + Bool.to_u32(U32.is_ne(v, want)) : U32), n)
    case Con{+c, rest} Z.Val{+v, _, m}:
      cards.check(rest, P.card(d, t, pos, c, l01, l23, 7, 0n, m), brute(d, t, pos, c), d, t, pos, l01, l23, (bad + Bool.to_u32(U32.is_ne(v, want)) : U32), (n + 1 : U32))

def one.at(p: P.At, +d: Nat, +t: U32) -> U32 & U32:
  match p:
    case P.At{+pos, +l01, +l23}:
      cards.check(R.moves(pos), Z.Val{0, 0n, P.memory(d)}, 0, d, t, pos, l01, l23, 0, 0)

# One ending: its strain, leader and the cards played before the check all come from
# the seed.
def one(+seed: U32, +k: U32) -> U32 & U32:
  +deal = D.ending(seed, k)
  +x = D.mix((seed + 77 : U32))
  +t = ((x >> 8n) % 5 : U32)
  +leader = ((x >> 12n) % 4 : U32)
  +plays = U32.to_nat(((x >> 16n) % (4 * k - 1) : U32))
  +start = R.pos.start(deal, leader)
  +d = Nat.sub(U32.to_nat((4 * k : U32)), plays)
  one.at(P.live.after(wander(plays, x, t, start, Nil{}), t, start), d, t)

def first.of(clean: Bool, +g: U32, +f: U32) -> U32:
  match clean:
    case True{}:
      g
    case False{}:
      f

def add(a: Sum, +seed: U32, r: U32 & U32) -> Sum:
  match a:
    case Sum{+bad, +first, +n}:
      match r:
        case (+b, +c):
          Sum{(bad + Bool.to_u32(U32.is_ne(b, 0)) : U32), first.of(U32.is_zero(bad) && U32.is_ne(b, 0), seed, first), (n + c : U32)}

def run(k: Nat, +seed: U32, +cards: U32, acc: Sum) -> Sum:
  match k:
    case 0n:
      acc
    case 1n+p:
      run(p, (seed + 1 : U32), cards, add(acc, seed, one(seed, cards)))

def num(r: Maybe<&2, U32>, +fallback: U32) -> U32:
  match r:
    case None{}:
      fallback
    case Some{x}:
      x

def arg(xs: List<&2, String>, n: Nat, +fallback: U32) -> U32:
  match xs n:
    case Nil{} _:
      fallback
    case Con{a, _} 0n:
      num(U32.read(a), fallback)
    case Con{_, t} 1n+p:
      arg(t, p, fallback)

def report.fail(ok: Bool, +first: U32) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, "FAIL: first at seed " ++ U32.show(first))

def report(s: Sum, +count: U32, +k: U32) -> IO(Unit):
  match s:
    case Sum{+bad, +first, +n}:
      do IO<Unit>:
        IO.print(U32.show(count) ++ " endings of " ++ U32.show(k) ++ " cards, " ++ U32.show(n) ++ " cards checked: " ++ U32.show(bad) ++ " endings disagree")
        report.fail(U32.is_zero(bad), first)

def args.data(xs: List<String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      h <> args.data(t)

def main.go(+args: List<&2, String>) -> IO(Unit):
  +count = arg(args, 1n, 1000)
  +k = arg(args, 2n, 3)
  +seed = arg(args, 3n, 1)
  report(run(U32.to_nat(count), seed, k, Sum{0, 0, 0}), count, k)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    main.go(args.data(args))
