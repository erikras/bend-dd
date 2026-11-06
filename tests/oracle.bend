# tests/oracle.bend: checks the search against brute-force minimax, with no DDS.
#
#   tests/oracle [count] [cards] [seed]
#
# Deals count random endings with this many cards in each hand and compares whole
# tables, in all 5 strains with all 4 leaders. Prints the node counts of both.

import Base
import ../src/cards.bend as C
import ../src/brute.bend as B
import ../src/search.bend as Z
import ../src/deal.bend as D

# A total: endings that disagreed, then nodes by brute force and by the search.
type Sum is Data:
  Sum{bad: U32, first: U32, brute: Nat, fast: Nat}

def ints.eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, s} Con{y, t}:
      Bool.and(U32.is_eq(x, y), ints.eq(s, t))
    case _ _:
      False{}

def compare(+seed: U32, a: B.Table, b: B.Table) -> Sum:
  match a b:
    case B.Table{x, n} B.Table{y, m}:
      +same = ints.eq(x, y)
      Sum{Bool.to_u32(Bool.not(same)), seed, n, m}

def one(+seed: U32, +k: U32) -> Sum:
  +deal = D.ending(seed, k)
  compare(seed, B.table(deal), Z.table(deal))

def first.of(clean: Bool, +g: U32, +f: U32) -> U32:
  match clean:
    case True{}:
      g
    case False{}:
      f

def add(a: Sum, b: Sum) -> Sum:
  match a b:
    case Sum{+x, f, n, m} Sum{+y, g, p, q}:
      Sum{(x + y : U32), first.of(U32.is_zero(x), g, f), Nat.add(n, p), Nat.add(m, q)}

def seq(n: Nat, +seed: U32, +k: U32) -> Sum:
  match n:
    case 0n:
      Sum{0, 0, 0n, 0n}
    case 1n+p:
      add(one(seed, k), seq(p, (seed + 1 : U32), k))

# Solves n endings from seed on, over a fork tree of the given depth.
def batch(+depth: Nat, +n: Nat, +seed: U32, +k: U32) -> Sum:
  match depth:
    case 0n:
      seq(n, seed, k)
    case 1n+p:
      +half = Nat.div(n, 2n)
      a b = batch(p, half, seed, k) batch(p, Nat.sub(n, half), (seed + U32.from_nat(half) : U32), k)
      add(a, b)

def arg.read(r: Maybe<&2, U32>, +fallback: U32) -> U32:
  match r:
    case None{}:
      fallback
    case Some{x}:
      x

def finish(good: Bool, +text: String) -> IO(Unit):
  match good:
    case True{}:
      IO.print("OK: " ++ text)
    case False{}:
      IO.die(Unit, 1, "FAIL: " ++ text)

def report(s: Sum, +count: U32, +k: U32, +ms: Nat) -> IO(Unit):
  match s:
    case Sum{+bad, first, brute, fast}:
      finish(U32.is_zero(bad), U32.show(count) ++ " " ++ U32.show(k) ++ "-card endings, " ++ U32.show(bad) ++ " differ (first at seed " ++ U32.show(first) ++ "); nodes: brute " ++ Nat.show(brute) ++ ", search " ++ Nat.show(fast) ++ "; " ++ Nat.show(ms) ++ " ms")

def run(+count: U32, +k: U32, +seed: U32) -> IO(Unit):
  do IO<Unit>:
    +threads : U32 <- IO.thread_count()
    t0 : Nat <- IO.now()
    +sum : Sum = batch(Nat.add(6n, U32.log2((threads * 2 - 1 : U32))), U32.to_nat(count), seed, k)
    t1 : Nat <- IO.now()
    report(sum, count, k, Nat.sub(t1, t0))

def main.go(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{_, Con{a, Con{b, Con{c, _}}}}:
      run(arg.read(U32.read(a), 1000), arg.read(U32.read(b), 4), arg.read(U32.read(c), 1))
    case Con{_, Con{a, Con{b, _}}}:
      run(arg.read(U32.read(a), 1000), arg.read(U32.read(b), 4), 1)
    case _:
      run(1000, 4, 1)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    main.go(args)
