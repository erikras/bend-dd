# tests/exhaust.bend: every ending of a given size, not a sample.
#
#   tests/exhaust [cards]
#
# See src/every.bend. Above the sizes this can reach, tests/oracle takes samples.

import Base
import ../src/every.bend as E

def arg.read(r: Maybe<&2, U32>, +fallback: U32) -> U32:
  match r:
    case None{}:
      fallback
    case Some{x}:
      x

def report.go(good: Bool, +text: String) -> IO(Unit):
  match good:
    case True{}:
      IO.print("OK: " ++ text)
    case False{}:
      IO.die(Unit, 1, "FAIL: " ++ text)

def report(s: E.Sum, +k: U32, +ms: Nat) -> IO(Unit):
  match s:
    case E.Sum{+deals, +bad, +lens, +owners}:
      report.go(Nat.is_eq(bad, 0n), "every " ++ U32.show(k) ++ "-card ending: " ++ Nat.show(deals) ++ " deals, " ++ Nat.show(bad) ++ " wrong; first wrong: lengths " ++ U32.hex(lens) ++ " owners " ++ U32.hex(owners) ++ "; " ++ Nat.show(ms) ++ " ms")

def run(xs: List<&2, U32>, +k: U32, a: E.Sum) -> IO(E.Sum):
  match xs:
    case Nil{}:
      IO.pure(E.Sum, a)
    case Con{+h, t}:
      do IO<E.Sum>:
        +s : E.Sum = E.of.lens(5n, k, h)
        run(t, k, E.add(a, s))

def main.go(+k: U32) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    +s : E.Sum <- run(E.lens.all(k), k, E.zero())
    t1 : Nat <- IO.now()
    report(s, k, Nat.sub(t1, t0))

def args.go(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{_, Con{a, _}}:
      main.go(arg.read(U32.read(a), 2))
    case _:
      main.go(2)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    args.go(args)
