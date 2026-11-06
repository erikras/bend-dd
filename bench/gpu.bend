# bench/gpu.bend: the brute-force search on the GPU, against the same work on the
# CPU. The fork tree has 2^d leaves, and each one solves the whole table of a
# random ending with k cards in each hand.
#
#   bend bench/gpu.bend -o build/gpu
#   build/gpu 14 3                 # on the GPU
#   build/gpu 14 3 +RTS --gpu off  # the same work on every CPU thread
#
# Prints the total nodes and a checksum of the tricks, which must agree.

import Base
import ../src/cards.bend as C
import ../src/deal.bend as D
import ../src/brute.bend as B

# Keeps the first k cards of a holding at most, from the bottom. Answers the kept
# holding and the number still to keep, in one word: count << 16 | holding.
def trim.go(n: Nat, z: Bool, +m: U32, +left: U32, +kept: U32) -> U32:
  match n z:
    case 0n _:
      ((left << 16n) .|. kept : U32)
    case 1n+p True{}:
      ((left << 16n) .|. kept : U32)
    case 1n+p False{}:
      +b = (m .&. (0 - m) : U32)
      +rest = (m .^. b : U32)
      +left2 = (left - 1 : U32)
      trim.go(p, U32.is_zero(rest) || U32.is_zero(left2), rest, left2, (kept .|. b : U32))

def trim(+m: U32, +left: U32) -> U32:
  trim.go(13n, U32.is_zero(m) || U32.is_zero(left), m, left, 0)

def hand.trim(h: C.Hand, +k: U32) -> C.Hand:
  match h:
    case C.Hand{s, x, d, c}:
      +a = trim(s, k)
      +b = trim(x, (a >> 16n : U32))
      +e = trim(d, (b >> 16n : U32))
      +f = trim(c, (e >> 16n : U32))
      C.Hand{(a .&. 65535 : U32), (b .&. 65535 : U32), (e .&. 65535 : U32), (f .&. 65535 : U32)}

def ending(d: C.Deal, +k: U32) -> C.Deal:
  match d:
    case C.Deal{n, e, s, w}:
      C.Deal{hand.trim(n, k), hand.trim(e, k), hand.trim(s, k), hand.trim(w, k)}

type Sum is Data:
  Sum{nodes: U32, tricks: U32}

def tricks.sum(xs: List<&2, U32>, +acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      tricks.sum(t, (acc * 31 + h : U32))

def leaf.go(t: B.Table) -> Sum:
  match t:
    case B.Table{ts, n}:
      Sum{n, tricks.sum(ts, 0)}

def leaf(+i: U32, +k: U32) -> Sum:
  leaf.go(B.table(ending(D.random(i), k)))

def merge(a: Sum, b: Sum) -> Sum:
  match a b:
    case Sum{n1, t1} Sum{n2, t2}:
      Sum{(n1 + n2 : U32), (t1 + t2 : U32)}

def run(+d: Nat, +i: U32, +k: U32) -> Sum:
  match d:
    case 0n:
      leaf(i, k)
    case 1n+p:
      a b = run(p, i, k) run(p, (i + (1 << p) : U32), k)
      merge(a, b)

def show(s: Sum) -> String:
  match s:
    case Sum{n, t}:
      "nodes " ++ U32.show(n) ++ " checksum " ++ U32.show(t)

def go(+d: Nat, +k: U32) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    s : Sum = run!(d, 0, k)
    IO.print(show(s))
    t1 : Nat <- IO.now()
    IO.print(U32.show(U32.from_nat(Nat.sub(t1, t0))) ++ " ms")

def arg(m: Maybe<&2, U32>, +fallback: U32) -> U32:
  match m:
    case None{}:
      fallback
    case Some{v}:
      v

def go.args(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{_, Con{d, Con{k, _}}}:
      go(U32.to_nat(arg(U32.read(d), 10)), arg(U32.read(k), 3))
    case _:
      go(10n, 3)

def main() -> IO(Unit):
  IO.bind(List<String>, Unit, IO.args(), go.args)
