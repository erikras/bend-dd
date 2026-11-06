# dd.bend: the double dummy solver's command line.
#
#   dd [deal or file]...
#
# Each argument is either one PBN deal, quoted so that it stays one argument,
# or a file with one deal per line. Blank lines and lines starting with # are
# skipped. For now dd prints each deal back in canonical form, starting from
# North.
#
#   dd --brute [deal or file]...
#
# Solves small endings by plain minimax. Each deal prints one line: the 20
# entries of its double dummy table, strain then declarer as in DDS's TABLE
# lines, then the number of positions visited. A summary goes to stderr.

import Base
import ./src/cards.bend as C
import ./src/pbn.bend as P
import ./src/brute.bend as B

# ---------------------------------------------------------------------------
# Reading deals

def line.keep(+s: String) -> Bool:
  Bool.not(String.is_empty(s) || String.starts_with(s, "#"))

def lines.add(keep: Bool, s: String, rest: List<&2, String>) -> List<&2, String>:
  match keep:
    case True{}:
      s <> rest
    case False{}:
      rest

# The lines of a file that hold a deal, trimmed.
def lines.clean(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      +s = String.trim(h)
      lines.add(line.keep(s), s, lines.clean(t))

# An argument is a deal when its second character is the colon after the seat.
def arg.is_deal(s: String) -> Bool:
  match s:
    case SCon{_, SCon{Chr{c}, _}}:
      U32.is_eq(c, 58)
    case _:
      False{}

def file.read.text(p: File & Result<&1, &1, U32 & String, String>) -> IO(List<&2, String>):
  match p:
    case (f, r):
      do IO<List<&2, String>>:
        File.close(f)
        s : String <- IO.pass(String, r)
        return lines.clean(String.lines(s))

def file.read.size(p: File & Result<&1, &1, U32 & String, U32>) -> IO(List<&2, String>):
  match p:
    case (f, r):
      do IO<List<&2, String>>:
        n : U32 <- IO.pass(U32, r)
        q : File & Result<&1, &1, U32 & String, String> <- File.read(f, n)
        file.read.text(q)

def file.read(path: String) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    f : File <- IO.try(File, File.open(path, "r"))
    p : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
    file.read.size(p)

def arg.read.go(deal: Bool, +a: String) -> IO(List<&2, String>):
  match deal:
    case True{}:
      IO.pure(List<&2, String>, [a])
    case False{}:
      file.read(a)

def arg.read(+a: String) -> IO(List<&2, String>):
  arg.read.go(arg.is_deal(a), a)

def list.append(xs: List<&2, String>, ys: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      h <> list.append(t, ys)

# All the deals named by the arguments, in order.
def args.read(xs: List<String>) -> IO(List<&2, String>):
  match xs:
    case Nil{}:
      IO.pure(List<&2, String>, Nil{})
    case Con{a, t}:
      do IO<List<&2, String>>:
        here : List<&2, String> <- arg.read(a)
        rest : List<&2, String> <- args.read(t)
        return list.append(here, rest)

# ---------------------------------------------------------------------------
# Printing deals

def show(+text: String, d: Maybe<&2, C.Deal>) -> IO(Unit):
  match d:
    case None{}:
      IO.die(Unit, 1, "dd: not a PBN deal: " ++ text)
    case Some{deal}:
      IO.print(P.print(deal))

def show.all(xs: List<&2, String>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+h, t}:
      do IO<Unit>:
        show(h, P.parse(h))
        show.all(t)

# ---------------------------------------------------------------------------
# Solving endings

# The output of one deal: its line, whether it is a good one, and its nodes.
type Out is Data:
  Out{good: Bool, line: String, nodes: U32}

def ints.show(xs: List<&2, U32>, tail: String) -> String:
  match xs:
    case Nil{}:
      tail
    case Con{h, t}:
      U32.show(h) ++ " " ++ ints.show(t, tail)

def brute.show(t: B.Table) -> Out:
  match t:
    case B.Table{ts, +n}:
      Out{True{}, ints.show(ts, U32.show(n)), n}

def brute.even(even: Bool, text: String, +deal: C.Deal) -> Out:
  match even:
    case True{}:
      brute.show(B.table(deal))
    case False{}:
      Out{False{}, "dd: hands differ in length: " ++ text, 0}

def brute.parsed(+text: String, d: Maybe<&2, C.Deal>) -> Out:
  match d:
    case None{}:
      Out{False{}, "dd: not a PBN deal: " ++ text, 0}
    case Some{+deal}:
      brute.even(B.deal.even(deal), text, deal)

def brute.one(+text: String) -> Out:
  brute.parsed(text, P.parse(text))

def brute.seq(xs: List<&2, String>) -> List<&2, Out>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      brute.one(h) <> brute.seq(t)

# Solves a list of n deals over a fork tree of the given depth.
def brute.batch(+depth: Nat, +n: Nat, +xs: List<&2, String>) -> List<&2, Out>:
  match depth:
    case 0n:
      brute.seq(xs)
    case 1n+p:
      +half = Nat.div(n, 2n)
      a b = brute.batch(p, half, List.take(&2, String, xs, half)) brute.batch(p, Nat.sub(n, half), List.drop(&2, String, xs, half))
      List.append(&2, Out, a, b)

# Prints every line, stopping at the first failure.
def brute.print.go(good: Bool, line: String) -> IO(Unit):
  match good:
    case True{}:
      IO.print(line)
    case False{}:
      IO.die(Unit, 1, line)

def brute.print(xs: List<&2, Out>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{Out{good, line, _}, t}:
      do IO<Unit>:
        brute.print.go(good, line)
        brute.print(t)

# How deep a fork tree must go to give every thread a share.
def fork.depth(+threads: U32) -> Nat:
  U32.log2((threads * 2 - 1 : U32))

# Runs a whole list of deals. The results are forced before the clock is read
# again, since compiled code is strict, so the time covers the solving.
def brute.run(+xs: List<&2, String>) -> IO(Unit):
  +n = List.length(&2, String, xs)
  do IO<Unit>:
    +threads : U32 <- IO.thread_count()
    t0 : Nat <- IO.now()
    +out : List<&2, Out> = brute.batch(fork.depth(threads), n, xs)
    t1 : Nat <- IO.now()
    IO.print_err("brute: " ++ U32.show(U32.from_nat(Nat.sub(t1, t0))) ++ " ms on " ++ U32.show(threads) ++ " threads")
    brute.print(out)

def args.tail(xs: List<String>) -> List<String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{_, t}:
      t

def main.go(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{SCon{Chr{45}, SCon{Chr{45}, SCon{Chr{98}, _}}}, t}:
      do IO<Unit>:
        deals : List<&2, String> <- args.read(t)
        brute.run(deals)
    case _:
      do IO<Unit>:
        deals : List<&2, String> <- args.read(xs)
        show.all(deals)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    main.go(args.tail(args))
