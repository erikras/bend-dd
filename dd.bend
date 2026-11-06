# dd.bend: the double dummy solver's command line.
#
#   dd [deal or file]...
#
# Each argument is either one PBN deal, quoted so that it stays one argument,
# or a file with one deal per line. Blank lines and lines starting with # are
# skipped. Each deal prints one line: the 20 entries of its double dummy table,
# strain then declarer as in DDS's TABLE lines, then the number of positions
# visited. A summary goes to stderr. There is no transposition table yet, so this
# is for endings, not full deals.
#
#   dd --brute [deal or file]...
#
# The same, by plain minimax: the oracle, for endings of up to about 5 cards.
#
#   dd --print [deal or file]...
#
# Prints each deal back in canonical form, starting from North.

import Base
import ./src/cards.bend as C
import ./src/pbn.bend as P
import ./src/brute.bend as B
import ./src/search.bend as Z

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
# Solving

# The output of one deal: its line, whether it is a good one, and its nodes.
type Out is Data:
  Out{good: Bool, line: String, nodes: Nat}

def ints.show(xs: List<&2, U32>, tail: String) -> String:
  match xs:
    case Nil{}:
      tail
    case Con{h, t}:
      U32.show(h) ++ " " ++ ints.show(t, tail)

def table.show(t: B.Table) -> Out:
  match t:
    case B.Table{ts, +n}:
      Out{True{}, ints.show(ts, Nat.show(n)), n}

# ~f is the solver, so that each one compiles to its own copy of the batch.
def one.even(~f: @+deal:C.Deal -> B.Table, even: Bool, text: String, +deal: C.Deal) -> Out:
  match even:
    case True{}:
      table.show(f(deal))
    case False{}:
      Out{False{}, "dd: hands differ in length: " ++ text, 0n}

def one.parsed(~f: @+deal:C.Deal -> B.Table, +text: String, d: Maybe<&2, C.Deal>) -> Out:
  match d:
    case None{}:
      Out{False{}, "dd: not a PBN deal: " ++ text, 0n}
    case Some{+deal}:
      one.even(~f, B.deal.even(deal), text, deal)

def one(~f: @+deal:C.Deal -> B.Table, +text: String) -> Out:
  one.parsed(~f, text, P.parse(text))

def seq(~f: @+deal:C.Deal -> B.Table, xs: List<&2, String>) -> List<&2, Out>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      one(~f, h) <> seq(~f, t)

# Solves a list of n deals over a fork tree of the given depth.
def batch(~f: @+deal:C.Deal -> B.Table, +depth: Nat, +n: Nat, +xs: List<&2, String>) -> List<&2, Out>:
  match depth:
    case 0n:
      seq(~f, xs)
    case 1n+p:
      +half = Nat.div(n, 2n)
      a b = batch(~f, p, half, List.take(&2, String, xs, half)) batch(~f, p, Nat.sub(n, half), List.drop(&2, String, xs, half))
      List.append(&2, Out, a, b)

# Prints every line, stopping at the first failure.
def out.print.go(good: Bool, line: String) -> IO(Unit):
  match good:
    case True{}:
      IO.print(line)
    case False{}:
      IO.die(Unit, 1, line)

def out.print(xs: List<&2, Out>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{Out{good, line, _}, t}:
      do IO<Unit>:
        out.print.go(good, line)
        out.print(t)

# How deep to fork: 64 leaves per thread or so. Tasks never move between threads,
# and endings differ a lot in size, so many small leaves balance better than one
# per thread. On 4-card endings this took 5.8 s against 7.4 s.
def fork.depth(+threads: U32) -> Nat:
  Nat.add(6n, U32.log2((threads * 2 - 1 : U32)))

# Runs a whole list of deals. The results are forced before the clock is read
# again, since compiled code is strict, so the time covers the solving.
def run(~f: @+deal:C.Deal -> B.Table, +name: String, +xs: List<&2, String>) -> IO(Unit):
  +n = List.length(&2, String, xs)
  do IO<Unit>:
    +threads : U32 <- IO.thread_count()
    t0 : Nat <- IO.now()
    +out : List<&2, Out> = batch(~f, fork.depth(threads), n, xs)
    t1 : Nat <- IO.now()
    IO.print_err(name ++ ": " ++ U32.show(U32.from_nat(Nat.sub(t1, t0))) ++ " ms on " ++ U32.show(threads) ++ " threads")
    out.print(out)

def args.tail(xs: List<String>) -> List<String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{_, t}:
      t

def brute.table(+deal: C.Deal) -> B.Table:
  B.table(deal)

def search.table(+deal: C.Deal) -> B.Table:
  Z.table(deal)

def main.go(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{SCon{Chr{45}, SCon{Chr{45}, SCon{Chr{98}, _}}}, t}:
      do IO<Unit>:
        deals : List<&2, String> <- args.read(t)
        run(~brute.table, "brute", deals)
    case Con{SCon{Chr{45}, SCon{Chr{45}, SCon{Chr{112}, _}}}, t}:
      do IO<Unit>:
        deals : List<&2, String> <- args.read(t)
        show.all(deals)
    case _:
      do IO<Unit>:
        deals : List<&2, String> <- args.read(xs)
        run(~search.table, "search", deals)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    main.go(args.tail(args))
