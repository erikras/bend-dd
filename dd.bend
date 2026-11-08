# dd.bend: the double dummy solver's command line.
#
#   dd [deal or file]...
#
# Each argument is either one PBN deal, quoted so that it stays one argument,
# or a file with one deal per line. Blank lines and lines starting with # are
# skipped. Each deal prints one line: the 20 entries of its double dummy table,
# strain then declarer as in DDS's TABLE lines, then the number of positions
# visited. A summary goes to stderr.
#
#   dd --grid [deal or file]...
#
# The same, for people: the deal and a grid of tricks, by strain and declarer.
#
#   dd -v [deal or file]...         (or --verbose)
#
# The hand diagram, the deal, the grid, and for each strain and declarer the nodes,
# the searches and targets, the cuts by kind, and the moves before and after
# equivalence, with totals and the speed.
#
#   dd --demo [seed] [cards]
#
# The same for a random ending from a seed: 1 and 5 cards in each hand by default.
#
#   dd --random [seed]
#
# Deals a random full deal and solves it: the hand diagram, the deal in PBN, and
# the double dummy table with declarers down and strains across. The seed picks
# the deal, so the same seed always gives the same one; without one it picks a
# seed at random and prints it.
#
#   dd --brute [deal or file]...
#
# The same, by plain minimax: the oracle, for endings of up to about 5 cards.
#
#   dd --sure [deal or file]...
#
# For each table entry, with the seat on declarer's left on lead, prints the tricks
# the search is sure of at the start: for that seat's side, then declarer's. This is
# for checking them against the true results.
#
#   dd --print [deal or file]...
#
# Prints each deal back in canonical form, starting from North.

import Base
import ./src/cards.bend as C
import ./src/pbn.bend as P
import ./src/brute.bend as B
import ./src/search.bend as Z
import ./src/show.bend as V
import ./src/deal.bend as D

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

# One strain's part of a line: its tricks without the nodes.
def part.show(t: B.Table) -> Out:
  match t:
    case B.Table{ts, +n}:
      Out{True{}, ints.show(ts, ""), n}

def out.end.go(good: Bool, a: String, +n: Nat) -> Out:
  match good:
    case True{}:
      Out{True{}, a ++ Nat.show(n), n}
    case False{}:
      Out{False{}, a, n}

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
# per thread. On 4-card endings this took 5.8 s against 7.4 s. Never deeper than one
# deal per leaf: the scheduler only hands out tasks until it has enough of them, so
# empty leaves would keep the forks over strains inside a deal on one thread.
def fork.depth(+threads: U32, +n: Nat) -> Nat:
  +deals = U32.log2((U32.from_nat(n) * 2 - 1 : U32))
  +wide = Nat.add(6n, U32.log2((threads * 2 - 1 : U32)))
  U32.to_nat(U32.min(U32.from_nat(deals), U32.from_nat(wide)))

# Runs a whole list of deals. The results are forced before the clock is read
# again, since compiled code is strict, so the time covers the solving.
def run(~f: @+deal:C.Deal -> B.Table, +name: String, +xs: List<&2, String>) -> IO(Unit):
  +n = List.length(&2, String, xs)
  do IO<Unit>:
    +threads : U32 <- IO.thread_count()
    t0 : Nat <- IO.now()
    +out : List<&2, Out> = batch(~f, fork.depth(threads, n), n, xs)
    t1 : Nat <- IO.now()
    IO.print_err(name ++ ": " ++ U32.show(U32.from_nat(Nat.sub(t1, t0))) ++ " ms on " ++ U32.show(threads) ++ " threads")
    out.print(out)

# ---------------------------------------------------------------------------
# Solving by strain

# The search forks over each strain of each deal rather than each deal: there are five
# times as many leaves to balance, and one deal still fills 5 threads. A fork inside
# a leaf would do neither, since the scheduler only hands out tasks until it has
# enough of them.
type Item is Data:
  Item{text: String, t: U32}

def items.of(xs: List<&2, String>) -> List<&2, Item>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Item{h, 0} <> (Item{h, 1} <> (Item{h, 2} <> (Item{h, 3} <> (Item{h, 4} <> items.of(t)))))

def part.even(even: Bool, +text: String, +t: U32, +deal: C.Deal) -> Out:
  match even:
    case True{}:
      part.show(Z.strain.table(t, deal))
    case False{}:
      Out{False{}, "dd: hands differ in length: " ++ text, 0n}

def part.parsed(+text: String, +t: U32, d: Maybe<&2, C.Deal>) -> Out:
  match d:
    case None{}:
      Out{False{}, "dd: not a PBN deal: " ++ text, 0n}
    case Some{+deal}:
      part.even(B.deal.even(deal), text, t, deal)

def part(i: Item) -> Out:
  match i:
    case Item{+text, +t}:
      part.parsed(text, t, P.parse(text))

def parts.seq(xs: List<&2, Item>) -> List<&2, Out>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      part(h) <> parts.seq(t)

def parts.batch(+depth: Nat, +n: Nat, +xs: List<&2, Item>) -> List<&2, Out>:
  match depth:
    case 0n:
      parts.seq(xs)
    case 1n+p:
      +half = Nat.div(n, 2n)
      a b = parts.batch(p, half, List.take(&2, Item, xs, half)) parts.batch(p, Nat.sub(n, half), List.drop(&2, Item, xs, half))
      List.append(&2, Out, a, b)

def out.join.go(g1: Bool, g2: Bool, a: String, b: String, +n: Nat, +k: Nat) -> Out:
  match g1 g2:
    case True{} True{}:
      Out{True{}, a ++ b, Nat.add(n, k)}
    case True{} False{}:
      Out{False{}, b, 0n}
    case False{} _:
      Out{False{}, a, 0n}

def out.join(x: Out, y: Out) -> Out:
  match x y:
    case Out{g1, a, +n} Out{g2, b, +k}:
      out.join.go(g1, g2, a, b, n, k)

def out.end(x: Out) -> Out:
  match x:
    case Out{+g, a, +n}:
      out.end.go(g, a, n)

# Each deal's five parts as its line: its tricks in order and then its nodes.
def parts.lines(xs: List<&2, Out>) -> List<&2, Out>:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, Con{e, t}}}}}:
      out.end(out.join(a, out.join(b, out.join(c, out.join(d, e))))) <> parts.lines(t)
    case _:
      Nil{}

def run.parts(+xs: List<&2, String>) -> IO(Unit):
  +items = items.of(xs)
  +n = List.length(&2, Item, items)
  do IO<Unit>:
    +threads : U32 <- IO.thread_count()
    t0 : Nat <- IO.now()
    +out : List<&2, Out> = parts.batch(fork.depth(threads, n), n, items)
    t1 : Nat <- IO.now()
    IO.print_err("search: " ++ U32.show(U32.from_nat(Nat.sub(t1, t0))) ++ " ms on " ++ U32.show(threads) ++ " threads")
    out.print(parts.lines(out))

# ---------------------------------------------------------------------------
# For people

# The time and speed of the plain search.
def speed.go(fast: Bool, +ms: Nat, +nodes: Nat) -> String:
  match fast:
    case True{}:
      "under 1 ms"
    case False{}:
      Nat.show(ms) ++ " ms, " ++ Nat.show(Nat.div(Nat.mul(1000n, nodes), ms)) ++ " nodes/s"

def speed(+ms: Nat, +nodes: Nat) -> String:
  speed.go(Nat.is_eq(ms, 0n), ms, nodes)

def table.nodes(t: B.Table) -> Nat:
  match t:
    case B.Table{_, n}:
      n

# The diagram, the PBN line, the grid and every statistic for one deal. The timing
# is of a plain search, since counting takes longer.
def deal.verbose(+deal: C.Deal) -> IO(Unit):
  do IO<Unit>:
    IO.print(V.diagram(deal))
    IO.print("")
    IO.print(P.print(deal))
    IO.print("")
    t0 : Nat <- IO.now()
    +plain : B.Table = Z.table(deal)
    t1 : Nat <- IO.now()
    IO.print(V.report(Z.table.report(deal)))
    IO.print("")
    +n : Nat = table.nodes(plain)
    IO.print("Solved all 20 entries, " ++ Nat.show(n) ++ " nodes: " ++ speed(Nat.sub(t1, t0), n) ++ ", on one thread with counting off")

def deal.grid(+deal: C.Deal) -> IO(Unit):
  do IO<Unit>:
    IO.print(P.print(deal))
    IO.print("")
    IO.print(V.table.grid(Z.table(deal)))

# One deal from its text, through f, or a message if it can't be played.
def human.even(~f: @+deal:C.Deal -> IO(Unit), even: Bool, text: String, +deal: C.Deal) -> IO(Unit):
  match even:
    case True{}:
      f(deal)
    case False{}:
      IO.die(Unit, 1, "dd: hands differ in length: " ++ text)

def human.parsed(~f: @+deal:C.Deal -> IO(Unit), +text: String, d: Maybe<&2, C.Deal>) -> IO(Unit):
  match d:
    case None{}:
      IO.die(Unit, 1, "dd: not a PBN deal: " ++ text)
    case Some{+deal}:
      human.even(~f, B.deal.even(deal), text, deal)

def human.all(~f: @+deal:C.Deal -> IO(Unit), xs: List<&2, String>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+h, t}:
      do IO<Unit>:
        human.parsed(~f, h, P.parse(h))
        human.all(~f, t)

def demo.num(r: Maybe<&2, U32>, +fallback: U32) -> U32:
  match r:
    case None{}:
      fallback
    case Some{x}:
      x

def demo.go(ok: Bool, +seed: U32, +k: U32) -> IO(Unit):
  match ok:
    case True{}:
      do IO<Unit>:
        IO.print("Ending " ++ U32.show(seed) ++ ", " ++ U32.show(k) ++ " cards in each hand")
        IO.print("")
        deal.verbose(D.ending(seed, k))
    case False{}:
      IO.die(Unit, 1, "dd: --demo takes 1 to 13 cards in each hand")

def demo(+seed: U32, +k: U32) -> IO(Unit):
  demo.go(U32.is_ge(k, 1) && U32.is_le(k, 13), seed, k)

def demo.args(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{a, Con{b, _}}:
      demo(demo.num(U32.read(a), 1), demo.num(U32.read(b), 5))
    case Con{a, _}:
      demo(demo.num(U32.read(a), 1), 5)
    case _:
      demo(1, 5)

def args.tail(xs: List<String>) -> List<String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{_, t}:
      t

# ---------------------------------------------------------------------------
# A random deal

# The table of one deal, with each strain on a thread of its own.
def fork.two(+a: U32, +b: U32, +deal: C.Deal) -> B.Table:
  x y = Z.strain.table(a, deal) Z.strain.table(b, deal)
  Z.table.join(x, y)

def fork.three(+deal: C.Deal) -> B.Table:
  x y = Z.strain.table(2, deal) fork.two(3, 4, deal)
  Z.table.join(x, y)

def table.fork(+deal: C.Deal) -> B.Table:
  x y = fork.two(0, 1, deal) fork.three(deal)
  Z.table.join(x, y)

def random.show(+seed: U32) -> IO(Unit):
  +deal = D.random(seed)
  do IO<Unit>:
    IO.print("Deal " ++ U32.show(seed))
    IO.print("")
    IO.print(V.diagram(deal))
    IO.print("")
    IO.print(P.print(deal))
    IO.print("")
    t0 : Nat <- IO.now()
    +t : B.Table = table.fork(deal)
    t1 : Nat <- IO.now()
    IO.print("Double dummy tricks for each declarer:")
    IO.print("")
    IO.print(V.table.by.decl(t))
    IO.print("")
    IO.print("Solved in " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms. Run dd --random " ++ U32.show(seed) ++ " to see this deal again.")

def random.seed.go(r: Maybe<&2, U32>, +fallback: U32) -> U32:
  match r:
    case None{}:
      fallback
    case Some{x}:
      x

def random.args(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{a, _}:
      random.show(random.seed.go(U32.read(a), 1))
    case _:
      do IO<Unit>:
        r : U32 <- IO.try(U32, IO.random_u32())
        random.show((r % 1000000 + 1 : U32))

def brute.table(+deal: C.Deal) -> B.Table:
  B.table(deal)

def search.bounds(+deal: C.Deal) -> B.Table:
  Z.bounds(deal)

def main.go(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{SCon{Chr{45}, SCon{Chr{118}, _}}, t}:
      do IO<Unit>:
        deals : List<&2, String> <- args.read(t)
        human.all(~deal.verbose, deals)
    case Con{SCon{Chr{45}, SCon{Chr{45}, SCon{Chr{118}, _}}}, t}:
      do IO<Unit>:
        deals : List<&2, String> <- args.read(t)
        human.all(~deal.verbose, deals)
    case Con{SCon{Chr{45}, SCon{Chr{45}, SCon{Chr{103}, _}}}, t}:
      do IO<Unit>:
        deals : List<&2, String> <- args.read(t)
        human.all(~deal.grid, deals)
    case Con{SCon{Chr{45}, SCon{Chr{45}, SCon{Chr{100}, _}}}, t}:
      demo.args(t)
    case Con{SCon{Chr{45}, SCon{Chr{45}, SCon{Chr{114}, _}}}, t}:
      random.args(t)
    case Con{SCon{Chr{45}, SCon{Chr{45}, SCon{Chr{98}, _}}}, t}:
      do IO<Unit>:
        deals : List<&2, String> <- args.read(t)
        run(~brute.table, "brute", deals)
    case Con{SCon{Chr{45}, SCon{Chr{45}, SCon{Chr{115}, _}}}, t}:
      do IO<Unit>:
        deals : List<&2, String> <- args.read(t)
        run(~search.bounds, "sure", deals)
    case Con{SCon{Chr{45}, SCon{Chr{45}, SCon{Chr{112}, _}}}, t}:
      do IO<Unit>:
        deals : List<&2, String> <- args.read(t)
        show.all(deals)
    case _:
      do IO<Unit>:
        deals : List<&2, String> <- args.read(xs)
        run.parts(deals)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    main.go(args.tail(args))
