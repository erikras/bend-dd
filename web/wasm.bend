# wasm.bend: a main around api.bend, for timing Bend's C built to WebAssembly.
#
#   wasm <file of PBN deals>
#   wasm --deals <deal>...
#
# The second form takes the deals as arguments, which needs no file IO.
#
# The page runs one call of api.bend per run of main, and prints its result:
#
#   wasm --strain <t> <deal>               api.strain
#   wasm --random <seed>                   api.random
#   wasm --cards <deal> <strain> <decl> <played>    api.cards
#   wasm --sim <setup> <seed> <first> <count>       api.sim
# Prints each deal's table as api.table gives it, 20 numbers, one deal at a time,
# with the five strains forked so that they run on threads of their own when the
# build has them. Then the time on stderr.

import Base
import ./api.bend as A

def fork.two(+pbn: String, +a: U32, +b: U32) -> String:
  x y = A.strain(pbn, a) A.strain(pbn, b)
  x ++ " " ++ y

def fork.three(+pbn: String) -> String:
  x y = A.strain(pbn, 2) fork.two(pbn, 3, 4)
  x ++ " " ++ y

def table(+pbn: String) -> String:
  x y = fork.two(pbn, 0, 1) fork.three(pbn)
  x ++ " " ++ y

def one(blank: Bool, +s: String) -> IO(Unit):
  match blank:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.print(table(s))

def all(xs: List<&2, String>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{h, t}:
      +s = String.trim(h)
      do IO<Unit>:
        one(String.is_empty(s), s)
        all(t)

def read.text(p: File & Result<&1, &1, U32 & String, String>) -> IO(List<&2, String>):
  match p:
    case (f, r):
      do IO<List<&2, String>>:
        File.close(f)
        s : String <- IO.pass(String, r)
        return String.lines(s)

def read.size(p: File & Result<&1, &1, U32 & String, U32>) -> IO(List<&2, String>):
  match p:
    case (f, r):
      do IO<List<&2, String>>:
        n : U32 <- IO.pass(U32, r)
        q : File & Result<&1, &1, U32 & String, String> <- File.read(f, n)
        read.text(q)

def read(path: String) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    f : File <- IO.try(File, File.open(path, "r"))
    p : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
    read.size(p)

def strings(xs: List<String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      h <> strings(t)

def timed(deals: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    +threads : U32 <- IO.thread_count()
    t0 : Nat <- IO.now()
    all(deals)
    t1 : Nat <- IO.now()
    IO.print_err("wasm: " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms on " ++ U32.show(threads) ++ " threads")

def num(r: Maybe<&2, U32>) -> U32:
  match r:
    case None{}:
      0
    case Some{x}:
      x

def go(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{_, Con{SCon{Chr{45}, SCon{Chr{45}, SCon{Chr{115}, SCon{Chr{116}, _}}}}, Con{t, Con{pbn, _}}}}:
      IO.print(A.strain(pbn, num(U32.read(t))))
    case Con{_, Con{SCon{Chr{45}, SCon{Chr{45}, SCon{Chr{114}, _}}}, Con{seed, _}}}:
      IO.print(A.random(num(U32.read(seed))))
    case Con{_, Con{SCon{Chr{45}, SCon{Chr{45}, SCon{Chr{99}, _}}}, Con{pbn, Con{t, Con{decl, Con{played, _}}}}}}:
      IO.print(A.cards(pbn, t, decl, played))
    case Con{_, Con{SCon{Chr{45}, SCon{Chr{45}, SCon{Chr{115}, SCon{Chr{105}, _}}}}, Con{setup, Con{seed, Con{first, Con{count, _}}}}}}:
      IO.print(A.sim(setup, num(U32.read(seed)), num(U32.read(first)), num(U32.read(count))))
    case Con{_, Con{SCon{Chr{45}, SCon{Chr{45}, SCon{Chr{100}, _}}}, t}}:
      timed(strings(t))
    case Con{_, Con{path, _}}:
      do IO<Unit>:
        deals : List<&2, String> <- read(path)
        +threads : U32 <- IO.thread_count()
        t0 : Nat <- IO.now()
        all(deals)
        t1 : Nat <- IO.now()
        IO.print_err("wasm: " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms on " ++ U32.show(threads) ++ " threads")
    case _:
      IO.die(Unit, 1, "usage: wasm <file of PBN deals>")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
