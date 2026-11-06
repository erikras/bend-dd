# hand.bend: deal a random bridge hand and print it.
#
#   bend hand.bend [deal-number]
#
# The deal number seeds the dealer, so the same number always gives the same
# deal. See src/cards.bend for the seats, the suits and the card encoding.

import Base
import ./src/cards.bend as C
import ./src/deal.bend as D
import ./src/pbn.bend as P
import ./src/show.bend as V

# ---------------------------------------------------------------------------
# Command line

def seed.read(m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}:
      1
    case Some{v}:
      v

def seed.arg(args: List<String>) -> U32:
  match args:
    case Nil{}:
      1
    case Con{a, rest}:
      seed.read(U32.read(a))

# The deal number: the first argument, or 1.
def seed(args: List<String>) -> U32:
  match args:
    case Nil{}:
      1
    case Con{prog, rest}:
      seed.arg(rest)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    +n : U32 = seed(args)
    +deal : C.Deal = D.random(n)
    IO.print("Deal " ++ U32.show(n))
    IO.print("")
    IO.print(V.diagram(deal))
    IO.print("")
    IO.print(P.print(deal))
