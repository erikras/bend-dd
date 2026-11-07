# brute.bend: plain minimax with no pruning, the oracle for small endings.
#
# North-South maximise their tricks and East-West minimise them. Every line of
# play is walked, so this is only usable for small endings. It stays in the repo
# as the reference the fast search is checked against.

import Base
import ./cards.bend as C
import ./rules.bend as R

# A value with the number of positions visited so far. Nat counts them: it is a
# machine word at run time, and it stops the program at 2^48 instead of wrapping.
type Res is Data:
  Res{value: U32, nodes: Nat}

def better(ns: Bool, +a: U32, +b: U32) -> U32:
  match ns:
    case True{}:
      U32.max(a, b)
    case False{}:
      U32.min(a, b)

# The value a node starts from before it has tried a move: whatever is worse
# for the side to play than any real result.
def seed(ns: Bool) -> U32:
  match ns:
    case True{}:
      0
    case False{}:
      13

# Tries the moves ms of a position with d cards left. best is the best value so
# far and r is the result of the move just tried: a call cannot be destructured
# in place, so a child's result rides into the next sibling as an argument.
#
# A child has one card fewer, and a sibling has one move fewer with the same d,
# so the recursion needs no separate fuel: d is exactly the plies left. The moves
# are never empty when d is above 0, as long as all hands were dealt the same
# number of cards.
def search(+d: Nat, ms: List<&2, U32>, +t: U32, +pos: R.Pos, +ns: Bool, +best: U32, r: Res) -> Res:
  match d ms r:
    case 0n _ Res{_, n}:
      Res{R.pos.won(pos), n}
    case 1n+p Nil{} Res{v, n}:
      Res{better(ns, best, v), n}
    case 1n+p Con{c, rest} Res{v, n}:
      +child = R.play(t, pos, c)
      +cns = R.pos.ns(child)
      search(1n+p, rest, t, pos, ns, better(ns, best, v),
        search(p, R.moves(child), t, child, cns, seed(cns), Res{seed(cns), 1n+n}))

# North-South's tricks from a position with d cards left.
def solve(+d: Nat, +t: U32, +pos: R.Pos, nodes: Nat) -> Res:
  +ns = R.pos.ns(pos)
  search(d, R.moves(pos), t, pos, ns, seed(ns), Res{seed(ns), nodes})

# The cards still to be played in a deal.
def deal.cards(d: C.Deal) -> U32:
  match d:
    case C.Deal{n, e, s, w}:
      (C.hand.count(n) + C.hand.count(e) + C.hand.count(s) + C.hand.count(w) : U32)

# Whether every hand holds the same number of cards, which play needs.
def deal.even(d: C.Deal) -> Bool:
  match d:
    case C.Deal{n, e, s, w}:
      +a = C.hand.count(n)
      U32.is_eq(a, C.hand.count(e)) && U32.is_eq(a, C.hand.count(s)) && U32.is_eq(a, C.hand.count(w))

# A double dummy table for one deal, in DDS's order: strain ♠ ♥ ♦ ♣ NT, then
# declarer N E S W. Each entry is the tricks declarer's side takes, with the seat
# on declarer's left on lead.
type Table is Data:
  Table{tricks: List<&2, U32>, nodes: Nat}

def table.entry(ns: Bool, +left: U32, v: U32) -> U32:
  match ns:
    case True{}:
      v
    case False{}:
      (left - v : U32)

def table.add(+decl: U32, +left: U32, r: Res, rest: Table) -> Table:
  match r rest:
    case Res{v, n} Table{ts, m}:
      Table{table.entry(U32.is_zero((decl .&. 1 : U32)), left, v) <> ts, Nat.add(n, m)}

# The entries for declarers 4 - k .. 3 of one strain, on top of rest.
def table.strain(+k: Nat, +d: Nat, +left: U32, +t: U32, +deal: C.Deal, rest: Table) -> Table:
  match k:
    case 0n:
      rest
    case 1n+p:
      +decl = (3 - U32.from_nat(p) : U32)
      +leader = ((decl + 1) .&. 3 : U32)
      table.add(decl, left, solve(d, t, R.pos.start(deal, leader), 0n),
        table.strain(p, d, left, t, deal, rest))

# The entries for strains 5 - k .. 4, on top of nothing.
def table.go(+k: Nat, +d: Nat, +left: U32, +deal: C.Deal) -> Table:
  match k:
    case 0n:
      Table{Nil{}, 0n}
    case 1n+p:
      table.strain(4n, d, left, (4 - U32.from_nat(p) : U32), deal,
        table.go(p, d, left, deal))

def table(+deal: C.Deal) -> Table:
  +cards = deal.cards(deal)
  table.go(5n, U32.to_nat(cards), (cards / 4 : U32), deal)
