# show.bend: what people read, the hand diagram and the double dummy grid.

import Base
import ./cards.bend as C
import ./pbn.bend as P
import ./brute.bend as B
import ./search.bend as Z

# ---------------------------------------------------------------------------
# Strings

# Drops the first n characters of s.
def str.drop(n: Nat, s: String) -> String:
  match n:
    case 0n:
      s
    case 1n+p:
      match s:
        case SNil{}:
          SNil{}
        case SCon{h, t}:
          str.drop(p, t)

# The first character of s, as a String.
def str.first(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{h, t}:
      SCon{h, SNil{}}

# The i-th character of s, as a String.
def str.at(i: U32, s: String) -> String:
  str.first(str.drop(U32.to_nat(i), s))

# Pads s with spaces on the right to w characters, if it is shorter.
def str.pad(+s: String, +w: U32) -> String:
  +len = U32.from_nat(String.length(s))
  +gap = (U32.max(w, len) - len : U32)
  s ++ String.repeat(" ", U32.to_nat(gap))

# ---------------------------------------------------------------------------
# Printing

# Some terminal fonts draw U+2665 and U+2666 hollow, so the heart is U+2764
# followed by U+FE0E (an invisible text-style selector) and the diamond is
# U+25C6. The selector counts as a character for str.pad but takes up no
# column on screen.
def suit.selector(heart: Bool) -> String:
  match heart:
    case True{}:
      "︎"
    case False{}:
      ""

# The symbol of a suit.
def suit.symbol(+s: U32) -> String:
  str.at(s, "♠❤◆♣") ++ suit.selector(U32.is_eq(s, 1))

def dash(void: Bool, h: String) -> String:
  match void:
    case True{}:
      "-"
    case False{}:
      h

# One line of a hand diagram, e.g. "♠ AQT4", with "-" for a void.
def line(+deal: C.Deal, +seat: U32, +suit: U32) -> String:
  +h = P.suit.print(C.hand.suit(U32.to_nat(suit), C.deal.hand(U32.to_nat(seat), deal)))
  suit.symbol(suit) ++ " " ++ dash(String.is_empty(h), h)

# The classic four-hand diagram: North on top, West and East in the
# middle, South at the bottom.
def diagram(+deal: C.Deal) -> String:
  +sp : String = "            "
  String.join([
    sp ++ "North",
    sp ++ line(deal, 0, 0),
    sp ++ line(deal, 0, 1),
    sp ++ line(deal, 0, 2),
    sp ++ line(deal, 0, 3),
    str.pad("West", 24) ++ "East",
    str.pad(line(deal, 3, 0), 24) ++ line(deal, 1, 0),
    str.pad(line(deal, 3, 1), 25) ++ line(deal, 1, 1),
    str.pad(line(deal, 3, 2), 24) ++ line(deal, 1, 2),
    str.pad(line(deal, 3, 3), 24) ++ line(deal, 1, 3),
    sp ++ "South",
    sp ++ line(deal, 2, 0),
    sp ++ line(deal, 2, 1),
    sp ++ line(deal, 2, 2),
    sp ++ line(deal, 2, 3)
  ], "\n")

# ---------------------------------------------------------------------------
# The double dummy grid

def strain.name(nt: Bool, +s: U32) -> String:
  match nt:
    case True{}:
      "NT"
    case False{}:
      suit.symbol(s)

# A name in a column, allowing for the heart's invisible selector.
def strain.pad(+s: U32, +w: U32) -> String:
  str.pad(strain.name(U32.is_eq(s, 4), s), (w + Bool.to_u32(U32.is_eq(s, 1)) : U32))

def grid.rows(k: Nat, +s: U32, xs: List<&2, U32>) -> String:
  match k xs:
    case 1n+p Con{a, Con{b, Con{c, Con{d, t}}}}:
      strain.pad(s, 4) ++ str.pad(U32.show(a), 4) ++ str.pad(U32.show(b), 4) ++ str.pad(U32.show(c), 4) ++ U32.show(d) ++ "\n" ++ grid.rows(p, (s + 1 : U32), t)
    case _ _:
      ""

# The tricks declarer takes, from a table's 20 entries: strains down, declarers
# across.
def grid(xs: List<&2, U32>) -> String:
  "    N   E   S   W\n" ++ grid.rows(5n, 0, xs)

def table.grid(t: B.Table) -> String:
  match t:
    case B.Table{ts, _}:
      grid(ts)

# ---------------------------------------------------------------------------
# Statistics

# The value at a position of a list.
def at(n: Nat, xs: List<&2, U32>) -> U32:
  match n xs:
    case 0n Con{h, _}:
      h
    case 1n+p Con{_, t}:
      at(p, t)
    case _ _:
      0

def field(+e: U32, +f: U32, +xs: List<&2, U32>) -> Nat:
  +i = U32.to_nat((e * 32 + f : U32))
  Nat.add(Nat.mul(Nat.mul(U32.to_nat(at(1n+i, xs)), 65536n), 65536n), U32.to_nat(at(i, xs)))

# The sum of a counter over the entries from e to 19.
def field.sum(n: Nat, +e: U32, +f: U32, +xs: List<&2, U32>) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      Nat.add(field(e, f, xs), field.sum(p, (e + 1 : U32), f, xs))

def total(+f: U32, +xs: List<&2, U32>) -> Nat:
  field.sum(20n, 0, f, xs)

# The targets of a log, in the order they were tried.
def targets.go(k: Nat, +log: U32, +more: U32) -> String:
  match k:
    case 0n:
      ""
    case 1n+p:
      U32.show((log .&. 15 : U32)) ++ " " ++ targets.go(p, (log >> 4n : U32), more)

def targets(+n: U32, +a: U32, +b: U32) -> String:
  targets.go(U32.to_nat(U32.min(n, 8)), a, 0) ++ targets.go(U32.to_nat((U32.max(n, 8) - 8 : U32)), b, 0)

def cell(+n: Nat, +w: U32) -> String:
  str.pad(Nat.show(n), w)

def seat.name(+s: U32) -> String:
  str.at(s, "NESW")

def rows.head() -> String:
  str.pad("", 3) ++ str.pad("decl", 5) ++ str.pad("lead", 5) ++ str.pad("tricks", 7) ++ str.pad("nodes", 12) ++ str.pad("searches", 9) ++ str.pad("targets", 18) ++ str.pad("target", 11) ++ str.pad("quick", 11) ++ str.pad("later", 11) ++ str.pad("after", 11) ++ str.pad("moves", 13) ++ "kept"

def row.counts(+e: U32, +xs: List<&2, U32>) -> String:
  cell(field(e, Z.stat.cuts(), xs), 11) ++ cell(field(e, (Z.stat.cuts() + 2 : U32), xs), 11) ++ cell(field(e, (Z.stat.cuts() + 4 : U32), xs), 11) ++ cell(field(e, (Z.stat.cuts() + 6 : U32), xs), 11) ++ cell(field(e, Z.stat.moves(), xs), 13) ++ Nat.show(field(e, Z.stat.kept(), xs))

# One line for table entry e.
def row(+e: U32, +tricks: U32, +xs: List<&2, U32>) -> String:
  +decl = (e .&. 3 : U32)
  +n = U32.from_nat(field(e, Z.stat.searches(), xs))
  +slot = U32.to_nat((e * 32 + Z.stat.log() : U32))
  strain.pad((e >> 2n : U32), 3) ++ str.pad(seat.name(decl), 5) ++ str.pad(seat.name(((decl + 1) .&. 3 : U32)), 5) ++ str.pad(U32.show(tricks), 7) ++ cell(field(e, Z.stat.nodes(), xs), 12) ++ str.pad(U32.show(n), 9) ++ str.pad(targets(n, at(slot, xs), at(1n+slot, xs)), 18) ++ row.counts(e, xs)

def rows(ts: List<&2, U32>, +e: U32, +xs: List<&2, U32>) -> String:
  match ts:
    case Nil{}:
      ""
    case Con{+h, t}:
      row(e, h, xs) ++ "\n" ++ rows(t, (e + 1 : U32), xs)

def totals(+xs: List<&2, U32>) -> String:
  str.pad("all", 20) ++ cell(total(Z.stat.nodes(), xs), 12) ++ cell(total(Z.stat.searches(), xs), 27) ++ cell(total(Z.stat.cuts(), xs), 11) ++ cell(total((Z.stat.cuts() + 2 : U32), xs), 11) ++ cell(total((Z.stat.cuts() + 4 : U32), xs), 11) ++ cell(total((Z.stat.cuts() + 6 : U32), xs), 11) ++ cell(total(Z.stat.moves(), xs), 13) ++ Nat.show(total(Z.stat.kept(), xs))

# Everything counted for a deal: the grid, then a line per strain and declarer.
def report(r: Z.Report) -> String:
  match r:
    case Z.Report{+ts, _, +xs}:
      grid(ts) ++ "\nTargets are North-South's tricks. The cut columns count positions settled by\ntarget too low or high, quick tricks, later tricks, and the check after the lead.\nMoves are the legal moves, and kept is what is left of them after equivalence.\n\n" ++ rows.head() ++ "\n" ++ rows(ts, 0, xs) ++ totals(xs)
