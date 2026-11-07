# every.bend: every ending of a given size, for checks that aren't samples.
#
# Goes through every position with k cards in each hand: every way to split them into
# four suits, longest suit first since the suits only differ by name, and every way to
# give them out. Only who holds what matters to the game, so each suit uses its top
# cards. For each, in all 5 strains with all 4 leaders, it checks that the tricks the
# search counts as sure never exceed the true ones, and that the search gives the same
# table as brute force.

import Base
import ./cards.bend as C
import ./rules.bend as R
import ./brute.bend as B
import ./search.bend as Z

# How it went: deals checked and how many were wrong, with the suit lengths and owners
# of the first that was, as a key to print it by.
type Sum is Data:
  Sum{deals: Nat, bad: Nat, lens: U32, owners: U32}

def ints.eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, s} Con{y, t}:
      Bool.and(U32.is_eq(x, y), ints.eq(s, t))
    case _ _:
      False{}

def sure.ok(ts: List<&2, U32>, ss: List<&2, U32>, +left: U32) -> Bool:
  match ts ss:
    case Con{+v, t} Con{+q, Con{+l, r}}:
      U32.is_le(q, (left - v : U32)) && U32.is_le(l, v) && sure.ok(t, r, left)
    case _ _:
      True{}

def table.tricks(t: B.Table) -> List<&2, U32>:
  match t:
    case B.Table{ts, _}:
      ts

def deal.of(+n01: U32, +n23: U32, +e01: U32, +e23: U32, +s01: U32, +s23: U32, +w01: U32, +w23: U32) -> C.Deal:
  C.Deal{C.Hand{(n01 >> 16n : U32), (n01 .&. 65535 : U32), (n23 >> 16n : U32), (n23 .&. 65535 : U32)},
    C.Hand{(e01 >> 16n : U32), (e01 .&. 65535 : U32), (e23 >> 16n : U32), (e23 .&. 65535 : U32)},
    C.Hand{(s01 >> 16n : U32), (s01 .&. 65535 : U32), (s23 >> 16n : U32), (s23 .&. 65535 : U32)},
    C.Hand{(w01 >> 16n : U32), (w01 .&. 65535 : U32), (w23 >> 16n : U32), (w23 .&. 65535 : U32)}}

def check.done(good: Bool, +lens: U32, +owners: U32) -> Sum:
  match good:
    case True{}:
      Sum{1n, 0n, 0, 0}
    case False{}:
      Sum{1n, 1n, lens, owners}

def check.deal(+deal: C.Deal, +k: U32, +lens: U32, +owners: U32) -> Sum:
  +truth = table.tricks(B.table(deal))
  check.done(sure.ok(truth, table.tricks(Z.bounds(deal)), k) && ints.eq(truth, table.tricks(Z.table(deal))), lens, owners)

def add(a: Sum, b: Sum) -> Sum:
  match a b:
    case Sum{+x, +p, +l, +o} Sum{+y, +q, +m, +v}:
      Sum{Nat.add(x, y), Nat.add(p, q), R.sel(Nat.is_eq(p, 0n), m, l), R.sel(Nat.is_eq(p, 0n), v, o)}

def zero() -> Sum:
  Sum{0n, 0n, 0, 0}

# The cards dealt so far.
type Hands is Data:
  Hands{n01: U32, n23: U32, e01: U32, e23: U32, s01: U32, s23: U32, w01: U32, w23: U32}

def nib(+x: U32, +i: U32) -> U32:
  ((x >> U32.to_nat((i * 4 : U32))) .&. 15 : U32)

# Which suit the next card is in, and how many of its suit went before it, as
# suit << 4 | used: on to the next suit with cards when this one is done.
def next.card(n: Nat, stay: Bool, +lens: U32, +s: U32, +used: U32) -> U32:
  match n stay:
    case 0n _:
      ((s << 4n) .|. used : U32)
    case 1n+p True{}:
      ((s << 4n) .|. used : U32)
    case 1n+p False{}:
      next.card(p, U32.is_ne(nib(lens, (s + 1 : U32)), 0), lens, (s + 1 : U32), 0)

def next.at(+lens: U32, +s: U32, +used: U32) -> U32:
  next.card(4n, U32.is_lt(used, nib(lens, s)), lens, s, used)

def give(+h: U32, +s: U32, +used: U32, hs: Hands) -> Hands:
  match hs:
    case Hands{+a, +b2, +c, +d, +e, +f, +g, +i}:
      +b = (1 << U32.to_nat((12 - used : U32)) : U32)
      +w = R.sel(U32.is_zero((s .&. 1 : U32)), (b << 16n : U32), b)
      +x = R.sel(U32.is_lt(s, 2), w, 0)
      +y = R.sel(U32.is_lt(s, 2), 0, w)
      Hands{R.sel(U32.is_eq(h, 0), (a .|. x : U32), a), R.sel(U32.is_eq(h, 0), (b2 .|. y : U32), b2),
        R.sel(U32.is_eq(h, 1), (c .|. x : U32), c), R.sel(U32.is_eq(h, 1), (d .|. y : U32), d),
        R.sel(U32.is_eq(h, 2), (e .|. x : U32), e), R.sel(U32.is_eq(h, 2), (f .|. y : U32), f),
        R.sel(U32.is_eq(h, 3), (g .|. x : U32), g), R.sel(U32.is_eq(h, 3), (i .|. y : U32), i)}

def leaf(+k: U32, +lens: U32, +owners: U32, hs: Hands) -> Sum:
  match hs:
    case Hands{a, b, c, d, e, f, g, i}:
      check.deal(deal.of(a, b, c, d, e, f, g, i), k, lens, owners)

# Gives out the n cards left, in turn. room packs what each hand can still take, and
# ok says the hand that took the last card had room for it. The owners word only
# keeps the last 16 cards, which is enough to find a position when a size can be run.
def walk(+n: Nat, ok: Bool, +k: U32, +lens: U32, +owners: U32, +s: U32, +used: U32, +room: U32, +hs: Hands) -> Sum:
  match n ok:
    case _ False{}:
      zero()
    case 0n True{}:
      leaf(k, lens, owners, hs)
    case 1n+p True{}:
      +at = next.at(lens, s, used)
      +ss = (at >> 4n : U32)
      +uu = (at .&. 15 : U32)
      +o = (owners << 2n : U32)
      add(add(walk(p, U32.is_ne(nib(room, 0), 0), k, lens, o, ss, (uu + 1 : U32), (room - 1 : U32), give(0, ss, uu, hs)),
              walk(p, U32.is_ne(nib(room, 1), 0), k, lens, (o .|. 1 : U32), ss, (uu + 1 : U32), (room - 16 : U32), give(1, ss, uu, hs))),
          add(walk(p, U32.is_ne(nib(room, 2), 0), k, lens, (o .|. 2 : U32), ss, (uu + 1 : U32), (room - 256 : U32), give(2, ss, uu, hs)),
              walk(p, U32.is_ne(nib(room, 3), 0), k, lens, (o .|. 3 : U32), ss, (uu + 1 : U32), (room - 4096 : U32), give(3, ss, uu, hs))))

def walk.par(+f: Nat, +n: Nat, ok: Bool, +k: U32, +lens: U32, +owners: U32, +s: U32, +used: U32, +room: U32, +hs: Hands) -> Sum:
  match f n ok:
    case _ _ False{}:
      zero()
    case 0n _ True{}:
      walk(n, True{}, k, lens, owners, s, used, room, hs)
    case 1n+g 0n True{}:
      leaf(k, lens, owners, hs)
    case 1n+g 1n+p True{}:
      +at = next.at(lens, s, used)
      +ss = (at >> 4n : U32)
      +uu = (at .&. 15 : U32)
      +o = (owners << 2n : U32)
      a b = walk.par(g, p, U32.is_ne(nib(room, 0), 0), k, lens, o, ss, (uu + 1 : U32), (room - 1 : U32), give(0, ss, uu, hs)) walk.par(g, p, U32.is_ne(nib(room, 1), 0), k, lens, (o .|. 1 : U32), ss, (uu + 1 : U32), (room - 16 : U32), give(1, ss, uu, hs))
      c d = walk.par(g, p, U32.is_ne(nib(room, 2), 0), k, lens, (o .|. 2 : U32), ss, (uu + 1 : U32), (room - 256 : U32), give(2, ss, uu, hs)) walk.par(g, p, U32.is_ne(nib(room, 3), 0), k, lens, (o .|. 3 : U32), ss, (uu + 1 : U32), (room - 4096 : U32), give(3, ss, uu, hs))
      add(add(a, b), add(c, d))

def hands.none() -> Hands:
  Hands{0, 0, 0, 0, 0, 0, 0, 0}

def room.of(+k: U32) -> U32:
  (k .|. (k << 4n) .|. (k << 8n) .|. (k << 12n) : U32)

# All the deals with these suit lengths, packed 4 bits each, forking f cards deep.
def of.lens(+f: Nat, +k: U32, +lens: U32) -> Sum:
  walk.par(f, U32.to_nat((k * 4 : U32)), True{}, k, lens, 0, 0, 0, room.of(k), hands.none())

def lens.keep(ok: Bool, +x: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match ok:
    case True{}:
      x <> acc
    case False{}:
      acc

# The ways to split rem cards among i more suits, each at most v, longer suits first,
# as packed lengths added to acc. A suit either takes v, if it can, or less than v.
def parts(+i: Nat, +v: Nat, ok: Bool, +rem: U32, +at: U32, +sofar: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match i v ok:
    case _ _ False{}:
      acc
    case 0n _ True{}:
      lens.keep(U32.is_zero(rem), sofar, acc)
    case 1n+q 0n True{}:
      parts(q, 0n, True{}, rem, (at + 1 : U32), sofar, acc)
    case 1n+q 1n+w True{}:
      +x = U32.from_nat(1n+w)
      parts(1n+q, w, True{}, rem, at, sofar,
        parts(q, 1n+w, U32.is_le(x, rem), (rem - x : U32), (at + 1 : U32), (sofar .|. (x << U32.to_nat((at * 4 : U32))) : U32), acc))

def lens.all(+k: U32) -> List<&2, U32>:
  parts(4n, 13n, True{}, (k * 4 : U32), 0, 0, Nil{})

def all.go(xs: List<&2, U32>, +k: U32) -> Sum:
  match xs:
    case Nil{}:
      zero()
    case Con{+h, t}:
      add(of.lens(0n, k, h), all.go(t, k))

# Every deal of k cards in each hand, in turn.
def all(+k: U32) -> Sum:
  all.go(lens.all(k), k)

def all.good(s: Sum) -> Bool:
  match s:
    case Sum{_, b, _, _}:
      Nat.is_eq(b, 0n)
