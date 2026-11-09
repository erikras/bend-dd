# play.bend: the value of one card, from any point in a trick.
#
# The table in search.bend solves whole deals from the start of a trick. A simulation
# asks something else: with the cards played so far, how many tricks does each card
# the player to move could play now take? This runs the same zero-window search from
# the position as it stands, with the root's moves cut down to the one card, under a
# driver of its own whose bounds don't rely on counts made for the start of a trick.
#
# Below the root everything is the search as it always runs, so mid-trick nodes,
# cuts and the transposition table behave as they do inside a whole-deal search.

import Base
import ./cards.bend as C
import ./rules.bend as R
import ./search.bend as Z

# One search with card c forced at the root. d is the cards still in the hands, and
# l01 and l23 the cards that were in play at the start of the current trick: the
# hands now, plus the cards on the table.
def ask.go(+d: Nat, +t: U32, +pos: R.Pos, +c: U32, +l01: U32, +l23: U32, +target: U32, r: Z.Res) -> Z.Res:
  match r:
    case Z.Res{_, n, m, _, _, _, _}:
      +ns = R.pos.ns(pos)
      Z.search(~(+t => m => +p => +c => +a => +b => m), d, 0n, Z.MCon{c, Z.MNil{}}, ns, Z.peek(Bool.not(ns), n, m, (U32.from_nat(d) - 1 : U32)), Z.mem.none(), 0, 0, 0, 0, 0, t, target, l01, l23, pos)

def ask(stop: Bool, +d: Nat, +t: U32, +pos: R.Pos, +c: U32, +l01: U32, +l23: U32, +target: U32, n: Nat, m: Array<U32>) -> Z.Res:
  match stop:
    case True{}:
      Z.Res{False{}, n, m, 0, Z.MNil{}, 0, 0}
    case False{}:
      ask.go(d, t, pos, c, l01, l23, target, Z.Res{False{}, n, m, 0, Z.MNil{}, 0, 0})

# Moves the bounds until they meet, as Z.narrow does.
def narrow(fuel: Nat, done: Bool, r: Z.Res, +target: U32, +d: Nat, +t: U32, +pos: R.Pos, +c: U32, +l01: U32, +l23: U32, +lo: U32, +hi: U32) -> Z.Val:
  match fuel done r:
    case 0n _ Z.Res{_, n, m, _, _, _, _}:
      Z.Val{lo, n, m}
    case 1n+p True{} Z.Res{_, n, m, _, _, _, _}:
      Z.Val{lo, n, m}
    case 1n+p False{} Z.Res{+ok, n, m, _, _, _, _}:
      +lo2 = Z.driver.lo(ok, target, lo)
      +hi2 = Z.driver.hi(ok, target, hi)
      +stop = U32.is_ge(lo2, hi2)
      +next = Z.driver.next(ok, lo2, hi2)
      narrow(p, stop, ask(stop, d, t, pos, c, l01, l23, next, n, m), next, d, t, pos, c, l01, l23, lo2, hi2)

# The tricks left to play, counting the one in progress.
def tricks.left(+d: Nat) -> U32:
  ((U32.from_nat(d) + 3) / 4 : U32)

# North-South's tricks in the whole deal when the player to move plays card c, with
# d cards in the hands, from a guess at the answer. The answer is between the tricks
# North-South have already won and those plus every trick left.
def card(+d: Nat, +t: U32, +pos: R.Pos, +c: U32, +l01: U32, +l23: U32, +guess: U32, n: Nat, m: Array<U32>) -> Z.Val:
  +lo = R.pos.won(pos)
  +hi = (lo + tricks.left(d) : U32)
  +target = Z.driver.first(guess, lo, hi)
  narrow(14n, False{}, ask(False{}, d, t, pos, c, l01, l23, target, n, m), target, d, t, pos, c, l01, l23, lo, hi)

# A memory array for a search with this many cards in the hands.
def memory(+d: Nat) -> Array<U32>:
  +k = Z.tt.depth(tricks.left(d))
  Z.tt.ready(k, [Z.mem.none() : U32^k])

# A position with the cards in play at the start of its trick.
type At is Data:
  At{pos: R.Pos, l01: U32, l23: U32}

# The cards in play at the start of the trick after these plays, from a position at
# the start of a trick. For working them out in tests.
def live.after.go(xs: List<&2, U32>, +t: U32, +pos: R.Pos, +l01: U32, +l23: U32) -> At:
  match xs:
    case Nil{}:
      At{pos, l01, l23}
    case Con{+c, rest}:
      +child = R.play(t, pos, c)
      +bound = U32.is_zero(R.trick.played(R.pos.trick(child)))
      live.after.go(rest, t, child, R.sel(bound, R.pos.live01(child), l01), R.sel(bound, R.pos.live23(child), l23))

def live.after(xs: List<&2, U32>, +t: U32, +pos: R.Pos) -> At:
  live.after.go(xs, t, pos, R.pos.live01(pos), R.pos.live23(pos))
