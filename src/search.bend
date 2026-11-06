# search.bend: the zero-window search and the target driver.
#
# search answers one question, "can North-South finish with at least target
# tricks?", in the style of DDS (docs/PLAN.md, 2.1 and 4). A driver asks it again
# and again, moving a lower and an upper bound until they meet.
#
# Against plain minimax this adds:
#   - stopping at the first move that settles a node;
#   - target too low or too high: at the start of a trick, the tricks won and
#     the tricks left may already decide the answer;
#   - card equivalence: of the cards in one hand that are adjacent among the cards
#     in play, only the top one is tried;
#   - move ordering: cards that win the trick first, and high cards on lead.

import Base
import ./cards.bend as C
import ./rules.bend as R
import ./brute.bend as B

# A true or false answer with the positions visited so far. Nat counts them: it
# is a machine word at run time, and it stops the program at 2^48 instead of
# wrapping, which takes days at this solver's rates.
type Res is Data:
  Res{ok: Bool, nodes: Nat}

# ---------------------------------------------------------------------------
# Card equivalence

# Walks the cards of m from the lowest up, keeping a card when the next card in
# play above it is not in m. rest is what is left to look at, and n bounds the
# loop: a holding has at most 13 cards.
def tops.go(n: Nat, z: Bool, +m: U32, +live: U32, +rest: U32, +acc: U32) -> U32:
  match n z:
    case 0n _:
      acc
    case 1n+p True{}:
      acc
    case 1n+p False{}:
      +b = (rest .&. (0 - rest) : U32)
      +more = (rest .^. b : U32)
      +above = (live .&. (0 - (b << 1n)) : U32)
      +next = (above .&. (0 - above) : U32)
      tops.go(p, U32.is_zero(more), m, live, more, R.sel(U32.is_zero((next .&. m : U32)), (acc .|. b : U32), acc))

# The cards of holding m worth trying, where live is every card in play in that
# suit at the start of the trick, m included. Cards with no other card in play
# between them win and lose to exactly the same cards, so only the top one of
# each run counts. A card already on the table in this trick is in live, since
# it still splits a run: with Q on the table, K and J are different.
def tops(+m: U32, +live: U32) -> U32:
  tops.go(13n, U32.is_zero(m), m, live, m, 0)

# ---------------------------------------------------------------------------
# Move ordering

# The cards of k that win straight away. On lead, that is the top card in play.
# Later in the trick, it is a higher card of the suit of the card winning so far,
# or any trump over a card that is not one. Agrees with R.beats, see LAWS.bend.
def wins.later(same: Bool, +trump: Bool, +k: U32, +best: U32) -> U32:
  match same:
    case True{}:
      (k .&. (0 - (C.card.bit(best) << 1n)) : U32)
    case False{}:
      R.sel(trump, k, 0)

def wins(first: Bool, +s: U32, +k: U32, +live: U32, +t: U32, +best: U32) -> U32:
  match first:
    case True{}:
      (k .&. (1 << U32.log2(live)) : U32)
    case False{}:
      wins.later(U32.is_eq(s, C.card.suit(best)), U32.is_eq(s, t), k, best)

# Pushes the cards of a holding onto acc, highest first, as R.moves.suit does, or
# lowest first.
def push.low(n: Nat, z: Bool, +suit: U32, +m: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n z:
    case 0n _:
      acc
    case 1n+p True{}:
      acc
    case 1n+p False{}:
      +r = U32.log2(m)
      +rest = (m .^. (1 << r) : U32)
      push.low(p, U32.is_zero(rest), suit, rest, C.card.make(suit, U32.from_nat(r)) <> acc)

def push(high: Bool, +suit: U32, +m: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match high:
    case True{}:
      R.moves.suit(suit, m, acc)
    case False{}:
      push.low(13n, U32.is_zero(m), suit, m, acc)

def push.all(+high: Bool, +a: U32, +b: U32, +c: U32, +d: U32, acc: List<&2, U32>) -> List<&2, U32>:
  push(high, 0, a, push(high, 1, b, push(high, 2, c, push(high, 3, d, acc))))

# The moves to try from the holdings k, of which w win straight away. On lead:
# winners, then the rest, high cards first. When partner is winning the trick,
# the cheapest cards first and any that overtake last. Otherwise the cheapest
# winner first, then the cheapest of the rest.
def order(+first: Bool, +mine: Bool, +k0: U32, +k1: U32, +k2: U32, +k3: U32, +w0: U32, +w1: U32, +w2: U32, +w3: U32) -> List<&2, U32>:
  +front = Bool.or(first, Bool.not(mine))
  +a0 = R.sel(front, w0, (k0 .^. w0 : U32))
  +a1 = R.sel(front, w1, (k1 .^. w1 : U32))
  +a2 = R.sel(front, w2, (k2 .^. w2 : U32))
  +a3 = R.sel(front, w3, (k3 .^. w3 : U32))
  push.all(first, a0, a1, a2, a3,
    push.all(first, (k0 .^. a0 : U32), (k1 .^. a1 : U32), (k2 .^. a2 : U32), (k3 .^. a3 : U32), Nil{}))

# ---------------------------------------------------------------------------
# Move generation

# The holding of suit s that may be played: all of it when free to play anything,
# otherwise only the suit led.
def legal(+free: Bool, +s: U32, +lead: U32, +m: U32) -> U32:
  R.sel(free || U32.is_eq(s, lead), m, 0)

def gen.go(+t: U32, +l01: U32, +l23: U32, +h01: U32, +h23: U32, +tr: U32) -> List<&2, U32>:
  +lead = R.trick.lead(tr)
  +seat = R.trick.seat(tr)
  +best = R.trick.best(tr)
  +played = R.trick.played(tr)
  +first = U32.is_zero(played)
  +mine = U32.is_zero(((seat .^. R.trick.owner(tr)) .&. 1 : U32))
  +free = U32.is_zero(R.suit.mask(U32.to_nat(lead), h01, h23))
  +l0 = (l01 >> 16n : U32)
  +l1 = (l01 .&. 65535 : U32)
  +l2 = (l23 >> 16n : U32)
  +l3 = (l23 .&. 65535 : U32)
  +k0 = tops(legal(free, 0, lead, (h01 >> 16n : U32)), l0)
  +k1 = tops(legal(free, 1, lead, (h01 .&. 65535 : U32)), l1)
  +k2 = tops(legal(free, 2, lead, (h23 >> 16n : U32)), l2)
  +k3 = tops(legal(free, 3, lead, (h23 .&. 65535 : U32)), l3)
  order(first, mine, k0, k1, k2, k3,
    wins(first, 0, k0, l0, t, best), wins(first, 1, k1, l1, t, best),
    wins(first, 2, k2, l2, t, best), wins(first, 3, k3, l3, t, best))

# The moves to try in a position, where l01 and l23 are the cards in play at the
# start of this trick. The trick word starts with no cards played.
def gen(+t: U32, pos: R.Pos, +l01: U32, +l23: U32) -> List<&2, U32>:
  match pos:
    case R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, +tr, won}:
      +seat = U32.to_nat(R.trick.seat(tr))
      gen.go(t, l01, l23, R.pick(seat, n01, e01, s01, w01), R.pick(seat, n23, e23, s23, w23), tr)

# ---------------------------------------------------------------------------
# Target cutoffs

# What the tricks alone say about reaching target: 0 nothing, 1 North-South have
# it already, 2 they cannot get there even if they win every trick left.
def cut(+won: U32, +left: U32, +target: U32) -> U32:
  R.sel(U32.is_ge(won, target), 1, R.sel(U32.is_lt((won + left : U32), target), 2, 0))

def cut.at(bound: Bool, +won: U32, +left: U32, +target: U32) -> U32:
  match bound:
    case True{}:
      cut(won, left, target)
    case False{}:
      0

# The moves to try after a cut: none when it settled the position.
def enter.go(go: Bool, +t: U32, +pos: R.Pos, +l01: U32, +l23: U32) -> List<&2, U32>:
  match go:
    case True{}:
      gen(t, pos, l01, l23)
    case False{}:
      Nil{}

# The answer a node starts from. With no cut, it is the one that does not settle
# the node yet: false when North-South choose, true when East-West choose.
def enter.ok(+code: U32, +ns: Bool) -> Bool:
  (U32.is_zero(code) && Bool.not(ns)) || U32.is_eq(code, 1)

def live.at(bound: Bool, +x: U32, +old: U32) -> U32:
  match bound:
    case True{}:
      x
    case False{}:
      old

# ---------------------------------------------------------------------------
# The search

# Tries the moves ms of a position with d cards left. r is the answer so far: a
# call cannot be destructured in place, so a child's answer rides into the next
# sibling as an argument. The answer settles a node once it says true for
# North-South or false for East-West, and otherwise the node goes on to the next
# move; with no moves left, the answer stands.
#
# A child has one card fewer, and a sibling has one move fewer with the same d.
def search(+d: Nat, ms: List<&2, U32>, ns: Bool, r: Res, +t: U32, +target: U32, +l01: U32, +l23: U32, +pos: R.Pos) -> Res:
  match d ms ns r:
    case 0n _ _ x:
      x
    case 1n+p Nil{} _ x:
      x
    case 1n+p _ True{} Res{True{}, n}:
      Res{True{}, n}
    case 1n+p _ False{} Res{False{}, n}:
      Res{False{}, n}
    case 1n+p Con{c, rest} True{} Res{False{}, n}:
      +child = R.play(t, pos, c)
      +cns = R.pos.ns(child)
      +tr = R.pos.trick(child)
      +bound = U32.is_zero(R.trick.played(tr))
      +code = cut.at(bound, R.pos.won(child), (U32.from_nat(p) >> 2n : U32), target)
      +c01 = live.at(bound, R.pos.live01(child), l01)
      +c23 = live.at(bound, R.pos.live23(child), l23)
      search(1n+p, rest, True{},
        search(p, enter.go(U32.is_zero(code), t, child, c01, c23), cns, Res{enter.ok(code, cns), 1n+n}, t, target, c01, c23, child),
        t, target, l01, l23, pos)
    case 1n+p Con{c, rest} False{} Res{True{}, n}:
      +child = R.play(t, pos, c)
      +cns = R.pos.ns(child)
      +tr = R.pos.trick(child)
      +bound = U32.is_zero(R.trick.played(tr))
      +code = cut.at(bound, R.pos.won(child), (U32.from_nat(p) >> 2n : U32), target)
      +c01 = live.at(bound, R.pos.live01(child), l01)
      +c23 = live.at(bound, R.pos.live23(child), l23)
      search(1n+p, rest, False{},
        search(p, enter.go(U32.is_zero(code), t, child, c01, c23), cns, Res{enter.ok(code, cns), 1n+n}, t, target, c01, c23, child),
        t, target, l01, l23, pos)

# Runs one search from the start of a trick, unless told there is nothing to ask.
def ask(stop: Bool, +d: Nat, +t: U32, +pos: R.Pos, +target: U32, n: Nat) -> Res:
  match stop:
    case True{}:
      Res{False{}, n}
    case False{}:
      +ns = R.pos.ns(pos)
      +l01 = R.pos.live01(pos)
      +l23 = R.pos.live23(pos)
      search(d, gen(t, pos, l01, l23), ns, Res{Bool.not(ns), n}, t, target, l01, l23, pos)

# ---------------------------------------------------------------------------
# The driver

# The bounds after asking about target: true raises the lower bound to it, and
# false lowers the upper bound to just below it.
def driver.lo(+ok: Bool, +target: U32, +lo: U32) -> U32:
  R.sel(ok, target, lo)

def driver.hi(+ok: Bool, +target: U32, +hi: U32) -> U32:
  R.sel(ok, hi, (target - 1 : U32))

# What to ask next: one step on from where the last answer left the bounds, since
# a value tends to be close to the guess it was found from.
def driver.next(+ok: Bool, +lo: U32, +hi: U32) -> U32:
  R.sel(ok, (lo + 1 : U32), hi)

# What to ask first: the guess, moved into the range where the answer is unknown.
def driver.first(+g: U32, +lo: U32, +hi: U32) -> U32:
  U32.max((lo + 1 : U32), U32.min(g, hi))

# Moves the bounds until they meet. done says they already had before this step,
# and r is the answer about target. Each step closes the gap by at least one, so
# the fuel only has to be more than the tricks left.
def narrow(fuel: Nat, done: Bool, r: Res, +target: U32, +d: Nat, +t: U32, +pos: R.Pos, +lo: U32, +hi: U32) -> B.Res:
  match fuel done r:
    case 0n _ Res{_, n}:
      B.Res{lo, n}
    case 1n+p True{} Res{_, n}:
      B.Res{lo, n}
    case 1n+p False{} Res{+ok, n}:
      +lo2 = driver.lo(ok, target, lo)
      +hi2 = driver.hi(ok, target, hi)
      +stop = U32.is_ge(lo2, hi2)
      +next = driver.next(ok, lo2, hi2)
      narrow(p, stop, ask(stop, d, t, pos, next, n), next, d, t, pos, lo2, hi2)

# North-South's tricks from the start of a trick with d cards left, starting from
# a guess at the answer.
def solve(+d: Nat, +t: U32, +pos: R.Pos, +guess: U32, n: Nat) -> B.Res:
  +lo = R.pos.won(pos)
  +hi = (lo + (U32.from_nat(d) >> 2n) : U32)
  +stop = U32.is_ge(lo, hi)
  +target = driver.first(guess, lo, hi)
  narrow(14n, stop, ask(stop, d, t, pos, target, n), target, d, t, pos, lo, hi)

# ---------------------------------------------------------------------------
# The table

# Fills the table from its last entry to its first, so that it comes out in the
# order of B.table. r is the result for entry i + 1, and it feeds the guess for
# entry i: moving the lead by one seat rarely changes the result by much.
def table.go(k: Nat, r: B.Res, +i: U32, +d: Nat, +left: U32, +deal: C.Deal, acc: List<&2, U32>) -> B.Table:
  match k r:
    case 0n B.Res{+v, n}:
      B.Table{B.table.entry(U32.is_zero(((i + 1) .&. 1 : U32)), left, v) <> acc, n}
    case 1n+p B.Res{+v, n}:
      +t = (i >> 2n : U32)
      +decl = (i .&. 3 : U32)
      +leader = ((decl + 1) .&. 3 : U32)
      table.go(p, solve(d, t, R.pos.start(deal, leader), v, n), (i - 1 : U32), d, left, deal,
        B.table.entry(U32.is_zero(((i + 1) .&. 1 : U32)), left, v) <> acc)

# The double dummy table of a deal, as B.table gives it.
def table(+deal: C.Deal) -> B.Table:
  +cards = B.deal.cards(deal)
  +d = U32.to_nat(cards)
  +left = (cards / 4 : U32)
  table.go(19n, solve(d, 4, R.pos.start(deal, 0), ((left + 1) / 2 : U32), 0n), 18, d, left, deal, Nil{})
