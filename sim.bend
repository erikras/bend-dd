# sim.bend: the simulator's command line.
#
#   sim deal=<deal> contract=<contract> by=<seat> [play=<cards>] [rules...] [options...]
#
# Takes what one player can see, deals the cards they can't at random many times,
# keeps the layouts that fit the auction and the play, solves each one double dummy,
# and prints, for each card the player to move could play, the tricks declarer
# takes on average and how often the contract makes.
#
#   deal=N:AKQ2.K73.A84.Q52 - J43.AQ5.KQ62.A83 -
#       The deal in PBN, with - for each hand that can't be seen. A hand that can be
#       seen is written whole, as it was dealt, even when some of it has been played.
#   contract=4S          The level and the strain: S, H, D, C or NT. X and XX are
#                        accepted and make no difference.
#   by=S                 Declarer: N, E, S or W. The seat on declarer's left leads.
#   play="HK H2 H5 HA"   The cards played so far, in order, suit first or rank
#                        first, separated by spaces or commas. The seat to play next
#                        must be one that can be seen.
#
# Rules from the auction, each for a hidden seat, a count, and a range:
#
#   W.hcp=11-15          West has 11 to 15 high card points.
#   W.S=5-               West has five or more spades. Also -3 (at most three), 4
#                        (exactly four), 4+ (four or more). H, D and C for the
#                        other suits.
#
# A seat that has shown out of a suit is known to have no more of it, from the play.
#
#   n=200                How many layouts to keep (200).
#   seed=7               The random seed, to see the same simulation again. Without
#                        one a seed is picked at random and printed.
#   tries=1000           Give up after this many deals for each layout kept (1000).
#   layouts=5            Instead of simulating, print the first few layouts that fit
#                        and the tricks North-South take with each card, one by one.
#                        This is for checking against DDS (tools/simcheck.py).
#
# Runtime options go between +RTS and -RTS, such as +RTS --threads 8 -RTS.

import Base
import ./src/cards.bend as C
import ./src/rules.bend as R
import ./src/pbn.bend as P
import ./src/show.bend as V
import ./src/play.bend as Q
import ./src/sim.bend as S

# ---------------------------------------------------------------------------
# Words and cards

def comma.space(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{+c}, t}:
      SCon{Chr{R.sel(U32.is_eq(c, 44), 32, c)}, comma.space(t)}

def words.add(keep: Bool, s: String, rest: List<&2, String>) -> List<&2, String>:
  match keep:
    case True{}:
      s <> rest
    case False{}:
      rest

def words.keep(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      words.add(Bool.not(String.is_empty(h)), h, words.keep(t))

# The words of s, separated by spaces or commas.
def words(s: String) -> List<&2, String>:
  words.keep(String.split(comma.space(s), ' '))

# The index of character c in a table, or the table's length when it isn't there.
def index(table: String, +c: U32) -> U32:
  P.seat.scan(table, c, 0)

# A rank, 0 for the deuce to 12 for the ace, or 13 when it isn't one.
def rank.parse(s: String) -> U32:
  match s:
    case SCon{Chr{49}, SCon{Chr{48}, SNil{}}}:
      8
    case SCon{Chr{+c}, SNil{}}:
      +b = P.rank.bit(c)
      R.sel(U32.is_zero(b), 13, U32.from_nat(U32.log2(b)))
    case _:
      13

def card.make(+suit: U32, +rank: U32) -> U32:
  R.sel(U32.is_lt(suit, 4) && U32.is_lt(rank, 13), C.card.make(suit, rank), 255)

def card.back(r: String) -> U32:
  match r:
    case SCon{Chr{+l}, t}:
      card.make(index("SHDC", l), rank.parse(String.reverse(t)))
    case _:
      255

def card.go(+first: U32, rest: String, +whole: String) -> U32:
  +fs = index("SHDC", first)
  R.sel(U32.is_lt(fs, 4), card.make(fs, rank.parse(rest)), card.back(String.reverse(whole)))

# A card such as SA or AS, H10 or HT, in capitals, or 255 when it isn't one.
def card.parse(s: String, +whole: String) -> U32:
  match s:
    case SCon{Chr{+a}, rest}:
      card.go(a, rest, whole)
    case _:
      255

# The cards of a play, and the first word that isn't one.
type Cards is Data:
  Cards{bad: String, cards: List<&2, U32>}

def cards.cons(+w: String, +c: U32, r: Cards) -> Cards:
  match r:
    case Cards{+bad, cs}:
      Cards{S.sel.str(U32.is_eq(c, 255) && String.is_empty(bad), w, bad), c <> cs}

def cards.parse(xs: List<&2, String>) -> Cards:
  match xs:
    case Nil{}:
      Cards{"", Nil{}}
    case Con{+w, t}:
      +u = String.to_upper(w)
      cards.cons(w, card.parse(u, u), cards.parse(t))

# ---------------------------------------------------------------------------
# Options

type Opts is Data:
  Opts{err: String, deal: String, contract: String, by: String, play: String, n: U32, seed: U32, tries: U32, layouts: U32, rules: List<&2, S.Rule>}

# A count's range: lo and hi, and whether it could be read.
type Rg is Data:
  Rg{ok: Bool, lo: U32, hi: U32}

def num.or(r: Maybe<&2, U32>, +d: U32) -> U32:
  match r:
    case None{}:
      d
    case Some{x}:
      x

def num.ok(r: Maybe<&2, U32>) -> Bool:
  match r:
    case None{}:
      False{}
    case Some{_}:
      True{}

def ends.plus(+s: String) -> Bool:
  String.ends_with(s, "+")

def range.one(plus: Bool, +s: String) -> Rg:
  match plus:
    case True{}:
      +t = String.take(s, Nat.sub(String.length(s), 1n))
      Rg{num.ok(U32.read(t)), num.or(U32.read(t), 0), 255}
    case False{}:
      Rg{num.ok(U32.read(s)), num.or(U32.read(s), 0), num.or(U32.read(s), 0)}

def range.parts(xs: List<&2, String>) -> Rg:
  match xs:
    case Con{+a, Nil{}}:
      range.one(ends.plus(a), a)
    case Con{+a, Con{+b, Nil{}}}:
      Rg{num.ok(U32.read(a)) || num.ok(U32.read(b)), num.or(U32.read(a), 0), num.or(U32.read(b), 255)}
    case _:
      Rg{False{}, 0, 0}

# 11-15, 5-, -3, 4 or 4+.
def range.parse(+s: String) -> Rg:
  range.parts(String.split(s, '-'))

def first.char(s: String) -> Char:
  match s:
    case SCon{c, _}:
      c
    case _:
      Chr{0}

# What a rule counts: 0 to 3 for a suit's length, 4 for points, 5 for nothing known.
def what.parse(+s: String) -> U32:
  +u = String.to_upper(s)
  R.sel(String.eq(u, "HCP") || String.eq(u, "PTS"), 4, R.sel(Nat.is_eq(String.length(u), 1n), index("SHDC", Char.to_u32(first.char(u))), 5))

def seat.parse(+s: String) -> U32:
  R.sel(Nat.is_eq(String.length(s), 1n), P.seat.parse(first.char(String.to_upper(s))), 4)

def rule.make(+seat: U32, +what: U32, r: Rg) -> Maybe<&2, S.Rule>:
  match r:
    case Rg{+ok, +lo, +hi}:
      S.maybe.rule(ok && U32.is_lt(seat, 4) && U32.is_lt(what, 5), S.Rule{seat, what, lo, hi})

def rule.parts(xs: List<&2, String>, +v: String) -> Maybe<&2, S.Rule>:
  match xs:
    case Con{+a, Con{+b, Nil{}}}:
      rule.make(seat.parse(a), what.parse(b), range.parse(v))
    case _:
      None{}

# A rule from its key, such as W.hcp, and its value, such as 11-15.
def rule.parse(+k: String, +v: String) -> Maybe<&2, S.Rule>:
  rule.parts(String.split(k, '.'), v)

def opts.rule(r: Maybe<&2, S.Rule>, +k: String, +v: String, o: Opts) -> Opts:
  match r o:
    case Some{+x} Opts{+e, +d, +c, +b, +p, +n, +s, +t, +l, rs}:
      Opts{e, d, c, b, p, n, s, t, l, x <> rs}
    case None{} Opts{+e, +d, +c, +b, +p, +n, +s, +t, +l, rs}:
      Opts{S.sel.str(String.is_empty(e), "can't read " ++ k ++ "=" ++ v, e), d, c, b, p, n, s, t, l, rs}

def num.set(+hit: Bool, +v: String, +old: U32) -> U32:
  R.sel(hit, num.or(U32.read(v), old), old)

def opts.maybe.rule(isr: Bool, +k: String, +v: String, o: Opts) -> Opts:
  match isr:
    case True{}:
      opts.rule(rule.parse(k, v), k, v, o)
    case False{}:
      o

# One key=value argument.
def opts.set(+k: String, +v: String, o: Opts) -> Opts:
  match o:
    case Opts{+e, +d, +c, +b, +p, +n, +s, +t, +l, rs}:
      +isd = String.eq(k, "deal")
      +isc = String.eq(k, "contract")
      +isb = String.eq(k, "by")
      +isp = String.eq(k, "play")
      +isn = String.eq(k, "n")
      +iss = String.eq(k, "seed")
      +ist = String.eq(k, "tries")
      +isl = String.eq(k, "layouts")
      +known = isd || isc || isb || isp || isn || iss || ist || isl
      +isr = Bool.not(known) && String.contains(k, ".")
      +bad = Bool.not(known || isr) || ((isn || iss || ist || isl) && Bool.not(num.ok(U32.read(v))))
      +e2 = S.sel.str(String.is_empty(e) && bad, "can't read " ++ k ++ "=" ++ v, e)
      opts.maybe.rule(isr, k, v, Opts{e2, S.sel.str(isd, v, d), S.sel.str(isc, v, c), S.sel.str(isb, v, b), S.sel.str(isp, v, p), num.set(isn, v, n), num.set(iss, v, s), num.set(ist, v, t), num.set(isl, v, l), rs})


def opts.arg(xs: List<&2, String>, +whole: String, o: Opts) -> Opts:
  match xs o:
    case Con{+k, Con{+v, rest}} x:
      opts.set(k, String.join(v <> rest, "="), x)
    case _ Opts{+e, +d, +c, +b, +p, +n, +s, +t, +l, rs}:
      Opts{S.sel.str(String.is_empty(e), "expected key=value, not " ++ whole, e), d, c, b, p, n, s, t, l, rs}

def opts.all(xs: List<String>, o: Opts) -> Opts:
  match xs:
    case Nil{}:
      o
    case Con{+a, t}:
      opts.all(t, opts.arg(String.split(a, '='), a, o))

def args.tail(xs: List<String>) -> List<String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{_, t}:
      t

# ---------------------------------------------------------------------------
# The deal with hidden hands

# What can be seen: the hands in view, empty for the hidden ones, and which are
# hidden. err is empty when the deal could be read.
type View is Data:
  View{err: String, deal: C.Deal, hidden: U32}

# A hand: 0 when it can't be read, 1 in view, 2 hidden.
type Hd is Data:
  Hd{kind: U32, hand: C.Hand}

def hand.check(r: Maybe<&2, C.Hand>) -> Hd:
  match r:
    case None{}:
      Hd{0, C.hand.empty()}
    case Some{+h}:
      Hd{R.sel(U32.is_eq(C.hand.count(h), 13), 1, 0), h}

def hand.read.go(hid: Bool, +s: String) -> Hd:
  match hid:
    case True{}:
      Hd{2, C.hand.empty()}
    case False{}:
      hand.check(P.hand.parse(s))

def hand.read(+s: String) -> Hd:
  hand.read.go(String.eq(s, "-") || String.eq(s, "?"), s)

def hd.bit(h: Hd, +seat: U32) -> U32:
  match h:
    case Hd{+k, _}:
      (Bool.to_u32(U32.is_eq(k, 2)) << U32.to_nat(seat) : U32)

def hd.ok(h: Hd) -> Bool:
  match h:
    case Hd{+k, _}:
      U32.is_ne(k, 0)

def hd.hand(h: Hd) -> C.Hand:
  match h:
    case Hd{_, x}:
      x

def view.make(+first: U32, +a: Hd, +b: Hd, +c: Hd, +d: Hd) -> View:
  +ok = hd.ok(a) && hd.ok(b) && hd.ok(c) && hd.ok(d)
  +disjoint = P.deal.disjoint(hd.hand(a), hd.hand(b), hd.hand(c), hd.hand(d))
  +hidden = (hd.bit(a, first) .|. hd.bit(b, ((first + 1) .&. 3 : U32)) .|. hd.bit(c, ((first + 2) .&. 3 : U32)) .|. hd.bit(d, ((first + 3) .&. 3 : U32)) : U32)
  +err = S.sel.str(ok, S.sel.str(disjoint, "", "a card is in two hands"), "each hand needs 13 cards, or - when it is hidden")
  View{err, P.deal.place(U32.to_nat(first), hd.hand(a), hd.hand(b), hd.hand(c), hd.hand(d)), hidden}

def view.list(+first: U32, xs: List<&2, String>) -> View:
  match xs:
    case Con{+a, Con{+b, Con{+c, Con{+d, Nil{}}}}}:
      view.make(first, hand.read(a), hand.read(b), hand.read(c), hand.read(d))
    case _:
      View{"a deal needs four hands", C.deal.empty(), 0}

def view.go(ok: Bool, +seat: U32, rest: String) -> View:
  match ok:
    case True{}:
      view.list(seat, words(String.to_upper(rest)))
    case False{}:
      View{"a deal starts with N:, E:, S: or W:", C.deal.empty(), 0}

def view.parse(s: String) -> View:
  match s:
    case SCon{+f, SCon{Chr{58}, rest}}:
      +seat = P.seat.parse(f)
      view.go(U32.is_lt(seat, 4), seat, rest)
    case _:
      View{"a deal starts with a seat and a colon, as in N:", C.deal.empty(), 0}


# ---------------------------------------------------------------------------
# The contract

# The level times 8 plus the strain, or 0 when it can't be read.
def contract.parse(s: String) -> U32:
  match s:
    case SCon{Chr{+l}, SCon{Chr{+x}, _}}:
      +level = (l - 48 : U32)
      +strain = index("SHDCN", x)
      R.sel(U32.is_ge(level, 1) && U32.is_le(level, 7) && U32.is_lt(strain, 5), (level * 8 + strain : U32), 0)
    case _:
      0

def strain.name(+t: U32) -> String:
  S.sel.str(U32.is_eq(t, 4), "NT", V.suit.symbol(t))

# ---------------------------------------------------------------------------
# Printing

def seat.name(+s: U32) -> String:
  S.seat.name(U32.to_nat(s))

def suit.line(+h: C.Hand, +s: U32) -> String:
  +x = P.suit.print(C.hand.suit(U32.to_nat(s), h))
  V.suit.symbol(s) ++ " " ++ S.sel.str(String.is_empty(x), "-", x)

def hand.line(+h: C.Hand) -> String:
  suit.line(h, 0) ++ "  " ++ suit.line(h, 1) ++ "  " ++ suit.line(h, 2) ++ "  " ++ suit.line(h, 3)

def seat.role(+s: U32, +decl: U32) -> String:
  S.sel.str(U32.is_eq(s, decl), " (declarer)", S.sel.str(U32.is_eq(s, ((decl + 2) .&. 3 : U32)), " (dummy)", ""))

# The cards each seat in view still holds.
def view.line(+s: U32, +decl: U32, +hidden: U32, +view: C.Deal, +played: C.Hand) -> String:
  S.sel.str(S.bit.at(hidden, s), "", V.str.pad(seat.name(s) ++ seat.role(s, decl), 18) ++ hand.line(S.hand.minus(C.deal.hand(U32.to_nat(s), view), played)) ++ "\n")

def plural(+n: U32, +one: String, +many: String) -> String:
  U32.show(n) ++ " " ++ S.sel.str(U32.is_eq(n, 1), one, many)

# The cards on the table in the trick in progress, with who played them.
def table.go(xs: List<&2, U32>, +seat: U32) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+c, t}:
      ", " ++ S.card.name(c) ++ " by " ++ seat.name(seat) ++ table.go(t, ((seat + 1) .&. 3 : U32))

def two.digits(+x: U32) -> String:
  S.sel.str(U32.is_lt(x, 10), "0", "") ++ U32.show(x)

# x / d to two places, as in 9.84.
def ratio(+x: U32, +d: U32) -> String:
  +v = ((x * 100 + d / 2) / U32.max(d, 1) : U32)
  U32.show((v / 100 : U32)) ++ "." ++ two.digits((v % 100 : U32))

# x / d as a percentage to one place, as in 62.5%.
def percent(+x: U32, +d: U32) -> String:
  +v = ((x * 1000 + d / 2) / U32.max(d, 1) : U32)
  U32.show((v / 10 : U32)) ++ "." ++ U32.show((v % 10 : U32)) ++ "%"

# One row of the result: a card and the cards that play the same as it, the tricks
# added up, and the layouts where the contract makes.
type Row is Data:
  Row{name: String, sum: U32, makes: U32}

def rows.make(cs: List<&2, S.Cand>, ss: List<&2, U32>, ks: List<&2, U32>) -> List<&2, Row>:
  match cs ss ks:
    case Con{S.Cand{+c, +run}, a} Con{+s, b} Con{+k, d}:
      +suit = C.card.suit(c)
      Row{V.str.pad(V.suit.symbol(suit) ++ P.suit.print(run), (8 + Bool.to_u32(U32.is_eq(suit, 1)) : U32)), s, k} <> rows.make(a, b, d)
    case _ _ _:
      Nil{}

# Best first for declarer's side: the most makes, then the most tricks.
def row.le.decl(a: Row, b: Row) -> Bool:
  match a b:
    case Row{_, +s1, +k1} Row{_, +s2, +k2}:
      U32.is_gt(k1, k2) || (U32.is_eq(k1, k2) && U32.is_ge(s1, s2))

# Best first for the defenders: the fewest makes, then the fewest tricks.
def row.le.def(a: Row, b: Row) -> Bool:
  match a b:
    case Row{_, +s1, +k1} Row{_, +s2, +k2}:
      U32.is_lt(k1, k2) || (U32.is_eq(k1, k2) && U32.is_le(s1, s2))

def rows.sort(mine: Bool, xs: List<&2, Row>) -> List<&2, Row>:
  match mine:
    case True{}:
      List.sort(~Row, ~row.le.decl, xs)
    case False{}:
      List.sort(~Row, ~row.le.def, xs)

def rows.show(xs: List<&2, Row>, +deals: U32) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{Row{name, +s, +k}, t}:
      name ++ V.str.pad(ratio(s, deals), 9) ++ percent(k, deals) ++ "\n" ++ rows.show(t, deals)

def rule.text(r: S.Rule) -> String:
  match r:
    case S.Rule{+seat, +what, +lo, +hi}:
      +thing = S.sel.str(U32.is_eq(what, 4), " points", " " ++ V.suit.symbol(what))
      +range = S.sel.str(U32.is_eq(lo, hi), U32.show(lo), S.sel.str(U32.is_ge(hi, 40), U32.show(lo) ++ "+", U32.show(lo) ++ "-" ++ U32.show(hi)))
      seat.name(seat) ++ " " ++ range ++ thing

def rules.text(rs: List<&2, S.Rule>) -> String:
  match rs:
    case Nil{}:
      ""
    case Con{r, Nil{}}:
      rule.text(r)
    case Con{r, t}:
      rule.text(r) ++ ", " ++ rules.text(t)

def voids.text(k: Nat, +i: U32, +voids: U32) -> String:
  match k:
    case 0n:
      ""
    case 1n+p:
      S.sel.str(S.bit.at(voids, i), ", " ++ seat.name((i >> 2n : U32)) ++ " has no " ++ V.suit.symbol((i .&. 3 : U32)), "") ++ voids.text(p, (i + 1 : U32), voids)

# ---------------------------------------------------------------------------
# Putting it together

# Everything worked out from the arguments. err is empty when they make sense.
type Prep is Data:
  Prep{err: String, job: S.Job, view: C.Deal, hidden: U32, decl: U32, level: U32, t: U32, plays: List<&2, U32>, cands: List<&2, S.Cand>, n: U32, seed: U32, tries: U32, layouts: U32}

def first.err(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+h, t}:
      S.sel.str(String.is_empty(h), first.err(t), h)

def setup.err(m: S.Made) -> String:
  match m:
    case S.Made{+e, _}:
      e

def setup.of(m: S.Made) -> S.Setup:
  match m:
    case S.Made{_, +s}:
      s

def setup.pos(+s: S.Setup) -> R.Pos:
  match s:
    case S.Setup{_, _, _, _, _, _, +pos, _, _, _}:
      pos

def setup.played(+s: S.Setup) -> C.Hand:
  match s:
    case S.Setup{_, _, _, +played, _, _, _, _, _, _}:
      played

def setup.voids(+s: S.Setup) -> U32:
  match s:
    case S.Setup{_, _, _, _, +voids, _, _, _, _, _}:
      voids

def setup.d(+s: S.Setup) -> U32:
  match s:
    case S.Setup{_, _, _, _, _, _, _, _, _, +d}:
      d

def mover(+s: S.Setup) -> U32:
  R.trick.seat(R.pos.trick(setup.pos(s)))

def cards.of(c: Cards) -> List<&2, U32>:
  match c:
    case Cards{_, cs}:
      cs

def cards.bad(c: Cards) -> String:
  match c:
    case Cards{+b, _}:
      S.sel.str(String.is_empty(b), "", "can't read the card " ++ b)

# The first rule about a hand in view, which can't say anything new.
def rules.seen(rs: List<&2, S.Rule>, +hidden: U32) -> String:
  match rs:
    case Nil{}:
      ""
    case Con{S.Rule{+seat, _, _, _}, t}:
      S.sel.str(S.bit.at(hidden, seat), rules.seen(t, hidden), seat.name(seat) ++ "'s hand is in view, so a rule about it says nothing: rules are for hidden hands")

def prep.go(+v: View, +ct: U32, +decl: U32, +cs: Cards, +rs: List<&2, S.Rule>, +n: U32, +seed: U32, +tries: U32, +layouts: U32, +e0: String) -> Prep:
  match v:
    case View{+ve, +view, +hidden}:
      +t = (ct .&. 7 : U32)
      +level = (ct >> 3n : U32)
      +plays = cards.of(cs)
      +made = S.setup(view, hidden, t, decl, plays)
      +s = setup.of(made)
      +cands = S.cands(s)
      +busy = S.bit.at(hidden, mover(s))
      +over = U32.is_zero(setup.d(s))
      +err = first.err([e0, S.sel.str(U32.is_zero(ct), "can't read the contract: write it as 4S, 3NT and so on", ""), S.sel.str(U32.is_lt(decl, 4), "", "by= takes N, E, S or W"), ve, rules.seen(rs, hidden), cards.bad(cs), setup.err(made), S.sel.str(over, "every card has been played", ""), S.sel.str(busy, "it's " ++ seat.name(mover(s)) ++ "'s turn to play, and that hand is hidden", ""), S.sel.str(U32.is_zero(n), "n= must be at least 1", "")])
      Prep{err, S.Job{s, rs, S.cands.cards(cands), t, U32.is_zero((decl .&. 1 : U32)), (level + 6 : U32)}, view, hidden, decl, level, t, plays, cands, n, seed, tries, layouts}

def prep(o: Opts) -> Prep:
  match o:
    case Opts{+e, +d, +c, +b, +p, +n, +s, +t, +l, +rs}:
      +e0 = first.err([e, S.sel.str(String.is_empty(d), "deal= is needed", ""), S.sel.str(String.is_empty(c), "contract= is needed", ""), S.sel.str(String.is_empty(b), "by= is needed", "")])
      prep.go(view.parse(d), contract.parse(String.to_upper(c)), seat.parse(b), cards.parse(words(p)), List.reverse(&2, S.Rule, rs), n, s, t, l, e0)

# What the player sees: the contract, the hands in view, the trick so far.
def header(+p: Prep) -> String:
  match p:
    case Prep{_, S.Job{+s, +rs, _, _, _, _}, +view, +hidden, +decl, +level, +t, +plays, _, _, _, _, _}:
      +played = setup.played(s)
      +k = U32.from_nat(List.length(&2, U32, plays))
      +done = (k / 4 : U32)
      +now = (k % 4 : U32)
      +mv = mover(s)
      +won = R.pos.won(setup.pos(s))
      +mine = R.sel(U32.is_zero((decl .&. 1 : U32)), won, (done - won : U32))
      +onlead = U32.is_zero(now)
      +table = table.go(List.drop(&2, U32, plays, U32.to_nat((done * 4 : U32))), ((mv - now) .&. 3 : U32))
      +turn = "Trick " ++ U32.show((done + 1 : U32)) ++ ": " ++ seat.name(mv) ++ S.sel.str(onlead, " to lead.", " to play" ++ table ++ ".")
      +sofar = S.sel.str(U32.is_zero(done), "", "\nTricks so far: declarer " ++ U32.show(mine) ++ ", defenders " ++ U32.show((done - mine : U32)) ++ ".")
      +vs = voids.text(16n, 0, setup.voids(s))
      +auction = S.sel.str(List.is_empty(&2, S.Rule, rs), "", "Auction: " ++ rules.text(rs) ++ ".\n")
      +shown = S.sel.str(String.is_empty(vs), "", "From the play: " ++ String.drop(vs, 2n) ++ ".\n")
      "Contract: " ++ U32.show(level) ++ strain.name(t) ++ " by " ++ seat.name(decl) ++ ".\n\n" ++ view.line(0, decl, hidden, view, played) ++ view.line(1, decl, hidden, view, played) ++ view.line(2, decl, hidden, view, played) ++ view.line(3, decl, hidden, view, played) ++ "\n" ++ auction ++ shown ++ turn ++ sofar

def result(+p: Prep, o: S.Out, +ms: Nat, +threads: U32) -> String:
  match p o:
    case Prep{_, S.Job{+s, _, _, _, +declns, +goal}, _, _, +decl, _, _, _, +cands, +n, _, _, _} S.Out{+deals, +tries, +nodes, ss, ks}:
      +mv = mover(s)
      +mine = Bool.not(Bool.xor(declns, U32.is_zero((mv .&. 1 : U32))))
      +rows = rows.sort(mine, rows.make(cands, ss, ks))
      +short = S.sel.str(U32.is_lt(deals, n), "Only " ++ U32.show(deals) ++ " of the " ++ U32.show(n) ++ " layouts asked for fit before the tries ran out.\n", "")
      +stats = "Dealt " ++ U32.show(tries) ++ " layouts and kept " ++ U32.show(deals) ++ " (" ++ percent(deals, tries) ++ "), solved in " ++ Nat.show(ms) ++ " ms on " ++ plural(threads, "thread", "threads") ++ ", " ++ Nat.show(nodes) ++ " nodes.\n"
      +foot = "Tricks are declarer's, on average. Makes is how often declarer takes " ++ U32.show(goal) ++ " or more.\nBest for " ++ seat.name(mv) ++ " first."
      +table = "\nCard    Tricks   Makes\n" ++ rows.show(rows, deals) ++ "\n" ++ foot
      stats ++ S.sel.str(U32.is_zero(deals), "No layout fits the rules and the play. Loosen the rules, or raise tries=.", short ++ table)

def lines.print(xs: List<&2, String>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{h, t}:
      do IO<Unit>:
        IO.print(h)
        lines.print(t)

def cards.text(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+c, t}:
      " " ++ U32.show(c) ++ cards.text(t)

def main.layouts(+p: Prep, +seed: U32) -> IO(Unit):
  match p:
    case Prep{_, +job, _, _, _, _, _, _, _, _, _, +tries, +k}:
      do IO<Unit>:
        IO.print("# cards" ++ cards.text(S.cands.cards(S.cands(S.job.setup(job)))))
        lines.print(S.layouts(job, k, seed, tries))

def main.sim(+p: Prep, +seed: U32) -> IO(Unit):
  match p:
    case Prep{_, +job, _, _, _, _, _, _, _, +n, _, +tries, _}:
      do IO<Unit>:
        +threads : U32 <- IO.thread_count()
        t0 : Nat <- IO.now()
        +out : S.Out = S.run(job, n, seed, tries, threads)
        t1 : Nat <- IO.now()
        IO.print(result(p, out, Nat.sub(t1, t0), threads))
        IO.print("Seed " ++ U32.show(seed) ++ ": add seed=" ++ U32.show(seed) ++ " to see the same layouts again.")

def main.mode(lay: Bool, +p: Prep, +seed: U32) -> IO(Unit):
  match lay:
    case True{}:
      main.layouts(p, seed)
    case False{}:
      do IO<Unit>:
        IO.print(header(p))
        IO.print("")
        main.sim(p, seed)

def prep.layouts(+p: Prep) -> U32:
  match p:
    case Prep{_, _, _, _, _, _, _, _, _, _, _, _, +k}:
      k

def prep.seed(+p: Prep) -> U32:
  match p:
    case Prep{_, _, _, _, _, _, _, _, _, _, +s, _, _}:
      s

def main.go(ok: Bool, +err: String, +p: Prep) -> IO(Unit):
  match ok:
    case False{}:
      IO.die(Unit, 1, "sim: " ++ err)
    case True{}:
      do IO<Unit>:
        r : U32 <- IO.try(U32, IO.random_u32())
        main.mode(U32.is_ne(prep.layouts(p), 0), p, R.sel(U32.is_zero(prep.seed(p)), (r % 1000000 + 1 : U32), prep.seed(p)))

def main.prep(+p: Prep) -> IO(Unit):
  match p:
    case Prep{+err, _, _, _, _, _, _, _, _, _, _, _, _}:
      main.go(String.is_empty(err), err, p)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    main.prep(prep(opts.all(args.tail(args), Opts{"", "", "", "", "", 200, 0, 1000, 0, Nil{}})))
