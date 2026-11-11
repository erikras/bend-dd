# api.bend: the solver for the web page.
#
# Pure defs with plain inputs and outputs, strings and numbers, so that the page
# never sees the solver's types. Nothing here changes how the solver works: each def
# calls the same functions the command lines call.

import Base
import ../src/cards.bend as C
import ../src/pbn.bend as P
import ../src/brute.bend as B
import ../src/search.bend as Z
import ../src/deal.bend as D
import ../src/rules.bend as R
import ../src/play.bend as Q
import ../src/sim.bend as S
import ../sim.bend as M

def ints(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, Nil{}}:
      U32.show(h)
    case Con{h, t}:
      U32.show(h) ++ " " ++ ints(t)

def table.text(t: B.Table) -> String:
  match t:
    case B.Table{ts, _}:
      ints(ts)

def strain.even(even: Bool, +t: U32, +deal: C.Deal) -> String:
  match even:
    case True{}:
      table.text(Z.strain.table(t, deal))
    case False{}:
      "error: hands differ in length"

def strain.parsed(+t: U32, d: Maybe<&2, C.Deal>) -> String:
  match d:
    case None{}:
      "error: not a PBN deal"
    case Some{+deal}:
      strain.even(B.deal.even(deal), t, deal)

# The tricks for one strain (0 spades, 1 hearts, 2 diamonds, 3 clubs, 4 notrump)
# with each declarer in turn, N E S W, as four numbers separated by spaces.
def strain(pbn: String, +t: U32) -> String:
  strain.parsed(t, P.parse(pbn))

# The whole table, 20 numbers: strain by strain, as dd prints them without the nodes.
def table(+pbn: String) -> String:
  strain(pbn, 0) ++ " " ++ strain(pbn, 1) ++ " " ++ strain(pbn, 2) ++ " " ++ strain(pbn, 3) ++ " " ++ strain(pbn, 4)

# The deal dd --random seed gives, in PBN.
def random(+seed: U32) -> String:
  P.print(D.random(seed))

# ---------------------------------------------------------------------------
# The simulator and the play

def json.ints.go(xs: List<&2, U32>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      U32.show(h) <> json.ints.go(t)

def json.ints(xs: List<&2, U32>) -> String:
  "[" ++ String.join(json.ints.go(xs), ",") ++ "]"

def json.cands.go(xs: List<&2, S.Cand>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{S.Cand{+c, +run}, t}:
      ("[" ++ U32.show(c) ++ ",\"" ++ S.card.name(c) ++ "\",\"" ++ P.suit.print(run) ++ "\"]") <> json.cands.go(t)

# The cards to try, each as "card run": its name and the ranks that play the same.
def json.cands(xs: List<&2, S.Cand>) -> String:
  "[" ++ String.join(json.cands.go(xs), ",") ++ "]"

def json.err(+e: String) -> String:
  "{\"error\":\"" ++ e ++ "\"}"

def opts.line(blank: Bool, +a: String, o: M.Opts) -> M.Opts:
  match blank:
    case True{}:
      o
    case False{}:
      M.opts.arg(String.split(String.trim(a), '='), String.trim(a), o)

# The options of a setup: key=value lines, as sim takes them on its command line.
def opts.lines(xs: List<&2, String>, o: M.Opts) -> M.Opts:
  match xs:
    case Nil{}:
      o
    case Con{+a, t}:
      opts.lines(t, opts.line(String.is_empty(String.trim(a)), a, o))

def setup.prep(+setup: String) -> M.Prep:
  M.prep(opts.lines(String.lines(setup), M.Opts{"", "", "", "", "", 200, 0, 1000, 0, Nil{}}))

def sim.out(+p: M.Prep, o: S.Out) -> String:
  match p o:
    case M.Prep{_, S.Job{+s, _, _, _, +declns, +goal}, _, _, _, _, _, _, +cands, _, _, _, _} S.Out{+deals, +tries, +nodes, ss, ks}:
      "{\"deals\":" ++ U32.show(deals) ++ ",\"tries\":" ++ U32.show(tries) ++ ",\"nodes\":" ++ Nat.show(nodes) ++ ",\"goal\":" ++ U32.show(goal) ++ ",\"declns\":" ++ S.sel.str(declns, "true", "false") ++ ",\"mover\":" ++ U32.show(M.mover(s)) ++ ",\"cards\":" ++ json.cands(cands) ++ ",\"sums\":" ++ json.ints(ss) ++ ",\"makes\":" ++ json.ints(ks) ++ "}"

def prep.ok(+p: M.Prep) -> Bool:
  match p:
    case M.Prep{+err, _, _, _, _, _, _, _, _, _, _, _, _}:
      String.is_empty(err)

def sim.go(ok: Bool, +p: M.Prep, +seed: U32, +first: U32, +count: U32) -> String:
  match ok p:
    case False{} M.Prep{+err, _, _, _, _, _, _, _, _, _, _, _, _}:
      json.err(err)
    case True{} M.Prep{_, +job, _, _, _, _, _, _, _, _, _, +tries, _}:
      sim.out(p, S.leaf.run(U32.is_zero(count), count, first, seed, tries, job))

# A part of a simulation: layouts first to first + count - 1 of the simulation that
# sim runs for these options and this seed, as JSON: the layouts kept and dealt, the
# nodes, and for each card to try the tricks declarer took added up and the layouts
# where the contract made. The parts of a simulation add up to the whole, since each
# layout has its own random state from the seed and its index.
#
# setup is sim's options, one key=value a line: deal=, contract=, by=, play=, the
# rules, and tries=. n= and seed= are ignored here.
def sim(+setup: String, +seed: U32, +first: U32, +count: U32) -> String:
  +p = setup.prep(setup)
  sim.go(prep.ok(p), p, seed, first, count)

def cards.vals(v: S.Vals) -> List<&2, U32>:
  match v:
    case S.Vals{vs, _, _}:
      vs

def cards.go(ok: Bool, +p: M.Prep) -> String:
  match ok p:
    case False{} M.Prep{+err, _, _, _, _, _, _, _, _, _, _, _, _}:
      json.err(err)
    case True{} M.Prep{_, +job, +view, _, _, _, _, _, +cands, _, _, _, _}:
      +d = S.setup.d(S.job.setup(job))
      "{\"cards\":" ++ json.cands(cands) ++ ",\"ns\":" ++ json.ints(cards.vals(S.solve.layout(job, view, 0n, Q.memory(d)))) ++ "}"

# The tricks North-South take in the whole deal with each card the player to move
# could play, from a full deal in PBN, the strain (S, H, D, C or NT), the declarer
# (N, E, S or W) and the cards played so far, as sim reads them. Cards that play
# the same are given once, with their run. As JSON.
def cards(+pbn: String, +strain: String, +decl: String, +played: String) -> String:
  +p = setup.prep("deal=" ++ pbn ++ "\ncontract=1" ++ strain ++ "\nby=" ++ decl ++ "\nplay=" ++ played)
  cards.go(prep.ok(p), p)
