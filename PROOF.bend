# PROOF.bend: the proofs of LAWS.bend. `bend PROOF.bend` is the gate.

import Base
import ./src/cards.bend as C
import ./src/pbn.bend as P
import ./src/rules.bend as R
import ./src/brute.bend as B
import ./SPEC.bend as S
import ./LAWS.bend as Laws

# ---------------------------------------------------------------------------
# PBN: string splitting, then the whole deal

# Splitting after a free prefix peels off that prefix.
def split_free(a: String, +sep: Char, +b: String, same: {Char.is_eq(sep, sep) == True{} : Bool}, f: S.Free(sep, a)) ->
  {String.split(a ++ SCon{sep, b}, sep) == (a <> String.split(b, sep)) : List<&2, String>}:
  match a:
    case SNil{}:
      %Equal.sym(Bool, Char.is_eq(sep, sep), True{}, same) : {String.split.fin(sep, String.split(b, sep), _) == (SNil{} <> String.split(b, sep)) : List<&2, String>}
      {==}
    case SCon{h, t}:
      (ne, ft) = f
      %Equal.sym(Bool, Char.is_eq(h, sep), False{}, ne) : {String.split.fin(h, String.split(t ++ SCon{sep, b}, sep), _) == (SCon{h, t} <> String.split(b, sep)) : List<&2, String>}
      %Equal.sym(List<&2, String>, String.split(t ++ SCon{sep, b}, sep), t <> String.split(b, sep), split_free(t, sep, b, same, ft)) : {String.split.fin(h, _, False{}) == (SCon{h, t} <> String.split(b, sep)) : List<&2, String>}
      {==}

# With no separator at all, splitting gives the whole string back.
def split_none(a: String, +sep: Char, f: S.Free(sep, a)) ->
  {String.split(a, sep) == [a] : List<&2, String>}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      (ne, ft) = f
      %Equal.sym(Bool, Char.is_eq(h, sep), False{}, ne) : {String.split.fin(h, String.split(t, sep), _) == [SCon{h, t}] : List<&2, String>}
      %Equal.sym(List<&2, String>, String.split(t, sep), [t], split_none(t, sep, ft)) : {String.split.fin(h, _, False{}) == [SCon{h, t}] : List<&2, String>}
      {==}

# Free carries over appending.
def free_append(a: String, +b: String, +sep: Char, fa: S.Free(sep, a), fb: S.Free(sep, b)) -> S.Free(sep, a ++ b):
  match a:
    case SNil{}:
      fb
    case SCon{h, t}:
      (ne, ft) = fa
      (ne, free_append(t, b, sep, ft, fb))

def free_emit(keep: Bool, -c: Char, -r: String, +sep: Char, fc: {Char.is_eq(c, sep) == False{} : Bool}, fr: S.Free(sep, r)) -> S.Free(sep, P.suit.emit(keep, c, r)):
  match keep:
    case True{}:
      (fc, fr)
    case False{}:
      fr

# A printed holding only uses letters from the table.
def free_print(+table: String, +bit: U32, +m: U32, +sep: Char, f: S.Free(sep, table)) -> S.Free(sep, P.suit.print.go(table, bit, m)):
  match table:
    case SNil{}:
      Unit{}
    case SCon{c, t}:
      (ne, ft) = f
      free_emit(U32.is_ne((m .&. bit : U32), 0), c, P.suit.print.go(t, (bit >> 1n : U32), m), sep, ne, free_print(t, (bit >> 1n : U32), m, sep, ft))

def free_ranks_dot() -> S.Free('.', P.ranks()):
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, Unit{})))))))))))))

def free_ranks_space() -> S.Free(' ', P.ranks()):
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, Unit{})))))))))))))

def free_suit_dot(+m: U32) -> S.Free('.', P.suit.print(m)):
  free_print(P.ranks(), 4096, m, '.', free_ranks_dot())

def free_suit_space(+m: U32) -> S.Free(' ', P.suit.print(m)):
  free_print(P.ranks(), 4096, m, ' ', free_ranks_space())

# Printing and then splitting a hand on dots lists its holdings.
def hand_split(+s: U32, +x: U32, +d: U32, +c: U32) ->
  {String.split(P.hand.print(C.Hand{s, x, d, c}), '.') == [P.suit.print(s), P.suit.print(x), P.suit.print(d), P.suit.print(c)] : List<&2, String>}:
  %Equal.sym(List<&2, String>, String.split(P.suit.print(s) ++ SCon{'.', P.suit.print(x) ++ SCon{'.', P.suit.print(d) ++ SCon{'.', P.suit.print(c)}}}, '.'), P.suit.print(s) <> String.split(P.suit.print(x) ++ SCon{'.', P.suit.print(d) ++ SCon{'.', P.suit.print(c)}}, '.'), split_free(P.suit.print(s), '.', P.suit.print(x) ++ SCon{'.', P.suit.print(d) ++ SCon{'.', P.suit.print(c)}}, {==}, free_suit_dot(s))) : {_ == [P.suit.print(s), P.suit.print(x), P.suit.print(d), P.suit.print(c)] : List<&2, String>}
  %Equal.sym(List<&2, String>, String.split(P.suit.print(x) ++ SCon{'.', P.suit.print(d) ++ SCon{'.', P.suit.print(c)}}, '.'), P.suit.print(x) <> String.split(P.suit.print(d) ++ SCon{'.', P.suit.print(c)}, '.'), split_free(P.suit.print(x), '.', P.suit.print(d) ++ SCon{'.', P.suit.print(c)}, {==}, free_suit_dot(x))) : {(P.suit.print(s) <> _) == [P.suit.print(s), P.suit.print(x), P.suit.print(d), P.suit.print(c)] : List<&2, String>}
  %Equal.sym(List<&2, String>, String.split(P.suit.print(d) ++ SCon{'.', P.suit.print(c)}, '.'), P.suit.print(d) <> String.split(P.suit.print(c), '.'), split_free(P.suit.print(d), '.', P.suit.print(c), {==}, free_suit_dot(d))) : {(P.suit.print(s) <> P.suit.print(x) <> _) == [P.suit.print(s), P.suit.print(x), P.suit.print(d), P.suit.print(c)] : List<&2, String>}
  %Equal.sym(List<&2, String>, String.split(P.suit.print(c), '.'), [P.suit.print(c)], split_none(P.suit.print(c), '.', free_suit_dot(c))) : {(P.suit.print(s) <> P.suit.print(x) <> P.suit.print(d) <> _) == [P.suit.print(s), P.suit.print(x), P.suit.print(d), P.suit.print(c)] : List<&2, String>}
  {==}

# A printed hand parses back, when its holdings do.
def hand_rt(+s: U32, +x: U32, +d: U32, +c: U32, gs: S.Good(s), gx: S.Good(x), gd: S.Good(d), gc: S.Good(c)) ->
  {P.hand.parse(P.hand.print(C.Hand{s, x, d, c})) == Some{C.Hand{s, x, d, c}} : Maybe<&2, C.Hand>}:
  %Equal.sym(List<&2, String>, String.split(P.hand.print(C.Hand{s, x, d, c}), '.'), [P.suit.print(s), P.suit.print(x), P.suit.print(d), P.suit.print(c)], hand_split(s, x, d, c)) : {P.hand.parse.list(_) == Some{C.Hand{s, x, d, c}} : Maybe<&2, C.Hand>}
  %Equal.sym(Maybe<&2, U32>, P.suit.parse(P.suit.print(s)), Some{s}, gs) : {P.hand.parse.make(_, P.suit.parse(P.suit.print(x)), P.suit.parse(P.suit.print(d)), P.suit.parse(P.suit.print(c))) == Some{C.Hand{s, x, d, c}} : Maybe<&2, C.Hand>}
  %Equal.sym(Maybe<&2, U32>, P.suit.parse(P.suit.print(x)), Some{x}, gx) : {P.hand.parse.make(Some{s}, _, P.suit.parse(P.suit.print(d)), P.suit.parse(P.suit.print(c))) == Some{C.Hand{s, x, d, c}} : Maybe<&2, C.Hand>}
  %Equal.sym(Maybe<&2, U32>, P.suit.parse(P.suit.print(d)), Some{d}, gd) : {P.hand.parse.make(Some{s}, Some{x}, _, P.suit.parse(P.suit.print(c))) == Some{C.Hand{s, x, d, c}} : Maybe<&2, C.Hand>}
  %Equal.sym(Maybe<&2, U32>, P.suit.parse(P.suit.print(c)), Some{c}, gc) : {P.hand.parse.make(Some{s}, Some{x}, Some{d}, _) == Some{C.Hand{s, x, d, c}} : Maybe<&2, C.Hand>}
  {==}

def hand_good(+h: C.Hand, g: S.Good.hand(h)) -> {P.hand.parse(P.hand.print(h)) == Some{h} : Maybe<&2, C.Hand>}:
  match h:
    case C.Hand{+s, +x, +d, +c}:
      (gs, gx, gd, gc) = g
      hand_rt(s, x, d, c, gs, gx, gd, gc)

# A printed hand has no spaces.
def free_hand_space(+h: C.Hand) -> S.Free(' ', P.hand.print(h)):
  match h:
    case C.Hand{+s, +x, +d, +c}:
      free_append(P.suit.print(s), SCon{'.', P.suit.print(x) ++ SCon{'.', P.suit.print(d) ++ SCon{'.', P.suit.print(c)}}}, ' ', free_suit_space(s),
        ({==}, free_append(P.suit.print(x), SCon{'.', P.suit.print(d) ++ SCon{'.', P.suit.print(c)}}, ' ', free_suit_space(x),
          ({==}, free_append(P.suit.print(d), SCon{'.', P.suit.print(c)}, ' ', free_suit_space(d),
            ({==}, free_suit_space(c)))))))

# Printing and then splitting the body of a deal on spaces lists its hands.
def deal_split(+a: C.Hand, +b: C.Hand, +c: C.Hand, +d: C.Hand) ->
  {String.split(P.hand.print(a) ++ SCon{' ', P.hand.print(b) ++ SCon{' ', P.hand.print(c) ++ SCon{' ', P.hand.print(d)}}}, ' ') == [P.hand.print(a), P.hand.print(b), P.hand.print(c), P.hand.print(d)] : List<&2, String>}:
  %Equal.sym(List<&2, String>, String.split(P.hand.print(a) ++ SCon{' ', P.hand.print(b) ++ SCon{' ', P.hand.print(c) ++ SCon{' ', P.hand.print(d)}}}, ' '), P.hand.print(a) <> String.split(P.hand.print(b) ++ SCon{' ', P.hand.print(c) ++ SCon{' ', P.hand.print(d)}}, ' '), split_free(P.hand.print(a), ' ', P.hand.print(b) ++ SCon{' ', P.hand.print(c) ++ SCon{' ', P.hand.print(d)}}, {==}, free_hand_space(a))) : {_ == [P.hand.print(a), P.hand.print(b), P.hand.print(c), P.hand.print(d)] : List<&2, String>}
  %Equal.sym(List<&2, String>, String.split(P.hand.print(b) ++ SCon{' ', P.hand.print(c) ++ SCon{' ', P.hand.print(d)}}, ' '), P.hand.print(b) <> String.split(P.hand.print(c) ++ SCon{' ', P.hand.print(d)}, ' '), split_free(P.hand.print(b), ' ', P.hand.print(c) ++ SCon{' ', P.hand.print(d)}, {==}, free_hand_space(b))) : {(P.hand.print(a) <> _) == [P.hand.print(a), P.hand.print(b), P.hand.print(c), P.hand.print(d)] : List<&2, String>}
  %Equal.sym(List<&2, String>, String.split(P.hand.print(c) ++ SCon{' ', P.hand.print(d)}, ' '), P.hand.print(c) <> String.split(P.hand.print(d), ' '), split_free(P.hand.print(c), ' ', P.hand.print(d), {==}, free_hand_space(c))) : {(P.hand.print(a) <> P.hand.print(b) <> _) == [P.hand.print(a), P.hand.print(b), P.hand.print(c), P.hand.print(d)] : List<&2, String>}
  %Equal.sym(List<&2, String>, String.split(P.hand.print(d), ' '), [P.hand.print(d)], split_none(P.hand.print(d), ' ', free_hand_space(d))) : {(P.hand.print(a) <> P.hand.print(b) <> P.hand.print(c) <> _) == [P.hand.print(a), P.hand.print(b), P.hand.print(c), P.hand.print(d)] : List<&2, String>}
  {==}

# ---------------------------------------------------------------------------
# From the exhaustive check to every holding

def disc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

# False is not True.
def no_ft(e: {False{} == True{} : Bool}) -> Empty:
  %e : disc(_)
  Unit{}

def disc.cmp(c: Cmp) -> Type:
  match c:
    case EQ{}:
      Empty
    case o:
      Unit

def no_lt(e: {LT{} == EQ{} : Cmp}) -> Empty:
  %e : disc.cmp(_)
  Unit{}

def no_gt(e: {GT{} == EQ{} : Cmp}) -> Empty:
  %e : disc.cmp(_)
  Unit{}

def and_true(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool} & {b == True{} : Bool}:
  match a:
    case True{}:
      ({==}, e)
    case False{}:
      Empty.absurd({a == True{} : Bool} & {b == True{} : Bool}, no_ft(e))

def cmp_fin_eq(t: Cmp, ab: Bool, bb: Bool, e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}) -> {t == EQ{} : Cmp} & {ab == bb : Bool}:
  match t:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp} & {ab == bb : Bool}, no_lt(e))
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp} & {ab == bb : Bool}, no_gt(e))
    case EQ{}:
      match ab bb:
        case False{} False{}:
          ({==}, {==})
        case False{} True{}:
          Empty.absurd({EQ{} == EQ{} : Cmp} & {False{} == True{} : Bool}, no_lt(e))
        case True{} False{}:
          Empty.absurd({EQ{} == EQ{} : Cmp} & {True{} == False{} : Bool}, no_gt(e))
        case True{} True{}:
          ({==}, {==})

def word_eq.go(-p: Nat, -x: Bool, -s: Word(p), -y: Bool, -t: Word(p), r: {s == t : Word(p)}, e: {x == y : Bool}) -> {WCon{x, s} == WCon{y, t} : Word(1n+p)}:
  %e : {WCon{x, s} == WCon{_, t} : Word(1n+p)}
  %r : {WCon{x, s} == WCon{x, _} : Word(1n+p)}
  {==}

def word_eq.fin(-p: Nat, -x: Bool, -s: Word(p), -y: Bool, -t: Word(p), pr: {Word.cmp(p, s, t) == EQ{} : Cmp} & {x == y : Bool}, rec: {Word.cmp(p, s, t) == EQ{} : Cmp} -> {s == t : Word(p)}) -> {WCon{x, s} == WCon{y, t} : Word(1n+p)}:
  (e1, e2) = pr
  word_eq.go(p, x, s, y, t, rec(e1), e2)

def word_eq(+n: Nat, +a: Word(n), +b: Word(n), e: {Word.cmp(n, a, b) == EQ{} : Cmp}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{x, s} WCon{y, t}:
          word_eq.fin(p, x, s, y, t, cmp_fin_eq(Word.cmp(p, s, t), x, y, e), q => word_eq(p, s, t, q))

def cmp_eq(c: Cmp, e: {Cmp.is_eq(c) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case EQ{}:
      {==}
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, no_ft(e))
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, no_ft(e))

# U32.is_eq means equal.
def u32_eq(+a: U32, +b: U32, e: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{x} U32{y}:
      %word_eq(32n, x, y, cmp_eq(Word.cmp(32n, x, y), e)) : {U32{x} == U32{_} : U32}
      {==}

def good_of_ok.go(+a: Maybe<&2, U32>, +m: U32, e: {S.holding.ok.go(a, m) == True{} : Bool}) -> {a == Some{m} : Maybe<&2, U32>}:
  match a:
    case None{}:
      Empty.absurd({None{} == Some{m} : Maybe<&2, U32>}, no_ft(e))
    case Some{+x}:
      %u32_eq(x, m, e) : {Some{x} == Some{_} : Maybe<&2, U32>}
      {==}

def good_of_ok(+m: U32, e: {S.holding.ok(m) == True{} : Bool}) -> S.Good(m):
  good_of_ok.go(P.suit.parse(P.suit.print(m)), m, e)

def step(k: Nat, m: U32) -> U32:
  match k:
    case 0n:
      m
    case 1n+j:
      step(j, U32.inc(m))

def step_inc(+k: Nat, +m: U32) -> {step(k, U32.inc(m)) == U32.inc(step(k, m)) : U32}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      step_inc(j, U32.inc(m))

def step_from(+k: Nat) -> {step(k, 0) == U32.from_nat(k) : U32}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(U32, step(j, U32.inc(0)), U32.inc(step(j, 0)), step_inc(j, 0)) : {_ == U32.from_nat(1n+j) : U32}
      %Equal.sym(U32, step(j, 0), U32.from_nat(j), step_from(j)) : {U32.inc(_) == U32.from_nat(1n+j) : U32}
      {==}

def Sigma.fst.bool(-A: Bool, -B: Bool, p: {A == True{} : Bool} & {B == True{} : Bool}) -> {A == True{} : Bool}:
  (a, b) = p
  a

def Sigma.snd.bool(-A: Bool, -B: Bool, p: {A == True{} : Bool} & {B == True{} : Bool}) -> {B == True{} : Bool}:
  (a, b) = p
  b

# Holding number k of a run that checked out checks out.
def holdings_at(+n: Nat, +k: Nat, +m: U32, all: {S.holdings.ok(n, m) == True{} : Bool}, lt: {Nat.is_lt(k, n) == True{} : Bool}) -> {S.holding.ok(step(k, m)) == True{} : Bool}:
  match n k:
    case 0n 0n:
      Empty.absurd({S.holding.ok(m) == True{} : Bool}, no_ft(lt))
    case 0n 1n+j:
      Empty.absurd({S.holding.ok(step(1n+j, m)) == True{} : Bool}, no_ft(lt))
    case 1n+p 0n:
      Sigma.fst.bool(S.holding.ok(m), S.holdings.ok(p, U32.inc(m)), and_true(S.holding.ok(m), S.holdings.ok(p, U32.inc(m)), all))
    case 1n+p 1n+j:
      holdings_at(p, j, U32.inc(m), Sigma.snd.bool(S.holding.ok(m), S.holdings.ok(p, U32.inc(m)), and_true(S.holding.ok(m), S.holdings.ok(p, U32.inc(m)), all)), lt)

def Laws.holding_roundtrip():
  {==}

def Laws.holding_good(k, lt):
  %step_from(k) : S.Good(_)
  good_of_ok(step(k, 0), holdings_at(8192n, k, 0, Laws.holding_roundtrip(), lt))

def Laws.hand_good(a, b, c, d, la, lb, lc, ld):
  (Laws.holding_good(a, la), Laws.holding_good(b, lb), Laws.holding_good(c, lc), Laws.holding_good(d, ld))

def Laws.deal_roundtrip(n, e, s, w, gn, ge, gs, gw, dj):
  %Equal.sym(List<&2, String>, String.split(P.hand.print(n) ++ SCon{' ', P.hand.print(e) ++ SCon{' ', P.hand.print(s) ++ SCon{' ', P.hand.print(w)}}}, ' '), [P.hand.print(n), P.hand.print(e), P.hand.print(s), P.hand.print(w)], deal_split(n, e, s, w)) : {P.deal.list(0n, _) == Some{C.Deal{n, e, s, w}} : Maybe<&2, C.Deal>}
  %Equal.sym(Maybe<&2, C.Hand>, P.hand.parse(P.hand.print(n)), Some{n}, hand_good(n, gn)) : {P.deal.make(0n, _, P.hand.parse(P.hand.print(e)), P.hand.parse(P.hand.print(s)), P.hand.parse(P.hand.print(w))) == Some{C.Deal{n, e, s, w}} : Maybe<&2, C.Deal>}
  %Equal.sym(Maybe<&2, C.Hand>, P.hand.parse(P.hand.print(e)), Some{e}, hand_good(e, ge)) : {P.deal.make(0n, Some{n}, _, P.hand.parse(P.hand.print(s)), P.hand.parse(P.hand.print(w))) == Some{C.Deal{n, e, s, w}} : Maybe<&2, C.Deal>}
  %Equal.sym(Maybe<&2, C.Hand>, P.hand.parse(P.hand.print(s)), Some{s}, hand_good(s, gs)) : {P.deal.make(0n, Some{n}, Some{e}, _, P.hand.parse(P.hand.print(w))) == Some{C.Deal{n, e, s, w}} : Maybe<&2, C.Deal>}
  %Equal.sym(Maybe<&2, C.Hand>, P.hand.parse(P.hand.print(w)), Some{w}, hand_good(w, gw)) : {P.deal.make(0n, Some{n}, Some{e}, Some{s}, _) == Some{C.Deal{n, e, s, w}} : Maybe<&2, C.Deal>}
  %Equal.sym(Bool, P.deal.disjoint(n, e, s, w), True{}, dj) : {P.deal.check(_, 0n, n, e, s, w) == Some{C.Deal{n, e, s, w}} : Maybe<&2, C.Deal>}
  {==}


def Laws.place_north(a, b, c, d):
  {==}

def Laws.place_east(a, b, c, d):
  {==}

def Laws.place_south(a, b, c, d):
  {==}

def Laws.place_west(a, b, c, d):
  {==}

def Laws.seat_letters():
  {==}

def Laws.card_codes():
  {==}

def Laws.moves_follow_spades(h01, h23, e):
  %Equal.sym(Bool, U32.is_zero((h01 >> 16n : U32)), False{}, e) : {R.moves.pick(_, 0, (h01 >> 16n : U32), h01, h23) == R.moves.suit(0, (h01 >> 16n : U32), Nil{}) : List<&2, U32>}
  {==}

def Laws.moves_void_spades(h01, h23, e):
  %Equal.sym(Bool, U32.is_zero((h01 >> 16n : U32)), True{}, e) : {R.moves.pick(_, 0, (h01 >> 16n : U32), h01, h23) == R.moves.all(h01, h23) : List<&2, U32>}
  {==}

def Laws.moves_follow_hearts(h01, h23, e):
  %Equal.sym(Bool, U32.is_zero((h01 .&. 65535 : U32)), False{}, e) : {R.moves.pick(_, 1, (h01 .&. 65535 : U32), h01, h23) == R.moves.suit(1, (h01 .&. 65535 : U32), Nil{}) : List<&2, U32>}
  {==}

def Laws.moves_void_hearts(h01, h23, e):
  %Equal.sym(Bool, U32.is_zero((h01 .&. 65535 : U32)), True{}, e) : {R.moves.pick(_, 1, (h01 .&. 65535 : U32), h01, h23) == R.moves.all(h01, h23) : List<&2, U32>}
  {==}

def Laws.moves_follow_diamonds(h01, h23, e):
  %Equal.sym(Bool, U32.is_zero((h23 >> 16n : U32)), False{}, e) : {R.moves.pick(_, 2, (h23 >> 16n : U32), h01, h23) == R.moves.suit(2, (h23 >> 16n : U32), Nil{}) : List<&2, U32>}
  {==}

def Laws.moves_void_diamonds(h01, h23, e):
  %Equal.sym(Bool, U32.is_zero((h23 >> 16n : U32)), True{}, e) : {R.moves.pick(_, 2, (h23 >> 16n : U32), h01, h23) == R.moves.all(h01, h23) : List<&2, U32>}
  {==}

def Laws.moves_follow_clubs(h01, h23, e):
  %Equal.sym(Bool, U32.is_zero((h23 .&. 65535 : U32)), False{}, e) : {R.moves.pick(_, 3, (h23 .&. 65535 : U32), h01, h23) == R.moves.suit(3, (h23 .&. 65535 : U32), Nil{}) : List<&2, U32>}
  {==}

def Laws.moves_void_clubs(h01, h23, e):
  %Equal.sym(Bool, U32.is_zero((h23 .&. 65535 : U32)), True{}, e) : {R.moves.pick(_, 3, (h23 .&. 65535 : U32), h01, h23) == R.moves.all(h01, h23) : List<&2, U32>}
  {==}

def Laws.moves_on_lead(h01, h23):
  {==}

def Laws.beats_rules():
  {==}

def Laws.trick_winner_spades():
  {==}

def Laws.trick_winner_clubs():
  {==}

def Laws.trick_winner_nt():
  {==}

def Laws.moves_holding():
  {==}

def Laws.tops_low_ranks():
  {==}

def Laws.tops_high_ranks():
  {==}

def Laws.tops_all_in_play():
  {==}

def Laws.tops_void(live):
  {==}

def Laws.cut_sound():
  {==}

def Laws.driver_finds():
  {==}

def Laws.gen_keeps_moves():
  {==}

def Laws.run_low_ranks():
  {==}

def Laws.run_high_ranks():
  {==}

def Laws.sure_never_exceeds():
  {==}

def Laws.sure_three_cards():
  {==}

def Laws.search_is_brute():
  {==}

def Laws.ws_kth_inverse():
  {==}

def Laws.run_below_all_live():
  {==}

def Laws.run_below_gaps():
  {==}

def Laws.bounds_give_back():
  {==}

def Laws.owners_agree():
  {==}

# ---------------------------------------------------------------------------
# The proof foundation


# The word lemmas.

def Laws.from_double(p, k):
  match k:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(Word(1n+p), S.W.from(1n+p, Nat.double(j)), WCon{False{}, S.W.from(p, j)}, Laws.from_double(p, j)) : {Word.inc(1n+p, Word.inc(1n+p, _)) == WCon{False{}, Word.inc(p, S.W.from(p, j))} : Word(1n+p)}
      {==}

def Laws.from_odd(p, k):
  %Equal.sym(Word(1n+p), S.W.from(1n+p, Nat.double(k)), WCon{False{}, S.W.from(p, k)}, Laws.from_double(p, k)) : {Word.inc(1n+p, _) == WCon{True{}, S.W.from(p, k)} : Word(1n+p)}
  {==}

def Laws.from_zero_width(k):
  match k:
    case 0n:
      {==}
    case 1n+j:
      {==}

def Laws.from_to(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          Laws.from_zero_width(Word.to_nat(0n, WNil{}))
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          %Equal.sym(Word(1n+p), S.W.from(1n+p, Nat.double(Word.to_nat(p, t))), WCon{False{}, S.W.from(p, Word.to_nat(p, t))}, Laws.from_double(p, Word.to_nat(p, t))) : {_ == WCon{False{}, t} : Word(1n+p)}
          %Equal.sym(Word(p), S.W.from(p, Word.to_nat(p, t)), t, Laws.from_to(p, t)) : {WCon{False{}, _} == WCon{False{}, t} : Word(1n+p)}
          {==}
        case WCon{True{}, +t}:
          %Equal.sym(Word(1n+p), S.W.from(1n+p, 1n+Nat.double(Word.to_nat(p, t))), WCon{True{}, S.W.from(p, Word.to_nat(p, t))}, Laws.from_odd(p, Word.to_nat(p, t))) : {_ == WCon{True{}, t} : Word(1n+p)}
          %Equal.sym(Word(p), S.W.from(p, Word.to_nat(p, t)), t, Laws.from_to(p, t)) : {WCon{True{}, _} == WCon{True{}, t} : Word(1n+p)}
          {==}

def Laws.u32_from(k):
  match k:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(U32, U32.from_nat(j), U32{S.W.from(32n, j)}, Laws.u32_from(j)) : {U32.inc(_) == U32{Word.inc(32n, S.W.from(32n, j))} : U32}
      {==}

def Laws.u32_roundtrip(u):
  match u:
    case U32{+w}:
      %Equal.sym(U32, U32.from_nat(Word.to_nat(32n, w)), U32{S.W.from(32n, Word.to_nat(32n, w))}, Laws.u32_from(Word.to_nat(32n, w))) : {_ == U32{w} : U32}
      %Equal.sym(Word(32n), S.W.from(32n, Word.to_nat(32n, w)), w, Laws.from_to(32n, w)) : {U32{_} == U32{w} : U32}
      {==}

# Facts about holdings, which rest on the word lemmas.

def no_lt0(+x: Nat, e: {Nat.is_lt(x, 0n) == True{} : Bool}) -> Empty:
  match x:
    case 0n:
      no_ft(e)
    case 1n+y:
      no_ft(e)

def facts_at(+n: Nat, +k: Nat, +m: U32, all: {S.facts.all(n, m) == True{} : Bool}, lt: {Nat.is_lt(k, n) == True{} : Bool}) -> {S.facts(step(k, m)) == True{} : Bool}:
  match n k:
    case 0n 0n:
      Empty.absurd({S.facts(m) == True{} : Bool}, no_ft(lt))
    case 0n 1n+j:
      Empty.absurd({S.facts(step(1n+j, m)) == True{} : Bool}, no_ft(lt))
    case 1n+p 0n:
      Sigma.fst.bool(S.facts(m), S.facts.all(p, U32.inc(m)), and_true(S.facts(m), S.facts.all(p, U32.inc(m)), all))
    case 1n+p 1n+j:
      facts_at(p, j, U32.inc(m), Sigma.snd.bool(S.facts(m), S.facts.all(p, U32.inc(m)), and_true(S.facts(m), S.facts.all(p, U32.inc(m)), all)), lt)

def Laws.lt_dbl(x, y, e):
  match x y:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, no_ft(e))
    case 0n 1n+b:
      {==}
    case 1n+a 0n:
      Empty.absurd({Nat.is_lt(Nat.double(1n+a), 0n) == True{} : Bool}, no_ft(e))
    case 1n+a 1n+b:
      Laws.lt_dbl(a, b, e)

def Laws.lt_dbl1(x, y, e):
  match x y:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(1n, 0n) == True{} : Bool}, no_ft(e))
    case 0n 1n+b:
      {==}
    case 1n+a 0n:
      Empty.absurd({Nat.is_lt(1n+Nat.double(1n+a), 0n) == True{} : Bool}, no_ft(e))
    case 1n+a 1n+b:
      Laws.lt_dbl1(a, b, e)

def Laws.lt_one(x, e):
  match x:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          Empty.absurd({Nat.is_lt(Nat.double(1n), 1n) == True{} : Bool}, no_ft(e))
        case 1n+b:
          Empty.absurd({Nat.is_lt(Nat.double(2n+b), 1n) == True{} : Bool}, no_ft(e))

def Laws.pow2_pos(j):
  match j:
    case 0n:
      {==}
    case 1n+i:
      Laws.lt_dbl(0n, S.pow2(i), Laws.pow2_pos(i))

def Laws.bound(n, j, w, e):
  match n:
    case 0n:
      match w:
        case WNil{}:
          Laws.pow2_pos(j)
    case 1n+p:
      match j w:
        case 0n WCon{False{}, +t}:
          Laws.lt_one(Word.to_nat(p, t), Laws.bound(p, 0n, t, Equal.cong(Word(1n+p), Word(p), (x => S.w.tail(p, x)), Word.and(1n+p, WCon{False{}, t}, S.ones(1n+p, 0n)), WCon{False{}, t}, e)))
        case 0n WCon{True{}, +t}:
          Empty.absurd({Nat.is_lt(Word.to_nat(1n+p, WCon{True{}, t}), S.pow2(0n)) == True{} : Bool}, no_ft(Equal.cong(Word(1n+p), Bool, (x => S.w.head(p, x)), Word.and(1n+p, WCon{True{}, t}, S.ones(1n+p, 0n)), WCon{True{}, t}, e)))
        case 1n+i WCon{False{}, +t}:
          Laws.lt_dbl(Word.to_nat(p, t), S.pow2(i), Laws.bound(p, i, t, Equal.cong(Word(1n+p), Word(p), (x => S.w.tail(p, x)), Word.and(1n+p, WCon{False{}, t}, S.ones(1n+p, 1n+i)), WCon{False{}, t}, e)))
        case 1n+i WCon{True{}, +t}:
          Laws.lt_dbl1(Word.to_nat(p, t), S.pow2(i), Laws.bound(p, i, t, Equal.cong(Word(1n+p), Word(p), (x => S.w.tail(p, x)), Word.and(1n+p, WCon{True{}, t}, S.ones(1n+p, 1n+i)), WCon{True{}, t}, e)))

def Laws.mask_ones():
  {==}

def Laws.holding_lt(u, h):
  match u:
    case U32{+w}:
      Laws.bound(32n, 13n, w, Equal.cong(U32, Word(32n), (x => S.u.word(x)), (U32{w} .&. 8191 : U32), U32{w}, h))

def Laws.facts_all():
  {==}

def Laws.facts_nat(k, lt):
  %step_from(k) : {S.facts(_) == True{} : Bool}
  facts_at(8192n, k, 0, Laws.facts_all(), lt)

def Laws.facts_holding(u, h):
  %Equal.sym(U32, u, U32.from_nat(U32.to_nat(u)), Equal.sym(U32, U32.from_nat(U32.to_nat(u)), u, Laws.u32_roundtrip(u))) : {S.facts(_) == True{} : Bool}
  Laws.facts_nat(U32.to_nat(u), Laws.holding_lt(u, h))

def Laws.card_code(s, r, ls, lr):
  match s:
    case 0n:
      match r:
            case 0n:
              {==}
            case 1n:
              {==}
            case 2n:
              {==}
            case 3n:
              {==}
            case 4n:
              {==}
            case 5n:
              {==}
            case 6n:
              {==}
            case 7n:
              {==}
            case 8n:
              {==}
            case 9n:
              {==}
            case 10n:
              {==}
            case 11n:
              {==}
            case 12n:
              {==}
            case 13n+x:
              Empty.absurd({S.code.ok(0n, 13n+x) == True{} : Bool}, no_lt0(x, lr))
    case 1n:
      match r:
            case 0n:
              {==}
            case 1n:
              {==}
            case 2n:
              {==}
            case 3n:
              {==}
            case 4n:
              {==}
            case 5n:
              {==}
            case 6n:
              {==}
            case 7n:
              {==}
            case 8n:
              {==}
            case 9n:
              {==}
            case 10n:
              {==}
            case 11n:
              {==}
            case 12n:
              {==}
            case 13n+x:
              Empty.absurd({S.code.ok(1n, 13n+x) == True{} : Bool}, no_lt0(x, lr))
    case 2n:
      match r:
            case 0n:
              {==}
            case 1n:
              {==}
            case 2n:
              {==}
            case 3n:
              {==}
            case 4n:
              {==}
            case 5n:
              {==}
            case 6n:
              {==}
            case 7n:
              {==}
            case 8n:
              {==}
            case 9n:
              {==}
            case 10n:
              {==}
            case 11n:
              {==}
            case 12n:
              {==}
            case 13n+x:
              Empty.absurd({S.code.ok(2n, 13n+x) == True{} : Bool}, no_lt0(x, lr))
    case 3n:
      match r:
            case 0n:
              {==}
            case 1n:
              {==}
            case 2n:
              {==}
            case 3n:
              {==}
            case 4n:
              {==}
            case 5n:
              {==}
            case 6n:
              {==}
            case 7n:
              {==}
            case 8n:
              {==}
            case 9n:
              {==}
            case 10n:
              {==}
            case 11n:
              {==}
            case 12n:
              {==}
            case 13n+x:
              Empty.absurd({S.code.ok(3n, 13n+x) == True{} : Bool}, no_lt0(x, lr))
    case 4n+y:
      Empty.absurd({S.code.ok(4n+y, r) == True{} : Bool}, no_lt0(y, ls))


# ---------------------------------------------------------------------------
# Words as sets of bits

def no_tf(e: {True{} == False{} : Bool}) -> Empty:
  no_ft(Equal.sym(Bool, True{}, False{}, e))


def hd(-p: Nat, -x: Bool, -y: Bool, -a: Word(p), -b: Word(p), e: {WCon{x, a} == WCon{y, b} : Word(1n+p)}) -> {x == y : Bool}:
  Equal.cong(Word(1n+p), Bool, (w => S.w.head(p, w)), WCon{x, a}, WCon{y, b}, e)


def tl(-p: Nat, -x: Bool, -y: Bool, -a: Word(p), -b: Word(p), e: {WCon{x, a} == WCon{y, b} : Word(1n+p)}) -> {a == b : Word(p)}:
  Equal.cong(Word(1n+p), Word(p), (w => S.w.tail(p, w)), WCon{x, a}, WCon{y, b}, e)


def cons.eq(-p: Nat, -x: Bool, -y: Bool, -a: Word(p), -b: Word(p), h: {x == y : Bool}, t: {a == b : Word(p)}) -> {WCon{x, a} == WCon{y, b} : Word(1n+p)}:
  %h : {WCon{x, a} == WCon{_, b} : Word(1n+p)}
  %t : {WCon{x, a} == WCon{x, _} : Word(1n+p)}
  {==}


def isz(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+k:
      Unit


def no_s0(-k: Nat, e: {1n+k == 0n : Nat}) -> Empty:
  %e : isz(_)
  Unit{}


def no_0s(-k: Nat, e: {0n == 1n+k : Nat}) -> Empty:
  no_s0(k, Equal.sym(Nat, 0n, 1n+k, e))


def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+k:
      k


def s_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, (x => pred(x)), 1n+a, 1n+b, e)


def andand(+x: Bool, +y: Bool) -> {Bool.and(Bool.and(x, y), x) == Bool.and(x, y) : Bool}:
  match x y:
    case False{} _:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}


def Laws.and_sub_left(n, a, k):
  match n:
    case 0n:
      match a k:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a k:
        case WCon{+x, +at} WCon{+y, +kt}:
          cons.eq(p, Bool.and(Bool.and(x, y), x), Bool.and(x, y), Word.and(p, Word.and(p, at, kt), at), Word.and(p, at, kt), andand(x, y), Laws.and_sub_left(p, at, kt))


def btrans(+x: Bool, +y: Bool, +z: Bool, h1: {Bool.and(x, y) == x : Bool}, h2: {Bool.and(y, z) == y : Bool}) -> {Bool.and(x, z) == x : Bool}:
  match x y z:
    case False{} _ _:
      {==}
    case True{} False{} _:
      Empty.absurd({Bool.and(True{}, z) == True{} : Bool}, no_ft(h1))
    case True{} True{} False{}:
      Empty.absurd({Bool.and(True{}, False{}) == True{} : Bool}, no_ft(h2))
    case True{} True{} True{}:
      {==}


def Laws.sub_trans(n, a, b, c, ab, bc):
  match n:
    case 0n:
      match a c:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{+x, +at} WCon{+y, +bt} WCon{+z, +ct}:
          cons.eq(p, Bool.and(x, z), x, Word.and(p, at, ct), at,
            btrans(x, y, z, hd(p, Bool.and(x, y), x, Word.and(p, at, bt), at, ab), hd(p, Bool.and(y, z), y, Word.and(p, bt, ct), bt, bc)),
            Laws.sub_trans(p, at, bt, ct, tl(p, Bool.and(x, y), x, Word.and(p, at, bt), at, ab), tl(p, Bool.and(y, z), y, Word.and(p, bt, ct), bt, bc)))


def Laws.count0_zero(n, x, e):
  match n:
    case 0n:
      match x:
        case WNil{}:
          {==}
    case 1n+p:
      match x:
        case WCon{False{}, +t}:
          cons.eq(p, False{}, False{}, t, Word.zero(p), {==}, Laws.count0_zero(p, t, e))
        case WCon{True{}, +t}:
          Empty.absurd({WCon{True{}, t} == Word.zero(1n+p) : Word(1n+p)}, no_s0(S.word.count(p, t), e))


def bxor_f(+b: Bool) -> {Bool.xor(b, False{}) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}


def Laws.xor_zero(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          cons.eq(p, Bool.xor(b, False{}), b, Word.xor(p, t, Word.zero(p)), t, bxor_f(b), Laws.xor_zero(p, t))


def count_xor.top(+p: Nat, +xt: Word(p), +wb: Bool, +wt: Word(p), h: {wb == True{} : Bool}, z: {xt == Word.zero(p) : Word(p)}) -> {S.word.count(1n+p, WCon{wb, wt}) == 1n+S.word.count(1n+p, Word.xor(1n+p, WCon{wb, wt}, WCon{True{}, xt})) : Nat}:
  %Equal.sym(Bool, wb, True{}, h) : {S.word.count(1n+p, WCon{_, wt}) == 1n+S.word.count(1n+p, Word.xor(1n+p, WCon{_, wt}, WCon{True{}, xt})) : Nat}
  %Equal.sym(Word(p), xt, Word.zero(p), z) : {S.word.count(1n+p, WCon{True{}, wt}) == 1n+S.word.count(1n+p, Word.xor(1n+p, WCon{True{}, wt}, WCon{True{}, _})) : Nat}
  %Equal.sym(Word(p), Word.xor(p, wt, Word.zero(p)), wt, Laws.xor_zero(p, wt)) : {1n+S.word.count(p, wt) == 1n+S.word.count(p, _) : Nat}
  {==}


def count_xor.low(+p: Nat, +xt: Word(p), +wb: Bool, +wt: Word(p), ih: {S.word.count(p, wt) == 1n+S.word.count(p, Word.xor(p, wt, xt)) : Nat}) -> {S.word.count(1n+p, WCon{wb, wt}) == 1n+S.word.count(1n+p, Word.xor(1n+p, WCon{wb, wt}, WCon{False{}, xt})) : Nat}:
  match wb:
    case False{}:
      ih
    case True{}:
      %Equal.sym(Nat, S.word.count(p, wt), 1n+S.word.count(p, Word.xor(p, wt, xt)), ih) : {1n+_ == 2n+S.word.count(p, Word.xor(p, wt, xt)) : Nat}
      {==}


def Laws.count_xor(n, x, w, s, one):
  match n:
    case 0n:
      match x w:
        case WNil{} WNil{}:
          Empty.absurd({0n == 1n : Nat}, no_0s(0n, one))
    case 1n+p:
      match x w:
        case WCon{True{}, +xt} WCon{+wb, +wt}:
          count_xor.top(p, xt, wb, wt, hd(p, wb, True{}, Word.and(p, xt, wt), xt, s), Laws.count0_zero(p, xt, s_inj(S.word.count(p, xt), 0n, one)))
        case WCon{False{}, +xt} WCon{+wb, +wt}:
          count_xor.low(p, xt, wb, wt, Laws.count_xor(p, xt, wt, tl(p, False{}, False{}, Word.and(p, xt, wt), xt, s), one))


def put_sub(+p: Nat, +c: Bool, +at: Word(p), +wt: Word(p), +h: S.Sub(1n+p, WCon{c, at}, Word.shr.pad(p, wt))) -> S.Sub(p, Word.shl.put(p, c, at), wt):
  match p:
    case 0n:
      match at wt:
        case WNil{} WNil{}:
          {==}
    case 1n+q:
      match at wt:
        case WCon{+a1, +ar} WCon{+w0, +wr}:
          cons.eq(q, Bool.and(c, w0), c, Word.and(q, Word.shl.put(q, a1, ar), wr), Word.shl.put(q, a1, ar),
            hd(1n+q, Bool.and(c, w0), c, Word.and(1n+q, WCon{a1, ar}, Word.shr.pad(q, wr)), WCon{a1, ar}, h),
            put_sub(q, a1, ar, wr, tl(1n+q, Bool.and(c, w0), c, Word.and(1n+q, WCon{a1, ar}, Word.shr.pad(q, wr)), WCon{a1, ar}, h)))


def Laws.shl_sub(n, a, w, h):
  match n:
    case 0n:
      match a w:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a w:
        case WCon{+a0, +at} WCon{+w0, +wt}:
          cons.eq(p, False{}, False{}, Word.and(p, Word.shl.put(p, a0, at), wt), Word.shl.put(p, a0, at), {==}, put_sub(p, a0, at, wt, h))


def u.unwrap(-x: Word(32n), -y: Word(32n), e: {U32{x} == U32{y} : U32}) -> {x == y : Word(32n)}:
  Equal.cong(U32, Word(32n), (u => S.u.word(u)), U32{x}, U32{y}, e)


def u.wrap(-x: Word(32n), -y: Word(32n), e: {x == y : Word(32n)}) -> {U32{x} == U32{y} : U32}:
  Equal.cong(Word(32n), U32, (v => U32{v}), x, y, e)


def Laws.shl_sub32(a, w, h):
  match a w:
    case U32{+x} U32{+y}:
      u.wrap(Word.and(32n, Word.shl(32n, x), y), Word.shl(32n, x), Laws.shl_sub(32n, x, y, u.unwrap(Word.and(32n, x, Word.shr(32n, y)), x, h)))


def Laws.shln_comm(a, k):
  match k:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(U32, U32.shln(U32.shl(a), j), U32.shl(U32.shln(a, j)), Laws.shln_comm(a, j)) : {U32.shl(_) == U32.shl(U32.shl(U32.shln(a, j))) : U32}
      {==}


def Laws.shln_sub(k, a, w, h):
  match k:
    case 0n:
      h
    case 1n+j:
      %Laws.shln_comm(a, j) : S.Sub32(_, w)
      Laws.shln_sub(j, U32.shl(a), w, Laws.shl_sub32(a, U32.shrn(w, j), h))


def Laws.shr_op(x):
  {==}


def bxor_sub(+w: Bool, +x: Bool, +m: Bool, h1: {Bool.and(w, m) == w : Bool}, h2: {Bool.and(x, w) == x : Bool}) -> {Bool.and(Bool.xor(w, x), m) == Bool.xor(w, x) : Bool}:
  match w x m:
    case False{} False{} _:
      {==}
    case False{} True{} _:
      Empty.absurd({Bool.and(True{}, m) == True{} : Bool}, no_ft(h2))
    case True{} _ False{}:
      Empty.absurd({Bool.and(Bool.xor(True{}, x), False{}) == Bool.xor(True{}, x) : Bool}, no_ft(h1))
    case True{} False{} True{}:
      {==}
    case True{} True{} True{}:
      {==}


def Laws.xor_sub(n, w, x, m, wm, xw):
  match n:
    case 0n:
      match w x m:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match w x m:
        case WCon{+w0, +wt} WCon{+x0, +xt} WCon{+m0, +mt}:
          cons.eq(p, Bool.and(Bool.xor(w0, x0), m0), Bool.xor(w0, x0), Word.and(p, Word.xor(p, wt, xt), mt), Word.xor(p, wt, xt),
            bxor_sub(w0, x0, m0, hd(p, Bool.and(w0, m0), w0, Word.and(p, wt, mt), wt, wm), hd(p, Bool.and(x0, w0), x0, Word.and(p, xt, wt), xt, xw)),
            Laws.xor_sub(p, wt, xt, mt, tl(p, Bool.and(w0, m0), w0, Word.and(p, wt, mt), wt, wm), tl(p, Bool.and(x0, w0), x0, Word.and(p, xt, wt), xt, xw)))


def band_mono(+a: Bool, +b: Bool, +k: Bool, h: {Bool.and(a, b) == a : Bool}) -> {Bool.and(Bool.and(a, k), Bool.and(b, k)) == Bool.and(a, k) : Bool}:
  match a b k:
    case False{} _ _:
      {==}
    case True{} False{} _:
      Empty.absurd({Bool.and(Bool.and(True{}, k), Bool.and(False{}, k)) == Bool.and(True{}, k) : Bool}, no_ft(h))
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}


def Laws.and_mono(n, a, b, k, h):
  match n:
    case 0n:
      match a b k:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b k:
        case WCon{+a0, +at} WCon{+b0, +bt} WCon{+k0, +kt}:
          cons.eq(p, Bool.and(Bool.and(a0, k0), Bool.and(b0, k0)), Bool.and(a0, k0), Word.and(p, Word.and(p, at, kt), Word.and(p, bt, kt)), Word.and(p, at, kt),
            band_mono(a0, b0, k0, hd(p, Bool.and(a0, b0), a0, Word.and(p, at, bt), at, h)),
            Laws.and_mono(p, at, bt, kt, tl(p, Bool.and(a0, b0), a0, Word.and(p, at, bt), at, h)))


def Laws.pad_mono(p, a, b, h):
  match p:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+q:
      match a b:
        case WCon{+a0, +at} WCon{+b0, +bt}:
          cons.eq(1n+q, Bool.and(a0, b0), a0, Word.and(1n+q, Word.shr.pad(q, at), Word.shr.pad(q, bt)), Word.shr.pad(q, at),
            hd(q, Bool.and(a0, b0), a0, Word.and(q, at, bt), at, h),
            Laws.pad_mono(q, at, bt, tl(q, Bool.and(a0, b0), a0, Word.and(q, at, bt), at, h)))


def Laws.shr_mono(n, a, b, h):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+a0, +at} WCon{+b0, +bt}:
          Laws.pad_mono(p, at, bt, tl(p, Bool.and(a0, b0), a0, Word.and(p, at, bt), at, h))


def shrn_mono.one(+a: U32, +b: U32, +h: S.Sub32(a, b)) -> S.Sub32(U32.shr(a), U32.shr(b)):
  match a b:
    case U32{+x} U32{+y}:
      u.wrap(Word.and(32n, Word.shr(32n, x), Word.shr(32n, y)), Word.shr(32n, x), Laws.shr_mono(32n, x, y, u.unwrap(Word.and(32n, x, y), x, h)))


def Laws.shrn_mono(k, a, b, h):
  match k:
    case 0n:
      h
    case 1n+j:
      shrn_mono.one(U32.shrn(a, j), U32.shrn(b, j), Laws.shrn_mono(j, a, b, h))


def Laws.and_mono32(a, b, k, h):
  match a b k:
    case U32{+x} U32{+y} U32{+z}:
      u.wrap(Word.and(32n, Word.and(32n, x, z), Word.and(32n, y, z)), Word.and(32n, x, z), Laws.and_mono(32n, x, y, z, u.unwrap(Word.and(32n, x, y), x, h)))


def Laws.hi_holding(w, h):
  Laws.shrn_mono(16n, w, S.valid.mask(), h)


def Laws.lo_holding(w, h):
  Laws.and_mono32(w, S.valid.mask(), 65535, h)


def band_t(+b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}


def Laws.pad_ones(p, x, j):
  match p:
    case 0n:
      match x j:
        case WNil{} 0n:
          {==}
        case WNil{} 1n+i:
          {==}
    case 1n+q:
      match x j:
        case WCon{+b, +r} 0n:
          cons.eq(1n+q, Bool.and(b, False{}), Bool.and(b, False{}), Word.and(1n+q, Word.shr.pad(q, r), S.ones(1n+q, 0n)), Word.shr.pad(q, Word.and(q, r, S.ones(q, 0n))), {==}, Laws.pad_ones(q, r, 0n))
        case WCon{+b, +r} 1n+i:
          cons.eq(1n+q, Bool.and(b, True{}), Bool.and(b, True{}), Word.and(1n+q, Word.shr.pad(q, r), S.ones(1n+q, i)), Word.shr.pad(q, Word.and(q, r, S.ones(q, i))), {==}, Laws.pad_ones(q, r, i))


def Laws.pad_inj(p, x, y, e):
  match p:
    case 0n:
      match x y:
        case WNil{} WNil{}:
          {==}
    case 1n+q:
      match x y:
        case WCon{+a, +r} WCon{+b, +t}:
          cons.eq(q, a, b, r, t, hd(1n+q, a, b, Word.shr.pad(q, r), Word.shr.pad(q, t), e), Laws.pad_inj(q, r, t, tl(1n+q, a, b, Word.shr.pad(q, r), Word.shr.pad(q, t), e)))


def Laws.shr_ones(n, w, j, h):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+w0, +wt}:
          cons.eq(p, Bool.and(w0, True{}), w0, Word.and(p, wt, S.ones(p, j)), wt, band_t(w0), Laws.pad_inj(p, Word.and(p, wt, S.ones(p, j)), wt,
            Equal.trans(Word(1n+p), Word.shr.pad(p, Word.and(p, wt, S.ones(p, j))), Word.and(1n+p, Word.shr.pad(p, wt), S.ones(1n+p, j)), Word.shr.pad(p, wt),
              Equal.sym(Word(1n+p), Word.and(1n+p, Word.shr.pad(p, wt), S.ones(1n+p, j)), Word.shr.pad(p, Word.and(p, wt, S.ones(p, j))), Laws.pad_ones(p, wt, j)), h)))


def zero_and(+n: Nat, +k: Word(n)) -> {Word.and(n, Word.zero(n), k) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match k:
        case WNil{}:
          {==}
    case 1n+p:
      match k:
        case WCon{+k0, +kt}:
          cons.eq(p, False{}, False{}, Word.and(p, Word.zero(p), kt), Word.zero(p), {==}, zero_and(p, kt))


def Laws.zero_ones(n, w, z):
  %Equal.sym(Word(n), w, Word.zero(n), z) : S.Sub(n, _, S.ones(n, 0n))
  zero_and(n, S.ones(n, 0n))


def Laws.shrn_comm(a, k):
  match k:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(U32, U32.shrn(U32.shr(a), j), U32.shr(U32.shrn(a, j)), Laws.shrn_comm(a, j)) : {U32.shr(_) == U32.shr(U32.shr(U32.shrn(a, j))) : U32}
      {==}


def shr_ones32(+w: U32, +j: Nat, +h: S.Sub32.ones(U32.shr(w), j)) -> S.Sub32.ones(w, 1n+j):
  match w:
    case U32{+x}:
      Laws.shr_ones(32n, x, j, h)


# If w shifted down k times is zero, w is under its first k bits.
def shrn_zero.step(+w: U32, +j: Nat, +z: {U32.shr(U32.shrn(w, j)) == 0 : U32}) -> {U32.shrn(U32.shr(w), j) == 0 : U32}:
  %Equal.sym(U32, U32.shrn(U32.shr(w), j), U32.shr(U32.shrn(w, j)), Laws.shrn_comm(w, j)) : {_ == 0 : U32}
  z


def Laws.shrn_zero(k, w, z):
  match k:
    case 0n:
      match w:
        case U32{+x}:
          Laws.zero_ones(32n, x, u.unwrap(x, Word.zero(32n), z))
    case 1n+j:
      shr_ones32(w, j, Laws.shrn_zero(j, U32.shr(w), shrn_zero.step(w, j, z)))


def Laws.split_zero(w, z1, z2):
  match w:
    case U32{+x}:
      u.wrap(x, Word.zero(32n), Equal.trans(Word(32n), x, Word.and(32n, x, S.ones(32n, 16n)), Word.zero(32n),
        Equal.sym(Word(32n), Word.and(32n, x, S.ones(32n, 16n)), x, Laws.shrn_zero(16n, U32{x}, z1)),
        u.unwrap(Word.and(32n, x, S.ones(32n, 16n)), Word.zero(32n), z2)))


def cmp.fin.eq(+t: Cmp, +ab: Bool, +bb: Bool, e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}) -> {t == EQ{} : Cmp} & {ab == bb : Bool}:
  match t ab bb:
    case LT{} _ _:
      Empty.absurd({LT{} == EQ{} : Cmp} & {ab == bb : Bool}, no_lt(e))
    case GT{} _ _:
      Empty.absurd({GT{} == EQ{} : Cmp} & {ab == bb : Bool}, no_gt(e))
    case EQ{} False{} False{}:
      ({==}, {==})
    case EQ{} True{} True{}:
      ({==}, {==})
    case EQ{} False{} True{}:
      Empty.absurd({EQ{} == EQ{} : Cmp} & {False{} == True{} : Bool}, no_lt(e))
    case EQ{} True{} False{}:
      Empty.absurd({EQ{} == EQ{} : Cmp} & {True{} == False{} : Bool}, no_gt(e))


def fin.fst(-t: Cmp, -x: Bool, -y: Bool, r: {t == EQ{} : Cmp} & {x == y : Bool}) -> {t == EQ{} : Cmp}:
  (c, h) = r
  c


def fin.snd(-t: Cmp, -x: Bool, -y: Bool, r: {t == EQ{} : Cmp} & {x == y : Bool}) -> {x == y : Bool}:
  (c, h) = r
  h


def Laws.cmp_eq(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          cons.eq(p, x, y, at, bt, fin.snd(Word.cmp(p, at, bt), x, y, cmp.fin.eq(Word.cmp(p, at, bt), x, y, e)), Laws.cmp_eq(p, at, bt, fin.fst(Word.cmp(p, at, bt), x, y, cmp.fin.eq(Word.cmp(p, at, bt), x, y, e))))


def is_eq.true(+c: Cmp, e: {Cmp.is_eq(c) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, no_ft(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, no_ft(e))


def Laws.u32_eq(a, b, e):
  match a b:
    case U32{+x} U32{+y}:
      u.wrap(x, y, Laws.cmp_eq(32n, x, y, is_eq.true(Word.cmp(32n, x, y), e)))


def Laws.and_sub32(a, k):
  match a k:
    case U32{+x} U32{+y}:
      u.wrap(Word.and(32n, Word.and(32n, x, y), x), Word.and(32n, x, y), Laws.and_sub_left(32n, x, y))


def Laws.sub_trans32(a, b, c, ab, bc):
  match a b c:
    case U32{+x} U32{+y} U32{+z}:
      u.wrap(Word.and(32n, x, z), x, Laws.sub_trans(32n, x, y, z, u.unwrap(Word.and(32n, x, y), x, ab), u.unwrap(Word.and(32n, y, z), y, bc)))


def Laws.count_xor32(x, w, s, one):
  match x w:
    case U32{+a} U32{+b}:
      Laws.count_xor(32n, a, b, u.unwrap(Word.and(32n, a, b), a, s), one)


def Laws.xor_sub32(w, x, m, wm, xw):
  match w x m:
    case U32{+a} U32{+b} U32{+c}:
      u.wrap(Word.and(32n, Word.xor(32n, a, b), c), Word.xor(32n, a, b), Laws.xor_sub(32n, a, b, c, u.unwrap(Word.and(32n, a, c), a, wm), u.unwrap(Word.and(32n, b, a), b, xw)))


# ---------------------------------------------------------------------------
# Moves

def tn(+r: Nat, lr: {Nat.is_lt(r, 13n) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(r)) == r : Nat}:
  match r:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n+x:
      Empty.absurd({U32.to_nat(U32.from_nat(13n+x)) == 13n+x : Nat}, no_lt0(x, lr))


def or_right(+x: Bool, -y: Bool, -w: Bool, e: {Bool.or(Bool.and(x, y), w) == True{} : Bool}, nx: {x == False{} : Bool}) -> {w == True{} : Bool}:
  match x:
    case False{}:
      e
    case True{}:
      Empty.absurd({w == True{} : Bool}, no_tf(nx))


def band_self(+b: Bool) -> {Bool.and(b, b) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}


def Laws.and_self(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          cons.eq(p, Bool.and(b, b), b, Word.and(p, t, t), t, band_self(b), Laws.and_self(p, t))


def sub_refl32(+m: U32) -> S.Sub32(m, m):
  match m:
    case U32{+x}:
      u.wrap(Word.and(32n, x, x), x, Laws.and_self(32n, x))


def not_t(+x: Bool, e: {x == False{} : Bool}) -> {Bool.not(x) == True{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, no_tf(e))


def f.p2(+m: U32, +fe: {S.facts(m) == True{} : Bool}) -> {Bool.and(S.fact.in(m), S.fact.next(m)) == True{} : Bool}:
  Sigma.snd.bool(S.fact.pop(m), Bool.and(S.fact.in(m), S.fact.next(m)), and_true(S.fact.pop(m), Bool.and(S.fact.in(m), S.fact.next(m)), fe))


def f.in(+m: U32, +fe: {S.facts(m) == True{} : Bool}) -> {S.fact.in(m) == True{} : Bool}:
  Sigma.fst.bool(S.fact.in(m), S.fact.next(m), and_true(S.fact.in(m), S.fact.next(m), f.p2(m, fe)))


def f.next(+m: U32, +fe: {S.facts(m) == True{} : Bool}) -> {S.fact.next(m) == True{} : Bool}:
  Sigma.snd.bool(S.fact.in(m), S.fact.next(m), and_true(S.fact.in(m), S.fact.next(m), f.p2(m, fe)))


def f.card(+m: U32, +fe: {S.facts(m) == True{} : Bool}, +nz: {U32.is_eq(m, 0) == False{} : Bool}) -> {S.fact.card(m) == True{} : Bool}:
  Sigma.snd.bool(Bool.not(U32.is_eq(m, 0)), S.fact.card(m), and_true(Bool.not(U32.is_eq(m, 0)), S.fact.card(m),
    or_right(U32.is_eq(m, 0), U32.is_eq(S.low(m), 0), Bool.and(Bool.not(U32.is_eq(m, 0)), S.fact.card(m)), f.next(m, fe), nz)))


def f.c1(+m: U32, +fe: {S.facts(m) == True{} : Bool}, +nz: {U32.is_eq(m, 0) == False{} : Bool}) -> {Bool.and(S.fact.bit(m), Bool.and(S.fact.cnt(m), S.fact.rest(m))) == True{} : Bool}:
  Sigma.snd.bool(S.fact.lt(m), Bool.and(S.fact.bit(m), Bool.and(S.fact.cnt(m), S.fact.rest(m))), and_true(S.fact.lt(m), Bool.and(S.fact.bit(m), Bool.and(S.fact.cnt(m), S.fact.rest(m))), f.card(m, fe, nz)))


def f.c2(+m: U32, +fe: {S.facts(m) == True{} : Bool}, +nz: {U32.is_eq(m, 0) == False{} : Bool}) -> {Bool.and(S.fact.cnt(m), S.fact.rest(m)) == True{} : Bool}:
  Sigma.snd.bool(S.fact.bit(m), Bool.and(S.fact.cnt(m), S.fact.rest(m)), and_true(S.fact.bit(m), Bool.and(S.fact.cnt(m), S.fact.rest(m)), f.c1(m, fe, nz)))


# What the facts about a non-empty holding give, one at a time.
def Laws.card_bit(s, r, ls, lr):
  match s:
    case 0n:
      match r:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n:
          {==}
        case 9n:
          {==}
        case 10n:
          {==}
        case 11n:
          {==}
        case 12n:
          {==}
        case 13n+x:
          Empty.absurd({S.cb.ok(0n, 13n+x) == True{} : Bool}, no_lt0(x, lr))
    case 1n:
      match r:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n:
          {==}
        case 9n:
          {==}
        case 10n:
          {==}
        case 11n:
          {==}
        case 12n:
          {==}
        case 13n+x:
          Empty.absurd({S.cb.ok(1n, 13n+x) == True{} : Bool}, no_lt0(x, lr))
    case 2n:
      match r:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n:
          {==}
        case 9n:
          {==}
        case 10n:
          {==}
        case 11n:
          {==}
        case 12n:
          {==}
        case 13n+x:
          Empty.absurd({S.cb.ok(2n, 13n+x) == True{} : Bool}, no_lt0(x, lr))
    case 3n:
      match r:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n:
          {==}
        case 9n:
          {==}
        case 10n:
          {==}
        case 11n:
          {==}
        case 12n:
          {==}
        case 13n+x:
          Empty.absurd({S.cb.ok(3n, 13n+x) == True{} : Bool}, no_lt0(x, lr))
    case 4n+y:
      Empty.absurd({S.cb.ok(4n+y, r) == True{} : Bool}, no_lt0(y, ls))


def Laws.one_bit(r, lr):
  match r:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n+x:
      Empty.absurd({S.one.ok(13n+x) == True{} : Bool}, no_lt0(x, lr))


def nat.eq(+a: Nat, +b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      Empty.absurd({0n == 1n+y : Nat}, no_ft(e))
    case 1n+x 0n:
      Empty.absurd({1n+x == 0n : Nat}, no_ft(e))
    case 1n+x 1n+y:
      %nat.eq(x, y, e) : {1n+x == 1n+_ : Nat}
      {==}


def card.suit.of(+s: Nat, +r: Nat, +ls: {Nat.is_lt(s, 4n) == True{} : Bool}, +lr: {Nat.is_lt(r, 13n) == True{} : Bool}) -> {C.card.suit(C.card.make(U32.from_nat(s), U32.from_nat(r))) == U32.from_nat(s) : U32}:
  Laws.u32_eq(C.card.suit(C.card.make(U32.from_nat(s), U32.from_nat(r))), U32.from_nat(s), Sigma.fst.bool(U32.is_eq(C.card.suit(C.card.make(U32.from_nat(s), U32.from_nat(r))), U32.from_nat(s)), U32.is_eq(C.card.bit(C.card.make(U32.from_nat(s), U32.from_nat(r))), (1 << r : U32)), and_true(U32.is_eq(C.card.suit(C.card.make(U32.from_nat(s), U32.from_nat(r))), U32.from_nat(s)), U32.is_eq(C.card.bit(C.card.make(U32.from_nat(s), U32.from_nat(r))), (1 << r : U32)), Laws.card_bit(s, r, ls, lr))))


def card.bit.of(+s: Nat, +r: Nat, +ls: {Nat.is_lt(s, 4n) == True{} : Bool}, +lr: {Nat.is_lt(r, 13n) == True{} : Bool}) -> {C.card.bit(C.card.make(U32.from_nat(s), U32.from_nat(r))) == (1 << r : U32) : U32}:
  Laws.u32_eq(C.card.bit(C.card.make(U32.from_nat(s), U32.from_nat(r))), (1 << r : U32), Sigma.snd.bool(U32.is_eq(C.card.suit(C.card.make(U32.from_nat(s), U32.from_nat(r))), U32.from_nat(s)), U32.is_eq(C.card.bit(C.card.make(U32.from_nat(s), U32.from_nat(r))), (1 << r : U32)), and_true(U32.is_eq(C.card.suit(C.card.make(U32.from_nat(s), U32.from_nat(r))), U32.from_nat(s)), U32.is_eq(C.card.bit(C.card.make(U32.from_nat(s), U32.from_nat(r))), (1 << r : U32)), Laws.card_bit(s, r, ls, lr))))


def card.one(+s: Nat, +r: Nat, +ls: {Nat.is_lt(s, 4n) == True{} : Bool}, +lr: {Nat.is_lt(r, 13n) == True{} : Bool}) -> {S.bits(C.card.bit(C.card.make(U32.from_nat(s), U32.from_nat(r)))) == 1n : Nat}:
  %Equal.sym(U32, C.card.bit(C.card.make(U32.from_nat(s), U32.from_nat(r))), (1 << r : U32), card.bit.of(s, r, ls, lr)) : {S.bits(_) == 1n : Nat}
  nat.eq(S.bits((1 << r : U32)), 1n, Laws.one_bit(r, lr))



# The lowest card of a holding, by induction on the bits of the word: x & -x
# is the word of its lowest bit, which is below the 13th in a holding.

def wc(-p: Nat, +b: Bool, -x: Word(p), -y: Word(p), e: {x == y : Word(p)}) -> {WCon{b, x} == WCon{b, y} : Word(1n+p)}:
  Equal.cong(Word(p), Word(1n+p), (v => WCon{b, v}), x, y, e)

# ---------------------------------------------------------------------------
# The lowest card of a holding, by induction on its bits

# The place of the lowest bit of a word, or its width when it has none.

def Laws.sub_not(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          match b:
            case False{}:
              wc(p, True{}, Word.adc(p, Word.zero(p), t, True{}, False{}), Word.not(p, t), Laws.sub_not(p, t))
            case True{}:
              wc(p, False{}, Word.adc(p, Word.zero(p), t, True{}, False{}), Word.not(p, t), Laws.sub_not(p, t))

def Laws.and_not(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          match b:
            case False{}:
              wc(p, False{}, Word.and(p, t, Word.not(p, t)), Word.zero(p), Laws.and_not(p, t))
            case True{}:
              wc(p, False{}, Word.and(p, t, Word.not(p, t)), Word.zero(p), Laws.and_not(p, t))

# A word and its negation share exactly its lowest bit.

def Laws.low_unit(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          match b:
            case False{}:
              wc(p, False{}, Word.and(p, t, Word.adc(p, Word.zero(p), t, True{}, True{})), S.unit(p, S.lsb(p, t)), Laws.low_unit(p, t))
            case True{}:
              wc(p, True{}, Word.and(p, t, Word.adc(p, Word.zero(p), t, True{}, False{})), Word.zero(p),
                Equal.trans(Word(p), Word.and(p, t, Word.adc(p, Word.zero(p), t, True{}, False{})), Word.and(p, t, Word.not(p, t)), Word.zero(p),
                  Equal.cong(Word(p), Word(p), (v => Word.and(p, t, v)), Word.adc(p, Word.zero(p), t, True{}, False{}), Word.not(p, t), Laws.sub_not(p, t)),
                  Laws.and_not(p, t)))

def lift0(+p: Nat, +t: Word(p), e: Either<&2, &2, {t == Word.zero(p) : Word(p)}, {Nat.is_lt(S.lsb(p, t), 0n) == True{} : Bool}>) -> Either<&2, &2, {WCon{False{}, t} == Word.zero(1n+p) : Word(1n+p)}, {Nat.is_lt(1n+S.lsb(p, t), 0n) == True{} : Bool}>:
  match e:
    case Inl{z}:
      Inl{wc(p, False{}, t, Word.zero(p), z)}
    case Inr{l}:
      Empty.absurd(Either<&2, &2, {WCon{False{}, t} == Word.zero(1n+p) : Word(1n+p)}, {Nat.is_lt(1n+S.lsb(p, t), 0n) == True{} : Bool}>, no_lt0(S.lsb(p, t), l))

def lift1(+p: Nat, +i: Nat, +t: Word(p), e: Either<&2, &2, {t == Word.zero(p) : Word(p)}, {Nat.is_lt(S.lsb(p, t), i) == True{} : Bool}>) -> Either<&2, &2, {WCon{False{}, t} == Word.zero(1n+p) : Word(1n+p)}, {Nat.is_lt(1n+S.lsb(p, t), 1n+i) == True{} : Bool}>:
  match e:
    case Inl{z}:
      Inl{wc(p, False{}, t, Word.zero(p), z)}
    case Inr{l}:
      Inr{l}

# A word within the low j bits is empty, or its lowest bit is below j.

def Laws.lsb_lt(n, j, w, h):
  match n:
    case 0n:
      match w:
        case WNil{}:
          Inl{{==}}
    case 1n+p:
      match j w:
        case 0n WCon{+b, +t}:
          match b:
            case True{}:
              Empty.absurd(Either<&2, &2, {WCon{True{}, t} == Word.zero(1n+p) : Word(1n+p)}, {Nat.is_lt(0n, 0n) == True{} : Bool}>, no_ft(hd(p, False{}, True{}, Word.and(p, t, S.ones(p, 0n)), t, h)))
            case False{}:
              lift0(p, t, Laws.lsb_lt(p, 0n, t, tl(p, False{}, False{}, Word.and(p, t, S.ones(p, 0n)), t, h)))
        case 1n+i WCon{+b, +t}:
          match b:
            case True{}:
              Inr{{==}}
            case False{}:
              lift1(p, i, t, Laws.lsb_lt(p, i, t, tl(p, False{}, False{}, Word.and(p, t, S.ones(p, i)), t, h)))

# For the 13 ranks: the word of bit j is 1 << j, and ctz finds j in it.

def Laws.unit_shl(j, lj):
  match j:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n+x:
      Empty.absurd({U32{S.unit(32n, 13n+x)} == (1 << 13n+x : U32) : U32}, no_lt0(x, lj))

def Laws.ctz_shl(j, lj):
  match j:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n+x:
      Empty.absurd({U32.ctz((1 << 13n+x : U32)) == 13n+x : Nat}, no_lt0(x, lj))

def low.in(+m: U32) -> S.Sub32(S.low(m), m):
  Laws.and_sub32(m, (0 - m : U32))

def rest.in(+m: U32) -> S.Sub32(S.rest(m), m):
  Laws.xor_sub32(m, S.low(m), m, sub_refl32(m), low.in(m))

def low.rest(+m: U32, +hm: S.Sub32(m, 8191)) -> S.Sub32(S.rest(m), 8191):
  Laws.sub_trans32(S.rest(m), m, 8191, rest.in(m), hm)

def low.shl(+w: Word(32n), +l: {Nat.is_lt(S.lsb(32n, w), 13n) == True{} : Bool}) -> {S.low(U32{w}) == (1 << S.lsb(32n, w) : U32) : U32}:
  Equal.trans(U32, S.low(U32{w}), U32{S.unit(32n, S.lsb(32n, w))}, (1 << S.lsb(32n, w) : U32), u.wrap(Word.and(32n, w, Word.adc(32n, Word.zero(32n), w, True{}, True{})), S.unit(32n, S.lsb(32n, w)), Laws.low_unit(32n, w)), Laws.unit_shl(S.lsb(32n, w), l))

def low.ctz(+w: Word(32n), +l: {Nat.is_lt(S.lsb(32n, w), 13n) == True{} : Bool}) -> {U32.ctz(S.low(U32{w})) == S.lsb(32n, w) : Nat}:
  Equal.trans(Nat, U32.ctz(S.low(U32{w})), U32.ctz((1 << S.lsb(32n, w) : U32)), S.lsb(32n, w), Equal.cong(U32, Nat, (u => U32.ctz(u)), S.low(U32{w}), (1 << S.lsb(32n, w) : U32), low.shl(w, l)), Laws.ctz_shl(S.lsb(32n, w), l))

def nz.absurd(+w: Word(32n), +z: {w == Word.zero(32n) : Word(32n)}, +nz: {U32.is_eq(U32{w}, 0) == False{} : Bool}) -> Empty:
  no_tf(Equal.trans(Bool, True{}, U32.is_eq(U32{w}, 0), False{}, Equal.sym(Bool, U32.is_eq(U32{w}, 0), True{}, Equal.cong(Word(32n), Bool, (v => U32.is_eq(U32{v}, 0)), w, Word.zero(32n), z)), nz))

def lsb.small(+w: Word(32n), +nz: {U32.is_eq(U32{w}, 0) == False{} : Bool}, e: Either<&2, &2, {w == Word.zero(32n) : Word(32n)}, {Nat.is_lt(S.lsb(32n, w), 13n) == True{} : Bool}>) -> {Nat.is_lt(S.lsb(32n, w), 13n) == True{} : Bool}:
  match e:
    case Inl{z}:
      Empty.absurd({Nat.is_lt(S.lsb(32n, w), 13n) == True{} : Bool}, nz.absurd(w, z, nz))
    case Inr{l}:
      l

# A holding that isn't empty has its lowest bit below the 13th.

def Laws.lsb_hold(w, hm, nz):
  lsb.small(w, nz, Laws.lsb_lt(32n, 13n, w, u.unwrap(Word.and(32n, w, S.ones(32n, 13n)), w, hm)))

def low.lt(+m: U32, +hm: S.Sub32(m, 8191), +nz: {U32.is_eq(m, 0) == False{} : Bool}) -> {Nat.is_lt(U32.ctz(S.low(m)), 13n) == True{} : Bool}:
  match m:
    case U32{+w}:
      %Equal.sym(Nat, U32.ctz(S.low(U32{w})), S.lsb(32n, w), low.ctz(w, Laws.lsb_hold(w, hm, nz))) : {Nat.is_lt(_, 13n) == True{} : Bool}
      Laws.lsb_hold(w, hm, nz)

def low.bit(+m: U32, +hm: S.Sub32(m, 8191), +nz: {U32.is_eq(m, 0) == False{} : Bool}) -> {(1 << U32.ctz(S.low(m)) : U32) == S.low(m) : U32}:
  match m:
    case U32{+w}:
      %Equal.sym(Nat, U32.ctz(S.low(U32{w})), S.lsb(32n, w), low.ctz(w, Laws.lsb_hold(w, hm, nz))) : {(1 << _ : U32) == S.low(U32{w}) : U32}
      Equal.sym(U32, S.low(U32{w}), (1 << S.lsb(32n, w) : U32), low.shl(w, Laws.lsb_hold(w, hm, nz)))


def low.card(+s: Nat, +m: U32, +ls: {Nat.is_lt(s, 4n) == True{} : Bool}, +hm: S.Sub32(m, 8191), +nz: {U32.is_eq(m, 0) == False{} : Bool}) -> S.Sub32(C.card.bit(C.card.make(U32.from_nat(s), U32.from_nat(U32.ctz(S.low(m))))), m):
  %Equal.sym(U32, C.card.bit(C.card.make(U32.from_nat(s), U32.from_nat(U32.ctz(S.low(m))))), (1 << U32.ctz(S.low(m)) : U32), card.bit.of(s, U32.ctz(S.low(m)), ls, low.lt(m, hm, nz))) : S.Sub32(_, m)
  %Equal.sym(U32, (1 << U32.ctz(S.low(m)) : U32), S.low(m), low.bit(m, hm, nz)) : S.Sub32(_, m)
  low.in(m)


def Laws.one_bit16(r, lr):
  match r:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n+x:
      Empty.absurd({S.one16.ok(13n+x) == True{} : Bool}, no_lt0(x, lr))

def x.one.go(+s: Nat, +r: Nat, +ls: {Nat.is_lt(s, 4n) == True{} : Bool}, +lr: {Nat.is_lt(r, 13n) == True{} : Bool}) -> {S.bits(R.sel(U32.is_zero((U32.from_nat(s) .&. 1 : U32)), ((1 << r : U32) << 16n : U32), (1 << r : U32))) == 1n : Nat}:
  match s:
    case 0n:
      nat.eq(S.bits(((1 << r : U32) << 16n : U32)), 1n, Laws.one_bit16(r, lr))
    case 1n:
      nat.eq(S.bits((1 << r : U32)), 1n, Laws.one_bit(r, lr))
    case 2n:
      nat.eq(S.bits(((1 << r : U32) << 16n : U32)), 1n, Laws.one_bit16(r, lr))
    case 3n:
      nat.eq(S.bits((1 << r : U32)), 1n, Laws.one_bit(r, lr))
    case 4n+y:
      Empty.absurd({S.bits(R.sel(U32.is_zero((U32.from_nat(4n+y) .&. 1 : U32)), ((1 << r : U32) << 16n : U32), (1 << r : U32))) == 1n : Nat}, no_lt0(y, ls))

# What playing a card takes from a hand is one bit.

def Laws.x_one(c, s, r, ls, lr, es, eb):
  %Equal.sym(U32, C.card.suit(c), U32.from_nat(s), es) : {S.bits(R.sel(U32.is_zero((_ .&. 1 : U32)), (C.card.bit(c) << 16n : U32), C.card.bit(c))) == 1n : Nat}
  %Equal.sym(U32, C.card.bit(c), (1 << r : U32), eb) : {S.bits(R.sel(U32.is_zero((U32.from_nat(s) .&. 1 : U32)), (_ << 16n : U32), _)) == 1n : Nat}
  x.one.go(s, r, ls, lr)

# ---------------------------------------------------------------------------
# Hands stay even

# Whether seat j has played to a trick of k cards, with seat s to play next: it
# is 1 to k seats back from s.

def Laws.peel_sound(n, z, s, m, acc, m0, ls, zf, hm, sm, ok):
  match n z:
    case 0n _:
      ok
    case 1n+p True{}:
      ok
    case 1n+p False{}:
      Laws.peel_sound(p, U32.is_zero(S.rest(m)), s, S.rest(m), C.card.make(U32.from_nat(s), U32.from_nat(U32.ctz(S.low(m)))) <> acc, m0, ls, {==},
        low.rest(m, hm),
        Laws.sub_trans32(S.rest(m), m, m0, rest.in(m), sm),
        ((Laws.sub_trans32(C.card.bit(C.card.make(U32.from_nat(s), U32.from_nat(U32.ctz(S.low(m))))), m, m0, low.card(s, m, ls, hm, Equal.sym(Bool, False{}, U32.is_eq(m, 0), zf)), sm),
          card.suit.of(s, U32.ctz(S.low(m)), ls, low.lt(m, hm, Equal.sym(Bool, False{}, U32.is_eq(m, 0), zf)))), ok))



def zero_sub32(+h: U32) -> S.Sub32(0, h):
  match h:
    case U32{+x}:
      u.wrap(Word.and(32n, Word.zero(32n), x), Word.zero(32n), zero_and(32n, x))


def ic.sub(-c: U32, -suit: U32, -m0: U32, i: S.InCard(c, suit, m0)) -> S.Sub32(C.card.bit(c), m0):
  (a, b) = i
  a


def ic.suit(-c: U32, -suit: U32, -m0: U32, i: S.InCard(c, suit, m0)) -> {C.card.suit(c) == suit : U32}:
  (a, b) = i
  b


def hi.in(+m: U32, +h: U32, +i: S.Sub32(m, (h >> 16n : U32))) -> S.Sub32((m << 16n : U32), h):
  Laws.shln_sub(16n, m, h, i)


def lo.in(+m: U32, +h: U32, +i: S.Sub32(m, (h .&. 65535 : U32))) -> S.Sub32(m, h):
  Laws.sub_trans32(m, (h .&. 65535 : U32), h, i, Laws.and_sub32(h, 65535))


def Laws.card_shape(s, r, ls, lr):
  match s r:
    case 0n 0n:
      {==}
    case 0n 1n:
      {==}
    case 0n 2n:
      {==}
    case 0n 3n:
      {==}
    case 0n 4n:
      {==}
    case 0n 5n:
      {==}
    case 0n 6n:
      {==}
    case 0n 7n:
      {==}
    case 0n 8n:
      {==}
    case 0n 9n:
      {==}
    case 0n 10n:
      {==}
    case 0n 11n:
      {==}
    case 0n 12n:
      {==}
    case 0n 13n+y:
      Empty.absurd({S.card.shape(C.card.make(U32.from_nat(0n), U32.from_nat(13n+y))) == True{} : Bool}, no_lt0(y, lr))
    case 1n 0n:
      {==}
    case 1n 1n:
      {==}
    case 1n 2n:
      {==}
    case 1n 3n:
      {==}
    case 1n 4n:
      {==}
    case 1n 5n:
      {==}
    case 1n 6n:
      {==}
    case 1n 7n:
      {==}
    case 1n 8n:
      {==}
    case 1n 9n:
      {==}
    case 1n 10n:
      {==}
    case 1n 11n:
      {==}
    case 1n 12n:
      {==}
    case 1n 13n+y:
      Empty.absurd({S.card.shape(C.card.make(U32.from_nat(1n), U32.from_nat(13n+y))) == True{} : Bool}, no_lt0(y, lr))
    case 2n 0n:
      {==}
    case 2n 1n:
      {==}
    case 2n 2n:
      {==}
    case 2n 3n:
      {==}
    case 2n 4n:
      {==}
    case 2n 5n:
      {==}
    case 2n 6n:
      {==}
    case 2n 7n:
      {==}
    case 2n 8n:
      {==}
    case 2n 9n:
      {==}
    case 2n 10n:
      {==}
    case 2n 11n:
      {==}
    case 2n 12n:
      {==}
    case 2n 13n+y:
      Empty.absurd({S.card.shape(C.card.make(U32.from_nat(2n), U32.from_nat(13n+y))) == True{} : Bool}, no_lt0(y, lr))
    case 3n 0n:
      {==}
    case 3n 1n:
      {==}
    case 3n 2n:
      {==}
    case 3n 3n:
      {==}
    case 3n 4n:
      {==}
    case 3n 5n:
      {==}
    case 3n 6n:
      {==}
    case 3n 7n:
      {==}
    case 3n 8n:
      {==}
    case 3n 9n:
      {==}
    case 3n 10n:
      {==}
    case 3n 11n:
      {==}
    case 3n 12n:
      {==}
    case 3n 13n+y:
      Empty.absurd({S.card.shape(C.card.make(U32.from_nat(3n), U32.from_nat(13n+y))) == True{} : Bool}, no_lt0(y, lr))
    case 4n+y _:
      Empty.absurd({S.card.shape(C.card.make(U32.from_nat(4n+y), U32.from_nat(r))) == True{} : Bool}, no_lt0(y, ls))


def to.hand.go(+s: Nat, +c: U32, +h01: U32, +h23: U32, +ls: {Nat.is_lt(s, 4n) == True{} : Bool}, +i: S.Sub32(C.card.bit(c), R.suit.mask(s, h01, h23)), +one: {S.bits(S.play.x(c)) == 1n : Nat}, +ok: {S.card.shape(c) == True{} : Bool}) -> S.And(S.Sub32(R.sel(U32.is_lt(U32.from_nat(s), 2), R.sel(U32.is_zero((U32.from_nat(s) .&. 1 : U32)), (C.card.bit(c) << 16n : U32), C.card.bit(c)), 0), h01), S.And(S.Sub32(R.sel(U32.is_lt(U32.from_nat(s), 2), 0, R.sel(U32.is_zero((U32.from_nat(s) .&. 1 : U32)), (C.card.bit(c) << 16n : U32), C.card.bit(c))), h23), S.And({S.bits(S.play.x(c)) == 1n : Nat}, {S.card.shape(c) == True{} : Bool}))):
  match s:
    case 0n:
      (hi.in(C.card.bit(c), h01, i), (zero_sub32(h23), (one, ok)))
    case 1n:
      (lo.in(C.card.bit(c), h01, i), (zero_sub32(h23), (one, ok)))
    case 2n:
      (zero_sub32(h01), (hi.in(C.card.bit(c), h23, i), (one, ok)))
    case 3n:
      (zero_sub32(h01), (lo.in(C.card.bit(c), h23, i), (one, ok)))
    case 4n+y:
      Empty.absurd(S.And(S.Sub32(R.sel(U32.is_lt(U32.from_nat(4n+y), 2), R.sel(U32.is_zero((U32.from_nat(4n+y) .&. 1 : U32)), (C.card.bit(c) << 16n : U32), C.card.bit(c)), 0), h01), S.And(S.Sub32(R.sel(U32.is_lt(U32.from_nat(4n+y), 2), 0, R.sel(U32.is_zero((U32.from_nat(4n+y) .&. 1 : U32)), (C.card.bit(c) << 16n : U32), C.card.bit(c))), h23), S.And({S.bits(S.play.x(c)) == 1n : Nat}, {S.card.shape(c) == True{} : Bool}))), no_lt0(y, ls))


# A card of suit s in that suit's holding of a hand is in the hand.
def to.hand(+s: Nat, +c: U32, +h01: U32, +h23: U32, +ls: {Nat.is_lt(s, 4n) == True{} : Bool}, +isub: S.Sub32(C.card.bit(c), R.suit.mask(s, h01, h23)), +isuit: {C.card.suit(c) == U32.from_nat(s) : U32}, +one: {S.bits(S.play.x(c)) == 1n : Nat}, +ok: {S.card.shape(c) == True{} : Bool}) -> S.InHand(c, h01, h23):
  %Equal.sym(U32, C.card.suit(c), U32.from_nat(s), isuit) : S.And(S.Sub32(R.sel(U32.is_lt(_, 2), R.sel(U32.is_zero((_ .&. 1 : U32)), (C.card.bit(c) << 16n : U32), C.card.bit(c)), 0), h01), S.And(S.Sub32(R.sel(U32.is_lt(_, 2), 0, R.sel(U32.is_zero((_ .&. 1 : U32)), (C.card.bit(c) << 16n : U32), C.card.bit(c))), h23), S.And({S.bits(S.play.x(c)) == 1n : Nat}, {S.card.shape(c) == True{} : Bool})))
  to.hand.go(s, c, h01, h23, ls, isub, one, ok)



def Laws.peel_hand(n, z, s, m, acc, h01, h23, ls, zf, hm, sm, ok):
  match n z:
    case 0n _:
      ok
    case 1n+p True{}:
      ok
    case 1n+p False{}:
      Laws.peel_hand(p, U32.is_zero(S.rest(m)), s, S.rest(m), C.card.make(U32.from_nat(s), U32.from_nat(U32.ctz(S.low(m)))) <> acc, h01, h23, ls, {==},
        low.rest(m, hm),
        Laws.sub_trans32(S.rest(m), m, R.suit.mask(s, h01, h23), rest.in(m), sm),
        (to.hand(s, C.card.make(U32.from_nat(s), U32.from_nat(U32.ctz(S.low(m)))), h01, h23, ls,
           Laws.sub_trans32(C.card.bit(C.card.make(U32.from_nat(s), U32.from_nat(U32.ctz(S.low(m))))), m, R.suit.mask(s, h01, h23), low.card(s, m, ls, hm, Equal.sym(Bool, False{}, U32.is_eq(m, 0), zf)), sm),
           card.suit.of(s, U32.ctz(S.low(m)), ls, low.lt(m, hm, Equal.sym(Bool, False{}, U32.is_eq(m, 0), zf))),
           Laws.x_one(C.card.make(U32.from_nat(s), U32.from_nat(U32.ctz(S.low(m)))), s, U32.ctz(S.low(m)), ls, low.lt(m, hm, Equal.sym(Bool, False{}, U32.is_eq(m, 0), zf)),
             card.suit.of(s, U32.ctz(S.low(m)), ls, low.lt(m, hm, Equal.sym(Bool, False{}, U32.is_eq(m, 0), zf))),
             card.bit.of(s, U32.ctz(S.low(m)), ls, low.lt(m, hm, Equal.sym(Bool, False{}, U32.is_eq(m, 0), zf)))),
           Laws.card_shape(s, U32.ctz(S.low(m)), ls, low.lt(m, hm, Equal.sym(Bool, False{}, U32.is_eq(m, 0), zf)))), ok))


def suit.hand(+s: Nat, +acc: List<&2, U32>, +h01: U32, +h23: U32, +ls: {Nat.is_lt(s, 4n) == True{} : Bool}, +hm: S.Sub32(R.suit.mask(s, h01, h23), 8191), ok: S.AllH(acc, h01, h23)) -> S.AllH(R.moves.suit(U32.from_nat(s), R.suit.mask(s, h01, h23), acc), h01, h23):
  Laws.peel_hand(13n, U32.is_zero(R.suit.mask(s, h01, h23)), s, R.suit.mask(s, h01, h23), acc, h01, h23, ls, {==}, hm, sub_refl32(R.suit.mask(s, h01, h23)), ok)


def Laws.all_hand(h01, h23, v01, v23):
  suit.hand(0n, R.moves.suit(1, (h01 .&. 65535 : U32), R.moves.suit(2, (h23 >> 16n : U32), R.moves.suit(3, (h23 .&. 65535 : U32), Nil{}))), h01, h23, {==}, Laws.hi_holding(h01, v01),
    suit.hand(1n, R.moves.suit(2, (h23 >> 16n : U32), R.moves.suit(3, (h23 .&. 65535 : U32), Nil{})), h01, h23, {==}, Laws.lo_holding(h01, v01),
      suit.hand(2n, R.moves.suit(3, (h23 .&. 65535 : U32), Nil{}), h01, h23, {==}, Laws.hi_holding(h23, v23),
        suit.hand(3n, Nil{}, h01, h23, {==}, Laws.lo_holding(h23, v23), Unit{}))))



def pick.suit(+k: Nat, +h01: U32, +h23: U32, +v01: S.Sub32(h01, S.valid.mask()), +v23: S.Sub32(h23, S.valid.mask()), +eb: {U32.is_zero(R.suit.mask(k, h01, h23)) == False{} : Bool}) -> S.AllH(R.moves.suit(U32.from_nat(k), R.suit.mask(k, h01, h23), Nil{}), h01, h23):
  match k:
    case 0n:
      suit.hand(0n, Nil{}, h01, h23, {==}, Laws.hi_holding(h01, v01), Unit{})
    case 1n:
      suit.hand(1n, Nil{}, h01, h23, {==}, Laws.lo_holding(h01, v01), Unit{})
    case 2n:
      suit.hand(2n, Nil{}, h01, h23, {==}, Laws.hi_holding(h23, v23), Unit{})
    case 3n:
      suit.hand(3n, Nil{}, h01, h23, {==}, Laws.lo_holding(h23, v23), Unit{})
    case 4n+y:
      Empty.absurd(S.AllH(R.moves.suit(U32.from_nat(4n+y), 0, Nil{}), h01, h23), no_tf(eb))


def pick.go(+k: Nat, +b: Bool, +lead: U32, +h01: U32, +h23: U32, +v01: S.Sub32(h01, S.valid.mask()), +v23: S.Sub32(h23, S.valid.mask()), +eb: {U32.is_zero(R.suit.mask(k, h01, h23)) == b : Bool}, +el: {lead == U32.from_nat(k) : U32}) -> S.AllH(R.moves.pick(b, lead, R.suit.mask(k, h01, h23), h01, h23), h01, h23):
  match b:
    case True{}:
      Laws.all_hand(h01, h23, v01, v23)
    case False{}:
      %Equal.sym(U32, lead, U32.from_nat(k), el) : S.AllH(R.moves.suit(_, R.suit.mask(k, h01, h23), Nil{}), h01, h23)
      pick.suit(k, h01, h23, v01, v23, eb)


def lead.is(+lead: U32, +k: Nat, +e: {U32.to_nat(lead) == k : Nat}) -> {lead == U32.from_nat(k) : U32}:
  %e : {lead == U32.from_nat(_) : U32}
  Equal.sym(U32, U32.from_nat(U32.to_nat(lead)), lead, Laws.u32_roundtrip(lead))


def of.go(+k: Nat, +lead: U32, +h01: U32, +h23: U32, +v01: S.Sub32(h01, S.valid.mask()), +v23: S.Sub32(h23, S.valid.mask()), +e: {U32.to_nat(lead) == k : Nat}) -> S.AllH(R.moves.pick(U32.is_zero(R.suit.mask(U32.to_nat(lead), h01, h23)), lead, R.suit.mask(U32.to_nat(lead), h01, h23), h01, h23), h01, h23):
  %Equal.sym(Nat, U32.to_nat(lead), k, e) : S.AllH(R.moves.pick(U32.is_zero(R.suit.mask(_, h01, h23)), lead, R.suit.mask(_, h01, h23), h01, h23), h01, h23)
  pick.go(k, U32.is_zero(R.suit.mask(k, h01, h23)), lead, h01, h23, v01, v23, {==}, lead.is(lead, k, e))


def Laws.moves_hand(lead, h01, h23, v01, v23):
  of.go(U32.to_nat(lead), lead, h01, h23, v01, v23, {==})



def Laws.peel_ne_acc(n, z, s, m, acc, ne):
  match n z:
    case 0n _:
      ne
    case 1n+p True{}:
      ne
    case 1n+p False{}:
      Laws.peel_ne_acc(p, U32.is_zero(S.rest(m)), s, S.rest(m), C.card.make(s, U32.from_nat(U32.ctz(S.low(m)))) <> acc, Unit{})


def suit.ne.go(+b: Bool, +s: U32, +m: U32, acc: List<&2, U32>, +e: {b == False{} : Bool}) -> S.NE(R.moves.peel(13n, b, s, m, acc)):
  match b:
    case False{}:
      Laws.peel_ne_acc(12n, U32.is_zero(S.rest(m)), s, S.rest(m), C.card.make(s, U32.from_nat(U32.ctz(S.low(m)))) <> acc, Unit{})
    case True{}:
      Empty.absurd(S.NE(R.moves.peel(13n, True{}, s, m, acc)), no_tf(e))


def Laws.suit_ne(s, m, acc, e):
  suit.ne.go(U32.is_zero(m), s, m, acc, e)


def suit.ne.acc(+s: U32, +m: U32, acc: List<&2, U32>, ne: S.NE(acc)) -> S.NE(R.moves.suit(s, m, acc)):
  Laws.peel_ne_acc(13n, U32.is_zero(m), s, m, acc, ne)


def zero.of(+x: U32, +e: {U32.is_zero(x) == True{} : Bool}) -> {x == 0 : U32}:
  Laws.u32_eq(x, 0, e)


def word.zero(+h: U32, +a: {U32.is_zero((h >> 16n : U32)) == True{} : Bool}, +b: {U32.is_zero((h .&. 65535 : U32)) == True{} : Bool}) -> {h == 0 : U32}:
  Laws.split_zero(h, zero.of((h >> 16n : U32), a), zero.of((h .&. 65535 : U32), b))


def nonzero.rw(+h: U32, +z: {h == 0 : U32}) -> {True{} == U32.is_zero(h) : Bool}:
  %Equal.sym(U32, h, 0, z) : {True{} == U32.is_zero(_) : Bool}
  {==}


def nonzero.absurd(+h: U32, +z: {h == 0 : U32}, +e: {U32.is_zero(h) == False{} : Bool}) -> Empty:
  no_tf(Equal.trans(Bool, True{}, U32.is_zero(h), False{}, nonzero.rw(h, z), e))


def pick.ne(+b: Bool, +lead: U32, +f: U32, +h01: U32, +h23: U32, +eb: {U32.is_zero(f) == b : Bool}, all: S.NE(R.moves.all(h01, h23))) -> S.NE(R.moves.pick(b, lead, f, h01, h23)):
  match b:
    case True{}:
      all
    case False{}:
      Laws.suit_ne(lead, f, Nil{}, eb)


def of.ne(+lead: U32, +h01: U32, +h23: U32, all: S.NE(R.moves.all(h01, h23))) -> S.NE(R.moves.of(lead, h01, h23)):
  pick.ne(U32.is_zero(R.suit.mask(U32.to_nat(lead), h01, h23)), lead, R.suit.mask(U32.to_nat(lead), h01, h23), h01, h23, {==}, all)


def a01.go(+b0: Bool, +b1: Bool, +h01: U32, +h23: U32, +e0: {U32.is_zero((h01 >> 16n : U32)) == b0 : Bool}, +e1: {U32.is_zero((h01 .&. 65535 : U32)) == b1 : Bool}, +e: {U32.is_zero(h01) == False{} : Bool}) -> S.NE(R.moves.all(h01, h23)):
  match b0 b1:
    case False{} _:
      Laws.suit_ne(0, (h01 >> 16n : U32), R.moves.suit(1, (h01 .&. 65535 : U32), R.moves.suit(2, (h23 >> 16n : U32), R.moves.suit(3, (h23 .&. 65535 : U32), Nil{}))), e0)
    case True{} False{}:
      suit.ne.acc(0, (h01 >> 16n : U32), R.moves.suit(1, (h01 .&. 65535 : U32), R.moves.suit(2, (h23 >> 16n : U32), R.moves.suit(3, (h23 .&. 65535 : U32), Nil{}))),
        Laws.suit_ne(1, (h01 .&. 65535 : U32), R.moves.suit(2, (h23 >> 16n : U32), R.moves.suit(3, (h23 .&. 65535 : U32), Nil{})), e1))
    case True{} True{}:
      Empty.absurd(S.NE(R.moves.all(h01, h23)), nonzero.absurd(h01, word.zero(h01, e0, e1), e))


def a23.go(+b2: Bool, +b3: Bool, +h01: U32, +h23: U32, +e2: {U32.is_zero((h23 >> 16n : U32)) == b2 : Bool}, +e3: {U32.is_zero((h23 .&. 65535 : U32)) == b3 : Bool}, +e: {U32.is_zero(h23) == False{} : Bool}) -> S.NE(R.moves.all(h01, h23)):
  match b2 b3:
    case False{} _:
      suit.ne.acc(0, (h01 >> 16n : U32), R.moves.suit(1, (h01 .&. 65535 : U32), R.moves.suit(2, (h23 >> 16n : U32), R.moves.suit(3, (h23 .&. 65535 : U32), Nil{}))),
        suit.ne.acc(1, (h01 .&. 65535 : U32), R.moves.suit(2, (h23 >> 16n : U32), R.moves.suit(3, (h23 .&. 65535 : U32), Nil{})),
          Laws.suit_ne(2, (h23 >> 16n : U32), R.moves.suit(3, (h23 .&. 65535 : U32), Nil{}), e2)))
    case True{} False{}:
      suit.ne.acc(0, (h01 >> 16n : U32), R.moves.suit(1, (h01 .&. 65535 : U32), R.moves.suit(2, (h23 >> 16n : U32), R.moves.suit(3, (h23 .&. 65535 : U32), Nil{}))),
        suit.ne.acc(1, (h01 .&. 65535 : U32), R.moves.suit(2, (h23 >> 16n : U32), R.moves.suit(3, (h23 .&. 65535 : U32), Nil{})),
          suit.ne.acc(2, (h23 >> 16n : U32), R.moves.suit(3, (h23 .&. 65535 : U32), Nil{}),
            Laws.suit_ne(3, (h23 .&. 65535 : U32), Nil{}, e3))))
    case True{} True{}:
      Empty.absurd(S.NE(R.moves.all(h01, h23)), nonzero.absurd(h23, word.zero(h23, e2, e3), e))


def Laws.moves_ne01(lead, h01, h23, e):
  of.ne(lead, h01, h23, a01.go(U32.is_zero((h01 >> 16n : U32)), U32.is_zero((h01 .&. 65535 : U32)), h01, h23, {==}, {==}, e))


def Laws.moves_ne23(lead, h01, h23, e):
  of.ne(lead, h01, h23, a23.go(U32.is_zero((h23 >> 16n : U32)), U32.is_zero((h23 .&. 65535 : U32)), h01, h23, {==}, {==}, e))


# ---------------------------------------------------------------------------
# The trick word

def and.zero(+n: Nat, +w: Word(n)) -> {Word.and(n, w, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          match b:
            case False{}:
              %Equal.sym(Word(p), Word.and(p, t, Word.zero(p)), Word.zero(p), and.zero(p, t)) : {WCon{False{}, _} == Word.zero(1n+p) : Word(1n+p)}
              {==}
            case True{}:
              %Equal.sym(Word(p), Word.and(p, t, Word.zero(p)), Word.zero(p), and.zero(p, t)) : {WCon{False{}, _} == Word.zero(1n+p) : Word(1n+p)}
              {==}

def band.assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.and_assoc(n, a, b, c):
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{+a0, +at} WCon{+b0, +bt} WCon{+c0, +ct}:
          cons.eq(p, Bool.and(Bool.and(a0, b0), c0), Bool.and(a0, Bool.and(b0, c0)), Word.and(p, Word.and(p, at, bt), ct), Word.and(p, at, Word.and(p, bt, ct)), band.assoc(a0, b0, c0), Laws.and_assoc(p, at, bt, ct))

def Laws.and_assoc32(a, b, c):
  match a b c:
    case U32{+x} U32{+y} U32{+z}:
      u.wrap(Word.and(32n, Word.and(32n, x, y), z), Word.and(32n, x, Word.and(32n, y, z)), Laws.and_assoc(32n, x, y, z))

def Laws.pad_and(p, a, b):
  match p:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+q:
      match a b:
        case WCon{+a0, +at} WCon{+b0, +bt}:
          cons.eq(1n+q, Bool.and(a0, b0), Bool.and(a0, b0), Word.shr.pad(q, Word.and(q, at, bt)), Word.and(1n+q, Word.shr.pad(q, at), Word.shr.pad(q, bt)), {==}, Laws.pad_and(q, at, bt))

def Laws.shr_and(n, a, b):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+a0, +at} WCon{+b0, +bt}:
          Laws.pad_and(p, at, bt)

def shr_and32(+a: U32, +b: U32) -> {U32.shr(U32.and(a, b)) == U32.and(U32.shr(a), U32.shr(b)) : U32}:
  match a b:
    case U32{+x} U32{+y}:
      u.wrap(Word.shr(32n, Word.and(32n, x, y)), Word.and(32n, Word.shr(32n, x), Word.shr(32n, y)), Laws.shr_and(32n, x, y))

def Laws.shrn_and(k, a, b):
  match k:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(U32, U32.shrn(U32.and(a, b), j), U32.and(U32.shrn(a, j), U32.shrn(b, j)), Laws.shrn_and(j, a, b)) : {U32.shr(_) == U32.and(U32.shr(U32.shrn(a, j)), U32.shr(U32.shrn(b, j))) : U32}
      shr_and32(U32.shrn(a, j), U32.shrn(b, j))

# The seat and the cards played of a trick word are in its low 4 bits.

def Laws.seat_low(x):
  %Equal.sym(U32, U32.and(U32.and(x, 15), 3), U32.and(x, U32.and(15, 3)), Laws.and_assoc32(x, 15, 3)) : {R.trick.seat(x) == _ : U32}
  {==}

def Laws.played_low(x):
  %Equal.sym(U32, U32.shrn(U32.and(x, 15), 2n), U32.and(U32.shrn(x, 2n), U32.shrn(15, 2n)), Laws.shrn_and(2n, x, 15)) : {R.trick.played(x) == (_ .&. 3 : U32) : U32}
  %Equal.sym(U32, U32.and(U32.and(U32.shrn(x, 2n), U32.shrn(15, 2n)), 3), U32.and(U32.shrn(x, 2n), U32.and(U32.shrn(15, 2n), 3)), Laws.and_assoc32(U32.shrn(x, 2n), U32.shrn(15, 2n), 3)) : {R.trick.played(x) == _ : U32}
  {==}

def Laws.put_and(p, c, at, kt):
  match p:
    case 0n:
      match at kt:
        case WNil{} WNil{}:
          {==}
    case 1n+q:
      match q:
        case 0n:
          match at kt:
            case WCon{+a1, WNil{}} WCon{+k0, WNil{}}:
              {==}
        case 1n+r:
          match at kt:
            case WCon{+a1, +ar} WCon{+k0, WCon{+k1, +ks}}:
              cons.eq(1n+r, Bool.and(c, k0), Bool.and(c, k0), Word.and(1n+r, Word.shl.put(1n+r, a1, ar), WCon{k1, ks}), Word.shl.put(1n+r, Bool.and(a1, k1), Word.and(1n+r, ar, Word.shr.pad(r, ks))), {==}, Laws.put_and(1n+r, a1, ar, WCon{k1, ks}))

def Laws.shl_and(n, z, k):
  match n:
    case 0n:
      match z k:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match p:
        case 0n:
          match z k:
            case WCon{+z0, WNil{}} WCon{+k0, WNil{}}:
              {==}
        case 1n+q:
          match z k:
            case WCon{+z0, +zt} WCon{+k0, WCon{+k1, +kr}}:
              cons.eq(1n+q, False{}, False{}, Word.and(1n+q, Word.shl.put(1n+q, z0, zt), WCon{k1, kr}), Word.shl.put(1n+q, Bool.and(z0, k1), Word.and(1n+q, zt, Word.shr.pad(q, kr))), {==}, Laws.put_and(1n+q, z0, zt, WCon{k1, kr}))

def bor_and(+a: Bool, +b: Bool, +k: Bool) -> {Bool.and(Bool.or(a, b), k) == Bool.or(Bool.and(a, k), Bool.and(b, k)) : Bool}:
  match a b k:
    case False{} _ _:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} _ True{}:
      {==}

def Laws.or_and(n, a, b, k):
  match n:
    case 0n:
      match a b k:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b k:
        case WCon{+a0, +at} WCon{+b0, +bt} WCon{+k0, +kt}:
          cons.eq(p, Bool.and(Bool.or(a0, b0), k0), Bool.or(Bool.and(a0, k0), Bool.and(b0, k0)), Word.and(p, Word.or(p, at, bt), kt), Word.or(p, Word.and(p, at, kt), Word.and(p, bt, kt)), bor_and(a0, b0, k0), Laws.or_and(p, at, bt, kt))

def bor_f(+b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.or_zero(n, a):
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{+a0, +at}:
          cons.eq(p, Bool.or(a0, False{}), a0, Word.or(p, at, Word.zero(p)), at, bor_f(a0), Laws.or_zero(p, at))

def u32.or_and(+a: U32, +b: U32, +k: U32) -> {U32.and(U32.or(a, b), k) == U32.or(U32.and(a, k), U32.and(b, k)) : U32}:
  match a b k:
    case U32{+x} U32{+y} U32{+z}:
      u.wrap(Word.and(32n, Word.or(32n, x, y), z), Word.or(32n, Word.and(32n, x, z), Word.and(32n, y, z)), Laws.or_and(32n, x, y, z))

def u32.or_zero(+a: U32) -> {U32.or(a, 0) == a : U32}:
  match a:
    case U32{+x}:
      u.wrap(Word.or(32n, x, Word.zero(32n)), x, Laws.or_zero(32n, x))

def u32.and_zero(+a: U32) -> {U32.and(a, 0) == 0 : U32}:
  match a:
    case U32{+x}:
      u.wrap(Word.and(32n, x, Word.zero(32n)), Word.zero(32n), and.zero(32n, x))

def u32.shl_and(+z: U32, +k: U32) -> {U32.and(U32.shl(z), k) == U32.shl(U32.and(z, U32.shr(k))) : U32}:
  match z k:
    case U32{+x} U32{+y}:
      u.wrap(Word.and(32n, Word.shl(32n, x), y), Word.shl(32n, Word.and(32n, x, Word.shr(32n, y))), Laws.shl_and(32n, x, y))

# A word shifted up by 2 has nothing in its low 2 bits, and up by 4, in its low 4.

def Laws.shl2_low(z):
  %Equal.sym(U32, U32.and(U32.shl(U32.shl(z)), 3), U32.shl(U32.and(U32.shl(z), 1)), u32.shl_and(U32.shl(z), 3)) : {_ == 0 : U32}
  %Equal.sym(U32, U32.and(U32.shl(z), 1), U32.shl(U32.and(z, 0)), u32.shl_and(z, 1)) : {U32.shl(_) == 0 : U32}
  %Equal.sym(U32, U32.and(z, 0), 0, u32.and_zero(z)) : {U32.shl(U32.shl(_)) == 0 : U32}
  {==}

def Laws.shl4_low(z):
  %Equal.sym(U32, U32.and(U32.shl(U32.shl(U32.shl(U32.shl(z)))), 15), U32.shl(U32.and(U32.shl(U32.shl(U32.shl(z))), 7)), u32.shl_and(U32.shl(U32.shl(U32.shl(z))), 15)) : {_ == 0 : U32}
  %Equal.sym(U32, U32.and(U32.shl(U32.shl(U32.shl(z))), 7), U32.shl(U32.and(U32.shl(U32.shl(z)), 3)), u32.shl_and(U32.shl(U32.shl(z)), 7)) : {U32.shl(_) == 0 : U32}
  %Equal.sym(U32, U32.and(U32.shl(U32.shl(z)), 3), 0, Laws.shl2_low(z)) : {U32.shl(U32.shl(_)) == 0 : U32}
  {==}


# Or-ing in a field 4 bits up leaves the low 4 bits as they were.

def Laws.kill4(x, z):
  %Equal.sym(U32, U32.and(U32.or(x, U32.shl(U32.shl(U32.shl(U32.shl(z))))), 15), U32.or(U32.and(x, 15), U32.and(U32.shl(U32.shl(U32.shl(U32.shl(z)))), 15)), u32.or_and(x, U32.shl(U32.shl(U32.shl(U32.shl(z)))), 15)) : {_ == U32.and(x, 15) : U32}
  %Equal.sym(U32, U32.and(U32.shl(U32.shl(U32.shl(U32.shl(z)))), 15), 0, Laws.shl4_low(z)) : {U32.or(U32.and(x, 15), _) == U32.and(x, 15) : U32}
  u32.or_zero(U32.and(x, 15))

# The low 4 bits of a trick word are its seat and its cards played.

def Laws.low4_make(s, p, l, o, b):
  %Equal.sym(U32, U32.and(R.trick.make(s, p, l, o, b), 15), U32.and(U32.or(U32.or(U32.or(s, U32.shl(U32.shl(p))), (l << 4n : U32)), (o << 7n : U32)), 15), Laws.kill4(U32.or(U32.or(U32.or(s, U32.shl(U32.shl(p))), (l << 4n : U32)), (o << 7n : U32)), U32.shln(b, 5n))) : {_ == U32.and(U32.or(s, U32.shl(U32.shl(p))), 15) : U32}
  %Equal.sym(U32, U32.and(U32.or(U32.or(U32.or(s, U32.shl(U32.shl(p))), (l << 4n : U32)), (o << 7n : U32)), 15), U32.and(U32.or(U32.or(s, U32.shl(U32.shl(p))), (l << 4n : U32)), 15), Laws.kill4(U32.or(U32.or(s, U32.shl(U32.shl(p))), (l << 4n : U32)), U32.shln(o, 3n))) : {_ == U32.and(U32.or(s, U32.shl(U32.shl(p))), 15) : U32}
  Laws.kill4(U32.or(s, U32.shl(U32.shl(p))), l)

def pad_or(+p: Nat, +a: Word(p), +b: Word(p)) -> {Word.shr.pad(p, Word.or(p, a, b)) == Word.or(1n+p, Word.shr.pad(p, a), Word.shr.pad(p, b)) : Word(1n+p)}:
  match p:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+q:
      match a b:
        case WCon{+a0, +at} WCon{+b0, +bt}:
          cons.eq(1n+q, Bool.or(a0, b0), Bool.or(a0, b0), Word.shr.pad(q, Word.or(q, at, bt)), Word.or(1n+q, Word.shr.pad(q, at), Word.shr.pad(q, bt)), {==}, pad_or(q, at, bt))

def shr_or(+a: U32, +b: U32) -> {U32.shr(U32.or(a, b)) == U32.or(U32.shr(a), U32.shr(b)) : U32}:
  match a b:
    case U32{WCon{+a0, +at}} U32{WCon{+b0, +bt}}:
      u.wrap(Word.shr.pad(31n, Word.or(31n, at, bt)), Word.or(32n, Word.shr.pad(31n, at), Word.shr.pad(31n, bt)), pad_or(31n, at, bt))

def shr2_or(+a: U32, +b: U32) -> {U32.shr(U32.shr(U32.or(a, b))) == U32.or(U32.shr(U32.shr(a)), U32.shr(U32.shr(b))) : U32}:
  %Equal.sym(U32, U32.shr(U32.or(a, b)), U32.or(U32.shr(a), U32.shr(b)), shr_or(a, b)) : {U32.shr(_) == U32.or(U32.shr(U32.shr(a)), U32.shr(U32.shr(b))) : U32}
  shr_or(U32.shr(a), U32.shr(b))

# The seat of a trick word made with seat s is s's low 2 bits.

def tr(-a: U32, -b: U32, -c: U32, x: {a == b : U32}, y: {b == c : U32}) -> {a == c : U32}:
  Equal.trans(U32, a, b, c, x, y)

def Laws.seat_make(s, p, l, o, b):
  tr(R.trick.seat(R.trick.make(s, p, l, o, b)), R.trick.seat(U32.and(R.trick.make(s, p, l, o, b), 15)), U32.and(s, 3),
    Laws.seat_low(R.trick.make(s, p, l, o, b)),
    tr(R.trick.seat(U32.and(R.trick.make(s, p, l, o, b), 15)), R.trick.seat(U32.and(U32.or(s, U32.shl(U32.shl(p))), 15)), U32.and(s, 3),
      Equal.cong(U32, U32, (x => R.trick.seat(x)), U32.and(R.trick.make(s, p, l, o, b), 15), U32.and(U32.or(s, U32.shl(U32.shl(p))), 15), Laws.low4_make(s, p, l, o, b)),
      tr(R.trick.seat(U32.and(U32.or(s, U32.shl(U32.shl(p))), 15)), R.trick.seat(U32.or(s, U32.shl(U32.shl(p)))), U32.and(s, 3),
        Equal.sym(U32, R.trick.seat(U32.or(s, U32.shl(U32.shl(p)))), R.trick.seat(U32.and(U32.or(s, U32.shl(U32.shl(p))), 15)), Laws.seat_low(U32.or(s, U32.shl(U32.shl(p))))),
        tr(U32.and(U32.or(s, U32.shl(U32.shl(p))), 3), U32.or(U32.and(s, 3), U32.and(U32.shl(U32.shl(p)), 3)), U32.and(s, 3),
          u32.or_and(s, U32.shl(U32.shl(p)), 3),
          tr(U32.or(U32.and(s, 3), U32.and(U32.shl(U32.shl(p)), 3)), U32.or(U32.and(s, 3), 0), U32.and(s, 3),
            Equal.cong(U32, U32, (x => U32.or(U32.and(s, 3), x)), U32.and(U32.shl(U32.shl(p)), 3), 0, Laws.shl2_low(p)),
            u32.or_zero(U32.and(s, 3)))))))

def low2.gone(+y: U32) -> {U32.shrn(U32.and(y, 3), 2n) == 0 : U32}:
  tr(U32.shrn(U32.and(y, 3), 2n), U32.and(U32.shrn(y, 2n), U32.shrn(3, 2n)), 0, Laws.shrn_and(2n, y, 3), u32.and_zero(U32.shrn(y, 2n)))

def played.small(+k: Nat, +lk: {Nat.is_lt(k, 4n) == True{} : Bool}) -> {U32.or(0, U32.and(U32.shr(U32.shr(U32.shl(U32.shl(U32.from_nat(k))))), 3)) == U32.from_nat(k) : U32}:
  match k:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n+x:
      Empty.absurd({U32.or(0, U32.and(U32.shr(U32.shr(U32.shl(U32.shl(U32.from_nat(4n+x))))), 3)) == U32.from_nat(4n+x) : U32}, no_lt0(x, lk))

# The cards played of a trick word made with fewer than 4 played come back out,
# whatever its other fields, when its seat has only its low 2 bits.

def Laws.played_make(k, lk, y, l, o, b):
  tr(R.trick.played(R.trick.make(U32.and(y, 3), U32.from_nat(k), l, o, b)), R.trick.played(U32.and(R.trick.make(U32.and(y, 3), U32.from_nat(k), l, o, b), 15)), U32.from_nat(k),
    Laws.played_low(R.trick.make(U32.and(y, 3), U32.from_nat(k), l, o, b)),
    tr(R.trick.played(U32.and(R.trick.make(U32.and(y, 3), U32.from_nat(k), l, o, b), 15)), R.trick.played(U32.and(U32.or(U32.and(y, 3), U32.shl(U32.shl(U32.from_nat(k)))), 15)), U32.from_nat(k),
      Equal.cong(U32, U32, (x => R.trick.played(x)), U32.and(R.trick.make(U32.and(y, 3), U32.from_nat(k), l, o, b), 15), U32.and(U32.or(U32.and(y, 3), U32.shl(U32.shl(U32.from_nat(k)))), 15), Laws.low4_make(U32.and(y, 3), U32.from_nat(k), l, o, b)),
      tr(R.trick.played(U32.and(U32.or(U32.and(y, 3), U32.shl(U32.shl(U32.from_nat(k)))), 15)), R.trick.played(U32.or(U32.and(y, 3), U32.shl(U32.shl(U32.from_nat(k))))), U32.from_nat(k),
        Equal.sym(U32, R.trick.played(U32.or(U32.and(y, 3), U32.shl(U32.shl(U32.from_nat(k))))), R.trick.played(U32.and(U32.or(U32.and(y, 3), U32.shl(U32.shl(U32.from_nat(k)))), 15)), Laws.played_low(U32.or(U32.and(y, 3), U32.shl(U32.shl(U32.from_nat(k)))))),
        tr(U32.and(U32.shr(U32.shr(U32.or(U32.and(y, 3), U32.shl(U32.shl(U32.from_nat(k)))))), 3), U32.and(U32.or(U32.shr(U32.shr(U32.and(y, 3))), U32.shr(U32.shr(U32.shl(U32.shl(U32.from_nat(k)))))), 3), U32.from_nat(k),
          Equal.cong(U32, U32, (x => U32.and(x, 3)), U32.shr(U32.shr(U32.or(U32.and(y, 3), U32.shl(U32.shl(U32.from_nat(k)))))), U32.or(U32.shr(U32.shr(U32.and(y, 3))), U32.shr(U32.shr(U32.shl(U32.shl(U32.from_nat(k)))))), shr2_or(U32.and(y, 3), U32.shl(U32.shl(U32.from_nat(k))))),
          tr(U32.and(U32.or(U32.shr(U32.shr(U32.and(y, 3))), U32.shr(U32.shr(U32.shl(U32.shl(U32.from_nat(k)))))), 3), U32.or(U32.and(U32.shr(U32.shr(U32.and(y, 3))), 3), U32.and(U32.shr(U32.shr(U32.shl(U32.shl(U32.from_nat(k))))), 3)), U32.from_nat(k),
            u32.or_and(U32.shr(U32.shr(U32.and(y, 3))), U32.shr(U32.shr(U32.shl(U32.shl(U32.from_nat(k))))), 3),
            tr(U32.or(U32.and(U32.shr(U32.shr(U32.and(y, 3))), 3), U32.and(U32.shr(U32.shr(U32.shl(U32.shl(U32.from_nat(k))))), 3)), U32.or(U32.and(0, 3), U32.and(U32.shr(U32.shr(U32.shl(U32.shl(U32.from_nat(k))))), 3)), U32.from_nat(k),
              Equal.cong(U32, U32, (x => U32.or(U32.and(x, 3), U32.and(U32.shr(U32.shr(U32.shl(U32.shl(U32.from_nat(k))))), 3))), U32.shr(U32.shr(U32.and(y, 3))), 0, low2.gone(y)),
              played.small(k, lk)))))))

def low4.r(+m: U32, +r: U32) -> {U32.and(U32.or(m, (r << 15n : U32)), 15) == U32.and(m, 15) : U32}:
  Laws.kill4(m, U32.shln(r, 11n))

def Laws.seat_make_r(s, p, l, o, b, r):
  tr(R.trick.seat(U32.or(R.trick.make(s, p, l, o, b), (r << 15n : U32))), R.trick.seat(U32.and(U32.or(R.trick.make(s, p, l, o, b), (r << 15n : U32)), 15)), U32.and(s, 3),
    Laws.seat_low(U32.or(R.trick.make(s, p, l, o, b), (r << 15n : U32))),
    tr(R.trick.seat(U32.and(U32.or(R.trick.make(s, p, l, o, b), (r << 15n : U32)), 15)), R.trick.seat(U32.and(R.trick.make(s, p, l, o, b), 15)), U32.and(s, 3),
      Equal.cong(U32, U32, (x => R.trick.seat(x)), U32.and(U32.or(R.trick.make(s, p, l, o, b), (r << 15n : U32)), 15), U32.and(R.trick.make(s, p, l, o, b), 15), low4.r(R.trick.make(s, p, l, o, b), r)),
      tr(R.trick.seat(U32.and(R.trick.make(s, p, l, o, b), 15)), R.trick.seat(R.trick.make(s, p, l, o, b)), U32.and(s, 3),
        Equal.sym(U32, R.trick.seat(R.trick.make(s, p, l, o, b)), R.trick.seat(U32.and(R.trick.make(s, p, l, o, b), 15)), Laws.seat_low(R.trick.make(s, p, l, o, b))),
        Laws.seat_make(s, p, l, o, b))))

def Laws.played_make_r(k, lk, y, l, o, b, r):
  tr(R.trick.played(U32.or(R.trick.make(U32.and(y, 3), U32.from_nat(k), l, o, b), (r << 15n : U32))), R.trick.played(U32.and(U32.or(R.trick.make(U32.and(y, 3), U32.from_nat(k), l, o, b), (r << 15n : U32)), 15)), U32.from_nat(k),
    Laws.played_low(U32.or(R.trick.make(U32.and(y, 3), U32.from_nat(k), l, o, b), (r << 15n : U32))),
    tr(R.trick.played(U32.and(U32.or(R.trick.make(U32.and(y, 3), U32.from_nat(k), l, o, b), (r << 15n : U32)), 15)), R.trick.played(U32.and(R.trick.make(U32.and(y, 3), U32.from_nat(k), l, o, b), 15)), U32.from_nat(k),
      Equal.cong(U32, U32, (x => R.trick.played(x)), U32.and(U32.or(R.trick.make(U32.and(y, 3), U32.from_nat(k), l, o, b), (r << 15n : U32)), 15), U32.and(R.trick.make(U32.and(y, 3), U32.from_nat(k), l, o, b), 15), low4.r(R.trick.make(U32.and(y, 3), U32.from_nat(k), l, o, b), r)),
      tr(R.trick.played(U32.and(R.trick.make(U32.and(y, 3), U32.from_nat(k), l, o, b), 15)), R.trick.played(R.trick.make(U32.and(y, 3), U32.from_nat(k), l, o, b)), U32.from_nat(k),
        Equal.sym(U32, R.trick.played(R.trick.make(U32.and(y, 3), U32.from_nat(k), l, o, b)), R.trick.played(U32.and(R.trick.make(U32.and(y, 3), U32.from_nat(k), l, o, b), 15)), Laws.played_low(R.trick.make(U32.and(y, 3), U32.from_nat(k), l, o, b))),
        Laws.played_make(k, lk, y, l, o, b))))

def and3.idem(+x: U32) -> {U32.and(U32.and(x, 3), 3) == U32.and(x, 3) : U32}:
  Laws.and_assoc32(x, 3, 3)

# After the lead and the middle cards: the next seat plays, one more card is down.

def Laws.next_seat(k, lk, win, rank, seat, lead, owner, best, c):
  match k:
    case 0n:
      tr(R.trick.seat(R.trick.make(U32.and((seat + 1 : U32), 3), 1, C.card.suit(c), seat, c)), U32.and(U32.and((seat + 1 : U32), 3), 3), U32.and((seat + 1 : U32), 3), Laws.seat_make(U32.and((seat + 1 : U32), 3), 1, C.card.suit(c), seat, c), and3.idem((seat + 1 : U32)))
    case 1n:
      tr(R.trick.seat(U32.or(R.trick.make(U32.and((seat + 1 : U32), 3), 2, lead, R.sel(win, seat, owner), R.sel(win, c, best)), (Bool.to_u32(rank) << 15n : U32))), U32.and(U32.and((seat + 1 : U32), 3), 3), U32.and((seat + 1 : U32), 3), Laws.seat_make_r(U32.and((seat + 1 : U32), 3), 2, lead, R.sel(win, seat, owner), R.sel(win, c, best), Bool.to_u32(rank)), and3.idem((seat + 1 : U32)))
    case 2n:
      tr(R.trick.seat(U32.or(R.trick.make(U32.and((seat + 1 : U32), 3), 3, lead, R.sel(win, seat, owner), R.sel(win, c, best)), (Bool.to_u32(rank) << 15n : U32))), U32.and(U32.and((seat + 1 : U32), 3), 3), U32.and((seat + 1 : U32), 3), Laws.seat_make_r(U32.and((seat + 1 : U32), 3), 3, lead, R.sel(win, seat, owner), R.sel(win, c, best), Bool.to_u32(rank)), and3.idem((seat + 1 : U32)))
    case 3n+x:
      Empty.absurd({R.trick.seat(R.trick.next.go(U32.is_eq(U32.from_nat(3n+x), 0), U32.is_eq(U32.from_nat(3n+x), 3), win, rank, seat, U32.from_nat(3n+x), lead, owner, best, c)) == U32.and((seat + 1 : U32), 3) : U32}, no_lt0(x, lk))

def Laws.next_played(k, lk, win, rank, seat, lead, owner, best, c):
  match k:
    case 0n:
      Laws.played_make(1n, {==}, (seat + 1 : U32), C.card.suit(c), seat, c)
    case 1n:
      Laws.played_make_r(2n, {==}, (seat + 1 : U32), lead, R.sel(win, seat, owner), R.sel(win, c, best), Bool.to_u32(rank))
    case 2n:
      Laws.played_make_r(3n, {==}, (seat + 1 : U32), lead, R.sel(win, seat, owner), R.sel(win, c, best), Bool.to_u32(rank))
    case 3n+x:
      Empty.absurd({R.trick.played(R.trick.next.go(U32.is_eq(U32.from_nat(3n+x), 0), U32.is_eq(U32.from_nat(3n+x), 3), win, rank, seat, U32.from_nat(3n+x), lead, owner, best, c)) == U32.from_nat(4n+x) : U32}, no_lt0(x, lk))


# After the fourth card: a new trick, with nothing played.

def Laws.next_end(win, rank, y1, lead, y2, best, c):
  match win:
    case True{}:
      Laws.played_make(0n, {==}, y1, R.none(), 0, 0)
    case False{}:
      Laws.played_make(0n, {==}, y2, R.none(), 0, 0)

def Laws.cmp_dbl(a, b, x, y):
  match a b x y:
    case False{} False{} 0n 0n:
      {==}
    case False{} False{} 0n 1n+v:
      {==}
    case False{} False{} 1n+u 0n:
      {==}
    case False{} False{} 1n+u 1n+v:
      Laws.cmp_dbl(False{}, False{}, u, v)
    case False{} True{} 0n 0n:
      {==}
    case False{} True{} 0n 1n+v:
      {==}
    case False{} True{} 1n+u 0n:
      {==}
    case False{} True{} 1n+u 1n+v:
      Laws.cmp_dbl(False{}, True{}, u, v)
    case True{} False{} 0n 0n:
      {==}
    case True{} False{} 0n 1n+v:
      {==}
    case True{} False{} 1n+u 0n:
      {==}
    case True{} False{} 1n+u 1n+v:
      Laws.cmp_dbl(True{}, False{}, u, v)
    case True{} True{} 0n 0n:
      {==}
    case True{} True{} 0n 1n+v:
      {==}
    case True{} True{} 1n+u 0n:
      {==}
    case True{} True{} 1n+u 1n+v:
      Laws.cmp_dbl(True{}, True{}, u, v)

def tonat.bit(+p: Nat, +b: Bool, +t: Word(p)) -> {Word.to_nat(1n+p, WCon{b, t}) == S.bitnat(b, Word.to_nat(p, t)) : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# Words compare as the numbers they stand for.

def Laws.cmp_nat(n, a, b):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+a0, +at} WCon{+b0, +bt}:
          %Equal.sym(Nat, Word.to_nat(1n+p, WCon{a0, at}), S.bitnat(a0, Word.to_nat(p, at)), tonat.bit(p, a0, at)) : {Word.cmp.fin(a0, b0, Word.cmp(p, at, bt)) == Nat.cmp(_, Word.to_nat(1n+p, WCon{b0, bt})) : Cmp}
          %Equal.sym(Nat, Word.to_nat(1n+p, WCon{b0, bt}), S.bitnat(b0, Word.to_nat(p, bt)), tonat.bit(p, b0, bt)) : {Word.cmp.fin(a0, b0, Word.cmp(p, at, bt)) == Nat.cmp(S.bitnat(a0, Word.to_nat(p, at)), _) : Cmp}
          %Equal.sym(Cmp, Word.cmp(p, at, bt), Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)), Laws.cmp_nat(p, at, bt)) : {Word.cmp.fin(a0, b0, _) == Nat.cmp(S.bitnat(a0, Word.to_nat(p, at)), S.bitnat(b0, Word.to_nat(p, bt))) : Cmp}
          Equal.sym(Cmp, Nat.cmp(S.bitnat(a0, Word.to_nat(p, at)), S.bitnat(b0, Word.to_nat(p, bt))), Word.cmp.fin(a0, b0, Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))), Laws.cmp_dbl(a0, b0, Word.to_nat(p, at), Word.to_nat(p, bt)))

def Laws.u32_cmp_nat(a, b):
  match a b:
    case U32{+x} U32{+y}:
      Laws.cmp_nat(32n, x, y)

def Laws.adc00(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          cons.eq(p, False{}, False{}, Word.adc(p, t, Word.zero(p), False{}, False{}), t, {==}, Laws.adc00(p, t))
        case WCon{True{}, +t}:
          cons.eq(p, True{}, True{}, Word.adc(p, t, Word.zero(p), False{}, False{}), t, {==}, Laws.adc00(p, t))

def Laws.adc01(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          cons.eq(p, True{}, True{}, Word.adc(p, t, Word.zero(p), False{}, False{}), t, {==}, Laws.adc00(p, t))
        case WCon{True{}, +t}:
          cons.eq(p, False{}, False{}, Word.adc(p, t, Word.zero(p), False{}, True{}), Word.inc(p, t), {==}, Laws.adc01(p, t))

# Adding one is counting up by one.

def Laws.add_one(u):
  match u:
    case U32{WCon{False{}, +t}}:
      u.wrap(WCon{True{}, Word.adc(31n, t, Word.zero(31n), False{}, False{})}, WCon{True{}, t}, cons.eq(31n, True{}, True{}, Word.adc(31n, t, Word.zero(31n), False{}, False{}), t, {==}, Laws.adc00(31n, t)))
    case U32{WCon{True{}, +t}}:
      u.wrap(WCon{False{}, Word.adc(31n, t, Word.zero(31n), False{}, True{})}, WCon{False{}, Word.inc(31n, t)}, cons.eq(31n, False{}, False{}, Word.adc(31n, t, Word.zero(31n), False{}, True{}), Word.inc(31n, t), {==}, Laws.adc01(31n, t)))

def Laws.add_zero32(u):
  match u:
    case U32{+w}:
      u.wrap(Word.adc(32n, w, Word.zero(32n), False{}, False{}), w, Laws.adc00(32n, w))


# Which side is to play is the low bit of the seat.

def Laws.side_seat(x):
  Equal.sym(U32, U32.and(U32.and(x, 3), 1), U32.and(x, 1), Laws.and_assoc32(x, 3, 1))



# ---------------------------------------------------------------------------
# Hands stay even, and the value bounds

def Laws.le_refl(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Laws.le_refl(p)

def Laws.le_zero(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Laws.le_trans(a, b, c, x, y):
  match a b c:
    case 0n _ _:
      Laws.le_zero(c)
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, no_ft(x))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, no_ft(y))
    case 1n+p 1n+q 1n+r:
      Laws.le_trans(p, q, r, x, y)

def Laws.le_succ(a, b, x):
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, no_ft(x))
    case 1n+p 1n+q:
      Laws.le_succ(p, q, x)

def Laws.le_add(a, b):
  match a:
    case 0n:
      Laws.le_zero(b)
    case 1n+p:
      Laws.le_add(p, b)

def Laws.add_zero(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Laws.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def Laws.add_succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Laws.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def Laws.lt_le(m, n, e):
  match m n:
    case 0n _:
      Laws.le_zero(n)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, no_ft(e))
    case 1n+p 1n+q:
      Laws.lt_le(p, q, e)

def Laws.nlt_le(m, n, e):
  match m n:
    case _ 0n:
      Laws.le_zero(m)
    case 0n 1n+q:
      Empty.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, no_tf(e))
    case 1n+p 1n+q:
      Laws.nlt_le(p, q, e)

def p1(-A: Type, -B: Type, p: A & B) -> A:
  (a, b) = p
  a

def p2(-A: Type, -B: Type, p: A & B) -> B:
  (a, b) = p
  b

# ---------------------------------------------------------------------------
# Max and min against bounds, through the numbers the words stand for

def lt.nat(+a: U32, +b: U32, +c: Bool, e: {U32.is_lt(a, b) == c : Bool}) -> {Cmp.is_lt(Nat.cmp(U32.to_nat(a), U32.to_nat(b))) == c : Bool}:
  %Laws.u32_cmp_nat(a, b) : {Cmp.is_lt(_) == c : Bool}
  e

def max.go(+c: Bool, +a: U32, +b: U32, +hi: Nat, +e: {Cmp.is_lt(Nat.cmp(U32.to_nat(a), U32.to_nat(b))) == c : Bool}, +ha: {Nat.is_le(U32.to_nat(a), hi) == True{} : Bool}, +hb: {Nat.is_le(U32.to_nat(b), hi) == True{} : Bool}) -> {Nat.is_le(U32.to_nat(Bool.pick(U32, c, b, a)), hi) == True{} : Bool} & {Nat.is_le(U32.to_nat(b), U32.to_nat(Bool.pick(U32, c, b, a))) == True{} : Bool}:
  match c:
    case True{}:
      (hb, Laws.le_refl(U32.to_nat(b)))
    case False{}:
      (ha, Laws.nlt_le(U32.to_nat(a), U32.to_nat(b), e))

def min.go(+c: Bool, +a: U32, +b: U32, +lo: Nat, +e: {Cmp.is_lt(Nat.cmp(U32.to_nat(a), U32.to_nat(b))) == c : Bool}, +la: {Nat.is_le(lo, U32.to_nat(a)) == True{} : Bool}, +lb: {Nat.is_le(lo, U32.to_nat(b)) == True{} : Bool}) -> {Nat.is_le(lo, U32.to_nat(Bool.pick(U32, c, a, b))) == True{} : Bool} & {Nat.is_le(U32.to_nat(Bool.pick(U32, c, a, b)), U32.to_nat(b)) == True{} : Bool}:
  match c:
    case True{}:
      (la, Laws.lt_le(U32.to_nat(a), U32.to_nat(b), e))
    case False{}:
      (lb, Laws.le_refl(U32.to_nat(b)))

# The max of two values at most hi is at most hi, and it is at least the second.

def Laws.max_le(a, b, hi, ha, hb):
  match a b:
    case U32{+x} U32{+y}:
      max.go(U32.is_lt(U32{x}, U32{y}), U32{x}, U32{y}, hi, lt.nat(U32{x}, U32{y}, U32.is_lt(U32{x}, U32{y}), {==}), ha, hb)

# The min of two values at least lo is at least lo, and it is at most the second.

def Laws.min_ge(a, b, lo, la, lb):
  match a b:
    case U32{+x} U32{+y}:
      min.go(U32.is_lt(U32{x}, U32{y}), U32{x}, U32{y}, lo, lt.nat(U32{x}, U32{y}, U32.is_lt(U32{x}, U32{y}), {==}), la, lb)

# ---------------------------------------------------------------------------
# Values in range: between the tricks won and those plus the tricks left

# Two facts that can be used many times, unlike a pair, which is used once.

def Laws.ok_in(ns, v, w, L, i):
  match ns:
    case True{}:
      (lo, hi) = i
      hi
    case False{}:
      (lo, hi) = i
      lo

def Laws.ok_better(ns, a, b, w, L, oa, ob):
  match ns:
    case True{}:
      p1({Nat.is_le(U32.to_nat(U32.max(a, b)), Nat.add(w, L)) == True{} : Bool}, {Nat.is_le(U32.to_nat(b), U32.to_nat(U32.max(a, b))) == True{} : Bool}, Laws.max_le(a, b, Nat.add(w, L), oa, ob))
    case False{}:
      p1({Nat.is_le(w, U32.to_nat(U32.min(a, b))) == True{} : Bool}, {Nat.is_le(U32.to_nat(U32.min(a, b)), U32.to_nat(b)) == True{} : Bool}, Laws.min_ge(a, b, w, oa, ob))

def Laws.in_better(ns, a, b, w, L, oa, ib):
  match ns:
    case True{}:
      (+lo, +hi) = ib
      (Laws.le_trans(w, U32.to_nat(b), U32.to_nat(U32.max(a, b)), lo, p2({Nat.is_le(U32.to_nat(U32.max(a, b)), Nat.add(w, L)) == True{} : Bool}, {Nat.is_le(U32.to_nat(b), U32.to_nat(U32.max(a, b))) == True{} : Bool}, Laws.max_le(a, b, Nat.add(w, L), oa, hi))),
        p1({Nat.is_le(U32.to_nat(U32.max(a, b)), Nat.add(w, L)) == True{} : Bool}, {Nat.is_le(U32.to_nat(b), U32.to_nat(U32.max(a, b))) == True{} : Bool}, Laws.max_le(a, b, Nat.add(w, L), oa, hi)))
    case False{}:
      (+lo, +hi) = ib
      (p1({Nat.is_le(w, U32.to_nat(U32.min(a, b))) == True{} : Bool}, {Nat.is_le(U32.to_nat(U32.min(a, b)), U32.to_nat(b)) == True{} : Bool}, Laws.min_ge(a, b, w, oa, lo)),
        Laws.le_trans(U32.to_nat(U32.min(a, b)), U32.to_nat(b), Nat.add(w, L), p2({Nat.is_le(w, U32.to_nat(U32.min(a, b))) == True{} : Bool}, {Nat.is_le(U32.to_nat(U32.min(a, b)), U32.to_nat(b)) == True{} : Bool}, Laws.min_ge(a, b, w, oa, lo)), hi))

def Laws.ok_seed(ns, w, L, h):
  match ns:
    case True{}:
      Laws.le_zero(Nat.add(w, L))
    case False{}:
      Laws.le_trans(w, Nat.add(w, L), 13n, Laws.le_add(w, L), h)

# ---------------------------------------------------------------------------
# Counting the cards of a hand

def Laws.xor0(h):
  match h:
    case U32{+x}:
      u.wrap(Word.xor(32n, x, Word.zero(32n)), x, Laws.xor_zero(32n, x))

def take.go(+b: Bool, +x: U32, +h01: U32, +h23: U32, +i1: S.Sub32(R.sel(b, x, 0), h01), +i2: S.Sub32(R.sel(b, 0, x), h23), +one: {S.bits(x) == 1n : Nat}) -> {S.cnt(h01, h23) == 1n+S.cnt(U32.xor(h01, R.sel(b, x, 0)), U32.xor(h23, R.sel(b, 0, x))) : Nat}:
  match b:
    case True{}:
      %Equal.sym(U32, U32.xor(h23, 0), h23, Laws.xor0(h23)) : {Nat.add(S.bits(h01), S.bits(h23)) == 1n+Nat.add(S.bits(U32.xor(h01, x)), S.bits(_)) : Nat}
      %Equal.sym(Nat, S.bits(h01), 1n+S.bits(U32.xor(h01, x)), Laws.count_xor32(x, h01, i1, one)) : {Nat.add(_, S.bits(h23)) == 1n+Nat.add(S.bits(U32.xor(h01, x)), S.bits(h23)) : Nat}
      {==}
    case False{}:
      %Equal.sym(U32, U32.xor(h01, 0), h01, Laws.xor0(h01)) : {Nat.add(S.bits(h01), S.bits(h23)) == 1n+Nat.add(S.bits(_), S.bits(U32.xor(h23, x))) : Nat}
      %Equal.sym(Nat, S.bits(h23), 1n+S.bits(U32.xor(h23, x)), Laws.count_xor32(x, h23, i2, one)) : {Nat.add(S.bits(h01), _) == 1n+Nat.add(S.bits(h01), S.bits(U32.xor(h23, x))) : Nat}
      Laws.add_succ(S.bits(h01), S.bits(U32.xor(h23, x)))

def Laws.and3_lt(x):
  match x:
    case U32{+w}:
      Laws.bound(32n, 2n, Word.and(32n, w, S.ones(32n, 2n)), Laws.and_assoc(32n, w, S.ones(32n, 2n), S.ones(32n, 2n)))

def seat.go(+k: Nat, +lk: {Nat.is_lt(k, 3n) == True{} : Bool}, +win: Bool, +rank: Bool, +seat: U32, +played: U32, +lead: U32, +owner: U32, +best: U32, +c: U32, +ep: {played == U32.from_nat(k) : U32}) -> {R.trick.seat(R.trick.next.go(U32.is_eq(played, 0), U32.is_eq(played, 3), win, rank, seat, played, lead, owner, best, c)) == U32.and((seat + 1 : U32), 3) : U32}:
  %Equal.sym(U32, played, U32.from_nat(k), ep) : {R.trick.seat(R.trick.next.go(U32.is_eq(_, 0), U32.is_eq(_, 3), win, rank, seat, _, lead, owner, best, c)) == U32.and((seat + 1 : U32), 3) : U32}
  Laws.next_seat(k, lk, win, rank, seat, lead, owner, best, c)

def played.go(+k: Nat, +lk: {Nat.is_lt(k, 3n) == True{} : Bool}, +win: Bool, +rank: Bool, +seat: U32, +played: U32, +lead: U32, +owner: U32, +best: U32, +c: U32, +ep: {played == U32.from_nat(k) : U32}) -> {R.trick.played(R.trick.next.go(U32.is_eq(played, 0), U32.is_eq(played, 3), win, rank, seat, played, lead, owner, best, c)) == U32.from_nat(1n+k) : U32}:
  %Equal.sym(U32, played, U32.from_nat(k), ep) : {R.trick.played(R.trick.next.go(U32.is_eq(_, 0), U32.is_eq(_, 3), win, rank, seat, _, lead, owner, best, c)) == U32.from_nat(1n+k) : U32}
  Laws.next_played(k, lk, win, rank, seat, lead, owner, best, c)

def end.go(+win: Bool, +rank: Bool, +y1: U32, +played: U32, +lead: U32, +y2: U32, +best: U32, +c: U32, +ep: {played == 3 : U32}) -> {R.trick.played(R.trick.next.go(U32.is_eq(played, 0), U32.is_eq(played, 3), win, rank, U32.and(y1, 3), played, lead, U32.and(y2, 3), best, c)) == 0 : U32}:
  %Equal.sym(U32, played, 3, ep) : {R.trick.played(R.trick.next.go(U32.is_eq(_, 0), U32.is_eq(_, 3), win, rank, U32.and(y1, 3), _, lead, U32.and(y2, 3), best, c)) == 0 : U32}
  Laws.next_end(win, rank, y1, lead, y2, best, c)

def rank.of(+t: U32, +tr: U32, +c: U32) -> Bool:
  (U32.is_eq(C.card.suit(c), C.card.suit(R.trick.best(tr))) || (R.trick.rank(tr) && Bool.not(R.beats(t, R.trick.best(tr), c))))

# In the middle of a trick, the next seat is to play and one more card is down.

def Laws.seat_mid(k, lk, tr, t, c, ep):
  seat.go(k, lk, R.beats(t, R.trick.best(tr), c), rank.of(t, tr, c), R.trick.seat(tr), R.trick.played(tr), R.trick.lead(tr), R.trick.owner(tr), R.trick.best(tr), c, ep)

def Laws.played_mid(k, lk, tr, t, c, ep):
  played.go(k, lk, R.beats(t, R.trick.best(tr), c), rank.of(t, tr, c), R.trick.seat(tr), R.trick.played(tr), R.trick.lead(tr), R.trick.owner(tr), R.trick.best(tr), c, ep)

# The fourth card ends the trick.

def Laws.played_end(tr, t, c, ep):
  end.go(R.beats(t, R.trick.best(tr), c), rank.of(t, tr, c), tr, R.trick.played(tr), R.trick.lead(tr), (tr >> 7n : U32), R.trick.best(tr), c, ep)

# Tricks won: the same within a trick, and one more or not when it ends.

def Laws.won_mid(k, lk, x, won, e):
  match k:
    case 0n:
      %Equal.sym(U32, R.trick.played(x), U32.from_nat(1n), e) : {R.sel(U32.is_eq(_, 0), (won + Bool.to_u32(U32.is_eq((x .&. 1 : U32), 0)) : U32), won) == won : U32}
      {==}
    case 1n:
      %Equal.sym(U32, R.trick.played(x), U32.from_nat(2n), e) : {R.sel(U32.is_eq(_, 0), (won + Bool.to_u32(U32.is_eq((x .&. 1 : U32), 0)) : U32), won) == won : U32}
      {==}
    case 2n:
      %Equal.sym(U32, R.trick.played(x), U32.from_nat(3n), e) : {R.sel(U32.is_eq(_, 0), (won + Bool.to_u32(U32.is_eq((x .&. 1 : U32), 0)) : U32), won) == won : U32}
      {==}
    case 3n+y:
      Empty.absurd({R.won.next(x, won) == won : U32}, no_lt0(y, lk))

def Laws.tn14(n, lt):
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n+x:
      Empty.absurd({U32.to_nat(U32.from_nat(14n+x)) == 14n+x : Nat}, no_lt0(x, lt))

def Laws.add_bit(u, b, lt):
  match b:
    case False{}:
      %Equal.sym(U32, U32.add(u, 0), u, Laws.add_zero32(u)) : {U32.to_nat(_) == U32.to_nat(u) : Nat}
      {==}
    case True{}:
      %Equal.sym(U32, U32.add(u, 1), U32.inc(u), Laws.add_one(u)) : {U32.to_nat(_) == 1n+U32.to_nat(u) : Nat}
      %Laws.u32_roundtrip(u) : {U32.to_nat(U32.inc(_)) == 1n+U32.to_nat(u) : Nat}
      Laws.tn14(1n+U32.to_nat(u), lt)

def Laws.won_end(x, won, e, lt):
  %Equal.sym(U32, R.trick.played(x), 0, e) : {U32.to_nat(R.sel(U32.is_eq(_, 0), (won + Bool.to_u32(U32.is_eq((x .&. 1 : U32), 0)) : U32), won)) == Nat.add(S.b2n(U32.is_eq((x .&. 1 : U32), 0)), U32.to_nat(won)) : Nat}
  Laws.add_bit(won, U32.is_eq((x .&. 1 : U32), 0), lt)

# ---------------------------------------------------------------------------
# Small steps on counts

def Laws.le_lt(a, b, e):
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_lt(a, 0n) == True{} : Bool}, no_ft(e))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      Laws.le_lt(p, q, e)

def Laws.le_lt_trans(a, b, c, x, y):
  match a b c:
    case _ _ 0n:
      Empty.absurd({Nat.is_lt(a, 0n) == True{} : Bool}, no_lt0(b, y))
    case 0n _ 1n+r:
      {==}
    case 1n+p 0n 1n+r:
      Empty.absurd({Nat.is_lt(1n+p, 1n+r) == True{} : Bool}, no_ft(x))
    case 1n+p 1n+q 1n+r:
      Laws.le_lt_trans(p, q, r, x, y)

def succ.inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, (z => S.pred(z)), 1n+a, 1n+b, e)

def tr.n(-a: Nat, -b: Nat, -c: Nat, x: {a == b : Nat}, y: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, x, y)

def sym.n(-a: Nat, -b: Nat, x: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, x)

# A trick over: with L = 1 + x, the plies left are those of x cards each.

def Laws.d_end(p, L, x, e1, ed):
  %e1 : {p == S.r4(S.pred(_)) : Nat}
  succ.inj(p, S.r4(x), succ.inj(1n+p, 1n+S.r4(x), succ.inj(2n+p, 2n+S.r4(x), succ.inj(3n+p, 3n+S.r4(x),
    tr.n(4n+p, S.r4(L), 4n+S.r4(x), ed, Equal.cong(Nat, Nat, (z => S.r4(z)), L, 1n+x, sym.n(1n+x, L, e1)))))))

def le.at(-a: Nat, -b: Nat, +c: Nat, e: {a == b : Nat}, h: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(a, c), Nat.is_le(b, c), True{}, Equal.cong(Nat, Bool, (z => Nat.is_le(z, c)), a, b, e), h)

# The tricks won and the cards left, after a trick: still at most 13.

def Laws.w_end(bb, w, L, x, e1, h):
  match bb:
    case False{}:
      %e1 : {Nat.is_le(Nat.add(w, S.pred(_)), 13n) == True{} : Bool}
      Laws.le_trans(Nat.add(w, x), 1n+Nat.add(w, x), 13n, Laws.le_succ(Nat.add(w, x), Nat.add(w, x), Laws.le_refl(Nat.add(w, x))),
        le.at(1n+Nat.add(w, x), Nat.add(w, L), 13n, tr.n(1n+Nat.add(w, x), Nat.add(w, 1n+x), Nat.add(w, L), sym.n(Nat.add(w, 1n+x), 1n+Nat.add(w, x), Laws.add_succ(w, x)), Equal.cong(Nat, Nat, (z => Nat.add(w, z)), 1n+x, L, e1)), h))
    case True{}:
      %e1 : {Nat.is_le(1n+Nat.add(w, S.pred(_)), 13n) == True{} : Bool}
      le.at(1n+Nat.add(w, x), Nat.add(w, L), 13n, tr.n(1n+Nat.add(w, x), Nat.add(w, 1n+x), Nat.add(w, L), sym.n(Nat.add(w, 1n+x), 1n+Nat.add(w, x), Laws.add_succ(w, x)), Equal.cong(Nat, Nat, (z => Nat.add(w, z)), 1n+x, L, e1)), h)

# A trick still to finish means fewer than 13 won.

def Laws.w_lt(w, L, x, e1, h):
  Laws.le_lt_trans(w, Nat.add(w, x), 13n, Laws.le_add(w, x),
    Laws.le_lt(Nat.add(w, x), 13n, le.at(1n+Nat.add(w, x), Nat.add(w, L), 13n, tr.n(1n+Nat.add(w, x), Nat.add(w, 1n+x), Nat.add(w, L), sym.n(Nat.add(w, 1n+x), 1n+Nat.add(w, x), Laws.add_succ(w, x)), Equal.cong(Nat, Nat, (z => Nat.add(w, z)), 1n+x, L, e1)), h)))

def cg(-a: U32, -b: U32, e: {a == b : U32}) -> {U32.to_nat(a) == U32.to_nat(b) : Nat}:
  Equal.cong(U32, Nat, (z => U32.to_nat(z)), a, b, e)

def nx(s: Nat) -> Nat:
  match s:
    case 0n:
      1n
    case 1n:
      2n
    case 2n:
      3n
    case _:
      0n

# One card played in the middle of a trick keeps the invariant, with the next
# seat to play.

def mid(+s: Nat, +k: Nat, +p: Nat, +L: Nat, +c: U32, +n01: U32, +n23: U32, +e01: U32, +e23: U32, +s01: U32, +s23: U32, +w01: U32, +w23: U32, +tr2: U32, +won: U32,
    +inv: S.Inv.go(n01, n23, e01, e23, s01, s23, w01, w23, s, k, U32.to_nat(won), 1n+p, L),
    +ls: {Nat.is_lt(s, 4n) == True{} : Bool}, +lk: {Nat.is_lt(k, 3n) == True{} : Bool},
    +i1: S.Sub32(S.play.a(c), R.pick(s, n01, e01, s01, w01)), +i2: S.Sub32(S.play.b(c), R.pick(s, n23, e23, s23, w23)),
    +one: {S.bits(S.play.x(c)) == 1n : Nat},
    +es: {U32.to_nat(R.trick.seat(tr2)) == nx(s) : Nat}, +ep: {R.trick.played(tr2) == U32.from_nat(1n+k) : U32}) ->
    S.Inv(R.play.go(s, S.play.a(c), S.play.b(c), n01, n23, e01, e23, s01, s23, w01, w23, tr2, R.won.next(tr2, won)), p, L):
  match s k:
    case 0n 0n:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls2, (+lk2, ((+e_0, (+e_1, (+e_2, +e_3))), (+ed, +ewl))))) = inv
      %Equal.sym(Nat, U32.to_nat(R.trick.seat(tr2)), 1n, es) : S.Inv.go(U32.xor(n01, S.play.a(c)), U32.xor(n23, S.play.b(c)), e01, e23, s01, s23, w01, w23, _, U32.to_nat(R.trick.played(tr2)), U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.trick.played(tr2)), 1n, cg(R.trick.played(tr2), U32.from_nat(1n), ep)) : S.Inv.go(U32.xor(n01, S.play.a(c)), U32.xor(n23, S.play.b(c)), e01, e23, s01, s23, w01, w23, 1n, _, U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.won.next(tr2, won)), U32.to_nat(won), cg(R.won.next(tr2, won), won, Laws.won_mid(0n, {==}, tr2, won, ep))) : S.Inv.go(U32.xor(n01, S.play.a(c)), U32.xor(n23, S.play.b(c)), e01, e23, s01, s23, w01, w23, 1n, 1n, _, p, L)
      ((Laws.xor_sub32(n01, S.play.a(c), S.valid.mask(), v_n01, i1), (Laws.xor_sub32(n23, S.play.b(c), S.valid.mask(), v_n23, i2), (v_e01, (v_e23, (v_s01, (v_s23, (v_w01, v_w23))))))), ({==}, ({==}, ((tr.n(1n+S.cnt(U32.xor(n01, S.play.a(c)), U32.xor(n23, S.play.b(c))), S.cnt(n01, n23), L, sym.n(S.cnt(n01, n23), 1n+S.cnt(U32.xor(n01, S.play.a(c)), U32.xor(n23, S.play.b(c))), take.go(U32.is_lt(C.card.suit(c), 2), S.play.x(c), n01, n23, i1, i2, one)), e_0), (e_1, (e_2, e_3))), (ed, ewl)))))
    case 0n 1n:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls2, (+lk2, ((+e_0, (+e_1, (+e_2, +e_3))), (+ed, +ewl))))) = inv
      %Equal.sym(Nat, U32.to_nat(R.trick.seat(tr2)), 1n, es) : S.Inv.go(U32.xor(n01, S.play.a(c)), U32.xor(n23, S.play.b(c)), e01, e23, s01, s23, w01, w23, _, U32.to_nat(R.trick.played(tr2)), U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.trick.played(tr2)), 2n, cg(R.trick.played(tr2), U32.from_nat(2n), ep)) : S.Inv.go(U32.xor(n01, S.play.a(c)), U32.xor(n23, S.play.b(c)), e01, e23, s01, s23, w01, w23, 1n, _, U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.won.next(tr2, won)), U32.to_nat(won), cg(R.won.next(tr2, won), won, Laws.won_mid(1n, {==}, tr2, won, ep))) : S.Inv.go(U32.xor(n01, S.play.a(c)), U32.xor(n23, S.play.b(c)), e01, e23, s01, s23, w01, w23, 1n, 2n, _, p, L)
      ((Laws.xor_sub32(n01, S.play.a(c), S.valid.mask(), v_n01, i1), (Laws.xor_sub32(n23, S.play.b(c), S.valid.mask(), v_n23, i2), (v_e01, (v_e23, (v_s01, (v_s23, (v_w01, v_w23))))))), ({==}, ({==}, ((tr.n(1n+S.cnt(U32.xor(n01, S.play.a(c)), U32.xor(n23, S.play.b(c))), S.cnt(n01, n23), L, sym.n(S.cnt(n01, n23), 1n+S.cnt(U32.xor(n01, S.play.a(c)), U32.xor(n23, S.play.b(c))), take.go(U32.is_lt(C.card.suit(c), 2), S.play.x(c), n01, n23, i1, i2, one)), e_0), (e_1, (e_2, e_3))), (ed, ewl)))))
    case 0n 2n:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls2, (+lk2, ((+e_0, (+e_1, (+e_2, +e_3))), (+ed, +ewl))))) = inv
      %Equal.sym(Nat, U32.to_nat(R.trick.seat(tr2)), 1n, es) : S.Inv.go(U32.xor(n01, S.play.a(c)), U32.xor(n23, S.play.b(c)), e01, e23, s01, s23, w01, w23, _, U32.to_nat(R.trick.played(tr2)), U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.trick.played(tr2)), 3n, cg(R.trick.played(tr2), U32.from_nat(3n), ep)) : S.Inv.go(U32.xor(n01, S.play.a(c)), U32.xor(n23, S.play.b(c)), e01, e23, s01, s23, w01, w23, 1n, _, U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.won.next(tr2, won)), U32.to_nat(won), cg(R.won.next(tr2, won), won, Laws.won_mid(2n, {==}, tr2, won, ep))) : S.Inv.go(U32.xor(n01, S.play.a(c)), U32.xor(n23, S.play.b(c)), e01, e23, s01, s23, w01, w23, 1n, 3n, _, p, L)
      ((Laws.xor_sub32(n01, S.play.a(c), S.valid.mask(), v_n01, i1), (Laws.xor_sub32(n23, S.play.b(c), S.valid.mask(), v_n23, i2), (v_e01, (v_e23, (v_s01, (v_s23, (v_w01, v_w23))))))), ({==}, ({==}, ((tr.n(1n+S.cnt(U32.xor(n01, S.play.a(c)), U32.xor(n23, S.play.b(c))), S.cnt(n01, n23), L, sym.n(S.cnt(n01, n23), 1n+S.cnt(U32.xor(n01, S.play.a(c)), U32.xor(n23, S.play.b(c))), take.go(U32.is_lt(C.card.suit(c), 2), S.play.x(c), n01, n23, i1, i2, one)), e_0), (e_1, (e_2, e_3))), (ed, ewl)))))
    case 0n 3n+y:
      Empty.absurd(S.Inv(R.play.go(0n, S.play.a(c), S.play.b(c), n01, n23, e01, e23, s01, s23, w01, w23, tr2, R.won.next(tr2, won)), p, L), no_lt0(y, lk))
    case 1n 0n:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls2, (+lk2, ((+e_0, (+e_1, (+e_2, +e_3))), (+ed, +ewl))))) = inv
      %Equal.sym(Nat, U32.to_nat(R.trick.seat(tr2)), 2n, es) : S.Inv.go(n01, n23, U32.xor(e01, S.play.a(c)), U32.xor(e23, S.play.b(c)), s01, s23, w01, w23, _, U32.to_nat(R.trick.played(tr2)), U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.trick.played(tr2)), 1n, cg(R.trick.played(tr2), U32.from_nat(1n), ep)) : S.Inv.go(n01, n23, U32.xor(e01, S.play.a(c)), U32.xor(e23, S.play.b(c)), s01, s23, w01, w23, 2n, _, U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.won.next(tr2, won)), U32.to_nat(won), cg(R.won.next(tr2, won), won, Laws.won_mid(0n, {==}, tr2, won, ep))) : S.Inv.go(n01, n23, U32.xor(e01, S.play.a(c)), U32.xor(e23, S.play.b(c)), s01, s23, w01, w23, 2n, 1n, _, p, L)
      ((v_n01, (v_n23, (Laws.xor_sub32(e01, S.play.a(c), S.valid.mask(), v_e01, i1), (Laws.xor_sub32(e23, S.play.b(c), S.valid.mask(), v_e23, i2), (v_s01, (v_s23, (v_w01, v_w23))))))), ({==}, ({==}, ((e_0, (tr.n(1n+S.cnt(U32.xor(e01, S.play.a(c)), U32.xor(e23, S.play.b(c))), S.cnt(e01, e23), L, sym.n(S.cnt(e01, e23), 1n+S.cnt(U32.xor(e01, S.play.a(c)), U32.xor(e23, S.play.b(c))), take.go(U32.is_lt(C.card.suit(c), 2), S.play.x(c), e01, e23, i1, i2, one)), e_1), (e_2, e_3))), (ed, ewl)))))
    case 1n 1n:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls2, (+lk2, ((+e_0, (+e_1, (+e_2, +e_3))), (+ed, +ewl))))) = inv
      %Equal.sym(Nat, U32.to_nat(R.trick.seat(tr2)), 2n, es) : S.Inv.go(n01, n23, U32.xor(e01, S.play.a(c)), U32.xor(e23, S.play.b(c)), s01, s23, w01, w23, _, U32.to_nat(R.trick.played(tr2)), U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.trick.played(tr2)), 2n, cg(R.trick.played(tr2), U32.from_nat(2n), ep)) : S.Inv.go(n01, n23, U32.xor(e01, S.play.a(c)), U32.xor(e23, S.play.b(c)), s01, s23, w01, w23, 2n, _, U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.won.next(tr2, won)), U32.to_nat(won), cg(R.won.next(tr2, won), won, Laws.won_mid(1n, {==}, tr2, won, ep))) : S.Inv.go(n01, n23, U32.xor(e01, S.play.a(c)), U32.xor(e23, S.play.b(c)), s01, s23, w01, w23, 2n, 2n, _, p, L)
      ((v_n01, (v_n23, (Laws.xor_sub32(e01, S.play.a(c), S.valid.mask(), v_e01, i1), (Laws.xor_sub32(e23, S.play.b(c), S.valid.mask(), v_e23, i2), (v_s01, (v_s23, (v_w01, v_w23))))))), ({==}, ({==}, ((e_0, (tr.n(1n+S.cnt(U32.xor(e01, S.play.a(c)), U32.xor(e23, S.play.b(c))), S.cnt(e01, e23), L, sym.n(S.cnt(e01, e23), 1n+S.cnt(U32.xor(e01, S.play.a(c)), U32.xor(e23, S.play.b(c))), take.go(U32.is_lt(C.card.suit(c), 2), S.play.x(c), e01, e23, i1, i2, one)), e_1), (e_2, e_3))), (ed, ewl)))))
    case 1n 2n:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls2, (+lk2, ((+e_0, (+e_1, (+e_2, +e_3))), (+ed, +ewl))))) = inv
      %Equal.sym(Nat, U32.to_nat(R.trick.seat(tr2)), 2n, es) : S.Inv.go(n01, n23, U32.xor(e01, S.play.a(c)), U32.xor(e23, S.play.b(c)), s01, s23, w01, w23, _, U32.to_nat(R.trick.played(tr2)), U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.trick.played(tr2)), 3n, cg(R.trick.played(tr2), U32.from_nat(3n), ep)) : S.Inv.go(n01, n23, U32.xor(e01, S.play.a(c)), U32.xor(e23, S.play.b(c)), s01, s23, w01, w23, 2n, _, U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.won.next(tr2, won)), U32.to_nat(won), cg(R.won.next(tr2, won), won, Laws.won_mid(2n, {==}, tr2, won, ep))) : S.Inv.go(n01, n23, U32.xor(e01, S.play.a(c)), U32.xor(e23, S.play.b(c)), s01, s23, w01, w23, 2n, 3n, _, p, L)
      ((v_n01, (v_n23, (Laws.xor_sub32(e01, S.play.a(c), S.valid.mask(), v_e01, i1), (Laws.xor_sub32(e23, S.play.b(c), S.valid.mask(), v_e23, i2), (v_s01, (v_s23, (v_w01, v_w23))))))), ({==}, ({==}, ((e_0, (tr.n(1n+S.cnt(U32.xor(e01, S.play.a(c)), U32.xor(e23, S.play.b(c))), S.cnt(e01, e23), L, sym.n(S.cnt(e01, e23), 1n+S.cnt(U32.xor(e01, S.play.a(c)), U32.xor(e23, S.play.b(c))), take.go(U32.is_lt(C.card.suit(c), 2), S.play.x(c), e01, e23, i1, i2, one)), e_1), (e_2, e_3))), (ed, ewl)))))
    case 1n 3n+y:
      Empty.absurd(S.Inv(R.play.go(1n, S.play.a(c), S.play.b(c), n01, n23, e01, e23, s01, s23, w01, w23, tr2, R.won.next(tr2, won)), p, L), no_lt0(y, lk))
    case 2n 0n:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls2, (+lk2, ((+e_0, (+e_1, (+e_2, +e_3))), (+ed, +ewl))))) = inv
      %Equal.sym(Nat, U32.to_nat(R.trick.seat(tr2)), 3n, es) : S.Inv.go(n01, n23, e01, e23, U32.xor(s01, S.play.a(c)), U32.xor(s23, S.play.b(c)), w01, w23, _, U32.to_nat(R.trick.played(tr2)), U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.trick.played(tr2)), 1n, cg(R.trick.played(tr2), U32.from_nat(1n), ep)) : S.Inv.go(n01, n23, e01, e23, U32.xor(s01, S.play.a(c)), U32.xor(s23, S.play.b(c)), w01, w23, 3n, _, U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.won.next(tr2, won)), U32.to_nat(won), cg(R.won.next(tr2, won), won, Laws.won_mid(0n, {==}, tr2, won, ep))) : S.Inv.go(n01, n23, e01, e23, U32.xor(s01, S.play.a(c)), U32.xor(s23, S.play.b(c)), w01, w23, 3n, 1n, _, p, L)
      ((v_n01, (v_n23, (v_e01, (v_e23, (Laws.xor_sub32(s01, S.play.a(c), S.valid.mask(), v_s01, i1), (Laws.xor_sub32(s23, S.play.b(c), S.valid.mask(), v_s23, i2), (v_w01, v_w23))))))), ({==}, ({==}, ((e_0, (e_1, (tr.n(1n+S.cnt(U32.xor(s01, S.play.a(c)), U32.xor(s23, S.play.b(c))), S.cnt(s01, s23), L, sym.n(S.cnt(s01, s23), 1n+S.cnt(U32.xor(s01, S.play.a(c)), U32.xor(s23, S.play.b(c))), take.go(U32.is_lt(C.card.suit(c), 2), S.play.x(c), s01, s23, i1, i2, one)), e_2), e_3))), (ed, ewl)))))
    case 2n 1n:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls2, (+lk2, ((+e_0, (+e_1, (+e_2, +e_3))), (+ed, +ewl))))) = inv
      %Equal.sym(Nat, U32.to_nat(R.trick.seat(tr2)), 3n, es) : S.Inv.go(n01, n23, e01, e23, U32.xor(s01, S.play.a(c)), U32.xor(s23, S.play.b(c)), w01, w23, _, U32.to_nat(R.trick.played(tr2)), U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.trick.played(tr2)), 2n, cg(R.trick.played(tr2), U32.from_nat(2n), ep)) : S.Inv.go(n01, n23, e01, e23, U32.xor(s01, S.play.a(c)), U32.xor(s23, S.play.b(c)), w01, w23, 3n, _, U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.won.next(tr2, won)), U32.to_nat(won), cg(R.won.next(tr2, won), won, Laws.won_mid(1n, {==}, tr2, won, ep))) : S.Inv.go(n01, n23, e01, e23, U32.xor(s01, S.play.a(c)), U32.xor(s23, S.play.b(c)), w01, w23, 3n, 2n, _, p, L)
      ((v_n01, (v_n23, (v_e01, (v_e23, (Laws.xor_sub32(s01, S.play.a(c), S.valid.mask(), v_s01, i1), (Laws.xor_sub32(s23, S.play.b(c), S.valid.mask(), v_s23, i2), (v_w01, v_w23))))))), ({==}, ({==}, ((e_0, (e_1, (tr.n(1n+S.cnt(U32.xor(s01, S.play.a(c)), U32.xor(s23, S.play.b(c))), S.cnt(s01, s23), L, sym.n(S.cnt(s01, s23), 1n+S.cnt(U32.xor(s01, S.play.a(c)), U32.xor(s23, S.play.b(c))), take.go(U32.is_lt(C.card.suit(c), 2), S.play.x(c), s01, s23, i1, i2, one)), e_2), e_3))), (ed, ewl)))))
    case 2n 2n:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls2, (+lk2, ((+e_0, (+e_1, (+e_2, +e_3))), (+ed, +ewl))))) = inv
      %Equal.sym(Nat, U32.to_nat(R.trick.seat(tr2)), 3n, es) : S.Inv.go(n01, n23, e01, e23, U32.xor(s01, S.play.a(c)), U32.xor(s23, S.play.b(c)), w01, w23, _, U32.to_nat(R.trick.played(tr2)), U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.trick.played(tr2)), 3n, cg(R.trick.played(tr2), U32.from_nat(3n), ep)) : S.Inv.go(n01, n23, e01, e23, U32.xor(s01, S.play.a(c)), U32.xor(s23, S.play.b(c)), w01, w23, 3n, _, U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.won.next(tr2, won)), U32.to_nat(won), cg(R.won.next(tr2, won), won, Laws.won_mid(2n, {==}, tr2, won, ep))) : S.Inv.go(n01, n23, e01, e23, U32.xor(s01, S.play.a(c)), U32.xor(s23, S.play.b(c)), w01, w23, 3n, 3n, _, p, L)
      ((v_n01, (v_n23, (v_e01, (v_e23, (Laws.xor_sub32(s01, S.play.a(c), S.valid.mask(), v_s01, i1), (Laws.xor_sub32(s23, S.play.b(c), S.valid.mask(), v_s23, i2), (v_w01, v_w23))))))), ({==}, ({==}, ((e_0, (e_1, (tr.n(1n+S.cnt(U32.xor(s01, S.play.a(c)), U32.xor(s23, S.play.b(c))), S.cnt(s01, s23), L, sym.n(S.cnt(s01, s23), 1n+S.cnt(U32.xor(s01, S.play.a(c)), U32.xor(s23, S.play.b(c))), take.go(U32.is_lt(C.card.suit(c), 2), S.play.x(c), s01, s23, i1, i2, one)), e_2), e_3))), (ed, ewl)))))
    case 2n 3n+y:
      Empty.absurd(S.Inv(R.play.go(2n, S.play.a(c), S.play.b(c), n01, n23, e01, e23, s01, s23, w01, w23, tr2, R.won.next(tr2, won)), p, L), no_lt0(y, lk))
    case 3n 0n:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls2, (+lk2, ((+e_0, (+e_1, (+e_2, +e_3))), (+ed, +ewl))))) = inv
      %Equal.sym(Nat, U32.to_nat(R.trick.seat(tr2)), 0n, es) : S.Inv.go(n01, n23, e01, e23, s01, s23, U32.xor(w01, S.play.a(c)), U32.xor(w23, S.play.b(c)), _, U32.to_nat(R.trick.played(tr2)), U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.trick.played(tr2)), 1n, cg(R.trick.played(tr2), U32.from_nat(1n), ep)) : S.Inv.go(n01, n23, e01, e23, s01, s23, U32.xor(w01, S.play.a(c)), U32.xor(w23, S.play.b(c)), 0n, _, U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.won.next(tr2, won)), U32.to_nat(won), cg(R.won.next(tr2, won), won, Laws.won_mid(0n, {==}, tr2, won, ep))) : S.Inv.go(n01, n23, e01, e23, s01, s23, U32.xor(w01, S.play.a(c)), U32.xor(w23, S.play.b(c)), 0n, 1n, _, p, L)
      ((v_n01, (v_n23, (v_e01, (v_e23, (v_s01, (v_s23, (Laws.xor_sub32(w01, S.play.a(c), S.valid.mask(), v_w01, i1), Laws.xor_sub32(w23, S.play.b(c), S.valid.mask(), v_w23, i2)))))))), ({==}, ({==}, ((e_0, (e_1, (e_2, tr.n(1n+S.cnt(U32.xor(w01, S.play.a(c)), U32.xor(w23, S.play.b(c))), S.cnt(w01, w23), L, sym.n(S.cnt(w01, w23), 1n+S.cnt(U32.xor(w01, S.play.a(c)), U32.xor(w23, S.play.b(c))), take.go(U32.is_lt(C.card.suit(c), 2), S.play.x(c), w01, w23, i1, i2, one)), e_3)))), (ed, ewl)))))
    case 3n 1n:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls2, (+lk2, ((+e_0, (+e_1, (+e_2, +e_3))), (+ed, +ewl))))) = inv
      %Equal.sym(Nat, U32.to_nat(R.trick.seat(tr2)), 0n, es) : S.Inv.go(n01, n23, e01, e23, s01, s23, U32.xor(w01, S.play.a(c)), U32.xor(w23, S.play.b(c)), _, U32.to_nat(R.trick.played(tr2)), U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.trick.played(tr2)), 2n, cg(R.trick.played(tr2), U32.from_nat(2n), ep)) : S.Inv.go(n01, n23, e01, e23, s01, s23, U32.xor(w01, S.play.a(c)), U32.xor(w23, S.play.b(c)), 0n, _, U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.won.next(tr2, won)), U32.to_nat(won), cg(R.won.next(tr2, won), won, Laws.won_mid(1n, {==}, tr2, won, ep))) : S.Inv.go(n01, n23, e01, e23, s01, s23, U32.xor(w01, S.play.a(c)), U32.xor(w23, S.play.b(c)), 0n, 2n, _, p, L)
      ((v_n01, (v_n23, (v_e01, (v_e23, (v_s01, (v_s23, (Laws.xor_sub32(w01, S.play.a(c), S.valid.mask(), v_w01, i1), Laws.xor_sub32(w23, S.play.b(c), S.valid.mask(), v_w23, i2)))))))), ({==}, ({==}, ((e_0, (e_1, (e_2, tr.n(1n+S.cnt(U32.xor(w01, S.play.a(c)), U32.xor(w23, S.play.b(c))), S.cnt(w01, w23), L, sym.n(S.cnt(w01, w23), 1n+S.cnt(U32.xor(w01, S.play.a(c)), U32.xor(w23, S.play.b(c))), take.go(U32.is_lt(C.card.suit(c), 2), S.play.x(c), w01, w23, i1, i2, one)), e_3)))), (ed, ewl)))))
    case 3n 2n:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls2, (+lk2, ((+e_0, (+e_1, (+e_2, +e_3))), (+ed, +ewl))))) = inv
      %Equal.sym(Nat, U32.to_nat(R.trick.seat(tr2)), 0n, es) : S.Inv.go(n01, n23, e01, e23, s01, s23, U32.xor(w01, S.play.a(c)), U32.xor(w23, S.play.b(c)), _, U32.to_nat(R.trick.played(tr2)), U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.trick.played(tr2)), 3n, cg(R.trick.played(tr2), U32.from_nat(3n), ep)) : S.Inv.go(n01, n23, e01, e23, s01, s23, U32.xor(w01, S.play.a(c)), U32.xor(w23, S.play.b(c)), 0n, _, U32.to_nat(R.won.next(tr2, won)), p, L)
      %Equal.sym(Nat, U32.to_nat(R.won.next(tr2, won)), U32.to_nat(won), cg(R.won.next(tr2, won), won, Laws.won_mid(2n, {==}, tr2, won, ep))) : S.Inv.go(n01, n23, e01, e23, s01, s23, U32.xor(w01, S.play.a(c)), U32.xor(w23, S.play.b(c)), 0n, 3n, _, p, L)
      ((v_n01, (v_n23, (v_e01, (v_e23, (v_s01, (v_s23, (Laws.xor_sub32(w01, S.play.a(c), S.valid.mask(), v_w01, i1), Laws.xor_sub32(w23, S.play.b(c), S.valid.mask(), v_w23, i2)))))))), ({==}, ({==}, ((e_0, (e_1, (e_2, tr.n(1n+S.cnt(U32.xor(w01, S.play.a(c)), U32.xor(w23, S.play.b(c))), S.cnt(w01, w23), L, sym.n(S.cnt(w01, w23), 1n+S.cnt(U32.xor(w01, S.play.a(c)), U32.xor(w23, S.play.b(c))), take.go(U32.is_lt(C.card.suit(c), 2), S.play.x(c), w01, w23, i1, i2, one)), e_3)))), (ed, ewl)))))
    case 3n 3n+y:
      Empty.absurd(S.Inv(R.play.go(3n, S.play.a(c), S.play.b(c), n01, n23, e01, e23, s01, s23, w01, w23, tr2, R.won.next(tr2, won)), p, L), no_lt0(y, lk))
    case 4n+y _:
      Empty.absurd(S.Inv(R.play.go(4n+y, S.play.a(c), S.play.b(c), n01, n23, e01, e23, s01, s23, w01, w23, tr2, R.won.next(tr2, won)), p, L), no_lt0(y, ls))


# The fourth card of a trick keeps the invariant: every hand has one card fewer,
# the winner leads, and the tricks won go up by one or not.

def end(+s: Nat, +p: Nat, +L: Nat, +c: U32, +n01: U32, +n23: U32, +e01: U32, +e23: U32, +s01: U32, +s23: U32, +w01: U32, +w23: U32, +tr2: U32, +won: U32,
    +inv: S.Inv.go(n01, n23, e01, e23, s01, s23, w01, w23, s, 3n, U32.to_nat(won), 1n+p, L),
    +ls: {Nat.is_lt(s, 4n) == True{} : Bool},
    +i1: S.Sub32(S.play.a(c), R.pick(s, n01, e01, s01, w01)), +i2: S.Sub32(S.play.b(c), R.pick(s, n23, e23, s23, w23)),
    +one: {S.bits(S.play.x(c)) == 1n : Nat},
    +ep: {R.trick.played(tr2) == 0 : U32}) ->
    S.Inv(R.play.go(s, S.play.a(c), S.play.b(c), n01, n23, e01, e23, s01, s23, w01, w23, tr2, R.won.next(tr2, won)), p, S.pred(L)):
  match s:
    case 0n:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls2, (+lk2, ((+e_0, (+e_1, (+e_2, +e_3))), (+ed, +ewl))))) = inv
      %Equal.sym(Nat, U32.to_nat(R.trick.played(tr2)), 0n, cg(R.trick.played(tr2), 0, ep)) : S.Inv.go(U32.xor(n01, S.play.a(c)), U32.xor(n23, S.play.b(c)), e01, e23, s01, s23, w01, w23, U32.to_nat(R.trick.seat(tr2)), _, U32.to_nat(R.won.next(tr2, won)), p, S.pred(L))
      %Equal.sym(Nat, U32.to_nat(R.won.next(tr2, won)), Nat.add(S.b2n(U32.is_eq((tr2 .&. 1 : U32), 0)), U32.to_nat(won)), Laws.won_end(tr2, won, ep, Laws.w_lt(U32.to_nat(won), L, S.cnt(w01, w23), e_3, ewl))) : S.Inv.go(U32.xor(n01, S.play.a(c)), U32.xor(n23, S.play.b(c)), e01, e23, s01, s23, w01, w23, U32.to_nat(R.trick.seat(tr2)), 0n, _, p, S.pred(L))
      ((Laws.xor_sub32(n01, S.play.a(c), S.valid.mask(), v_n01, i1), (Laws.xor_sub32(n23, S.play.b(c), S.valid.mask(), v_n23, i2), (v_e01, (v_e23, (v_s01, (v_s23, (v_w01, v_w23))))))), (Laws.and3_lt(tr2), ({==}, ((Equal.cong(Nat, Nat, (z => S.pred(z)), 1n+S.cnt(U32.xor(n01, S.play.a(c)), U32.xor(n23, S.play.b(c))), L, tr.n(1n+S.cnt(U32.xor(n01, S.play.a(c)), U32.xor(n23, S.play.b(c))), S.cnt(n01, n23), L, sym.n(S.cnt(n01, n23), 1n+S.cnt(U32.xor(n01, S.play.a(c)), U32.xor(n23, S.play.b(c))), take.go(U32.is_lt(C.card.suit(c), 2), S.play.x(c), n01, n23, i1, i2, one)), e_0)), (Equal.cong(Nat, Nat, (z => S.pred(z)), 1n+S.cnt(e01, e23), L, e_1), (Equal.cong(Nat, Nat, (z => S.pred(z)), 1n+S.cnt(s01, s23), L, e_2), Equal.cong(Nat, Nat, (z => S.pred(z)), 1n+S.cnt(w01, w23), L, e_3)))), (Laws.d_end(p, L, S.cnt(w01, w23), e_3, ed), Laws.w_end(U32.is_eq((tr2 .&. 1 : U32), 0), U32.to_nat(won), L, S.cnt(w01, w23), e_3, ewl))))))
    case 1n:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls2, (+lk2, ((+e_0, (+e_1, (+e_2, +e_3))), (+ed, +ewl))))) = inv
      %Equal.sym(Nat, U32.to_nat(R.trick.played(tr2)), 0n, cg(R.trick.played(tr2), 0, ep)) : S.Inv.go(n01, n23, U32.xor(e01, S.play.a(c)), U32.xor(e23, S.play.b(c)), s01, s23, w01, w23, U32.to_nat(R.trick.seat(tr2)), _, U32.to_nat(R.won.next(tr2, won)), p, S.pred(L))
      %Equal.sym(Nat, U32.to_nat(R.won.next(tr2, won)), Nat.add(S.b2n(U32.is_eq((tr2 .&. 1 : U32), 0)), U32.to_nat(won)), Laws.won_end(tr2, won, ep, Laws.w_lt(U32.to_nat(won), L, S.cnt(n01, n23), e_0, ewl))) : S.Inv.go(n01, n23, U32.xor(e01, S.play.a(c)), U32.xor(e23, S.play.b(c)), s01, s23, w01, w23, U32.to_nat(R.trick.seat(tr2)), 0n, _, p, S.pred(L))
      ((v_n01, (v_n23, (Laws.xor_sub32(e01, S.play.a(c), S.valid.mask(), v_e01, i1), (Laws.xor_sub32(e23, S.play.b(c), S.valid.mask(), v_e23, i2), (v_s01, (v_s23, (v_w01, v_w23))))))), (Laws.and3_lt(tr2), ({==}, ((Equal.cong(Nat, Nat, (z => S.pred(z)), 1n+S.cnt(n01, n23), L, e_0), (Equal.cong(Nat, Nat, (z => S.pred(z)), 1n+S.cnt(U32.xor(e01, S.play.a(c)), U32.xor(e23, S.play.b(c))), L, tr.n(1n+S.cnt(U32.xor(e01, S.play.a(c)), U32.xor(e23, S.play.b(c))), S.cnt(e01, e23), L, sym.n(S.cnt(e01, e23), 1n+S.cnt(U32.xor(e01, S.play.a(c)), U32.xor(e23, S.play.b(c))), take.go(U32.is_lt(C.card.suit(c), 2), S.play.x(c), e01, e23, i1, i2, one)), e_1)), (Equal.cong(Nat, Nat, (z => S.pred(z)), 1n+S.cnt(s01, s23), L, e_2), Equal.cong(Nat, Nat, (z => S.pred(z)), 1n+S.cnt(w01, w23), L, e_3)))), (Laws.d_end(p, L, S.cnt(n01, n23), e_0, ed), Laws.w_end(U32.is_eq((tr2 .&. 1 : U32), 0), U32.to_nat(won), L, S.cnt(n01, n23), e_0, ewl))))))
    case 2n:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls2, (+lk2, ((+e_0, (+e_1, (+e_2, +e_3))), (+ed, +ewl))))) = inv
      %Equal.sym(Nat, U32.to_nat(R.trick.played(tr2)), 0n, cg(R.trick.played(tr2), 0, ep)) : S.Inv.go(n01, n23, e01, e23, U32.xor(s01, S.play.a(c)), U32.xor(s23, S.play.b(c)), w01, w23, U32.to_nat(R.trick.seat(tr2)), _, U32.to_nat(R.won.next(tr2, won)), p, S.pred(L))
      %Equal.sym(Nat, U32.to_nat(R.won.next(tr2, won)), Nat.add(S.b2n(U32.is_eq((tr2 .&. 1 : U32), 0)), U32.to_nat(won)), Laws.won_end(tr2, won, ep, Laws.w_lt(U32.to_nat(won), L, S.cnt(e01, e23), e_1, ewl))) : S.Inv.go(n01, n23, e01, e23, U32.xor(s01, S.play.a(c)), U32.xor(s23, S.play.b(c)), w01, w23, U32.to_nat(R.trick.seat(tr2)), 0n, _, p, S.pred(L))
      ((v_n01, (v_n23, (v_e01, (v_e23, (Laws.xor_sub32(s01, S.play.a(c), S.valid.mask(), v_s01, i1), (Laws.xor_sub32(s23, S.play.b(c), S.valid.mask(), v_s23, i2), (v_w01, v_w23))))))), (Laws.and3_lt(tr2), ({==}, ((Equal.cong(Nat, Nat, (z => S.pred(z)), 1n+S.cnt(n01, n23), L, e_0), (Equal.cong(Nat, Nat, (z => S.pred(z)), 1n+S.cnt(e01, e23), L, e_1), (Equal.cong(Nat, Nat, (z => S.pred(z)), 1n+S.cnt(U32.xor(s01, S.play.a(c)), U32.xor(s23, S.play.b(c))), L, tr.n(1n+S.cnt(U32.xor(s01, S.play.a(c)), U32.xor(s23, S.play.b(c))), S.cnt(s01, s23), L, sym.n(S.cnt(s01, s23), 1n+S.cnt(U32.xor(s01, S.play.a(c)), U32.xor(s23, S.play.b(c))), take.go(U32.is_lt(C.card.suit(c), 2), S.play.x(c), s01, s23, i1, i2, one)), e_2)), Equal.cong(Nat, Nat, (z => S.pred(z)), 1n+S.cnt(w01, w23), L, e_3)))), (Laws.d_end(p, L, S.cnt(e01, e23), e_1, ed), Laws.w_end(U32.is_eq((tr2 .&. 1 : U32), 0), U32.to_nat(won), L, S.cnt(e01, e23), e_1, ewl))))))
    case 3n:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls2, (+lk2, ((+e_0, (+e_1, (+e_2, +e_3))), (+ed, +ewl))))) = inv
      %Equal.sym(Nat, U32.to_nat(R.trick.played(tr2)), 0n, cg(R.trick.played(tr2), 0, ep)) : S.Inv.go(n01, n23, e01, e23, s01, s23, U32.xor(w01, S.play.a(c)), U32.xor(w23, S.play.b(c)), U32.to_nat(R.trick.seat(tr2)), _, U32.to_nat(R.won.next(tr2, won)), p, S.pred(L))
      %Equal.sym(Nat, U32.to_nat(R.won.next(tr2, won)), Nat.add(S.b2n(U32.is_eq((tr2 .&. 1 : U32), 0)), U32.to_nat(won)), Laws.won_end(tr2, won, ep, Laws.w_lt(U32.to_nat(won), L, S.cnt(s01, s23), e_2, ewl))) : S.Inv.go(n01, n23, e01, e23, s01, s23, U32.xor(w01, S.play.a(c)), U32.xor(w23, S.play.b(c)), U32.to_nat(R.trick.seat(tr2)), 0n, _, p, S.pred(L))
      ((v_n01, (v_n23, (v_e01, (v_e23, (v_s01, (v_s23, (Laws.xor_sub32(w01, S.play.a(c), S.valid.mask(), v_w01, i1), Laws.xor_sub32(w23, S.play.b(c), S.valid.mask(), v_w23, i2)))))))), (Laws.and3_lt(tr2), ({==}, ((Equal.cong(Nat, Nat, (z => S.pred(z)), 1n+S.cnt(n01, n23), L, e_0), (Equal.cong(Nat, Nat, (z => S.pred(z)), 1n+S.cnt(e01, e23), L, e_1), (Equal.cong(Nat, Nat, (z => S.pred(z)), 1n+S.cnt(s01, s23), L, e_2), Equal.cong(Nat, Nat, (z => S.pred(z)), 1n+S.cnt(U32.xor(w01, S.play.a(c)), U32.xor(w23, S.play.b(c))), L, tr.n(1n+S.cnt(U32.xor(w01, S.play.a(c)), U32.xor(w23, S.play.b(c))), S.cnt(w01, w23), L, sym.n(S.cnt(w01, w23), 1n+S.cnt(U32.xor(w01, S.play.a(c)), U32.xor(w23, S.play.b(c))), take.go(U32.is_lt(C.card.suit(c), 2), S.play.x(c), w01, w23, i1, i2, one)), e_3))))), (Laws.d_end(p, L, S.cnt(s01, s23), e_2, ed), Laws.w_end(U32.is_eq((tr2 .&. 1 : U32), 0), U32.to_nat(won), L, S.cnt(s01, s23), e_2, ewl))))))
    case 4n+y:
      Empty.absurd(S.Inv(R.play.go(4n+y, S.play.a(c), S.play.b(c), n01, n23, e01, e23, s01, s23, w01, w23, tr2, R.won.next(tr2, won)), p, S.pred(L)), no_lt0(y, ls))

def eq_of_nat(+x: U32, +k: Nat, +e: {U32.to_nat(x) == k : Nat}) -> {x == U32.from_nat(k) : U32}:
  %e : {x == U32.from_nat(_) : U32}
  Equal.sym(U32, U32.from_nat(U32.to_nat(x)), x, Laws.u32_roundtrip(x))

def nx_ok(+s: Nat, +ls: {Nat.is_lt(s, 4n) == True{} : Bool}) -> {U32.to_nat(U32.and((U32.from_nat(s) + 1 : U32), 3)) == nx(s) : Nat}:
  match s:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n+y:
      Empty.absurd({U32.to_nat(U32.and((U32.from_nat(4n+y) + 1 : U32), 3)) == nx(4n+y) : Nat}, no_lt0(y, ls))

def play_inv.go(+s: Nat, +k: Nat, +t: U32, +c: U32, +p: Nat, +L: Nat, +n01: U32, +n23: U32, +e01: U32, +e23: U32, +s01: U32, +s23: U32, +w01: U32, +w23: U32, +tr: U32, +won: U32,
    +es: {U32.to_nat(R.trick.seat(tr)) == s : Nat}, +ek: {U32.to_nat(R.trick.played(tr)) == k : Nat},
    +inv: S.Inv.go(n01, n23, e01, e23, s01, s23, w01, w23, s, k, U32.to_nat(won), 1n+p, L),
    +i1: S.Sub32(S.play.a(c), R.pick(s, n01, e01, s01, w01)), +i2: S.Sub32(S.play.b(c), R.pick(s, n23, e23, s23, w23)),
    +one: {S.bits(S.play.x(c)) == 1n : Nat}) ->
    S.Inv(R.play.go(s, S.play.a(c), S.play.b(c), n01, n23, e01, e23, s01, s23, w01, w23, R.trick.next(tr, t, c), R.won.next(R.trick.next(tr, t, c), won)), p, S.lnext(k, L)):
  match k:
    case 0n:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls, (+lk, (+ev, (+ed, +ewl))))) = inv
      mid(s, 0n, p, L, c, n01, n23, e01, e23, s01, s23, w01, w23, R.trick.next(tr, t, c), won, inv, ls, {==}, i1, i2, one,
        tr.n(U32.to_nat(R.trick.seat(R.trick.next(tr, t, c))), U32.to_nat(U32.and((R.trick.seat(tr) + 1 : U32), 3)), nx(s),
          cg(R.trick.seat(R.trick.next(tr, t, c)), U32.and((R.trick.seat(tr) + 1 : U32), 3), Laws.seat_mid(0n, {==}, tr, t, c, eq_of_nat(R.trick.played(tr), 0n, ek))),
          tr.n(U32.to_nat(U32.and((R.trick.seat(tr) + 1 : U32), 3)), U32.to_nat(U32.and((U32.from_nat(s) + 1 : U32), 3)), nx(s),
            Equal.cong(U32, Nat, (z => U32.to_nat(U32.and((z + 1 : U32), 3))), R.trick.seat(tr), U32.from_nat(s), eq_of_nat(R.trick.seat(tr), s, es)),
            nx_ok(s, ls))),
        Laws.played_mid(0n, {==}, tr, t, c, eq_of_nat(R.trick.played(tr), 0n, ek)))
    case 1n:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls, (+lk, (+ev, (+ed, +ewl))))) = inv
      mid(s, 1n, p, L, c, n01, n23, e01, e23, s01, s23, w01, w23, R.trick.next(tr, t, c), won, inv, ls, {==}, i1, i2, one,
        tr.n(U32.to_nat(R.trick.seat(R.trick.next(tr, t, c))), U32.to_nat(U32.and((R.trick.seat(tr) + 1 : U32), 3)), nx(s),
          cg(R.trick.seat(R.trick.next(tr, t, c)), U32.and((R.trick.seat(tr) + 1 : U32), 3), Laws.seat_mid(1n, {==}, tr, t, c, eq_of_nat(R.trick.played(tr), 1n, ek))),
          tr.n(U32.to_nat(U32.and((R.trick.seat(tr) + 1 : U32), 3)), U32.to_nat(U32.and((U32.from_nat(s) + 1 : U32), 3)), nx(s),
            Equal.cong(U32, Nat, (z => U32.to_nat(U32.and((z + 1 : U32), 3))), R.trick.seat(tr), U32.from_nat(s), eq_of_nat(R.trick.seat(tr), s, es)),
            nx_ok(s, ls))),
        Laws.played_mid(1n, {==}, tr, t, c, eq_of_nat(R.trick.played(tr), 1n, ek)))
    case 2n:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls, (+lk, (+ev, (+ed, +ewl))))) = inv
      mid(s, 2n, p, L, c, n01, n23, e01, e23, s01, s23, w01, w23, R.trick.next(tr, t, c), won, inv, ls, {==}, i1, i2, one,
        tr.n(U32.to_nat(R.trick.seat(R.trick.next(tr, t, c))), U32.to_nat(U32.and((R.trick.seat(tr) + 1 : U32), 3)), nx(s),
          cg(R.trick.seat(R.trick.next(tr, t, c)), U32.and((R.trick.seat(tr) + 1 : U32), 3), Laws.seat_mid(2n, {==}, tr, t, c, eq_of_nat(R.trick.played(tr), 2n, ek))),
          tr.n(U32.to_nat(U32.and((R.trick.seat(tr) + 1 : U32), 3)), U32.to_nat(U32.and((U32.from_nat(s) + 1 : U32), 3)), nx(s),
            Equal.cong(U32, Nat, (z => U32.to_nat(U32.and((z + 1 : U32), 3))), R.trick.seat(tr), U32.from_nat(s), eq_of_nat(R.trick.seat(tr), s, es)),
            nx_ok(s, ls))),
        Laws.played_mid(2n, {==}, tr, t, c, eq_of_nat(R.trick.played(tr), 2n, ek)))
    case 3n:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls, (+lk, (+ev, (+ed, +ewl))))) = inv
      end(s, p, L, c, n01, n23, e01, e23, s01, s23, w01, w23, R.trick.next(tr, t, c), won, inv, ls, i1, i2, one, Laws.played_end(tr, t, c, eq_of_nat(R.trick.played(tr), 3n, ek)))
    case 4n+y:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls, (+lk, (+ev, (+ed, +ewl))))) = inv
      Empty.absurd(S.Inv(R.play.go(s, S.play.a(c), S.play.b(c), n01, n23, e01, e23, s01, s23, w01, w23, R.trick.next(tr, t, c), R.won.next(R.trick.next(tr, t, c), won)), p, S.lnext(4n+y, L)), no_lt0(y, lk))

# Playing a card of the hand to play keeps the invariant, with one ply fewer.

def Laws.play_inv(t, c, p, L, n01, n23, e01, e23, s01, s23, w01, w23, tr, won, inv, i1, i2, one):
  play_inv.go(U32.to_nat(R.trick.seat(tr)), U32.to_nat(R.trick.played(tr)), t, c, p, L, n01, n23, e01, e23, s01, s23, w01, w23, tr, won, {==}, {==}, inv, i1, i2, one)

def dz(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+m:
      Empty

def no_zs(-m: Nat, e: {0n == 1n+m : Nat}) -> Empty:
  %e : dz(_)
  Unit{}

def pick_valid(+s: Nat, +a: U32, +b: U32, +c: U32, +d: U32, +va: S.V(a), +vb: S.V(b), +vc: S.V(c), +vd: S.V(d)) -> S.V(R.pick(s, a, b, c, d)):
  match s:
    case 0n:
      va
    case 1n:
      vb
    case 2n:
      vc
    case 3n+y:
      vd

def pick_cnt(+s: Nat, +n01: U32, +n23: U32, +e01: U32, +e23: U32, +s01: U32, +s23: U32, +w01: U32, +w23: U32) -> {S.cnt(R.pick(s, n01, e01, s01, w01), R.pick(s, n23, e23, s23, w23)) == S.pickn(s, S.cnt(n01, n23), S.cnt(e01, e23), S.cnt(s01, s23), S.cnt(w01, w23)) : Nat}:
  match s:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+y:
      {==}

# The seat to play has not played to the trick, so it holds L cards.

def Laws.even_self(s, k, L, a, b, c, d, ev, ls, lk):
  match s k:
    case 0n 0n:
      (+e_0, (+e_1, (+e_2, +e_3))) = ev
      e_0
    case 0n 1n:
      (+e_0, (+e_1, (+e_2, +e_3))) = ev
      e_0
    case 0n 2n:
      (+e_0, (+e_1, (+e_2, +e_3))) = ev
      e_0
    case 0n 3n:
      (+e_0, (+e_1, (+e_2, +e_3))) = ev
      e_0
    case 0n 4n+y:
      Empty.absurd({S.pickn(0n, a, b, c, d) == L : Nat}, no_lt0(y, lk))
    case 1n 0n:
      (+e_0, (+e_1, (+e_2, +e_3))) = ev
      e_1
    case 1n 1n:
      (+e_0, (+e_1, (+e_2, +e_3))) = ev
      e_1
    case 1n 2n:
      (+e_0, (+e_1, (+e_2, +e_3))) = ev
      e_1
    case 1n 3n:
      (+e_0, (+e_1, (+e_2, +e_3))) = ev
      e_1
    case 1n 4n+y:
      Empty.absurd({S.pickn(1n, a, b, c, d) == L : Nat}, no_lt0(y, lk))
    case 2n 0n:
      (+e_0, (+e_1, (+e_2, +e_3))) = ev
      e_2
    case 2n 1n:
      (+e_0, (+e_1, (+e_2, +e_3))) = ev
      e_2
    case 2n 2n:
      (+e_0, (+e_1, (+e_2, +e_3))) = ev
      e_2
    case 2n 3n:
      (+e_0, (+e_1, (+e_2, +e_3))) = ev
      e_2
    case 2n 4n+y:
      Empty.absurd({S.pickn(2n, a, b, c, d) == L : Nat}, no_lt0(y, lk))
    case 3n 0n:
      (+e_0, (+e_1, (+e_2, +e_3))) = ev
      e_3
    case 3n 1n:
      (+e_0, (+e_1, (+e_2, +e_3))) = ev
      e_3
    case 3n 2n:
      (+e_0, (+e_1, (+e_2, +e_3))) = ev
      e_3
    case 3n 3n:
      (+e_0, (+e_1, (+e_2, +e_3))) = ev
      e_3
    case 3n 4n+y:
      Empty.absurd({S.pickn(3n, a, b, c, d) == L : Nat}, no_lt0(y, lk))
    case 4n+y _:
      Empty.absurd({S.pickn(4n+y, a, b, c, d) == L : Nat}, no_lt0(y, ls))

def ne.hi(+b: Bool, +lead: U32, +h01: U32, +h23: U32, +x: Nat, +eb: {U32.is_zero(h23) == b : Bool}, +e: {S.bits(h23) == 1n+x : Nat}) -> S.NE(R.moves.of(lead, h01, h23)):
  match b:
    case False{}:
      Laws.moves_ne23(lead, h01, h23, eb)
    case True{}:
      Empty.absurd(S.NE(R.moves.of(lead, h01, h23)), no_zs(x, tr.n(0n, S.bits(h23), 1n+x, Equal.cong(U32, Nat, (z => S.bits(z)), 0, h23, Equal.sym(U32, h23, 0, zero.of(h23, eb))), e)))

def ne.lo(+b: Bool, +lead: U32, +h01: U32, +h23: U32, +x: Nat, +eb: {U32.is_zero(h01) == b : Bool}, +e: {S.cnt(h01, h23) == 1n+x : Nat}) -> S.NE(R.moves.of(lead, h01, h23)):
  match b:
    case False{}:
      Laws.moves_ne01(lead, h01, h23, eb)
    case True{}:
      ne.hi(U32.is_zero(h23), lead, h01, h23, x, {==}, tr.n(S.bits(h23), S.cnt(h01, h23), 1n+x, Equal.cong(U32, Nat, (z => S.cnt(z, h23)), 0, h01, Equal.sym(U32, h01, 0, zero.of(h01, eb))), e))

# A hand with a card has a move.

def Laws.ne_cnt(lead, h01, h23, x, e):
  ne.lo(U32.is_zero(h01), lead, h01, h23, x, {==}, e)

def succ_pred(+L: Nat, +m: Nat, +e: {1n+m == S.r4(L) : Nat}) -> {1n+S.pred(L) == L : Nat}:
  match L:
    case 0n:
      Empty.absurd({1n+S.pred(0n) == 0n : Nat}, no_zs(m, Equal.sym(Nat, 1n+m, 0n, e)))
    case 1n+y:
      {==}

# A position's moves: from its hand, and some while cards are left.

def Laws.kid_hand(pos, p, L, ci):
  match pos:
    case R.Pos{+n01, +n23, +e01, +e23, +s01, +s23, +w01, +w23, +tr, +won}:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls, (+lk, (+ev, (+ed, +ewl))))) = ci
      Laws.moves_hand(R.trick.lead(tr), R.pick(U32.to_nat(R.trick.seat(tr)), n01, e01, s01, w01), R.pick(U32.to_nat(R.trick.seat(tr)), n23, e23, s23, w23),
        pick_valid(U32.to_nat(R.trick.seat(tr)), n01, e01, s01, w01, v_n01, v_e01, v_s01, v_w01),
        pick_valid(U32.to_nat(R.trick.seat(tr)), n23, e23, s23, w23, v_n23, v_e23, v_s23, v_w23))

def Laws.kid_h(pos, p, L, ci):
  match pos:
    case R.Pos{+n01, +n23, +e01, +e23, +s01, +s23, +w01, +w23, +tr, +won}:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls, (+lk, (+ev, (+ed, +ewl))))) = ci
      ewl

def Laws.kid_vin(pos, p, L, ns, ci):
  match pos p:
    case R.Pos{+n01, +n23, +e01, +e23, +s01, +s23, +w01, +w23, +tr, +won} 0n:
      Unit{}
    case R.Pos{+n01, +n23, +e01, +e23, +s01, +s23, +w01, +w23, +tr, +won} 1n+q:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls, (+lk, (+ev, (+ed, +ewl))))) = ci
      Inl{(Laws.ne_cnt(R.trick.lead(tr), R.pick(U32.to_nat(R.trick.seat(tr)), n01, e01, s01, w01), R.pick(U32.to_nat(R.trick.seat(tr)), n23, e23, s23, w23), S.pred(L),
          tr.n(S.cnt(R.pick(U32.to_nat(R.trick.seat(tr)), n01, e01, s01, w01), R.pick(U32.to_nat(R.trick.seat(tr)), n23, e23, s23, w23)), L, 1n+S.pred(L),
            tr.n(S.cnt(R.pick(U32.to_nat(R.trick.seat(tr)), n01, e01, s01, w01), R.pick(U32.to_nat(R.trick.seat(tr)), n23, e23, s23, w23)), S.pickn(U32.to_nat(R.trick.seat(tr)), S.cnt(n01, n23), S.cnt(e01, e23), S.cnt(s01, s23), S.cnt(w01, w23)), L,
              pick_cnt(U32.to_nat(R.trick.seat(tr)), n01, n23, e01, e23, s01, s23, w01, w23),
              Laws.even_self(U32.to_nat(R.trick.seat(tr)), U32.to_nat(R.trick.played(tr)), L, S.cnt(n01, n23), S.cnt(e01, e23), S.cnt(s01, s23), S.cnt(w01, w23), ev, ls, lk)),
            sym.n(1n+S.pred(L), L, succ_pred(L, Nat.add(U32.to_nat(R.trick.played(tr)), q), tr.n(1n+Nat.add(U32.to_nat(R.trick.played(tr)), q), Nat.add(U32.to_nat(R.trick.played(tr)), 1n+q), S.r4(L), sym.n(Nat.add(U32.to_nat(R.trick.played(tr)), 1n+q), 1n+Nat.add(U32.to_nat(R.trick.played(tr)), q), Laws.add_succ(U32.to_nat(R.trick.played(tr)), q)), ed))))),
        Laws.ok_seed(ns, U32.to_nat(won), L, ewl))}

def go_won(+s: Nat, +a: U32, +b: U32, +n01: U32, +n23: U32, +e01: U32, +e23: U32, +s01: U32, +s23: U32, +w01: U32, +w23: U32, +tr2: U32, +won2: U32) -> {R.pos.won(R.play.go(s, a, b, n01, n23, e01, e23, s01, s23, w01, w23, tr2, won2)) == won2 : U32}:
  match s:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+y:
      {==}

def inr_eq(+x: U32, +a: Nat, +b: Nat, +L: Nat, +e: {a == b : Nat}, +i: S.InR(x, a, L)) -> S.InR(x, b, L):
  %e : S.InR(x, _, L)
  i

def le.to(+a: Nat, -b: Nat, -c: Nat, e: {b == c : Nat}, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(a, c), Nat.is_le(a, b), True{}, Equal.cong(Nat, Bool, (z => Nat.is_le(a, z)), c, b, sym.n(b, c, e)), h)

# A child's range after a trick sits inside its parent's.

def Laws.widen_end(x, bb, w, L, y, e1, i):
  match bb:
    case False{}:
      (+lo, +hi) = i
      %e1 : S.InR(x, w, _)
      (lo, Laws.le_trans(U32.to_nat(x), Nat.add(w, y), Nat.add(w, 1n+y),
        le.to(U32.to_nat(x), Nat.add(w, S.pred(L)), Nat.add(w, y), Equal.cong(Nat, Nat, (z => Nat.add(w, S.pred(z))), L, 1n+y, sym.n(1n+y, L, e1)), hi),
        le.to(Nat.add(w, y), 1n+Nat.add(w, y), Nat.add(w, 1n+y), sym.n(Nat.add(w, 1n+y), 1n+Nat.add(w, y), Laws.add_succ(w, y)), Laws.le_succ(Nat.add(w, y), Nat.add(w, y), Laws.le_refl(Nat.add(w, y))))))
    case True{}:
      (+lo, +hi) = i
      %e1 : S.InR(x, w, _)
      (Laws.le_trans(w, 1n+w, U32.to_nat(x), Laws.le_succ(w, w, Laws.le_refl(w)), lo),
        le.to(U32.to_nat(x), 1n+Nat.add(w, S.pred(L)), Nat.add(w, 1n+y),
          tr.n(1n+Nat.add(w, S.pred(L)), 1n+Nat.add(w, y), Nat.add(w, 1n+y), Equal.cong(Nat, Nat, (z => 1n+Nat.add(w, S.pred(z))), L, 1n+y, sym.n(1n+y, L, e1)), sym.n(Nat.add(w, 1n+y), 1n+Nat.add(w, y), Laws.add_succ(w, y))), hi))

def widen.go(+k: Nat, +t: U32, +c: U32, +p: Nat, +L: Nat, +n01: U32, +n23: U32, +e01: U32, +e23: U32, +s01: U32, +s23: U32, +w01: U32, +w23: U32, +tr: U32, +won: U32,
    +ek: {U32.to_nat(R.trick.played(tr)) == k : Nat},
    +inv: S.Inv.go(n01, n23, e01, e23, s01, s23, w01, w23, U32.to_nat(R.trick.seat(tr)), k, U32.to_nat(won), 1n+p, L),
    +x: U32, +i: S.InR(x, S.wN(R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c)), S.lnext(k, L))) -> S.InR(x, U32.to_nat(won), L):
  match k:
    case 0n:
      inr_eq(x, S.wN(R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c)), U32.to_nat(won), L,
        tr.n(S.wN(R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c)), U32.to_nat(R.won.next(R.trick.next(tr, t, c), won)), U32.to_nat(won),
          cg(R.pos.won(R.play.go(U32.to_nat(R.trick.seat(tr)), S.play.a(c), S.play.b(c), n01, n23, e01, e23, s01, s23, w01, w23, R.trick.next(tr, t, c), R.won.next(R.trick.next(tr, t, c), won))), R.won.next(R.trick.next(tr, t, c), won), go_won(U32.to_nat(R.trick.seat(tr)), S.play.a(c), S.play.b(c), n01, n23, e01, e23, s01, s23, w01, w23, R.trick.next(tr, t, c), R.won.next(R.trick.next(tr, t, c), won))),
          cg(R.won.next(R.trick.next(tr, t, c), won), won, Laws.won_mid(0n, {==}, R.trick.next(tr, t, c), won, Laws.played_mid(0n, {==}, tr, t, c, eq_of_nat(R.trick.played(tr), 0n, ek))))), i)
    case 1n:
      inr_eq(x, S.wN(R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c)), U32.to_nat(won), L,
        tr.n(S.wN(R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c)), U32.to_nat(R.won.next(R.trick.next(tr, t, c), won)), U32.to_nat(won),
          cg(R.pos.won(R.play.go(U32.to_nat(R.trick.seat(tr)), S.play.a(c), S.play.b(c), n01, n23, e01, e23, s01, s23, w01, w23, R.trick.next(tr, t, c), R.won.next(R.trick.next(tr, t, c), won))), R.won.next(R.trick.next(tr, t, c), won), go_won(U32.to_nat(R.trick.seat(tr)), S.play.a(c), S.play.b(c), n01, n23, e01, e23, s01, s23, w01, w23, R.trick.next(tr, t, c), R.won.next(R.trick.next(tr, t, c), won))),
          cg(R.won.next(R.trick.next(tr, t, c), won), won, Laws.won_mid(1n, {==}, R.trick.next(tr, t, c), won, Laws.played_mid(1n, {==}, tr, t, c, eq_of_nat(R.trick.played(tr), 1n, ek))))), i)
    case 2n:
      inr_eq(x, S.wN(R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c)), U32.to_nat(won), L,
        tr.n(S.wN(R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c)), U32.to_nat(R.won.next(R.trick.next(tr, t, c), won)), U32.to_nat(won),
          cg(R.pos.won(R.play.go(U32.to_nat(R.trick.seat(tr)), S.play.a(c), S.play.b(c), n01, n23, e01, e23, s01, s23, w01, w23, R.trick.next(tr, t, c), R.won.next(R.trick.next(tr, t, c), won))), R.won.next(R.trick.next(tr, t, c), won), go_won(U32.to_nat(R.trick.seat(tr)), S.play.a(c), S.play.b(c), n01, n23, e01, e23, s01, s23, w01, w23, R.trick.next(tr, t, c), R.won.next(R.trick.next(tr, t, c), won))),
          cg(R.won.next(R.trick.next(tr, t, c), won), won, Laws.won_mid(2n, {==}, R.trick.next(tr, t, c), won, Laws.played_mid(2n, {==}, tr, t, c, eq_of_nat(R.trick.played(tr), 2n, ek))))), i)
    case 3n:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls, (+lk, (+ev, (+ed, +ewl))))) = inv
      Laws.widen_end(x, U32.is_eq((R.trick.next(tr, t, c) .&. 1 : U32), 0), U32.to_nat(won), L, S.pred(L), succ_pred(L, 3n+p, ed),
        inr_eq(x, S.wN(R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c)), Nat.add(S.b2n(U32.is_eq((R.trick.next(tr, t, c) .&. 1 : U32), 0)), U32.to_nat(won)), S.pred(L),
          tr.n(S.wN(R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c)), U32.to_nat(R.won.next(R.trick.next(tr, t, c), won)), Nat.add(S.b2n(U32.is_eq((R.trick.next(tr, t, c) .&. 1 : U32), 0)), U32.to_nat(won)),
            cg(R.pos.won(R.play.go(U32.to_nat(R.trick.seat(tr)), S.play.a(c), S.play.b(c), n01, n23, e01, e23, s01, s23, w01, w23, R.trick.next(tr, t, c), R.won.next(R.trick.next(tr, t, c), won))), R.won.next(R.trick.next(tr, t, c), won), go_won(U32.to_nat(R.trick.seat(tr)), S.play.a(c), S.play.b(c), n01, n23, e01, e23, s01, s23, w01, w23, R.trick.next(tr, t, c), R.won.next(R.trick.next(tr, t, c), won))),
            Laws.won_end(R.trick.next(tr, t, c), won, Laws.played_end(tr, t, c, eq_of_nat(R.trick.played(tr), 3n, ek)), Laws.w_lt(U32.to_nat(won), L, S.pred(L), succ_pred(L, 3n+p, ed), ewl))), i))
    case 4n+y:
      ((+v_n01, (+v_n23, (+v_e01, (+v_e23, (+v_s01, (+v_s23, (+v_w01, +v_w23))))))), (+ls, (+lk, (+ev, (+ed, +ewl))))) = inv
      Empty.absurd(S.InR(x, U32.to_nat(won), L), no_lt0(y, lk))

def widen(+t: U32, +c: U32, +p: Nat, +L: Nat, +n01: U32, +n23: U32, +e01: U32, +e23: U32, +s01: U32, +s23: U32, +w01: U32, +w23: U32, +tr: U32, +won: U32,
    +inv: S.Inv.go(n01, n23, e01, e23, s01, s23, w01, w23, U32.to_nat(R.trick.seat(tr)), U32.to_nat(R.trick.played(tr)), U32.to_nat(won), 1n+p, L),
    +x: U32, +i: S.InR(x, S.wN(R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c)), S.lnext(U32.to_nat(R.trick.played(tr)), L))) -> S.InR(x, U32.to_nat(won), L):
  widen.go(U32.to_nat(R.trick.played(tr)), t, c, p, L, n01, n23, e01, e23, s01, s23, w01, w23, tr, won, {==}, inv, x, i)

def ok_vin(+ns: Bool, +v: U32, +w: Nat, +L: Nat, -A: Type, vin: (A & S.Ok(ns, v, w, L)) | S.InR(v, w, L)) -> S.Ok(ns, v, w, L):
  match vin:
    case Inl{x}:
      (a, o) = x
      o
    case Inr{i}:
      Laws.ok_in(ns, v, w, L, i)

# The value the brute force search gives lies between the tricks won and those
# plus the tricks left, in every position that keeps the invariant: whatever the
# cards, the trick so far and the side to play.

def Laws.search_in(d, ms, t, pos, ns, best, r, L, inv, hand, bok, vin):
  match d ms pos r:
    case 0n _ R.Pos{+n01, +n23, +e01, +e23, +s01, +s23, +w01, +w23, +tr, +won} B.Res{_, n}:
      (Laws.le_refl(U32.to_nat(won)), Laws.le_add(U32.to_nat(won), L))
    case 1n+p Nil{} R.Pos{+n01, +n23, +e01, +e23, +s01, +s23, +w01, +w23, +tr, +won} B.Res{+v, n}:
      match vin:
        case Inl{x}:
          (ne, o) = x
          Empty.absurd(S.InR(B.better(ns, best, v), U32.to_nat(won), L), ne)
        case Inr{i}:
          Laws.in_better(ns, best, v, U32.to_nat(won), L, bok, i)
    case 1n+p Con{+c, +rest} R.Pos{+n01, +n23, +e01, +e23, +s01, +s23, +w01, +w23, +tr, +won} B.Res{+v, +n}:
      ((+i1, (+i2, (+one, +cok))), hrest) = hand
      +ci = Laws.play_inv(t, c, p, L, n01, n23, e01, e23, s01, s23, w01, w23, tr, won, inv, i1, i2, one)
      +cns = R.pos.ns(R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c))
      +L2 = S.lnext(U32.to_nat(R.trick.played(tr)), L)
      Laws.search_in(1n+p, rest, t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, ns, B.better(ns, best, v),
        B.search(p, R.moves(R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c)), t, R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c), cns, B.seed(cns), B.Res{B.seed(cns), 1n+n}), L, inv, hrest,
        Laws.ok_better(ns, best, v, U32.to_nat(won), L, bok, ok_vin(ns, v, U32.to_nat(won), L, S.NE(Con{c, rest}), vin)),
        Inr{widen(t, c, p, L, n01, n23, e01, e23, s01, s23, w01, w23, tr, won, inv, S.rv(B.search(p, R.moves(R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c)), t, R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c), cns, B.seed(cns), B.Res{B.seed(cns), 1n+n})),
          Laws.search_in(p, R.moves(R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c)), t, R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c), cns, B.seed(cns), B.Res{B.seed(cns), 1n+n}, L2, ci,
            Laws.kid_hand(R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c), p, L2, ci), Laws.ok_seed(cns, S.wN(R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c)), L2, Laws.kid_h(R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c), p, L2, ci)), Laws.kid_vin(R.play(t, R.Pos{n01, n23, e01, e23, s01, s23, w01, w23, tr, won}, c), p, L2, cns, ci)))})

# The same from the root: what B.solve gives for a position that keeps the
# invariant is between the tricks won and those plus the tricks left.

def Laws.solve_in(d, t, pos, nodes, L, inv):
  Laws.search_in(d, R.moves(pos), t, pos, R.pos.ns(pos), B.seed(R.pos.ns(pos)), B.Res{B.seed(R.pos.ns(pos)), nodes}, L, inv,
    Laws.kid_hand(pos, d, L, inv), Laws.ok_seed(R.pos.ns(pos), S.wN(pos), L, Laws.kid_h(pos, d, L, inv)), Laws.kid_vin(pos, d, L, R.pos.ns(pos), inv))

# ---------------------------------------------------------------------------
# A dealt position

def start.played(+leader: U32, +el: {U32.and(leader, 3) == leader : U32}) -> {U32.to_nat(R.trick.played(R.trick.start(leader))) == 0n : Nat}:
  %el : {U32.to_nat(R.trick.played(R.trick.make(_, 0, 4, 0, 0))) == 0n : Nat}
  cg(R.trick.played(R.trick.make(U32.and(leader, 3), 0, 4, 0, 0)), 0, Laws.played_make(0n, {==}, leader, 4, 0, 0))

# Any deal of L cards to each hand, with any leader, starts out keeping the invariant.

def Laws.start_inv(deal, leader, L, ok, el, lL):
  match deal:
    case C.Deal{+n, +e, +s, +w}:
      ((+vn01, (+vn23, +cn)), ((+ve01, (+ve23, +ce)), ((+vs01, (+vs23, +cs)), (+vw01, (+vw23, +cw))))) = ok
      %Equal.sym(Nat, U32.to_nat(R.trick.played(R.trick.start(leader))), 0n, start.played(leader, el)) : S.Inv.go(R.hand.pack01(n), R.hand.pack23(n), R.hand.pack01(e), R.hand.pack23(e), R.hand.pack01(s), R.hand.pack23(s), R.hand.pack01(w), R.hand.pack23(w), U32.to_nat(R.trick.seat(R.trick.start(leader))), _, U32.to_nat(0), S.r4(L), L)
      ((vn01, (vn23, (ve01, (ve23, (vs01, (vs23, (vw01, vw23))))))), (Laws.and3_lt(R.trick.start(leader)), ({==}, ((cn, (ce, (cs, cw))), ({==}, lL)))))

# So the brute force value of any such deal is between 0 and L.

def Laws.solve_deal(deal, leader, L, t, nodes, ok, el, lL):
  match deal:
    case C.Deal{+n, +e, +s, +w}:
      Laws.solve_in(S.r4(L), t, R.pos.start(C.Deal{n, e, s, w}, leader), nodes, L, Laws.start_inv(C.Deal{n, e, s, w}, leader, L, ok, el, lL))


# ---------------------------------------------------------------------------
# Toward the sure tricks: lower bounds through the search, and every card a move

def lt.nat2(+a: U32, +b: U32, +c: Bool, e: {U32.is_lt(a, b) == c : Bool}) -> {Cmp.is_lt(Nat.cmp(U32.to_nat(a), U32.to_nat(b))) == c : Bool}:
  %Laws.u32_cmp_nat(a, b) : {Cmp.is_lt(_) == c : Bool}
  e

def maxge.go(+c: Bool, +a: U32, +b: U32, +e: {Cmp.is_lt(Nat.cmp(U32.to_nat(a), U32.to_nat(b))) == c : Bool}) -> S.And({Nat.is_le(U32.to_nat(a), U32.to_nat(Bool.pick(U32, c, b, a))) == True{} : Bool}, {Nat.is_le(U32.to_nat(b), U32.to_nat(Bool.pick(U32, c, b, a))) == True{} : Bool}):
  match c:
    case True{}:
      (Laws.lt_le(U32.to_nat(a), U32.to_nat(b), e), Laws.le_refl(U32.to_nat(b)))
    case False{}:
      (Laws.le_refl(U32.to_nat(a)), Laws.nlt_le(U32.to_nat(a), U32.to_nat(b), e))

# The max is at least each of the two.

def Laws.max_ge(a, b):
  match a b:
    case U32{+x} U32{+y}:
      maxge.go(U32.is_lt(U32{x}, U32{y}), U32{x}, U32{y}, lt.nat2(U32{x}, U32{y}, U32.is_lt(U32{x}, U32{y}), {==}))

def a1(-A: Data, -B: Data, +p: S.And(A, B)) -> A:
  (+x, +y) = p
  x

def a2(-A: Data, -B: Data, +p: S.And(A, B)) -> B:
  (+x, +y) = p
  y

def ge.max(+lb: Nat, +a: U32, +b: U32, +h: Either<&2, &2, S.GE(lb, a), S.GE(lb, b)>) -> S.GE(lb, U32.max(a, b)):
  match h:
    case Inl{ha}:
      Laws.le_trans(lb, U32.to_nat(a), U32.to_nat(U32.max(a, b)), ha, a1({Nat.is_le(U32.to_nat(a), U32.to_nat(U32.max(a, b))) == True{} : Bool}, {Nat.is_le(U32.to_nat(b), U32.to_nat(U32.max(a, b))) == True{} : Bool}, Laws.max_ge(a, b)))
    case Inr{hb}:
      Laws.le_trans(lb, U32.to_nat(b), U32.to_nat(U32.max(a, b)), hb, a2({Nat.is_le(U32.to_nat(a), U32.to_nat(U32.max(a, b))) == True{} : Bool}, {Nat.is_le(U32.to_nat(b), U32.to_nat(U32.max(a, b))) == True{} : Bool}, Laws.max_ge(a, b)))

def pp1(-A: Type, -B: Type, p: A & B) -> A:
  (a, b) = p
  a

# Some move of ms has a child worth at least lb, or every move does.

def Laws.max_keep(p, ms, t, pos, best, r, lb, h):
  match ms r:
    case Nil{} B.Res{+v, n}:
      ge.max(lb, best, v, h)
    case Con{+c, rest} B.Res{+v, +n}:
      Laws.max_keep(p, rest, t, pos, U32.max(best, v), B.search(p, R.moves(R.play(t, pos, c)), t, R.play(t, pos, c), R.pos.ns(R.play(t, pos, c)), B.seed(R.pos.ns(R.play(t, pos, c))), B.Res{B.seed(R.pos.ns(R.play(t, pos, c))), 1n+n}), lb, Inl{ge.max(lb, best, v, h)})

# North-South to play reach lb if one of their moves does.

def Laws.max_ex(p, ms, t, pos, best, r, lb, ex):
  match ms r:
    case Nil{} B.Res{+v, n}:
      Empty.absurd(S.GE(lb, U32.max(best, v)), ex)
    case Con{+c, rest} B.Res{+v, +n}:
      match ex:
        case Inl{k}:
          Laws.max_keep(p, rest, t, pos, U32.max(best, v), B.search(p, R.moves(R.play(t, pos, c)), t, R.play(t, pos, c), R.pos.ns(R.play(t, pos, c)), B.seed(R.pos.ns(R.play(t, pos, c))), B.Res{B.seed(R.pos.ns(R.play(t, pos, c))), 1n+n}), lb, Inr{k(1n+n)})
        case Inr{e}:
          Laws.max_ex(p, rest, t, pos, U32.max(best, v), B.search(p, R.moves(R.play(t, pos, c)), t, R.play(t, pos, c), R.pos.ns(R.play(t, pos, c)), B.seed(R.pos.ns(R.play(t, pos, c))), B.Res{B.seed(R.pos.ns(R.play(t, pos, c))), 1n+n}), lb, e)

# East-West to play stay at lb or above if every move does.

def Laws.min_all(p, ms, t, pos, best, r, lb, all, hb, hr):
  match ms r:
    case Nil{} B.Res{+v, n}:
      pp1({Nat.is_le(lb, U32.to_nat(U32.min(best, v))) == True{} : Bool}, {Nat.is_le(U32.to_nat(U32.min(best, v)), U32.to_nat(v)) == True{} : Bool}, Laws.min_ge(best, v, lb, hb, hr))
    case Con{+c, rest} B.Res{+v, +n}:
      (k, ra) = all
      Laws.min_all(p, rest, t, pos, U32.min(best, v), B.search(p, R.moves(R.play(t, pos, c)), t, R.play(t, pos, c), R.pos.ns(R.play(t, pos, c)), B.seed(R.pos.ns(R.play(t, pos, c))), B.Res{B.seed(R.pos.ns(R.play(t, pos, c))), 1n+n}), lb, ra,
        pp1({Nat.is_le(lb, U32.to_nat(U32.min(best, v))) == True{} : Bool}, {Nat.is_le(U32.to_nat(U32.min(best, v)), U32.to_nat(v)) == True{} : Bool}, Laws.min_ge(best, v, lb, hb, hr)), k(1n+n))

# ---------------------------------------------------------------------------
# Every card of a holding is among the moves

def Laws.count_none(n, w, h):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          match b:
            case True{}:
              Empty.absurd({S.word.count(1n+p, WCon{True{}, t}) == 0n : Nat}, no_ft(hd(p, False{}, True{}, Word.and(p, t, S.ones(p, 0n)), t, h)))
            case False{}:
              Laws.count_none(p, t, tl(p, False{}, False{}, Word.and(p, t, S.ones(p, 0n)), t, h))

# A word within the low j bits has at most j bits.

def Laws.count_le(n, j, w, h):
  match n:
    case 0n:
      match w:
        case WNil{}:
          Laws.le_zero(j)
    case 1n+p:
      match j w:
        case 0n WCon{+b, +t}:
          %Equal.sym(Nat, S.word.count(1n+p, WCon{b, t}), 0n, Laws.count_none(1n+p, WCon{b, t}, h)) : {Nat.is_le(_, 0n) == True{} : Bool}
          {==}
        case 1n+i WCon{+b, +t}:
          match b:
            case True{}:
              Laws.count_le(p, i, t, tl(p, True{}, True{}, Word.and(p, t, S.ones(p, i)), t, h))
            case False{}:
              Laws.le_succ(S.word.count(p, t), i, Laws.count_le(p, i, t, tl(p, False{}, False{}, Word.and(p, t, S.ones(p, i)), t, h)))

def split.lift(+p: Nat, +i: Nat, +t: Word(p), e: Either<&2, &2, {i == S.lsb(p, t) : Nat}, S.Sub(p, S.unit(p, i), Word.xor(p, t, S.unit(p, S.lsb(p, t))))>) -> Either<&2, &2, {1n+i == 1n+S.lsb(p, t) : Nat}, S.Sub(1n+p, WCon{False{}, S.unit(p, i)}, WCon{False{}, Word.xor(p, t, S.unit(p, S.lsb(p, t)))})>:
  match e:
    case Inl{x}:
      Inl{Equal.cong(Nat, Nat, (z => 1n+z), i, S.lsb(p, t), x)}
    case Inr{y}:
      Inr{wc(p, False{}, Word.and(p, S.unit(p, i), Word.xor(p, t, S.unit(p, S.lsb(p, t)))), S.unit(p, i), y)}

# A bit of w is its lowest bit, or a bit of what is left without it.

def Laws.unit_split(n, r, w, h):
  match n:
    case 0n:
      match w:
        case WNil{}:
          Inr{{==}}
    case 1n+p:
      match r w:
        case 0n WCon{+b, +t}:
          match b:
            case True{}:
              Inl{{==}}
            case False{}:
              Empty.absurd(Either<&2, &2, {0n == S.lsb(1n+p, WCon{False{}, t}) : Nat}, S.Sub(1n+p, S.unit(1n+p, 0n), Word.xor(1n+p, WCon{False{}, t}, S.unit(1n+p, S.lsb(1n+p, WCon{False{}, t}))))>, no_ft(hd(p, False{}, True{}, Word.and(p, Word.zero(p), t), Word.zero(p), h)))
        case 1n+i WCon{+b, +t}:
          match b:
            case True{}:
              Inr{wc(p, False{}, Word.and(p, S.unit(p, i), Word.xor(p, t, Word.zero(p))), S.unit(p, i),
                Equal.trans(Word(p), Word.and(p, S.unit(p, i), Word.xor(p, t, Word.zero(p))), Word.and(p, S.unit(p, i), t), S.unit(p, i),
                  Equal.cong(Word(p), Word(p), (v => Word.and(p, S.unit(p, i), v)), Word.xor(p, t, Word.zero(p)), t, Laws.xor_zero(p, t)),
                  tl(p, False{}, False{}, Word.and(p, S.unit(p, i), t), S.unit(p, i), h)))}
            case False{}:
              split.lift(p, i, t, Laws.unit_split(p, i, t, tl(p, False{}, False{}, Word.and(p, S.unit(p, i), t), S.unit(p, i), h)))

def Laws.mem_acc(n, z, s, m, acc, c, mem):
  match n z:
    case 0n _:
      mem
    case 1n+p True{}:
      mem
    case 1n+p False{}:
      Laws.mem_acc(p, U32.is_zero(S.rest(m)), s, S.rest(m), C.card.make(s, U32.from_nat(U32.ctz(S.low(m)))) <> acc, c, Inr{mem})

def sub_at(-a: U32, -b: U32, +k: U32, e: {a == b : U32}, h: S.Sub32(a, k)) -> S.Sub32(b, k):
  %e : S.Sub32(_, k)
  h

def sub_in(+x: U32, -a: U32, -b: U32, e: {a == b : U32}, h: S.Sub32(x, a)) -> S.Sub32(x, b):
  %e : S.Sub32(x, _)
  h

def one.r(+r: Nat, +lr: {Nat.is_lt(r, 13n) == True{} : Bool}) -> {S.bits((1 << r : U32)) == 1n : Nat}:
  nat.eq(S.bits((1 << r : U32)), 1n, Laws.one_bit(r, lr))

def unit.sub(+r: Nat, +lr: {Nat.is_lt(r, 13n) == True{} : Bool}, +w: Word(32n), +xm: S.Sub32((1 << r : U32), U32{w})) -> S.Sub(32n, S.unit(32n, r), w):
  u.unwrap(Word.and(32n, S.unit(32n, r), w), S.unit(32n, r), sub_at((1 << r : U32), U32{S.unit(32n, r)}, U32{w}, Equal.sym(U32, U32{S.unit(32n, r)}, (1 << r : U32), Laws.unit_shl(r, lr)), xm))

def rest.eq(+w: Word(32n)) -> {S.rest(U32{w}) == U32{Word.xor(32n, w, S.unit(32n, S.lsb(32n, w)))} : U32}:
  u.wrap(Word.xor(32n, w, Word.and(32n, w, Word.adc(32n, Word.zero(32n), w, True{}, True{}))), Word.xor(32n, w, S.unit(32n, S.lsb(32n, w))),
    Equal.cong(Word(32n), Word(32n), (v => Word.xor(32n, w, v)), Word.and(32n, w, Word.adc(32n, Word.zero(32n), w, True{}, True{})), S.unit(32n, S.lsb(32n, w)), Laws.low_unit(32n, w)))

def cnt.one(+r: Nat, +lr: {Nat.is_lt(r, 13n) == True{} : Bool}, +w: Word(32n), +xm: S.Sub32((1 << r : U32), U32{w})) -> {S.bits(U32{w}) == 1n+S.bits(U32.xor(U32{w}, (1 << r : U32))) : Nat}:
  Laws.count_xor32((1 << r : U32), U32{w}, xm, one.r(r, lr))

def tf.of(+w: Word(32n), +zf: {True{} == U32.is_eq(U32{w}, 0) : Bool}) -> {U32{w} == 0 : U32}:
  Laws.u32_eq(U32{w}, 0, Equal.sym(Bool, True{}, U32.is_eq(U32{w}, 0), zf))

# Every card of a holding that the peel has yet to reach comes out of it, as long as
# the fuel n covers the cards left. sp says where the card is in w: its lowest bit,
# or among the rest.

def Laws.mem_peel(n, z, s, w, acc, c, r, ec, lr, zf, hm, xm, cn, sp):
  match n z sp:
    case 0n _ _:
      Empty.absurd(S.Mem(c, R.moves.peel(0n, z, s, U32{w}, acc)), no_ft(Equal.trans(Bool, False{}, Nat.is_le(S.bits(U32{w}), 0n), True{},
        Equal.cong(Nat, Bool, (v => Nat.is_le(v, 0n)), 1n+S.bits(U32.xor(U32{w}, (1 << r : U32))), S.bits(U32{w}), Equal.sym(Nat, S.bits(U32{w}), 1n+S.bits(U32.xor(U32{w}, (1 << r : U32))), cnt.one(r, lr, w, xm))), cn)))
    case 1n+p True{} _:
      Empty.absurd(S.Mem(c, R.moves.peel(1n+p, True{}, s, U32{w}, acc)), no_zs(S.bits(U32.xor(U32{w}, (1 << r : U32))),
        Equal.trans(Nat, 0n, S.bits(U32{w}), 1n+S.bits(U32.xor(U32{w}, (1 << r : U32))), Equal.cong(U32, Nat, (u => S.bits(u)), 0, U32{w}, Equal.sym(U32, U32{w}, 0, tf.of(w, zf))), cnt.one(r, lr, w, xm))))
    case 1n+p False{} Inl{+e}:
      Laws.mem_acc(p, U32.is_zero(S.rest(U32{w})), s, S.rest(U32{w}), C.card.make(s, U32.from_nat(U32.ctz(S.low(U32{w})))) <> acc, c,
        Inl{Equal.trans(U32, C.card.make(s, U32.from_nat(U32.ctz(S.low(U32{w})))), C.card.make(s, U32.from_nat(r)), c,
          Equal.cong(Nat, U32, (x => C.card.make(s, U32.from_nat(x))), U32.ctz(S.low(U32{w})), r,
            Equal.trans(Nat, U32.ctz(S.low(U32{w})), S.lsb(32n, w), r, low.ctz(w, Laws.lsb_hold(w, hm, Equal.sym(Bool, False{}, U32.is_eq(U32{w}, 0), zf))), Equal.sym(Nat, r, S.lsb(32n, w), e))),
          Equal.sym(U32, c, C.card.make(s, U32.from_nat(r)), ec))})
    case 1n+p False{} Inr{+y}:
      %Equal.sym(U32, S.rest(U32{w}), U32{Word.xor(32n, w, S.unit(32n, S.lsb(32n, w)))}, rest.eq(w)) : S.Mem(c, R.moves.peel(p, U32.is_zero(_), s, _, C.card.make(s, U32.from_nat(U32.ctz(S.low(U32{w})))) <> acc))
      Laws.mem_peel(p, U32.is_zero(U32{Word.xor(32n, w, S.unit(32n, S.lsb(32n, w)))}), s, Word.xor(32n, w, S.unit(32n, S.lsb(32n, w))), C.card.make(s, U32.from_nat(U32.ctz(S.low(U32{w})))) <> acc, c, r, ec, lr, {==},
        sub_at(S.rest(U32{w}), U32{Word.xor(32n, w, S.unit(32n, S.lsb(32n, w)))}, 8191, rest.eq(w), low.rest(U32{w}, hm)),
        sub_at(U32{S.unit(32n, r)}, (1 << r : U32), U32{Word.xor(32n, w, S.unit(32n, S.lsb(32n, w)))}, Laws.unit_shl(r, lr), u.wrap(Word.and(32n, S.unit(32n, r), Word.xor(32n, w, S.unit(32n, S.lsb(32n, w)))), S.unit(32n, r), y)),
        Equal.trans(Bool, Nat.is_le(1n+S.bits(U32{Word.xor(32n, w, S.unit(32n, S.lsb(32n, w)))}), 1n+p), Nat.is_le(S.bits(U32{w}), 1n+p), True{}, Equal.cong(Nat, Bool, (v => Nat.is_le(v, 1n+p)), 1n+S.bits(U32{Word.xor(32n, w, S.unit(32n, S.lsb(32n, w)))}), S.bits(U32{w}), Equal.sym(Nat, S.bits(U32{w}), 1n+S.bits(U32{Word.xor(32n, w, S.unit(32n, S.lsb(32n, w)))}), Equal.trans(Nat, S.bits(U32{w}), 1n+S.bits(S.rest(U32{w})), 1n+S.bits(U32{Word.xor(32n, w, S.unit(32n, S.lsb(32n, w)))}), Laws.count_xor32(S.low(U32{w}), U32{w}, low.in(U32{w}), Equal.trans(Nat, S.bits(S.low(U32{w})), S.bits((1 << S.lsb(32n, w) : U32)), 1n, Equal.cong(U32, Nat, (u => S.bits(u)), S.low(U32{w}), (1 << S.lsb(32n, w) : U32), low.shl(w, Laws.lsb_hold(w, hm, Equal.sym(Bool, False{}, U32.is_eq(U32{w}, 0), zf)))), one.r(S.lsb(32n, w), Laws.lsb_hold(w, hm, Equal.sym(Bool, False{}, U32.is_eq(U32{w}, 0), zf))))), Equal.cong(U32, Nat, (u => 1n+S.bits(u)), S.rest(U32{w}), U32{Word.xor(32n, w, S.unit(32n, S.lsb(32n, w)))}, rest.eq(w))))), cn),
        Laws.unit_split(32n, r, Word.xor(32n, w, S.unit(32n, S.lsb(32n, w))), y))

def mem_suit(+sj: U32, +m: U32, acc: List<&2, U32>, +c: U32, +r: Nat, +ec: {c == C.card.make(sj, U32.from_nat(r)) : U32}, +lr: {Nat.is_lt(r, 13n) == True{} : Bool}, +hm: S.Sub32(m, 8191), +xm: S.Sub32((1 << r : U32), m)) -> S.Mem(c, R.moves.suit(sj, m, acc)):
  match m:
    case U32{+w}:
      Laws.mem_peel(13n, U32.is_zero(U32{w}), sj, w, acc, c, r, ec, lr, {==}, hm, xm,
        Laws.count_le(32n, 13n, w, u.unwrap(Word.and(32n, w, S.ones(32n, 13n)), w, hm)),
        Laws.unit_split(32n, r, w, unit.sub(r, lr, w, xm)))

# Every card of the hand is a move when the hand is on lead.

def Laws.mem_lead(j, r, h01, h23, v01, v23, lj, lr, xm):
  match j:
    case 0n:
      mem_suit(0, (h01 >> 16n : U32), R.moves.suit(1, (h01 .&. 65535 : U32), R.moves.suit(2, (h23 >> 16n : U32), R.moves.suit(3, (h23 .&. 65535 : U32), Nil{}))), C.card.make(0, U32.from_nat(r)), r, {==}, lr, Laws.hi_holding(h01, v01), xm)
    case 1n:
      Laws.mem_acc(13n, U32.is_zero((h01 >> 16n : U32)), 0, (h01 >> 16n : U32), R.moves.suit(1, (h01 .&. 65535 : U32), R.moves.suit(2, (h23 >> 16n : U32), R.moves.suit(3, (h23 .&. 65535 : U32), Nil{}))), C.card.make(1, U32.from_nat(r)),
        mem_suit(1, (h01 .&. 65535 : U32), R.moves.suit(2, (h23 >> 16n : U32), R.moves.suit(3, (h23 .&. 65535 : U32), Nil{})), C.card.make(1, U32.from_nat(r)), r, {==}, lr, Laws.lo_holding(h01, v01), xm))
    case 2n:
      Laws.mem_acc(13n, U32.is_zero((h01 >> 16n : U32)), 0, (h01 >> 16n : U32), R.moves.suit(1, (h01 .&. 65535 : U32), R.moves.suit(2, (h23 >> 16n : U32), R.moves.suit(3, (h23 .&. 65535 : U32), Nil{}))), C.card.make(2, U32.from_nat(r)),
        Laws.mem_acc(13n, U32.is_zero((h01 .&. 65535 : U32)), 1, (h01 .&. 65535 : U32), R.moves.suit(2, (h23 >> 16n : U32), R.moves.suit(3, (h23 .&. 65535 : U32), Nil{})), C.card.make(2, U32.from_nat(r)),
          mem_suit(2, (h23 >> 16n : U32), R.moves.suit(3, (h23 .&. 65535 : U32), Nil{}), C.card.make(2, U32.from_nat(r)), r, {==}, lr, Laws.hi_holding(h23, v23), xm)))
    case 3n:
      Laws.mem_acc(13n, U32.is_zero((h01 >> 16n : U32)), 0, (h01 >> 16n : U32), R.moves.suit(1, (h01 .&. 65535 : U32), R.moves.suit(2, (h23 >> 16n : U32), R.moves.suit(3, (h23 .&. 65535 : U32), Nil{}))), C.card.make(3, U32.from_nat(r)),
        Laws.mem_acc(13n, U32.is_zero((h01 .&. 65535 : U32)), 1, (h01 .&. 65535 : U32), R.moves.suit(2, (h23 >> 16n : U32), R.moves.suit(3, (h23 .&. 65535 : U32), Nil{})), C.card.make(3, U32.from_nat(r)),
          Laws.mem_acc(13n, U32.is_zero((h23 >> 16n : U32)), 2, (h23 >> 16n : U32), R.moves.suit(3, (h23 .&. 65535 : U32), Nil{}), C.card.make(3, U32.from_nat(r)),
            mem_suit(3, (h23 .&. 65535 : U32), Nil{}, C.card.make(3, U32.from_nat(r)), r, {==}, lr, Laws.lo_holding(h23, v23), xm))))
    case 4n+y:
      Empty.absurd(S.Mem(C.card.make(U32.from_nat(4n+y), U32.from_nat(r)), R.moves.of(4, h01, h23)), no_lt0(y, lj))

def kid.at(+lb: Nat, +p: Nat, +t: U32, +pos: R.Pos, +h: U32, +c: U32, e: {h == c : U32}, k: S.Kid(lb, p, t, pos, c)) -> S.Kid(lb, p, t, pos, h):
  %Equal.sym(U32, h, c, e) : S.Kid(lb, p, t, pos, _)
  k

# A move that is one of the moves, and whose child reaches lb, is a witness.

def Laws.ex_mem(lb, p, t, pos, ms, c, mem, k):
  match ms:
    case Nil{}:
      Empty.absurd(S.ExK(lb, p, t, pos, Nil{}), mem)
    case Con{+h, tl}:
      match mem:
        case Inl{e}:
          Inl{kid.at(lb, p, t, pos, h, c, e, k)}
        case Inr{m2}:
          Inr{Laws.ex_mem(lb, p, t, pos, tl, c, m2, k)}


# ---------------------------------------------------------------------------
# The winning card in the trick word

def syu(-a: U32, -b: U32, x: {a == b : U32}) -> {b == a : U32}:
  Equal.sym(U32, a, b, x)

def cgu(-a: U32, -b: U32, -F: U32 -> U32, x: {a == b : U32}) -> {F(a) == F(b) : U32}:
  Equal.cong(U32, U32, F, a, b, x)

def Laws.shrn_or(k, a, b):
  match k:
    case 0n:
      {==}
    case 1n+j:
      tr(U32.shr(U32.shrn(U32.or(a, b), j)), U32.shr(U32.or(U32.shrn(a, j), U32.shrn(b, j))), U32.or(U32.shr(U32.shrn(a, j)), U32.shr(U32.shrn(b, j))),
        cgu(U32.shrn(U32.or(a, b), j), U32.or(U32.shrn(a, j), U32.shrn(b, j)), (x => U32.shr(x)), Laws.shrn_or(j, a, b)),
        shr_or(U32.shrn(a, j), U32.shrn(b, j)))

# What a field of an or holds is the or of what it holds in each part.

def Laws.field_or(k, m, a, b):
  tr(U32.and(U32.shrn(U32.or(a, b), k), m), U32.and(U32.or(U32.shrn(a, k), U32.shrn(b, k)), m), U32.or(U32.and(U32.shrn(a, k), m), U32.and(U32.shrn(b, k), m)),
    cgu(U32.shrn(U32.or(a, b), k), U32.or(U32.shrn(a, k), U32.shrn(b, k)), (x => U32.and(x, m)), Laws.shrn_or(k, a, b)),
    u32.or_and(U32.shrn(a, k), U32.shrn(b, k), m))

# A part inside mask K reads, at any field, only what K leaves there.

def Laws.field_mask(x, kk, k, m, h):
  tr(U32.and(U32.shrn(x, k), m), U32.and(U32.shrn(U32.and(x, kk), k), m), U32.and(U32.shrn(x, k), U32.and(U32.shrn(kk, k), m)),
    cgu(x, U32.and(x, kk), (z => U32.and(U32.shrn(z, k), m)), syu(U32.and(x, kk), x, h)),
    tr(U32.and(U32.shrn(U32.and(x, kk), k), m), U32.and(U32.and(U32.shrn(x, k), U32.shrn(kk, k)), m), U32.and(U32.shrn(x, k), U32.and(U32.shrn(kk, k), m)),
      cgu(U32.shrn(U32.and(x, kk), k), U32.and(U32.shrn(x, k), U32.shrn(kk, k)), (z => U32.and(z, m)), Laws.shrn_and(k, x, kk)),
      Laws.and_assoc32(U32.shrn(x, k), U32.shrn(kk, k), m)))

def Laws.shr_shl_w(p, b, t):
  match p:
    case 0n:
      match b t:
        case True{} WNil{}:
          {==}
        case False{} WNil{}:
          {==}
    case 1n+q:
      match b t:
        case True{} WCon{+b2, +t2}:
          wc(1n+q, True{}, Word.shr.pad(q, Word.shl.put(q, b2, t2)), Word.and(1n+q, WCon{b2, t2}, S.ones(1n+q, q)), Laws.shr_shl_w(q, b2, t2))
        case False{} WCon{+b2, +t2}:
          wc(1n+q, False{}, Word.shr.pad(q, Word.shl.put(q, b2, t2)), Word.and(1n+q, WCon{b2, t2}, S.ones(1n+q, q)), Laws.shr_shl_w(q, b2, t2))

def Laws.shr_shl(x):
  match x:
    case U32{WCon{+b, +t}}:
      u.wrap(Word.shr.pad(31n, Word.shl.put(31n, b, t)), Word.and(32n, WCon{b, t}, S.ones(32n, 31n)), Laws.shr_shl_w(31n, b, t))

def Laws.and_all_w(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          match b:
            case True{}:
              wc(p, True{}, Word.and(p, t, S.ones(p, p)), t, Laws.and_all_w(p, t))
            case False{}:
              wc(p, False{}, Word.and(p, t, S.ones(p, p)), t, Laws.and_all_w(p, t))

# The bits that survive k shifts up and k back down.

def Laws.shrn_shln(k, x):
  match k:
    case 0n:
      match x:
        case U32{+w}:
          syu(U32{Word.and(32n, w, S.ones(32n, 32n))}, U32{w}, u.wrap(Word.and(32n, w, S.ones(32n, 32n)), w, Laws.and_all_w(32n, w)))
    case 1n+j:
      tr(U32.shr(U32.shrn(U32.shl(U32.shln(x, j)), j)), U32.shrn(U32.shr(U32.shl(U32.shln(x, j))), j), U32.and(x, S.keep(1n+j)),
        syu(U32.shrn(U32.shr(U32.shl(U32.shln(x, j))), j), U32.shr(U32.shrn(U32.shl(U32.shln(x, j)), j)), Laws.shrn_comm(U32.shl(U32.shln(x, j)), j)),
        tr(U32.shrn(U32.shr(U32.shl(U32.shln(x, j))), j), U32.shrn(U32.and(U32.shln(x, j), 2147483647), j), U32.and(x, S.keep(1n+j)),
          cgu(U32.shr(U32.shl(U32.shln(x, j))), U32.and(U32.shln(x, j), 2147483647), (z => U32.shrn(z, j)), Laws.shr_shl(U32.shln(x, j))),
          tr(U32.shrn(U32.and(U32.shln(x, j), 2147483647), j), U32.and(U32.shrn(U32.shln(x, j), j), U32.shrn(2147483647, j)), U32.and(x, S.keep(1n+j)),
            Laws.shrn_and(j, U32.shln(x, j), 2147483647),
            tr(U32.and(U32.shrn(U32.shln(x, j), j), U32.shrn(2147483647, j)), U32.and(U32.and(x, S.keep(j)), U32.shrn(2147483647, j)), U32.and(x, S.keep(1n+j)),
              cgu(U32.shrn(U32.shln(x, j), j), U32.and(x, S.keep(j)), (z => U32.and(z, U32.shrn(2147483647, j))), Laws.shrn_shln(j, x)),
              Laws.and_assoc32(x, S.keep(j), U32.shrn(2147483647, j))))))

def or0l.w(+n: Nat, +w: Word(n)) -> {Word.or(n, Word.zero(n), w) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          match b:
            case True{}:
              wc(p, True{}, Word.or(p, Word.zero(p), t), t, or0l.w(p, t))
            case False{}:
              wc(p, False{}, Word.or(p, Word.zero(p), t), t, or0l.w(p, t))

def or0l(+a: U32) -> {U32.or(0, a) == a : U32}:
  match a:
    case U32{+x}:
      u.wrap(Word.or(32n, Word.zero(32n), x), x, or0l.w(32n, x))

def Laws.owner_make(s, p, l, o, b, hs, hp, hl, ho, hb):
  tr(U32.and(U32.shrn(U32.or(U32.or(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), U32.shln(b, 9n)), 7n), 3), U32.or(U32.and(U32.shrn(U32.or(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), 7n), 3), U32.and(U32.shrn(U32.shln(b, 9n), 7n), 3)), o, Laws.field_or(7n, 3, U32.or(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), U32.shln(b, 9n)), tr(U32.or(U32.and(U32.shrn(U32.or(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), 7n), 3), U32.and(U32.shrn(U32.shln(b, 9n), 7n), 3)), U32.or(o, 0), o, Equal.trans(U32, U32.or(U32.and(U32.shrn(U32.or(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), 7n), 3), U32.and(U32.shrn(U32.shln(b, 9n), 7n), 3)), U32.or(o, U32.and(U32.shrn(U32.shln(b, 9n), 7n), 3)), U32.or(o, 0), cgu(U32.and(U32.shrn(U32.or(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), 7n), 3), o, (z => U32.or(z, U32.and(U32.shrn(U32.shln(b, 9n), 7n), 3))), tr(U32.and(U32.shrn(U32.or(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), 7n), 3), U32.or(U32.and(U32.shrn(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), 7n), 3), U32.and(U32.shrn(U32.shln(o, 7n), 7n), 3)), o, Laws.field_or(7n, 3, U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), tr(U32.or(U32.and(U32.shrn(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), 7n), 3), U32.and(U32.shrn(U32.shln(o, 7n), 7n), 3)), U32.or(0, o), o, Equal.trans(U32, U32.or(U32.and(U32.shrn(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), 7n), 3), U32.and(U32.shrn(U32.shln(o, 7n), 7n), 3)), U32.or(0, U32.and(U32.shrn(U32.shln(o, 7n), 7n), 3)), U32.or(0, o), cgu(U32.and(U32.shrn(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), 7n), 3), 0, (z => U32.or(z, U32.and(U32.shrn(U32.shln(o, 7n), 7n), 3))), tr(U32.and(U32.shrn(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), 7n), 3), U32.or(U32.and(U32.shrn(U32.or(s, U32.shln(p, 2n)), 7n), 3), U32.and(U32.shrn(U32.shln(l, 4n), 7n), 3)), 0, Laws.field_or(7n, 3, U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), tr(U32.or(U32.and(U32.shrn(U32.or(s, U32.shln(p, 2n)), 7n), 3), U32.and(U32.shrn(U32.shln(l, 4n), 7n), 3)), U32.or(0, 0), 0, Equal.trans(U32, U32.or(U32.and(U32.shrn(U32.or(s, U32.shln(p, 2n)), 7n), 3), U32.and(U32.shrn(U32.shln(l, 4n), 7n), 3)), U32.or(0, U32.and(U32.shrn(U32.shln(l, 4n), 7n), 3)), U32.or(0, 0), cgu(U32.and(U32.shrn(U32.or(s, U32.shln(p, 2n)), 7n), 3), 0, (z => U32.or(z, U32.and(U32.shrn(U32.shln(l, 4n), 7n), 3))), tr(U32.and(U32.shrn(U32.or(s, U32.shln(p, 2n)), 7n), 3), U32.or(U32.and(U32.shrn(s, 7n), 3), U32.and(U32.shrn(U32.shln(p, 2n), 7n), 3)), 0, Laws.field_or(7n, 3, s, U32.shln(p, 2n)), tr(U32.or(U32.and(U32.shrn(s, 7n), 3), U32.and(U32.shrn(U32.shln(p, 2n), 7n), 3)), U32.or(0, 0), 0, Equal.trans(U32, U32.or(U32.and(U32.shrn(s, 7n), 3), U32.and(U32.shrn(U32.shln(p, 2n), 7n), 3)), U32.or(0, U32.and(U32.shrn(U32.shln(p, 2n), 7n), 3)), U32.or(0, 0), cgu(U32.and(U32.shrn(s, 7n), 3), 0, (z => U32.or(z, U32.and(U32.shrn(U32.shln(p, 2n), 7n), 3))), tr(U32.and(U32.shrn(s, 7n), 3), U32.and(U32.shrn(s, 7n), U32.and(U32.shrn(3, 7n), 3)), 0, Laws.field_mask(s, 3, 7n, 3, hs), u32.and_zero(U32.shrn(s, 7n)))), cgu(U32.and(U32.shrn(U32.shln(p, 2n), 7n), 3), 0, (z => U32.or(0, z)), tr(U32.and(U32.shrn(U32.shln(p, 2n), 7n), 3), U32.and(U32.shrn(U32.shln(p, 2n), 7n), U32.and(U32.shrn(12, 7n), 3)), 0, Laws.field_mask(U32.shln(p, 2n), 12, 7n, 3, Laws.shln_sub(2n, p, 12, hp)), u32.and_zero(U32.shrn(U32.shln(p, 2n), 7n))))), {==}))), cgu(U32.and(U32.shrn(U32.shln(l, 4n), 7n), 3), 0, (z => U32.or(0, z)), tr(U32.and(U32.shrn(U32.shln(l, 4n), 7n), 3), U32.and(U32.shrn(U32.shln(l, 4n), 7n), U32.and(U32.shrn(112, 7n), 3)), 0, Laws.field_mask(U32.shln(l, 4n), 112, 7n, 3, Laws.shln_sub(4n, l, 112, hl)), u32.and_zero(U32.shrn(U32.shln(l, 4n), 7n))))), {==}))), cgu(U32.and(U32.shrn(U32.shln(o, 7n), 7n), 3), o, (z => U32.or(0, z)), tr(U32.and(U32.shrn(U32.shln(o, 7n), 7n), 3), U32.and(U32.and(o, S.keep(7n)), 3), o, cgu(U32.shrn(U32.shln(o, 7n), 7n), U32.and(o, S.keep(7n)), (z => U32.and(z, 3)), Laws.shrn_shln(7n, o)), tr(U32.and(U32.and(o, S.keep(7n)), 3), U32.and(o, U32.and(S.keep(7n), 3)), o, Laws.and_assoc32(o, S.keep(7n), 3), ho)))), or0l(o)))), cgu(U32.and(U32.shrn(U32.shln(b, 9n), 7n), 3), 0, (z => U32.or(o, z)), tr(U32.and(U32.shrn(U32.shln(b, 9n), 7n), 3), U32.and(U32.shrn(U32.shln(b, 9n), 7n), U32.and(U32.shrn(32256, 7n), 3)), 0, Laws.field_mask(U32.shln(b, 9n), 32256, 7n, 3, Laws.shln_sub(9n, b, 32256, hb)), u32.and_zero(U32.shrn(U32.shln(b, 9n), 7n))))), u32.or_zero(o)))

# The same with the rank bit on top.

def Laws.owner_make_r(s, p, l, o, b, r, hs, hp, hl, ho, hb, hr):
  tr(U32.and(U32.shrn(U32.or(R.trick.make(s, p, l, o, b), U32.shln(r, 15n)), 7n), 3), U32.or(U32.and(U32.shrn(R.trick.make(s, p, l, o, b), 7n), 3), U32.and(U32.shrn(U32.shln(r, 15n), 7n), 3)), o, Laws.field_or(7n, 3, R.trick.make(s, p, l, o, b), U32.shln(r, 15n)),
    tr(U32.or(U32.and(U32.shrn(R.trick.make(s, p, l, o, b), 7n), 3), U32.and(U32.shrn(U32.shln(r, 15n), 7n), 3)), U32.or(o, 0), o,
      Equal.trans(U32, U32.or(U32.and(U32.shrn(R.trick.make(s, p, l, o, b), 7n), 3), U32.and(U32.shrn(U32.shln(r, 15n), 7n), 3)), U32.or(o, U32.and(U32.shrn(U32.shln(r, 15n), 7n), 3)), U32.or(o, 0),
        cgu(U32.and(U32.shrn(R.trick.make(s, p, l, o, b), 7n), 3), o, (z => U32.or(z, U32.and(U32.shrn(U32.shln(r, 15n), 7n), 3))), Laws.owner_make(s, p, l, o, b, hs, hp, hl, ho, hb)),
        cgu(U32.and(U32.shrn(U32.shln(r, 15n), 7n), 3), 0, (z => U32.or(o, z)), tr(U32.and(U32.shrn(U32.shln(r, 15n), 7n), 3), U32.and(U32.shrn(U32.shln(r, 15n), 7n), U32.and(U32.shrn(32768, 7n), 3)), 0, Laws.field_mask(U32.shln(r, 15n), 32768, 7n, 3, Laws.shln_sub(15n, r, 32768, hr)), u32.and_zero(U32.shrn(U32.shln(r, 15n), 7n))))),
      u32.or_zero(o)))

def Laws.best_make(s, p, l, o, b, hs, hp, hl, ho, hb):
  tr(U32.and(U32.shrn(U32.or(U32.or(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), U32.shln(b, 9n)), 9n), 63), U32.or(U32.and(U32.shrn(U32.or(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), 9n), 63), U32.and(U32.shrn(U32.shln(b, 9n), 9n), 63)), b, Laws.field_or(9n, 63, U32.or(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), U32.shln(b, 9n)), tr(U32.or(U32.and(U32.shrn(U32.or(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), 9n), 63), U32.and(U32.shrn(U32.shln(b, 9n), 9n), 63)), U32.or(0, b), b, Equal.trans(U32, U32.or(U32.and(U32.shrn(U32.or(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), 9n), 63), U32.and(U32.shrn(U32.shln(b, 9n), 9n), 63)), U32.or(0, U32.and(U32.shrn(U32.shln(b, 9n), 9n), 63)), U32.or(0, b), cgu(U32.and(U32.shrn(U32.or(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), 9n), 63), 0, (z => U32.or(z, U32.and(U32.shrn(U32.shln(b, 9n), 9n), 63))), tr(U32.and(U32.shrn(U32.or(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), 9n), 63), U32.or(U32.and(U32.shrn(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), 9n), 63), U32.and(U32.shrn(U32.shln(o, 7n), 9n), 63)), 0, Laws.field_or(9n, 63, U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), tr(U32.or(U32.and(U32.shrn(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), 9n), 63), U32.and(U32.shrn(U32.shln(o, 7n), 9n), 63)), U32.or(0, 0), 0, Equal.trans(U32, U32.or(U32.and(U32.shrn(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), 9n), 63), U32.and(U32.shrn(U32.shln(o, 7n), 9n), 63)), U32.or(0, U32.and(U32.shrn(U32.shln(o, 7n), 9n), 63)), U32.or(0, 0), cgu(U32.and(U32.shrn(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), 9n), 63), 0, (z => U32.or(z, U32.and(U32.shrn(U32.shln(o, 7n), 9n), 63))), tr(U32.and(U32.shrn(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), 9n), 63), U32.or(U32.and(U32.shrn(U32.or(s, U32.shln(p, 2n)), 9n), 63), U32.and(U32.shrn(U32.shln(l, 4n), 9n), 63)), 0, Laws.field_or(9n, 63, U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), tr(U32.or(U32.and(U32.shrn(U32.or(s, U32.shln(p, 2n)), 9n), 63), U32.and(U32.shrn(U32.shln(l, 4n), 9n), 63)), U32.or(0, 0), 0, Equal.trans(U32, U32.or(U32.and(U32.shrn(U32.or(s, U32.shln(p, 2n)), 9n), 63), U32.and(U32.shrn(U32.shln(l, 4n), 9n), 63)), U32.or(0, U32.and(U32.shrn(U32.shln(l, 4n), 9n), 63)), U32.or(0, 0), cgu(U32.and(U32.shrn(U32.or(s, U32.shln(p, 2n)), 9n), 63), 0, (z => U32.or(z, U32.and(U32.shrn(U32.shln(l, 4n), 9n), 63))), tr(U32.and(U32.shrn(U32.or(s, U32.shln(p, 2n)), 9n), 63), U32.or(U32.and(U32.shrn(s, 9n), 63), U32.and(U32.shrn(U32.shln(p, 2n), 9n), 63)), 0, Laws.field_or(9n, 63, s, U32.shln(p, 2n)), tr(U32.or(U32.and(U32.shrn(s, 9n), 63), U32.and(U32.shrn(U32.shln(p, 2n), 9n), 63)), U32.or(0, 0), 0, Equal.trans(U32, U32.or(U32.and(U32.shrn(s, 9n), 63), U32.and(U32.shrn(U32.shln(p, 2n), 9n), 63)), U32.or(0, U32.and(U32.shrn(U32.shln(p, 2n), 9n), 63)), U32.or(0, 0), cgu(U32.and(U32.shrn(s, 9n), 63), 0, (z => U32.or(z, U32.and(U32.shrn(U32.shln(p, 2n), 9n), 63))), tr(U32.and(U32.shrn(s, 9n), 63), U32.and(U32.shrn(s, 9n), U32.and(U32.shrn(3, 9n), 63)), 0, Laws.field_mask(s, 3, 9n, 63, hs), u32.and_zero(U32.shrn(s, 9n)))), cgu(U32.and(U32.shrn(U32.shln(p, 2n), 9n), 63), 0, (z => U32.or(0, z)), tr(U32.and(U32.shrn(U32.shln(p, 2n), 9n), 63), U32.and(U32.shrn(U32.shln(p, 2n), 9n), U32.and(U32.shrn(12, 9n), 63)), 0, Laws.field_mask(U32.shln(p, 2n), 12, 9n, 63, Laws.shln_sub(2n, p, 12, hp)), u32.and_zero(U32.shrn(U32.shln(p, 2n), 9n))))), {==}))), cgu(U32.and(U32.shrn(U32.shln(l, 4n), 9n), 63), 0, (z => U32.or(0, z)), tr(U32.and(U32.shrn(U32.shln(l, 4n), 9n), 63), U32.and(U32.shrn(U32.shln(l, 4n), 9n), U32.and(U32.shrn(112, 9n), 63)), 0, Laws.field_mask(U32.shln(l, 4n), 112, 9n, 63, Laws.shln_sub(4n, l, 112, hl)), u32.and_zero(U32.shrn(U32.shln(l, 4n), 9n))))), {==}))), cgu(U32.and(U32.shrn(U32.shln(o, 7n), 9n), 63), 0, (z => U32.or(0, z)), tr(U32.and(U32.shrn(U32.shln(o, 7n), 9n), 63), U32.and(U32.shrn(U32.shln(o, 7n), 9n), U32.and(U32.shrn(384, 9n), 63)), 0, Laws.field_mask(U32.shln(o, 7n), 384, 9n, 63, Laws.shln_sub(7n, o, 384, ho)), u32.and_zero(U32.shrn(U32.shln(o, 7n), 9n))))), {==}))), cgu(U32.and(U32.shrn(U32.shln(b, 9n), 9n), 63), b, (z => U32.or(0, z)), tr(U32.and(U32.shrn(U32.shln(b, 9n), 9n), 63), U32.and(U32.and(b, S.keep(9n)), 63), b, cgu(U32.shrn(U32.shln(b, 9n), 9n), U32.and(b, S.keep(9n)), (z => U32.and(z, 63)), Laws.shrn_shln(9n, b)), tr(U32.and(U32.and(b, S.keep(9n)), 63), U32.and(b, U32.and(S.keep(9n), 63)), b, Laws.and_assoc32(b, S.keep(9n), 63), hb)))), or0l(b)))

# The same with the rank bit on top.

def Laws.best_make_r(s, p, l, o, b, r, hs, hp, hl, ho, hb, hr):
  tr(U32.and(U32.shrn(U32.or(R.trick.make(s, p, l, o, b), U32.shln(r, 15n)), 9n), 63), U32.or(U32.and(U32.shrn(R.trick.make(s, p, l, o, b), 9n), 63), U32.and(U32.shrn(U32.shln(r, 15n), 9n), 63)), b, Laws.field_or(9n, 63, R.trick.make(s, p, l, o, b), U32.shln(r, 15n)),
    tr(U32.or(U32.and(U32.shrn(R.trick.make(s, p, l, o, b), 9n), 63), U32.and(U32.shrn(U32.shln(r, 15n), 9n), 63)), U32.or(b, 0), b,
      Equal.trans(U32, U32.or(U32.and(U32.shrn(R.trick.make(s, p, l, o, b), 9n), 63), U32.and(U32.shrn(U32.shln(r, 15n), 9n), 63)), U32.or(b, U32.and(U32.shrn(U32.shln(r, 15n), 9n), 63)), U32.or(b, 0),
        cgu(U32.and(U32.shrn(R.trick.make(s, p, l, o, b), 9n), 63), b, (z => U32.or(z, U32.and(U32.shrn(U32.shln(r, 15n), 9n), 63))), Laws.best_make(s, p, l, o, b, hs, hp, hl, ho, hb)),
        cgu(U32.and(U32.shrn(U32.shln(r, 15n), 9n), 63), 0, (z => U32.or(b, z)), tr(U32.and(U32.shrn(U32.shln(r, 15n), 9n), 63), U32.and(U32.shrn(U32.shln(r, 15n), 9n), U32.and(U32.shrn(32768, 9n), 63)), 0, Laws.field_mask(U32.shln(r, 15n), 32768, 9n, 63, Laws.shln_sub(15n, r, 32768, hr)), u32.and_zero(U32.shrn(U32.shln(r, 15n), 9n))))),
      u32.or_zero(b)))

def Laws.lead_make(s, p, l, o, b, hs, hp, hl, ho, hb):
  tr(U32.and(U32.shrn(U32.or(U32.or(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), U32.shln(b, 9n)), 4n), 7), U32.or(U32.and(U32.shrn(U32.or(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), 4n), 7), U32.and(U32.shrn(U32.shln(b, 9n), 4n), 7)), l, Laws.field_or(4n, 7, U32.or(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), U32.shln(b, 9n)), tr(U32.or(U32.and(U32.shrn(U32.or(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), 4n), 7), U32.and(U32.shrn(U32.shln(b, 9n), 4n), 7)), U32.or(l, 0), l, Equal.trans(U32, U32.or(U32.and(U32.shrn(U32.or(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), 4n), 7), U32.and(U32.shrn(U32.shln(b, 9n), 4n), 7)), U32.or(l, U32.and(U32.shrn(U32.shln(b, 9n), 4n), 7)), U32.or(l, 0), cgu(U32.and(U32.shrn(U32.or(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), 4n), 7), l, (z => U32.or(z, U32.and(U32.shrn(U32.shln(b, 9n), 4n), 7))), tr(U32.and(U32.shrn(U32.or(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), 4n), 7), U32.or(U32.and(U32.shrn(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), 4n), 7), U32.and(U32.shrn(U32.shln(o, 7n), 4n), 7)), l, Laws.field_or(4n, 7, U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), U32.shln(o, 7n)), tr(U32.or(U32.and(U32.shrn(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), 4n), 7), U32.and(U32.shrn(U32.shln(o, 7n), 4n), 7)), U32.or(l, 0), l, Equal.trans(U32, U32.or(U32.and(U32.shrn(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), 4n), 7), U32.and(U32.shrn(U32.shln(o, 7n), 4n), 7)), U32.or(l, U32.and(U32.shrn(U32.shln(o, 7n), 4n), 7)), U32.or(l, 0), cgu(U32.and(U32.shrn(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), 4n), 7), l, (z => U32.or(z, U32.and(U32.shrn(U32.shln(o, 7n), 4n), 7))), tr(U32.and(U32.shrn(U32.or(U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), 4n), 7), U32.or(U32.and(U32.shrn(U32.or(s, U32.shln(p, 2n)), 4n), 7), U32.and(U32.shrn(U32.shln(l, 4n), 4n), 7)), l, Laws.field_or(4n, 7, U32.or(s, U32.shln(p, 2n)), U32.shln(l, 4n)), tr(U32.or(U32.and(U32.shrn(U32.or(s, U32.shln(p, 2n)), 4n), 7), U32.and(U32.shrn(U32.shln(l, 4n), 4n), 7)), U32.or(0, l), l, Equal.trans(U32, U32.or(U32.and(U32.shrn(U32.or(s, U32.shln(p, 2n)), 4n), 7), U32.and(U32.shrn(U32.shln(l, 4n), 4n), 7)), U32.or(0, U32.and(U32.shrn(U32.shln(l, 4n), 4n), 7)), U32.or(0, l), cgu(U32.and(U32.shrn(U32.or(s, U32.shln(p, 2n)), 4n), 7), 0, (z => U32.or(z, U32.and(U32.shrn(U32.shln(l, 4n), 4n), 7))), tr(U32.and(U32.shrn(U32.or(s, U32.shln(p, 2n)), 4n), 7), U32.or(U32.and(U32.shrn(s, 4n), 7), U32.and(U32.shrn(U32.shln(p, 2n), 4n), 7)), 0, Laws.field_or(4n, 7, s, U32.shln(p, 2n)), tr(U32.or(U32.and(U32.shrn(s, 4n), 7), U32.and(U32.shrn(U32.shln(p, 2n), 4n), 7)), U32.or(0, 0), 0, Equal.trans(U32, U32.or(U32.and(U32.shrn(s, 4n), 7), U32.and(U32.shrn(U32.shln(p, 2n), 4n), 7)), U32.or(0, U32.and(U32.shrn(U32.shln(p, 2n), 4n), 7)), U32.or(0, 0), cgu(U32.and(U32.shrn(s, 4n), 7), 0, (z => U32.or(z, U32.and(U32.shrn(U32.shln(p, 2n), 4n), 7))), tr(U32.and(U32.shrn(s, 4n), 7), U32.and(U32.shrn(s, 4n), U32.and(U32.shrn(3, 4n), 7)), 0, Laws.field_mask(s, 3, 4n, 7, hs), u32.and_zero(U32.shrn(s, 4n)))), cgu(U32.and(U32.shrn(U32.shln(p, 2n), 4n), 7), 0, (z => U32.or(0, z)), tr(U32.and(U32.shrn(U32.shln(p, 2n), 4n), 7), U32.and(U32.shrn(U32.shln(p, 2n), 4n), U32.and(U32.shrn(12, 4n), 7)), 0, Laws.field_mask(U32.shln(p, 2n), 12, 4n, 7, Laws.shln_sub(2n, p, 12, hp)), u32.and_zero(U32.shrn(U32.shln(p, 2n), 4n))))), {==}))), cgu(U32.and(U32.shrn(U32.shln(l, 4n), 4n), 7), l, (z => U32.or(0, z)), tr(U32.and(U32.shrn(U32.shln(l, 4n), 4n), 7), U32.and(U32.and(l, S.keep(4n)), 7), l, cgu(U32.shrn(U32.shln(l, 4n), 4n), U32.and(l, S.keep(4n)), (z => U32.and(z, 7)), Laws.shrn_shln(4n, l)), tr(U32.and(U32.and(l, S.keep(4n)), 7), U32.and(l, U32.and(S.keep(4n), 7)), l, Laws.and_assoc32(l, S.keep(4n), 7), hl)))), or0l(l)))), cgu(U32.and(U32.shrn(U32.shln(o, 7n), 4n), 7), 0, (z => U32.or(l, z)), tr(U32.and(U32.shrn(U32.shln(o, 7n), 4n), 7), U32.and(U32.shrn(U32.shln(o, 7n), 4n), U32.and(U32.shrn(384, 4n), 7)), 0, Laws.field_mask(U32.shln(o, 7n), 384, 4n, 7, Laws.shln_sub(7n, o, 384, ho)), u32.and_zero(U32.shrn(U32.shln(o, 7n), 4n))))), u32.or_zero(l)))), cgu(U32.and(U32.shrn(U32.shln(b, 9n), 4n), 7), 0, (z => U32.or(l, z)), tr(U32.and(U32.shrn(U32.shln(b, 9n), 4n), 7), U32.and(U32.shrn(U32.shln(b, 9n), 4n), U32.and(U32.shrn(32256, 4n), 7)), 0, Laws.field_mask(U32.shln(b, 9n), 32256, 4n, 7, Laws.shln_sub(9n, b, 32256, hb)), u32.and_zero(U32.shrn(U32.shln(b, 9n), 4n))))), u32.or_zero(l)))

# The same with the rank bit on top.

def Laws.lead_make_r(s, p, l, o, b, r, hs, hp, hl, ho, hb, hr):
  tr(U32.and(U32.shrn(U32.or(R.trick.make(s, p, l, o, b), U32.shln(r, 15n)), 4n), 7), U32.or(U32.and(U32.shrn(R.trick.make(s, p, l, o, b), 4n), 7), U32.and(U32.shrn(U32.shln(r, 15n), 4n), 7)), l, Laws.field_or(4n, 7, R.trick.make(s, p, l, o, b), U32.shln(r, 15n)),
    tr(U32.or(U32.and(U32.shrn(R.trick.make(s, p, l, o, b), 4n), 7), U32.and(U32.shrn(U32.shln(r, 15n), 4n), 7)), U32.or(l, 0), l,
      Equal.trans(U32, U32.or(U32.and(U32.shrn(R.trick.make(s, p, l, o, b), 4n), 7), U32.and(U32.shrn(U32.shln(r, 15n), 4n), 7)), U32.or(l, U32.and(U32.shrn(U32.shln(r, 15n), 4n), 7)), U32.or(l, 0),
        cgu(U32.and(U32.shrn(R.trick.make(s, p, l, o, b), 4n), 7), l, (z => U32.or(z, U32.and(U32.shrn(U32.shln(r, 15n), 4n), 7))), Laws.lead_make(s, p, l, o, b, hs, hp, hl, ho, hb)),
        cgu(U32.and(U32.shrn(U32.shln(r, 15n), 4n), 7), 0, (z => U32.or(l, z)), tr(U32.and(U32.shrn(U32.shln(r, 15n), 4n), 7), U32.and(U32.shrn(U32.shln(r, 15n), 4n), U32.and(U32.shrn(32768, 4n), 7)), 0, Laws.field_mask(U32.shln(r, 15n), 32768, 4n, 7, Laws.shln_sub(15n, r, 32768, hr)), u32.and_zero(U32.shrn(U32.shln(r, 15n), 4n))))),
      u32.or_zero(l)))


# ---------------------------------------------------------------------------
# The winning card through a trick

def idem(+y: U32, +m: U32, +e: {U32.and(m, m) == m : U32}) -> S.Sub32(U32.and(y, m), m):
  tr(U32.and(U32.and(y, m), m), U32.and(y, U32.and(m, m)), U32.and(y, m), Laws.and_assoc32(y, m, m), cgu(U32.and(m, m), m, (z => U32.and(y, z)), e))

def bit1(+b: Bool) -> S.Sub32(Bool.to_u32(b), 1):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# The lead: the card led wins so far, for its seat, and its suit is the suit led.

def Laws.first_win(win, rank, seat, played, lead, owner, best, c, ep, hs, hu, hc):
  %Equal.sym(U32, played, 0, ep) : S.And({R.trick.owner(R.trick.next.go(U32.is_eq(_, 0), U32.is_eq(_, 3), win, rank, seat, _, lead, owner, best, c)) == seat : U32}, S.And({R.trick.best(R.trick.next.go(U32.is_eq(_, 0), U32.is_eq(_, 3), win, rank, seat, _, lead, owner, best, c)) == c : U32}, {R.trick.lead(R.trick.next.go(U32.is_eq(_, 0), U32.is_eq(_, 3), win, rank, seat, _, lead, owner, best, c)) == C.card.suit(c) : U32}))
  (Laws.owner_make(U32.and((seat + 1 : U32), 3), 1, C.card.suit(c), seat, c, idem((seat + 1 : U32), 3, {==}), {==}, hu, hs, hc),
    (Laws.best_make(U32.and((seat + 1 : U32), 3), 1, C.card.suit(c), seat, c, idem((seat + 1 : U32), 3, {==}), {==}, hu, hs, hc),
      Laws.lead_make(U32.and((seat + 1 : U32), 3), 1, C.card.suit(c), seat, c, idem((seat + 1 : U32), 3, {==}), {==}, hu, hs, hc)))

def mid.keep(+win: Bool, +rank: Bool, +seat: U32, +q: U32, +lead: U32, +owner: U32, +best: U32, +c: U32, +ew: {win == False{} : Bool}, +hq: S.Sub32(q, 3), +hl: S.Sub32(lead, 7), +ho: S.Sub32(owner, 3), +hb: S.Sub32(best, 63)) ->
    S.And({R.trick.owner(U32.or(R.trick.make(U32.and((seat + 1 : U32), 3), q, lead, R.sel(win, seat, owner), R.sel(win, c, best)), U32.shln(Bool.to_u32(rank), 15n))) == owner : U32},
      S.And({R.trick.best(U32.or(R.trick.make(U32.and((seat + 1 : U32), 3), q, lead, R.sel(win, seat, owner), R.sel(win, c, best)), U32.shln(Bool.to_u32(rank), 15n))) == best : U32},
        {R.trick.lead(U32.or(R.trick.make(U32.and((seat + 1 : U32), 3), q, lead, R.sel(win, seat, owner), R.sel(win, c, best)), U32.shln(Bool.to_u32(rank), 15n))) == lead : U32})):
  %Equal.sym(Bool, win, False{}, ew) : S.And({R.trick.owner(U32.or(R.trick.make(U32.and((seat + 1 : U32), 3), q, lead, R.sel(_, seat, owner), R.sel(_, c, best)), U32.shln(Bool.to_u32(rank), 15n))) == owner : U32}, S.And({R.trick.best(U32.or(R.trick.make(U32.and((seat + 1 : U32), 3), q, lead, R.sel(_, seat, owner), R.sel(_, c, best)), U32.shln(Bool.to_u32(rank), 15n))) == best : U32}, {R.trick.lead(U32.or(R.trick.make(U32.and((seat + 1 : U32), 3), q, lead, R.sel(_, seat, owner), R.sel(_, c, best)), U32.shln(Bool.to_u32(rank), 15n))) == lead : U32}))
  (Laws.owner_make_r(U32.and((seat + 1 : U32), 3), q, lead, owner, best, Bool.to_u32(rank), idem((seat + 1 : U32), 3, {==}), hq, hl, ho, hb, bit1(rank)),
    (Laws.best_make_r(U32.and((seat + 1 : U32), 3), q, lead, owner, best, Bool.to_u32(rank), idem((seat + 1 : U32), 3, {==}), hq, hl, ho, hb, bit1(rank)),
      Laws.lead_make_r(U32.and((seat + 1 : U32), 3), q, lead, owner, best, Bool.to_u32(rank), idem((seat + 1 : U32), 3, {==}), hq, hl, ho, hb, bit1(rank))))

# The second and third cards: a card that doesn't win leaves the winner, the
# winning card and the suit led as they were.

def Laws.mid_keep(k, lk, nk, win, rank, seat, played, lead, owner, best, c, ep, ew, hl, ho, hb):
  match k:
    case 0n:
      Empty.absurd(S.And({R.trick.owner(R.trick.next.go(U32.is_eq(played, 0), U32.is_eq(played, 3), win, rank, seat, played, lead, owner, best, c)) == owner : U32}, S.And({R.trick.best(R.trick.next.go(U32.is_eq(played, 0), U32.is_eq(played, 3), win, rank, seat, played, lead, owner, best, c)) == best : U32}, {R.trick.lead(R.trick.next.go(U32.is_eq(played, 0), U32.is_eq(played, 3), win, rank, seat, played, lead, owner, best, c)) == lead : U32})), no_tf(nk))
    case 1n:
      %Equal.sym(U32, played, U32.from_nat(1n), ep) : S.And({R.trick.owner(R.trick.next.go(U32.is_eq(_, 0), U32.is_eq(_, 3), win, rank, seat, _, lead, owner, best, c)) == owner : U32}, S.And({R.trick.best(R.trick.next.go(U32.is_eq(_, 0), U32.is_eq(_, 3), win, rank, seat, _, lead, owner, best, c)) == best : U32}, {R.trick.lead(R.trick.next.go(U32.is_eq(_, 0), U32.is_eq(_, 3), win, rank, seat, _, lead, owner, best, c)) == lead : U32}))
      mid.keep(win, rank, seat, 2, lead, owner, best, c, ew, {==}, hl, ho, hb)
    case 2n:
      %Equal.sym(U32, played, U32.from_nat(2n), ep) : S.And({R.trick.owner(R.trick.next.go(U32.is_eq(_, 0), U32.is_eq(_, 3), win, rank, seat, _, lead, owner, best, c)) == owner : U32}, S.And({R.trick.best(R.trick.next.go(U32.is_eq(_, 0), U32.is_eq(_, 3), win, rank, seat, _, lead, owner, best, c)) == best : U32}, {R.trick.lead(R.trick.next.go(U32.is_eq(_, 0), U32.is_eq(_, 3), win, rank, seat, _, lead, owner, best, c)) == lead : U32}))
      mid.keep(win, rank, seat, 3, lead, owner, best, c, ew, {==}, hl, ho, hb)
    case 3n+y:
      Empty.absurd(S.And({R.trick.owner(R.trick.next.go(U32.is_eq(played, 0), U32.is_eq(played, 3), win, rank, seat, played, lead, owner, best, c)) == owner : U32}, S.And({R.trick.best(R.trick.next.go(U32.is_eq(played, 0), U32.is_eq(played, 3), win, rank, seat, played, lead, owner, best, c)) == best : U32}, {R.trick.lead(R.trick.next.go(U32.is_eq(played, 0), U32.is_eq(played, 3), win, rank, seat, played, lead, owner, best, c)) == lead : U32})), no_lt0(y, lk))


# ---------------------------------------------------------------------------
# Nothing beats the top card at no trumps

def Laws.code_at(s, r, ls, lr):
  match s r:
    case 0n 0n:
      {==}
    case 0n 1n:
      {==}
    case 0n 2n:
      {==}
    case 0n 3n:
      {==}
    case 0n 4n:
      {==}
    case 0n 5n:
      {==}
    case 0n 6n:
      {==}
    case 0n 7n:
      {==}
    case 0n 8n:
      {==}
    case 0n 9n:
      {==}
    case 0n 10n:
      {==}
    case 0n 11n:
      {==}
    case 0n 12n:
      {==}
    case 0n 13n+y:
      Empty.absurd({S.code.at(0n, 13n+y) == True{} : Bool}, no_lt0(y, lr))
    case 1n 0n:
      {==}
    case 1n 1n:
      {==}
    case 1n 2n:
      {==}
    case 1n 3n:
      {==}
    case 1n 4n:
      {==}
    case 1n 5n:
      {==}
    case 1n 6n:
      {==}
    case 1n 7n:
      {==}
    case 1n 8n:
      {==}
    case 1n 9n:
      {==}
    case 1n 10n:
      {==}
    case 1n 11n:
      {==}
    case 1n 12n:
      {==}
    case 1n 13n+y:
      Empty.absurd({S.code.at(1n, 13n+y) == True{} : Bool}, no_lt0(y, lr))
    case 2n 0n:
      {==}
    case 2n 1n:
      {==}
    case 2n 2n:
      {==}
    case 2n 3n:
      {==}
    case 2n 4n:
      {==}
    case 2n 5n:
      {==}
    case 2n 6n:
      {==}
    case 2n 7n:
      {==}
    case 2n 8n:
      {==}
    case 2n 9n:
      {==}
    case 2n 10n:
      {==}
    case 2n 11n:
      {==}
    case 2n 12n:
      {==}
    case 2n 13n+y:
      Empty.absurd({S.code.at(2n, 13n+y) == True{} : Bool}, no_lt0(y, lr))
    case 3n 0n:
      {==}
    case 3n 1n:
      {==}
    case 3n 2n:
      {==}
    case 3n 3n:
      {==}
    case 3n 4n:
      {==}
    case 3n 5n:
      {==}
    case 3n 6n:
      {==}
    case 3n 7n:
      {==}
    case 3n 8n:
      {==}
    case 3n 9n:
      {==}
    case 3n 10n:
      {==}
    case 3n 11n:
      {==}
    case 3n 12n:
      {==}
    case 3n 13n+y:
      Empty.absurd({S.code.at(3n, 13n+y) == True{} : Bool}, no_lt0(y, lr))
    case 4n+y _:
      Empty.absurd({S.code.at(4n+y, r) == True{} : Bool}, no_lt0(y, ls))

def or_ff(+a: Bool, +b: Bool, +ea: {a == False{} : Bool}, +eb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, ea) : {Bool.or(_, b) == False{} : Bool}
  eb

def and_fl(+a: Bool, +b: Bool, +ea: {a == False{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, ea) : {Bool.and(_, b) == False{} : Bool}
  {==}

def and_fr(+a: Bool, +b: Bool, +eb: {b == False{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      {==}

def Laws.lt_ne(n, m, e):
  match n m:
    case 0n 0n:
      Empty.absurd({Cmp.is_eq(Nat.cmp(0n, 0n)) == False{} : Bool}, no_ft(e))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Laws.lt_ne(p, q, e)

def Laws.lt_ngt(n, m, e):
  match n m:
    case 0n _:
      match m:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p 0n:
      Empty.absurd({Cmp.is_gt(Nat.cmp(1n+p, 0n)) == False{} : Bool}, no_ft(e))
    case 1n+p 1n+q:
      Laws.lt_ngt(p, q, e)

def add.s(+a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, (z => 1n+z), Nat.add(p, 1n+b), 1n+Nat.add(p, b), add.s(p, b))

def cmp_x(+x: Nat, +b: Nat) -> {Nat.cmp(x, 1n+Nat.add(b, x)) == LT{} : Cmp}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), add.s(b, p)) : {Nat.cmp(p, _) == LT{} : Cmp}
      cmp_x(p, b)

def cmp_x2(+x: Nat, +b: Nat) -> {Nat.cmp(1n+Nat.add(b, x), x) == GT{} : Cmp}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), add.s(b, p)) : {Nat.cmp(_, p) == GT{} : Cmp}
      cmp_x2(p, b)

def cmp_refl(+x: Nat) -> {Nat.cmp(x, x) == EQ{} : Cmp}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      cmp_refl(p)

# Adding the same to both sides keeps the order.

def Laws.cmp_add(a, b, x):
  match a b:
    case 0n 0n:
      cmp_refl(x)
    case 0n 1n+q:
      cmp_x(x, q)
    case 1n+p 0n:
      cmp_x2(x, p)
    case 1n+p 1n+q:
      Laws.cmp_add(p, q, x)

def ok.a(+c: U32, +ok: {S.card.shape(c) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(C.card.suit(c)), 4n) == True{} : Bool}:
  Sigma.fst.bool(Nat.is_lt(U32.to_nat(C.card.suit(c)), 4n), Bool.and(Nat.is_lt(U32.to_nat(C.card.rank(c)), 13n), U32.is_eq(c, C.card.make(C.card.suit(c), C.card.rank(c)))), and_true(Nat.is_lt(U32.to_nat(C.card.suit(c)), 4n), Bool.and(Nat.is_lt(U32.to_nat(C.card.rank(c)), 13n), U32.is_eq(c, C.card.make(C.card.suit(c), C.card.rank(c)))), ok))

def ok.bc(+c: U32, +ok: {S.card.shape(c) == True{} : Bool}) -> {Bool.and(Nat.is_lt(U32.to_nat(C.card.rank(c)), 13n), U32.is_eq(c, C.card.make(C.card.suit(c), C.card.rank(c)))) == True{} : Bool}:
  Sigma.snd.bool(Nat.is_lt(U32.to_nat(C.card.suit(c)), 4n), Bool.and(Nat.is_lt(U32.to_nat(C.card.rank(c)), 13n), U32.is_eq(c, C.card.make(C.card.suit(c), C.card.rank(c)))), and_true(Nat.is_lt(U32.to_nat(C.card.suit(c)), 4n), Bool.and(Nat.is_lt(U32.to_nat(C.card.rank(c)), 13n), U32.is_eq(c, C.card.make(C.card.suit(c), C.card.rank(c)))), ok))

def ok.b(+c: U32, +ok: {S.card.shape(c) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(C.card.rank(c)), 13n) == True{} : Bool}:
  Sigma.fst.bool(Nat.is_lt(U32.to_nat(C.card.rank(c)), 13n), U32.is_eq(c, C.card.make(C.card.suit(c), C.card.rank(c))), and_true(Nat.is_lt(U32.to_nat(C.card.rank(c)), 13n), U32.is_eq(c, C.card.make(C.card.suit(c), C.card.rank(c))), ok.bc(c, ok)))

def ok.c(+c: U32, +ok: {S.card.shape(c) == True{} : Bool}) -> {c == C.card.make(C.card.suit(c), C.card.rank(c)) : U32}:
  Laws.u32_eq(c, C.card.make(C.card.suit(c), C.card.rank(c)), Sigma.snd.bool(Nat.is_lt(U32.to_nat(C.card.rank(c)), 13n), U32.is_eq(c, C.card.make(C.card.suit(c), C.card.rank(c))), and_true(Nat.is_lt(U32.to_nat(C.card.rank(c)), 13n), U32.is_eq(c, C.card.make(C.card.suit(c), C.card.rank(c))), ok.bc(c, ok))))

def ne4(+x: U32, +lt: {Nat.is_lt(U32.to_nat(x), 4n) == True{} : Bool}) -> {U32.is_eq(x, 4) == False{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(x, 4), Nat.cmp(U32.to_nat(x), U32.to_nat(4)), Laws.u32_cmp_nat(x, 4)) : {Cmp.is_eq(_) == False{} : Bool}
  Laws.lt_ne(U32.to_nat(x), 4n, lt)

def code.nat(+s: Nat, +r: Nat, +ls: {Nat.is_lt(s, 4n) == True{} : Bool}, +lr: {Nat.is_lt(r, 13n) == True{} : Bool}) -> {U32.to_nat(C.card.make(U32.from_nat(s), U32.from_nat(r))) == Nat.add(r, Nat.mul(16n, s)) : Nat}:
  nat.eq(U32.to_nat(C.card.make(U32.from_nat(s), U32.from_nat(r))), Nat.add(r, Nat.mul(16n, s)), Laws.code_at(s, r, ls, lr))

# A card of the suit with a lower rank is a lower code.

def card.nat(+c: U32, +j: Nat, +lj: {Nat.is_lt(j, 4n) == True{} : Bool}, +ok: {S.card.shape(c) == True{} : Bool}, +es: {C.card.suit(c) == U32.from_nat(j) : U32}) -> {U32.to_nat(c) == Nat.add(U32.to_nat(C.card.rank(c)), Nat.mul(16n, j)) : Nat}:
  Equal.trans(Nat, U32.to_nat(c), U32.to_nat(C.card.make(U32.from_nat(j), U32.from_nat(U32.to_nat(C.card.rank(c))))), Nat.add(U32.to_nat(C.card.rank(c)), Nat.mul(16n, j)),
    Equal.cong(U32, Nat, (z => U32.to_nat(z)), c, C.card.make(U32.from_nat(j), U32.from_nat(U32.to_nat(C.card.rank(c)))),
      Equal.trans(U32, c, C.card.make(C.card.suit(c), C.card.rank(c)), C.card.make(U32.from_nat(j), U32.from_nat(U32.to_nat(C.card.rank(c)))), ok.c(c, ok),
        Equal.trans(U32, C.card.make(C.card.suit(c), C.card.rank(c)), C.card.make(U32.from_nat(j), C.card.rank(c)), C.card.make(U32.from_nat(j), U32.from_nat(U32.to_nat(C.card.rank(c)))),
          Equal.cong(U32, U32, (z => C.card.make(z, C.card.rank(c))), C.card.suit(c), U32.from_nat(j), es),
          Equal.cong(U32, U32, (z => C.card.make(U32.from_nat(j), z)), C.card.rank(c), U32.from_nat(U32.to_nat(C.card.rank(c))), Equal.sym(U32, U32.from_nat(U32.to_nat(C.card.rank(c))), C.card.rank(c), Laws.u32_roundtrip(C.card.rank(c))))))),
    code.nat(j, U32.to_nat(C.card.rank(c)), lj, ok.b(c, ok)))

def gt.no(+c: U32, +j: Nat, +r: Nat, +lj: {Nat.is_lt(j, 4n) == True{} : Bool}, +lr: {Nat.is_lt(r, 13n) == True{} : Bool}, +ok: {S.card.shape(c) == True{} : Bool}, +es: {C.card.suit(c) == U32.from_nat(j) : U32}, +er: {Nat.is_lt(U32.to_nat(C.card.rank(c)), r) == True{} : Bool}) -> {U32.is_gt(c, C.card.make(U32.from_nat(j), U32.from_nat(r))) == False{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(c, C.card.make(U32.from_nat(j), U32.from_nat(r))), Nat.cmp(U32.to_nat(c), U32.to_nat(C.card.make(U32.from_nat(j), U32.from_nat(r)))), Laws.u32_cmp_nat(c, C.card.make(U32.from_nat(j), U32.from_nat(r)))) : {Cmp.is_gt(_) == False{} : Bool}
  %Equal.sym(Nat, U32.to_nat(c), Nat.add(U32.to_nat(C.card.rank(c)), Nat.mul(16n, j)), card.nat(c, j, lj, ok, es)) : {Cmp.is_gt(Nat.cmp(_, U32.to_nat(C.card.make(U32.from_nat(j), U32.from_nat(r))))) == False{} : Bool}
  %Equal.sym(Nat, U32.to_nat(C.card.make(U32.from_nat(j), U32.from_nat(r))), Nat.add(r, Nat.mul(16n, j)), code.nat(j, r, lj, lr)) : {Cmp.is_gt(Nat.cmp(Nat.add(U32.to_nat(C.card.rank(c)), Nat.mul(16n, j)), _)) == False{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(Nat.add(U32.to_nat(C.card.rank(c)), Nat.mul(16n, j)), Nat.add(r, Nat.mul(16n, j))), Nat.cmp(U32.to_nat(C.card.rank(c)), r), Laws.cmp_add(U32.to_nat(C.card.rank(c)), r, Nat.mul(16n, j))) : {Cmp.is_gt(_) == False{} : Bool}
  Laws.lt_ngt(U32.to_nat(C.card.rank(c)), r, er)

def beats.first(+c: U32, +j: Nat, +r: Nat, +lj: {Nat.is_lt(j, 4n) == True{} : Bool}, +lr: {Nat.is_lt(r, 13n) == True{} : Bool}, +ok: {S.card.shape(c) == True{} : Bool},
    lo: Either<&2, &2, {U32.is_eq(C.card.suit(c), U32.from_nat(j)) == False{} : Bool}, S.And({C.card.suit(c) == U32.from_nat(j) : U32}, {Nat.is_lt(U32.to_nat(C.card.rank(c)), r) == True{} : Bool})>) ->
    {Bool.and(U32.is_eq(C.card.suit(c), C.card.suit(C.card.make(U32.from_nat(j), U32.from_nat(r)))), U32.is_gt(c, C.card.make(U32.from_nat(j), U32.from_nat(r)))) == False{} : Bool}:
  match lo:
    case Inl{e}:
      and_fl(U32.is_eq(C.card.suit(c), C.card.suit(C.card.make(U32.from_nat(j), U32.from_nat(r)))), U32.is_gt(c, C.card.make(U32.from_nat(j), U32.from_nat(r))),
        Equal.trans(Bool, U32.is_eq(C.card.suit(c), C.card.suit(C.card.make(U32.from_nat(j), U32.from_nat(r)))), U32.is_eq(C.card.suit(c), U32.from_nat(j)), False{},
          Equal.cong(U32, Bool, (z => U32.is_eq(C.card.suit(c), z)), C.card.suit(C.card.make(U32.from_nat(j), U32.from_nat(r))), U32.from_nat(j), card.suit.of(j, r, lj, lr)), e))
    case Inr{p}:
      (+es, +er) = p
      and_fr(U32.is_eq(C.card.suit(c), C.card.suit(C.card.make(U32.from_nat(j), U32.from_nat(r)))), U32.is_gt(c, C.card.make(U32.from_nat(j), U32.from_nat(r))), gt.no(c, j, r, lj, lr, ok, es, er))

# At no trumps, no card beats the card led when it is of another suit, or of the
# suit with a lower rank.

def Laws.beats_top(j, r, c, lj, lr, ok, lo):
  or_ff(Bool.and(U32.is_eq(C.card.suit(c), C.card.suit(C.card.make(U32.from_nat(j), U32.from_nat(r)))), U32.is_gt(c, C.card.make(U32.from_nat(j), U32.from_nat(r)))),
    Bool.and(U32.is_eq(C.card.suit(c), 4), U32.is_ne(C.card.suit(C.card.make(U32.from_nat(j), U32.from_nat(r))), 4)),
    beats.first(c, j, r, lj, lr, ok, lo),
    and_fl(U32.is_eq(C.card.suit(c), 4), U32.is_ne(C.card.suit(C.card.make(U32.from_nat(j), U32.from_nat(r))), 4), ne4(C.card.suit(c), ok.a(c, ok))))

def Laws.unit_lt(n, q, r, lq, h):
  match n:
    case 0n:
      Empty.absurd({Nat.is_lt(q, r) == True{} : Bool}, no_lt0(q, lq))
    case 1n+p:
      match q r:
        case 0n 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, no_ft(hd(p, False{}, True{}, Word.and(p, Word.zero(p), S.ones(p, 0n)), Word.zero(p), h)))
        case 0n 1n+i:
          {==}
        case 1n+k 0n:
          Empty.absurd({Nat.is_lt(1n+k, 0n) == True{} : Bool}, no_lt0(k, Laws.unit_lt(p, k, 0n, lq, tl(p, False{}, False{}, Word.and(p, S.unit(p, k), S.ones(p, 0n)), S.unit(p, k), h))))
        case 1n+k 1n+i:
          Laws.unit_lt(p, k, i, lq, tl(p, False{}, False{}, Word.and(p, S.unit(p, k), S.ones(p, i)), S.unit(p, k), h))

def sub.at(-a: U32, -b: U32, +k: U32, e: {a == b : U32}, h: S.Sub32(a, k)) -> S.Sub32(b, k):
  %e : S.Sub32(_, k)
  h

def hi.back(+b: U32, +h: U32, +hb: S.Sub32(b, 65535), +i: S.Sub32(U32.shln(b, 16n), h)) -> S.Sub32(b, U32.shrn(h, 16n)):
  sub.at(U32.shrn(U32.shln(b, 16n), 16n), b, U32.shrn(h, 16n), Equal.trans(U32, U32.shrn(U32.shln(b, 16n), 16n), U32.and(b, S.keep(16n)), b, Laws.shrn_shln(16n, b), hb), Laws.shrn_mono(16n, U32.shln(b, 16n), h, i))

def lo.back(+b: U32, +h: U32, +hb: S.Sub32(b, 65535), +i: S.Sub32(b, h)) -> S.Sub32(b, U32.and(h, 65535)):
  Equal.trans(U32, U32.and(b, U32.and(h, 65535)), U32.and(U32.and(b, h), 65535), b, Equal.sym(U32, U32.and(U32.and(b, h), 65535), U32.and(b, U32.and(h, 65535)), Laws.and_assoc32(b, h, 65535)),
    Equal.trans(U32, U32.and(U32.and(b, h), 65535), U32.and(b, 65535), b, Equal.cong(U32, U32, (z => U32.and(z, 65535)), U32.and(b, h), b, i), hb))

# What playing a card of suit j takes out of a hand is the card's bit in that
# suit's holding.

def back.j(+j: Nat, +b: U32, +h01: U32, +h23: U32, +lj: {Nat.is_lt(j, 4n) == True{} : Bool}, +hb: S.Sub32(b, 65535),
    +i1: S.Sub32(R.sel(U32.is_lt(U32.from_nat(j), 2), R.sel(U32.is_zero((U32.from_nat(j) .&. 1 : U32)), (b << 16n : U32), b), 0), h01),
    +i2: S.Sub32(R.sel(U32.is_lt(U32.from_nat(j), 2), 0, R.sel(U32.is_zero((U32.from_nat(j) .&. 1 : U32)), (b << 16n : U32), b)), h23)) -> S.Sub32(b, R.suit.mask(j, h01, h23)):
  match j:
    case 0n:
      hi.back(b, h01, hb, i1)
    case 1n:
      lo.back(b, h01, hb, i1)
    case 2n:
      hi.back(b, h23, hb, i2)
    case 3n:
      lo.back(b, h23, hb, i2)
    case 4n+y:
      Empty.absurd(S.Sub32(b, R.suit.mask(4n+y, h01, h23)), no_lt0(y, lj))

def lt32(+q: Nat, +lq: {Nat.is_lt(q, 13n) == True{} : Bool}) -> {Nat.is_lt(q, 32n) == True{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n+x:
      Empty.absurd({Nat.is_lt(13n+x, 32n) == True{} : Bool}, no_lt0(x, lq))

def bit16(+q: Nat, +lq: {Nat.is_lt(q, 13n) == True{} : Bool}) -> S.Sub32((1 << q : U32), 65535):
  match q:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n+x:
      Empty.absurd(S.Sub32((1 << 13n+x : U32), 65535), no_lt0(x, lq))

def below.go(+bq: Bool, +c: U32, +j: Nat, +r: Nat, +h01: U32, +h23: U32, +eb: {U32.is_eq(C.card.suit(c), U32.from_nat(j)) == bq : Bool}, +ok: {S.card.shape(c) == True{} : Bool},
    +i1: S.Sub32(S.play.a(c), h01), +i2: S.Sub32(S.play.b(c), h23), +top: S.Sub32(R.suit.mask(j, h01, h23), U32{S.ones(32n, r)}), +lj: {Nat.is_lt(j, 4n) == True{} : Bool}) ->
    Either<&2, &2, {U32.is_eq(C.card.suit(c), U32.from_nat(j)) == False{} : Bool}, S.And({C.card.suit(c) == U32.from_nat(j) : U32}, {Nat.is_lt(U32.to_nat(C.card.rank(c)), r) == True{} : Bool})>:
  match bq:
    case False{}:
      Inl{eb}
    case True{}:
      +es = Laws.u32_eq(C.card.suit(c), U32.from_nat(j), eb)
      +q = U32.to_nat(C.card.rank(c))
      +lq = ok.b(c, ok)
      +sm = back.j(j, C.card.bit(c), h01, h23, lj, bit16(q, lq),
        sub.at(S.play.a(c), R.sel(U32.is_lt(U32.from_nat(j), 2), R.sel(U32.is_zero((U32.from_nat(j) .&. 1 : U32)), (C.card.bit(c) << 16n : U32), C.card.bit(c)), 0), h01,
          Equal.cong(U32, U32, (z => R.sel(U32.is_lt(z, 2), R.sel(U32.is_zero((z .&. 1 : U32)), (C.card.bit(c) << 16n : U32), C.card.bit(c)), 0)), C.card.suit(c), U32.from_nat(j), es), i1),
        sub.at(S.play.b(c), R.sel(U32.is_lt(U32.from_nat(j), 2), 0, R.sel(U32.is_zero((U32.from_nat(j) .&. 1 : U32)), (C.card.bit(c) << 16n : U32), C.card.bit(c))), h23,
          Equal.cong(U32, U32, (z => R.sel(U32.is_lt(z, 2), 0, R.sel(U32.is_zero((z .&. 1 : U32)), (C.card.bit(c) << 16n : U32), C.card.bit(c)))), C.card.suit(c), U32.from_nat(j), es), i2))
      +so = Laws.sub_trans32(C.card.bit(c), R.suit.mask(j, h01, h23), U32{S.ones(32n, r)}, sm, top)
      Inr{(es, Laws.unit_lt(32n, q, r, lt32(q, lq),
        u.unwrap(Word.and(32n, S.unit(32n, q), S.ones(32n, r)), S.unit(32n, q),
          sub.at((1 << q : U32), U32{S.unit(32n, q)}, U32{S.ones(32n, r)}, Equal.sym(U32, U32{S.unit(32n, q)}, (1 << q : U32), Laws.unit_shl(q, lq)), so))))}

# A card of another hand, when no card of that hand in suit j is as high as rank r,
# is of another suit or lower in suit j.

def Laws.below_top(c, j, r, h01, h23, ok, i1, i2, top, lj):
  below.go(U32.is_eq(C.card.suit(c), U32.from_nat(j)), c, j, r, h01, h23, {==}, ok, i1, i2, top, lj)
