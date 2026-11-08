# PROOF.bend: the proofs of LAWS.bend. `bend PROOF.bend` is the gate.

import Base
import ./src/cards.bend as C
import ./src/pbn.bend as P
import ./src/rules.bend as R
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

