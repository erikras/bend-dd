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
