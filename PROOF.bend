# PROOF.bend: the proofs of LAWS.bend. `bend PROOF.bend` is the gate.

import Base
import ./src/cards.bend as C
import ./src/pbn.bend as P
import ./src/rules.bend as R
import ./LAWS.bend as Laws

def Laws.holding_roundtrip():
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
