# bend-dd

A double dummy bridge solver written in [Bend2](https://bend2.dev/).

A double dummy solver takes a bridge deal with all four hands visible and
computes, for every declarer and every strain, how many tricks can be won
with perfect play by both sides. The goal of this project is to build one in
Bend, using its parallel runtime (CPU and GPU) to search the game tree, and
to check its answers against Bo Haglund's
[DDS](https://privat.bahnhof.se/wb758135/bridge/index.html), the reference
double dummy solver.

## Status

Phases 0 and 1 of the [plan](docs/PLAN.md) are done. There is a dealer, a PBN
parser and printer, the rules of play, and a brute-force minimax that matches
DDS on thousands of small endings. It can't solve full deals yet: that needs the
search from Phase 2 on.

## Requirements

Bend2 (`curl -fsSL https://bend-lang.com/install.sh | sh`), last tested with
2.0.40. Native builds need clang 14 or newer. The checks against DDS need
Python 3, and `tools/test.sh` makes a `.venv` with
[endplay](https://github.com/dominicprice/endplay) on its first run.

## Usage

Run it directly:

```sh
bend hand.bend          # deal number 1
bend hand.bend 42       # deal number 42
```

Or build a native executable:

```sh
bend hand.bend -o hand
./hand 42
```

The deal number seeds the shuffle, so the same number always gives the same
deal. The output is a hand diagram followed by the deal in
[PBN](https://www.tistis.nl/pbn/) form, which is what DDS takes as input:

```
Deal 42

            North
            ♠ A8
            ❤︎ J94
            ◆ KQ62
            ♣ KT86
West                    East
♠ T952                  ♠ K64
❤︎ T2                    ❤︎ 873
◆ JT754                 ◆ A3
♣ 97                    ♣ Q5432
            South
            ♠ QJ73
            ❤︎ AKQ65
            ◆ 98
            ♣ AJ

N:A8.J94.KQ62.KT86 K64.873.A3.Q5432 QJ73.AKQ65.98.AJ T952.T2.JT754.97
```

`dd` reads PBN deals, from its arguments (quoted, one deal per argument) or
from files with one deal per line, and prints them back in canonical form:

```sh
bend dd.bend -o dd
./dd "E:K64.873.A3.Q5432 QJ73.AKQ65.98.AJ T952.T2.JT754.97 A8.J94.KQ62.KT86"
```

`dd --brute` solves small endings by plain minimax. Each deal prints the 20
entries of its double dummy table, by strain (♠ ♥ ♦ ♣ NT) and then declarer
(N E S W) as in DDS's `TABLE` lines, followed by the positions visited:

```sh
./dd --brute "N:AK... Q.J.. J..A. T..K."
```

Use it for endings of up to about 5 cards in each hand. Runtime options go
between `+RTS` and `-RTS`, such as `+RTS --threads 8 -RTS`.

## Testing

```sh
tools/test.sh           # build, check the proofs and run every test
tools/test.sh --quick   # skip the proofs and shrink the DDS comparison
```

The proofs are in `LAWS.bend` and `PROOF.bend`, and take several minutes to
check. `tools/check.py` compares `dd` against DDS: see its `--help`. The DDS test
files in `tests/data` are vendored under the Apache 2.0 license.

## Roadmap

The full plan, with the algorithm choices and the testing strategy, is in
[docs/PLAN.md](docs/PLAN.md). In short:

1. Deal and print hands (done).
2. Represent the deal as bitboards, generate legal plays and brute-force small
   endings (done).
3. Solve a single strain and lead with alpha-beta search.
4. Add transposition tables, move ordering and quick tricks.
5. Compute the full 4 x 5 table of trick counts, compared against DDS.
6. Parallelize the search with Bend's parallel calls.
