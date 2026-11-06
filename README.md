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

Phases 0 to 5 of the [plan](docs/PLAN.md) are done. There is a dealer, a PBN parser
and printer, the rules of play, a brute-force minimax as an oracle, and a zero-window
search with target cutoffs, card equivalence, quick and later tricks, DDS's move
ordering, and a transposition table with partition search. It solves whole deals, and
all 1,100 tables of DDS's `list100` and `list1000` match exactly. On an Apple M6 it
does about 8.5 deals a second on 12 threads, against about 73 for DDS on the same
machine. Closing that gap is Phase 6.

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
from files with one deal per line, and solves them. Each deal prints the 20
entries of its double dummy table, by strain (♠ ♥ ♦ ♣ NT) and then declarer
(N E S W) as in DDS's `TABLE` lines, followed by the positions visited:

```sh
bend dd.bend -o dd
./dd "N:AK... Q.J.. J..A. T..K."
```

For now it is for endings: a full 13-card deal takes minutes or more. Runtime
options go between `+RTS` and `-RTS`, such as `+RTS --threads 8 -RTS`.

To see it work on a random ending, with 5 cards in each hand by default:

```sh
./dd --demo             # ending number 1, 5 cards in each hand
./dd --demo 42 8        # ending number 42, 8 cards in each hand
```

That prints the hand diagram, the deal in PBN, a grid of the tricks declarer takes,
statistics for each strain and declarer, and the time:

```
    N   E   S   W
♠   7   0   7   0
❤︎   6   0   6   0
◆   2   4   2   4
♣   3   5   3   5
NT  4   0   4   0
```

`dd --grid` prints only the deal and the grid, and `dd -v` (or `--verbose`) all of it,
for deals you give it the same way as plain `dd`. The statistics are, per strain and
declarer: the seat on lead, the nodes, the zero-window searches and their targets, the
positions cut by target too low or high, quick tricks, later tricks and the check
after the lead, and the legal moves against those left after equivalence. Then
totals, and the speed of a plain search. Plain `dd` has the counting compiled out:
we measured no difference beyond noise, and counting takes about 5 times as long.

`dd --brute` does the same by plain minimax, the oracle the search is checked
against, for endings of up to about 5 cards in each hand. `dd --sure` prints the
tricks the search counts as sure at the start of each entry, to check them against
the true results. `dd --print` prints each
deal back in canonical form, starting from North.

## Testing

```sh
tools/test.sh           # build, check the proofs and run every test
tools/test.sh --quick   # skip the proofs and shrink the DDS comparison
```

The proofs are in `LAWS.bend` and `PROOF.bend`, and take several minutes to
check. `tests/oracle` checks the search against brute force with no Python. `tools/check.py` compares `dd` against DDS: see its `--help`. The DDS test
files in `tests/data` are vendored under the Apache 2.0 license.

## Roadmap

The full plan, with the algorithm choices and the testing strategy, is in
[docs/PLAN.md](docs/PLAN.md). In short:

1. Deal and print hands (done).
2. Represent the deal as bitboards, generate legal plays and brute-force small
   endings (done).
3. Solve a single strain and lead with alpha-beta search (done).
4. Add transposition tables, move ordering and quick tricks (done).
5. Compute the full 4 x 5 table of trick counts, compared against DDS (done).
6. Parallelize the search with Bend's parallel calls (done over strains and deals).
