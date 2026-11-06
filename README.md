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

Early days. So far there is a CLI that deals and prints a bridge hand.

## Requirements

Bend2 (`curl -fsSL https://bend-lang.com/install.sh | sh`). Native builds
need clang 14 or newer.

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

## Roadmap

The full plan, with the algorithm choices and the testing strategy, is in
[docs/PLAN.md](docs/PLAN.md). In short:

1. Deal and print hands (done).
2. Represent the deal as bitboards and generate legal plays.
3. Solve a single strain and lead with alpha-beta search.
4. Add transposition tables, move ordering and quick tricks.
5. Compute the full 4 x 5 table of trick counts, compared against DDS.
6. Parallelize the search with Bend's parallel calls.
