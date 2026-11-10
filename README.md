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
does about 16 deals a second on 12 threads, against about 70 for DDS on the same
machine. Closing that gap is Phase 6, which is under way.

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

To deal a random hand and see its double dummy table, run:

```sh
tools/deal.sh           # a random deal
tools/deal.sh 42        # deal number 42
```

It builds `dd` if needed and runs `dd --random`, which prints the hand diagram,
the deal in PBN, and the tricks each declarer takes in each strain:

```
    NT  ♠   ❤︎   ◆   ♣
N   11  11  11  9   10
S   11  11  11  9   10
E   2   2   2   4   3
W   2   2   2   4   3
```

A full deal takes well under a second, with each strain on its own thread. The
seed is printed with the deal, so `tools/deal.sh <seed>` shows it again.

`dd` reads PBN deals, from its arguments (quoted, one deal per argument) or
from files with one deal per line, and solves them. Each deal prints the 20
entries of its double dummy table, by strain (♠ ♥ ♦ ♣ NT) and then declarer
(N E S W) as in DDS's `TABLE` lines, followed by the positions visited:

```sh
bend dd.bend -o dd
./dd "N:AK... Q.J.. J..A. T..K."
```

Runtime
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

## Simulation

At the table nobody sees all four hands. `sim` takes what one player can see, deals
the hidden cards at random many times, keeps the layouts that fit the auction and
the play, solves each one double dummy, and says for each card the player could
play now how many tricks declarer takes on average and how often the contract
makes. Every layout that fits is equally likely. On an Apple M6 the example below,
200 layouts of an opening lead with 10 cards to try, takes 0.9 s on 12
threads on a quiet machine (the run shown shared it) and 4.4 s on one.

```sh
tools/sim.sh deal="N:- - - T952.T2.JT754.97" contract=4H by=S \
  S.hcp=15-19 S.H=5+ N.hcp=8-11 N.H=3+ n=200 seed=11
```

```
Contract: 4❤︎ by South.

West              ♠ T952  ❤︎ T2  ◆ JT754  ♣ 97

Auction: South 15-19 points, South 5+ ❤︎, North 8-11 points, North 3+ ❤︎.
Trick 1: West to lead.

Dealt 11117 layouts and kept 200 (1.8%), solved in 1607 ms on 12 threads, 44935270 nodes.

Card    Tricks   Makes
♣7      11.15    94.5%
♣9      11.16    94.5%
◆7      11.19    95.0%
◆54     11.19    95.0%
◆JT     11.21    95.5%
♠T9     11.22    96.0%
♠5      11.23    96.0%
♠2      11.23    96.0%
❤︎2      11.31    96.0%
❤︎T      11.32    96.0%

Tricks are declarer's, on average. Makes is how often declarer takes 10 or more.
Best for West first.
Seed 11: add seed=11 to see the same layouts again.
```

The arguments, in any order:

- `deal=` the deal in PBN, with `-` for each hand that can't be seen. A hand in view
  is written whole, as dealt, even after some of it has been played.
- `contract=` such as `4S` or `3NT`, and `by=` declarer's seat. The seat on
  declarer's left leads.
- `play=` the cards played so far, in order, such as `play="DJ D2 DA D8 S2"`. Suit
  first or rank first, `T` or `10`, separated by spaces or commas. The seat to play
  next must be one in view: declarer plays for dummy too, so give both hands.
- Rules from the auction about hidden hands: `W.hcp=11-15` for high card points,
  `W.S=5+` for at least five spades, and also `-3` (at most three), `4` (exactly
  four) and `4-6`. `H`, `D` and `C` for the other suits.
- `n=` the layouts to keep (200), `seed=` to see the same layouts again, and
  `tries=` the deals to try for each layout before giving up on it (1000).

A seat that fails to follow suit is known to be void in it from then on, with no
rule needed. Cards that play the same, such as touching honours, share a row. Each
layout has its own random state, so a seed gives the same layouts whatever the
number of threads. The layouts are split over the threads, each with its own
transposition table, which it keeps from one layout to the next.

Each card is solved by the same search as whole deals, started from the position as
it stands with its root's moves cut to that card (`src/play.bend`). `tests/play`
checks that against brute force from random points in random endings, and
`tools/simcheck.py` replays the first layouts of a simulation in DDS and checks every
card against its `SolveBoard`.

## Web app

`web/` is a page that runs the solver in the browser: the deal, the double dummy
table filling in strain by strain, par, a play-through that shows what every legal
card takes, and the simulator. The solver is Bend's C target built by Emscripten to
WebAssembly, in a pool of Web Workers. `docs/WEBAPP_PLAN.md` has the plan and the
measurements behind that choice: on cadmium a full deal takes 0.4 s with one worker
per strain, and the simulation above 3.5 s on 8 workers.

```sh
tools/web.sh build      # the solver and the page, into web/dist
tools/web.sh serve      # build, then serve it on http://localhost:8642/
tools/web.sh test       # check the page's solver against dd, sim and DDS
tools/web.sh shots      # check the page in Chromium and save web/shots/ (needs Playwright)
tools/web.sh bench      # time native dd, Bend's JS target and WebAssembly on list100
```

It needs Emscripten (`brew install emscripten`) as well as bend, clang, node and
python3; Bun comes inside bend. Everything the page shows is in the link:
`#seed=11&c=4H&by=W&play=S7,SQ` opens deal 11 in 4♥ by West after two cards. Click a
number in the table to play that contract, click cards to play them, and use the
arrow keys to step through. `web/dist` is a folder of static files that any web
server can host.

## iOS app

`ios/` is the web app as an iPhone and iPad app: a SwiftUI app with the page in a
WKWebView, served from the app bundle, with the solver as WebAssembly in workers as
on the web. A page's WebAssembly memories share one cap in WebKit, and each solver
run takes about 530 MB of address space, so the app runs 2 to 4 workers by the
device's memory, and each worker does one job and is replaced
(`web/src/pool.ts`). On the iPhone 18 Pro simulator with 3 workers, a full
play-through takes 8 s and the 1000-layout simulation above 33 s.

```sh
tools/ios.sh sim        # build the page and the app, and run it in the simulator
tools/ios.sh archive    # a signed Release build, in ios/build
tools/ios.sh upload     # archive, then upload to App Store Connect for TestFlight
```

It needs Xcode, xcodegen (`brew install xcodegen`) and what the web app needs.
Signing is automatic with the Apple ID signed in to Xcode, for the team in
`ios/project.yml`, and the bundle ID is `co.formnerd.doubledummy`.

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
