# Plan: a double dummy solver in Bend2

This is the build plan for `bend-dd`. It covers what we are building, how the
standard double dummy algorithms map onto Bend2, the order we build things
in, how we test against DDS, and the questions that are still open.

## 1. Goal

Given a deal with all 52 cards visible, compute the double dummy table: for
each of the 5 strains (♠ ♥ ♦ ♣ NT) and each of the 4 declarers, the number of
tricks declarer takes with perfect play by everyone. That is the same output
as DDS's `CalcDDtable`, and its `TABLE` lines in DDS's test files, so it can be
checked number for number.

Later goals, once the table is right and fast: solve an arbitrary
mid-play position (DDS's `SolveBoard`: the trick count for every legal card),
batch mode over many deals, par scores, and play analysis.

## 2. What we learned

### 2.1 How DDS works

The reference is Bo Haglund and Søren Hein's description of DDS
(`doc/Alg-dds_x.pdf` in [dds-bridge/dds](https://github.com/dds-bridge/dds)),
which builds on Ginsberg's partition search (GIB, JAIR 2001), Chang's 1996 NYU
report, and Pearl's zero-window search. The parts that matter:

1. **Zero-window search on a target.** `Search(pos, target)` only answers
   "can the side to move take at least `target` more tricks?" and returns
   true/false. A driver calls it repeatedly, moving a lower and upper bound
   until they meet (an MTD(f)-style loop). Every search is a null-window
   alpha-beta, which prunes far more than a full-window minimax.
2. **Cheap cutoffs at the start of each trick**, before any card is tried:
   - *Target too low or high*: tricks already won, or tricks won plus tricks
     left, already decide the answer.
   - *Quick tricks*: count sure winners for the side on lead (top cards,
     entries to partner, trumps drawn first in a suit contract).
   - *Later tricks*: count sure tricks the opponents get later (top trumps,
     a stopper in every suit the leader can lead).
3. **Card equivalence.** Cards that are adjacent among the cards still in
   play (AK, or AQ once the K is gone) are one move. This is recomputed every
   trick and cuts the branching factor a lot.
4. **Move ordering.** Hand-tuned weights per position in the trick (leader,
   second hand, third hand, fourth hand), plus "best move" memory from earlier
   cutoffs and from the transposition table. Good ordering is what makes
   alpha-beta fast.
5. **Transposition table with partition search.** Positions are stored only
   at trick boundaries, keyed by the suit lengths of each hand and the leader,
   with lower and upper bounds on future tricks. Each entry also stores the
   *winning ranks*: which cards actually won tricks by rank in the search
   below. Cards below the lowest winning rank in a suit are treated as "x", and
   ranks are stored as relative ranks (AQ97 left in a suit is the same as
   AKQJ). One stored entry then matches many real positions. Winning ranks
   are backed up the tree as a union at each node.
6. **Small-card filter** (Kuijf): a card that was shown never to win by rank
   only needs one representative per hand and suit.

None of this is exotic. The difficulty is getting every piece right and
fast, and testing makes or breaks it.

### 2.2 What Bend2 gives us and what it doesn't

From the Bend guide (`bend guide`, v2.0.x), the Base library, the `WONTFIX`
list and the runtime benchmarks in the Bend repo:

| Bend fact | What it means for the solver |
|---|---|
| Pure and affine; no mutation except `Array`, which has exactly one owner and updates in place | There is no make/undo. A position is an immutable record of a few `U32`s, and "make a move" builds a new record, which is cheap. The transposition table is an `Array<U32>` threaded linearly through the search, so it really is updated in place. |
| `U32` only; `U64` is "coming soon" | No 52-bit card sets. We store hands per suit as 13-bit masks (§3). Hash keys are 32-bit, so a TT entry stores its full key to rule out false matches. |
| Recursion must terminate (structural, left-to-right args); no mutual recursion; no `if`; `match` only on parameters | The search is a single def carrying a `Nat` fuel, with the move loop as a tail self-call, the same shape as Bend's own `queens` benchmark. Decisions are computed by the caller and passed in as `Bool`s. This is verbose but well trodden. No `@unsafe`. |
| Parallelism is binary fork-join with no work stealing; each fork should be balanced | Alpha-beta is sequential by nature and its subtrees are wildly unbalanced, so we parallelize *across* independent searches (strains, leaders, deals), not inside one search, at least at first. |
| `~` template arguments are compiled into separate copies | The trump suit can be a template argument, giving five specialised copies of the hot code with the trump checks folded away. |
| Records of scalars ride in registers; non-tail recursion costs a heap frame; no common-subexpression elimination | Keep the position small and flat, bind values once, and expect per-node overhead to be higher than C. We measure this early (Phase 1). |
| No C escape from pure code (foreign code is IO only) | Everything in the search is Bend. There is no falling back to a C transposition table. |
| GPU: Bend's own `queens` search is ~3.5× slower on an M4 GPU than on its CPU cores | The goal is to use every core and the GPU. The CPU path comes first because it is simpler; the GPU path is designed for, then measured (§5). |
| `Array.fork` plus `Array.atomic.*` exist, but `Array.fork` is `@unsafe` | A shared, lock-free TT across parallel searches is ruled out by the no-`@unsafe` rule. Every parallel search owns its own TT. |
| The checker normalises a pure `main` slowly; compiled `IO` mains are fast | The solver's `main` is IO and is built with `bend dd.bend -o dd`. |

### 2.3 What Phase 1 measured

On an M1 Max (8 performance and 2 efficiency cores) under Bend 2.0.40, running
plain minimax over 2.8 billion nodes of 4-card endings. The machine had other
work running, so these are rough. `bench/brute.c` is the same search in C and
visits exactly the same nodes.

| | nodes/s |
|---|---|
| C, `clang -O2`, 1 thread | 80M |
| Bend, 1 thread | 63M |
| Bend, 2 threads | 124M |
| Bend, 4 threads | 246M |
| Bend, 8 threads | 390M |
| Bend, 10 threads, 16 leaves | 378M |
| Bend, 10 threads, 1024 leaves | 477M |

`bench/gpu.bend` runs the same search on 3-card endings: 113M to 133M nodes/s on
the GPU against about 525M on the CPU threads, so the GPU is 4 to 5 times slower.

What this changes:

- One Bend thread costs about 27% over C, not the several times §8 feared, even
  with a position record and a heap move list at every node.
- A `Nat` is a machine integer at run time and a shift by a `Nat` is one
  instruction. Depth can bound the recursion, so no separate fuel is needed: the
  child call takes one off `d`, and the sibling keeps `d` and drops a move.
- Many more fork leaves than threads balance better, even with no work stealing.
  §5 says to go only as wide as the core count, because each leaf owns a TT. That
  trade-off needs measuring in Phase 5, for example by sharing one TT across the
  deals in a leaf.
- Finite laws cost about 8 ms per case in the checker, so the proof gate is the
  slow part of the tests (`tools/test.sh --quick` skips it). Laws that hold by
  induction are nearly free, so they are worth the extra work.

### 2.4 What Phase 2 measured

`src/search.bend` on the same M1 Max, under Bend 2.0.40. Node counts are exact and
repeat from run to run. The machine had other work running (load 15 to 80), so
times and rates are rough. A node is a card played, counted the same way in both
searches, and each deal is a whole table of 20 searches.

Next to brute force, on 10 threads, totals per row:

| cards per hand | deals | nodes, brute | nodes, search | ratio | ms, brute | ms, search |
|---|---|---|---|---|---|---|
| 3 | 2000 | 55,759,338 | 3,607,167 | 15 | 173 | 32 |
| 4 | 2000 | 2,942,094,712 | 16,079,950 | 183 | 9,153 | 163 |
| 5 | 1000 | 122,644,356,888 | 43,916,908 | 2,793 | 452,066 | 303 |
| 6 | 3 | 12,131,516,935 | 559,222 | 21,694 | 149,914 | 9 |

How far the search goes, per deal (7 cards on 1 thread, the rest on 10, with one
thread per deal at a time):

| cards per hand | deals | mean nodes | median | worst | ms per deal, wall |
|---|---|---|---|---|---|
| 7 | 300 | 2,264,479 | 1,241,486 | 38,446,086 | 86 (1 thread) |
| 8 | 200 | 22,133,476 | 10,689,092 | 236,307,135 | 163 |
| 9 | 100 | 196,973,248 | 104,623,872 | 2,045,911,207 | 1,518 |
| 10 | 30 | 1,533,547,481 | 794,510,643 | 8,508,143,932 | 15,625 |
| 11 | 5 | 9,110,939,553 | 7,605,487,776 | 15,740,756,763 | 123,338 |

What each piece is worth, as mean nodes per deal on 100 7-card endings, with that
piece taken out:

| search | nodes | against the full search |
|---|---|---|
| Full search | 2,434,232 | |
| No card equivalence | 27,309,629 | 11.2× |
| No target cutoffs | 8,941,594 | 3.7× |
| No move ordering | 6,581,147 | 2.7× |
| No guess from the previous leader | 2,739,520 | 1.13× |
| Bisection instead of stepping from the guess | 2,592,248 | 1.06× |

What this changes:

- Each extra card costs about 8 times the nodes, which puts a full 13-card table
  near 6 × 10^11 nodes, or hours. The transposition table has to carry it from
  there, as planned. Phase 3 should be judged on the 8-card set.
- The search runs about 26M nodes/s on one thread, against 63M for brute force.
  Most of the difference is probably that it generates, collapses and orders moves at every
  node. Without ordering the rate rose by up to 2×, but it pays for itself by 7
  cards. This is the first target for the lookup tables of Phase 6.
- One deal runs on one thread, so large endings waste the other cores: the rate on
  10 threads falls from 135M at 8 cards to 74M at 11, as a few long deals fill
  few leaves. The worst deal is 10 to 17 times the mean from 7 to 9 cards, so batches need many leaves
  (§5), and single deals need the fork over strains from Phase 5.
- `Nat` is a checked 48-bit integer at run time, not a wrapping one, so it is the
  node counter: `1n+n` costs a test and past 2^48 the program stops with an error.
  That is days of work at these rates. It runs on the GPU too.
- The search needs no modes and no fuel (§4), and a cut needs no special return: it
  enters the child with no moves and the answer already set.
- Equivalence has to use the cards in play at the *start* of the trick. A card on
  the table still splits a run (with Q on the table, K and J differ), so the search
  carries that mask from trick to trick.

Still unproved: the target cutoff law takes for granted that a result lies between
won and won + left, and equivalence and the search have no law that holds for every
position. Tests stand in for these so far. Search and brute force also start only
from the first card of a trick: mid-trick starts come with Phase 7.

### 2.5 What Phase 3 measured

The same set of 200 random 8-card endings as a whole table per deal, on 10 threads
under load, adding one piece at a time. Node counts are exact; times are rough.

| Search | Mean nodes per deal | ms per deal |
|---|---|---|
| Phase 2 | 22,133,476 | 163 |
| + quick tricks, later tricks, the check after the lead | 3,598,543 | about 26 |
| + best-move memory | 3,294,949 | about 30 |
| + DDS's weights for all four places in the trick | 830,281 | about 10 |

Then with one piece at a time taken out of the final search, or put back to the
Phase 2 ordering. All of them cost more nodes and more time:

| Taken out | Mean nodes | Nodes against full | ms per deal |
|---|---|---|---|
| Nothing | 830,281 | | 9.7 |
| Quick tricks | 1,774,883 | 2.14× | 19.7 |
| Weights on lead | 1,731,616 | 2.09× | 17.5 |
| Weights for the last hand | 1,232,748 | 1.48× | 13.1 |
| Weights for the second hand | 1,154,317 | 1.39× | 13.4 |
| Later tricks | 1,002,687 | 1.21× | 11.5 |
| The check after the lead | 980,090 | 1.18× | 10.9 |
| Weights for the third hand | 921,841 | 1.11× | 11.0 |
| Best-move memory | 889,353 | 1.07× | 10.4 |
| The top card of each suit going first | 871,192 | 1.05× | 10.2 |

How far it goes now, a whole table per deal, one thread per deal at a time on 10:

| Cards per hand | Deals | Mean nodes | Worst | ms per deal, wall |
|---|---|---|---|---|
| 7 | 300 | 126,328 | 997,636 | 9.8 (1 thread) |
| 8 | 200 | 830,281 | 7,698,987 | 63.6 (1 thread), 11.2 (10) |
| 9 | 100 | 4,762,776 | 29,565,080 | 64 |
| 10 | 100 | 34,999,956 | 254,237,288 | 517 |
| 11 | 30 | 342,366,357 | 1,519,005,259 | 6,294 |
| 12 | 10 | 1,659,368,884 | 5,273,690,194 | 45,473 |

Next to brute force, totals: 3 cards, 2000 deals: 55.8M against 1.04M nodes (54×).
4 cards, 2000 deals: 2.94B against 3.27M (899×). 5 cards, 500 deals: 60.2B against
2.92M (20,650×).

What this changes:

- One thread now does about 13M nodes/s, half of Phase 2's 26M, and 10 threads about
  74M. Weights are most of that cost, and they more than pay for it: a node is twice
  as dear and there are 27 times fewer. Lookup tables in Phase 6 can win some of it
  back, since most of the arguments to a weight only change per suit.
- A call can't be destructured inside the search, and that affects any array the
  search reads. Each `Res` carries the value read for the next child, by a helper.
  The transposition table probe in Phase 4 has the same shape.
- The later-tricks rule in the DDS notes that gives more than one trick for two
  suits topped by the opponents at no trumps is not used: a top card can be forced
  out as a discard if its suit is never led, so one trick is all that can be
  claimed by that argument. The notes also give two tricks for the top two trumps
  without a condition; the code asks that one of those hands has two trumps, since
  two singletons fall together.
- The weights are from the notes, which say they only give an idea of DDS's current
  code. They still leave room to tune.

Still unproved: quick and later tricks have no law for every position. They are
checked against true results on whole deals (`check.py sure`, 1100 deals), on
endings against DDS, against brute force, and in a law for a sample of 2-card
endings.

## 3. Data representation

**Cards.** Suit 0..3 = ♠ ♥ ♦ ♣ (as in `hand.bend` and DDS's strain order),
then 4 = NT for strains. Within a suit, a 13-bit mask where bit 12 is the
ace and bit 0 the deuce, so a higher bit is a higher card, the highest card is
`log2` and the lowest is `ctz`. (`hand.bend` uses rank 0 = ace for dealing;
the PBN parser converts.) A single card is one `U32`: `suit << 4 | rank`.

**A position** is the cards left in each hand plus the trick state:

```
type Pos is Data:
  Pos{
    n01: U32, n23: U32,   # North: ♠<<16|♥, ♦<<16|♣
    e01: U32, e23: U32,   # East
    s01: U32, s23: U32,   # South
    w01: U32, w23: U32,   # West
    trick: U32,           # leader (2 bits), cards played so far (2 bits),
                          # lead suit, current winning card and its owner
    won: U32              # tricks won by the side we search for
  }
```

Ten words, all scalars. The cards still in play in a suit are the OR of the
four hands. We start with this packed form; if the shifting turns out to be
expensive, sixteen unpacked masks is the alternative, and we measure both.

**Moves.** The legal moves for a hand are generated as a short cons list of
card codes, with equivalent cards collapsed to one, already sorted by the
ordering weights. A list is the shape Bend walks best (a flat loop), and it
is at most 13 long.

**The search result** is `(ok: Bool, win: winning ranks as 4 × 13-bit masks in
2 words, tt: Array<U32>)`. Returning the table alongside the answer is how it
gets threaded.

**The transposition table** is one `Array<U32>`, for example 2^20 words (4 MB)
per independent search. An entry is about 8 words:

- the suit lengths of N, E and S in three suits (48 bits, 2 words), which with
  the leader is the bucket key, as in DDS;
- the leader plus the lower and upper bound on future tricks (1 word);
- per suit, the owner (2 bits) of each relative rank, top rank first: 26 bits,
  one word per suit (4 words);
- per suit, how many top relative ranks matter (4 bits each, 1 word).

A lookup hashes the key into a bucket of a few entries and checks each
one with a mask and an XOR per suit. A store replaces round-robin within the
bucket. The same array can also hold the "best move per depth" slots for move
ordering.

## 4. The search in Bend

One def, `search`, implements the DDS pseudo-code:

1. At a trick boundary: target-too-low-or-high, quick tricks, later tricks,
   then a TT probe. Any of these can answer straight away.
2. Otherwise generate and order the moves for the hand to play, then walk the
   list: the child search is a non-tail call, the next sibling is a tail call.
   For the side trying to reach the target, stop at the first true; for the
   other side, stop at the first false. Merge winning ranks as in §2.1.
3. At the end of a trick, store the result and its winning ranks in the TT.

Because Bend forbids mutual recursion, "search a node" and "try the next
move" are the same def: a call with a position's moves and a starting answer.
Depth bounds the recursion: a child has one card fewer, and a sibling has the same
depth with one move fewer, so no separate fuel is needed. A child's answer rides
into the next sibling as an argument, and that sibling stops at once if the answer
settles the node.

The **driver** for one strain and leader starts from a guess (half the tricks, or
the answer for the previous leader, later perhaps quick tricks) and narrows the bounds with zero-window
searches, threading the same TT through every call. The four leaders of one
strain share one TT, as in DDS.

## 5. Parallelism

In order of payoff:

1. **Batch of deals × strains.** Many deals, each with five strains, are
   independent searches with their own TT. This is a balanced fork tree with
   thousands of leaves, which is what Bend's scheduler wants. It is the natural
   way to beat DDS on throughput.
2. **One deal's table.** Five strains in parallel (each strain runs its four
   leaders in sequence to share the TT). That is at most 5× and unbalanced, since NT
   and suit contracts take different times. Splitting by leader as well gives 20
   leaves at the cost of less TT sharing; we measure both.
3. **Inside one search** (research, Phase 6): search several targets at once,
   or split the root moves. (A shared TT would need `Array.fork`, which is
   `@unsafe`, so it is out.)
4. **GPU, as a real target.** Erik wants all the compute in use. Two
   obstacles: per-lane work in a search diverges (lanes on the same SIMD group
   wait for each other), and each lane needs its own TT, while the GPU has
   ~16k lanes and the TT is megabytes. The plan is a GPU batch kernel with a
   much smaller TT per lane (or none for the deeper part of the tree), fed
   enough deals to fill the lanes. We then measure deals per second on the GPU
   against the CPU pool. If both help, a batch is split between them in
   proportion to their measured rates. Whether a GPU bang and CPU parallel work
   can actually run at the same time in Bend's runtime is something to test
   early, since Bend runs one computation at a time between effects.

Each parallel leaf owns its own TT, so the TT size times the number of live
leaves must fit in memory. The batch tree should therefore go only as wide
as the core count needs, then run deals in sequence inside each leaf.

## 6. Phases

Each phase ends with something we can run and check.

**Phase 0: Foundations.**
Split the code into modules (`src/cards.bend`, `src/pbn.bend`, `src/deal.bend`,
...) with `hand.bend` reusing them. Add a PBN parser and a `dd` CLI that reads
deals from the arguments or a file. Add the test harness (§7) and a
`LAWS.bend` / `PROOF.bend` pair with the first laws (§7.5).
*Done when:* parse then print round-trips 1,000 deals from `hand.bend`, and
`bend PROOF.bend` prints ALL PROOFS CHECK.

**Phase 1: Rules and a brute-force oracle.**
Legal move generation (follow suit), trick winner with and without trumps,
and a plain minimax with no pruning, for small endings.
*Done when:* it matches DDS on thousands of random 3 to 5 card endings, in every
strain and with every leader. We also record a raw node rate (nodes per
second) to compare with C early.

**Phase 2: Zero-window search.**
The `search` def, the target driver, target-too-low-or-high, card
equivalence, and simple move ordering (high cards and the same suit first).
*Done when:* it matches the brute-force oracle on all small endings and
handles 7 to 8 card endings quickly. We log node counts from here on.
*Done:* see §2.4.

**Phase 3: Cutoffs and ordering.**
Quick tricks, later tricks, and DDS's move-ordering weights per hand position.
*Done when:* node counts drop sharply on the 8-card set, with no wrong
answers.
*Done:* see §2.5.

**Phase 4: Transposition table.**
First an exact-position TT (relative ranks, bounds, bucketed array). Then
partition search: winning-rank backup, masked matching, and the small-card
filter.
*Done when:* full 13-card deals solve and the table matches DDS's `list100`
exactly.

**Phase 5: Full table and batching.**
The 20-entry table, parallel over strains, and a batch mode over many deals.
*Done when:* 100% agreement with DDS on `list1000` (later `list10000`), and we
have a throughput figure next to DDS on the same Mac.

**Phase 6: Performance.**
Read the emitted C for refcount traffic, precompute lookup tables (relative
ranks, equivalence, quick-trick tables) where they beat bit loops, tune TT
size and replacement, and try the intra-search parallelism from §5.

**Phase 6b: GPU.**
A batch kernel on the GPU (§5, item 4): size the per-lane TT, measure deals per
second against the CPU, and split batches across both if that is faster.
*Done when:* the batch mode uses the GPU wherever it raises total throughput,
with results still matching DDS.

**Phase 7: Extras.**
A `SolveBoard`-style API for mid-play positions (tricks for every legal card),
par scores, play analysis, and possibly laws (§7.5).

## 7. Testing

### 7.1 Reference data

- **DDS's own test files** (Apache 2.0): `hands/list100.txt`, `list1000.txt`
  and `list10000.txt` hold random deals in PBN with the expected `TABLE`
  (20 numbers, `[strain][declarer]`). We vendor `list100` and `list1000` into
  `tests/data/` with attribution. These are the acceptance tests.
- **DDS as a live oracle** through the `endplay` Python package (MIT, bundles
  DDS, installs with pip). It can solve any deal, including partial deals and
  mid-trick positions, so it covers the small endings in Phases 1 to 3 and
  random deals from `hand.bend`.

### 7.2 Harness

`tools/check.py` runs the Bend binary over a file of deals, compares each
result with the reference, and prints mismatches (with the PBN, strain and
leader so a failure can be replayed), node counts and timing. The same script
runs on Erik's Mac.

### 7.3 Layers

1. **Unit:** card encoding, PBN round trip, move generation (counts and
   follow-suit), trick winner, equivalence collapsing, relative-rank
   conversion, and TT store then lookup.
2. **Oracle inside Bend:** the brute-force minimax from Phase 1 stays in the
   repo. Every later optimisation is checked against it on random small
   endings, with no Python needed.
3. **Against DDS:** small endings via `endplay`, full deals via the vendored
   lists.
4. **Metamorphic checks** that need no reference: rotating the deal by one
   seat rotates the table; permuting the suits permutes the suit columns and
   leaves NT unchanged; every result is between 0 and 13.
5. **Performance regression:** node counts and time per deal on a fixed set,
   recorded per commit, with DDS timed on the same machine as a baseline.

### 7.4 Where tests run

The cloud sandbox has not been able to run the Bend compiler so far, so today
the tests run on Erik's Mac (we are not using GitHub Actions). One script,
`tools/test.sh`, builds the binaries, checks the proofs and runs every test
layer, so a cloud session can hand it to the Mac in one step.

### 7.5 Laws

Bend can prove laws in `LAWS.bend`. Cheap, useful ones: PBN parse after print
is the identity; the trick winner is the hand with the highest card of the lead
suit or the highest trump; move generation only returns cards in the hand and
follows suit when it can. Each phase adds the laws for what it builds, for
example card equivalence (playing either of two equivalent cards gives the
same result), relative-rank conversion, and that a TT entry only matches
positions it covers. "The fast solver equals brute-force minimax" is the
real prize. We aim for it piece by piece, proving each pruning rule sound on
its own, and keep the tests as the safety net while it stays unproven.

Laws rule out `@unsafe` in anything they cover: Bend fails the proof check for
every def that depends on one. So the search stays termination-checked, with
a `Nat` fuel (§4).

## 8. Risks

- **Per-node cost.** Heap frames for non-tail calls and refcounting on shared
  values could make each node several times more expensive than in C. We
  measure in Phase 1 and design around it, for example by keeping the position
  record flat and taking care over what is marked `+`.
- **TT efficiency** depends on in-place `Array` updates staying in place. One
  accidental copy (an extra owner) turns O(1) into O(n). We check the emitted C.
- **Verbosity.** No `if`, no matching on computed values, and one def for the
  whole search make the code long. Small helper defs and clear naming keep it
  readable. `@unsafe` is not an option, because the laws need checked code.
- **Bend is young** (frequent releases, a "soon" list that includes U64). We
  pin a Bend version in the README and `tools/test.sh`, and re-test when we upgrade.

## 9. Decisions

Answered by Erik on 2026-11-06:

1. **Scope:** the 4 × 5 table per deal is the target output.
2. **Performance bar:** throughput over many deals. Batch mode (§5, item 1)
   is the main event, and single-deal latency matters less.
3. **`@unsafe`:** not used anywhere.
4. **Laws:** yes, proved laws in `LAWS.bend`, growing every phase.
5. **Compute:** use all of it, CPU cores and GPU (Phase 6b).
6. **Tooling:** no GitHub Actions. Tests run on Erik's Mac through
   `tools/test.sh`. Python plus `endplay` as the oracle and the vendored DDS
   lists stay.

Still open: plain text output only, or JSON too.
