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

Plain minimax over 2.85 to 2.94 billion nodes of 4-card endings under Bend 2.0.40.
`bench/brute.c` is the same search in C and visits exactly the same nodes. The first
numbers came from an M1 Max (8 performance and 2 efficiency cores) with other work
running. This project now runs only on an M6 (2 super, 4 performance and 6 efficiency
cores, a 12-core GPU), measured on 2026-11-06, again with other work on the machine.

| | M1 Max, nodes/s | M6, nodes/s |
|---|---|---|
| C, `clang -O2`, 1 thread | 80M | 145M |
| Bend, 1 thread | 63M | 112M |
| Bend, 2 threads | 124M | 207M |
| Bend, 4 threads | 246M | 335M |
| Bend, 6 threads | | 473M |
| Bend, 8 threads | 390M | 551M |
| Bend, 10 threads, 16 leaves | 378M | |
| Bend, 10 threads, 1024 leaves | 477M | |
| Bend, 12 threads, 1024 leaves | | 689M |

`bench/gpu.bend` runs the same search on 3-card endings. The M1's GPU gave 113M to 133M
nodes/s against about 525M on the CPU threads, 4 to 5 times slower. The M6's GPU gives
27M against 794M, 29 times slower, and was the same on a second run. Its 12 GPU cores
are far fewer than the M1 Max's, and we don't know how much else was using the GPU.
This counts against Phase 6b.

What this changes:

- One Bend thread costs about 27% over C (29% on the M6), not the several times §8
  feared, even with a position record and a heap move list at every node.
- On the M6, 6 threads give 4.2 times one thread and 12 give 6.1 times: the last 6 are
  efficiency cores, which add less than the first 6.
- A `Nat` is a machine integer at run time and a shift by a `Nat` is one
  instruction. Depth can bound the recursion, so no separate fuel is needed: the
  child call takes one off `d`, and the sibling keeps `d` and drops a move.
- Many more fork leaves than threads balance better, even with no work stealing.
  A leaf only holds its TT while it is solving, so width costs no memory (§5).
- Finite laws cost about 8 ms per case in the checker, so the proof gate is the
  slow part of the tests (`tools/test.sh --quick` skips it). Laws that hold by
  induction are nearly free, so they are worth the extra work.

### 2.4 What Phase 2 measured

The Phase 2 search (commit ca1ebc9) under Bend 2.0.40. Node counts are exact and
repeat from run to run, on both machines. Both had other work running (load 15 to 80),
so times and rates are rough. A node is a card played, counted the same way in both
searches, and each deal is a whole table of 20 searches.

Next to brute force, on 10 threads on the M1 and 12 on the M6, totals per row. The 5-
and 6-card rows are different deals on the two machines, since the deals depend on
which rows ran before them:

| cards per hand | deals | nodes, brute | nodes, search | ratio | ms brute, M1 | ms search, M1 | ms brute, M6 | ms search, M6 |
|---|---|---|---|---|---|---|---|---|
| 3 | 2000 | 55,759,338 | 3,607,167 | 15 | 173 | 32 | 86 | 14 |
| 4 | 2000 | 2,942,094,712 | 16,079,950 | 183 | 9,153 | 163 | 4,447 | 69 |
| 5, M1 | 1000 | 122,644,356,888 | 43,916,908 | 2,793 | 452,066 | 303 | | |
| 5, M6 | 1000 | 129,616,911,590 | 43,467,700 | 2,982 | | | 212,194 | 148 |
| 6, M1 | 3 | 12,131,516,935 | 559,222 | 21,694 | 149,914 | 9 | | |
| 6, M6 | 3 | 13,031,944,780 | 1,081,736 | 12,047 | | | 65,866 | 16 |

How far the search goes, per deal (7 cards on 1 thread, the rest on all of them, with
one thread per deal at a time):

| cards per hand | deals | mean nodes | median | worst | ms per deal, M1 | ms per deal, M6 |
|---|---|---|---|---|---|---|
| 7 | 300 | 2,264,479 | 1,241,486 | 38,446,086 | 86 (1 thread) | 49 (1 thread) |
| 8 | 200 | 22,133,476 | 10,689,092 | 236,307,135 | 163 | 95 |
| 9 | 100 | 196,973,248 | 104,623,872 | 2,045,911,207 | 1,518 | 817 |
| 10 | 30 | 1,533,547,481 | 794,510,643 | 8,508,143,932 | 15,625 | 8,741 |
| 11 | 5 | 9,110,939,553 | 7,605,487,776 | 15,740,756,763 | 123,338 | 80,830 |

The times of 8 to 10 cards on the M6 had load 30 to 50 from other work.

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
- The search runs about 26M nodes/s on one thread on the M1 (46M on the M6), against
  63M for brute force (112M).
  Most of the difference is probably that it generates, collapses and orders moves at every
  node. Without ordering the rate rose by up to 2×, but it pays for itself by 7
  cards. This is the first target for the lookup tables of Phase 6.
- One deal runs on one thread, so large endings waste the other cores: the rate on
  the M1's 10 threads falls from 135M at 8 cards to 74M at 11 (M6, 12 threads: 234M to
  113M), as a few long deals fill
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

The same set of 200 random 8-card endings as a whole table per deal, adding one piece
at a time, on the M1's 10 threads and the M6's 12, both with other work running. Node
counts are exact and came out the same on both. M6 times are the best of 3 runs.

| Search | Mean nodes per deal | ms per deal, M1 | ms per deal, M6 |
|---|---|---|---|
| Phase 2 | 22,133,476 | 163 | 95 |
| + quick tricks, later tricks, the check after the lead | 3,598,543 | about 26 | 14.5 |
| + best-move memory | 3,294,949 | about 30 | 18.4 |
| + DDS's weights for all four places in the trick | 830,281 | about 10 | 6.3 |

Then with one piece at a time taken out of the final search, or put back to the
Phase 2 ordering. The M1 column is from before the driver change of §2.6 and the M6
column after it, which is why its node counts differ slightly from the M1's. On the
M1 they all cost more nodes and more time. On the M6, under load 15 to 25, the last
few are within the noise of the full search for time, so they pay for themselves only
narrowly, if at all:

| Taken out | Mean nodes, M1 | Mean nodes, M6 | Nodes against full, M6 | ms per deal, M1 | ms per deal, M6 |
|---|---|---|---|---|---|
| Nothing | 830,281 | 825,796 | | 9.7 | 6.9 |
| Quick tricks | 1,774,883 | 1,768,121 | 2.14× | 19.7 | 14.5 |
| Weights on lead | 1,731,616 | 1,702,397 | 2.06× | 17.5 | 12.1 |
| Weights for the last hand | 1,232,748 | 1,226,395 | 1.49× | 13.1 | 8.7 |
| Weights for the second hand | 1,154,317 | 1,149,316 | 1.39× | 13.4 | 8.4 |
| Later tricks | 1,002,687 | 997,416 | 1.21× | 11.5 | 7.0 |
| The check after the lead | 980,090 | 974,505 | 1.18× | 10.9 | 6.9 |
| Weights for the third hand | 921,841 | 920,652 | 1.11× | 11.0 | 6.6 |
| Best-move memory | 889,353 | 884,428 | 1.07× | 10.4 | 6.6 |
| The top card of each suit going first | 871,192 | 866,423 | 1.05× | 10.2 | 7.2 |

How far it goes without a table, a whole table per deal, one thread per deal at a time.
The M6 rows are after the driver change, and the M1's before it:

| Cards per hand | Deals | Mean nodes, M6 | Worst, M6 | ms per deal, M1 | ms per deal, M6 |
|---|---|---|---|---|---|
| 3 | 2000 | 409 | 1,370 | | 0.005 |
| 4 | 2000 | 1,489 | 8,444 | | 0.012 |
| 5 | 1000 | 5,706 | 36,957 | | 0.05 |
| 6 | 500 | 24,418 | 187,085 | | 0.18 |
| 7 | 300 | 125,168 | 1,000,720 | 9.8 (1 thread) | 5.4 (1 thread) |
| 8 | 200 | 825,796 | 7,668,729 | 63.6 (1 thread), 11.2 (10) | 35.1 (1 thread), 7.0 (12) |
| 9 | 100 | 4,743,849 | 30,169,311 | 64 | 40 |
| 10 | 100 | 35,045,873 | 252,577,378 | 517 | 287 |
| 11 | 30 | 342,093,094 | 1,517,960,014 | 6,294 | 3,735 |
| 12 | 10 | 1,658,252,702 | 5,277,280,824 | 45,473 | 27,726 |

Next to brute force, totals: 3 cards, 2000 deals: 55.8M against 1.04M nodes (54×).
4 cards, 2000 deals: 2.94B against 3.27M (899×). 5 cards, 500 deals: 60.2B against
2.92M (20,650×).

What this changes:

- One thread now does about 13M nodes/s on the M1 (23M on the M6), half of Phase 2's
  26M (46M), and all threads about 74M (120M). Weights are most of that cost, and they more than pay for it: a node is twice
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

### 2.6 The driver, and whole deals with no table

The driver used to start a strain from the previous strain's result, and it searched
for answers that the sure tricks already gave, since the cuts don't run on the first
card of a search. In a table it could step through targets one at a time, as in 2 3 4
5 6 7 8. Now the sure tricks bound it, and each strain starts from the middle of those
bounds. On the 200 8-card endings:

| Driver | Mean nodes | Searches per entry, mean | Most searches for one entry |
|---|---|---|---|
| Before (e5f0047) | 830,281 | 2.55 | 8 |
| Sure tricks as bounds, the same guess | 828,222 | 2.29 | 7 |
| + the middle of the bounds for a new strain | 825,796 | 2.18 | 6 |
| + bisecting when the gap is 3 or more | about 852,000 | | |
| A perfect first guess, as a limit | 794,530 | | |

So the stepping looked bad but cost little. Even a perfect guess saves only 4% of
nodes at 8 cards and 6% at 9, since the work is in the two searches next to the true
value, and bisecting costs 3% more, since it asks far from the answer. Guessing from
the trump fit gave about 0.5% fewer nodes but a worse worst case, so it isn't used. At
10 cards, nodes are level with before.

Whole deals of `list100` with no table, one single-threaded process per deal and 8 at
a time, with a limit of 40 minutes per deal: of the first 20 started, 16 finished and
4 hit the limit. All 16 matched DDS. They took 3.1 to 33.7 billion nodes, mean 16.6
billion, at about 15M nodes/s, so 3.5 to 39 minutes each, and those 4 took more than
about 36 billion. That is at least 10 times the 12-card mean, near the 8 times that
§2.4 expected, and far too slow to be useful: a table was needed, as planned.

### 2.7 What Phase 4 measured

Whole tables of `list100` on the M6, 12 threads, with other work running. Every row
matches DDS on all 100 deals, except the first, which didn't finish them.

| Search | Mean nodes per deal | Worst deal | Wall for 100 deals |
|---|---|---|---|
| No table (§2.6, 16 of 21 deals) | more than 16,600,000,000 | | |
| Table, hashed on lengths, one table for all 5 strains | 83,758,437 | 2,651,318,416 | 369 s |
| + small card filter, and hashing on levels of top cards | 11,461,796 | 234,233,597 | 46 s |
| + hashing on the suits that matter, with a directory, and a table per strain | 6,978,487 | 83,772,644 | 20 s |
| + 2^23 words per strain instead of 2^21 | 5,989,681 | 55,229,848 | 15 s |

What this changes:

- Partition search works in Bend with no `@unsafe`, and it works first time against
  thousands of endings and the DDS lists, so the plan's design of the entry held. Each
  answer carries its winning ranks up in its `Res`. A trick won by rank adds the card
  and the run below it in its hand, since the search only tries the top of a run. Each
  cut adds what it looks at: quick tricks the top run of the side's cards in each suit,
  later tricks the top card of each suit or the top two trumps, and the check after the
  lead the card that wins.
- The hash matters more than anything else in the table. An entry can only be hashed
  on what every position it matches shares, and that is less than DDS's bucket by
  lengths can bear with 8 entries a bucket: late in a deal a few lengths hold most of
  the positions. So an entry goes by its pattern, the suits whose top 3 cards all
  matter, and hashes on those cards' owners. A lookup tries each pattern that the
  directory word for its lengths has seen. On the first 20 deals, in mean nodes, top
  cards hashed per suit: 1, 7.5M; 2, 5.0M; 3, 4.4M; 4, 4.5M; 6, 5.3M.
- With this hash the table's size matters up to a point. On `list100`, words per
  strain against mean nodes and wall for 100 deals: 2^19, 12.8M, 41 s; 2^20, 8.6M, 26 s;
  2^21, 7.0M, 20 s; 2^22, 6.2M, 16 s; 2^23, 6.0M, 16 s; 2^24, 5.9M, 16 s; 2^25, 5.9M,
  16 s. So 2^23, which is 32 MB, and about 390 MB in all on 12 threads.
- Using the table only from 4 or 5 tricks left costs 18% and 77% in time, and using it
  from 2 costs 6%, so it stays at 3.
- 4 entries a bucket cost half as many nodes again as 8.
- The small card filter cuts nodes by a third (10.1M to 6.6M on the first 20).
- A best move kept in each entry, as DDS does, gave nothing here (6.60M to 6.69M), so
  it is out: the memory by depth and the weights already find most of it.
- The table does update in place: in the emitted C a store is a `blk_write` to the
  array's own block, and there is no array copy. A table 64 times bigger takes about
  the same time.
- A table can outlive its deal, since an entry is about a position, with relative
  ranks, not about the deal it came from. But sharing one across the items of a leaf
  gave no fewer nodes on `list1000`, at any width of the tree, and made node counts
  depend on the number of threads. So it is out.
- Leaving a winner's run out of the ranks when its side succeeded, since it only needed
  that card, passed the tests but saved only 1%, so it is out too.
- Nearly every position at the start of a trick now ends in the table or a cut, so the
  nodes are mostly the three cards in between. Speed per node is about 8M/s on one
  thread, against 23M with no table.

Termination needed one change to the search's shape. The table is read going into a
child, and that decides the child's moves, but the search can't destructure a call. So
a child enters with a phase argument of 1 and takes its moves out of its `Res`, then
goes on with phase 0. This fits the rule that arguments are compared left to right.

Still unproved: partition search itself has no law for every position. Laws cover the
parts: entries' top cards and ranks, runs, bounds and owner words. Tests stand in for
the rest: brute force on small endings, DDS on endings and on all of both lists.

### 2.8 What Phase 5 measured

`tools/check.py speed` on the M6, on all 12 threads, with other work running. `dd`'s
tables match both lists exactly, all 1,100.

| File | Deals | `dd`, deals/s | DDS one at a time, deals/s | DDS in batches, deals/s | Behind DDS in batches |
|---|---|---|---|---|---|
| `list100` | 100 | 6.6 | 28.2 | 81.1 | 12.2× |
| `list1000` | 1000 | 8.5 | 26.4 | 72.6 | 8.6× |

What this changes:

- Decision 2 asked for throughput over many deals. We are about 9 times behind DDS in
  batches, and further behind per thread: DDS's batches gain only about 3 times on one
  at a time here, so it isn't using the cores that `dd` is. Phase 6 is where this gets
  worked on.
- Phase 6b looks doubtful on this machine. The GPU was 29 times slower than the CPU
  threads on plain minimax (§2.3), every lane would need its own table, and the search
  now wants 32 MB per strain for its best results.
- One deal now uses up to 5 threads, a deal of 23M nodes going from 2.3 s to 1.2 s, as
  far as its largest strain allows. A fork nested inside a leaf of the fork tree did
  nothing: the scheduler only hands out tasks until it has enough of them, and a tree
  that is mostly empty leaves has enough at once. So `dd` forks over pairs of deal and
  strain, with no leaf that has no work, in one flat tree.
- The rest of the imbalance is the tail: on `list100` the worst 5 deals held 45% of
  all nodes before the last hash, and 12 threads give only 4.5 times one, since tasks
  never move and a heavy strain can land on an efficiency core. 6 threads were within
  15% of 12. Splitting a heavy strain by leader would need a table per leader.

### 2.9 What Phase 6 has measured so far

**The comparison with DDS.** The `nodes` that DDS reports is `trickNodes`, which only
counts positions at the start of a trick (`ab_search.cpp`, once per fourth card). Ours
counts every card, so the two can't be compared as they stand. Counting ours DDS's way,
on the first 20 deals of `list100`, one thread, 20 calls of `SolveBoard` for DDS:

| | Trick nodes per table | s per table | ns per trick node |
|---|---|---|---|
| DDS | 520,675 | 0.081 | 156 |
| `dd` at the start of Phase 6 | 1,435,137 | 0.52 | 361 |
| `dd` before the quick tricks port | 897,144 | 0.27 | 305 |
| `dd` now | 779,297 | 0.27 | 341 |

So on one thread the gap has gone from 6.4× to 3.3×: now 1.5× in search size and 2.2×
in cost per node. The gap in throughput is smaller than that, because DDS through
`endplay` gains only about 2.8× from its batches here while `dd` gains 6.1×.

**Where throughput is now**, from `tools/check.py speed`:

| File | `dd` at the start of Phase 6, deals/s | `dd` now, deals/s | DDS in batches, deals/s | Behind DDS |
|---|---|---|---|---|
| `list100` | 6.6 | 15.8 | 76.4 | 4.8× |
| `list1000` | 8.5 | 16.1 | 70.0 | 4.4× |

**Kept**, as measured on `list100` from a mean of 6.0M nodes and 15.9 s of wall:

| Change | Mean nodes | Wall |
|---|---|---|
| Moves as a list type of their own, a smaller frame across a child, probing only patterns in the directory, no weighing for a single move | 6.0M | 13.7 s |
| Quick tricks rest only on the top cards the target needs | 4.1M | 8.4 s |
| Later tricks rest only on what they looked at | 3.6M | 7.5 s |
| Trumps trim like other suits when the opponents have none | 3.5M | 7.4 s |
| At no trumps, later tricks rest only on the opponents' top cards | 3.5M | 7.2 s |
| Quick tricks from DDS (below) | 3.0M | 6.3 s |

The biggest lesson is that what a cut rests on matters as much as whether it cuts: an
entry that names fewer cards matches more positions. A count that only rises with the
top cards it counts need only keep as many of them as the target needs, as DDS does.

Reference counts are per type at run time, and that is the other lesson. A `List`
shared anywhere in the program (and `dd` shares several) makes every `Con` cell of any
list get a counted redirect when it is built. A list type of its own for moves removed
all of that from the search, for 14% of the time. So anything built at every node needs
a type of its own, and `term_keep` and `rfc_seal` in the emitted C show where this
goes wrong.

**Tried and not kept.** Each was measured on `list100` against what was current then:

- *A finer fork, with a table per leader:* nodes double (6.0M to 11.6M), and wall goes
  from 16 s to 29 s. It isn't needed either, as the next point shows.
- *More threads than cores, to let the OS balance them:* no gain at 16, 24 or 48. On
  300 deals of `list1000`, 6, 8, 10 and 12 threads give 4.3×, 5.0×, 5.8× and 6.1× one
  thread, the same 6.1× as plain minimax (§2.3). So a big batch is already at what the
  machine can do, and the 4.5× of §2.8 came from the heavy tail of `list100`.
- *DDS's exact weights on lead (`weight_alloc_trump0`, `weight_alloc_nt0`):* worse, 3.5M
  nodes to 4.0M, or 4.2M with the top card of each suit going first as well. So the
  weights from the notes stay, and the other positions weren't ported.
- *Looking in the table before the sure tricks,* as DDS does from 5 tricks left:
  worse, 6.0M nodes to 6.2M, or 6.5M for all positions.
- *Working out each suit's part of the hash once per lookup,* and *keeping all 8 first
  words of a bucket on one cache line:* no gain. A lookup is already about 50 ns.
- *Leaving a winner's run out of the ranks when its side succeeded:* 3% fewer nodes,
  but only 1% in time, with no proof, so it is out.
- *Taking out the best-move memory, the check after the lead, or the top card first,
  or changing the memory's weight:* all within 5% either way, about the noise. None
  makes a clear gain, so none has changed.
- *Other sizes:* 2^21, 2^22 and 2^24 words of table, 2 or 4 top cards in the hash, and
  the table from 2 or 4 tricks left. None beat what is there.
- *Lookup tables for ranks and runs (not built):* `U32.popcount`, `U32.ctz` and so
  `C.bits.count` compile to CPU instructions in the emitted C, while a read from an
  `Array` has to thread the array through a block read. So a table can't beat what
  these use now. The loops that are left, such as `own` and `tops`, are per card and
  short late in a deal, where most positions are.
- *The GPU, one more measurement:* 28× slower than the CPU threads on plain minimax,
  the same as before (§2.3), so Phase 6b isn't worth more time on this machine.

**Quick tricks from DDS.** Ported from `quick_tricks.cpp` one case at a time, each
checked against DDS and brute force, on `list100` from 3.49M mean nodes:

| Case | Mean nodes | Kept |
|---|---|---|
| Long suits once others are out, and second cards in either hand (`qs.alt`) | 3.21M | Yes |
| Ax opposite Kx as the way across to partner | 3.20M | No: no real change |
| The same counts in the trump suit, and trumps alone keep only what the target needs | 3.18M | Yes |
| Tricks on lengths when the opponents are void, and one trick by partner's ruff | 3.03M | Yes |
| After the lead, a lone trump wins whatever its rank | 3.00M | Yes |
| The finesse through the left hand opponent | 2.98M | No: its count needs a third card that trimming can drop, which gave wrong tables, for under 1% |

Trick nodes per table on the first 20 deals are now 779,297 against DDS's 520,675, so
1.5× where they were 1.7×. But time gained less than nodes: the count costs more at
every start of a trick, so one thread went from 0.27 s to 0.27 s per table, and
`list1000` from 15.7 to 16.1 deals/s, against 70.0 for DDS (4.4× behind).

These rules need care that the tests only just gave. As first ported, a long suit in
partner's hand counted once partner's trumps had drawn the opponents'. But partner may
have to use that suit to get in, and be ruffed or blocked: one 4-card ending in 5,000
came out wrong. DDS only counts trumps the leader draws, and so do we now. The brute
force check in `tools/test.sh` caught this, where 8,500 endings against DDS had not. It
is now a unit test, and 20,000 3-card, 20,000 4-card and 1,000 5-card endings agree
with brute force, plus 30,000 from two suits.

**What is left.** The profile is flat: the search itself 25%, the table's lookup 15%
and its key 10%, moves about 20%, sure tricks 5% or more. Search size is 1.5× DDS's, and
time per table is 3.3×. More cases in the count have stopped paying, so the gap left is
mostly cost per node, spread thinly through what Bend compiles, and no large piece of it
is known. Working out the count only where the cheaper one fails might win a few
percent.

### 2.10 Proving the sure tricks

The goal was a law for each sure trick rule that holds in every position: what the rule
counts never exceeds what the side really takes against best defence. None of them is
proved that way yet. What there is instead, and why:

**Every position up to 3 cards, by enumeration.** `src/every.bend` walks every ending
with k cards in each hand: every split of the cards into suits (longest first, since
suits only differ by name) and every way to give them out, using the top cards of each
suit, since only who holds what matters. For each, in all 5 strains with all 4
leaders, it checks that sure tricks never exceed the truth by brute force and that the
search gives the same table. `build/exhaust k` runs it compiled:

| Cards per hand | Positions | Wrong | Time on the M6 |
|---|---|---|---|
| 1 | 120 | 0 | under 1 s |
| 2 | 37,800 | 0 | 1 s |
| 3 | 12,566,400 | 0 | 53 min, under heavy load |

`tools/test.sh` runs 1 and 2 cards every time, and 3 is to be run after any change to a
rule. This is a check of every position of those sizes, but it isn't a proof in the
kernel, and it can't reach 4 cards: that is about 10^10 positions, each of over a
million brute force nodes. Above 3 cards the evidence is still samples. After the port
of §2.9, 200,000 more 4-card endings (half of them from two suits) and 2,000 5-card
endings agree with brute force, along with the DDS lists.

**In the checker, enumeration is far too slow.** The same check of every 1-card ending
as a law took 573 s of CPU for 120 positions, about 5 s each, so 2 cards would take
days. Laws by enumeration stop at the samples that are there now.

**A proof for every position is a large piece of work, not a step.** The checker sees a
`U32` as 32 bits (`Word(32n)`), so facts about words can be proved by induction, and
this works: that `Word.cmp` of a word with itself is `EQ` takes a dozen lines and checks
in under a second. But a rule's law needs the whole minimax to go through, and before
any rule comes a foundation that isn't there yet:

1. Order and arithmetic on words: `cmp` being an order, `max` and `min`, adding one
   without overflow. Base only has `add` commuting.
2. Bounds on the brute force value, that it lies between the tricks won and those
   plus the tricks left. That needs every hand to keep the same number of cards, since
   a node with no moves takes the seed (0 or 13). So it needs the count of a hand to be
   right, and `popcount` works by bit tricks.
3. That `R.play` and `R.moves` do what the rules say for every position, past the
   follow-suit laws that exist.
4. Then a game argument for each rule: a line of play for the side that takes that
   many tricks whatever the defence does, carried through four cards a trick and
   through the bits of every hand.

Each rule is a separate argument on top of that. Quick tricks alone have long suits,
two hands, entries and ruffs, with trimming of what they rest on. My estimate is
thousands of lines of proof with no tactics, so it wasn't attempted here past the
first lemma. The bug of §2.9 shows why it would be worth it: a rule that holds on
every 3-card position and on most 4-card ones was still wrong.

**Rule by rule**, what holds now:

| Rule | Every position up to | Samples beyond | For every position |
|---|---|---|---|
| Target cuts | 3 cards; law for every won, left and target, given that the value lies in range | lists | No: needs foundation 2 |
| Quick tricks: top runs, safe from ruffs | 3 cards | 4 and 5 cards, lists | No |
| Quick tricks: long suits and second cards (`qs.alt`) | 3 cards | 4 and 5 cards, lists | No |
| Quick tricks: the trump suit | 3 cards | 4 and 5 cards, lists | No |
| Quick tricks: voids and partner's ruff | 3 cards | 4 and 5 cards, lists | No |
| Later tricks | 3 cards | 4 and 5 cards, lists | No |
| The check after the lead | 3 cards | 4 and 5 cards, lists | No |
| What each rule rests on, for the table | 3 cards for the search, though the table is never used under 4 cards | 4 and 5 cards, lists | No |

That last row matters: at 3 cards the table isn't used (it starts at 3 tricks left, and
the first trick is the root), so the exhaustive check says nothing about winning ranks.

**The foundation, begun.** These are in `LAWS.bend` now, all proved:

- `facts_holding`: for any holding (a `U32` with no bits past the 13th), `popcount`
  counts it, and its lowest card `b = m & -m` is in it. If it isn't empty, `b` is one
  card below the 13th, `1 << ctz(b)` is `b`, and taking it leaves a holding with one
  card fewer. Checked once for each of the 8192 holdings in one pass (`facts_all`),
  lifted to any number below 8192 (`facts_nat`), and then to any holding through
  the next two.
- `holding_lt` (with `bound`, `mask_ones` and the `Nat` lemmas `lt_dbl`, `lt_dbl1`,
  `lt_one` and `pow2_pos`): a word with no bits past the 13th stands for a number below
  8192. These are proofs by induction on words, for any width.
- `from_to`, `u32_roundtrip` and the lemmas under them: a word is the word for its
  number, so a fact about holding number k is a fact about the holding.
- `card_code`: a card's code gives back its suit and rank, for every suit below 4 and
  rank below 13.
- Words as sets of bits, all by induction for any word (31 laws, under "Words as sets
  of bits"): `Sub(a, b)`, every bit of a is in b, and how it goes with `and`, `xor` and
  shifts (`and_sub_left`, `sub_trans`, `and_mono`, `shr_mono`, `shrn_mono`, `shl_sub`,
  `shln_sub`); taking a bit that is in w leaves one fewer (`count_xor`); taking bits of
  a valid hand word keeps it valid (`xor_sub`), and a valid word's two holdings are
  holdings (`hi_holding`, `lo_holding`); a word with nothing in either half is zero
  (`split_zero`); and words that compare equal are equal (`cmp_eq`, `u32_eq`).

The one pass over 8192 holdings is what the gate pays for: `bend PROOF.bend` takes
about 15 minutes now, against 6.5 before the foundation.

**What the rest takes.** Proofs by induction on words go well: each of these took one
to four tries, at 10 to 20 lines. The plan for steps 2 and 3 needs roughly these, each
of that size or a few times it:

1. *Done:* that a holding is below 8192 when its bits above 13 are clear.
2. *Done:* facts about each holding in one pass of 8192, and card codes.
3. *Done:* shifts and masks, by subsets rather than by recomputing the holdings: a
   card in a holding is in the hand's word, and validity is kept.
4. *Done:* taking a card that is in a hand leaves one card fewer, by `S.bits`.
5. *Done:* every card that `R.moves` gives is in the hand to play, and there is one when
   the hand has a card (an induction over `R.moves.peel`). Under "Moves" in `LAWS.bend`:
   `moves_hand` says every card of `R.moves.of(lead, h01, h23)` from valid words is in
   the hand, as the two masks `R.play` takes out of its words (`S.InHand`), and
   `moves_ne01` and `moves_ne23` say the list isn't empty when either word has a card.
   Beneath them, `peel_sound` and `peel_hand` follow the peel card by card, and
   `card_bit` and `one_bit` check the 52 card codes and 13 rank bits.
6. The trick word: seat, cards played, lead and winner after `R.trick.next`, for every
   value of each field. They are packed with shifts and masks, so this is like 3.
7. Hands stay even: with the seat to play and the cards played, each hand has the
   right number of cards (step 2 of the plan).
8. Small comparisons and adding one to the tricks won, for values up to 13.
9. The bounds on the value (step 3), by induction over `B.search`.

That is about 60 to 120 lemmas, or 1,500 to 3,000 lines, before the first sure-trick
rule. Every check of the whole `PROOF.bend` takes 13 minutes or more, and the facts
about holdings will make it longer. It can be done; it is days of steady work, not a
night's.

**The kernel check.** `bend PROOF.bend --verdict` rechecks proofs with a kernel proved
in Lean. It has never run here: Bend 2.0.40 needs Lean 4.34.0 exactly, and only 4.35.0
is installed.

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

**The transposition table** is one `Array<U32>`, 2^23 words (32 MB) per strain of a
whole deal. `src/search.bend` has the entry as built, and §2.7 says what changed. As
first planned, an entry is about 8 words:

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

The **driver** for one strain and leader takes its bounds from the sure tricks. It
starts from a guess (the answer for the previous leader, or the middle of the bounds
for a strain's first entry) and narrows the bounds with zero-window searches,
threading the same TT through every call. The four leaders of one
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

Each parallel leaf owns its own TT, but a leaf only makes one while it is solving, so
what is live at once is the TT size times the number of threads, whatever the width of
the tree. The tree can be as wide as balance wants.

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
*Done:* see §2.5 and §2.6.

**Phase 4: Transposition table.**
First an exact-position TT (relative ranks, bounds, bucketed array). Then
partition search: winning-rank backup, masked matching, and the small-card
filter.
*Done when:* full 13-card deals solve and the table matches DDS's `list100`
exactly.
*Done:* see §2.7.

**Phase 5: Full table and batching.**
The 20-entry table, parallel over strains, and a batch mode over many deals.
*Done when:* 100% agreement with DDS on `list1000` (later `list10000`), and we
have a throughput figure next to DDS on the same Mac.
*Done:* see §2.8, except for `list10000`, which isn't vendored yet.

**Phase 6: Performance.** *Under way:* see §2.9.
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
