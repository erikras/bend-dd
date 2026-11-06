#!/usr/bin/env python3
"""Compare dd's results against DDS.

  check.py endings [--count N] [--cards 3 4 5] [--seed S] [--threads T] [--suits N] [--brute]
      Deals random endings, solves them with `dd` (or `dd --brute`) and with DDS
      (through the endplay package) in every strain with every leader, and
      compares. Also reports dd's node rate.

  check.py oracle [--count N] [--cards 3 4 5] [--seed S] [--threads T] [--suits N]
      Deals random endings and solves them with `dd` and `dd --brute`, which must
      agree. Reports the node counts of both and their times. Needs no DDS.

  check.py nodes [--count N] [--cards 7 8] [--seed S] [--threads T] [--suits N]
      Reports dd's node counts and times without checking them, with the median
      and worst deal, for sizes too slow to check against DDS or brute force.

  check.py human [--count N] [--cards 4 6 8] [--seed S]
      Checks dd -v and dd --grid against plain dd on random endings: the same grid
      and the same nodes, with per-entry rows adding up to the totals.

  check.py sure [--file tests/data/list100.txt ...] [--limit N] [--count N] [--cards 4 6 8]
      The tricks the search counts as sure must not exceed the true ones, on whole
      deals from the DDS lists and on random endings against DDS.

  check.py lists [--file tests/data/list100.txt ...] [--limit N]
      Checks the vendored DDS lists: dd must read every deal and print it back
      unchanged, and endplay's DDS must reproduce every TABLE line, which pins
      down the order of the table that dd has to match.

  check.py full [--file tests/data/list100.txt] [--limit N] [--threads T]
      Solves whole deals from a DDS list with dd and compares them with their TABLE
      lines. Reports node counts and times.

  check.py roundtrip [--count N]
      Parses and prints the first N deals from ./hand with dd, which must print
      them back unchanged.

Run it from the root of the repo, after building ./dd and ./hand.
"""

import argparse
import os
import random
import re
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RANKS = "AKQJT98765432"
SEATS = "NESW"
STRAINS = ["S", "H", "D", "C", "NT"]


def fail(msg):
    print("FAIL: " + msg)
    sys.exit(1)


def run_dd(args, threads=None):
    """Runs ./dd, answering its stdout lines and its stderr text."""
    cmd = [os.path.join(ROOT, "dd")] + args
    if threads:
        cmd += ["+RTS", "--threads", str(threads), "-RTS"]
    p = subprocess.run(cmd, capture_output=True, text=True)
    if p.returncode != 0:
        fail("%s exited with %d: %s" % (" ".join(cmd[:3]), p.returncode, p.stderr.strip()))
    return p.stdout.splitlines(), p.stderr


def with_deals(deals, fn):
    """Writes deals to a temporary file and calls fn with its path."""
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as f:
        f.write("\n".join(deals) + "\n")
        path = f.name
    try:
        return fn(path)
    finally:
        os.unlink(path)


# ---------------------------------------------------------------------------
# Endings


def random_ending(rng, cards, suits=4):
    """A random deal with this many cards in each hand, as PBN. With fewer suits,
    the cards come from that many of them, which makes long runs and voids common."""
    pool = [c for s in rng.sample(range(4), suits) for c in range(s * 13, (s + 1) * 13)]
    deck = rng.sample(pool, 4 * cards)
    hands = []
    for seat in range(4):
        mine = sorted(deck[seat * cards : (seat + 1) * cards])
        suits = ["".join(RANKS[c % 13] for c in mine if c // 13 == s) for s in range(4)]
        hands.append(".".join(suits))
    return "N:" + " ".join(hands)


def dds_table(pbn, cards):
    """The 20 table entries from DDS: the tricks declarer's side takes, by
    strain then declarer, with the seat on declarer's left on lead."""
    from endplay.dds import solve_board
    from endplay.types import Deal, Denom, Player

    out = []
    for strain in [Denom.spades, Denom.hearts, Denom.diamonds, Denom.clubs, Denom.nt]:
        for declarer in range(4):
            leader = (declarer + 1) % 4
            deal = Deal(pbn)
            deal.first = Player(leader)
            deal.trump = strain
            best = max(tricks for _, tricks in solve_board(deal))
            out.append(cards - best)
    return out


def check_endings(args):
    rng = random.Random(args.seed)
    total = rate_nodes = rate_ms = 0
    for cards in args.cards:
        deals = [random_ending(rng, cards, args.suits) for _ in range(args.count)]
        t0 = time.time()
        flags = ["--brute"] if args.brute else []
        lines, err = with_deals(deals, lambda p: run_dd(flags + [p], args.threads))
        wall = time.time() - t0
        if len(lines) != len(deals):
            fail("dd answered %d lines for %d deals" % (len(lines), len(deals)))
        nodes = 0
        for pbn, line in zip(deals, lines):
            fields = [int(x) for x in line.split()]
            got, n = fields[:20], fields[20]
            nodes += n
            want = dds_table(pbn, cards)
            if got != want:
                for i in range(20):
                    if got[i] != want[i]:
                        fail(
                            "%s strain %s declarer %s: dd %d, DDS %d"
                            % (pbn, STRAINS[i // 4], SEATS[i % 4], got[i], want[i])
                        )
        m = re.search(r"(\d+) ms on (\d+) threads", err)
        ms = int(m.group(1)) if m else 0
        threads = m.group(2) if m else "?"
        rate = nodes * 1000 // ms if ms else 0
        print(
            "%d-card endings: %d deals x 20 searches match DDS; %d nodes in %d ms on %s threads (%d nodes/s, %.1fs wall)"
            % (cards, len(deals), nodes, ms, threads, rate, wall)
        )
        total += len(deals)
        rate_nodes += nodes
        rate_ms += ms
    print("OK: %d endings, %d searches" % (total, total * 20))


def solve_all(flags, deals, threads):
    """Solves deals with dd, answering their tables, nodes, and the ms dd reports."""
    lines, err = with_deals(deals, lambda p: run_dd(flags + [p], threads))
    if len(lines) != len(deals):
        fail("dd answered %d lines for %d deals" % (len(lines), len(deals)))
    fields = [[int(x) for x in line.split()] for line in lines]
    m = re.search(r"(\d+) ms on (\d+) threads", err)
    return [f[:20] for f in fields], [f[20] for f in fields], int(m.group(1)) if m else 0


def check_oracle(args):
    rng = random.Random(args.seed)
    print("cards  deals   searches    nodes (brute)    nodes (search)  ratio   ms (brute)  ms (search)")
    total = 0
    for cards in args.cards:
        deals = [random_ending(rng, cards, args.suits) for _ in range(args.count)]
        want, brute_nodes, brute_ms = solve_all(["--brute"], deals, args.threads)
        got, nodes, ms = solve_all([], deals, args.threads)
        for pbn, g, w in zip(deals, got, want):
            for i in range(20):
                if g[i] != w[i]:
                    fail(
                        "%s strain %s declarer %s: search %d, brute %d"
                        % (pbn, STRAINS[i // 4], SEATS[i % 4], g[i], w[i])
                    )
        print(
            "%5d %6d %10d %16d %17d %6.0f %12d %12d"
            % (cards, len(deals), len(deals) * 20, sum(brute_nodes), sum(nodes), sum(brute_nodes) / max(sum(nodes), 1), brute_ms, ms)
        )
        total += len(deals)
    print("OK: %d endings, %d searches agree with brute force" % (total, total * 20))


def check_nodes(args):
    rng = random.Random(args.seed)
    print("cards  deals  nodes/deal (mean)  (median)     (max)    ms/deal   ms total  nodes/s")
    for cards in args.cards:
        deals = [random_ending(rng, cards, args.suits) for _ in range(args.count)]
        _, nodes, ms = solve_all([], deals, args.threads)
        nodes.sort()
        print(
            "%5d %6d %18d %9d %9d %10.2f %10d %8d"
            % (
                cards,
                len(deals),
                sum(nodes) // len(nodes),
                nodes[len(nodes) // 2],
                nodes[-1],
                ms / len(deals),
                ms,
                sum(nodes) * 1000 // max(ms, 1),
            )
        )


# ---------------------------------------------------------------------------
# The DDS lists


def read_list(path):
    """The (pbn, table) pairs of a DDS hands file."""
    deals = []
    pbn = None
    with open(path) as f:
        for line in f:
            if line.startswith("PBN "):
                pbn = re.search(r'"([^"]+)"', line).group(1)
            elif line.startswith("TABLE "):
                deals.append((pbn, [int(x) for x in line.split()[1:]]))
    return deals


def check_lists(args):
    from endplay.dds import calc_dd_table
    from endplay.types import Deal, Denom, Player

    for path in args.file:
        deals = read_list(path)
        if args.limit:
            deals = deals[: args.limit]
        if any(len(t) != 20 for _, t in deals):
            fail("%s: a TABLE line without 20 entries" % path)
        lines, _ = with_deals([p for p, _ in deals], lambda p: run_dd(["--print", p]))
        for (pbn, _), line in zip(deals, lines):
            if pbn != line:
                fail("%s: dd printed %s for %s" % (path, line, pbn))
        for pbn, want in deals:
            table = calc_dd_table(Deal(pbn))
            got = [
                table[strain, Player(seat)]
                for strain in [Denom.spades, Denom.hearts, Denom.diamonds, Denom.clubs, Denom.nt]
                for seat in range(4)
            ]
            if got != want:
                fail("%s: %s: DDS %s, TABLE %s" % (path, pbn, got, want))
        print("%s: %d deals read by dd and matched by DDS" % (os.path.relpath(path, ROOT), len(deals)))
    print("OK: lists")


# ---------------------------------------------------------------------------
# Round trip


def check_roundtrip(args):
    hand = os.path.join(ROOT, "hand")
    deals = []
    for i in range(1, args.count + 1):
        out = subprocess.run([hand, str(i)], capture_output=True, text=True, check=True).stdout
        deals.append(out.strip().splitlines()[-1])
    lines, _ = with_deals(deals, lambda p: run_dd(["--print", p]))
    if lines != deals:
        fail("dd changed a deal from hand")
    print("OK: %d deals from hand round-trip through dd" % len(deals))


def check_full(args):
    deals = read_list(args.file)
    if args.limit:
        deals = deals[: args.limit]
    got, nodes, ms = solve_all([], [p for p, _ in deals], args.threads)
    for (pbn, want), g in zip(deals, got):
        if g != want:
            fail("%s: dd %s, TABLE %s" % (pbn, g, want))
    nodes.sort()
    print(
        "OK: %d whole deals match DDS; mean %d nodes, median %d, worst %d; %d ms (%.0f ms per deal)"
        % (len(deals), sum(nodes) // len(nodes), nodes[len(nodes) // 2], nodes[-1], ms, ms / len(deals))
    )


def grid_of(lines):
    """The 20 entries of a printed grid, by strain and then declarer."""
    start = next(i for i, l in enumerate(lines) if l.split() == ["N", "E", "S", "W"])
    return [int(x) for l in lines[start + 1 : start + 6] for x in l.split()[-4:]]


def check_human(args):
    rng = random.Random(args.seed)
    for cards in args.cards:
        deals = [random_ending(rng, cards) for _ in range(args.count)]
        tables, nodes, _ = solve_all([], deals, None)
        for pbn, table, n in zip(deals, tables, nodes):
            lines, _ = run_dd(["--grid", pbn])
            if grid_of(lines) != table:
                fail("%s: dd --grid disagrees with dd" % pbn)
            lines, _ = run_dd(["-v", pbn])
            if pbn not in lines or grid_of(lines) != table:
                fail("%s: dd -v disagrees with dd" % pbn)
            head = next(i for i, l in enumerate(lines) if l.split()[:1] == ["decl"])
            rows = [l.split() for l in lines[head + 1 : head + 21]]
            total = lines[head + 21].split()
            # nodes, then from the right: searches come after the targets.
            if sum(int(r[4]) for r in rows) != n or int(total[1]) != n:
                fail("%s: dd -v has %s nodes in its totals, dd %d" % (pbn, total[1], n))
            for r, t in zip(rows, table):
                if int(r[3]) != t:
                    fail("%s: dd -v row %s against table entry %d" % (pbn, r, t))
                searches = int(r[5])
                targets = r[6 : 6 + searches]
                cuts = r[6 + searches : 6 + searches + 4]
                moves, kept = int(r[-2]), int(r[-1])
                if kept > moves or len(cuts) != 4 or searches < 1:
                    fail("%s: dd -v row %s" % (pbn, r))
            if str(n) + " nodes" not in lines[-1]:
                fail("%s: dd -v ends with %s, dd has %d nodes" % (pbn, lines[-1], n))
        print("%d-card endings: %d deals: dd -v and dd --grid agree with dd" % (cards, len(deals)))
    print("OK: output for people")


def sure_table(deals):
    lines, _ = with_deals(deals, lambda p: run_dd(["--sure", p]))
    if len(lines) != len(deals):
        fail("dd answered %d lines for %d deals" % (len(lines), len(deals)))
    return [[int(x) for x in line.split()] for line in lines]


def sure_check(deals, tables, cards):
    """Compares dd's sure tricks with tables of the tricks declarer's side takes."""
    quick = later = 0
    for pbn, table, sure in zip(deals, tables, sure_table(deals)):
        for i in range(20):
            q, l = sure[2 * i], sure[2 * i + 1]
            if q > cards - table[i] or l > table[i]:
                fail(
                    "%s strain %s declarer %s: sure %d for the leader's side and %d for declarer's, true %d and %d"
                    % (pbn, STRAINS[i // 4], SEATS[i % 4], q, l, cards - table[i], table[i])
                )
            quick += q
            later += l
    return quick, later


def check_sure(args):
    for path in args.file:
        deals = read_list(path)
        if args.limit:
            deals = deals[: args.limit]
        pbns = [p for p, _ in deals]
        q, l = sure_check(pbns, [t for _, t in deals], 13)
        print(
            "%s: %d deals x 20: sure tricks never exceed DDS (mean %.2f quick, %.2f later)"
            % (os.path.relpath(path, ROOT), len(deals), q / (20.0 * len(deals)), l / (20.0 * len(deals)))
        )
    rng = random.Random(args.seed)
    for cards in args.cards:
        pbns = [random_ending(rng, cards, args.suits) for _ in range(args.count)]
        q, l = sure_check(pbns, [dds_table(p, cards) for p in pbns], cards)
        print(
            "%d-card endings: %d deals x 20: sure tricks never exceed DDS (mean %.2f quick, %.2f later)"
            % (cards, len(pbns), q / (20.0 * len(pbns)), l / (20.0 * len(pbns)))
        )
    print("OK: sure tricks")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)

    p = sub.add_parser("endings")
    p.add_argument("--count", type=int, default=1000)
    p.add_argument("--cards", type=int, nargs="+", default=[3, 4, 5])
    p.add_argument("--seed", type=int, default=1)
    p.add_argument("--threads", type=int)
    p.add_argument("--suits", type=int, default=4, choices=[1, 2, 3, 4])
    p.add_argument("--brute", action="store_true")
    p.set_defaults(fn=check_endings)

    p = sub.add_parser("oracle")
    p.add_argument("--count", type=int, default=1000)
    p.add_argument("--cards", type=int, nargs="+", default=[3, 4, 5])
    p.add_argument("--seed", type=int, default=1)
    p.add_argument("--threads", type=int)
    p.add_argument("--suits", type=int, default=4, choices=[1, 2, 3, 4])
    p.set_defaults(fn=check_oracle)

    p = sub.add_parser("nodes")
    p.add_argument("--count", type=int, default=100)
    p.add_argument("--cards", type=int, nargs="+", default=[7, 8])
    p.add_argument("--seed", type=int, default=1)
    p.add_argument("--threads", type=int)
    p.add_argument("--suits", type=int, default=4, choices=[1, 2, 3, 4])
    p.set_defaults(fn=check_nodes)

    p = sub.add_parser("lists")
    p.add_argument(
        "--file",
        nargs="+",
        default=[os.path.join(ROOT, "tests/data", f) for f in ("list100.txt", "list1000.txt")],
    )
    p.add_argument("--limit", type=int)
    p.set_defaults(fn=check_lists)

    p = sub.add_parser("sure")
    p.add_argument(
        "--file",
        nargs="*",
        default=[os.path.join(ROOT, "tests/data", f) for f in ("list100.txt", "list1000.txt")],
    )
    p.add_argument("--limit", type=int)
    p.add_argument("--count", type=int, default=500)
    p.add_argument("--cards", type=int, nargs="+", default=[2, 3, 4, 6, 8])
    p.add_argument("--seed", type=int, default=1)
    p.add_argument("--suits", type=int, default=4, choices=[1, 2, 3, 4])
    p.set_defaults(fn=check_sure)

    p = sub.add_parser("human")
    p.add_argument("--count", type=int, default=30)
    p.add_argument("--cards", type=int, nargs="+", default=[3, 5, 7])
    p.add_argument("--seed", type=int, default=1)
    p.set_defaults(fn=check_human)

    p = sub.add_parser("full")
    p.add_argument("--file", default=os.path.join(ROOT, "tests/data/list100.txt"))
    p.add_argument("--limit", type=int, default=10)
    p.add_argument("--threads", type=int)
    p.set_defaults(fn=check_full)

    p = sub.add_parser("roundtrip")
    p.add_argument("--count", type=int, default=1000)
    p.set_defaults(fn=check_roundtrip)

    args = parser.parse_args()
    args.fn(args)


if __name__ == "__main__":
    main()
