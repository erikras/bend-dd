#!/usr/bin/env python3
"""Compare dd's results against DDS.

  check.py endings [--count N] [--cards 3 4 5] [--seed S] [--threads T]
      Deals random endings, solves them with `dd --brute` and with DDS (through
      the endplay package) in every strain with every leader, and compares.
      Also reports dd's node rate.

  check.py lists [--file tests/data/list100.txt ...] [--limit N]
      Checks the vendored DDS lists: dd must read every deal and print it back
      unchanged, and endplay's DDS must reproduce every TABLE line, which pins
      down the order of the table that dd has to match.

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


def random_ending(rng, cards):
    """A random deal with this many cards in each hand, as PBN."""
    deck = rng.sample(range(52), 4 * cards)
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
        deals = [random_ending(rng, cards) for _ in range(args.count)]
        t0 = time.time()
        lines, err = with_deals(deals, lambda p: run_dd(["--brute", p], args.threads))
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
        lines, _ = with_deals([p for p, _ in deals], lambda p: run_dd([p]))
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
    lines, _ = with_deals(deals, lambda p: run_dd([p]))
    if lines != deals:
        fail("dd changed a deal from hand")
    print("OK: %d deals from hand round-trip through dd" % len(deals))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)

    p = sub.add_parser("endings")
    p.add_argument("--count", type=int, default=1000)
    p.add_argument("--cards", type=int, nargs="+", default=[3, 4, 5])
    p.add_argument("--seed", type=int, default=1)
    p.add_argument("--threads", type=int)
    p.set_defaults(fn=check_endings)

    p = sub.add_parser("lists")
    p.add_argument(
        "--file",
        nargs="+",
        default=[os.path.join(ROOT, "tests/data", f) for f in ("list100.txt", "list1000.txt")],
    )
    p.add_argument("--limit", type=int)
    p.set_defaults(fn=check_lists)

    p = sub.add_parser("roundtrip")
    p.add_argument("--count", type=int, default=1000)
    p.set_defaults(fn=check_roundtrip)

    args = parser.parse_args()
    args.fn(args)


if __name__ == "__main__":
    main()
