#!/usr/bin/env python3
"""tools/simcheck.py: checks the simulator's layouts against DDS.

    tools/simcheck.py [--count K] [--sim ./sim] sim-arguments...

Runs the simulator with layouts=K added to its arguments, so that it prints the
first K layouts that fit and, for each one, the tricks North-South take in the whole
deal with each card it tries. Then it replays the play in each layout with endplay,
asks DDS's SolveBoard for the value of every card of the player to move, and checks
that the two agree. It also checks that each layout keeps the hands in view and the
cards each hidden seat played, and that it fits the rules given.

Needs endplay, as tools/test.sh sets up in .venv.
"""

import argparse
import subprocess
import sys

from endplay.dds import solve_board
from endplay.types import Card, Deal, Denom, Player

SEATS = "NESW"
SUITS = "SHDC"
RANKS = "23456789TJQKA"


def card_parse(word):
    """A card as sim reads it: suit first or rank first, 10 or T."""
    w = word.upper().replace("10", "T")
    if w[0] in SUITS:
        return SUITS.index(w[0]), RANKS.index(w[1:])
    return SUITS.index(w[-1]), RANKS.index(w[:-1])


def hand_sets(pbn):
    """The four hands of a PBN deal, by seat, as sets of (suit, rank)."""
    first = SEATS.index(pbn[0])
    hands = {}
    for i, h in enumerate(pbn[2:].split()):
        seat = (first + i) % 4
        cards = set()
        if h != "-":
            for s, holding in enumerate(h.split(".")):
                cards |= {(s, RANKS.index(r)) for r in holding}
        hands[seat] = (h == "-", cards)
    return hands


def winner(trick, leader, trump):
    best = 0
    for i in range(1, 4):
        s, r = trick[i]
        bs, br = trick[best]
        if (s == bs and r > br) or (s == trump and bs != trump):
            best = i
    return (leader + best) % 4


def points(cards):
    return sum({12: 4, 11: 3, 10: 2, 9: 1}.get(r, 0) for _, r in cards)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=20)
    ap.add_argument("--sim", default="./sim")
    opts, rest = ap.parse_known_args()
    args = dict(a.split("=", 1) for a in rest)
    out = subprocess.run([opts.sim, *rest, f"layouts={opts.count}", "+RTS", "--threads", "1", "-RTS"],
                         capture_output=True, text=True)
    if out.returncode != 0:
        sys.exit(f"sim failed: {out.stderr.strip()}")
    lines = out.stdout.splitlines()
    tries = [int(x) for x in lines[0].split()[2:]]
    contract = args["contract"].upper()
    trump = "SHDCN".index(contract[1])
    decl = SEATS.index(args["by"].upper())
    leader = (decl + 1) % 4
    plays = [card_parse(w) for w in args.get("play", "").replace(",", " ").split()]
    view = hand_sets(args["deal"])
    rules = []
    for k, v in args.items():
        if "." in k:
            seat, what = k.split(".")
            lo, hi = (v.rstrip("+"), "99") if v.endswith("+") else (v.split("-") + [v])[:2] if "-" in v else (v, v)
            rules.append((SEATS.index(seat.upper()), what.upper(), int(lo or 0), int(hi or 99)))

    bad = 0
    for n, line in enumerate(lines[1:]):
        pbn, values = line.split(" | ")
        values = [int(x) for x in values.split()]
        layout = hand_sets(pbn)
        problems = []
        for seat, (hidden, cards) in view.items():
            if not hidden and layout[seat][1] != cards:
                problems.append(f"{SEATS[seat]} is not the hand in view")
        for seat, what, lo, hi in rules:
            cards = layout[seat][1]
            v = points(cards) if what == "HCP" else sum(1 for s, _ in cards if s == SUITS.index(what))
            if not lo <= v <= hi:
                problems.append(f"{SEATS[seat]}.{what} is {v}")

        deal = Deal(pbn)
        deal.trump = [Denom.spades, Denom.hearts, Denom.diamonds, Denom.clubs, Denom.nt][trump]
        deal.first = [Player.north, Player.east, Player.south, Player.west][leader]
        seat, trick, ns = leader, [], 0
        for s, r in plays:
            if (s, r) not in layout[seat][1]:
                problems.append(f"{SEATS[seat]} played {SUITS[s]}{RANKS[r]} but doesn't hold it")
            deal.play(Card(f"{SUITS[s]}{RANKS[r]}"))
            trick.append((s, r))
            if len(trick) == 4:
                seat = winner(trick, (seat + 1) % 4, trump)
                ns += seat % 2 == 0
                trick = []
            else:
                seat = (seat + 1) % 4
        left = 13 - len(plays) // 4
        dds = {}
        for c, t in solve_board(deal):
            dds[(int(c.suit), RANKS.index(str(c)[1:].replace("10", "T")))] = t
        for code, v in zip(tries, values):
            key = (code >> 4, code & 15)
            if key not in dds:
                problems.append(f"DDS has no value for {SUITS[key[0]]}{RANKS[key[1]]}")
                continue
            t = dds[key]
            want = ns + (t if seat % 2 == 0 else left - t)
            if want != v:
                problems.append(f"{SUITS[key[0]]}{RANKS[key[1]]}: sim {v}, DDS {want}")
        if problems:
            bad += 1
            print(f"layout {n + 1}: {pbn}: " + "; ".join(problems))
    print(f"{len(lines) - 1} layouts, {len(tries)} cards each: {bad} disagree")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
