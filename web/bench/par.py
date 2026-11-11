#!/usr/bin/env python3
"""Par scores from DDS (through endplay) for a file of PBN deals, for the page's par
check: one line per deal, the 16 scores for NS for dealer N E S W (outer) and
vulnerability None NS EW All (inner).

  par.py deals.pbn > par.txt
"""
import sys
from endplay.types import Deal, Vul, Player
from endplay.dds import calc_dd_table, par

vuls = [Vul.none, Vul.ns, Vul.ew, Vul.both]
dealers = [Player.north, Player.east, Player.south, Player.west]
for line in open(sys.argv[1]):
    if not line.strip():
        continue
    t = calc_dd_table(Deal(line.strip()))
    print(" ".join(str(par(t, v, d).score) for d in dealers for v in vuls))
