#!/bin/sh
# tools/sim.sh: simulate the play from what one player can see.
#
#   tools/sim.sh deal="N:- - - T952.T2.JT754.97" contract=4H by=S S.hcp=15-19 S.H=5+
#
# Builds sim first if it is missing or older than its sources, then runs it with
# these arguments. See sim.bend for all of them.

set -e
cd "$(dirname "$0")/.."
PATH="$HOME/.bend/bin:$PATH"

if [ ! -x sim ] || [ -n "$(find sim.bend src -name '*.bend' -newer sim)" ]; then
  echo "Building sim..." >&2
  bend sim.bend -o sim
fi

exec ./sim "$@"
