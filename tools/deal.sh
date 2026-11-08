#!/bin/sh
# tools/deal.sh: deal a random hand and print its double dummy table.
#
#   tools/deal.sh           a random deal
#   tools/deal.sh 42        deal number 42
#
# Builds dd first if it is missing or older than its sources.

set -e
cd "$(dirname "$0")/.."
PATH="$HOME/.bend/bin:$PATH"

if [ ! -x dd ] || [ -n "$(find dd.bend src -name '*.bend' -newer dd)" ]; then
  echo "Building dd..." >&2
  bend dd.bend -o dd
fi

exec ./dd --random "$@"
