#!/bin/sh
# tools/test.sh: build everything, check the proofs and run every test.
#
#   tools/test.sh           everything
#   tools/test.sh --quick   skip the proof check and shrink the DDS comparison
#
# Not run here, since it takes the best part of an hour: build/exhaust 3, every
# position of 3 cards. Run it after changing a sure trick rule.
#
# Needs bend, clang 14+ and python3. The first run makes a .venv with endplay.

set -e
cd "$(dirname "$0")/.."
PATH="$HOME/.bend/bin:$PATH"

# The Bend version the repo was last tested with. A different one only warns,
# since a new release is worth trying, but it may explain a failure.
BEND_VERSION=2.0.40

quick=0
[ "$1" = "--quick" ] && quick=1

have=$(bend version | sed -n 's/[^0-9]*\([0-9][0-9.]*\).*/\1/p' | head -n 1)
if [ "$have" != "$BEND_VERSION" ]; then
  echo "warning: tested with bend $BEND_VERSION, this is bend $have"
fi

if grep -n '@unsafe\|^def [^ (]*?' hand.bend dd.bend sim.bend LAWS.bend SPEC.bend PROOF.bend src/*.bend tests/*.bend bench/*.bend; then
  echo "FAIL: @unsafe is not allowed anywhere"
  exit 1
fi

echo "== build"
bend hand.bend -o hand
bend dd.bend -o dd
bend sim.bend -o sim
bend tests/unit.bend -o tests/unit
bend tests/oracle.bend -o tests/oracle
mkdir -p build
bend bench/gpu.bend -o build/gpu
bend tests/play.bend -o build/play

echo "== unit tests"
tests/unit

echo "== every ending of 1 and 2 cards"
bend tests/exhaust.bend -o build/exhaust
build/exhaust 1
build/exhaust 2

echo "== search against brute force, inside Bend"
if [ $quick = 1 ]; then
  tests/oracle 2000 3
  tests/oracle 500 4
else
  tests/oracle 5000 3
  tests/oracle 5000 4
  tests/oracle 200 5
  # From fewer suits, which makes long runs and voids common.
  tests/oracle 5000 3 1 2
  tests/oracle 2000 4 1 2
  tests/oracle 200 3 1 1
fi

echo "== single cards from any point in a trick, against brute force"
if [ $quick = 1 ]; then
  build/play 1000 3
  build/play 300 4
else
  build/play 5000 3
  build/play 2000 4
  build/play 200 5
fi

echo "== hand output"
want=$(cat tests/data/hand.sha256)
got=$(i=1; while [ $i -le 1000 ]; do ./hand $i; i=$((i + 1)); done | shasum -a 256 | cut -d ' ' -f 1)
if [ "$got" != "$want" ]; then
  echo "FAIL: hand's output changed: $got"
  exit 1
fi
echo "OK: hand prints the same 1000 deals"

if [ $quick = 0 ]; then
  echo "== proofs"
  out=$(bend PROOF.bend 2>&1) || { echo "$out"; exit 1; }
  echo "$out"
  case "$out" in
    *"ALL PROOFS CHECK"*) ;;
    *) exit 1 ;;
  esac
fi

echo "== python"
if [ ! -x .venv/bin/python ]; then
  python3 -m venv .venv
  .venv/bin/pip install -q endplay
fi

echo "== round trip"
.venv/bin/python tools/check.py roundtrip --count 1000

echo "== DDS lists"
.venv/bin/python tools/check.py lists

echo "== whole deals against DDS"
if [ $quick = 1 ]; then
  .venv/bin/python tools/check.py full --limit 12
else
  .venv/bin/python tools/check.py speed
  .venv/bin/python tools/check.py full --file tests/data/list10000.txt --limit 10000
fi

echo "== search against brute force, from Python"
if [ $quick = 1 ]; then
  .venv/bin/python tools/check.py oracle --count 500 --cards 3 4
else
  .venv/bin/python tools/check.py oracle --count 2000 --cards 3 4
  .venv/bin/python tools/check.py oracle --count 2000 --cards 3 4 --suits 2
  .venv/bin/python tools/check.py oracle --count 100 --cards 5
fi

echo "== output for people"
./dd --demo 1 5 > /dev/null
.venv/bin/python tools/check.py human

echo "== sure tricks against DDS"
if [ $quick = 1 ]; then
  .venv/bin/python tools/check.py sure --limit 100 --count 50 --cards 2 4 8
else
  .venv/bin/python tools/check.py sure --count 300
  .venv/bin/python tools/check.py sure --file --count 300 --cards 4 6 --suits 2
fi

echo "== endings against DDS"
if [ $quick = 1 ]; then
  .venv/bin/python tools/check.py endings --count 200 --cards 3 4
  .venv/bin/python tools/check.py endings --count 200 --cards 3 --brute
  .venv/bin/python tools/check.py endings --count 20 --cards 7
else
  .venv/bin/python tools/check.py endings --count 2000 --cards 3 4
  .venv/bin/python tools/check.py endings --count 1000 --cards 3 4 --brute
  .venv/bin/python tools/check.py endings --count 200 --cards 5 --brute
  .venv/bin/python tools/check.py endings --count 500 --cards 5 6
  .venv/bin/python tools/check.py endings --count 300 --cards 7
  .venv/bin/python tools/check.py endings --count 200 --cards 8
  .venv/bin/python tools/check.py endings --count 200 --cards 6 --suits 2
fi

echo "== simulation layouts against DDS"
d42="N:A8.J94.KQ62.KT86 - QJ73.AKQ65.98.AJ -"
.venv/bin/python tools/simcheck.py --count 10 deal="N:- - - T952.T2.JT754.97" contract=4H by=S S.hcp=15-19 S.H=5+ seed=1
.venv/bin/python tools/simcheck.py --count 10 deal="$d42" contract=3NT by=N play=C5 E.C=5+ seed=2
.venv/bin/python tools/simcheck.py --count 10 deal="$d42" contract=6H by=S play="DJ D2 DA D8 S2" W.D=5+ seed=3
.venv/bin/python tools/simcheck.py --count 10 deal="N:- K64.873.A3.Q5432 - T952.T2.JT754.97" contract=2S by=W play="HA H3 H6 HT HK H7 HQ H2 D2" N.hcp=12-20 seed=4
.venv/bin/python tools/simcheck.py --count 10 deal="N:- - - T952.T2.JT754.97" contract=4H by=S play="DJ D2 DA D8 D3 D9 D4 DK DQ C2 S3 D5 S4 S6 SK" seed=5

echo "ALL TESTS PASS"
