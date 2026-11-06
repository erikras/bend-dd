#!/bin/sh
# tools/test.sh: build everything, check the proofs and run every test.
#
#   tools/test.sh           everything
#   tools/test.sh --quick   skip the proof check and shrink the DDS comparison
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

if grep -n '@unsafe\|^def [^ (]*?' hand.bend dd.bend LAWS.bend SPEC.bend PROOF.bend src/*.bend tests/*.bend bench/*.bend; then
  echo "FAIL: @unsafe is not allowed anywhere"
  exit 1
fi

echo "== build"
bend hand.bend -o hand
bend dd.bend -o dd
bend tests/unit.bend -o tests/unit

echo "== unit tests"
tests/unit

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

echo "== endings against DDS"
if [ $quick = 1 ]; then
  .venv/bin/python tools/check.py endings --count 200 --cards 3 4
else
  .venv/bin/python tools/check.py endings --count 2000 --cards 3 4
  .venv/bin/python tools/check.py endings --count 200 --cards 5
fi

echo "ALL TESTS PASS"
