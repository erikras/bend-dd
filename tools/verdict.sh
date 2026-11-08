#!/bin/sh
# tools/verdict.sh: recheck the proofs with Bend's kernel, as far as it can go.
#
# `bend PROOF.bend --verdict` runs out of fuel on the laws that walk a whole
# domain (see docs/PLAN.md §2.10), so this copies the proofs to a temporary
# directory, leaves those laws and whatever rests on them out
# (tools/verdict_prune.py), and runs --verdict on the rest. Needs Lean 4.34.0
# (elan toolchain leanprover/lean4:v4.34.0) for bend 2.0.40.

set -e
cd "$(dirname "$0")/.."
PATH="$HOME/.bend/bin:$HOME/.elan/bin:$PATH"
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
cp -r src SPEC.bend LAWS.bend PROOF.bend "$dir"
python3 tools/verdict_prune.py "$dir"
cd "$dir"
BEND_NO_TELEMETRY=1 bend PROOF.bend --verdict
