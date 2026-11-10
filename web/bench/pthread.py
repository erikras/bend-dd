#!/usr/bin/env python3
"""Times the threaded WebAssembly build on deals passed as arguments, against dd.

  pthread.py <wasm-pthread.cjs> <threads> deals.pbn dd-output.txt [limit]

The build forks each deal's five strains over Emscripten's pthreads, one deal at a
time, so 5 threads is the most it can use.
"""
import subprocess, sys

js, threads, deals_file, dd_file = sys.argv[1:5]
n = int(sys.argv[5]) if len(sys.argv) > 5 else 100
deals = [l.strip() for l in open(deals_file) if l.strip()][:n]
want = [" ".join(l.split()[:20]) for l in open(dd_file) if l.strip()][:n]
p = subprocess.run(["node", js, "+RTS", "--threads", threads, "-RTS", "--deals", *deals], capture_output=True, text=True)
got = [l for l in p.stdout.splitlines() if l.strip()]
bad = sum(1 for a, b in zip(got, want) if a != b) + abs(len(got) - len(want))
last = (p.stderr.strip().splitlines() or ["?"])[-1]
if not last.startswith("wasm:"):
    print(f"wasm pthread {threads}: failed: {last}")
    sys.exit(1)
ms = int(last.split()[1])
print(f"wasm pthread {threads}: {len(got)} deals in {ms / 1000:.1f} s, {ms / max(len(got), 1):.0f} ms a deal, {bad} wrong")
sys.exit(1 if bad else 0)
