#!/bin/sh
# tools/web.sh: build, serve, test and time the web app.
#
#   tools/web.sh build        the solver for the page and the page, into web/dist
#   tools/web.sh serve [port] build, then serve web/dist on localhost (8642)
#   tools/web.sh test         build, then check the page's solver against dd on list100,
#                             its simulator against sim, its play-through against the
#                             table, and its par against DDS
#   tools/web.sh shots        build, then check the page in Chromium with Playwright and
#                             save screenshots to web/shots/, then in WebKit as an
#                             iPhone 15 (web/bench/iphone.mjs), with its memory
#   tools/web.sh deploy [branch]  build, then deploy a preview to Cloudflare Pages at
#                             https://<branch>.bend-dd.pages.dev/ (dev by default; never main)
#   tools/web.sh bench        time every route on list100: native dd, Bend's JS target,
#                             and Bend's C as WebAssembly with and without threads
#
# Needs bend, clang, node, python3 and Emscripten (brew install emscripten). Bun
# comes with bend: `BUN_BE_BUN=1 bend` is Bun.
#
# The page runs Bend's C, built by Emscripten to WebAssembly without threads, in
# a pool of Web Workers, one strain or one chunk of a simulation each
# (docs/WEBAPP_PLAN.md, section 2, has why).
# web/wasm-patch.py makes the few changes the C needs to build for WebAssembly.

set -e
cd "$(dirname "$0")/.."
PATH="$HOME/.bend/bin:$PATH"
bun() { BUN_BE_BUN=1 bend "$@"; }

B=web/build
D=web/dist
mkdir -p $B

# Emscripten's flags for the solver: tail calls, since Bend's segments jump to each
# other by musttail; a memory that grows, since the heap is mapped at the start, and
# grows by just what's asked: Safari and iOS cap the memory of all a page's workers
# together, and the default 20% more made each one 615 MB rather than 545.
EMFLAGS="-std=c11 -O3 -mtail-call -lm -sALLOW_MEMORY_GROWTH=1 -sMAXIMUM_MEMORY=4GB -sMEMORY_GROWTH_GEOMETRIC_STEP=0"

newer() { # newer target sources...: true when target is missing or older than one
  t=$1; shift
  [ -e "$t" ] || return 0
  for s in "$@"; do [ "$s" -nt "$t" ] && return 0; done
  return 1
}

build_solver() {
  srcs="web/api.bend web/wasm.bend web/wasm-patch.py src/*.bend sim.bend"
  if newer $B/api.mjs $srcs; then
    echo "== bend: api.mjs (the JavaScript target)"
    bend web/api.bend -o $B/api.mjs
  fi
  if newer $B/solver.wasm $srcs tools/web.sh; then
    echo "== bend + emcc: solver.wasm"
    bend web/wasm.bend -o $B/wasm.c
    python3 web/wasm-patch.py $B/wasm.c $B/wasm-patched.c
    emcc $B/wasm-patched.c $EMFLAGS -Wno-unknown-attributes -o $B/solver.mjs \
      -sMODULARIZE=1 -sEXPORT_ES6=1 -sENVIRONMENT=web,worker,node -sEXIT_RUNTIME=1
  fi
}

build_page() {
  echo "== bun: the page"
  [ -d web/node_modules/preact ] || (cd web && bun install)
  rm -rf $D && mkdir -p $D
  bun build web/src/main.tsx web/src/worker.ts --outdir $D --minify --target browser
  cp web/src/index.html web/src/style.css $D/
  cp $B/solver.mjs $B/solver.wasm $D/
}

dd_ready() {
  if newer dd dd.bend src/*.bend; then bend dd.bend -o dd; fi
  if newer sim sim.bend src/*.bend; then bend sim.bend -o sim; fi
  grep '^PBN' tests/data/list100.txt | sed 's/.*"\(.*\)".*/\1/' > $B/list100.pbn
  if newer $B/list100.dd dd $B/list100.pbn; then ./dd $B/list100.pbn > $B/list100.dd; fi
}

case "$1" in
  build)
    build_solver
    build_page
    ;;
  serve)
    build_solver
    build_page
    exec node web/serve.mjs $D "${2:-8642}"
    ;;
  test)
    build_solver
    dd_ready
    echo "== the page's solver (WebAssembly) against dd, list100, five workers"
    node web/bench/bench.mjs wasm strains $B/list100.pbn $B/list100.dd
    echo "== api.sim in chunks against sim (JS target)"
    node web/bench/simcheck.mjs 16
    echo "== the page's simulator (its chunks, merged) against sim, row for row"
    bun web/bench/pagesim.ts
    echo "== play-through: api.cards and the page's rules of play against the table"
    bun web/bench/playcheck.ts $B/list100.pbn $B/list100.dd 4
    echo "== the page's par against DDS's, list100 with every dealer and vulnerability"
    if [ -x .venv/bin/python ]; then
      .venv/bin/python web/bench/par.py $B/list100.pbn > $B/list100.par
      bun web/bench/parcheck.ts $B/list100.dd $B/list100.par
    else
      echo "skipped: no .venv with endplay (tools/test.sh makes one)"
    fi
    ;;
  shots)
    # The page in Chromium: tables against dd, a play-through, the README's simulation
    # against sim, and screenshots in web/shots/. Needs Playwright: NODE_PATH=<the
    # node_modules that has it>, and CHROMIUM=<binary> to use a Chromium of your own.
    build_solver
    build_page
    dd_ready
    node web/serve.mjs $D 8643 > /dev/null &
    server=$!
    trap 'kill $server' EXIT
    sleep 1
    node web/bench/shots.mjs http://localhost:8643/
    node web/bench/layout.mjs http://localhost:8643/
    node web/bench/iphone.mjs http://localhost:8643/
    ;;
  deploy)
    # A preview on Cloudflare Pages, at <branch>.bend-dd.pages.dev (dev by default).
    # Wrangler logs in through the browser (npx wrangler login); no token is kept here.
    # Production is the main branch, which this never deploys to.
    branch=${2:-dev}
    if [ "$branch" = "main" ]; then
      echo "tools/web.sh deploy: main is production; deploy a preview branch instead"
      exit 1
    fi
    build_solver
    build_page
    if ! npx --yes wrangler pages project list 2>/dev/null | grep -q "bend-dd"; then
      # --force: a classic Pages project; wrangler 4.160 otherwise hands this to
      # Workers, which fails to find the static files.
      npx --yes wrangler pages project create bend-dd --production-branch main --force
    fi
    npx --yes wrangler pages deploy $D --project-name bend-dd --branch "$branch" --commit-dirty=true
    echo "preview: https://$branch.bend-dd.pages.dev/"
    ;;
  bench)
    build_solver
    dd_ready
    if newer $B/wasm-pthread.cjs $B/wasm.c web/wasm-patch.py tools/web.sh; then
      # Five strains at once share one heap here, so it needs more than one does.
      echo "== emcc: wasm-pthread.cjs"
      python3 web/wasm-patch.py $B/wasm.c $B/wasm-patched-1g.c 1024
      emcc $B/wasm-patched-1g.c $EMFLAGS -Wno-unknown-attributes -pthread -sNODERAWFS=1 -sPTHREAD_POOL_SIZE=8 -o $B/wasm-pthread.cjs
    fi
    uptime
    echo "== native dd"
    ./dd +RTS --threads 1 -RTS $B/list100.pbn > /dev/null
    ./dd $B/list100.pbn > /dev/null
    echo "== Bend's JavaScript target"
    node web/bench/bench.mjs js one $B/list100.pbn $B/list100.dd
    node web/bench/bench.mjs js strains $B/list100.pbn $B/list100.dd
    echo "== Bend's C as WebAssembly"
    node web/bench/bench.mjs wasm one $B/list100.pbn $B/list100.dd
    node web/bench/bench.mjs wasm strains $B/list100.pbn $B/list100.dd
    python3 web/bench/pthread.py $B/wasm-pthread.cjs 1 $B/list100.pbn $B/list100.dd
    python3 web/bench/pthread.py $B/wasm-pthread.cjs 5 $B/list100.pbn $B/list100.dd
    uptime
    ;;
  *)
    sed -n '2,18p' "$0" | sed 's/^# \{0,1\}//'
    exit 1
    ;;
esac
