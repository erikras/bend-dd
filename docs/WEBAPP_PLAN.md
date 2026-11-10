# Plan: a web app for seeing and studying deals

This is a plan, not code. It says what the app does, how the Bend solver gets into it,
where it runs, and the order to build it in. The decisions Erik needs to make are in
§8, each with a recommendation.

## 1. Goal

A web page where anyone can look at a bridge deal and see what double dummy analysis
says about it:

- the four hands, drawn the way bridge players expect;
- the 4 x 5 double dummy table, and the par score that follows from it;
- the play, trick by trick, with every legal card marked by the tricks it takes;
- the single-dummy simulator: hide the hands a player can't see, give the auction's
  rules, and see each card's average tricks and how often the contract makes.

The same speed rule as the solver applies: it should feel instant for one deal and stay
quick for a simulation. A deal should be shareable as a link.

## 2. What we have to work with

What main has now (as of 2026-11-10):

- `dd` solves PBN deals to the full table, about 16 deals a second on cadmium's 12
  threads. 12 threads give about 6 times one, so one thread does a deal in roughly
  0.4 s.
- `dd --random [seed]` deals a hand from a seed and solves it.
- `sim` runs the single-dummy simulation, 200 layouts of an opening lead in 0.9 s on 12
  threads and 4.4 s on one. Each layout has its own random state from the seed and its
  index (`layout.seed` in `src/sim.bend`), so a seed gives the same layouts whatever the
  split. That matters below: the work can be cut into pieces anywhere and still give
  the CLI's exact answer.
- `src/play.bend` values one card from any point in a trick, which is exactly what a
  play-through view needs.

What Bend 2.0.40 gives us for the web (from its guide and compiler source):

- `bend file.bend -o file.mjs` emits an ES module of the file's non-IO defs, which a JS
  file can import and call. Values cross without a copy; constructors look like
  `{$: "Name", field: value}`, `Nat` is a number.
- `bend page.html -o dist` bundles a web page that imports `.bend` files directly.
- The JavaScript target runs sequentially: no parallel calls, no GPU. Parallelism in a
  browser has to come from Web Workers, one solver per worker.
- `bend file.bend -o file.c` emits C. The runtime it emits uses pthreads, C11 atomics,
  `mmap`, `poll` and signals. In principle Emscripten can build that to WebAssembly with
  threads, but nothing in Bend supports it, and it is untested.
- Bend can also write servers (`TCP.listen`, as in `demos/io_http_server`), but HTTP and
  JSON written by hand in Bend would be a lot of code for little gain.

What we don't know yet, and must measure first (Phase 0): how fast the JS target runs
the search. Its output is plain JS functions, not an interpreter, so a guess is 3 to 10
times slower than one native thread. That would put one table at about 1 to 4 s in one
worker and about 0.3 to 1 s with one worker per strain (a heavy strain sets the pace). The memory is known: the
transposition table is a 32 MB `Array<U32>` per strain, so 5 workers need about 160 MB.

## 3. Architecture

### 3.1 Options

| | A. Everything in the browser (recommended) | B. Native solver on a server | C. WebAssembly from the emitted C |
|---|---|---|---|
| How | Bend → `.mjs` → one solver per Web Worker | A small HTTP service runs the `dd` and `sim` binaries | Emscripten builds Bend's C, pthreads become workers |
| Speed for one user | Slowest, unknown until Phase 0 | Fastest: 12 native threads | Likely between A and B |
| Many users | Each brings their own CPU, so it scales for free | Users share the server's cores; needs a queue and limits | Same as A |
| Cost and upkeep | A static site: free, nothing to keep running | A machine to pay for, patch and watch | Static site, but needs COOP/COEP headers for threads |
| Risk | Low; it is Bend's supported path | Low technically, but it is a service on the internet | High: unsupported, may not build at all |
| Works offline, no account | Yes | No | Yes |

### 3.2 Recommendation

Start with **A**, and decide B or C only if Phase 0 says the browser is too slow.

The Bend code goes in one new file, `web/api.bend`, that imports `src/` and exposes a
few pure defs with plain inputs and outputs (strings and numbers), so nothing in the
solver changes and the proofs are untouched:

- `api.strain(pbn, strain) -> String`: the four declarers' tricks for one strain. Five
  workers each take a strain, and the page shows each column as it arrives.
- `api.cards(pbn, trump, played) -> String`: for the player to move, the tricks each
  legal card takes, from `src/play.bend`. This drives the play-through.
- `api.sim(setup, seed, first, count) -> String`: the tallies for layouts `first` to
  `first + count - 1`. The page splits `n` layouts over the workers in small chunks,
  adds the tallies up as they come back, and draws the results as they firm up. Because
  layouts are seeded by index, the merged answer equals `sim`'s for the same seed.
- `api.random(seed) -> String`: a deal from a seed, the same one `dd --random` gives.

Each returns a short text in a fixed format (or JSON written by Bend) rather than Bend
constructors, so the JS side stays independent of the solver's types.

`bend web/api.bend -o web/dist/api.mjs` builds the module. Building it ahead of time,
rather than letting the page bundler compile `.bend` on the fly, keeps the worker setup
ordinary and the output cacheable.

The page itself is TypeScript with Preact (small and fast), built with Bun, which Bend
already needs. A worker pool of `min(navigator.hardwareConcurrency, 8)` workers, each
holding one transposition table that it keeps from one job to the next, as `sim` does.
On phones the pool is smaller (2 to 4), and if memory is short the table size becomes a
parameter of `api.bend` (a check for Phase 0).

### 3.3 If the browser is too slow

- A server (B) would wrap the existing binaries: `POST /table` runs `dd`, `POST /sim`
  runs `sim` and streams its rows. A thin layer in Bun or Go, one job per core, a queue,
  and a per-IP rate limit. The page would try the server for large simulations and fall
  back to workers. Hosting would be a small Linux VM (Hetzner, Fly.io), built with clang;
  the GPU is not needed.
- WebAssembly (C) is worth a one-day spike only if A is too slow and B is unwanted.

## 4. The UI

One page, three panes that share one deal.

**Deal.** The four hands around a compass, North at the top, with dealer and
vulnerability. Suits in the usual order with ♠ ♥ ♦ ♣ symbols, red and black or a
four-colour option. Cards played so far are greyed out. Ways to get a deal:

- *Random*, from a seed shown on screen, the same deal as `dd --random <seed>`;
- *Paste PBN*, the format `dd` reads;
- *Edit*, clicking cards into hands (Phase 5);
- *Open a file* of PBN boards, shown as a list to step through (Phase 5).

**Analysis.** The double dummy table (declarers down, strains across, as `dd --random`
prints it), filled in column by column as the workers finish, plus the par contract and
score worked out from the table in TypeScript. Clicking a cell picks that contract and
declarer for the other panes.

**Play.** Click a card to play it. Every legal card for the player to move shows the
tricks it takes for declarer, with the best cards highlighted and the cost of each
mistake shown as -1, -2. Undo, step back and forward through the tricks, and a running
count of tricks won. Cards that play the same (touching honours) are marked as a group,
as `sim` shows them.

**Simulate.** Pick whose view it is (the opening leader, or declarer with dummy), and the
hidden hands drop out of the diagram. Rules from the auction as rows: seat, points or a
suit, and a range, the same rules `sim` takes. Then the number of layouts and a seed.
The result is `sim`'s table drawn as bars per card, average tricks and percent making,
updating as chunks come in, with the layouts kept and dealt, and the time. Later, a
histogram of tricks per card (a small addition to `src/sim.bend`'s tally) and a list of
sample layouts to open in the Deal pane.

**Sharing.** The whole state lives in the URL fragment: deal, dealer, vulnerability,
play so far, and simulation settings. A link opens the same view, needs no server
storage, and the seed makes a simulation repeat exactly.

Accessibility and layout: works with the keyboard (arrow keys to step through play),
readable at phone width with the hands stacked, and suit colours that don't rely on
colour alone.

## 5. Hosting

For option A the app is a folder of static files. Erik doesn't want GitHub Actions, so
the build and the deploy both run on cadmium from one script, `tools/web.sh build` and
`tools/web.sh deploy`.

| Host | Deploy without Actions | Custom headers (needed for C) | Cost |
|---|---|---|---|
| Cloudflare Pages (recommended) | `wrangler pages deploy web/dist` from the Mac | Yes, `_headers` file | Free |
| GitHub Pages | Push `web/dist` to a `gh-pages` branch (GitHub's own Pages build then publishes it) | No | Free |
| Netlify | `netlify deploy` from the Mac | Yes | Free tier |
| A VPS (needed for B) | `rsync` and a service | Yes | About $5 to $20 a month |

Cloudflare Pages is recommended because it is free, deploys from the command line,
allows the headers WebAssembly threads would need, and serves preview URLs for each
deploy. A custom domain is optional.

## 6. Testing

- `tools/test.sh` gains a web step: build `api.mjs`, run it under Bun on `list100`, and
  check every table against the native `dd`'s output. Then check `api.sim` split into
  chunks against `sim` with the same seed, number for number.
- A Playwright smoke test on cadmium: open a random deal, wait for the table, play a
  trick, run a small simulation, check the numbers against the CLI.
- Speed is tracked in a small `tools/web.sh bench`: one table and the README's
  200-layout simulation, in Bun and in a real browser, so the numbers sit next to the
  native ones in `docs/PLAN.md`.

## 7. Phases

Each phase ends with something usable and deployed.

0. **Spike, about a day.** Build `api.mjs` for one strain. Time `list100` under Bun and
   in Chrome and Safari workers on cadmium, and on a phone. Measure memory with 5 and 8
   workers. Check that `api.sim` chunks merge to `sim`'s exact output. Outcome: go on
   with A, or bring §3.3 back to Erik with numbers.
1. **API and workers.** `web/api.bend`, the worker pool, the tests in §6.
2. **Viewer.** Deal diagram, random and pasted deals, the table filling in by strain,
   par, shareable links. Deploy. This is the first version people can use.
3. **Play-through.** Per-card tricks at every point, undo and step, keyboard.
4. **Simulator.** The Simulate pane with rules, progress, and results drawn as bars.
5. **More input and output.** Deal editor, PBN files with many boards, export of the
   tables as CSV, and possibly LIN links from BBO hand records.
6. **Only if needed.** The server (B) for large simulations, or the WebAssembly spike (C).

## 8. Decisions for Erik

1. **Where the solver runs.** Recommended: in the browser (A), confirmed by Phase 0's
   numbers before anything else is built. The alternative is a server running the
   native binaries (B), faster but a running service to pay for and watch.
2. **Where it's hosted.** Recommended: Cloudflare Pages, deployed from cadmium with one
   command. Alternatives: GitHub Pages from a branch, or a VPS.
3. **Who it's for.** Public on the open web, or just for Erik for now? This changes how
   much polish Phase 2 needs and whether a domain name is worth getting.
4. **What the first version shows.** Recommended: the viewer and the table (Phase 2)
   ship first, then play-through, then the simulator. Alternatively, wait and launch with
   all three.
5. **Same repo or a new one.** Recommended: a `web/` folder in this repo, so the app
   and the solver are tested and versioned together.
