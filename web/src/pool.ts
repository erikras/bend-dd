// A pool of solver workers with one queue. Each job is one run of the solver's
// main (web/wasm.bend) with these arguments, and resolves to what it printed.
//
// Each run makes a new instance of the solver, whose memory grows past 512 MB, and
// a worker that has finished one still holds that memory until its garbage is
// collected. Safari and the iOS app count it all against the page and fail the next
// run or end the page, so a worker is used for one job and then replaced. The
// solver is compiled once, here, and handed to each worker with its job.

type Pending = { id: number; args: string[]; tag: string; tries: number; ok: (s: string) => void; fail: (e: Error) => void };

// The solver's message when its heap can't be had: the memory of the workers just
// replaced may not be back yet, so the job waits a little and runs again.
const NO_MEMORY = /reservation failed|out of memory/i;

export class Pool {
  private workers: Worker[] = [];
  private idle: Worker[] = [];
  private queue: Pending[] = [];
  private busy = new Map<Worker, Pending>();
  private next = 1;
  private mod = WebAssembly.compileStreaming(fetch(new URL("./solver.wasm", import.meta.url)));

  constructor(readonly size: number) {
    for (let i = 0; i < size; i++) this.idle.push(this.spawn());
  }

  private spawn(): Worker {
    const w = new Worker(new URL("./worker.js", import.meta.url), { type: "module" });
    w.onmessage = (e) => this.done(w, e.data);
    w.onerror = (e) => this.done(w, { error: e.message || "the solver failed" });
    this.workers.push(w);
    return w;
  }

  run(args: string[], tag = ""): Promise<string> {
    return new Promise((ok, fail) => {
      this.queue.push({ id: this.next++, args, tag, tries: 0, ok, fail });
      this.pump();
    });
  }

  // Drops the jobs that haven't started, as when a new deal replaces the old one:
  // all of them, or those with this tag.
  clear(tag?: string) {
    const drop = this.queue.filter((p) => tag === undefined || p.tag === tag);
    this.queue = this.queue.filter((p) => !drop.includes(p));
    for (const p of drop) p.fail(new Error("cancelled"));
  }

  private pump() {
    while (this.idle.length && this.queue.length) {
      const w = this.idle.pop()!;
      const p = this.queue.shift()!;
      this.busy.set(w, p);
      this.mod.then(
        (mod) => w.postMessage({ id: p.id, args: p.args, mod }),
        (e) => this.done(w, { error: String(e) }),
      );
    }
  }

  private done(w: Worker, msg: { out?: string; error?: string }) {
    const p = this.busy.get(w);
    if (!p) return;
    this.busy.delete(w);
    w.terminate();
    this.workers = this.workers.filter((x) => x !== w);
    this.idle.push(this.spawn());
    if (msg.error !== undefined && NO_MEMORY.test(msg.error) && p.tries < 4) {
      p.tries++;
      setTimeout(() => { this.queue.unshift(p); this.pump(); }, 250 * p.tries);
    } else if (msg.error !== undefined) p.fail(new Error(msg.error));
    else p.ok(msg.out ?? "");
    this.pump();
  }
}

// A table uses five, one per strain; a simulation uses them all. Each worker's
// memory is about 530 MB, most of it reserved and never touched; the solver uses
// about 75 MB of it.
export function poolSize(): number {
  const n = navigator.hardwareConcurrency || 4;
  // The iOS app (ios/) sets a lower cap from the device's memory: iOS ends the
  // page's process when the workers' memories add up to too much.
  const cap = (globalThis as any).ddNative?.maxWorkers ?? 8;
  return Math.max(2, Math.min(cap, n - 1));
}
