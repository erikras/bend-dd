// A pool of solver workers with one queue. Each job is one run of the solver's
// main (web/wasm.bend) with these arguments, and resolves to what it printed.

type Pending = { id: number; args: string[]; tag: string; ok: (s: string) => void; fail: (e: Error) => void };

export class Pool {
  private workers: Worker[] = [];
  private idle: Worker[] = [];
  private queue: Pending[] = [];
  private busy = new Map<Worker, Pending>();
  private next = 1;

  constructor(readonly size: number) {
    for (let i = 0; i < size; i++) {
      const w = new Worker(new URL("./worker.js", import.meta.url), { type: "module" });
      w.onmessage = (e) => this.done(w, e.data);
      w.onerror = (e) => this.done(w, { error: e.message || "the solver failed" });
      this.workers.push(w);
      this.idle.push(w);
    }
  }

  run(args: string[], tag = ""): Promise<string> {
    return new Promise((ok, fail) => {
      this.queue.push({ id: this.next++, args, tag, ok, fail });
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
      w.postMessage({ id: p.id, args: p.args });
    }
  }

  private done(w: Worker, msg: { out?: string; error?: string }) {
    const p = this.busy.get(w);
    this.busy.delete(w);
    this.idle.push(w);
    if (p) {
      if (msg.error !== undefined) p.fail(new Error(msg.error));
      else p.ok(msg.out ?? "");
    }
    this.pump();
  }
}

// A table uses five, one per strain; a simulation uses them all. Each worker needs
// about 75 MB while it solves.
export function poolSize(): number {
  const n = navigator.hardwareConcurrency || 4;
  return Math.max(2, Math.min(8, n - 1));
}
