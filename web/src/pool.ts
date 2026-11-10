// A pool of solver workers with one queue. Each job is one run of the solver's
// main (web/wasm.bend) with these arguments, and resolves to what it printed.

type Pending = { id: number; args: string[]; ok: (s: string) => void; fail: (e: Error) => void };

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

  run(args: string[]): Promise<string> {
    return new Promise((ok, fail) => {
      this.queue.push({ id: this.next++, args, ok, fail });
      this.pump();
    });
  }

  // Drops the jobs that haven't started, as when a new deal replaces the old one.
  clear() {
    for (const p of this.queue) p.fail(new Error("cancelled"));
    this.queue = [];
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

// Five is the most a table can use, one worker per strain.
export function poolSize(): number {
  const n = navigator.hardwareConcurrency || 4;
  return Math.max(2, Math.min(5, n - 1));
}
