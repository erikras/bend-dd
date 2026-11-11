// One solver: Bend's C as WebAssembly, run once per job in a new instance of the
// module that the pool compiled and sent with the job. A new instance starts with a
// zeroed memory, which the patched runtime relies on (web/wasm-patch.py), and costs
// under a millisecond. The pool replaces this worker after one job (web/src/pool.ts).

type Job = { id: number; args: string[]; mod: WebAssembly.Module };

let glue: Promise<any> | undefined;

function load() {
  if (!glue) {
    const url = new URL("./solver.mjs", self.location.href).href;
    glue = import(/* @vite-ignore */ url).then((m) => m.default);
  }
  return glue;
}

// The size of the instance's memory when the run ended, sent back with the answer.
let memBytes = 0;

async function run(args: string[], mod: WebAssembly.Module): Promise<string> {
  const create = await load();
  let out = "";
  let err = "";
  let mem: WebAssembly.Memory | undefined;
  try {
    await create({
      arguments: args,
      print: (s: string) => { out += s + "\n"; },
      printErr: (s: string) => { if (!s.startsWith("warning:")) err += s + "\n"; },
      instantiateWasm: (imports: WebAssembly.Imports, ok: (i: WebAssembly.Instance, m: WebAssembly.Module) => void) => {
        WebAssembly.instantiate(mod, imports).then((i) => {
          mem = Object.values(i.exports).find((x) => x instanceof WebAssembly.Memory) as WebAssembly.Memory | undefined;
          ok(i, mod);
        });
        return {};
      },
    });
  } catch (x) {
    memBytes = mem?.buffer.byteLength ?? 0;
    if (!out) throw new Error(err.trim() || String(x));
  }
  memBytes = mem?.buffer.byteLength ?? 0;
  if (!out && err) throw new Error(err.trim());
  return out.trim();
}

self.onmessage = async (e: MessageEvent<Job>) => {
  const { id, args, mod } = e.data;
  try {
    const out = await run(args, mod);
    (self as any).postMessage({ id, out, mem: memBytes });
  } catch (x) {
    (self as any).postMessage({ id, error: String((x as Error).message || x), mem: memBytes });
  }
};

load();
