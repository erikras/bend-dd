// One solver: Bend's C as WebAssembly, run once per job in a new instance of the
// compiled module. A new instance starts with a zeroed memory, which the patched
// runtime relies on (web/wasm-patch.py), and costs under a millisecond.

type Job = { id: number; args: string[] };

let compiled: Promise<{ create: any; mod: WebAssembly.Module }> | undefined;

function load() {
  if (!compiled) {
    const base = new URL("./", self.location.href).href;
    const url = base + "solver.mjs";
    compiled = Promise.all([
      import(/* @vite-ignore */ url).then((m) => m.default),
      WebAssembly.compileStreaming(fetch(base + "solver.wasm")),
    ]).then(([create, mod]) => ({ create, mod }));
  }
  return compiled;
}

async function run(args: string[]): Promise<string> {
  const { create, mod } = await load();
  let out = "";
  let err = "";
  try {
    await create({
      arguments: args,
      print: (s: string) => { out += s + "\n"; },
      printErr: (s: string) => { if (!s.startsWith("warning:")) err += s + "\n"; },
      instantiateWasm: (imports: WebAssembly.Imports, ok: (i: WebAssembly.Instance, m: WebAssembly.Module) => void) => {
        WebAssembly.instantiate(mod, imports).then((i) => ok(i, mod));
        return {};
      },
    });
  } catch (x) {
    if (!out) throw new Error(err.trim() || String(x));
  }
  if (!out && err) throw new Error(err.trim());
  return out.trim();
}

self.onmessage = async (e: MessageEvent<Job>) => {
  const { id, args } = e.data;
  try {
    (self as any).postMessage({ id, out: await run(args) });
  } catch (x) {
    (self as any).postMessage({ id, error: String((x as Error).message || x) });
  }
};

load();
