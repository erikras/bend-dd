#!/usr/bin/env python3
"""Patches Bend's emitted C so that Emscripten can build it to WebAssembly.

  wasm-patch.py in.c out.c [heap MB] [stack MB]

Each change is a plain text substitution that must match exactly once, so a new
Bend release that moves the code fails loudly here instead of building wrong.
"""
import sys

src, dst = sys.argv[1], sys.argv[2]
heap_mb = int(sys.argv[3]) if len(sys.argv) > 3 else 512
stack_mb = int(sys.argv[4]) if len(sys.argv) > 4 else 16
c = open(src).read()

def sub(old, new, why):
    global c
    n = c.count(old)
    if n != 1:
        sys.exit(f"wasm-patch: expected one '{old[:60]}' ({why}), found {n}")
    c = c.replace(old, new)

# 1. Segments jump to each other by musttail. WebAssembly's tail calls can't pass a
#    struct by value, so the Env (two pointers) goes as two arguments.
sub("#define WL_SIG Env e, ", "#define WL_SIG DEV u64* e_mem, DEV u64* e_alc, ", "segment signature")
sub("#define WL_ALL e, ", "#define WL_ALL e.mem, e.alc, ", "segment arguments")
sub("#define WL_CASE(F) WL_FN WL_##F(WL_SIG) {", "#define WL_CASE(F) WL_FN WL_##F(WL_SIG) { Env e = { e_mem, e_alc };", "segment entry")

# 2. The heap: an 8 GB reservation that the OS fills lazily. A wasm32 memory holds
#    4 GB at most and Emscripten's mmap commits what it maps, so reserve less.
sub("u64 size   = (!gpu ? 1ull << 33 :", f"u64 size   = (!gpu ? {heap_mb}ull << 20 :", "heap size")

# 3. Each thread's stack: 2 GB reserved. The same, smaller.
sub("u64   len = 1ull << 31;\n  u64   alt = 4 * SIGSTKSZ;", f"u64   len = {stack_mb}ull << 20;\n  u64   alt = 4 * SIGSTKSZ;", "stack size")

# 4. The event loop sizes its select() sets to the highest descriptor, in 8-byte
#    steps. Emscripten's select reads and writes a whole fd_set, 128 bytes.
sub("u64 len = (u64)top / 64 * 8 + 8;", "u64 len = (u64)top / 64 * 8 + 8;\n  len = len < sizeof(fd_set) ? sizeof(fd_set) : len;", "select set size")

# 5. The heap tries fixed addresses high up first, to leave room to grow in place:
#    about fifteen 1 GB maps, each of which Emscripten's mmap allocates and zeroes.
#    A wasm32 memory has no such addresses, so go straight to an ordinary map.
sub("static bool corpus_at(void* at, u64 size) {\n", "static bool corpus_at(void* at, u64 size) {\n#ifdef __EMSCRIPTEN__\n  return false;\n#endif\n", "fixed heap addresses")

# 6. Emscripten's mmap zeroes what it maps, which touches every page of the heap:
#    about 50 ms and the whole heap in real memory, on every run. Memory past the
#    break has never been used and a new wasm memory is zero, so take it from sbrk.
#    The page makes a new instance for every run, so this holds each time.
sub("static void* pool_try(void* at, u64 bytes) {\n", "static void* pool_try(void* at, u64 bytes) {\n#ifdef __EMSCRIPTEN__\n  char* p = sbrk(bytes + 65536);\n  return p == (char*)-1 ? MAP_FAILED : (void*)(((uintptr_t)p + 65535) & ~(uintptr_t)65535);\n#endif\n", "fresh heap")

open(dst, "w").write(c)
