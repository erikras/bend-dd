// bench/brute.c: the same plain minimax as src/brute.bend, in plain C, as a
// baseline for the node rate. It visits exactly the same positions, so its node
// count must match dd --brute. It keeps Bend's shape on purpose: position records
// copied per move, the same packed words, and a move list built per node (in a
// stack array here, not a heap list).
//
//   clang -O2 -o build/brute-c bench/brute.c && build/brute-c file-of-deals

#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

typedef uint32_t u32;

typedef struct {
  u32 w[8];   // n01 n23 e01 e23 s01 s23 w01 w23
  u32 trick;  // seat | played << 2 | lead << 4 | owner << 7 | best << 9
  u32 won;
} Pos;

static uint64_t nodes;

static inline u32 make(u32 seat, u32 played, u32 lead, u32 owner, u32 best) {
  return seat | played << 2 | lead << 4 | owner << 7 | best << 9;
}

static inline int beats(u32 t, u32 best, u32 c) {
  u32 cs = c >> 4, bs = best >> 4;
  return (cs == bs && c > best) || (cs == t && bs != t);
}

static inline Pos play(u32 t, Pos p, u32 c) {
  u32 tr = p.trick, seat = tr & 3, played = (tr >> 2) & 3, lead = (tr >> 4) & 7;
  u32 owner = (tr >> 7) & 3, best = (tr >> 9) & 63, cs = c >> 4;
  u32 m = 1u << (c & 15);
  p.w[seat * 2 + (cs >= 2)] ^= (cs & 1) == 0 ? m << 16 : m;
  int win = beats(t, best, c);
  if (played == 0) {
    p.trick = make((seat + 1) & 3, 1, cs, seat, c);
  } else if (played == 3) {
    u32 w = win ? seat : owner;
    p.trick = make(w, 0, 4, 0, 0);
    p.won += (w & 1) == 0;
  } else {
    p.trick = make((seat + 1) & 3, played + 1, lead, win ? seat : owner, win ? c : best);
  }
  return p;
}

static inline int peel(u32 suit, u32 m, u32* out, int n) {
  while (m) {
    u32 b = m & (0 - m);
    m ^= b;
    out[n++] = suit << 4 | (u32)__builtin_ctz(b);
  }
  return n;
}

static inline int moves(const Pos* p, u32* out) {
  u32 seat = p->trick & 3, lead = (p->trick >> 4) & 7;
  u32 a = p->w[seat * 2], b = p->w[seat * 2 + 1];
  u32 f = lead == 0 ? a >> 16 : lead == 1 ? (a & 65535) : lead == 2 ? b >> 16 : lead == 3 ? (b & 65535) : 0;
  if (f) {
    return peel(lead, f, out, 0);
  }
  int n = peel(3, b & 65535, out, 0);
  n = peel(2, b >> 16, out, n);
  n = peel(1, a & 65535, out, n);
  return peel(0, a >> 16, out, n);
}

static u32 search(int d, u32 t, const Pos* p) {
  if (d == 0) {
    return p->won;
  }
  int ns = (p->trick & 1) == 0;
  u32 best = ns ? 0 : 13, ms[13];
  int n = moves(p, ms);
  for (int i = 0; i < n; i++) {
    nodes++;
    Pos child = play(t, *p, ms[i]);
    u32 v = search(d - 1, t, &child);
    best = ns ? (v > best ? v : best) : (v < best ? v : best);
  }
  return best;
}

static int rank_bit(char c) {
  const char* r = "23456789TJQKA";
  const char* f = strchr(r, c);
  return f ? (int)(f - r) : -1;
}

int main(int argc, char** argv) {
  FILE* f = fopen(argv[1], "r");
  char line[256];
  uint64_t total = 0;
  u32 sum = 0;
  struct timespec a, b;
  Pos deals[100000];
  int counts[100000], nd = 0;
  while (fgets(line, sizeof line, f)) {
    Pos p;
    memset(&p, 0, sizeof p);
    int seat = 0, suit = 0, cards = 0;
    for (char* c = line + 2; *c && *c != '\n'; c++) {
      if (*c == ' ') { seat++; suit = 0; }
      else if (*c == '.') { suit++; }
      else {
        u32 m = 1u << rank_bit(*c);
        p.w[seat * 2 + (suit >= 2)] |= (suit & 1) == 0 ? m << 16 : m;
        cards++;
      }
    }
    counts[nd] = cards;
    deals[nd++] = p;
  }
  clock_gettime(CLOCK_MONOTONIC, &a);
  for (int i = 0; i < nd; i++) {
    for (u32 t = 0; t < 5; t++) {
      for (u32 decl = 0; decl < 4; decl++) {
        Pos p = deals[i];
        p.trick = make((decl + 1) & 3, 0, 4, 0, 0);
        sum += search(counts[i], t, &p);
      }
    }
  }
  clock_gettime(CLOCK_MONOTONIC, &b);
  total = nodes;
  double ms = (b.tv_sec - a.tv_sec) * 1e3 + (b.tv_nsec - a.tv_nsec) / 1e6;
  printf("%d deals, %llu nodes in %.0f ms: %.0f nodes/s (checksum %u)\n", nd,
    (unsigned long long)total, ms, total * 1e3 / ms, sum);
  return 0;
}
