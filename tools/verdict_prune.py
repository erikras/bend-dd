"""tools/verdict_prune.py DIR: drop the laws Bend's kernel can't check from a copy.

Bend 2.0.40's kernel (`bend --verdict`) evaluates with a fixed fuel, so a law
proved by running a check over a whole domain, like `{S.facts.all(8192n, 0) ==
True{}}`, runs out of fuel there. This removes from DIR/LAWS.bend and
DIR/PROOF.bend every law whose proof is a bare `{==}` with no arguments, the
laws listed below that walk a domain in other ways, and every proof that rests
on one of them, so the rest can go through the kernel.
"""
import re
import sys

ALSO = ["holding_roundtrip"]


def blocks(path):
    pre, bl, cur = [], [], None
    for line in open(path).read().split("\n"):
        top = line and not line[0].isspace() and not line.startswith(("#", "import"))
        if top:
            cur = [line]
            bl.append(cur)
        elif cur is None:
            pre.append(line)
        else:
            cur.append(line)
    return pre, bl


def name(b):
    m = re.match(r"(?:@unsafe\s+)?(?:law|def|type)\s+([\w.]+)", b[0])
    return m.group(1) if m else None


def main(d):
    lp, lb = blocks(d + "/LAWS.bend")
    pp, pb = blocks(d + "/PROOF.bend")
    dead = {"Laws." + k for k in ALSO}
    for b in pb:
        n = name(b)
        if n and n.startswith("Laws.") and b[0].endswith("():") and len(b) > 1 and b[1].strip() == "{==}":
            dead.add(n)
    changed = True
    while changed:
        changed = False
        for b in pb:
            n = name(b)
            if n in dead:
                continue
            text = "\n".join(b)
            if any(re.search(r"(?<![\w.])" + re.escape(x) + r"\(", text) for x in dead):
                dead.add(n)
                changed = True
    laws = {x[5:] for x in dead if x.startswith("Laws.")}
    open(d + "/LAWS.bend", "w").write("\n".join(lp + ["\n".join(b) for b in lb if name(b) not in laws]))
    open(d + "/PROOF.bend", "w").write("\n".join(pp + ["\n".join(b) for b in pb if name(b) not in dead]))
    kept = sum(1 for b in lb if b[0].startswith("law ") and name(b) not in laws)
    print(f"{len(laws)} laws left out, {kept} kept: " + " ".join(sorted(laws)))


main(sys.argv[1])
