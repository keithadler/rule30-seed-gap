"""For every no-11 word e, compute the forced left half-plane (phase 0) and classify each cell
(depth k, time t) as: constant, a single e bit, its negation, or how many e bits it depends on."""
import sys
n = int(sys.argv[1]); KM = int(sys.argv[2]); TM = int(sys.argv[3])
words = []
def gen(p, last):
    if len(p) == n: words.append(p); return
    gen(p + [0], 0)
    if not last: gen(p + [1], 1)
gen([], 0)
NT = 2 * n
C = sum(1 << t for t in range(1, NT + 2, 2))
def cols(e):
    # column -1: odd times 1, even times not e
    A = 0
    for t in range(NT):
        A |= (1 if t & 1 else 1 - e[t // 2]) << t
    out = [A]; prev, cur = C, A
    for k in range(2, KM + 1):
        nxt = ((cur >> 1) ^ (cur | prev))
        prev, cur = cur, nxt; out.append(cur)
    return out            # out[k-1] valid for times t <= NT - k
W = len(words); print("words", W)
vec = {}                  # (k,t) -> bitset over words
for wi, e in enumerate(words):
    cs = cols(e)
    for k in range(1, KM + 1):
        c = cs[k - 1]
        for t in range(TM):
            if t + k <= NT - 1 and (c >> t) & 1:
                vec[(k, t)] = vec.get((k, t), 0) | (1 << wi)
full = (1 << W) - 1
ev = [sum(1 << wi for wi, e in enumerate(words) if e[j]) for j in range(n)]
def name(v):
    if v == 0: return "0"
    if v == full: return "1"
    for j in range(n):
        if v == ev[j]: return f"e{j}"
        if v == full ^ ev[j]: return f"~e{j}"
    return "*"
for t in range(TM):
    print(f"t={t}:", " ".join(name(vec.get((k, t), 0)) if t + k <= NT - 1 else "?" for k in range(1, KM + 1)))
