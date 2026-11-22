"""Check the repetition lemma on real seeds: every seed in [-A, A], run while the center column
is 0,1,0,1,...; inside the surviving window, any i < i2 with e[i:i+m] == e[i2:i2+m] must have
2m < w + 2*i2, where -w is the seed's leftmost one."""
import sys
A = int(sys.argv[1]); viol = 0; pairs = 0; best = 0
for s in range(1, 1 << (2 * A + 1)):
    cells = {j - A for j in range(2 * A + 1) if (s >> j) & 1}
    w = -min(cells)
    e = []; t = 0; cur = cells
    while t < 200:
        if ((0 in cur) != bool(t & 1)): break
        if t % 2 == 0: e.append(1 if 1 in cur else 0)
        nxt = set()
        for i in range(min(cur) - 1, max(cur) + 2):
            if ((i - 1) in cur) != ((i in cur) or ((i + 1) in cur)): nxt.add(i)
        cur = nxt; t += 1
    T = t                     # column correct on times 0..T-1
    n = len(e)
    for i in range(n):
        for i2 in range(i + 1, n):
            m = 0
            while i2 + m < n and 2 * (i2 + m) + 1 < T and e[i + m] == e[i2 + m]: m += 1
            if m:
                pairs += 1
                if 2 * m >= w + 2 * i2 and w + 2 * i2 >= 1: viol += 1
                best = max(best, 2 * m - (w + 2 * i2))
print("A", A, "seeds", (1 << (2 * A + 1)) - 1, "repeating pairs", pairs, "violations", viol, "closest margin (must stay < 0):", best)
