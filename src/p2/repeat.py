"""Repetition lemma: for a period-2 seed with leftmost one at -w, any i < i2 has
   lcp(e shifted i, e shifted i2) < i2 + w/2.   So w > 2*(lcp - i2) for every pair.
For each right half R (width <= r) compute e for n double steps and the best lower bound on w."""
import sys
r = int(sys.argv[1]); n = int(sys.argv[2])
def e_of(R):
    row = R; e = []
    for t in range(2 * n):
        if t % 2 == 0: e.append(row & 1)
        row = ((row << 1) | (t & 1)) ^ (row | (row >> 1))
    return e
def bound(e):
    best = (-10**9, 0, 0, 0)
    for j in range(1, n // 2):                 # shift
        run = 0
        # lcp(e[i:], e[i+j:]) for all i by scanning from the right, only trusted inside the window
        l = [0] * (n - j + 1)
        for i in range(n - j - 1, -1, -1):
            l[i] = l[i + 1] + 1 if e[i] == e[i + j] else 0
        for i in range(0, n - j):
            if i + j + l[i] >= n: continue    # runs off the window: lcp only known to be >= this
            b = 2 * (l[i] - (i + j))
            if b > best[0]: best = (b, i, i + j, l[i])
    return best
res = []
for R in range(0, 1 << r):
    e = e_of(R)
    # condition for an alternating column: no two ones in a row in e (else this R is already dead)
    res.append((bound(e), R))
res.sort(reverse=True)
from collections import Counter
print("right halves", len(res), "window", n, "double steps")
print("largest bounds (w > b, i, i2, lcp, R):")
for (b, R) in res[:8]: print("  ", b, bin(R))
c = Counter(max(b[0], 0) // 10 * 10 for b, R in res)
print("bound histogram by tens (0 = nothing learned):", sorted(c.items()))
