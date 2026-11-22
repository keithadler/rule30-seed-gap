"""Exact count of rows beside an alternating center column.
Counts words w (cells 1..k at even time T, cell 1 = 1) for which SOME right half at time 0
gives w at time T with column 0 = t mod 2 throughout.  usage: rowlang_sat.py T kmax"""
import sys
from pysat.solvers import Cadical153
T = int(sys.argv[1]); K = int(sys.argv[2])
assert T % 2 == 0
vid = {}
def v(t, j):
    if (t, j) not in vid: vid[(t, j)] = len(vid) + 1
    return vid[(t, j)]
s = Cadical153()
for t in range(T + 1):
    s.add_clause([v(t, 0)] if t & 1 else [-v(t, 0)])
for t in range(T):
    for j in range(1, K + (T - t - 1) + 1):
        n, l, c, r = v(t + 1, j), v(t, j - 1), v(t, j), v(t, j + 1)
        # n = l xor (c or r)
        for lb in (0, 1):
            for cb in (0, 1):
                for rb in (0, 1):
                    nb = lb ^ (cb | rb)
                    cl = [(-l if lb else l), (-c if cb else c), (-r if rb else r), (n if nb else -n)]
                    s.add_clause(cl)
counts = [0] * (K + 1)
def dfs(prefix):
    k = len(prefix)
    counts[k] += 1
    if k == K: return
    for b in (0, 1):
        a = prefix + [v(T, k + 1) if b else -v(T, k + 1)]
        if s.solve(assumptions=a): dfs(a)
a0 = [v(T, 1)]
if s.solve(assumptions=a0): dfs(a0)
print("T", T, "counts k=1..:", *counts[1:])
