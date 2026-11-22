"""Like rightlang_sat.py, but only right halves of width <= W (cells beyond W are 0 at time 0). Usage: rightlang_w.py N ph W
with a SAT feasibility check per prefix. Column 0 is c(t) = (t+ph)&1. Usage: rightlang_sat.py N ph"""
import sys
from pysat.solvers import Cadical153
N, ph, W = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
c = lambda t: (t + ph) & 1
free = [t for t in range(4 * N) if not c(t)][:N]
Tm = free[-1]
nv = 0; X = {}; cl = []
def new():
    global nv; nv += 1; return nv
for t in range(Tm + 1):
    for i in range(1, Tm + 2 - t): X[t, i] = new()
for t in range(Tm):
    for i in range(1, Tm + 1 - t):
        y, ce, r = X[t + 1, i], X[t, i], X[t, i + 1]
        o = new(); cl += [[-ce, o], [-r, o], [ce, r, -o]]
        if i == 1:
            if c(t): cl += [[y, o], [-y, -o]]      # y = 1 ^ o
            else: cl += [[-y, o], [y, -o]]         # y = o
        else:
            l = X[t, i - 1]; cl += [[-y, l, o], [-y, -l, -o], [y, -l, o], [y, l, -o]]
cl += [[-X[0, i]] for i in range(W + 1, Tm + 2)]
s = Cadical153(bootstrap_with=cl)
count = [0] * (N + 1); words = {n: [] for n in range(N + 1)}
def dfs(assump, n):
    count[n] += 1
    if n <= 40: words[n].append(''.join('1' if a > 0 else '0' for a in assump))
    if n == N: return
    v = X[free[n], 1]
    for lit in (-v, v):
        if s.solve(assumptions=assump + [lit]): dfs(assump + [lit], n + 1)
dfs([], 0)
print(f"W={W} ph={ph}", ' '.join(f"{n}:{count[n]}" for n in range(1, N + 1)), flush=True)
