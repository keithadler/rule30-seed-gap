"""Shortest horizon T at which 'some seed of half-width A has column 0 with period p on [t0,T]' becomes UNSAT.
Uses the exact backward-cone pruned encoding. Usage: mint.py p A1 A2 ..."""
import os, sys, time
from pysat.solvers import Cadical153
from sat_period import build

def unsat(A, T, p, t0):
    cl, _ = build(A, T, p, t0, prune=True)
    s = Cadical153(bootstrap_with=cl); r = s.solve(); s.delete()
    return not r

p = int(sys.argv[1])
for A in map(int, sys.argv[2:]):
    t0 = int(os.environ.get('T0', '0')); t = time.time()
    lo = hi = max(p + 1, t0 + p + 1)
    while not unsat(A, hi, p, t0):
        lo = hi + 1; hi *= 2
        if hi > 2000: break
    if hi > 2000:
        print(f"p={p} t0={t0} A={A}: still SAT at T=2000", flush=True); continue
    while lo < hi:
        m = (lo + hi) // 2
        if unsat(A, m, p, t0): hi = m
        else: lo = m + 1
    print(f"p={p} t0={t0} A={A}: UNSAT first at T={lo}  ({time.time()-t:.0f}s)", flush=True)
