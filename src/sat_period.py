"""Is there a finite seed (support in [-A,A]) whose column `col` equals itself shifted by p over [t0, T]?
Rule 30: y = l ^ (c | r).  UNSAT means: no seed of that width looks periodic over that window."""
import sys, time
from pysat.solvers import Cadical153

def build(A, T, p, t0, col=0, rule=30, prune=False):
    nv = [0]
    def new():
        nv[0] += 1; return nv[0]
    cl = []
    X = {}
    for t in range(T + 1):
        # prune: a cell at (t,i) can only reach column 0 by time T if |i| <= T-t (exact, not a relaxation)
        lim = min(A + t, T - t) if prune else A + t
        for i in range(-lim, lim + 1):
            X[t, i] = new()
    def get(t, i):  # None means constant 0 (outside the seed's cone)
        if (t, i) in X: return X[t, i]
        if abs(i) > A + t: return None
        raise AssertionError("pruned cell referenced")
    for t in range(T):
        for i in range(-(A + t + 1), A + t + 2):
            y = X.get((t + 1, i))
            if y is None:
                continue
            l, c, r = get(t, i - 1), get(t, i), get(t, i + 1)
            if rule == 30:
                # o = c | r
                if c is None and r is None: o = None
                elif c is None: o = r
                elif r is None: o = c
                else:
                    o = new(); cl += [[-c, o], [-r, o], [c, r, -o]]
                # y = l ^ o
                if l is None and o is None: cl.append([-y])
                elif l is None: cl += [[-y, o], [y, -o]]
                elif o is None: cl += [[-y, l], [y, -l]]
                else: cl += [[-y, l, o], [-y, -l, -o], [y, -l, o], [y, l, -o]]
            else:  # rule 90 sanity: y = l ^ r
                if l is None and r is None: cl.append([-y])
                elif l is None: cl += [[-y, r], [y, -r]]
                elif r is None: cl += [[-y, l], [y, -l]]
                else: cl += [[-y, l, r], [-y, -l, -r], [y, -l, r], [y, l, -r]]
    for t in range(t0, T - p + 1):
        a, b = X[t, col], X[t + p, col]
        cl += [[-a, b], [a, -b]]
    cl.append([X[0, i] for i in range(-A, A + 1) if (0, i) in X])  # nonzero seed
    return cl, X

def sim(seed, A, T, rule=30):
    row = {i: 1 for i in range(-A, A + 1) if (seed >> (i + A)) & 1}
    cols = []
    for t in range(T + 1):
        cols.append(row.get(0, 0))
        nxt = {}
        for i in range(min(row, default=0) - 1, max(row, default=0) + 2):
            l, c, r = row.get(i - 1, 0), row.get(i, 0), row.get(i + 1, 0)
            nxt[i] = (l ^ (c | r)) if rule == 30 else (l ^ r)
        row = {i: v for i, v in nxt.items() if v}
    return cols

if __name__ == "__main__":
    A, T, t0, P = map(int, sys.argv[1:5]); rule = int(sys.argv[5]) if len(sys.argv) > 5 else 30
    for p in range(1, P + 1):
        cl, X = build(A, T, p, t0, rule=rule)
        s = Cadical153(bootstrap_with=cl); t = time.time()
        r = s.solve()
        msg = f"A={A} T={T} t0={t0} p={p}: {'SAT' if r else 'UNSAT'} ({time.time()-t:.1f}s, {len(cl)} clauses)"
        if r:
            m = set(v for v in s.get_model() if v > 0)
            seed = sum(1 << (i + A) for i in range(-A, A + 1) if X[0, i] in m)
            cols = sim(seed, A, T, rule)
            ok = all(cols[t] == cols[t + p] for t in range(t0, T - p + 1))
            msg += f" seed={seed} verified={ok}"
        print(msg, flush=True)
