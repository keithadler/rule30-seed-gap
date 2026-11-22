"""Simulate the right half-plane (cells 1..W) with column 0 = t&1 and record e(s) = x_{2s}(1)."""
import numpy as np, sys
def run(a, S):
    e = np.zeros(S, dtype=np.uint8)
    for s in range(S):
        e[s] = a[0]
        for c in (0, 1):
            l = np.empty_like(a); l[0] = c; l[1:] = a[:-1]
            r = np.empty_like(a); r[-1] = 0; r[:-1] = a[1:]
            a = l ^ (a | r)
    return e
if __name__ == "__main__":
    rng = np.random.default_rng(int(sys.argv[1])); S = int(sys.argv[2]); trials = int(sys.argv[3])
    W = 2 * S + 50
    facs = {n: set() for n in (12, 16, 20, 24)}
    for k in range(trials):
        e = run(rng.integers(0, 2, W, dtype=np.uint8), S)
        st = ''.join(map(str, e))
        if k < 3:
            g = [len(x) + 1 for x in st.strip('0').split('1')[1:-1]]
            print(''.join(map(str, g)))
        for n in facs:
            for i in range(S // 3, S - n): facs[n].add(st[i:i + n])
    print({n: len(v) for n, v in facs.items()})
