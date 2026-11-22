"""Upper bound on the rows beside an alternating center column.
A word w = cells 1..k at an even time T is kept only if columns 0..k+1 can be filled in on
times T-tau..T-1 (column 0 alternating) so that Rule 30 holds at cells 1..k on those steps.
That is a necessary condition, checked exactly with an automaton reading w left to right.
usage: rowbound.py tau kmax"""
import sys
tau = int(sys.argv[1]); K = int(sys.argv[2])
M = 1 << tau
# column value as int: bit i = value at time T-tau+i.  column 0: (T-tau+i) mod 2, T even
C0 = sum((((i - tau) & 1) << i) for i in range(tau))
top = tau - 1
low = M // 2 - 1
def ok(P, A, B):
    # inner steps: A[i+1] = P[i] ^ (A[i] | B[i]) for i < tau-1 ; returns final letter or -1
    v = P ^ (A | B)
    if (v & low) != (A >> 1): return -1
    return (v >> top) & 1
# succ[(P,A)][w] = bitmask over B of allowed next columns (new state (A,B))
succ = {}
def get(P, A):
    key = P * M + A
    if key not in succ:
        m = [0, 0]
        for B in range(M):
            w = ok(P, A, B)
            if w >= 0: m[w] |= 1 << B
        succ[key] = m
    return succ[key]
# DFA state: tuple over A of bitmask of B  (set of NFA states (A,B)), stored as dict A->mask
start = {}
for A in range(M): start[A] = 0
st = {}
for A in range(M):           # initial NFA states (C0, A); read w1
    pass
def step(S, w):              # S: dict P -> mask of A
    out = {}
    for P, mask in S.items():
        A = 0; mm = mask
        while mm:
            if mm & 1:
                b = get(P, A)[w]
                if b: out[A] = out.get(A, 0) | b
            mm >>= 1; A += 1
    return out
def freeze(S): return tuple(sorted(S.items()))
S0 = {C0: (1 << M) - 1}
cur = {freeze(step(S0, 1)): 1}      # cell 1 must be 1
cur = {s: c for s, c in cur.items() if s}
ids = set(cur)
counts = [sum(cur.values())]
for k in range(2, K + 1):
    nxt = {}
    for s, c in cur.items():
        S = dict(s)
        for w in (0, 1):
            t = freeze(step(S, w))
            if t: nxt[t] = nxt.get(t, 0) + c
    cur = nxt; ids |= set(cur)
    counts.append(sum(cur.values()))
print("tau", tau, "automaton states seen", len(ids))
print("counts k=1..:", *counts)
print("ratio at end: %.4f" % (counts[-1] / counts[-2]))
