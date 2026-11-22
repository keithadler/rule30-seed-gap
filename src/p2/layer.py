import sys, random
from collections import defaultdict, Counter
N = int(sys.argv[1]); random.seed(3)
seeds = [0] + [random.getrandbits(30) | 1 for _ in range(30)]
data = []   # (window bits at time of a one in e, next gap)
allrows = []
for R in seeds:
    row = R; rows = []
    for t in range(N):
        rows.append(row)
        row = ((row << 1) | (t & 1)) ^ (row | (row >> 1))
    ones = [t for t in range(600, N, 2) if rows[t] & 1]
    for a, b in zip(ones, ones[1:]):
        data.append((rows[a] & ((1 << 40) - 1), (b - a) // 2))
print("events", len(data), "gap counts", sorted(Counter(g for _, g in data).items()))
for k in range(2, 26):
    m = (1 << k) - 1
    d = defaultdict(Counter)
    for w, g in data: d[w & m][g] += 1
    amb = sum(sum(c.values()) - max(c.values()) for c in d.values())
    print(f"k={k:2d} distinct windows {len(d):6d}  possible {2**(k-1):9d}  events not decided by window {amb}")
