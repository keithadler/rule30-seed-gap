import random, sys
N = int(sys.argv[1]); K = int(sys.argv[2]); ph = 0
def run(R):
    row = R; rows = []
    Y = 0
    for t in range(N):
        Y |= (row & 1) << t
        rows.append(row)
        row = ((row << 1) | ((t + ph) & 1)) ^ (row | (row >> 1))
    return Y, rows
Y0, rows0 = run(0)
random.seed(7)
res = []
tests = [1, 2, 4, 32, 0b1111100010100] + [random.getrandbits(random.choice([8, 16, 24, 40])) | 1 for _ in range(K)]
for R in tests:
    Y, rows = run(R)
    d = Y ^ Y0
    last = d.bit_length()          # first time after which column 1 agrees forever (within N)
    # leftmost differing cell at a few times
    lows = []
    for t in (N // 4, N // 2, N - 1):
        x = rows[t] ^ rows0[t]
        lows.append((x & -x).bit_length() if x else -1)
    res.append((R, last, bin(d).count("1"), lows))
merged = [r for r in res if r[1] < N // 2]
print("N", N, "tested", len(res), "merged before N/2:", len(merged))
print("diff count min", min(r[2] for r in res), "max", max(r[2] for r in res))
for r in res[:12]: print(bin(r[0]), "last diff t", r[1], "diff count", r[2], "leftmost diff cell at N/4,N/2,N", r[3])
ls = sorted(r[1] for r in res); print("last-diff times: min", ls[0], "median", ls[len(ls)//2], "max", ls[-1])
