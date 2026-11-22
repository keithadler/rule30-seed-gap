import sys, random
N = int(sys.argv[1]); S = int(sys.argv[2]); random.seed(5)
ks = (5, 8, 10, 12, 14, 16, 18, 20)
seen = {k: set() for k in ks}; ev = 0; skipped = 0
marks = {S // 16, S // 4, S}
for n in range(1, S + 1):
    row = random.getrandbits(random.choice([8, 16, 30, 40])) | 1; rows = []
    for t in range(N):
        rows.append(row)
        row = ((row << 1) | (t & 1)) ^ (row | (row >> 1))
    ones = [t for t in range(600, N, 2) if rows[t] & 1]
    if any(b - a == 4 for a, b in zip(ones, ones[1:])): skipped += 1
    else:
        ev += len(ones)
        for t in ones:
            w = rows[t]
            for k in ks: seen[k].add(w & ((1 << k) - 1))
    if n in marks:
        print(f"seeds {n:4d} (gap-2 seeds left out: {skipped}) events {ev:8d} |", " ".join(f"k={k}:{len(seen[k])}" for k in ks), flush=True)
