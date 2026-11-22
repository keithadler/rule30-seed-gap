"""Fixed right half, every left half at once.

Fix the right half R (cells 1,2,...; zero beyond its width) and the center column c(t) = (t+ph)&1.
Rule 30 is left-permutive, so exactly one left half keeps the center on that trace: the forced left half L(1), L(2), ...
A seed with right half R and a finite left half supported in [-A,-1] can follow the trace only until the first
k > A with L(k) = 1 (if its left half is the forced prefix), or fails earlier (if it is not).
So one computation of L to depth N settles every such seed with A below the last 1 found.

Method (Python integers as bit sets):
  rows of the right half-plane, bit i-1 = cell i:   row' = ((row << 1) | c(t)) ^ (row | (row >> 1));  y(t) = cell 1
  columns of the left half-plane, bit t = time t:    col(-1) = (c >> 1) ^ (c | y);  col(-k-1) = (col(-k) >> 1) ^ (col(-k) | col(-k+1))
  L(k) = bit 0 of col(-k).
"""
import sys

def forced_left(R, ph, N):
    """R: int, bit i-1 = cell i. Returns L as a bytes object, L[k-1] = L(k), k = 1..N."""
    row = R; Y = 0
    for t in range(N):
        row &= (1 << (N - t + 1)) - 1          # only cells 1..N-t+1 can still reach column 1 by time N-1
        Y |= (row & 1) << t
        row = ((row << 1) | ((t + ph) & 1)) ^ (row | (row >> 1))
    C = 0
    for t in range(ph ^ 1, N + 1, 2): C |= 1 << t     # bit t = c(t) = (t+ph)&1
    prev = C
    cur = ((C >> 1) ^ (C | Y)) & ((1 << N) - 1)       # column -1, valid for t = 0..N-1
    L = bytearray(N)
    for k in range(1, N + 1):
        L[k - 1] = cur & 1
        nxt = ((cur >> 1) ^ (cur | prev)) & ((1 << (N - k)) - 1)   # column -(k+1), valid for t = 0..N-k-1
        prev, cur = cur, nxt
    return bytes(L)

def runs(L):
    """For each left edge A (A = 0, or L(A) = 1): the zero run after it. Returns (last_one, records, hist)
    records: list of (A, run) each time the run sets a new maximum; hist: run -> count. The final, unfinished run is dropped."""
    N = len(L); ones = [0] + [k + 1 for k in range(N) if L[k]]
    rec = []; best = -1; hist = {}
    for a, b in zip(ones, ones[1:]):
        g = b - a - 1; hist[g] = hist.get(g, 0) + 1
        if g > best: best = g; rec.append((a, g))
    return ones[-1], rec, hist

if __name__ == "__main__":
    R = int(sys.argv[1], 2) if len(sys.argv[1]) and sys.argv[1] != "0" else 0   # right half as a bit string, cell 1 LAST
    N = int(sys.argv[2])
    for ph in (0, 1):
        L = forced_left(R, ph, N); last, rec, hist = runs(L)
        print(f"R={sys.argv[1]} ph={ph} depth={N}: last one at {last}; ones {sum(L)}; longest zero run {rec[-1][1]} after depth {rec[-1][0]}")
        print("  record runs (after depth: run):", ' '.join(f"{a}:{g}" for a, g in rec))
        print("  run histogram:", ' '.join(f"{g}:{n}" for g, n in sorted(hist.items())), flush=True)
