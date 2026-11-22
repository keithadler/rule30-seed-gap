"""Forced left half L = Lambda(e) for phase 0 (center column 0,1,0,1,...): e(s) = column 1 at time 2s.
x_t(-1) must be 1 at odd t and equal not e(t/2) at even t; each new left cell is fixed by that."""
def forced(e):
    T = 2 * len(e) - 1            # times 0..T-1 decided -> L(1..T)
    tri = [[0] * (T + 2) for _ in range(T + 2)]; L = []
    for m in range(T):
        want = 1 if m & 1 else 1 - e[m // 2]
        for b in (0, 1):
            tri[0][m] = b
            for t in range(1, m + 1):
                j = m - t
                r = tri[t - 1][j - 1] if j >= 1 else ((t - 1) & 1)
                tri[t][j] = tri[t - 1][j + 1] ^ (tri[t - 1][j] | r)
            if tri[m][0] == want: break
        else: raise AssertionError
        L.append(b)
    return L
if __name__ == "__main__":
    import sys
    ws = [l.strip() for l in open(sys.argv[1]) if l[0] in '01']
    best = {}
    for w in ws:
        L = forced([int(ch) for ch in w]); n = len(L)
        for A in range(0, n):
            if A > 0 and L[A - 1] == 0: continue
            g = 0
            while A + g < n and L[A + g] == 0: g += 1
            if A + g == n: continue          # run hits the end of the window: unknown
            if g > best.get(A, (-1,))[0]: best[A] = (g, w)
    print("A:maxrun (words from right-side language, right width unconstrained)")
    print(' '.join(f"{A}:{best[A][0]}" for A in sorted(best)))
