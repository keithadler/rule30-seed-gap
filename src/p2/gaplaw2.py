"""Counting law with exact counts for limited width: predicted horizon = first T with
(N_w,ph0(T/2) + N_w,ph1(T/2)) * 2^-(T-w) < 1, N_w,ph(n) = words e of length n from right halves of width <= w."""
import math, csv, glob, re
obs = {int(r['w']): int(r['longest_gap']) for r in csv.DictReader(open('../../results/gap_period2_exact.csv'))}
for w in (30, 38, 46, 54):
    C = []
    for ph in (0, 1):
        t = open(f'../../results/p2/gaplaw/w{w}_ph{ph}.txt').read().split()
        C.append({int(a): int(b) for a, b in (x.split(':') for x in t[2:])})
    nmax = max(C[0])
    out = []
    for T in range(w, 2 * nmax + 1):
        n = T / 2; lo = math.floor(n); hi = math.ceil(n)
        tot = sum(math.sqrt(c[lo] * c[hi]) for c in C)
        out.append((T, tot * 2.0 ** -(T - w)))
    T0 = next((T for T, a in out if a < 1), None)
    print(f"w={w}: words at n={nmax}: {C[0][nmax]} + {C[1][nmax]}; predicted gap {T0 - w if T0 else '>' + str(2*nmax-w)}, measured {obs[w]}")
    print("   expected survivors by extra step:", ' '.join(f"{a:.2f}" for T, a in out if T >= w)[:200])
