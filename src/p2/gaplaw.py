"""Counting law for the gap. A seed of width w is fixed on the left by the first ~w/2 values of e; after time w every
further step is one yes/no coincidence (odd time: column -1 must be 1; even time: it must be NOT e). If these behave
like coin flips, the number of seeds still alive at time T is about 2 N(T/2) 2^-(T-w), where N(n) is the number of
words e of length n that some right half can produce (exact counts, phase 0, from rightlang_sat.py; doubled for the
two phases). Predicted horizon = first T where that drops below 1. Compare with the measured horizons."""
import math, csv
N = {int(a): int(b) for a, b in (x.split(':') for x in open('../../results/p2/counts48_ph0.txt').read().split()[1:])}
def logN(n):  # interpolate for half-integers; extrapolate with the last ratio
    if n <= 48:
        lo = max(1, math.floor(n)); hi = min(48, lo + 1)
        return math.log2(N[lo]) + (n - lo) * (math.log2(N[hi]) - math.log2(N[lo]))
    return math.log2(N[48]) + (n - 48) * math.log2(N[48] / N[47])
obs = {int(r['w']): int(r['longest_gap']) for r in csv.DictReader(open('../../results/gap_period2_exact.csv'))}
def pred(w):
    T = w
    while 1 + logN(T / 2) - (T - w) >= 0: T += 1
    return T - w
err = []
print(" w  measured  predicted")
for w in sorted(obs):
    p = pred(w); err.append(p - obs[w])
    if w % 4 == 2 or w in (19, 82): print(f"{w:3d} {obs[w]:7d} {p:9d}")
import statistics
print("mean error (predicted - measured):", round(statistics.mean(err), 2), " mean |error|:", round(statistics.mean(map(abs, err)), 2), " worst:", min(err), max(err))
big = [e for w, e in zip(sorted(obs), err) if w >= 29]
print("widths 29..82 only: mean error", round(statistics.mean(big), 2), " mean |error|", round(statistics.mean(map(abs, big)), 2), " worst", min(big), max(big))
print("extrapolated (last growth ratio 1.110 held fixed; an upper guess since the ratio is still falling):", {w: pred(w) for w in (100, 150, 200, 500, 1000)})
