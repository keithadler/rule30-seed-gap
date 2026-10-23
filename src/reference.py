"""Independent, deliberately simple reference for the gap (no bit tricks, no shared code with gapscan.c).
For every right half R of width r and the chosen target trace, build the seed one left cell at a time (the cell at depth k is chosen so the center cell at time k matches the
target; a wrong choice flips it, because Rule 30 is left-permutive), then report the largest 'gap' = (depth of the first 1 beyond depth r) - r over all nonzero seeds.
Usage: python3 reference.py r [trace]   with trace in {01, 10} (default 01).  Practical up to r = 12 or so."""
import sys
def step(row, lo):
    """one Rule 30 step on a dict-free list; row[i] is the cell at position lo+i; returns (new_row, new_lo) with one extra cell on each side"""
    n = len(row); get = lambda j: row[j] if 0 <= j < n else 0
    return [get(j - 1) ^ (get(j) | get(j + 1)) for j in range(-1, n + 1)], lo - 1
def center_after(seed, lo, t):
    row = list(seed)
    for _ in range(t): row, lo = step(row, lo)
    return row[-lo] if 0 <= -lo < len(row) else 0
def forced_left(R, r, trace, depth):
    right = [(R >> j) & 1 for j in range(r)]              # x_1 .. x_r
    left = []                                              # left[k-1] = x_{-k}
    for k in range(1, depth + 1):
        for guess in (0, 1):
            seed = (left + [guess])[::-1] + [trace(0)] + right    # positions -k .. r
            if center_after(seed, -k, k) == trace(k): left.append(guess); break
    return left
def main():
    r = int(sys.argv[1]); word = sys.argv[2] if len(sys.argv) > 2 else "01"
    trace = lambda t: int(word[t % len(word)])
    depth = 2 * r + 30; best = 0; count = 0
    for R in range(1 << r):
        L = forced_left(R, r, trace, depth)
        if not (R or trace(0) or any(L[:r])): continue                      # zero seed
        gap = next((k + 1 - r for k in range(r, depth) if L[k]), depth - r + 1)
        if gap > best: best, count = gap, 0
        if gap == best: count += 1
    print(f"r={r} trace={word}: longest gap {best} (reached by {count} right halves)")
main()
