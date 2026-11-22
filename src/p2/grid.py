"""Horizon by left width and right width.
For a right half R the left half is forced.  A seed that keeps the forced cells to depth a and is
zero beyond first goes wrong at time k = depth of the first forced one beyond a (the change moves
right one cell per step).  So  H(a, r) = max over right halves of width <= r, both phases, of that k.
usage: grid.py rmax amax [procs]   ->  writes grid_r<rmax>_a<amax>.txt"""
import sys
from multiprocessing import Pool
from megacheck import forced_left
RM, AM = int(sys.argv[1]), int(sys.argv[2]); procs = int(sys.argv[3]) if len(sys.argv) > 3 else 4
N = AM + 80
ONE = b"\x01"
def job(lohi):
    lo, hi = lohi
    best = [[0] * (AM + 1) for _ in range(RM + 1)]
    over = 0
    for R in range(lo, hi):
        w = R.bit_length(); row = best[w]
        for ph in (0, 1):
            L = forced_left(R, ph, N)
            for a in range(AM + 1):
                i = L.find(ONE, a)
                if i < 0: over += 1; i = N
                if i + 1 > row[a]: row[a] = i + 1
    return best, over
if __name__ == "__main__":
    step = 2048
    jobs = [(lo, min(lo + step, 1 << RM)) for lo in range(0, 1 << RM, step)]
    best = [[0] * (AM + 1) for _ in range(RM + 1)]; over = 0
    with Pool(procs) as p:
        for b, o in p.imap_unordered(job, jobs):
            over += o
            for w in range(RM + 1):
                bw, cw = best[w], b[w]
                for a in range(AM + 1):
                    if cw[a] > bw[a]: bw[a] = cw[a]
    for w in range(1, RM + 1):                 # width <= r
        for a in range(AM + 1): best[w][a] = max(best[w][a], best[w - 1][a])
    with open(f"grid_r{RM}_a{AM}.txt", "w") as f:
        f.write(f"# H(a, r): rows r = 0..{RM} (right width), columns a = 0..{AM} (left width). runs past depth {N}: {over}\n")
        for w in range(RM + 1): f.write(" ".join(map(str, best[w])) + "\n")
    print("done; runs past the window:", over)
