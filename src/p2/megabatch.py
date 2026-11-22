"""All right halves of width <= r (cells 1..r), both phases, forced left half to depth N. Usage: megabatch.py r N [procs]"""
import sys
from multiprocessing import Pool
from megacheck import forced_left, runs
r, N = int(sys.argv[1]), int(sys.argv[2]); procs = int(sys.argv[3]) if len(sys.argv) > 3 else 3
def job(R):
    out = []
    for ph in (0, 1):
        L = forced_left(R, ph, N); last, rec, hist = runs(L)
        out.append((R, ph, last, rec[-1][1], rec[-1][0], rec, hist))
    return out
if __name__ == "__main__":
    minlast = N; worst = (0,); hist = {}; recbydepth = {}
    with Pool(procs) as p:
        for res in p.imap_unordered(job, range(1 << r), chunksize=64):
            for R, ph, last, g, at, rec, h in res:
                minlast = min(minlast, last)
                if g > worst[0]: worst = (g, at, R, ph)
                for k, v in h.items(): hist[k] = hist.get(k, 0) + v
                for a, gg in rec:                     # longest run by depth decade
                    d = len(str(a)); recbydepth[d] = max(recbydepth.get(d, 0), gg)
    print(f"right halves of width <= {r}: {1 << r} x 2 phases, depth {N}")
    print(f"smallest 'last one' over all of them: {minlast}")
    print(f"longest zero run: {worst[0]} after depth {worst[1]} (R={worst[2]:b}, cell 1 last; ph={worst[3]})")
    print("longest run starting at a depth with d digits:", ' '.join(f"{d}:{g}" for d, g in sorted(recbydepth.items())))
    print("run histogram:", ' '.join(f"{g}:{n}" for g, n in sorted(hist.items())))
