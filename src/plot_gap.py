"""Draw results/gap_chart.png from results/gap_period2_exact.csv.  Needs matplotlib.
usage (from the repo root): python src/plot_gap.py"""
import csv
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

rows = [(int(r["w"]), int(r["longest_gap"])) for r in csv.DictReader(open("results/gap_period2_exact.csv"))]
ws = [w for w, _ in rows]; gaps = [g for _, g in rows]
wmax = max(ws)
BG, FG, GRID = "#10141f", "#e6e8ee", "#2a3040"
fig, ax = plt.subplots(figsize=(10, 6), dpi=160)
fig.patch.set_facecolor(BG); ax.set_facecolor(BG)
ax.plot([0, wmax], [0, wmax], "--", color="#e5484d", lw=2, label="if the continuation were random-like: gap about w")
ax.plot(ws, gaps, "-o", color="#3ddc97", lw=2, ms=4, label=f"longest gap (exact, w ≤ {wmax})")
peak = max(rows, key=lambda r: r[1])
ax.annotate(f"largest: {peak[1]} at w = {peak[0]}", xy=peak, xytext=(peak[0] + 9, peak[1] + 3), color="#3ddc97",
            arrowprops=dict(arrowstyle="-", color="#3ddc97", lw=1))
late = [g for w, g in rows if w >= 57]
if late:
    ax.annotate(f"{min(late)} to {max(late)} for w = 57 to {wmax}", xy=(wmax - 12, max(late)), xytext=(wmax - 30, max(late) + 12),
                color="#3ddc97", arrowprops=dict(arrowstyle="-", color="#3ddc97", lw=1))
ax.set_xlim(2, wmax); ax.set_ylim(0, wmax + 2)
ax.set_xlabel("seed half-width w", color=FG, fontsize=13)
ax.set_ylabel("steps the center column keeps alternating past the edge", color=FG, fontsize=11)
ax.set_title("Rule 30: a finite seed can't follow an alternating center column for long past its edge", color=FG, fontsize=13, loc="left")
ax.tick_params(colors=FG); ax.grid(color=GRID, lw=0.8)
for s in ax.spines.values(): s.set_color(GRID)
leg = ax.legend(loc="upper left", facecolor="#161c2b", edgecolor=GRID, fontsize=11)
for t in leg.get_texts(): t.set_color(FG)
fig.text(0.01, 0.01, f"Numerical evidence, not a proof. Exact (SAT) to w={wmax}, brute-force checked to w=38. Period-2 target.",
         color="#8a90a0", fontsize=9)
fig.tight_layout(rect=(0, 0.03, 1, 1))
fig.savefig("results/gap_chart.png", facecolor=BG)
