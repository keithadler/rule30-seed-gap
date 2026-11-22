# Period 2: how an alternating center column works, and why I could not rule it out

**Status: no proof.** This note records an attempt (Keith Adler, working with Claude, November 2026) to prove that no finite Rule 30 seed has a center column that alternates `0,1,0,1,...` forever. The attempt failed. What it found is a description of the mechanism and one small machine-checked lemma. Nothing here is a claim on Wolfram's prize, and I have not checked the literature for any of it beyond what `CREDITS.md` lists.

Throughout, the center column is `c(t) = t mod 2` (the other phase behaves the same way), `y(t)` is column 1, and `e(s) = y(2s)` is column 1 at even times.

## 1. The problem splits into a left side and a right side

Rule 30 is `x'(i) = x(i-1) XOR (x(i) OR x(i+1))`. Fix column 0 to be `0,1,0,1,...`.

* **The left half-plane evolves on its own**, with column 0 as its boundary. The center column stays alternating exactly when
  * column -1 is 1 at every odd time, and
  * at even times, `y(t) = NOT x_t(-1)`. This puts no condition on the left; it says what column 1 must be.
* **The right half enters only through `e`.** The right half-plane also evolves on its own given column 0, and it produces `e`. One consequence is immediate: `e` never has two ones in a row (`y(2s) = 1` forces `y(2s+1) = 1` and `y(2s+2) = 0`).
* **The first left columns are explicit in `e`.** At times `(2s, 2s+1)`:

  | column | value at time 2s | value at time 2s+1 |
  |---|---|---|
  | -1 | NOT e(s) | 1 |
  | -2 | e(s) | e(s+1) |
  | -3 | NOT e(s+1) | NOT e(s+1) |
  | -4 | 0 | e(s+2) |

  The 0 in the last row is `e(s) AND e(s+1)`, which vanishes because `e` has no two ones in a row.

**Proved in Lean** (`lean/Period2.lean`, core only, axioms: `propext`): `alt_forces_col4`. If the center column reads `0,1,0,1,0` on times `t .. t+4`, then column -4 is 0 at time `t`. This is a structural fact about alternating columns. It does not rule them out.

## 2. The left side alone has no small-gap structure

Drop the right half and keep only the two left conditions plus "no two ones in a row" (`src/p2/onesided.c`).

* **The left halves that survive `A` steps are counted by Fibonacci numbers**: 1, 2, 2, 3, 3, 5, 5, 8, 8, 13, ... for `A = 0, 1, 2, ...` (checked to `A = 56`). Each corresponds to one word `e` with no two ones in a row. An exhaustive search over left halves therefore costs about `1.27^A`, not `2^A`.
* **The one-sided horizon grows like chance.** The first time some condition must fail, over all left halves of width at most `A`:

  | A | 1 | 8 | 16 | 19 | 30 | 43 | 54 |
  |---|---|---|---|---|---|---|---|
  | one-sided horizon | 8 | 18 | 26 | 38 | 45 | 70 | 82 |
  | two-sided horizon (CSV) | - | 15 | 26 | 36 | 39 | 52 | 66 |

  The one-sided horizon is never below the two-sided one, as it must be. Its excess over `A` reaches 27 and 28 at `A = 43` and `54`, and the histogram of excesses at `A = 55, 56` decays geometrically with no cutoff (`results/p2/os_ph*_56.txt`). That is what independent coin-flip checks over `1.27^A` candidates would give.

So the small gaps in the README's table do not come from the left half. They come from the right half.

## 3. The right side is heavily restricted

Which words `e` can some right half produce? (`src/p2/rightlang.c` by brute force to length 13; `src/p2/rightlang_sat.py` with a SAT check per prefix to length 30. The two agree where they overlap.)

| length n | 5 | 10 | 15 | 20 | 25 | 30 |
|---|---|---|---|---|---|---|
| words a right half can produce | 12 | 68 | 251 | 721 | 1,780 | 3,908 |
| words with no two ones in a row | 13 | 144 | 1,597 | 17,711 | 196,418 | 2,178,309 |

* The growth ratio from one length to the next falls from 1.31 at `n = 13` to 1.157 at `n = 30` and is still falling. Whether the growth is exponential with a small base or slower is **not decided** at this length.
* Zeros come in runs of at most 4.
* There is no short list of forbidden patterns: 237 minimal forbidden words up to length 30 (`11`, `00000`, `101001`, `0100101`, `010010001`, ...), with new ones at every length from 9 on.
* The full list of length-30 words is in `results/p2/words30_ph0.txt`.

## 4. In the long run the right side does something very regular

Simulate the right half-plane for a long time with column 0 held at `0,1,0,1,...` (`src/p2/rightsim.py`) and write `e` as the gaps between its ones.

* **Usually the gaps settle to 5s with isolated 3s.** This held for 40 random right halves over 900 double steps, and for finite right halves of width 0, 1, 20 and 40 over 2,500 double steps. After the start-up, between two 3s there were always at least three 5s; three was by far the commonest, and up to 31 were seen. The 3s arrive at irregular times and showed no sign of stopping.
* **There is at least one other stable behaviour.** Nine of the 255 nonzero right halves of width 8 (for example a single 1 at cell 6) give gap 2 forever, that is `e = 1,0,1,0,...`, for the 600 double steps tested.

### The orderly part on the right is a strip four cells wide

Added later the same day (`src/p2/layer.py`: 31 right halves, 20,000 steps each, events after step 600, 64,388 gaps, all of them 3 or 5).

* **There is no deep regular background on the right.** Rows stop repeating with period 10 somewhere between cell 1 and cell 20 (mean 7.6). The 155 background of section 5 is on the left only, where it is forced.
* **Cells 1 to 4 are locked.** At every even time when column 1 is 1, cells 1 to 4 read `1110`.
* **Cell 5 decides the next gap.** If cell 5 is 1 at that time the next gap is 3; if it is 0 the next gap is 5. There was no exception in 64,388 gaps.
* **Rows beside the center are restricted much deeper.** The number of distinct patterns of cells 1 to `k` at those times, for `k = 2 .. 25`:
  1, 1, 1, 2, 2, 3, 3, 5, 8, 13, 18, 30, 48, 79, 119, 185, 282, 428, 624, 927, 1372, 1982, 2826, 4037, out of `2^(k-1)` possible. That is a factor of about 1.45 per cell.
  These are the patterns the runs **visited**, not all the patterns that are possible; see the next heading.
* **The visited counts creep up with more data** (`src/p2/satur.py`, gap-2 runs left out). With 35,239, 147,028 and 595,053 events the counts were 3, 3, 4 at `k = 8`; 18, 18, 21 at `k = 12`; 116, 119, 122 at `k = 16`; 604, 668, 709 at `k = 20`. Cells 1 to 5 took two patterns throughout.

So the 3s are not signals moving through a background. The sequence of 3s and 5s is cell 5 read at certain times, and cell 5 is at the edge of the chaotic part.

### Which rows are possible, as opposed to visited

I had guessed the restriction could be proved from one remark: `x_{t+1}(1) = x_t(0) XOR (x_t(1) OR x_t(2))`, so wherever column 1 is 0 the cell in column 2 is forced. **That does not give the visited counts.** The exact number of possible rows is much larger.

`src/p2/rowlang_sat.py` counts, with one SAT call per prefix, the words `w` of length `k` (first cell 1) for which some right half at time 0 gives `w` in cells 1 to `k` at time `T`, with column 0 alternating throughout:

| look-back T | k=4 | k=6 | k=8 | k=10 | k=12 | k=14 |
|---|---|---|---|---|---|---|
| 6 | 4 | 10 | 29 | 90 | 288 | 921 |
| 12 | 4 | 10 | 28 | 83 | 241 | 709 |
| 24 | 4 | 10 | 26 | 74 | 195 | 541 |
| 48 | 4 | 9 | 23 | 63 | 165 | 450 |
| 96 | 4 | 7 | 21 | 55 | 135 | not run |
| visited (595,053 events) | 1 | 2 | 4 | 9 | 21 | 51 |
| all words with first cell 1 | 8 | 32 | 128 | 512 | 2,048 | 8,192 |

* The possible set is a real restriction (450 of 8,192 at `k = 14`, `T = 48`) and it shrinks as `T` grows, slowly: at `k = 12` it goes 288, 241, 195, 165, 135 as `T` doubles from 6 to 96.
* At `T = 48` it is still about nine times the visited set at `k = 14`, and cells 1 to 4 can still take four patterns, not one.
* So either the possible set keeps shrinking toward the visited one at look-backs far beyond 96, or the visited rows are only the typical ones and rarer rows stay possible forever. The creep in the visited counts points to the second. **This is not decided.**
* `src/p2/rowbound.py` gives the same kind of count without SAT, from an automaton that reads the row left to right and keeps only the last `tau` steps. It is an upper bound on the possible set and agrees with the SAT counts where they overlap (for `tau = T = 6` it gives 92 and 290 at `k = 10, 12` against 90 and 288).

What is established is therefore weaker than I first said: the rows beside an alternating column are restricted, by an amount that can be computed exactly for any fixed look-back, and the runs visit far fewer rows than that. The rate of 1.45 per cell is a measurement of visited rows, not a bound.

### The right side does not forget its starting cells

`src/p2/merge.py` compares column 1 for a given right half with column 1 for the empty right half. For 65 right halves (widths 1 to 40) over 6,000 steps, none merged: column 1 still differed in the last 20 steps in every case, at 2,031 to 3,675 of the 6,000 steps. So the question does not reduce to one fixed sequence.

## 5. What that forces on the left

`src/p2/forced.py` computes the unique left half that keeps the center alternating for a given `e`.

* **`e` = all gaps 5** forces a left half that is spatially periodic with period **155**, with zero runs of at most 6. This is one of the Rule 30 backgrounds with an alternating site (item 7 of `OPEN_QUESTIONS.md`). So an alternating center column is a column inside that background.
* **One 3 among the 5s** (after eight 5s): the forced left half follows the 155 background up to depth 86, departs at depth 87, and shows no period up to 200 in the next 699 cells.

### Checking small right halves against deep left halves

For a fixed right half the left half is forced, and it can be computed column by column with big integers (`src/p2/megacheck.py`). So a search for a counterexample costs `2^(right width)`, not `2^(left + right)`: a seed with a given right half exists only if its forced left half is zero beyond some depth.

* **Empty right half, depth 1,000,000, both phases**: the last one is at depth 999,999. The longest zero run is 22 (phase 0, after depth 564,972) and 20 (phase 1).
* **Every right half of width up to 16** (65,536, both phases), **depth 10,000** (`src/p2/megabatch.py`): the smallest depth of the last one is 9,986. The longest zero run is 27, after depth 8,300.
* The number of zero runs halves with each extra cell of length (about 650 million runs counted), and the longest run starting at a depth of 1, 2, 3, 4 digits is 8, 17, 25, 27. Halving at each step is what coin flips would give.
* Checked against the slower method of this section on 30 random right halves, and against the README's table for widths 2 to 12.

So no seed with right width at most 16 and left width at most 9,986 has an alternating center column forever. This is a bound from computation, not a proof. Outputs are in `results/p2/mega_*.txt`.

## 6. Why this did not become a proof

* A finite seed cannot stay in the pure background: Jen's theorem (see `CREDITS.md`) allows at most one eventually periodic column, and here column 1 would be a second. So the 3s must keep arriving. That is the only thing proved about them.
* Each 3 changes the required left half everywhere deeper than it can reach. The left half a seed needs is therefore a chaotic function of when the 3s arrive, and those times are produced by the chaotic part of the pattern.
* A proof along this line has to show that those arrival times never keep matching a finite left half. I found nothing that controls them. It is the same kind of statement as Problem 1 itself.

Other routes tried, each stopped for a stated reason:

* **Forced cells deep on the left** that would contradict a finite seed. Only shallow ones exist (the table in section 1). Since the one-sided gap is unbounded, no bounded-window argument on the left alone can work.
* **Left diagonals.** For any finite seed each diagonal parallel to the left edge is eventually periodic with period a power of 2 (from `D_d(t+1) = D_{d-2}(t) XOR (D_{d-1}(t) OR D_d(t))`). But column -1 meets each diagonal once, at the diagonal's first cell.
* **Right diagonals.** They are exactly periodic (`G_d(t+1) = G_d(t) XOR (G_{d-1}(t) OR G_{d-2}(t))`), which forces `x_{t-mP}(-mP) = c(t)` when `P` is the period of the diagonal through the center at time `t`. A contradiction would need `P < (t - A)/2`, and the periods grow much faster than that.

## 6a. One thing that can be proved: e cannot repeat early

Added later the same day, from a direct attack on the gap described under Kopra's theorem below.

**Lemma.** Let the seed's leftmost one be at `-w`, and let `e` be as above. For all `0 <= i < i2`: if `e[i .. i+m) = e[i2 .. i2+m)` then `2m < w + 2*i2`.

**Proof.** The cell at depth `k` at time 0 depends only on `e(0), ..., e(floor((k-1)/2))` (the sideways formulas of section 1). So the left halves at times `2i` and `2*i2` agree at depths 1 to `2m`. At time `2i` the left half is zero beyond depth `w + 2i`. At time `2*i2` it has a one at depth `w + 2*i2`, because the left edge moves one cell per step, and that is deeper than `w + 2i`. If `2m >= w + 2*i2`, that one would have to be a zero.

* It follows that `e` is not eventually periodic. For this case that is an elementary proof of what section 6 took from Jen's theorem.
* A block of `e` that repeats with period `j` from position `i` is shorter than `i + 2j + w/2`.
* Checked on every seed in `[-7, 7]` inside its surviving window (`src/p2/repeat_check.py 7`): 1,616 repeating pairs, no violation.
* **Proved in Lean** (`lean/Repeat.lean`, core only, axioms: `propext`, `Quot.sound`): `repeat_bound_alt` is the lemma as stated here. It rests on `repeat_bound`, which holds for any Rule 30 evolution, with no assumption on the center column: if columns 0 and -1 read the same for `n` steps from time `a` as from a later time `b`, then `n < W + b`, where `-W` is the seed's leftmost one. `left_det` is the step that two columns over `n` steps fix the row to depth `n` on the left.
* **Two corollaries, also in `lean/Repeat.lean`.** `two_columns_never_periodic`: for any finite nonzero row, columns 0 and -1 are never both eventually periodic with a common period. For Rule 30 this is the two-adjacent-columns theorem of Jen and Kopra; `seed0_two_columns` states it for the single-cell pattern. `alt_e_never_periodic`: if the center column alternates forever, column -1 read at even times is not eventually periodic. So section 6 no longer needs to cite Jen for that step.
* Because `e` usually starts with a long stretch of gaps 2, 5, 2, 5, ..., the lemma gives a lower bound on the left width for 887 of the 1,024 right halves of width up to 10, above 100 for 247 of them and up to 532 (`src/p2/repeat.py 10 300`).

**Why it does not finish the job.** The proof uses one known one in the later left half, the edge at depth `w + 2*i2`. That depth grows with `i2`, so the lemma says nothing about repetitions late in the run. Closing the gap would need a one within a bounded distance beyond depth `w + 2i`, that is, a bound on zero runs inside the pattern, and nothing bounds those.

I also looked for cells of the forced left half-plane that are a single bit of `e` (`src/p2/cells.py`). They exist only in columns -1 to -6; from column -7 to column -30 there are none, with or without restricting `e` to what the right side can produce.

## Prior work on this case

Read for this note: the HTML version of Condrey's paper and the arXiv preprint 2202.13809 of Kopra (see `CREDITS.md`). I did not read the journal version of Kopra's paper or Jen's papers.

* **Condrey states this case as open**: the next unresolved case is eventual period two, and the paper makes no claim about it. Its acknowledgments credit Jarkko Kari with suggesting the exclusion of nonconstant periodic traces as the next step. Its period-1 proof rests on a left half that is the same at every step (an alternating tail), and it gives no such object for period 2. It proves only the lower bound `H(2,w) >= w`.
* **Condrey's `H(p,w)` is for eventually periodic traces.** Everything in this note and in the README's table requires the alternation from time 0, so the numbers here are lower bounds for his quantity, not the same thing.
* **Kopra's theorem needs two full adjacent columns.** If two adjacent columns are eventually periodic, left permutivity makes every column to their left eventually periodic, which contradicts the left edge moving at speed 1. An alternating center column gives one full column and half of the next (column -1 at odd times, section 1). The missing half is `e`, and the argument does not go through without it. Kopra's preprint also notes that the class of rules his method covers contains Rule 90, where a single column can be periodic, so any single-column result needs something specific to Rule 30.
* I found nothing in either paper about the 155 background, the right-side language, or the split in section 1. I have not searched further.

## 7. What might be worth doing with this

* **Describe the right-side language exactly.** Is "5s with isolated 3s, at least three 5s between" the whole long-run language apart from the gap-2 behaviour? Is its growth exponential or slower?
* **Decide possible against visited.** Section 4 found that the runs visit far fewer rows than are possible at look-back 96. Does the possible set shrink to the visited one as the look-back grows, or do the rare rows stay possible? If cells 1 to 4 are ever forced to `1110`, at what look-back?
* **Check a prediction.** If the long-run language has positive but small entropy, the gap in the README's table should grow linearly with a small slope rather than logarithmically. Widths to 82 cannot tell these apart (the gap is 10 to 15 from width 57 to 82).
* **Check whether any of this is known.** I have not searched for it.

## Reproduce

```bash
cc -O3 -o onesided src/p2/onesided.c && ./onesided 40 0 1      # width, phase, use the no-two-ones rule
```

```bash
cc -O3 -o rightlang src/p2/rightlang.c && ./rightlang 25 0     # right-half cells, phase: word counts to length 13
```

```bash
python3 -m venv .venv && .venv/bin/pip install python-sat numpy
```

```bash
.venv/bin/python src/p2/rightlang_sat.py 30 0                  # word counts to length 30 (a few minutes)
```

```bash
cd src/p2 && ../../.venv/bin/python rightsim.py 1 900 40       # seed, double steps, runs: gap sequences from random right halves
```

```bash
cd src/p2 && python3 megacheck.py 0 100000                      # right half as bits (0 = empty), depth: forced left half and its zero runs
```

```bash
cd src/p2 && python3 megabatch.py 10 2000 3                     # right width, depth, processes: every right half up to that width
```

```bash
cd src/p2 && python3 layer.py 20000                              # steps: the strip beside the center and the row counts
```

```bash
cd src/p2 && ../../.venv/bin/python rowlang_sat.py 48 14           # look-back, longest word: exact count of possible rows
```

```bash
cd src/p2 && python3 rowbound.py 6 22                            # look-back, longest word: automaton upper bound
```

```bash
cd src/p2 && python3 satur.py 10000 640                          # steps, right halves: visited counts at three data sizes
```

```bash
cd src/p2 && python3 merge.py 6000 60                            # steps, random right halves: merging test against the empty right half
```

```bash
cd src/p2 && python3 repeat_check.py 7 && python3 repeat.py 10 300   # the repetition lemma: check on all small seeds, and its strength
```

```bash
cd src/p2 && python3 cells.py 16 30 8                            # word length, columns, times: which left cells are single bits of e
```

```bash
cd lean && lake build Period2 Repeat                           # Lean 4.36.0, core only
```
