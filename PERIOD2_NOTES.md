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

## 5. What that forces on the left

`src/p2/forced.py` computes the unique left half that keeps the center alternating for a given `e`.

* **`e` = all gaps 5** forces a left half that is spatially periodic with period **155**, with zero runs of at most 6. This is one of the Rule 30 backgrounds with an alternating site (item 7 of `OPEN_QUESTIONS.md`). So an alternating center column is a column inside that background.
* **One 3 among the 5s** (after eight 5s): the forced left half follows the 155 background up to depth 86, departs at depth 87, and shows no period up to 200 in the next 699 cells.

## 6. Why this did not become a proof

* A finite seed cannot stay in the pure background: Jen's theorem (see `CREDITS.md`) allows at most one eventually periodic column, and here column 1 would be a second. So the 3s must keep arriving. That is the only thing proved about them.
* Each 3 changes the required left half everywhere deeper than it can reach. The left half a seed needs is therefore a chaotic function of when the 3s arrive, and those times are produced by the chaotic part of the pattern.
* A proof along this line has to show that those arrival times never keep matching a finite left half. I found nothing that controls them. It is the same kind of statement as Problem 1 itself.

Other routes tried, each stopped for a stated reason:

* **Forced cells deep on the left** that would contradict a finite seed. Only shallow ones exist (the table in section 1). Since the one-sided gap is unbounded, no bounded-window argument on the left alone can work.
* **Left diagonals.** For any finite seed each diagonal parallel to the left edge is eventually periodic with period a power of 2 (from `D_d(t+1) = D_{d-2}(t) XOR (D_{d-1}(t) OR D_d(t))`). But column -1 meets each diagonal once, at the diagonal's first cell.
* **Right diagonals.** They are exactly periodic (`G_d(t+1) = G_d(t) XOR (G_{d-1}(t) OR G_{d-2}(t))`), which forces `x_{t-mP}(-mP) = c(t)` when `P` is the period of the diagonal through the center at time `t`. A contradiction would need `P < (t - A)/2`, and the periods grow much faster than that.

## 7. What might be worth doing with this

* **Describe the right-side language exactly.** Is "5s with isolated 3s, at least three 5s between" the whole long-run language apart from the gap-2 behaviour? Is its growth exponential or slower?
* **Explain the regularity.** Why does the right half-plane settle next to an alternating column, when Rule 30 is chaotic elsewhere?
* **Check a prediction.** If the long-run language has positive but small entropy, the gap in the README's table should grow linearly with a small slope rather than logarithmically. Widths to 56 cannot tell these apart.
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
cd lean && lake build Period2                                  # Lean 4.36.0, core only
```
