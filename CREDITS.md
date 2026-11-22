# Credits

* **Keith Adler**: project owner and director; would be the human submitter of anything entered for a prize.
* **Claude (Anthropic)**: wrote and ran the code, ran the Lean, and helped analyze results, at Keith's direction. Wolfram's prize rules require naming every contributor, including AI agents.

Prior work this builds on (all credit to their authors; none of this repo's content should be read as superseding them):

* D. L. Condrey, *Finite Configurations Cannot Generate a Constant Trace in Rule 30*, arXiv:2609.09431 (2026): the period-1 result with the sharp horizon, and the statement that eventual periods above 1 are open. `lean/ConstColumn.lean` is an independent re-derivation of the upper bound.
* E. Rowland, *Local Nested Structure in Rule 30*, Complex Systems 16 (2006) 239-258: left-bijectivity, unique rightful histories, period doubling.
* E. Jen, *Aperiodicity in one-dimensional cellular automata*, Physica D 45 (1990): a finite Rule 30 orbit has at most one eventually periodic column.
* J. Kopra, *Rapid left expansivity, a commonality between Wolfram's Rule 30 and powers of p/q*, Theoretical Computer Science 946 (2023) 113668 (citation as given by Condrey; I read the arXiv preprint 2202.13809 by the same author on the same subject, which has a different title): for any nonzero configuration that is zero far to the left, no two adjacent Rule 30 columns are both eventually periodic. The single-column question is stated there as open. `lean/Repeat.lean` proves this for columns 0 and -1 of Rule 30, with an explicit bound, by a direct argument; it is not a formalization of Kopra's proof and does not cover his wider class of rules.
* S. Wolfram, *Announcing the Rule 30 Prizes* (2019), and rule30prize.org.
