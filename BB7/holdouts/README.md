# BB7/holdouts: five BB(7) holdouts that never halt

Five 7-state machines from the bbchallenge BB(7) holdout list, each proved in Coq **never to halt** from the blank
tape (`Theorem nonhalt : ~ halts tm c0`), with no axioms (`Print Assumptions` reports "Closed under the global
context"). None of them is a record candidate; deciding them removes five machines from the holdout list.

| machine | verdict | community status (2026-10-29) | proof |
|---|---|---|---|
| `1RB1LD_1RC0RF_0LA0RA_0LA0LE_1LA0LG_0LA---_1RD1LG` (16582) | never halts | holdout, undecided | [`BB7_16582_1RB1LD.v`](verify/BB7_16582_1RB1LD.v) |
| `1RB0RC_1RC0RA_1LD0LB_1LE0LA_0LF---_1RC0LG_1LF1LA` (N2) | never halts | holdout, undecided | [`BB7_N2_1RB0RC.v`](verify/BB7_N2_1RB0RC.v) |
| `1RB1RE_1LC0RA_1RF0RD_1LC0LE_1LD0LC_1RG0RE_0RB---` (N2m) | never halts | holdout, undecided | [`BB7_N2m_1RB1RE.v`](verify/BB7_N2m_1RB1RE.v) |
| `1RB1RE_1RC1RA_0LD1LE_1RE1LE_0RG0RF_---0LG_1LC1RA` (H1) | never halts | holdout, undecided | [`BB7_H1_1RB1RE.v`](verify/BB7_H1_1RB1RE.v) |
| `1RB1RF_0LC1LD_1RD1LD_0RE0RG_1LB1RF_1RA1RD_---0LE` (H2) | never halts | holdout, undecided | [`BB7_H2_1RB1RF.v`](verify/BB7_H2_1RB1RF.v) |

**Community status.** All five strings appear verbatim, in this form, in the latest public bbchallenge holdout list,
`undecided_06.06.2026_16,949,557.txt.gz` (Phase 2 Stage 7, first step), lines 11,438,768 / 6,924,647 / 15,412,813 /
15,678,661 / 15,774,786. None has a page on the bbchallenge wiki, and we found no other record of them being decided.
The wiki lists one later step (Andrew Ducharme, FAR RWL_mod, 16,949,557 → 15,743,264) whose holdout list is not yet
public, so we could not check that step; if it removed any of these machines, that decision came first. Our five resisted
the generic deciders we tried (n-gram CPS, CTL variants); RWL_mod was not among them.

## The arguments

**16582** `1RB1LD_1RC0RF_0LA0RA_0LA0LE_1LA0LG_0LA---_1RD1LG`. Two configuration families, in plain binary,
carry a counter x, an accumulator j and a stage counter k (or m):
β = `A> 00 (100)^x 1010 (100)^j 1010 (110)^k 10100 …` and γ = `A> 00 (100)^x 1010 (100)^j 10 (100)^m 00100 …`.
Four rules, proved for all parameter values, take each member of the families to another member: β(x, j, k+1) →
β(2x+3, j+2, k), β(x, j, 0) → γ(2x+3, 0, j+1), and the same two for γ. Each round sweeps right over the x blocks,
takes one unit from the stage counter and "bounces" the blocks back, two for each one consumed. The blank tape
reaches γ(61, 0, 3) after 11,331 steps. Since every family member has a successor that is again a family member,
the machine never halts. (It grows fast: the number of binary digits of x roughly quadruples per super-step.)

**N2** `1RB0RC_1RC0RA_1LD0LB_1LE0LA_0LF---_1RC0LG_1LF1LA`. The tape is read in 2-cell blocks as a list of segments
S = (01)^p (10)^q separated by `11`, plus an accumulator (x, y) next to the head. Nine segment-level rules (counting
down x, borrowing from the nearest segment that is not (1,1), and rebuilding the list when every segment is used up)
are proved for all parameter values. The invariant is a parity condition: either every p, q, x, y is odd, or x is even
and the leftmost segment is (even, odd) with all others (odd, odd). Every rule keeps this invariant. The
configurations that no rule covers, which are where the halt could happen, all break it. The blank tape reaches a valid
configuration after 520 steps. Without the parity condition, random segment configurations do halt, so the invariant
is needed.

**N2m** `1RB1RE_1LC0RA_1RF0RD_1LC0LE_1LD0LC_1RG0RE_0RB---`. After 4 steps it is in state E on a blank tape. From there
it is N2 mirrored left-to-right with its states renamed (A→G, B→F, C→C, D→B, E→A, F→D, G→E). The proof derives
the result from N2's proof with busycoq's `flip_halts` and `perm_nonhalt` lemmas. (N2 and N2m are separate
entries in the holdout list because they start differently.)

**H1** `1RB1RE_1RC1RA_0LD1LE_1RE1LE_0RG0RF_---0LG_1LC1RA`. At each left-end event the tape is a list of digits, a
digit d being the run (10)^d, with a single extra 0 between digits. There are five head forms. Nine macro rules,
proved for all digit lists, describe the run. The first digit counts down while an accumulator grows. When a zero
digit is reached, the machine borrows: it refills the run of zero digits with 1s and moves the rest of the
accumulator into the next nonzero digit. When the list is empty, it is rebuilt from the accumulator. A borrow can
fail only if the accumulator is too small for the run of zeros it must refill. The invariant prevents this: for
every run of z ≥ 1 zero digits followed by a nonzero digit, z + 2 ≤ (the sum of the digits before the run) + a
constant that depends on the form. Every rule keeps it. The blank tape reaches a valid configuration after 29 steps.

**H2** `1RB1RF_0LC1LD_1RD1LD_0RE0RG_1LB1RF_1RA1RD_---0LE`. This is H1 with its states renamed (A→F, B→A, C→B, D→C,
E→D, F→G, G→E) but a different start: it starts in H1's state B on a blank tape. After 19 steps it is in H1's form D2
with digit list [1], which satisfies H1's invariant. The proof file is H1's proof with the renamed table and a new
start lemma. H1's rules and invariant go through unchanged.

## Checking

The proofs use busycoq (commit `bd2e36f`, Coq 8.20.1) and the same 7-state setup as [`../verify/`](../verify/)
(`BB72.v`, `Individual72.v`, byte-identical copies; `c0` is the blank tape in state A). A reviewer only needs to
confirm each declared machine string. [`verify/check.py`](verify/check.py) compiles the files and checks the rest:

- the `tm` table equals the string in the file's `(* machine: … *)` header;
- the theorem is exactly `~ halts tm c0`;
- there are no axioms.

It checks the table and the theorem twice, once as text and once with a Coq probe that `Check`s
`nonhalt : ~ halts tm c0` and each of the 14 transitions by `eq_refl`. It also runs `Print Assumptions`.

    cd BB7/holdouts/verify
    BUSYCOQ=/path/to/busycoq/verify python3 check.py      # busycoq's Individual.vo and Flip.vo must be built

It prints `PASS <file>: <machine> never halts (machine-checked, no axioms)` for each file. The whole run takes about
two minutes. CI job `bb7-holdouts` runs it.

## Credit

The proofs are by Claude agents (Anthropic) working in this project, 2026-09 to 2026-10. They used this project's
symbolic-execution engine for the cell-level lemmas and hand-written Coq for the families, invariants and composition.
The holdout list is the bbchallenge community's (Phase 1 enumeration by mxdys's enumerator
[ccz181078/TM](https://github.com/ccz181078/TM) and contributors; Phase 2 stages as listed on the
[wiki](https://wiki.bbchallenge.org/wiki/BB(7))). The machine 16582 was singled out by this project's
growth ranking of a sample of Phase 1 holdouts. The pairs N2/N2m and H1/H2 came out of this project's scans of
the June 2026 list. Not yet reviewed by the bbchallenge community.
