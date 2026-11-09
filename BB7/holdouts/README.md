# BB7/holdouts: 131 BB(7) holdouts that never halt

131 7-state machines from the bbchallenge BB(7) holdout list, each proved in Coq **never to halt** from the blank
tape (`Theorem nonhalt : ~ halts tm c0`), with no axioms (`Print Assumptions` reports "Closed under the global
context"). None of them is a record candidate; deciding them removes 131 machines from the holdout list.

- Seven machines with individual arguments (16582, N2, N2m, H1, H2, c01, c02): table and arguments below.
- 124 digit-list machines with one shared proof scheme (2026-11-09):
  [section below](#124-digit-list-machines-2026-11-09).

## Seven machines with individual arguments

| machine | verdict | community status (2026-10-29) | proof |
|---|---|---|---|
| `1RB1LD_1RC0RF_0LA0RA_0LA0LE_1LA0LG_0LA---_1RD1LG` (16582) | never halts | holdout, undecided | [`BB7_16582_1RB1LD.v`](verify/BB7_16582_1RB1LD.v) |
| `1RB0RC_1RC0RA_1LD0LB_1LE0LA_0LF---_1RC0LG_1LF1LA` (N2) | never halts | holdout, undecided | [`BB7_N2_1RB0RC.v`](verify/BB7_N2_1RB0RC.v) |
| `1RB1RE_1LC0RA_1RF0RD_1LC0LE_1LD0LC_1RG0RE_0RB---` (N2m) | never halts | holdout, undecided | [`BB7_N2m_1RB1RE.v`](verify/BB7_N2m_1RB1RE.v) |
| `1RB1RE_1RC1RA_0LD1LE_1RE1LE_0RG0RF_---0LG_1LC1RA` (H1) | never halts | holdout, undecided | [`BB7_H1_1RB1RE.v`](verify/BB7_H1_1RB1RE.v) |
| `1RB1RF_0LC1LD_1RD1LD_0RE0RG_1LB1RF_1RA1RD_---0LE` (H2) | never halts | holdout, undecided | [`BB7_H2_1RB1RF.v`](verify/BB7_H2_1RB1RF.v) |
| `1RB---_0RC0RA_0RD1LG_0LE1RC_1RF0LF_1LE1LD_0LD0LB` (c01) | never halts | holdout, undecided (2026-11-08) | [`BB7_c01_1RB_0RC0RA.v`](verify/BB7_c01_1RB_0RC0RA.v) |
| `1RB---_0RC0RA_0RD1LG_0LE1RC_1RF0LF_1LE1LD_0RD0LB` (c02) | never halts | holdout, undecided (2026-11-08) | [`BB7_c02_1RB_0RC0RA.v`](verify/BB7_c02_1RB_0RC0RA.v) |

**Community status.** All seven strings appear verbatim, in this form, in the latest public bbchallenge holdout list,
`undecided_06.06.2026_16,949,557.txt.gz` (Phase 2 Stage 7, first step), lines 11,438,768 / 6,924,647 / 15,412,813 /
15,678,661 / 15,774,786 / 286,167 / 286,168. None has a page on the bbchallenge wiki, and we found no other record of them being decided.
The wiki lists one later step (Andrew Ducharme, FAR RWL_mod, 16,949,557 → 15,743,264) whose holdout list is not yet
public, so we could not check that step; if it removed any of these machines, that decision came first. The first five resisted
the generic deciders we tried (n-gram CPS, CTL variants); RWL_mod was not among them.

### The arguments

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

**c01** `1RB---_0RC0RA_0RD1LG_0LE1RC_1RF0LF_1LE1LD_0LD0LB` and **c02** `1RB---_0RC0RA_0RD1LG_0LE1RC_1RF0LF_1LE1LD_0RD0LB` (they differ only in G0, `0LD` / `0RD`). At the right end of the tape in
state C reading 0, the tape is a digit list: conf D = enc(D) C> 0^∞ with enc(d :: T) = (10)^d 0 enc(T). Three macro
rules, proved for all parameter values, describe the run:

- `R_dec`: [a+2, d+1, T] → [a+4, d, T] (the first digit grows while the next one counts down);
- `R_borrow`: [k+m+3, 0^(k+1), d+1, T] → [2, 1^k, m+3, d, T] (a run of zero digits is refilled with 1s, and the rest
  of the first digit moves on);
- `R_end`: [m+1, 0^z] → [2, 1^(m+1)] (the list is used up and rebuilt).

The halt (A1) could only be reached by a borrow whose first digit is too small for the run of zeros after it. The
invariant `INV` says that the first digit is at least 2 and that every run of z ≥ 1 zero digits followed by a nonzero
digit has z + 2 ≤ the sum of the digits before it; every rule keeps it (`step_inv`), so every borrow has room. The
blank tape reaches conf [3] after 22 steps (`init_reach`). The machine builds very long lists (about 3,000 digits
after 3.2·10^6 steps), which is why the generic deciders did not settle it.

## 124 digit-list machines (2026-11-09)

124 further machines share one proof scheme. Each proof file is self-contained (it imports only `Individual72`) and
has the same structure; only the cell-level lemmas and a handful of numbers change from file to file.

**The configurations.** At certain moments the head is at one end of the written part of the tape, in a fixed state
(the "K-config" column below), and the tape reads as an accumulator A next to the head followed by a list of digits
d1, d2, …. A digit d is a block u^d, where the unit u is `1`, `10` or `110` (the "digit" column), and digits are
separated by a single 0. A digit can be 0. Write conf A [d1, d2, …] for such a configuration.

**Three macro rules**, each proved in Coq from the cell level for all parameter values:

- D (count down): conf A (d+1 :: T) →+ conf (A + c) (d :: T). The first digit loses one unit and the accumulator
  gains c.
- B (borrow): conf (s·k + h + m) (0^(k+1) ++ (y+1) :: T) →+ conf a1 (t^k ++ (m + r0) :: y :: T), for every k and m.
  When the list starts with k+1 zero digits, the machine refills them with digit t, pays for that out of the
  accumulator, and moves what is left into the next nonzero digit.
- E (rebuild): conf X (0^z) →+ conf A' T(X) for every accumulator X the invariant allows. When every digit is used
  up, the list is rebuilt from the accumulator.

**Why the machine never halts.** Every configuration of this form is covered by one of the three rules, but the
rules hold only above small lower bounds on the accumulator, and rule B needs at least s·k + h to refill k+1 zero
digits. The inductive invariant `okz` guarantees enough: for every run of z ≥ 1 zero digits followed by a nonzero
digit, s·z + h ≤ p + s, where p is the accumulator plus the sum of the digits before the run. Nine machines (families
F168, F177, F199, F201, F236) also carry a parity condition `phi`: A + (sum of the digits) has a fixed parity. Their
rebuild rule E is proved only for accumulators of that parity, and `phi` guarantees it. A generic section
(`Section DL`, in one of two variants: 111 files use the one that also tracks a lower bound on the accumulator at
rebuild time, 13 the plain one) proves once that the three rules, together with simple side conditions on c, s, h,
a1, t and r0 that `lia` checks, make the invariant inductive (`step_inv`), and hence that the machine never halts
(`dl_nonhalt`). Each file instantiates that section with its own rules and with `init_reach`: the blank tape
reaches a first configuration that satisfies the invariant within 61 steps.

Because B is proved for every k and E for every allowed X, a borrow deep inside a long run of zeros, or an unusual
rebuilt list, cannot escape the argument. A finite simulation or a fit of the rules to a few literal cases could
miss such cases. The longest literal lists seen in these runs have 604 digits (F70).

**Community status.** All 124 machine strings appear verbatim in the same June 2026 list
(`undecided_06.06.2026_16,949,557.txt.gz`); the "list line" column gives the line. The same caveat as above applies
to the later RWL_mod step, whose list is not public. We have not checked each machine individually against the
bbchallenge wiki.

**Families.** The family labels (F1, F7, …) are this project's internal grouping of machines with similar runs; they
are only labels. Three families are only partly covered here: F7 (33 of 35 members), F6 (2 of 36) and F1 (1 of 119).
The other members of these families are not decided by this directory.

The table gives, for each machine, the K-config state and the end of the tape where the head sits, the digit unit,
c and s from rules D and B, and the parity condition if there is one.

| family | machine | list line | K-config | digit | c | s | parity | proof |
|---|---|---:|---|---|---:|---:|---|---|
| F1 | `1RB1RG_0LC0LD_1RE0LD_0RC1LB_1RF1RD_1LE1RG_1RA---` | 16,351,513 | C, left end | (10)^d | 2 | 1 | – | [`BB7_F1_1RB1RG.v`](verify/BB7_F1_1RB1RG.v) |
| F6 | `1RB---_1RC0RC_0LD0LE_1RA0LE_0RF1LC_1RG0RC_1RA1RE` | 1,116,435 | D, left end | (10)^d | 2 | 1 | – | [`BB7_F6_1RBHHH_1RC0RC_7241bc.v`](verify/BB7_F6_1RBHHH_1RC0RC_7241bc.v) |
| F6 | `1RB---_1RC0RC_0LD0LE_1RA0LE_0RF1LC_1RG1RA_1RA1RE` | 1,116,437 | D, left end | (10)^d | 2 | 1 | – | [`BB7_F6_1RBHHH_1RC0RC_ecdb35.v`](verify/BB7_F6_1RBHHH_1RC0RC_ecdb35.v) |
| F7 | `1RB---_1LC1RA_0LB1RD_0RB1RE_0LF0LG_1RC0LG_0RF1LE` | 846,949 | F, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RBHHH_1LC1RA_fd607a.v`](verify/BB7_F7_1RBHHH_1LC1RA_fd607a.v) |
| F7 | `1RB---_1LC1RA_0LB1RD_0RB1RE_0LF0LG_1RC1LD_0RF1LE` | 846,950 | F, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RBHHH_1LC1RA_c93c7d.v`](verify/BB7_F7_1RBHHH_1LC1RA_c93c7d.v) |
| F7 | `1RB---_1LC1RA_1RB1RD_0RB1RE_0LF0LG_1RC0LG_0RF1LE` | 852,454 | F, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RBHHH_1LC1RA_0da678.v`](verify/BB7_F7_1RBHHH_1LC1RA_0da678.v) |
| F7 | `1RB---_1LC1RA_1RB1RD_0RB1RE_0LF0LG_1RC1LD_0RF1LE` | 852,455 | F, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RBHHH_1LC1RA_317e02.v`](verify/BB7_F7_1RBHHH_1LC1RA_317e02.v) |
| F7 | `1RB0LC_1LA1LE_0RD---_1LB0RG_0LA1LF_0RD0RG_0LD1RF` | 2,545,915 | D, right end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB0LC_1LA1LE_480f81.v`](verify/BB7_F7_1RB0LC_1LA1LE_480f81.v) |
| F7 | `1RB0LC_1LA1LE_0RD---_1LB1RE_0LA1LF_0RD0RG_0LD1RF` | 2,545,922 | D, right end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB0LC_1LA1LE_f84872.v`](verify/BB7_F7_1RB0LC_1LA1LE_f84872.v) |
| F7 | `1RB0LF_1RC1RD_1LB0RG_0RC1RE_0LA0LF_0RA1LE_0LA---` | 5,139,934 | A, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB0LF_1RC1RD_cb02ae.v`](verify/BB7_F7_1RB0LF_1RC1RD_cb02ae.v) |
| F7 | `1RB0LF_1RC1RD_1LB1RG_0RC1RE_0LA0LF_0RA1LE_1RC---` | 5,140,182 | A, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB0LF_1RC1RD_0bc7fa.v`](verify/BB7_F7_1RB0LF_1RC1RD_0bc7fa.v) |
| F7 | `1RB0LG_0LC1RE_1LB1RD_1RC---_0RC1RF_0LA0LG_0RA1LF` | 5,250,942 | A, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB0LG_0LC1RE_91741b.v`](verify/BB7_F7_1RB0LG_0LC1RE_91741b.v) |
| F7 | `1RB0RB_1RC1RG_1RD1RB_0LE0LF_1LG0LF_1LD1LE_0RA---` | 6,540,349 | G, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB0RB_1RC1RG_8a5b00.v`](verify/BB7_F7_1RB0RB_1RC1RG_8a5b00.v) |
| F7 | `1RB0RF_1LC1LD_0LD0LB_1LE0LB_0RA---_1RG1RE_1RC1RF` | 8,389,219 | E, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB0RF_1LC1LD_52efbf.v`](verify/BB7_F7_1RB0RF_1LC1LD_52efbf.v) |
| F7 | `1RB0RG_0LC---_1LD0LD_1LE1LB_1LF1LD_0RA0RG_1RF1RA` | 8,661,848 | B, right end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB0RG_0LCHHH_5fa688.v`](verify/BB7_F7_1RB0RG_0LCHHH_5fa688.v) |
| F7 | `1RB1LC_1LA1LD_1LA---_0LA1LE_0RF0RG_1LB0RG_0LF1RE` | 10,667,577 | F, right end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB1LC_1LA1LD_56aaa5.v`](verify/BB7_F7_1RB1LC_1LA1LD_56aaa5.v) |
| F7 | `1RB1LC_1LA1LD_1LA---_0LA1LE_0RF0RG_1LB1RD_0LF1RE` | 10,667,578 | F, right end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB1LC_1LA1LD_4e2d6a.v`](verify/BB7_F7_1RB1LC_1LA1LD_4e2d6a.v) |
| F7 | `1RB1LD_1RC1RD_1LB0RG_0RC1RE_0LA0LF_0RA1LE_0LA---` | 11,538,005 | A, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB1LD_1RC1RD_515128.v`](verify/BB7_F7_1RB1LD_1RC1RD_515128.v) |
| F7 | `1RB1LD_1RC1RD_1LB1RG_0RC1RE_0LA0LF_0RA1LE_1RC---` | 11,538,072 | A, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB1LD_1RC1RD_81b555.v`](verify/BB7_F7_1RB1LD_1RC1RD_81b555.v) |
| F7 | `1RB1LE_0LC1RE_1LB1RD_1RC---_0RC1RF_0LA0LG_0RA1LF` | 11,644,229 | A, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB1LE_0LC1RE_4ca583.v`](verify/BB7_F7_1RB1LE_0LC1RE_4ca583.v) |
| F7 | `1RB1RC_0RC0RA_1RD0RA_0LE---_1LF0LF_1LG1LD_1LB1LF` | 14,409,912 | D, right end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB1RC_0RC0RA_4ddd71.v`](verify/BB7_F7_1RB1RC_0RC0RA_4ddd71.v) |
| F7 | `1RB1RC_1LA0RG_0RB1RD_0LE0LF_1RA0LF_0RE1LD_0LE---` | 14,484,664 | E, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB1RC_1LA0RG_120c9d.v`](verify/BB7_F7_1RB1RC_1LA0RG_120c9d.v) |
| F7 | `1RB1RC_1LA0RG_0RB1RD_0LE0LF_1RA1LC_0RE1LD_0LE---` | 14,484,665 | E, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB1RC_1LA0RG_8b43c6.v`](verify/BB7_F7_1RB1RC_1LA0RG_8b43c6.v) |
| F7 | `1RB1RC_1LA1RG_0RB1RD_0LE0LF_1RA0LF_0RE1LD_1RB---` | 14,507,498 | E, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB1RC_1LA1RG_c88bc1.v`](verify/BB7_F7_1RB1RC_1LA1RG_c88bc1.v) |
| F7 | `1RB1RC_1LA1RG_0RB1RD_0LE0LF_1RA1LC_0RE1LD_1RB---` | 14,507,499 | E, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB1RC_1LA1RG_b3ef24.v`](verify/BB7_F7_1RB1RC_1LA1RG_b3ef24.v) |
| F7 | `1RB1RD_1RC1RA_1LD0LF_0RG1RE_---0LC_1LC1LC_1RF0RA` | 15,108,906 | D, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB1RD_1RC1RA_521d2e.v`](verify/BB7_F7_1RB1RD_1RC1RA_521d2e.v) |
| F7 | `1RB1RE_0LC0LD_0RE0LD_1LB1LC_1RA1RF_0RG---_1RD0RB` | 15,143,610 | B, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB1RE_0LC0LD_4584d8.v`](verify/BB7_F7_1RB1RE_0LC0LD_4584d8.v) |
| F7 | `1RB1RE_0LC0LD_0RE0LD_1LB1LC_1RA1RF_0RG---_1RD0RE` | 15,143,611 | B, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB1RE_0LC0LD_c19c7a.v`](verify/BB7_F7_1RB1RE_0LC0LD_c19c7a.v) |
| F7 | `1RB1RF_1RC1RA_0LD0LE_0RA0LE_1LC1LD_0RG---_1RE0RA` | 16,305,633 | C, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB1RF_1RC1RA_ef93e9.v`](verify/BB7_F7_1RB1RF_1RC1RA_ef93e9.v) |
| F7 | `1RB1RF_1RC1RA_0LD0LE_0RA0LE_1LC1LD_0RG---_1RE0RC` | 16,305,634 | C, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB1RF_1RC1RA_9fc1a7.v`](verify/BB7_F7_1RB1RF_1RC1RA_9fc1a7.v) |
| F7 | `1RB1RF_1RC1RA_0LD0LE_1LF0LE_1LC1LD_0RG---_1RA0RA` | 16,305,674 | F, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB1RF_1RC1RA_9ec91e.v`](verify/BB7_F7_1RB1RF_1RC1RA_9ec91e.v) |
| F7 | `1RB1RF_1RC1RA_0LD0LE_1LF0LE_1LC1LD_0RG---_1RE0RA` | 16,305,676 | F, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB1RF_1RC1RA_fa5590.v`](verify/BB7_F7_1RB1RF_1RC1RA_fa5590.v) |
| F7 | `1RB1RG_0LC0LD_1LE0LD_1LB1LC_0RF---_1RD0RG_1RA1RE` | 16,350,774 | E, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB1RG_0LC0LD_b021e2.v`](verify/BB7_F7_1RB1RG_0LC0LD_b021e2.v) |
| F7 | `1RB1RG_0LC0LD_1LE0LD_1LB1LC_0RF---_1RG0RG_1RA1RE` | 16,350,775 | E, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB1RG_0LC0LD_2107f5.v`](verify/BB7_F7_1RB1RG_0LC0LD_2107f5.v) |
| F7 | `1RB1RG_1LC0LE_0RF1RD_---0LB_1LB1LB_1RE0RG_1RA1RC` | 16,572,407 | C, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB1RG_1LC0LE_c4c97e.v`](verify/BB7_F7_1RB1RG_1LC0LE_c4c97e.v) |
| F7 | `1RB1RG_1LC1LF_1RE0LD_1LB1RC_---0LB_0RA0RC_1RA1RF` | 16,710,902 | C, left end | (10)^d | 2 | 1 | – | [`BB7_F7_1RB1RG.v`](verify/BB7_F7_1RB1RG.v) |
| F32 | `1RB---_1LC1LB_0LD0LB_0RE1LD_0RF1RG_1RC1RF_0RA0RF` | 781,113 | D, left end | 1^d | 2 | 1 | – | [`BB7_F32_1RBHHH_1LC1LB_4e4017.v`](verify/BB7_F32_1RBHHH_1LC1LB_4e4017.v) |
| F32 | `1RB0RF_0LC0LD_1LE0LD_1LB1LC_0RA---_1RG1RE_1RB1RF` | 8,032,707 | E, left end | (10)^d | 2 | 1 | – | [`BB7_F32_1RB0RF_0LC0LD_9704ed.v`](verify/BB7_F32_1RB0RF_0LC0LD_9704ed.v) |
| F32 | `1RB0RG_0LC---_1LF0LD_1LE1LB_1LF1LD_0RA0RG_1RF1RA` | 8,663,835 | B, right end | (10)^d | 2 | 1 | – | [`BB7_F32_1RB0RG_0LCHHH_7f1181.v`](verify/BB7_F32_1RB0RG_0LCHHH_7f1181.v) |
| F32 | `1RB1LA_1LC1LD_0RB1LB_0RE0LD_0LA0RF_---1RG_1RD1RE` | 9,753,447 | D, right end | (110)^d | 2 | 1 | – | [`BB7_F32_1RB1LA_1LC1LD_a295a7.v`](verify/BB7_F32_1RB1LA_1LC1LD_a295a7.v) |
| F32 | `1RB1LA_1LC1LG_0RD1LB_0LA0RE_---1RF_1RC1RD_0RD0LG` | 9,761,736 | C, right end | (110)^d | 2 | 1 | – | [`BB7_F32_1RB1LA_1LC1LG_038baf.v`](verify/BB7_F32_1RB1LA_1LC1LG_038baf.v) |
| F32 | `1RB1LA_1LC1LG_0RD1LB_0LA0RE_---1RF_1RG1RD_0RD0LG` | 9,761,737 | G, right end | (110)^d | 2 | 1 | – | [`BB7_F32_1RB1LA_1LC1LG_83701a.v`](verify/BB7_F32_1RB1LA_1LC1LG_83701a.v) |
| F32 | `1RB1RA_0LC0LG_0RD1LC_0RA1RE_0RF0RA_1RG---_1LB1LG` | 13,400,368 | C, left end | 1^d | 2 | 1 | – | [`BB7_F32_1RB1RA_0LC0LG_2aa88a.v`](verify/BB7_F32_1RB1RA_0LC0LG_2aa88a.v) |
| F32 | `1RB1RA_0RC0RA_0LD1RC_0LE1LF_1LB1LE_0LG0LE_1LA---` | 13,531,695 | C, right end | 1^d | 2 | 1 | – | [`BB7_F32_1RB1RA_0RC0RA_9c9f7d.v`](verify/BB7_F32_1RB1RA_0RC0RA_9c9f7d.v) |
| F32 | `1RB1RC_0RC0RA_1RD0RA_0LE---_1LB0LF_1LG1LD_1LB1LF` | 14,409,911 | D, right end | (10)^d | 2 | 1 | – | [`BB7_F32_1RB1RC_0RC0RA_c3587a.v`](verify/BB7_F32_1RB1RC_0RC0RA_c3587a.v) |
| F32 | `1RB1RF_1RC1RA_0LD0LE_1LF0LE_1LC1LD_0RG---_1RC0RA` | 16,305,675 | F, left end | (10)^d | 2 | 1 | – | [`BB7_F32_1RB1RF.v`](verify/BB7_F32_1RB1RF.v) |
| F32 | `1RB1RG_0LC0LD_1LE0LD_1LB1LC_0RF---_1RB0RG_1RA1RE` | 16,350,773 | E, left end | (10)^d | 2 | 1 | – | [`BB7_F32_1RB1RG_0LC0LD_331e78.v`](verify/BB7_F32_1RB1RG_0LC0LD_331e78.v) |
| F44 | `1RB---_1LC1LB_0RE0RD_1RC1RD_0LF1RE_1LB1LG_0LA0LB` | 786,674 | C, right end | 1^d | 3 | 1 | – | [`BB7_F44_1RBHHH_1LC1LB_c1a736.v`](verify/BB7_F44_1RBHHH_1LC1LB_c1a736.v) |
| F44 | `1RB0RG_0LC---_1LD1LC_0LE0LC_0RF1LE_1RG1RA_1RD1RG` | 8,662,074 | D, left end | 1^d | 3 | 1 | – | [`BB7_F44_1RB0RG_0LCHHH_941ab4.v`](verify/BB7_F44_1RB0RG_0LCHHH_941ab4.v) |
| F44 | `1RB1RA_0LC0LG_0RD1LC_1RA1RE_0RF0RA_1LA---_1LB1LG` | 13,400,389 | B, left end | 1^d | 3 | 1 | – | [`BB7_F44_1RB1RA_0LC0LG_6dc192.v`](verify/BB7_F44_1RB1RA_0LC0LG_6dc192.v) |
| F44 | `1RB1RA_0LC0LG_0RD1LC_1RA1RE_1RF0RA_0LG---_1LB1LG` | 13,400,393 | B, left end | 1^d | 3 | 1 | – | [`BB7_F44_1RB1RA_0LC0LG_da478c.v`](verify/BB7_F44_1RB1RA_0LC0LG_da478c.v) |
| F44 | `1RB1RA_0RC0RA_0LD1RC_1LE1LF_1LB1LE_0LG0LE_1RE---` | 13,531,729 | B, right end | 1^d | 3 | 1 | – | [`BB7_F44_1RB1RA.v`](verify/BB7_F44_1RB1RA.v) |
| F44 | `1RB1RA_0RC0RA_0LD1RC_1LE1LF_1LB1LE_1LG0LE_0RA---` | 13,531,734 | B, right end | 1^d | 3 | 1 | – | [`BB7_F44_1RB1RA_0RC0RA_b2a973.v`](verify/BB7_F44_1RB1RA_0RC0RA_b2a973.v) |
| F44 | `1RB1RE_1RC1RB_0LD0LG_0RA1LD_0RF0RB_1LB---_1LC1LG` | 15,683,601 | C, left end | 1^d | 3 | 1 | – | [`BB7_F44_1RB1RE_1RC1RB_32e621.v`](verify/BB7_F44_1RB1RE_1RC1RB_32e621.v) |
| F44 | `1RB1RE_1RC1RB_0LD0LG_0RA1LD_1RF0RB_0LG---_1LC1LG` | 15,683,605 | C, left end | 1^d | 3 | 1 | – | [`BB7_F44_1RB1RE_1RC1RB_0bc824.v`](verify/BB7_F44_1RB1RE_1RC1RB_0bc824.v) |
| F50 | `1RB---_1LC1LB_0RE0RD_1RC1RD_0LF1RE_0LB1LG_0LA0LB` | 786,672 | E, right end | 1^d | 2 | 1 | – | [`BB7_F50_1RBHHH_1LC1LB_a0bff6.v`](verify/BB7_F50_1RBHHH_1LC1LB_a0bff6.v) |
| F50 | `1RB0RE_1LC1LC_1LD0LB_0RA1RG_1RF1RD_1RC1RE_---0LC` | 7,794,932 | D, left end | (10)^d | 2 | 1 | – | [`BB7_F50_1RB0RE_1LC1LC_1df397.v`](verify/BB7_F50_1RB0RE_1LC1LC_1df397.v) |
| F50 | `1RB0RG_0LC---_1LD1LC_0LE0LC_0RF1LE_0RG1RA_1RD1RG` | 8,662,073 | E, left end | 1^d | 2 | 1 | – | [`BB7_F50_1RB0RG.v`](verify/BB7_F50_1RB0RG.v) |
| F50 | `1RB1RA_0LC0LG_0RD1LC_0RA1RE_0RF0RA_1LA---_1LB1LG` | 13,400,366 | C, left end | 1^d | 2 | 1 | – | [`BB7_F50_1RB1RA_0LC0LG_80cb17.v`](verify/BB7_F50_1RB1RA_0LC0LG_80cb17.v) |
| F50 | `1RB1RA_0LC0LG_0RD1LC_0RA1RE_1RF0RA_0LG---_1LB1LG` | 13,400,370 | C, left end | 1^d | 2 | 1 | – | [`BB7_F50_1RB1RA_0LC0LG_08d82b.v`](verify/BB7_F50_1RB1RA_0LC0LG_08d82b.v) |
| F50 | `1RB1RA_0RC0RA_0LD1RC_0LE1LF_1LB1LE_0LG0LE_1RE---` | 13,531,697 | C, right end | 1^d | 2 | 1 | – | [`BB7_F50_1RB1RA_0RC0RA_2b89b3.v`](verify/BB7_F50_1RB1RA_0RC0RA_2b89b3.v) |
| F50 | `1RB1RA_0RC0RA_0LD1RC_0LE1LF_1LB1LE_1LG0LE_0RA---` | 13,531,699 | C, right end | 1^d | 2 | 1 | – | [`BB7_F50_1RB1RA_0RC0RA_59b970.v`](verify/BB7_F50_1RB1RA_0RC0RA_59b970.v) |
| F51 | `1RB---_1RC1RB_0RD0RB_0LE1RD_1LF1LG_1LC1LF_0LA0LF` | 1,318,471 | C, right end | 1^d | 3 | 1 | – | [`BB7_F51_1RBHHH_1RC1RB_0dda9a.v`](verify/BB7_F51_1RBHHH_1RC1RB_0dda9a.v) |
| F51 | `1RB1RA_0LC0LG_0RD1LC_1RA1RE_0RF0RA_1LG---_1LB1LG` | 13,400,390 | B, left end | 1^d | 3 | 1 | – | [`BB7_F51_1RB1RA_0LC0LG_84e324.v`](verify/BB7_F51_1RB1RA_0LC0LG_84e324.v) |
| F51 | `1RB1RA_0LC0LG_0RD1LC_1RA1RE_1RF0RA_0RG---_1LB1LG` | 13,400,394 | B, left end | 1^d | 3 | 1 | – | [`BB7_F51_1RB1RA_0LC0LG_ac0f9d.v`](verify/BB7_F51_1RB1RA_0LC0LG_ac0f9d.v) |
| F51 | `1RB1RA_0RC0RA_0LD1RC_1LE1LF_1LB1LE_0LG0LE_1RA---` | 13,531,728 | B, right end | 1^d | 3 | 1 | – | [`BB7_F51_1RB1RA_0RC0RA_e30611.v`](verify/BB7_F51_1RB1RA_0RC0RA_e30611.v) |
| F51 | `1RB1RA_0RC0RA_0LD1RC_1LE1LF_1LB1LE_1LG0LE_0LA---` | 13,531,733 | B, right end | 1^d | 3 | 1 | – | [`BB7_F51_1RB1RA_0RC0RA_23875e.v`](verify/BB7_F51_1RB1RA_0RC0RA_23875e.v) |
| F51 | `1RB1RE_1RC1RB_0LD0LG_0RA1LD_0RF0RB_1LG---_1LC1LG` | 15,683,602 | D, left end | 1^d | 3 | 1 | – | [`BB7_F51_1RB1RE.v`](verify/BB7_F51_1RB1RE.v) |
| F51 | `1RB1RE_1RC1RB_0LD0LG_0RA1LD_1RF0RB_0RG---_1LC1LG` | 15,683,606 | C, left end | 1^d | 3 | 1 | – | [`BB7_F51_1RB1RE_1RC1RB_c7cee1.v`](verify/BB7_F51_1RB1RE_1RC1RB_c7cee1.v) |
| F68 | `1RB---_1RC1RG_1RD1RB_0LE0LF_1RA0LF_1LB1LD_0RE0RA` | 1,404,995 | B, left end | (10)^d | 2 | 1 | – | [`BB7_F68_1RBHHH_1RC1RG_2fd7d0.v`](verify/BB7_F68_1RBHHH_1RC1RG_2fd7d0.v) |
| F68 | `1RB0LF_1RC---_1RD1RG_1RE1RC_0LA0LF_1LC1LE_0RA0RB` | 4,960,420 | C, left end | (10)^d | 2 | 1 | – | [`BB7_F68_1RB0LF_1RCHHH_aaa7de.v`](verify/BB7_F68_1RB0LF_1RCHHH_aaa7de.v) |
| F68 | `1RB1RD_1LC1LG_1LD1LB_0RE0RA_1LF0RA_1LB---_0LE0LF` | 14,976,334 | B, right end | (10)^d | 2 | 1 | – | [`BB7_F68_1RB1RD_1LC1LG_7b2f89.v`](verify/BB7_F68_1RB1RD_1LC1LG_7b2f89.v) |
| F68 | `1RB1RE_0LC0LD_1RF0LD_1LE1LB_1RA1RG_1RE---_0RC0RF` | 15,145,240 | E, left end | (10)^d | 2 | 1 | – | [`BB7_F68_1RB1RE.v`](verify/BB7_F68_1RB1RE.v) |
| F68 | `1RB1RG_1RC1RA_0LD0LE_1RF0LE_1LA1LC_1RA---_0RD0RF` | 16,914,757 | A, left end | (10)^d | 2 | 1 | – | [`BB7_F68_1RB1RG_1RC1RA_7975ea.v`](verify/BB7_F68_1RB1RG_1RC1RA_7975ea.v) |
| F69 | `1RB---_1LC1LB_0LD0LB_0RE1LD_1RF1RG_1RC1RF_1RA0RF` | 781,116 | C, left end | 1^d | 3 | 1 | – | [`BB7_F69_1RBHHH_1LC1LB_0b5330.v`](verify/BB7_F69_1RBHHH_1LC1LB_0b5330.v) |
| F69 | `1RB0RG_1RC---_1LD1LC_0LE0LC_0RF1LE_1RG1RA_1RD1RG` | 9,116,624 | D, left end | 1^d | 3 | 1 | – | [`BB7_F69_1RB0RG_1RCHHH_506e34.v`](verify/BB7_F69_1RB0RG_1RCHHH_506e34.v) |
| F69 | `1RB1RA_0LC0LG_0RD1LC_1RA1RE_1RF0RA_1RG---_1LB1LG` | 13,400,397 | B, left end | 1^d | 3 | 1 | – | [`BB7_F69_1RB1RA_0LC0LG_4143c1.v`](verify/BB7_F69_1RB1RA_0LC0LG_4143c1.v) |
| F69 | `1RB1RA_0RC0RA_0LD1RC_1LE1LF_1LB1LE_1LG0LE_1LA---` | 13,531,736 | B, right end | 1^d | 3 | 1 | – | [`BB7_F69_1RB1RA_0RC0RA_3c7147.v`](verify/BB7_F69_1RB1RA_0RC0RA_3c7147.v) |
| F69 | `1RB1RE_1RC1RB_0LD0LG_0RA1LD_1RF0RB_1RG---_1LC1LG` | 15,683,609 | D, left end | 1^d | 3 | 1 | – | [`BB7_F69_1RB1RE.v`](verify/BB7_F69_1RB1RE.v) |
| F70 | `1RB---_1RC1RB_0RD0RB_0LE1RD_1LF1LG_1LC1LF_1LA0LF` | 1,318,472 | C, right end | 1^d | 3 | 1 | – | [`BB7_F70_1RBHHH_1RC1RB_f06d31.v`](verify/BB7_F70_1RBHHH_1RC1RB_f06d31.v) |
| F70 | `1RB0RG_1LC---_1LD1LC_0LE0LC_0RF1LE_1RG1RA_1RD1RG` | 8,868,955 | D, left end | 1^d | 3 | 1 | – | [`BB7_F70_1RB0RG_1LCHHH_81dba5.v`](verify/BB7_F70_1RB0RG_1LCHHH_81dba5.v) |
| F70 | `1RB1RA_0LC0LG_0RD1LC_1RA1RE_1RF0RA_1LG---_1LB1LG` | 13,400,396 | B, left end | 1^d | 3 | 1 | – | [`BB7_F70_1RB1RA_0LC0LG_18661a.v`](verify/BB7_F70_1RB1RA_0LC0LG_18661a.v) |
| F70 | `1RB1RA_0RC0RA_0LD1RC_1LE1LF_1LB1LE_1LG0LE_1RA---` | 13,531,737 | B, right end | 1^d | 3 | 1 | – | [`BB7_F70_1RB1RA.v`](verify/BB7_F70_1RB1RA.v) |
| F70 | `1RB1RE_1RC1RB_0LD0LG_0RA1LD_1RF0RB_1LG---_1LC1LG` | 15,683,608 | C, left end | 1^d | 3 | 1 | – | [`BB7_F70_1RB1RE_1RC1RB_c9cfba.v`](verify/BB7_F70_1RB1RE_1RC1RB_c9cfba.v) |
| F71 | `1RB---_0RC0RG_0LD1RC_1LE1LF_1LB1LE_1LA0LE_1RB1RG` | 363,248 | B, right end | 1^d | 3 | 1 | – | [`BB7_F71_1RBHHH_0RC0RG_c45a4a.v`](verify/BB7_F71_1RBHHH_0RC0RG_c45a4a.v) |
| F71 | `1RB0RG_1LC---_0LE0LD_1LC1LD_0RF1LE_1RG1RA_1RC1RG` | 8,865,393 | C, left end | 1^d | 3 | 1 | – | [`BB7_F71_1RB0RG_1LCHHH_681a1c.v`](verify/BB7_F71_1RB0RG_1LCHHH_681a1c.v) |
| F71 | `1RB1RA_0LC0LG_0RD1LC_1RA1RE_1RF0RA_1LB---_1LB1LG` | 13,400,395 | B, left end | 1^d | 3 | 1 | – | [`BB7_F71_1RB1RA_0LC0LG_845298.v`](verify/BB7_F71_1RB1RA_0LC0LG_845298.v) |
| F71 | `1RB1RA_0RC0RA_0LD1RC_1LE1LF_1LB1LE_1LG0LE_1RB---` | 13,531,738 | B, right end | 1^d | 3 | 1 | – | [`BB7_F71_1RB1RA_0RC0RA_944d13.v`](verify/BB7_F71_1RB1RA_0RC0RA_944d13.v) |
| F71 | `1RB1RE_1RC1RB_0LD0LG_0RA1LD_1RF0RB_1LC---_1LC1LG` | 15,683,607 | D, left end | 1^d | 3 | 1 | – | [`BB7_F71_1RB1RE.v`](verify/BB7_F71_1RB1RE.v) |
| F72 | `1RB---_1RC1RB_0RD0RB_0LE1RD_0LF1LG_1LC1LF_0LA0LF` | 1,318,457 | D, right end | 1^d | 2 | 1 | – | [`BB7_F72_1RBHHH_1RC1RB_1f8ea9.v`](verify/BB7_F72_1RBHHH_1RC1RB_1f8ea9.v) |
| F72 | `1RB1RA_0LC0LG_0RD1LC_0RA1RE_0RF0RA_1LG---_1LB1LG` | 13,400,367 | C, left end | 1^d | 2 | 1 | – | [`BB7_F72_1RB1RA_0LC0LG_9a3b8c.v`](verify/BB7_F72_1RB1RA_0LC0LG_9a3b8c.v) |
| F72 | `1RB1RA_0LC0LG_0RD1LC_0RA1RE_1RF0RA_0RG---_1LB1LG` | 13,400,371 | C, left end | 1^d | 2 | 1 | – | [`BB7_F72_1RB1RA_0LC0LG_71a853.v`](verify/BB7_F72_1RB1RA_0LC0LG_71a853.v) |
| F72 | `1RB1RA_0RC0RA_0LD1RC_0LE1LF_1LB1LE_0LG0LE_1RA---` | 13,531,696 | C, right end | 1^d | 2 | 1 | – | [`BB7_F72_1RB1RA.v`](verify/BB7_F72_1RB1RA.v) |
| F72 | `1RB1RA_0RC0RA_0LD1RC_0LE1LF_1LB1LE_1LG0LE_0LA---` | 13,531,698 | C, right end | 1^d | 2 | 1 | – | [`BB7_F72_1RB1RA_0RC0RA_a5732f.v`](verify/BB7_F72_1RB1RA_0RC0RA_a5732f.v) |
| F86 | `1RB---_1RC1RB_0RD0RB_0LE1RD_0LF1LG_1LC1LF_1LA0LF` | 1,318,458 | D, right end | 1^d | 2 | 1 | – | [`BB7_F86_1RBHHH.v`](verify/BB7_F86_1RBHHH.v) |
| F86 | `1RB0RG_1LC---_1LD1LC_0LE0LC_0RF1LE_0RG1RA_1RD1RG` | 8,868,954 | E, left end | 1^d | 2 | 1 | – | [`BB7_F86_1RB0RG_1LCHHH_cb4714.v`](verify/BB7_F86_1RB0RG_1LCHHH_cb4714.v) |
| F86 | `1RB1RA_0LC0LG_0RD1LC_0RA1RE_1RF0RA_1LG---_1LB1LG` | 13,400,373 | C, left end | 1^d | 2 | 1 | – | [`BB7_F86_1RB1RA_0LC0LG_8ce2f0.v`](verify/BB7_F86_1RB1RA_0LC0LG_8ce2f0.v) |
| F86 | `1RB1RA_0RC0RA_0LD1RC_0LE1LF_1LB1LE_1LG0LE_1RA---` | 13,531,702 | C, right end | 1^d | 2 | 1 | – | [`BB7_F86_1RB1RA_0RC0RA_51ecd7.v`](verify/BB7_F86_1RB1RA_0RC0RA_51ecd7.v) |
| F92 | `1RB---_1LC1LB_0LD0LB_0RE1LD_1RF1RG_1RC1RF_0RA0RF` | 781,115 | C, left end | 1^d | 3 | 1 | – | [`BB7_F92_1RBHHH_1LC1LB_5fc5f8.v`](verify/BB7_F92_1RBHHH_1LC1LB_5fc5f8.v) |
| F92 | `1RB1RA_0LC0LG_0RD1LC_1RA1RE_0RF0RA_1RG---_1LB1LG` | 13,400,391 | B, left end | 1^d | 3 | 1 | – | [`BB7_F92_1RB1RA.v`](verify/BB7_F92_1RB1RA.v) |
| F92 | `1RB1RA_0RC0RA_0LD1RC_1LE1LF_1LB1LE_0LG0LE_1LA---` | 13,531,727 | B, right end | 1^d | 3 | 1 | – | [`BB7_F92_1RB1RA_0RC0RA_a36292.v`](verify/BB7_F92_1RB1RA_0RC0RA_a36292.v) |
| F92 | `1RB1RE_1RC1RB_0LD0LG_0RA1LD_0RF0RB_1RG---_1LC1LG` | 15,683,603 | C, left end | 1^d | 3 | 1 | – | [`BB7_F92_1RB1RE_1RC1RB_92041d.v`](verify/BB7_F92_1RB1RE_1RC1RB_92041d.v) |
| F93 | `1RB0RG_0LC---_0LE0LD_1LC1LD_0RF1LE_1RG1RA_1RC1RG` | 8,659,897 | C, left end | 1^d | 3 | 1 | – | [`BB7_F93_1RB0RG_0LCHHH_9d48e3.v`](verify/BB7_F93_1RB0RG_0LCHHH_9d48e3.v) |
| F93 | `1RB1RA_0LC0LG_0RD1LC_1RA1RE_1RF0RA_0LB---_1LB1LG` | 13,400,392 | B, left end | 1^d | 3 | 1 | – | [`BB7_F93_1RB1RA_0LC0LG_629911.v`](verify/BB7_F93_1RB1RA_0LC0LG_629911.v) |
| F93 | `1RB1RA_0RC0RA_0LD1RC_1LE1LF_1LB1LE_1LG0LE_0RB---` | 13,531,735 | B, right end | 1^d | 3 | 1 | – | [`BB7_F93_1RB1RA.v`](verify/BB7_F93_1RB1RA.v) |
| F93 | `1RB1RE_1RC1RB_0LD0LG_0RA1LD_1RF0RB_0LC---_1LC1LG` | 15,683,604 | C, left end | 1^d | 3 | 1 | – | [`BB7_F93_1RB1RE_1RC1RB_612725.v`](verify/BB7_F93_1RB1RE_1RC1RB_612725.v) |
| F123 | `1RB0RG_0LC---_0LE0LD_1LC1LD_0RF1LE_0RG1RA_1RC1RG` | 8,659,896 | E, left end | 1^d | 2 | 1 | – | [`BB7_F123_1RB0RG_0LCHHH_106ce6.v`](verify/BB7_F123_1RB0RG_0LCHHH_106ce6.v) |
| F123 | `1RB1RA_0LC0LG_0RD1LC_0RA1RE_1RF0RA_0LB---_1LB1LG` | 13,400,369 | C, left end | 1^d | 2 | 1 | – | [`BB7_F123_1RB1RA.v`](verify/BB7_F123_1RB1RA.v) |
| F123 | `1RB1RA_0RC0RA_0LD1RC_0LE1LF_1LB1LE_1LG0LE_0RB---` | 13,531,700 | C, right end | 1^d | 2 | 1 | – | [`BB7_F123_1RB1RA_0RC0RA_12e0c0.v`](verify/BB7_F123_1RB1RA_0RC0RA_12e0c0.v) |
| F144 | `1RB1RA_0LC0LG_0RD1LC_1RA1RE_0RF0RA_0LG---_1LB1LG` | 13,400,388 | B, left end | 1^d | 3 | 1 | – | [`BB7_F144_1RB1RA_0LC0LG_b4fc0f.v`](verify/BB7_F144_1RB1RA_0LC0LG_b4fc0f.v) |
| F144 | `1RB1RA_0RC0RA_0LD1RC_1LE1LF_1LB1LE_0LG0LE_0RA---` | 13,531,726 | B, right end | 1^d | 3 | 1 | – | [`BB7_F144_1RB1RA_0RC0RA_8a541e.v`](verify/BB7_F144_1RB1RA_0RC0RA_8a541e.v) |
| F144 | `1RB1RE_1RC1RB_0LD0LG_0RA1LD_0RF0RB_0LG---_1LC1LG` | 15,683,600 | C, left end | 1^d | 3 | 1 | – | [`BB7_F144_1RB1RE.v`](verify/BB7_F144_1RB1RE.v) |
| F168 | `1RB0LG_1RC1RB_0RD0RB_0LE1RD_0LD1LF_---1LA_1LC1LG` | 5,717,216 | D, right end | 1^d | 3 | 2 | A + Σd even | [`BB7_F168_1RB0LG_1RC1RB_127a84.v`](verify/BB7_F168_1RB0LG_1RC1RB_127a84.v) |
| F168 | `1RB1RA_0RC0RA_0LD1RC_0LE1LE_---1LF_1RA0LG_1LB1LG` | 13,531,683 | C, right end | 1^d | 3 | 2 | A + Σd even | [`BB7_F168_1RB1RA.v`](verify/BB7_F168_1RB1RA.v) |
| F177 | `1RB1RA_0LC0LF_0RD1LC_1RA1RE_0RF0RG_1LB1LF_---0RA` | 13,397,764 | C, left end | 1^d | 3 | 2 | A + Σd odd | [`BB7_F177_1RB1RA_0LC0LF_c4fc79.v`](verify/BB7_F177_1RB1RA_0LC0LF_c4fc79.v) |
| F177 | `1RB1RA_0RC0RA_0LD1RC_1LE1LF_1LB1LE_0LA0LG_---0LE` | 13,531,724 | B, right end | 1^d | 3 | 2 | A + Σd odd | [`BB7_F177_1RB1RA.v`](verify/BB7_F177_1RB1RA.v) |
| F197 | `1RB0RC_1LC1LD_0LD0LB_0RE0LB_1RF1RG_1RC1RE_0RA---` | 6,829,096 | C, left end | (10)^d | 2 | 1 | – | [`BB7_F197_1RB0RC.v`](verify/BB7_F197_1RB0RC.v) |
| F197 | `1RB0RE_1LC1LD_0LD0LB_0RE0LB_1RF1RG_1RC1RE_0RA---` | 7,796,249 | C, left end | (10)^d | 2 | 1 | – | [`BB7_F197_1RB0RE_1LC1LD_6f7cad.v`](verify/BB7_F197_1RB0RE_1LC1LD_6f7cad.v) |
| F199 | `1RB1RA_0LC0LF_0RD1LC_1RA1RE_0RF1RG_1LB1LF_---0RA` | 13,397,765 | C, left end | 1^d | 3 | 2 | A + Σd odd | [`BB7_F199_1RB1RA_0LC0LF_d20467.v`](verify/BB7_F199_1RB1RA_0LC0LF_d20467.v) |
| F199 | `1RB1RA_0RC0RA_0LD1RC_1LE1LF_1LB1LE_0LA1LG_---0LE` | 13,531,725 | B, right end | 1^d | 3 | 2 | A + Σd odd | [`BB7_F199_1RB1RA.v`](verify/BB7_F199_1RB1RA.v) |
| F201 | `1RB0LG_1RC1RB_0RD0RB_0LE1RD_0LE1LF_---1LA_1LC1LG` | 5,717,217 | D, right end | 1^d | 3 | 2 | A + Σd even | [`BB7_F201_1RB0LG_1RC1RB_cf082e.v`](verify/BB7_F201_1RB0LG_1RC1RB_cf082e.v) |
| F201 | `1RB1RE_1RC1RB_0LD0LG_0RA1LD_---1RF_1LG0RB_1LC1LG` | 15,683,598 | D, left end | 1^d | 3 | 2 | A + Σd even | [`BB7_F201_1RB1RE.v`](verify/BB7_F201_1RB1RE.v) |
| F236 | `1RB1RA_0LC0LF_0RD1LC_1RA1RE_1LF1RG_1LB1LF_---0RA` | 13,397,766 | C, left end | 1^d | 3 | 2 | A + Σd odd | [`BB7_F236_1RB1RA.v`](verify/BB7_F236_1RB1RA.v) |
| F279 | `1RB0LA_0RC0RG_1RD---_0LE0LF_1LE0RF_1LF1RA_0RD0RG` | 1,517,751 | A, left end | 1^d | 3 | 2 | – | [`BB7_F279_1RB0LA.v`](verify/BB7_F279_1RB0LA.v) |

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

The proofs of the first five machines are by Claude agents (Anthropic) working in this project, 2026-09 to 2026-10. They used this project's
symbolic-execution engine for the cell-level lemmas and hand-written Coq for the families, invariants and composition.
The holdout list is the bbchallenge community's (Phase 1 enumeration by mxdys's enumerator
[ccz181078/TM](https://github.com/ccz181078/TM) and contributors; Phase 2 stages as listed on the
[wiki](https://wiki.bbchallenge.org/wiki/BB(7))). The machine 16582 was singled out by this project's
growth ranking of a sample of Phase 1 holdouts. The pairs N2/N2m and H1/H2 came out of this project's scans of
the June 2026 list. c01 and c02 were analysed and proved in Coq by Argon, a Google Gemini model run by the repository owner in Google's
Antigravity (2026-11-07), with this project's symbolic-execution engine for the cell-level lemmas; the logical path
in their `Require` line was changed from `BB8` to `BB7` here, and they were re-checked here.

The 124 digit-list machines came out of this project's classification of the "rebuilder" machines in the June 2026
list. Their proofs are by a Claude agent (Anthropic) working in this project (2026-11-08 to 2026-11-09). A generator
fits the three macro rules to each machine's literal run, proves the cell-level lemmas with this project's
symbolic-execution engine, and instantiates the generic section; the borrow rules that the engine cannot frame in
one piece (families F168, F177, F199, F201, F236, F279 and F7) go through a generated induction over rounds. As
for c01 and c02, the only change made here is the logical path in the `Require` line (`BB8` to `BB7`).

None of these proofs has been reviewed by the bbchallenge community yet.
