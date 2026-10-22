# A 9-state machine above f_ω(f_ω(465009))

    1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA

> **Superseded (2026-10-18)** as this folder's BB(9) entry by C04,
> [`1RB0RA_..._1RI---_0RI0RF`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF.md), which Coq proves
> beats fw2's exact score. fw2's files are unchanged; C04's comparison uses them.
> C04 has since been superseded too; the current BB(9) entry is listed in [`README.md`](README.md).

Below we call this machine **fw2**. It halts from the blank tape. Coq proves its exact number of ones at the halt as
an explicit recursion, and proves that its score exceeds f_ω(f_ω(465009)) in the standard fast-growing hierarchy.
Coq also proves that it beats the earlier BB(9) record of this repository (`1RB0RA_..._0LH1RZ`, which it supersedes),
two later 9-state machines of this project, Jacobzheng's 2024 BB(9) champion and Racheline's 2024 BB(10) champion.
It does not beat our 10-state machine n1 ([`../BB10/`](../BB10/)), which is at level f_(ω+1).

fw2 is a counter of Ackermann type on a list of digits, the same digit family and the same three counting rules as
Jacobzheng's BB(9) champion (13 of its 18 transitions are the champion's). The difference is what happens when the
list is used up: fw2 rebuilds a list of about 3b/4 digits from the counter b, and it does this twice before it halts.
The first list, [1; 1], comes from the start-up and leaves the counter b₁ = 620011. The two rebuilt lists give
b₂ > f_ω(465009) and b₃ > f_ω(f_ω(465009)). fw2 and its three Coq files were found and written by Argon, a Google Gemini model (section 5).
Written 2026-10-16.

|   | 0   | 1   |                       |
|---|-----|-----|-----------------------|
| A | 1RB | 0RD |                       |
| B | 1LC | 1LC |                       |
| C | 0RA | 0LB |                       |
| D | 1RE | 1RD |                       |
| E | 0LG | 0LF |                       |
| F | 1LE | 1LF |                       |
| G | 0RH | 1LG |                       |
| H | 1RD | 1RI |                       |
| I | 1RZ | 1RA | I0 is the halt        |

The string is in tree normal form. With the state labels of the Coq proof of Jacobzheng's champion
(`BB9_champion_1RB1RA.v`), the same machine is `1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RH0RA_1LB1LF_1RZ1RE_1LI1LI_0RE0LH`,
started in state E. The renaming is E→A, H→B, I→C, A→D, B→E, F→F, C→G, D→H, G→I. In those labels it shares all of
A–D and F, and E1, G1 and I1, with the champion `1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_1LB0LH`. The
simulator of section 4.3 checks the renaming.

**Main facts.** N is the number of 1s on the tape when I reads 0. The halting transition writes a 1 on that 0, so the
standard score is σ = N + 1.

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms). |
| Exact score | Machine-checked formula: N = b₃ + 3, so σ = b₃ + 4, where b₃ is given by the recursion of section 1. It is not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_ω(f_ω(465009)) < N + 1 = σ. No upper bound is proved. |
| Earlier BB(9) record `1RB0RA_..._0LH1RZ` ([this folder](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_1RG1LD_0RH0RF_0RG0RE_0LH1RZ.txt)) | Beaten, machine-checked (`fw2_beats_record`). |
| Two later 9-state machines of this project (section 3.3) | Beaten, machine-checked (`fw2_beats_redir_0LA`, `fw2_beats_redir_0LA_fh`). |
| BB(9) champion of Jacobzheng (2024) | Beaten, machine-checked against its Coq-proved exact score (`fw2_beats_bb9_champion`). |
| BB(10) champion of Racheline (2024) | Beaten, machine-checked against a Coq-proved upper bound on its score (`fw2_beats_bb10_champion`). |
| n1 (BB10/, f_(ω+1)) | **Not** beaten. |
| Steps | Not computed. The first 49 are in the Coq proof. |

---

## 1. How it works

### 1.1 Notation

- `0^∞` is the blank part of the tape, and `x^n` is n copies of the word x.
- `<H` means state H with the head on the cell to its left.
- In the Coq files, `l {{q}}> r` has the head on the first cell of r, and `l <{{q}} r` has the head on the first cell
  of l. The left side l is listed outward from the head.
- Lists of digits are written top digit first. `0^k` is k zero digits, `2^m` is m digits 2, and `++` is
  concatenation.

"X → Y" below means that the machine goes from X to Y in at least one step (Coq's `-->+`), and "→*" allows zero
steps. All configurations, rules and functions are definitions and lemmas of
[`BB9_fw2_1RB0RD.v`](verify_fw2/multifile/BB9_fw2_1RB0RD.v).

### 1.2 The digit family

    Kd ds a b = 0^∞ <H 1^(b+1) 0 1^a 0 1^(d_1) 0 1^(d_2) 0 … 0 1^(d_n) 0^∞,      ds = [d_1; …; d_n]

The head reads the blank just left of the word. b is the **counter**, a the **accumulator**, and ds the list of
**digits**. Trailing zero digits are invisible on the tape: `Kd ds a b` and `Kd (ds ++ [0]) a b` are the same
configuration. The rules, proved for all parameters:

| Coq | rule | when |
|---|---|---|
| `KR1` | `Kd ds (a+1) b` → `Kd ds a (b+3)` | a > 0 |
| `KR2` | `Kd ((y+1) :: t) 0 b` → `Kd (y :: t) (b+2) 1` | a = 0, top digit > 0 |
| `KR3` | `Kd (0^(m+1) ++ (y+1) :: t) 0 (2(m+1) + s)` → `Kd (2^m ++ (s+2) :: y :: t) 2 1` | a = 0, top m + 1 digits 0 |
| `KR4O3` | `Kd 0^k 0 (4m+3)` → `Kd (2 :: trip m) 0 1` | all digits 0, b ≡ 3 (mod 4) |
| `KR4Ex` | `Kd 0^k 0 (2m)` →* `c_end m`, and I reads 0 there: the halt | all digits 0, b even |

Here `trip m` = `(0,1,2)^m (0,1,1)` is a list of 3m + 3 digits, and `c_end m` = `0^∞ (110)^m 1101 I> 0^∞` holds
2m + 3 ones. No rule covers an all-zero list with b ≡ 1 (mod 4); the run never meets that case.

`KR1`, `KR2` and `KR3` are the rules R1, R2 and R3 of Jacobzheng's champion, with the same statements
(`BB9_champion_1RB1RA.v`). There the end-of-list rules are different: the champion rebuilds a list of b + 2 digits
when b is even and halts when b is odd.

### 1.3 Clearing a digit: the functions U_j

The **depth** of a digit is the number of zero digits above it. Coq defines (`UX`, `U`, `X`)

    U_0(x) = 3x + 7,          U_(j+1)(x) = U_j^(x−2j)(X_j),
    X_0 = 7,                  X_(j+1) = U_j(U_j(X_j)),

where g^n is g applied n times. So U_1(x) = U_0^x(7), and X_1 = 91. The main lemma (`CDPx_all`) is: if B ≥ 2j, then

    Kd (0^j ++ v :: Us) 0 B   →*   Kd (0^(j+1) ++ Us) 0 (U_j^v(B)).

In words: a digit v at depth j is counted down to 0, and each unit applies U_j to the counter. By induction on j:
- At depth 0, `KR2` moves b + 2 into the accumulator, and b + 2 steps of `KR1` give the counter
  1 + 3(b + 2) = U_0(b) (`CHx`).
- At depth j + 1, `KR3` borrows one unit from the digit. It writes j digits 2 above it and the digit s + 2, where
  s = B − 2(j + 1), and two steps of `KR1` make the counter 7. Clearing the j digits 2 at depths 0, …, j − 1 gives
  the counter X_j (`BLKx`, `Yb_X`). Clearing the digit s + 2 at depth j then gives U_j^(s+2)(X_j) = U_(j+1)(B).

Coq also proves:
- U_j(x) ≥ x + 2j + 5 (`Ugrow`), which keeps the hypothesis B ≥ 2j true;
- U_j(x) ≡ x + 1 (mod 2) for x ≥ 2j (`Upar`): every application flips the parity of the counter;
- for j ≥ 2 and x ≥ 2j, U_j(x) ≡ 7 (mod 8) if x is even, and ≡ 0 (mod 8) if x is odd (`U_mod8`).

### 1.4 Clearing a rebuilt list

`KR4O3` turns the counter b = 4m + 3 into the list `2 :: trip m` and resets the counter to 1. Clearing it
(`clear_rebuilt`, `TRIP_ALL`):
- the top digit 2, at depth 0, takes the counter from 1 to U_0(U_0(1)) = 37;
- each triple (0, 1, 2) of `trip m` starts at some depth j: the 0 only adds one to the depth, the 1 applies
  U_(j+1) once, and the 2 applies U_(j+2) twice (`Tpre`);
- the final (0, 1, 1) applies U_(3m+2) and then U_(3m+3) (`Tv`).

So `Kd (2 :: trip m) 0 1` →* `Kd 0^(3m+4) 0 (Tv m 1 37)`. The last function applied is U_(3m+3), at depth
3m + 3 ≈ 3b/4. Since U_j grows like f_(j+1) (section 3.1), the new counter is about f_ω(3b/4).

### 1.5 Parity: why there are exactly three lists

Clearing `2 :: trip m` from the counter 1 applies U 3m + 4 times, so `Tv m 1 37` ≡ 1 + 3m + 4 ≡ m + 1 (mod 2)
(`Tv_par`). The mod-8 rule of section 1.3 gives more: if m is even, then the counter before the last two
applications is odd, U_(3m+2) sends it to 0 (mod 8), and U_(3m+3) sends that even number to 7 (mod 8) (`Tv_mod8`).

- **List 1.** The run reaches `Kd [0; 0] 0 b₁` with b₁ = U_1(10) = 620011 = 4·155002 + 3 (section 2).
- **List 2.** b₁ ≡ 3 (mod 4), so `KR4O3` builds `2 :: trip m₁` with m₁ = 155002, which is even. So
  b₂ = Tv m₁ 1 37 ≡ 7 (mod 8) (`b2_mod8`).
- **List 3.** b₂ ≡ 3 (mod 4) again, so `KR4O3` builds `2 :: trip m₂` with m₂ = ⌊b₂/4⌋. b₂ ≡ 7 (mod 8) makes m₂ odd.
  So b₃ = Tv m₂ 1 37 is even (`b3_even`).
- **Halt.** `KR4Ex` applies to the even b₃, and the machine halts with b₃ + 3 ones on the tape.

---

## 2. The run

| | configuration | how | Coq |
|---|---|---|---|
| 0 | blank tape, state A | | |
| 1 | `Kd [1; 1] 0 1`, at step 49 | 49 single steps | `init_reach` |
| 2 | `Kd [0; 1] 0 10`, at step 127 | the top digit 1 at depth 0: U_0(1) = 10 | `CDPx_all` |
| 3 | `Kd [0; 0] 0 b₁`, b₁ = U_1(10) = 620011 | the digit 1 at depth 1 | `run1` |
| 4 | `Kd (2 :: trip 155002) 0 1` | `KR4O3`, m₁ = 155002 | `step_cascade` |
| 5 | `Kd 0^465010 0 b₂`, b₂ = Tv 155002 1 37 | clearing list 2; the deepest digit is at depth 465009 | `clear_rebuilt` |
| 6 | `Kd (2 :: trip m₂) 0 1`, m₂ = ⌊b₂/4⌋ | `KR4O3` | `step_cascade` |
| 7 | `Kd 0^(3m₂+4) 0 b₃`, b₃ = Tv m₂ 1 37 | clearing list 3 | `clear_rebuilt`, `run3` |
| 8 | `c_end (b₃/2)`: I reads 0, the halt | `KR4Ex` | `run3`, `halt` |

The step numbers 49 and 127 come from the simulator of section 4.3; the 49 steps of `init_reach` are also in the Coq
proof, as `do 49 step`. In row 2, the configuration `Kd [10; 0] 0 7` comes next, at step 243 (`KR3`, then two `KR1`).
The simulator follows the literal run for 2·10⁸ steps; at that point it is still in row 3, with the digit 10 counted
down to 2. The total number of steps has not been computed.

---

## 3. The score

### 3.1 What Coq proves

From [`verify_fw2/multifile/BB9_fw2_bound.v`](verify_fw2/multifile/BB9_fw2_bound.v):

- `score_exact`: the halting configuration holds exactly b₃ + 3 ones. It is `c_end (b₃/2)`.
- `sigma_lower_bound`: the halting tape holds N ones with f_ω(f_ω(465009)) < N + 1.
- `sigma_lower_bound_strong`: the halting tape holds N ones, and there is a b (namely b₂) with
  2^465010 · f_ω(465009) ≤ b, b ≡ 7 (mod 8) and f_ω(3⌊b/4⌋ + 3) < N + 1. (The Coq statement writes the exponent as
  3·⌊b₁/4⌋ + 4 and 465009 as `465 * 1000 + 9`.)

The hierarchy is defined at lines 48–54: f_0(n) = n + 1, f_(k+1)(n) = f_k^n(n), f_ω(n) = f_n(n).

The proof of the bounds:
1. **U against f_j.** If 2^(j+1)·n ≤ z, then 2^(j+1)·f_(j+1)(n) ≤ U_j(z) (`Ubound`), and 2^(j+2)·(j + 1) ≤ X_j
   (`Xbound`).
2. **A rebuilt list.** For m ≥ 1, 2^(3m+4)·f_ω(3m + 3) ≤ Tv m 1 37 (`Tv_big`). The proof applies `Ubound` to the
   last applications of U, at depths 3m, 3m + 2 and 3m + 3; the last one gives at least f_(3m+4)(3m + 3) ≥
   f_ω(3m + 3).
3. **List 2.** ⌊b₁/4⌋ = 155002 (`b1_div4`), so b₂ ≥ 2^465010·f_ω(465009) (`b2_big`) and ⌊b₂/4⌋ ≥ f_ω(465009)
   (`b2_quarter`).
4. **List 3.** b₃ ≥ f_ω(3⌊b₂/4⌋ + 3) (`b3_big`). f_ω is monotone (`f_omega_mono`), so b₃ ≥ f_ω(f_ω(465009)), and
   σ = b₃ + 4 is larger.

### 3.2 How large

The following is on paper. The run applies an f_ω-sized clearing twice: list 2 reaches depth 465009, and list 3
reaches depth 3⌊b₂/4⌋ + 3 > 3·f_ω(465009). So σ is of order f_ω(f_ω(n)) for a modest n; Coq proves
σ > f_ω(f_ω(465009)), and we do not prove an upper bound. For comparison, f_(ω+1)(n) = f_ω^n(n), so
f_ω(f_ω(n)) < f_(ω+1)(n) for n ≥ 2. n1 (BB10/) has the proved lower bound f_(ω+1)((3T − 13)/7 − 2) with
T = 2↑^37 3, which is far larger.

### 3.3 Comparisons (machine-checked)

[`verify_fw2/multifile/BB9_fw2_vs_records.v`](verify_fw2/multifile/BB9_fw2_vs_records.v) compares fw2 with five
machines. Each theorem has the form

    exists c' N' c N,  c0 -[ tm' ]->* c' /\ halted tm' c' /\ ones' c' N' /\
                       c0 -[ tm ]->* c /\ halted tm c /\ ones c N /\ N' + 1 < N    (or N' + 1 < N + 1)

(for the 10-state champion, with the 10-state `evstep` and `halted`), where tm' is the other machine, imported from
its own Coq proof together with that proof's score theorem. So both
machines halt, with N' and N ones, and fw2 has more. The probe checks that the four 9-state `ones` predicates are the
same predicate. `N' + 1 < N` holds whichever convention one uses for the other machine's final write.

| machine | its score, as proved in Coq | fw2 wins by | theorem |
|---|---|---|---|
| `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_1RG1LD_0RH0RF_0RG0RE_0LH1RZ`, the earlier BB(9) record of this repository ([`verify/`](verify/), 2026-10-07) | N' = 3·(2↑^(12B−9) 8) + 108⌊B/5⌋ + 70 with 2B + 4 = 2↑^13 3 (`BB9_record_bound.score_closed`); about f_ω(6·2↑^13 3) | N' + 1 < N | `fw2_beats_record` |
| `1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LI0LC_1RG1LD_1LC0RH_1RG1LF_---0LA` (this project, 2026-10-08, not published before) | N' = 3·(2↑^(K+2) 5) + 10n + 6⌊K/5⌋ + 11 with K = 2n + 35, n = ⌊(12B+8)/5⌋, 2B + 4 = 2↑^37 3 (`BB9_redir_0LA_bound.score_closed`) | N' + 1 < N | `fw2_beats_redir_0LA` |
| `1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LI0LC_1RG1LD_1LC1RH_0LH0RF_---0LA` (this project, 2026-10-08, not published before) | N' + 12b = 3·(2↑^(K+42) 4) + 9u + 10(n − 3) + 100, same K and n (`BB9_redir_0LA_fh_bound.score_closed`) | N' + 1 < N | `fw2_beats_redir_0LA_fh` |
| `1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_1LB0LH`, Jacobzheng's BB(9) champion (2024) | exactly N' = b₂' + 3 (`BB9_champion_bound.score_exact`); f_ω(f_9(2)) < N' + 1 | N' + 1 < N + 1 | `fw2_beats_bb9_champion` |
| `1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_0LF0LJ_1LH0LJ`, Racheline's BB(10) champion (2024) | N' + 1 ≤ 2↑^P (2P) for some P ≤ 2↑^25 49 (`BB10_champion_upper.champion_upper_ex`); f_ω(f_ω(25)) < N' + 1 | N' + 1 < N + 1 | `fw2_beats_bb10_champion` |

Here 2↑^k n is Knuth's up-arrow (`arrow k 2 n` in Coq). The proofs bound each rival by an expression
2↑^K x ≤ f_(K+1)(x) ≤ f_ω(m) with K, x ≤ m ≤ f_ω(465009) (`f_arrow_ge`, `arrow_le_fo`), and then use
σ > f_ω(f_ω(465009)).

- **The earlier BB(9) record.** `1RB0RA_..._0LH1RZ` (this folder, [write-up](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_1RG1LD_0RH0RF_0RG0RE_0LH1RZ.txt),
  [`verify/`](verify/)) is superseded by fw2. Its files stay here unchanged, as history.
- **The two `---0LA` machines** come from our BB(8) record ([`../BB8/`](../BB8/)). The first is that record with its
  halt E0 redirected to 0LI and a new state I (I1 = 0LA), which restarts the BB(8) program on a re-encoded list. The
  second is a sibling that also changes G1, H0 and H1. Their Coq proofs were written in this project on
  2026-10-08 and were not published before. They are included in `verify_fw2/multifile/` because the comparison
  imports them. On paper both are roughly f_ω(2.4·2↑^37 3): single f_ω, like the record.
- **Jacobzheng's BB(9) champion.** The wiki "Champions" table lists it with σ > f_ω(f_9(2)). Its Coq proofs are the
  ones of [`verify/`](verify/), unchanged.
- **Racheline's BB(10) champion.** The wiki lists it with σ > f_ω(f_ω(25)). It is a 10-state machine of the same
  family as Jacobzheng's champion. For BB(10), n1 already beats it (BB10/). fw2 beats it with one state fewer. The
  upper bound `BB10_champion_upper.v` was written in this project and is published here for the first time; the other
  BB(10) champion files are the ones of [`../BB10/verify/`](../BB10/verify/), unchanged.
- **n1** (BB10/) is not beaten (section 3.2), and neither is T12a (BB12/) nor the BB(13)/BB(14) machines.

---

## 4. Verification

### 4.1 What Coq proves

The development is in [`verify_fw2/multifile/`](verify_fw2/multifile/). It uses Coq 8.20.1 on top of
[busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`). The logical path `BB8` is historical.

| statement | Coq name | file |
|---|---|---|
| fw2 halts from the blank tape | `halt` | `BB9_fw2_1RB0RD.v` |
| the rules and runs of sections 1–2 | `KR1`, `KR2`, `KR3`, `KR4O3`, `KR4Ex`, `CDPx_all`, `TRIP_ALL`, `clear_rebuilt`, `init_reach`, `run1`, `step_cascade`, `run3` | `BB9_fw2_1RB0RD.v` |
| the parities of section 1.5 | `Upar`, `U_mod8`, `Tv_par`, `Tv_mod8`, `b1_mod8`, `b2_mod8`, `b3_even` | `BB9_fw2_1RB0RD.v` |
| the halting tape holds b₃ + 3 ones | `score_exact` | `BB9_fw2_bound.v` |
| f_ω(f_ω(465009)) < N + 1, and the strong form | `sigma_lower_bound`, `sigma_lower_bound_strong` | `BB9_fw2_bound.v` |
| fw2 beats the five machines of section 3.3 | `fw2_beats_record`, `fw2_beats_redir_0LA`, `fw2_beats_redir_0LA_fh`, `fw2_beats_bb9_champion`, `fw2_beats_bb10_champion` | `BB9_fw2_vs_records.v` |

The three fw2 files are Argon's, unchanged: `BB9_fw2_1RB0RD.v` (813 lines), `BB9_fw2_bound.v` (368 lines, imports the
halting file unchanged and restates the transition table as `tm_table`) and `BB9_fw2_vs_records.v` (287 lines). The
other 16 files are the dependency closure of the comparison file; [`verify_fw2/README.md`](verify_fw2/README.md)
lists them and where each comes from.

`compile_clean.sh` rebuilds the files from scratch and runs two probes. Stage 1 compiles the four files of the
halting proof and the bounds (38 s in the recorded build) and runs `probe.v`. Stage 2 compiles the comparison
file and its other 15 dependencies (1 h 43 min with `PAR=1` in the recorded build; three of them are large generated halting proofs) and runs
`probe_vs.v`. The probes:

- check all 18 entries of fw2's transition table by conversion, against lines generated from the machine string
  (I0 is `None`), and the same for the 92 entries of the five machines of section 3.3; check that the start
  configuration is the blank tape in state A;
- print the definitions the statements use (`iter`, `f`, `f_omega`, `ones`, `U`, `Tv`, `b1`, `b2`, `b3`, …), and
  check that the 9-state `ones` predicates of the compared files are one and the same;
- run `Print Assumptions` on the four main theorems (`probe.v`) and the five comparisons (`probe_vs.v`). All nine
  report "Closed under the global context".

The GitHub workflow (job `bb9-fw2`) runs stage 1 and `probe.v` whenever its files change (and weekly). Stage 2 takes hours and, like BB10/
and BB12/, is not run in CI; it was checked locally from scratch, and the logs of that build (both stages) are in
`verify_fw2/multifile/`.

**Re-checked here**, besides that build:
- `check.py`, our mechanical reviewer for busycoq proofs, passes on the halting proof. It compiles the file, checks
  the Coq transition table against the machine string, checks the theorem statement, and requires `Print Assumptions`
  to report no axioms.
- A separate `Print Assumptions` probe on all the theorems above, in the development where Argon's files were first
  checked, reported no axioms.

### 4.2 Not machine-checked

- **σ = N + 1.** In Coq the halting transition is `None`, and `ones` counts the 1s of the halted configuration. The
  extra 1 written by I0 = 1RZ is the standard convention.
- **The size estimates** of section 3.2, and the comparison with n1 (not beaten, on paper).
- **The step numbers** of section 2, except the 49 of `init_reach`. They come from simulation.
- **The wiki's bounds** for the two champions, quoted in section 3.3. The comparisons themselves use the Coq-proved
  scores, not the wiki's numbers.

### 4.3 Independent checks

[`tools/fw2_writeup_chk.py`](tools/fw2_writeup_chk.py) is a cell-by-cell simulator written for this write-up. It shares
no code with the Coq files. It exits nonzero on any failure. Result (2026-10-16, about 90 seconds): **ALL PASS**.

| check | instances |
|---|---|
| the champion-label form, renamed, is the tree-normal-form string; 13 of 18 transitions shared with Jacobzheng's champion | 1 |
| the blank tape is `Kd [1; 1] 0 1` at step 49 | 1 |
| `KR1`, `KR2` (random digit lists, a and b) | 60 each |
| `KR3` (m ≤ 5, y ≤ 5, s ≤ 20) | 80 |
| `KR4O3` and `KR4Ex` (k ≤ 3, m ≤ 24), with exactly 2m + 3 ones at the halt | 100 each |
| U_1(10) = 620011 = 4·155002 + 3 and X_1 = 91, from the recursion of section 1.3 | 2 |
| 60 small starts: every later visit to the Kd family is the configuration the rules predict, and each halt comes where `KR4Ex` predicts, with its ones count | 49,101 Kd visits |
| the real run from step 49 to step 200,000,049: every visit to the Kd family is the configuration the rules predict | 12,319 Kd visits |
| every defined transition is read | 1 |

The simulator only checks this description against the machine. The proof does not depend on it.

---

## 5. Discovery and credit

- **Found** by Argon, a Google Gemini model, run by the repository owner in Google's Antigravity on 2026-10-15.
- **Proved** by Argon: the three Coq files `BB9_fw2_1RB0RD.v` (`halt`), `BB9_fw2_bound.v` (`score_exact` and the
  hierarchy bounds) and `BB9_fw2_vs_records.v` (the five comparisons). They are published unchanged.
- **Re-checked** independently here (section 4): `check.py`; a from-scratch compile with two probes and
  `Print Assumptions`; the simulator of section 4.3. This write-up was written here.
- **Built on** Jacobzheng's 2024 BB(9) champion: the same digit family, the same counting rules R1–R3 and 13 of its
  18 transitions (section 1.2).
- **The compared machines' proofs** were written in this project before fw2 (section 3.3, and
  [`verify_fw2/README.md`](verify_fw2/README.md)).
