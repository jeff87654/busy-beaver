# R18a: an 18-state machine at level f_(ω·2), derived from Jacobzheng's J20

    1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_0LQ0LO_1LR1LP_0LQ1LN_0RO1LB_0LL1RZ

|   | 0   | 1   |                                                                              |
|---|-----|-----|------------------------------------------------------------------------------|
| A | 1LH | 0LG | engine: A1 erases the first cell of a digit ≥ 2 (J20's)                      |
| B | 0LI | 1RC | engine: B0 = end of the list, B1 = next digit (J20's)                        |
| C | 0LD | 1LA | engine: C0 = digit 1 (pass), C1 = digit ≥ 2 (J20's)                          |
| D | 0RE | 1LD | engine: walk left over a passed digit (J20's)                                |
| E | **0RH** | 1RL | E1 splits a cell off the head (engine); E0 starts the refill, keeping the gap |
| F | 1RB | 1RF | engine: the sweep state, walks right over the accumulator (J20's)            |
| G | 1LA | 1LG | engine: walk back (J20's)                                                    |
| H | 1RF | 1RM | left end: H0 = inner list (new sweep), H1 = marker: expansion or refill      |
| I | 1LJ | 1LI | end of a list: merge it into one block (J20's)                               |
| J | 0LK | 1LI | end of a list (J20's)                                                        |
| K | 1RL | 1RE | K0 writes the marker (outer boundary), K1 = outer list exhausted (J20's)     |
| L | 0RL | 0RF | start of a sweep (J20's)                                                     |
| M | 0LN | 1RM | walk right over the block (expansion and refill)                             |
| N | **0LQ** | 0LO | rewrite the block from the right, period 3; N0 exits into Q              |
| O | **1LR** | 1LP | rewriter; O0 exits into R                                                |
| P | **0LQ** | 1LN | rewriter; P0 exits into Q                                                |
| Q | 0RO | 1LB | exit dispatch: Q0 = blank (expansion, back to F), Q1 = marker (refill)       |
| R | 0LL | 1RZ | exit dispatch: R0 = blank (expansion, back to F), R1 = marker: the halt      |

This project's machine (2026-11-07), derived from Jacobzheng's 20-state machine J20 ([`../BB20/`](../BB20/), the
bbchallenge wiki's BB(20) champion). Rows A–P are J20's except the four slots in bold. J20's four refill states Q, R,
S, T are deleted. Their rewriter was the same keep/keep/erase cycle as J20's expansion rewriter N, O, P, so the
refill now reuses the expansion's walker M and rewriter N, O, P. Two new dispatch states Q and R tell the two modes
apart at the rewriter exit. In a refill, E0 = `0RH` keeps the far-left marker one cell further left, so the exit
reads the marker; in an expansion it reads the blank. That saves 2 states and keeps J20's f_(ω·2) class. All 35
non-halting slots are used.

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB18_R18a.halt`. The halt is decided by a residue mod 3, which the proof computes exactly (section 2), as for J20: every level map is x ↦ x + 1 (mod 3). |
| Exact score | Machine-checked formula: the halting tape holds 2c + 2 ones, where G³(28) + 8 = 3(k + 1), a₂ = hoc_2^k(28) and a₂ + 2(k + 2) + 2 = 3c + 1, for J20's recursion G, ho, hoc (section 1; `score_exact`). The halt R1 = `1RZ` is read on a 1 and writes 1, so σ = N = 2c + 2. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω·2)(f_ω(f_ω(f_10(2)))) < N = σ (`sigma_lower_bound`). |
| Comparisons | **Machine-checked** (Coq, `beats_J19`, `beats_M18_229`): N is above J19's proved BB(19) bound f_(ω+7)(f_(ω+7)(5)) and above M18_229round's proved BB(18) bound f_(ω+3)^229(9). Those are comparisons with the other machines' proved lower bounds; neither machine has a proved upper bound. Section 4. Not yet reviewed by the bbchallenge community. |
| Steps | Not computed. σ is at most the number of steps (each step writes at most one new 1), so the bound on σ is a bound on the steps too. |

## 1. How it works

Lists are blocks of 1s separated by single 0s: [a, b, c] is 1^a 0 1^b 0 1^c. As in J20, the tape holds an **inner**
list at the left end and an **outer** list, and one sweep engine (states A–H, L) runs both; a marker (a single 1 at
the far left) says which list is being swept. The Coq file uses J20's configurations:

    inner:  CI x [d2, ..., dn] R  =  0^∞ [H] 1^x 0 1^d2 0 ... 0 1^dn 0 0 R        (H on the blank left of the list)
    outer:  CO a [o1, ..., om]    =  0^∞ 1 0 0 [F] 1^a 0 1^o1 0 ... 0 1^om 0^∞     (F on the outer accumulator)

The inner list, the expansion and the outer rounds R0 and R1 are J20's, with the same functions (`CI_E0`, `CI_E1`,
`CI_exit`, `EXP`, `R0`, `R1`, `LV_in`, `LV_out`, `Chain_in`, `Chain_out`):

    inner level maps   h_0(x) = x + 4,  h_(m+1)(x) = h_m^(x+2)(2)            (position m+2 is f_m-class)
    outer head map     G(a) = hc_1^(a div 3)(a mod 3 + 3) + 2(a div 3) + 4    (f_ω-class; G(0..5) = 7, 8, 9, 28, 32, 36)
    outer level maps   ho_0 = G,  ho_(m+1)(a) = ho_m^(a+1)(3)                 (outer level m is f_(ω+m)-class)
    hoc_m^0(a) = a,  hoc_m^(n+1)(a) = hoc_(m+1)^n(ho_m(a))                    (n digits 2 at levels m, m+1, ...)

    R0   CO a [e+2, r]           →*  CO G(a) [e+1, r]
    R1   CO a [1^(p+1), e+2, r]  →*  CO 3 [1^p, a+2, e+1, r]
    EX   CO a [1^n]              →*  the merged block of T = a + 2n + 2 cells, and the refill

The only change is at the rewriter's exit. In an **expansion**, N0, P0 = `0LQ` and O0 = `1LR` read the blank left of
the block, and Q0 = `0RO` or R0 = `0LL` continues to F exactly where J20's `0RF` exits did (`EXP`, three residue
cases). In a **refill** (K1 = `1RE`, E0 = `0RH`, H1 = `1RM`; `OEX`, `SW_exit_out`), M walks to the right end of the
merged block and N, O, P rewrite it from the right with period 3 (`triNOP`), with the gap and the marker on its left.
The exit then reads the marker (`RF_halt`, `RF_A`, `RF_B`):

| T | result |
|---|---|
| 3c + 1 | O0 writes the gap's 1 and R reads the marker: R1 = `1RZ`, the halt, with 2c + 2 ones on the tape |
| 3k + 2 | Q1 = `1LB`: the outer list CO 0 [1, 1, 2^k] |
| 3k | Q1 = `1LB`: the outer list CO 0 [1, 2^k] |

## 2. The run, and why it halts

| phase | what runs | result |
|---|---|---|
| boot | 13 steps from the blank tape | CO 3 [] (`boot`) |
| exhaustion 1 | EX: T = 3 + 2 = 5 = 3·1 + 2 | refill: CO 0 [1, 1, 2] |
| two R1 rounds | R1, R1 | CO 3 [1, 2, 1], then CO 3 [5, 1, 1] |
| first digit | `LV_out` at level 0 on the digit 5: four R0 rounds | CO a₁ [1, 1, 1], a₁ = G⁴(3) = G³(28) |
| exhaustion 2 | EX: T = a₁ + 8 = 3(k + 1) | refill: CO 0 [1, 2^(k+1)] |
| R1, R0 | R1, then R0 with G(3) = 28 | CO 3 [2, 1, 2^k], then CO 28 [1, 1, 2^k] |
| the long part | `Chain_out` on the k twos at levels 2, ..., k + 1 | CO a₂ [1^(k+2)], a₂ = hoc_2^k(28) |
| exhaustion 3 | EX: T = a₂ + 2(k + 2) + 2 = 3c + 1 | R1 is read: halt, 2c + 2 ones (`run_gen`, `run`, `halt`) |

**The mod-3 invariant** is J20's: every level map is x ↦ x + 1 (mod 3) (`h_P1`, `G_P1`, `ho_P1`), so
hoc_m^n(a) ≡ a + n (`hoc_mod`). Hence a₁ = G³(28) ≡ 28 + 3 ≡ 1 and T = a₁ + 8 ≡ 0 at the second exhaustion
(`K_gen`); then a₂ ≡ 28 + k and T = a₂ + 2k + 6 ≡ 1 at the third (`C_gen`): the halt. No residue depends on anything
the proof does not compute, so the machine halts after exactly two refills.

The halting tape is 0^∞ [R on the marker 1] 1 0 (1 1 0)^c 0^∞: 2c + 2 ones (`ones_Hh`, `score_exact`), and R1 writes
a 1 on a 1, so σ = 2c + 2.

**Size** (`BB18_R18a.v`, sections "Lower bounds for the machine's hierarchy" and "Final bound"). J20's transfer
lemmas carry over (`h_dom`, `G_dom`, `ho_dom`, `hc_tower`). G(28) ≥ hc_1^9(4) ≥ 8 f_10(2) (`G28`), and two more
applications of `G_dom` give k + 1 ≥ 2Y with Y = f_ω(f_ω(f_10(2))). The last step of the chain is
a₂ = ho_(k+1)(hoc_2^(k−1)(28)) (`hoc_last`), so `ho_dom` gives a₂ ≥ 6 f_(ω+k+1)(k + 1) = 6 f_(ω·2)(k + 1), and
N = 2c + 2 > f_(ω·2)(Y) (`bound_gen`, `sigma_lower_bound`).

## 3. Verification

[`verify_r18a/`](verify_r18a/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about 30 s, built in CI (job
`bb13-bb14`). `probe.v` re-checks the transition table entry by entry against the string above (36 checks generated
from the string) and the blank start configuration. It prints the definitions the statements use and confirms that
`halt`, `score_exact`, `sigma_lower_bound`, `beats_J19` and `beats_M18_229` are closed under the global context.
The proof also passes this project's `check.py` (the statement `halts tm c0` read from the file, the table compared
with the machine string, `Print Assumptions halt` closed), 2026-11-08.

[`tools/r18a_writeup_chk.py`](tools/r18a_writeup_chk.py) simulates the machine string (exactly, jumping only over
same-state runs), without the Coq files (about 10 s). It checks:

1. exhaustion and refill of CO a [1^n] for a = 0..79, n = 0..6: the three cases of the table above, and the number
   of ones at the halt (560 cases);
2. 400 random R1 rounds;
3. R0 for heads a = 0..5 against G computed from the Coq file's recursion, and G(a) ≡ a + 1 (mod 3) for a = 0..8;
4. the run from the blank tape: its outer boundaries are CO 3 [] (after 13 steps), CO 0 [1, 1, 2], CO 3 [1, 2, 1],
   CO 3 [5, 1, 1] and CO 28 [4, 1, 1] (the next one needs G(28)), as in the table of section 2, and the machine does
   not halt in the next 3·10^6 macro steps (2.2·10^11 steps).

## 4. Comparisons

- **In Coq**: `beats_J19` (f_(ω+7)(f_(ω+7)(5)) < N, J19's proved bound, [`../BB19/`](../BB19/)) and `beats_M18_229`
  (f_(ω+3)^229(9) < N, M18_229round's proved bound, below). Both follow from Y ≥ 2048 (`Y_big`), since
  f_(ω·2)(Y) = f_(ω+Y)(Y). They compare R18a with the other machines' proved lower bounds; neither J19 nor
  M18_229round has a proved upper bound.
- So BB(19) ≥ BB(18) + 1 > f_(ω·2)(f_ω(f_ω(f_10(2)))) is the better proved bound for BB(19) too.
- On paper: the same argument puts N above the bbchallenge wiki's BB(18) bound f_(ω+4)(228) (M18_229round's row,
  checked 2026-11-08): f_(ω·2)(Y) = f_(ω+Y)(Y) ≥ f_(ω+4)(Y) ≥ f_(ω+4)(228).
- J20 (20 states) stays above R18a: its proved f_(ω·2)(f_(ω+2)^2(f_10(2))) is above R18a's proved
  f_(ω·2)(f_ω(f_ω(f_10(2)))), since f_(ω+2)(n) ≥ f_ω(n) and f_(ω·2) is increasing. On paper the scores are ordered the
  same way: both are about f_(ω·2)(k), where J20's k is at least f_(ω+2)^2(f_10(2)) and R18a's k is of the order of
  f_ω(f_ω(f_10(2))).
- Not yet reviewed by the bbchallenge community.

## Credit

This project (the repository owner with Claude models (Anthropic) as agents) found R18a on 2026-11-07, by a search
for an 18-state compression of Jacobzheng's J20 (the refill merged into the expansion rewriter), and wrote the Coq
proof `BB18_R18a.v` (an adaptation of this repository's J20 proof `BB20_JZ20.v`), the probe, the checker and this
write-up. The two-list design, the engine, the expansion and the mod-3 schedule are Jacobzheng's, from J20.
