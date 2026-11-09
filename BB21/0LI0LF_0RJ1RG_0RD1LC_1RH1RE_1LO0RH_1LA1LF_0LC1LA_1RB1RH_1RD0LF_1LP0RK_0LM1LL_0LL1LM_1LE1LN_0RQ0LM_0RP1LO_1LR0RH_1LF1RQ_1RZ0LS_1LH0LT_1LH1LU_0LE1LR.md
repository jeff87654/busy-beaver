# B21: Racheline's BB(21) champion, an ω²-class machine (halting proved)

    0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LR

Found by Racheline (the BB(21) row of the bbchallenge wiki's
[Champions](https://wiki.bbchallenge.org/wiki/Champions) page, "Racheline in 2024", checked 2026-11-08, which gives
the lower bound f_(ω²)^2(4↑↑341) and marks it "Not independently verified"). The analysis and the Coq proof below
are this project's. All 41 non-halting slots are used.

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB21_B21.halt`. It halts at the sixth refill. The halt is decided by a residue schedule (the refill accumulator mod 4, section 2), computed exactly in the proof. |
| Score | Machine-checked: the halting tape holds N ones with 4↑↑341 < N (`sigma_lower_bound`; 4↑↑0 = 1, 4↑↑(n+1) = 4^(4↑↑n)). The halt R0 = `1RZ` is read on a 0 and writes 1, so σ = N + 1. |
| Level | **Not proved here.** The wiki's bound f_(ω²)^2(4↑↑341) is not a theorem of this repository; only 4↑↑341 < N is. On paper (section 4, an argument, not a Coq lemma) the machine is f_(ω²)-class. |
| Comparisons | Its *proved* bound is far below the proved bounds of R18a (BB(18)) and J20 (BB(20)), so BB(21) ≥ BB(20) + 1 is the better proved bound for BB(21). On paper it is far above both (ω² against ω·2). Not yet reviewed by the bbchallenge community. |
| Steps | Not computed. σ is at most the number of steps, so the bound on σ is a bound on the steps too. |

## 1. How it works

The tape at an **A boundary** (state A at the left end, facing left) is a list of blocks

    0^∞ <A B0 00 B1 00 B2 ...

and a block is a list of digits written as runs of 1s separated by single 0s ([3, 1, 2] is 111 0 1 0 11). An **E**
block has only digits 1 and length ≥ 2; **P** is the lone block [1]. From an A boundary, one sweep runs:

- **the level-1 engine** on B0 (states at the left end; `CA_E0`, `CA_E1`, `LV`, `Chain`, `CA_exit`). It leaves B0 as
  digits 1 and hands the accumulator A + 3 to state J, where A is given by the level maps
  h_0(x) = x + 4, h_(m+1)(x) = h_m^(x+3)(1) (a digit at position m + 2 of B0 is reduced through h_m). If B0 is
  already all 1s, its first digit is stripped and J starts with accumulator 4.
- **J walks right.** It strips the first digit of each E block it crosses (accumulator + 2 each) and acts on the
  first block T that is not an E (`J_E_raw`, `J_dec_raw`, `J_est0_raw`, `J_est1_raw`, `J_P_raw`):

| T | action |
|---|---|
| [w ≥ 2, ...] | w − 1; the block X(acc) is appended to the block just left of T |
| [1, tail], tail not all 1s | one engine step inside T, starting from acc − 1 |
| P, next block [2] | T becomes X(acc + 2); that [2] becomes the new P |
| P at the right end | **the refill** (below) |

  with X(4) = [5], X(6) = [4, 2], X(2k + 2) = [4, 1^(k−2), 2]. Then the head walks back to the A boundary (`RW`).

- **The refill** (`refill_halt`, `refill_cont`; R, S, T, U rewrite the last block from the right with period 4,
  `zigRSTU`). With x the accumulator after absorbing the final P: x ≡ 0 (mod 4): R reads a 0 and halts (R0 = `1RZ`).
  x ≡ 2 (mod 4): ",4,1" is appended to the last remaining block and (x − 2)/4 lone [2] blocks are added, which starts
  the next phase.

`BB21_B21_absdef.v` writes these rules as an abstract step function `astep` on block lists, and `BB21_B21_sim.v`
proves that the machine simulates it (`astep_sim`, `halts_from`). The boot reaches the A boundary [1, 1, 4, 1, 2] 00 [1]
after 162 steps (`boot`).

## 2. The run, and why it halts

A phase starts with a list that ends in N lone [2] blocks behind a P. The marker P walks through the 2s; each time,
the block X(acc + 2) it leaves behind is processed at that depth, with the in-block engine at the next level. Inside
a phase every sweep lowers an ordinal-valued measure of the block list, so the phase ends at [E^(N−1), P], and the
final sweep absorbs all N items: x_p = J + 2, where J is the accumulator of that sweep.

**Lemma D (dominance).** That picture needs a fact that simulation cannot check: no E block is stripped down to P
inside a phase and B0 never empties, so that the sweep only ever meets the shapes of the table. The paper argument
for it had a gap (deep engine exits are not monotone in time). The Coq proof replaces it with an explicit invariant
`INV` (`BB21_B21_inv.v`): length conditions between neighbouring blocks (|L| ≥ 2·lead1(R) + 2), a shape condition
on B0, and a growth bound on every block above the frontier in terms of B0, with the gap lemma `GAP`. Every
transition preserves `INV` (`inv_est`, `inv_dec_es`, `inv_dec_b0`, `inv_compl`, `inv_P`, `inv_refill`), and
`proc` (`BB21_B21_proc.v`, nested induction on the depth and a reverse-lexicographic order) processes a whole
frontier block under it.

**The residue schedule** (`BB21_B21_run.v`). Every level map h_m with m ≥ 2 has values ≡ 17 (mod 64) (`h_mod64`), and the
J accumulator at the end of a phase is exactly 64q + 20 + 2·(number of E blocks). Tracking that count mod 8 through
the phases gives N_4 = 16a + 5 and E counts 16a + 4, 24a + 16q_4 + 10, 36a + 24q_4 + 16q_5 + 19 at the ends of phases
4, 5, 6. So the final accumulators J are ≡ 0, 0, 2 (mod 4): refills #4 and #5 continue, and at refill #6,
x = J + 2 ≡ 0 (mod 4): the machine halts (`abstract_halt`, `halt`). The same schedule in 2-adic form, with the deep
exit d = −4/3 and N_(p+1) = N_p − 1 + (x_p − 2)/4:

| refill | phase | N_p (2-adic) | x_p = d + 2N_p | x_p mod 4 | result |
|---|---|---|---|---|---|
| #1, #2 | boot | | 3, 5 | 3, 1 | continue (on the literal machine) |
| #3 | 3 (the boot list) | 1 | 2/3 | 2 | continue |
| #4 | 4 | −1/3 | −2 | 2 | continue |
| #5 | 5 | −7/3 | −6 | 2 | continue |
| #6 | 6 | −16/3 | −12 | 0 | **halt** |

The halt does not depend on a residue class the proof leaves open: the machine halts at refill #6 deterministically.

**Score** (`BB21_B21_score.v`). The halting tape holds N ≥ J/2 ones, J ≥ (number of E blocks) ≥ J_3/2 − 10, and
J_3 = h_3(h_1³(1)) + 3 = h_2^340(1) + 3 ≥ 64·4↑↑341 (`jacc_s3`, `J3_tet`; h_1(x) = 4x + 13, h_1³(1) = 337), so
4↑↑341 < N (`sigma_lower_bound_tet`). An exact formula for N
is built inside the proof but not exported; there is no closed form.

## 3. Verification

[`verify/`](verify/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about 2 minutes (13 files), built in CI
(job `bb13-bb14`). `BB212.v` and `Individual212.v` instantiate busycoq for 21 states (new here). `probe.v` re-checks
the transition table entry by entry against the string above (42 checks generated from the string) and the blank
start configuration. It prints the definitions the statements use and confirms that `halt`, `sigma_lower_bound`
and the abstract-machine theorem `BB21_B21_run.abstract_halt` are closed under the global context. The proof also
passes this project's `check.py` (extended to 21 states), 2026-11-08.

[`tools/b21_writeup_chk.py`](tools/b21_writeup_chk.py) simulates the machine string (exactly, jumping only over
same-state runs), without the Coq files (about 30 s). It checks:

1. 1200 random sweeps against the table of section 1 (0–5 E blocks, all four target shapes, accumulators up to 120);
2. the level-1 engine on 300 random B0 lists (exit accumulator A + 3 from the h recursion);
3. the final sweep and refill on 24 cases (both classes of the accumulator mod 4);
4. 9 large cases: the refill, then the next phase sweep by sweep (up to 151 sweeps) until its first deep engine run;
5. the boot (the A boundary [1, 1, 4, 1, 2] 00 [1] after 162 steps);
6. the residue schedule above (mod 2^64): refills #3 to #5 continue, #6 halts.

These checks cover the rules, not Lemma D; Lemma D holds only because the run's block lengths are astronomically
separated, and it is proved in Coq, not by simulation.

## 4. Size and comparisons

- **Proved:** 4↑↑341 < N, σ = N + 1. This is far below R18a's proved f_(ω·2)(f_ω(f_ω(f_10(2)))) (BB(18),
  [`../BB18/`](../BB18/)) and J20's proved f_(ω·2)(f_(ω+2)^2(f_10(2))) (BB(20), [`../BB20/`](../BB20/)), so for now
  BB(21) ≥ BB(20) + 1 is the better proved bound for BB(21). It is even below BB(7)'s proved 3↑^20 3 (> 3↑↑↑3 > 4↑↑341).
- **On paper only** (an argument, not a Coq lemma): a phase that starts with N lone [2] blocks has block ordinal about
  ω^(ω·N); the rules follow the fundamental sequences, so the accumulator at the end of phase p is at least about
  f_(ω·N_p)(N_p) = f_(ω²)(N_p), and N_(p+1) ≈ x_p/4. With three big phases this gives roughly f_(ω²)^3(4↑↑340), which
  is above the wiki's f_(ω²)^2(4↑↑341). A formal version needs a quantitative form of `proc` and FGH transfer lemmas;
  it is not done.
- If that argument is right, B21 is far above R18a and J20 (ω² against ω·2), but no Coq lemma says so.
- Not yet reviewed by the bbchallenge community.

## Credit

Machine by Racheline, listed as the BB(21) champion on the bbchallenge wiki's Champions page (with the bound
f_(ω²)^2(4↑↑341), "Not independently verified"). This project (the repository owner with Claude models (Anthropic)
as agents) worked out the block rules and the residue schedule, found and closed the gap in the dominance argument
(Lemma D, as the invariant `INV`), and wrote the Coq proof (2026-11-08), the 21-state busycoq setup, the probe, the
checker and this write-up. The proof confirms that the machine halts, with σ > 4↑↑341; the wiki's f_(ω²) bound remains
unverified.
