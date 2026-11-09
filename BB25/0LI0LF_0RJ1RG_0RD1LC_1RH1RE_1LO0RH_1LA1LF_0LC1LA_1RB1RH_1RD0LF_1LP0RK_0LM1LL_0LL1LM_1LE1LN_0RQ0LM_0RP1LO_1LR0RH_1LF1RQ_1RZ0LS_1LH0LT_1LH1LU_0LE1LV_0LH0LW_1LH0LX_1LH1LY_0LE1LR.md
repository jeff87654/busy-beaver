# W2PR: a 25-state machine built on Racheline's B21, with five ω² phases instead of three

    0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LV_0LH0LW_1LH0LX_1LH1LY_0LE1LR

This project's machine (2026-11-07), built on Racheline's B21 ([`../BB21/`](../BB21/), the bbchallenge wiki's BB(21)
champion). Rows A–T are B21's. U1 is changed from `1LR` to `1LV`, and V, W, X, Y are a copy of B21's refill cycle
R, S, T, U, except V0 = `0LH` where R0 is the halt:

|   | 0   | 1   |                                                                              |
|---|-----|-----|------------------------------------------------------------------------------|
| U | 0LE | **1LV** | B21's U, but the cycle continues into the copy V, W, X, Y              |
| V | **0LH** | 0LW | copy of R; V0 continues (where R0 halts)                               |
| W | 1LH | 0LX | copy of S                                                                    |
| X | 1LH | 1LY | copy of T                                                                    |
| Y | 0LE | 1LR | copy of U (back to R)                                                        |

B21's refill rewrites the final block from the right with the period-4 cycle R, S, T, U and decides the halt by the
accumulator mod 4. With the copy, the cycle has period 8, so the refill decides by the accumulator mod 8: it halts
only in one class mod 8 and continues, through V, in the other class that B21 halts on. Until B21's halting refill
(#6), the two machines run step for step alike, with V, W, X, Y in place of R, S, T, U on alternate passes of the
cycle. W2PR passes refills #6 and #7 and halts at refill #8, after five big ω² phases instead of three. All 49 non-halting
slots are used.

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB25_W2PR.halt`. It halts at the eighth refill. The halt is decided by a residue schedule (the refill accumulator mod 8, section 2), computed exactly in the proof. |
| Score | Machine-checked: the halting tape holds N ones with Fh⁵(4↑↑341) < N, where Fh(n) = h_n(0) is the engine's level map at 0 (`sigma_lower_bound`; h_0(x) = x + 4, h_(m+1)(x) = h_m^(x+3)(1), as in B21). Fh is f_ω-class, so this is roughly f_ω^5(4↑↑341). The halt R0 = `1RZ` is read on a 0 and writes 1, so σ = N + 1. |
| Level | **On paper only** (an argument, not a Coq lemma): about f_(ω²)^5(4↑↑340), two f_(ω²) phases above B21. |
| Comparisons | Its proved bound is above B21's first published bound 4↑↑341, but below the proved bounds of R18a (BB(18)), J20 (BB(20)) and B21's ω² bound f_(ω²)^3(4↑↑341) (BB(21), `../BB21/verify_w2/`), so BB(25) ≥ BB(21) + 4 is the better proved bound for BB(25). W2PR's own ω² bound is not proved yet. On paper it is far above both, and above B21; the wiki's Champions table has no rows between BB(21) and BB(29) (checked 2026-11-08). Not yet reviewed by the bbchallenge community. |
| Steps | Not computed. σ is at most the number of steps, so the bound on σ is a bound on the steps too. |

## 1. How it works

Everything up to the refill is B21's: the block list at an A boundary, the level-1 engine on B0, the J sweep with its
four actions, the marker P walking through the lone 2s, and the dominance invariant `INV`. See B21's write-up. The
Coq proof reuses B21's machine-independent layers unchanged (section 3).

**The refill** (`BB25_W2PR_tm.v`: `zig8`, `refill_halt`, `refill_cont_a`, `refill_cont_b`, `refill_V`; the rule is
`refillW` in `BB25_W2PR_sim.v`). R, S, T, U, V, W, X, Y rewrite the final block from the right with period 8. With x
the accumulator after absorbing the final P:

| x | result |
|---|---|
| 0 mod 8 | R reads a 0 and halts (R0 = `1RZ`) |
| 2 mod 4 | B21's continue: ",4,1" is appended to the last remaining block, and (x − 2)/4 lone [2] blocks follow |
| 4 mod 8 | V0 = `0LH` continues: the last remaining block loses one 1 and gets ",4,1", and x/4 lone [2] blocks follow |

(B21 halts on both 0 mod 8 and 4 mod 8.) The new continue changes the next phase's start by one leading 1 in its
frontier block. `inv_refill_gen`, B21's phase-start lemma, already covers that shape.

## 2. The run, and why it halts

As in B21, a phase that starts with N lone 2s ends at [E^(N−1), P], and the final sweep absorbs all N items. In
2-adic form (deep exit accumulator d = −4/3, x_p = d + 2N_p, N_(p+1) = N_p − 1 + k_p with k_p = (x_p − 2)/4 or
x_p/4):

| refill | phase | N_p (2-adic) | x_p | x_p mod 8 | result |
|---|---|---|---|---|---|
| #3 | 3 (the boot list) | 1 | 2/3 | 2 mod 4 | continue (B21's rule) |
| #4 | 4 | −1/3 | −2 | 6 | continue (B21's rule) |
| #5 | 5 | −7/3 | −6 | 2 | continue (B21's rule) |
| #6 | 6 | −16/3 | −12 | 4 | continue through V (B21 halts here) |
| #7 | 7 | −28/3 | −20 | 4 | continue through V |
| #8 | 8 | −46/3 | −32 | 0 | **halt** |

The Coq proof (`BB25_W2PR_run.v`) does this exactly. It works with residues mod 256: the engine value of a deep B0 is
81 mod 256. It finds the J accumulators at the ends of phases 4 to 8 to be 4, 0, 2, 2, 6 (mod 8) (J is the
accumulator before the final P, so x = J + 2), and it shows that each phase applies Fh at least once to the block
count (`Fh_step`, `step_lb`), which gives the bound (`abstract_finalW`, `sigma_lower_boundW`). The halt does not depend
on a residue class the proof leaves open.

## 3. Verification

[`verify/`](verify/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about 3 minutes (14 files), built in CI
(job `bb13-bb14`). `BB252.v` and `Individual252.v` instantiate busycoq for 25 states (new here). Seven files are B21's
machine-independent layers, byte-identical to [`../BB21/verify/multifile/`](../BB21/verify/multifile/)'s:
`BB21_B21_{absdef,grow,steps,inv,proc,phase,run}.v`. `share_check.sh` checks that, and `compile_clean.sh` runs it
when the BB21 tree is present. `probe.v` re-checks the transition table entry by entry against the string above (50
checks generated from the string) and the blank start configuration. It prints the definitions the statements use and
confirms that `halt`, `sigma_lower_bound` and `BB25_W2PR_run.abstract_finalW` are closed under the global context. The
proof also passes this project's `check.py` (extended to 25 states), 2026-11-08.

[`tools/w2pr_writeup_chk.py`](tools/w2pr_writeup_chk.py) simulates the machine string (exactly, jumping only over
same-state runs), without the Coq files (about 15 s). It checks:

1. 600 random sweeps and 200 level-1 engine runs against B21's rules;
2. the final sweep and refill on 64 cases covering every class of the accumulator mod 8 (the table of section 1);
3. 36 large cases, 9 in each class mod 8: the refill, then the next phase sweep by sweep until its first deep engine
   run;
4. the boot (the A boundary [1, 1, 4, 1, 2] 00 [1] after 162 steps);
5. the run from the blank tape is step-for-step identical to B21's for 200,000 macro steps (7.2·10^8 steps), with
   V, W, X, Y read as R, S, T, U;
6. the residue schedule above (mod 2^64): refills #3 to #7 continue, #6 and #7 through V, and #8 halts.

## 4. Size and comparisons

- **Proved:** Fh⁵(4↑↑341) < N, σ = N + 1, with Fh(n) = h_n(0) f_ω-class: roughly f_ω^5(4↑↑341). This is above B21's
  first published bound 4↑↑341 (since Fh(n) ≥ n). By an easy argument (not a Coq lemma) it is far below R18a's proved
  f_(ω·2)(f_ω(f_ω(f_10(2)))) and J20's proved f_(ω·2)(f_(ω+2)^2(f_10(2))): already f_(ω+1)(n) = f_ω^n(n) dominates
  f_ω^5 for n ≥ 5. B21's proved f_(ω²)^3(4↑↑341) ([`../BB21/verify_w2/`](../BB21/verify_w2/)) is higher still, so
  BB(25) ≥ BB(21) + 4 is the better proved bound for BB(25).
- **On paper only** (an argument, not a Coq lemma): each big phase is an f_(ω²) step, as in B21 (see B21's write-up,
  section 4), so five big phases give about f_(ω²)^5(4↑↑340). That is two f_(ω²) applications above B21's (on paper
  about f_(ω²)^3(4↑↑340); the wiki's bound for B21 is f_(ω²)^2(4↑↑341)). If it is right, W2PR would fill the wiki's
  empty rows BB(25) to BB(28). A formal version needs the same quantitative frontier-processing lemma as B21's f_(ω²)
  bound; it is not done.
- Not yet reviewed by the bbchallenge community.

## Credit

The ω² machinery is Racheline's (B21, the bbchallenge wiki's BB(21) champion). This project (the repository owner with
Claude models (Anthropic) as agents) designed W2PR (the mod-8 refill: U1 = `1LV` and the copy V–Y of B21's refill
cycle, 2026-11-07), wrote the Coq proof (2026-11-08) on top of this repository's B21 proof, the 25-state busycoq
setup, the probe, the checker and this write-up.
