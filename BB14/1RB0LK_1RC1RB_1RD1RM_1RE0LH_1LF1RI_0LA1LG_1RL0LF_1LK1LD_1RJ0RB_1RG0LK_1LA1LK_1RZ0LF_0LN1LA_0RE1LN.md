# M14_fw3x4: a 14-state machine at level f_(ω+3)^4

    1RB0LK_1RC1RB_1RD1RM_1RE0LH_1LF1RI_0LA1LG_1RL0LF_1LK1LD_1RJ0RB_1RG0LK_1LA1LK_1RZ0LF_0LN1LA_0RE1LN

This is the machine with its states named in order of first visit from the blank tape (start A). It is easier to
read in the state order of M12's core ([`../BB12/`](../BB12/)), where it is M14_fw3 (the previous entry) with six
transitions changed and started in G instead of A:

    1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LL1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_0LG1LN_1RN0LH_1RK0LL   (start G)

| core | 0   | 1   | name in the string above |                                                     |
|---|-----|-----|---|------------------------------------------------------------------------|
| A | 1RB | 1RA | B |                                                                        |
| B | 1RI | 1RC | C |                                                                        |
| C | 0LD | 1LG | M |                                                                        |
| D | 0RE | 1LD | N |                                                                        |
| E | **1LL** | 1RF | E | E0 goes to L (M14_fw3: `0LK`)                                     |
| F | 1RM | 0RA | I |                                                                        |
| G | 1RA | 0LH | A | the start state (M14_fw3 starts in A)                                |
| H | 1LG | 1LH | K |                                                                        |
| I | 1RE | 0LJ | D |                                                                        |
| J | 1LH | 1LI | H |                                                                        |
| K | 1RZ | 0LL | L | K0 is the halt, as in M14_fw3                                         |
| L | **0LG** | **1LN** | F | (M14_fw3: `1LN`, `1LK`)                                    |
| M | **1RN** | 0LH | J | (M14_fw3: `1RK`)                                                   |
| N | **1RK** | **0LL** | G | (M14_fw3: `1LD`, `0RK`)                                    |

States A–J and K1 are as in M12, M13b, M14_31 and M14_fw3 ([`README.md`](README.md)). The halting transition is
undefined in the Coq tables (`---`); it is written `1RZ` here. Started in G, the machine first writes a 1 and moves
right into A (G0 = `1RA`).

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB14_M14_fw3x4_entry.halt : halts tm c0`, for the table of the machine string. |
| Exact score | Machine-checked formula: N = p + a + 7 ones when the halt (L0; K0 in core order) is read, where (p, a) = `pa_final` is given by the recursion of section 2 (`score_exact`). It is read on a 0 and the halting transition writes a 1, so σ = N + 1. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+3)^4(f_ω(4)) < N (`sigma_bound`), where f_(ω+3)(n) = f_(ω+2)^n(n). |
| M14_fw3 (previous BB(14) entry) | **In Coq, against its exact score** (`BB14_M14_fw3x4_cmp.v`): M14_fw3's halting tape holds exactly p + a + 6 ones for its (p, a) = `pa_final` (M14_fw3's `score_exact`), that number is at most f_(ω+3)(f_ω(13)), and it is below M14_fw3x4's N (`beats_M14_fw3_exact`, `beats_M14_fw3_score`); every halting tape of M14_fw3 holds fewer ones than every halting tape of M14_fw3x4 (`beats_M14_fw3_all`). Both halt reading a 0, so σ(M14_fw3x4) > σ(M14_fw3). |
| Steps | Not computed. |

## 1. How it works

M14_fw3x4 runs the engine and counters of M12, M14_31 and M14_fw3; read [M14_fw3's write-up](1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_1LN1LK_1RK0LH_1LD0RK.md)
first. The configurations `Ca`, `Ch`, `Ce_z`, `Cd_z` carry a pair (p, a): p blocks 01 on the left of the head and a
run of 1s. The cascade `CH_CA` takes `Ch j b` to `Ca j W_j(b)`, with W_0(b) = b + 3 and W_(j+1)(b) = W_j^(b+1)(2), an
f_j-level step. Because p grows on each pass, one pass Kc (`Kc_step`) is of level f_ω, Kc_full (b/2 passes,
`Kc_full_all`) and Kd_step (`Kd_step_all`) of level f_(ω+1), and an outer step (`Outer_step_exec`: one Kc_full, a
reload bounce and (a/2 − 1)/3 Kd_steps) of level f_(ω+2) (`Kc_full_dom`, `Kd_step_dom`, `Outer_step_dom`).

As in M14_fw3, a **unary counter E** on the right of the tape, a block (10)^E, is used up one 10 per outer step, so an
outer loop with E ≥ n steps gives f_(ω+3)(n) (`Outer_loop`, `Outer_loop_fw3`). The new part is what lies **to the
right of the counter**. In M14_fw3 the end of the counter is the halt. Here it is a sentinel tail, and when the
counter runs out the machine reads the sentinel, runs a short bridge, and writes a **new counter** of half the size of
one of the huge numbers just produced, leaving a shorter sentinel behind (each step is a Coq lemma of Neon's file):

| loop | counter | sentinel after the counter | bridge at its end | next counter |
|---|---|---|---|---|
| 1 | E₀ = W_5(1)/2 − 1 | 1111 | `Trans1_exec` | E₁ = b/2 − 1, for b = W_p(W_p(a + 4)) after a Kc_full, a run of Kd_steps and a Kc_full |
| 2 | E₁ | 11 | `Trans2_exec` | E₂ = a/2 + 1, after a Kc_full, two runs of Kd_steps and a Kc_full |
| 3 | E₂ | 011 | `Trans3_exec` | E₃ = a/2 + 3, after one Kc_full |
| 4 | E₃ − 1 | 10 | `Trans4_HALT_exec` | none: after a Kc_full, a run of Kd_steps and a Kc_full the machine reads K0 on a blank and halts |

Each new counter is at least the lower bound proved for the previous loop's output (`Trans1_dom`, `Trans2_dom`,
`Trans3_dom`), so the four loops nest: f_(ω+3)^4.

## 2. The run

From the blank tape, 240 steps reach `Ch 6 3 (0100011 0^∞)` (`Boot_240`; the left side is (01)^6). The cascade then
produces W_6(3) and W_5(1), and `Boot_to_Loop1` reaches the start of loop 1 with the counter E₀ = W_5(1)/2 − 1 and the
sentinel 1111, at the pair `pb_L1_0` = (3 + W_6(3)/2, W_(3 + W_6(3)/2)(6)); f_ω(4) ≤ E₀ (`E0_ge_fw4`, from
16·f_ω(4) ≤ W_5(1)). Then (`run_to_end`)

    pa_final = Trans4_pa_final (Outer_step^(E₃−1) (Trans3_pb (Outer_step^E₂ (Trans2_pb (Outer_step^E₁ (Trans1_pb (Outer_step^E₀ (pb_L1_0))))))))

with E₁, E₂, E₃ computed from the pair at the end of the loop before, and the halting configuration `c_end p a`,
reading a 0 with 1^(a+7) (01)^p on its left, holds p + a + 7 ones (`ones_c_end`, `score_exact`). The four loops give
f_(ω+3)^4(f_ω(4)) < N (`pa_final_dom`, `N_final_gt_fw3x4`, `sigma_bound`).

## 3. Verification

[`verify_m14_fw3x4/`](verify_m14_fw3x4/): busycoq `bd2e36f`, Coq 8.20.1, built in CI (job `bb13-bb14`). `probe.v`
re-checks three transition tables entry by entry against the two strings above (84 checks generated from the
strings), the two start configurations, prints the definitions the statements use, and confirms that fourteen
theorems are closed under the global context. The entry file `BB14_M14_fw3x4_entry.v` passes this project's
`check.py` (the statement `halts tm c0` read from the file, the table compared with the machine string,
`Print Assumptions halt` closed), 2026-11-23.

`BB14_M14_fw3x4.v` is Neon's file, unchanged. Its `halt` is stated for the G-started table in M12's state order, so
the entry file restates its results for the machine string's table (see the directory's README).
`BB14_M14_fw3x4_cmp.v` (the comparison with M14_fw3's exact score) was written here; it loads M14_fw3's proof file,
a byte-identical copy of [`verify_m14_fw3/multifile/BB14_M14_fw3.v`](verify_m14_fw3/multifile/BB14_M14_fw3.v).

**Independent audit** (2026-11-23, a Claude agent of this project, before the packaging): Neon's file and all its
busycoq dependencies were rebuilt from source, with no axioms and no warnings; the source was scanned for Admitted,
axioms, unsafe flags and redefinitions of busycoq's notions (none). The headline statements were proved again over
definitions written for the audit (both machine strings transcribed by hand, its own count of ones, the hierarchy
with Coq's `Nat.iter`): `BB14_M14_fw3x4_audit.v`. An independent literal simulator,
[`tools/m14_fw3x4_lit_chk.py`](tools/m14_fw3x4_lit_chk.py), confirms that the two strings are the same machine and that
all 14 states are reached, that the configuration after 240 steps is `Boot_240`'s, and checks 26 of the file's macro
and bridge rules on 659 concrete instances (random parameters and right tails), with no failure. The large composite
steps (outer step, loop starts, bridges) cannot be simulated (W_3(1) is already astronomically large); they rest on
the Coq proof.

## 4. Comparisons

- **In Coq, against M14_fw3's exact score** (`BB14_M14_fw3x4_cmp.v`). Neon's file runs M14_fw3 itself, in a module
  `M14_Old`: its own copy of the table (pinned to the published string), its own exact count N_old and the upper
  bound N_old ≤ f_(ω+3)(f_ω(13)), proved for variables from the definitions of M14_fw3's maps; since f_ω(4) ≥ 13 this
  is at most f_(ω+3)^2(f_ω(4)), below N (`N_old_lt_N_final`). The comparison file loads the published proof and shows
  that its exact score p + a + 6 is N_old (`M14_fw3_score_agrees`, by determinism), hence `beats_M14_fw3_exact`.
- The 15- and 16-state entries are not affected: J15_fw13's proved lower bound f_(ω+13)(20) ([`../BB15/`](../BB15/))
  and J16_w2's f_(ω·2)(f_15(2)) ([`../BB16/`](../BB16/)) are far above M14_fw3x4's proved f_(ω+3)^4(f_ω(4)).
  M14_fw3x4 has no proved upper bound; on paper (not machine-checked), its score is of level f_(ω+3) (four loops of outer
  steps, each at most a few applications of f_(ω+2), as for M14_fw3 above), far below f_(ω+13)(20), so BB(14) + 1 does not improve the BB(15) row.
- Not yet reviewed by the bbchallenge community.

## Credit

Found and proved in Coq by Gemini 4 Neon, a Google Gemini model run by the repository owner in Google's
Antigravity (2026-11-22/23), in a staged search of M12's core around M14_fw3 with the start state free (Neon's
search found f_(ω+3)^2 and f_(ω+3)^3 halters with shorter sentinel chains first; M14_fw3x4 came from a slice with
K0, L1, N0 and N1 free). Audited and re-checked here (clean build, statements re-proved over independent definitions,
literal simulator, check.py, probe), with the entry file, the comparison file and this write-up.
