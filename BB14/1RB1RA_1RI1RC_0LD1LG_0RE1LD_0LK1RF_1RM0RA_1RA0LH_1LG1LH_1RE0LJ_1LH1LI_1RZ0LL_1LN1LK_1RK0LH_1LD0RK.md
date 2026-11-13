# M14_fw3: a 14-state machine at level f_(ω+3)

    1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_1LN1LK_1RK0LH_1LD0RK

|   | 0   | 1   |                                                                      |
|---|-----|-----|----------------------------------------------------------------------|
| A | 1RB | 1RA |                                                                      |
| B | 1RI | 1RC |                                                                      |
| C | 0LD | 1LG |                                                                      |
| D | 0RE | 1LD |                                                                      |
| E | **0LK** | 1RF | E0 goes to K (M14_31: `0RN`)                                      |
| F | 1RM | 0RA |                                                                      |
| G | 1RA | 0LH |                                                                      |
| H | 1LG | 1LH |                                                                      |
| I | 1RE | 0LJ |                                                                      |
| J | 1LH | 1LI |                                                                      |
| K | **1RZ** | 0LL | K0 is the halt (M14_31: `0LL`)                                    |
| L | **1LN** | 1LK | (M14_31: `0LH`)                                                   |
| M | **1RK** | 0LH | (M14_31: `0LK`)                                                   |
| N | **1LD** | **0RK** | new role (M14_31: `1LM`, N1 the halt)                         |

States A–J, K1, L1 and M1 are as in M12 ([`../BB12/`](../BB12/)), M13b and M14_31 ([`README.md`](README.md)). The
halting transition K0 is undefined in the Coq table (`---`); it is written `1RZ` here.

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB14_M14_fw3.halt`. |
| Exact score | Machine-checked formula: N = p + a + 6 ones when K0 is read, where (p, a) = `pa_final` is given by the recursion of section 2 (`score_exact`). K0 is read on a 0 and the halting transition writes a 1, so σ = N + 1. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+3)(f_ω(3)) < N (`sigma_bound`), where f_(ω+3)(n) = f_(ω+2)^n(n). |
| M14_31 (previous BB(14) entry) | **In Coq, against its exact score** (`BB14_M14_fw3_cmp.v`): M14_31's halting tape holds exactly p + a + 4 ones for (p, a) = `pa32` (M14_31's `score_exact`; σ = N for M14_31, which halts reading a 1), and that number is below M14_fw3's N (`beats_M14_31_exact`, `beats_M14_31_score`). So σ(M14_fw3) = N + 1 > σ(M14_31). Argon's file also has `beats_M14_31`, which compares with M14_31's proved lower bound only. |
| Relabelled form | `1RB1RA_1RC1RJ_1RD0LK_0LE1RI_1RZ0LF_1LG1LE_1LH0RE_0RD1LH_1RL0RA_0LH1LN_1LM1LC_1RE0LM_1LN1LM_1RA0LM`: the same machine with the states renamed in order of first visit from the blank tape (`tm_tnf`; `halt_tnf`, `sigma_bound_tnf`, `beats_M14_31_tnf` transfer the results through the renaming, which is a Coq lemma, `tm_perm_tnf`). |
| Steps | Not computed. |

## 1. How it works

M14_fw3 runs the engine and counters of M12, M13b and M14_31; read [M14_31's write-up](1RB1RA_1RI1RC_0LD1LG_0RE1LD_0RN1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LL0LL_0LH1LK_0LK0LH_1LM---.md)
first. The configurations `Ca`, `Ch`, `Ci`, `Ce_z`, `Cd_z`, the engine W, the counter rules `C_REL`, `D_STEP` and the
macro steps Kc, Kc_full, Kd_step and Kd_iter (one f_(ω+2) round per iterated Kd_step) are the same, re-proved for this
table in `BB14_M14_fw3.v`.

The new part is a **unary counter E on the right of the tape**, a block (10)^E (Argon's analysis; each step below is
a Coq lemma). The outer loop starts at `Ce_z p a 0 0 (0 (10)^E 0^∞)` and makes two big rounds:

- **Phase 1** (`Phase1_exec`): E0, K, L and N rewrite the block 1^(a+2) into a d-counter of about a/2 and bounce
  back into the engine (`Phase1_reload`, `N_bounce_step`); then about a/6 iterated Kd_steps and one Kc_full. The
  d-counter is left at 1, so the round ends at `Ce_z p₁ a₁ 0 1 …` with E untouched (`Phase1_pa`).
- **Phase 2** (`Phase2_exec`): from that remainder, E1 → F0 → M0 = `1RK` walk into the block and use up its first
  10, then the same reload, about a₁/6 iterated Kd_steps and a Kc_full; this round ends at `Ce_z p₂ a₂ 0 0 …` with
  E decreased by one (`Phase2_pa`).

So each decrement of E costs two f_(ω+2) rounds (`Outer_step`, `Outer_loop`). When E = 0, Phase 1 runs once more and
M0 = `1RK` then finds K reading a blank 0: the halt (`HALT_E0`).

## 2. The run

From the blank tape, 139 steps reach `Ch 3 3 0^∞` (`Boot_139`); the engine then produces W_3(3), and the reload
writes the counter E₀ = W_3(3)/2 − 3 (`E0`), with f_ω(3) ≤ E₀ (`E0_ge_f_omega_3`). A 72-step bridge, a few counter steps and
eight small Kd_steps (`Boot_bridge_72`, `Boot_to_pa_init`) reach the start of the outer loop at `pa_init`. Then

    pa_final = Phase1_pa (Outer_step^E₀ (pa_init)),

and the halting configuration `c_end p a`, K reading a 0 with 1^(a+6) (01)^p on its left, holds p + a + 6 ones
(`run_to_end`, `ones_c_end`, `score_exact`). Each Outer_step is two f_(ω+2) rounds and there are E₀ ≥ f_ω(3) of
them, which gives f_(ω+3)(f_ω(3)) < N (`pa_final_dom_fw3`, `sigma_bound`).

## 3. Verification

[`verify_m14_fw3/`](verify_m14_fw3/): busycoq `bd2e36f`, Coq 8.20.1, built in CI (job `bb13-bb14`). `probe.v`
re-checks both transition tables (`tm` and `tm_tnf`) entry by entry against the two strings above (56 checks
generated from the strings) and the blank start configuration, prints the definitions the statements use, and
confirms that the nine theorems `halt`, `score_exact`, `sigma_bound`, `beats_M14_31`, `halt_tnf`,
`sigma_bound_tnf`, `beats_M14_31_tnf`, `beats_M14_31_exact` and `beats_M14_31_score` are closed under the global
context. The main proof also passes this project's `check.py` (the statement `halts tm c0` read from the file, the
table compared with the machine string, `Print Assumptions halt` closed), 2026-11-12.

`BB14_M14_fw3.v` is Argon's file, unchanged except for a first line `(* machine: … *)`. `BB14_M14_fw3_cmp.v` (the
comparison with M14_31's exact score) was written here; it loads M14_31's proof file, a byte-identical copy of
[`verify_m14_31/multifile/BB14_M14_31.v`](verify_m14_31/multifile/BB14_M14_31.v).

There is no independent simulator for this write-up; sections 1 and 2 summarise Argon's analysis, and every rule
cited is a lemma of the Coq file.

## 4. Comparisons

- **In Coq, against M14_31's exact score** (`BB14_M14_fw3_cmp.v`). From the definitions of M14_31's maps it proves
  an upper bound on M14_31's score: W_j(b) ≤ f_ω(j + b + 4), so one Kc step at most triples an f_ω, Kc_full is at
  most f_(ω+1)², Kd_step at most f_(ω+1)³, and each of M14_31's eight round maps (`D2_round`, `D1_round`,
  `K0_z0_round`, …) at most two applications of f_(ω+2). Starting from f_(ω+2)(f_ω(3)), above M14_31's first pair
  `pa1` and its reload point (8, W_8(8)), the 31 rounds give p + a + 4 < f_(ω+2)^64(f_ω(3)) ≤ f_(ω+3)(f_ω(3)) for
  M14_31's `pa32` (f_ω(3) ≥ 192 > 64), below M14_fw3's N. No closed term of the hierarchy is evaluated: every bound
  is proved for variables.
- The 15- and 16-state entries are not affected: J15_fw13's proved lower bound f_(ω+13)(20) ([`../BB15/`](../BB15/))
  and J16_w2's f_(ω·2)(f_15(2)) ([`../BB16/`](../BB16/)) are far above M14_fw3's proved f_(ω+3)(f_ω(3)). M14_fw3 has no
  proved upper bound; on paper (not machine-checked), its score is of level f_(ω+3) (each of its 2E₀ + 1 big rounds
  is at most a few applications of f_(ω+2), as for M14_31 above), far below f_(ω+13)(20), so BB(14) + 1 does not
  improve the BB(15) row.
- Not yet reviewed by the bbchallenge community.

## Credit

Found and proved in Coq by Argon, a Google Gemini model run by the repository owner in Google's Antigravity
(2026-11-09), by a search over M12's core with the outer states E0, K, L, M0 and N free. Re-checked here (check.py,
clean build, probe), with the comparison file and this write-up.
