# M13_19: a 13-state machine at level f_(ω+2), nineteen rounds deep

    1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LM1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_0LM1LK_0LG1LL

|   | 0   | 1   |                                                                      |
|---|-----|-----|----------------------------------------------------------------------|
| A | 1RB | 1RA |                                                                      |
| B | 1RI | 1RC |                                                                      |
| C | 0LD | 1LG |                                                                      |
| D | 0RE | 1LD |                                                                      |
| E | **0LM** | 1RF | E0 goes to M (M13b: `1LK`)                                        |
| F | **1RG** | 0RA | F0 goes to G (M13b: `1RM`); see below                             |
| G | 1RA | 0LH |                                                                      |
| H | 1LG | 1LH |                                                                      |
| I | 1RE | 0LJ |                                                                      |
| J | 1LH | 1LI |                                                                      |
| K | **1RZ** | 0LL | K0 is the halt (M13b: `0LL`)                                      |
| L | **0LM** | 1LK | (M13b: `0LH`)                                                     |
| M | **0LG** | **1LL** | new role (M13b: M0 was the halt, M1 `0LH`)                    |

States A–J and K1, L1 are as in M12 ([`../BB12/`](../BB12/)) and M13b ([`README.md`](README.md)). The halting
transition K0 is undefined in the Coq table (`---`); it is written `1RZ` here.

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB13_M13_19.halt`. |
| Score | K0 is read on a 0 and the halting transition writes a 1, so σ = N + 1, where N is the number of ones when K0 is read. No exact formula is stated in Coq; the halting configuration is `c_end p m` with p + m + 4 ones (`ones_c_end`). |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+2)^19(f_ω(3)) < N (`sigma_bound`) and f_(ω+2)^18(f_(ω+1)(f_(ω+1)(3))) < N (`sigma_bound_fw1`). |
| M13b (previous BB(13) entry) | **In Coq, against its exact score** (`BB13_M13_19_cmp.v`): M13b's halting tape holds exactly p + a + 5 ones for (p, a) = `pa7` (M13b's `score_exact`), and that number is below M13_19's N (`beats_M13b_exact`, `beats_M13b_score`). Both machines have σ = N + 1, so σ(M13_19) > σ(M13b). Argon's file also has `beats_M13b`, which compares with M13b's proved lower bound only. |
| Relabelled form | `1RB1RA_1RC1RK_1RD0LM_0LE1RI_0LH1LF_0LE1LG_1RZ0LF_1RA0LJ_1RH0RA_1LH1LJ_0LL1LH_0RD1LL_1LJ1LC`: the same machine with the states renamed in order of first visit from the blank tape (`tm_tnf`; `halt_tnf`, `sigma_bound_tnf`, `beats_M13b_tnf` transfer the results through the renaming, which is a Coq lemma, `tm_perm_tnf`). |
| Steps | Not computed. |

## 1. How it works

M13_19 runs the engine and counters of M12 and M13b; read [M13b's write-up](1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LL0LL_0LH1LK_1RZ0LH.md)
first. The configurations `Ca`, `Ch`, `Ci`, `Ce_z`, `Cd_z`, the engine W (W_0(b) = b + 3,
W_(j+1)(b) = W_j^(b+1)(2)), the counter rules `C_REL`, `D_STEP` and the macro steps Kc, Kc_full and Kd_step (one
f_(ω+2) round per iterated Kd_step) are the same, re-proved for this table in `BB13_M13_19.v`, here with an arbitrary
right tail z.

Two changes free a state. F0 = `1RG` replaces M13b's `1RM`: in the counter rules F0 is entered just before a 1 is
read, and G1 = `0LH` does what M13b's M1 = `0LH` did, so every rule survives. M is then free, and E0, K, L, M keep
a **stack** of numbers on the right of the counter: `stack_tail [u₁; …; u_D]` = (01)^u₁ 1 (01)^u₂ 1 … 0^∞ (Argon's
analysis; each case below is a Coq lemma). Every round starts at `Cd_z 7 3 d (stack_tail us)` and runs Kd_step about
d/3 times; what happens next depends on d mod 3:

- **d ≡ 2, one entry** (`Step_Rem2`): one Kc_full, then the engine walks over the stack entry (`Rem2_to_Ca`,
  `BLK_1`) and the machine reloads with a fresh one-entry stack (`EmptyR_reload`).
- **d ≡ 1** (`Step_Rem1`): one Kc_full, then `Ci_even_reload` pushes a new entry: the depth D grows by one.
- **d ≡ 0** (`Step_Rem0_cont`, `Step_Rem0_halt`): the top entry is popped and the engine drains the remaining D − 1
  entries (`Ca_drain_one`); each one flips the parity of the engine's output. If D − 1 is even the output is even
  and the machine reloads with a one-entry stack; if it is odd, `Halt_odd_b` ends on K reading a 0: the halt.

The level d is known modulo 3^(22−r) in round r (one factor 3 is used up per round). `RoundState M c D N` (Coq)
records a round's start: the configuration is reached from the blank tape, the stack has D entries, d ≡ c (mod M),
and d is above a bound built from N.

## 2. The run

From the blank tape, 388 steps reach `Cd_z 7 3 2 (stack_tail [3])` (`Boot_388`), and the first round starts with
d ≥ 6·f_ω(3) + 8 (`Boot_Round1`, from W_6(3) ≥ 32·f_ω(3), `W6_3_ge_f_omega_3`). The Coq lemmas `Reach_Round2` …
`Reach_Round19` then give each round's start:

| round | modulus | d mod modulus | d mod 3 | stack depth | case |
|---|---|---|---|---|---|
| 1 | 3^21 | 7845264905 | 2 | 1 | Rem2 |
| 2 | 3^20 | 3323341382 | 2 | 1 | Rem2 |
| 3 | 3^19 | 1024923929 | 2 | 1 | Rem2 |
| 4 | 3^18 | 236202590 | 2 | 1 | Rem2 |
| 5 | 3^17 | 125781898 | 1 | 1 | Rem1 (push) |
| 6 | 3^16 | 36336568 | 1 | 2 | Rem1 (push) |
| 7 | 3^15 | 6311965 | 1 | 3 | Rem1 (push) |
| 8 | 3^14 | 107002 | 1 | 4 | Rem1 (push) |
| 9 | 3^13 | 939162 | 0 | 5 | Rem0, four entries drained, continue |
| 10 | 3^12 | 371754 | 0 | 1 | Rem0, continue |
| 11 | 3^11 | 147156 | 0 | 1 | Rem0, continue |
| 12 | 3^10 | 21347 | 2 | 1 | Rem2 |
| 13 | 3^9 | 4758 | 0 | 1 | Rem0, continue |
| 14 | 3^8 | 3527 | 2 | 1 | Rem2 |
| 15 | 3^7 | 438 | 0 | 1 | Rem0, continue |
| 16 | 3^6 | 359 | 2 | 1 | Rem2 |
| 17 | 3^5 | 156 | 0 | 1 | Rem0, continue |
| 18 | 3^4 | 55 | 1 | 1 | Rem1 (push) |
| 19 | 3^3 | 12 | 0 | 2 | Rem0, one entry drained: halt |

The modulus, residue and depth columns are the arguments of the `RoundState` lemmas; the last two columns follow
from them. Each round adds one f_(ω+2) level, so after round 19 (`Run_Halt_19`) the halting tape holds more than
f_(ω+2)^19(f_ω(3)) ones (`sigma_bound`). The halting configuration is `c_end p m`, with K reading a 0 and
p + m + 4 ones on the tape (`c_end_halted`, `ones_c_end`).

## 3. Verification

[`verify_m13_19/`](verify_m13_19/): busycoq `bd2e36f`, Coq 8.20.1, built in CI (job `bb13-bb14`). `probe.v`
re-checks both transition tables (`tm` and `tm_tnf`) entry by entry against the two strings above (52 checks
generated from the strings) and the blank start configuration, prints the definitions the statements use, and
confirms that the nine theorems `halt`, `sigma_bound`, `sigma_bound_fw1`, `beats_M13b`, `halt_tnf`,
`sigma_bound_tnf`, `beats_M13b_tnf`, `beats_M13b_exact` and `beats_M13b_score` are closed under the global context.
The main proof also passes this project's `check.py` (the statement `halts tm c0` read from the file, the table
compared with the machine string, `Print Assumptions halt` closed), 2026-11-12.

`BB13_M13_19.v` is Argon's file, unchanged except for line endings and a first line `(* machine: … *)`.
`BB13_M13_19_cmp.v` (the comparison with M13b's exact score) was written here; it loads M13b's two proof files,
byte-identical copies of [`verify_m13b/multifile/`](verify_m13b/multifile/).

There is no independent simulator for this write-up; sections 1 and 2 summarise Argon's analysis, and every rule
cited is a lemma of the Coq file.

## 4. Comparisons

- **In Coq, against M13b's exact score** (`BB13_M13_19_cmp.v`). From the definitions of M13b's maps it proves an
  upper bound on M13b's score: W_j(b) ≤ f_ω(j + b + 4), so one Kc step at most triples an f_ω, Kc_full is at most
  f_(ω+1)², Kd_step at most f_(ω+1)³, and each of M13b's six big rounds (an iterated Kd_step, with its reload and
  Kc_full) at most two applications of f_(ω+2). Starting from f_(ω+2)(f_ω(3)), above M13b's opening and its reload
  point (8, W_8(8)), this gives p + a + 5 < f_(ω+2)^14(f_ω(3)) for M13b's `pa7`, below M13_19's f_(ω+2)^19(f_ω(3)).
  No closed term of the hierarchy is evaluated: every bound is proved for variables.
- On paper (not machine-checked), M13_19's proved lower bound is also above the proved lower bounds of M13
  (f_(ω+2)(f_ω(20))) and M12 (f_(ω+2)(f_(ω+1)(f_(ω+1)(3)))); neither of those machines has a proved upper bound.
- Not yet reviewed by the bbchallenge community.

## Credit

Found and proved in Coq by Argon, a Google Gemini model run by the repository owner in Google's Antigravity
(2026-11-09), by a search over M12's core with F0 redirected and the outer states E0, K, L, M free. Re-checked here
(check.py, clean build, probe), with the comparison file and this write-up.
