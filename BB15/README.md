# BB15/: 15 states, 2 symbols

## Current entry: J15_fw13 (Argon, on Jacobzheng's engine)

    1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LA0RN_0LA1RO_1RZ1RM

Halts from the blank tape; O0 (`1RZ` in the string) is the halt. It is read on a 0 and writes 1, so σ = N + 1, where N
is the number of ones when O0 is read. Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+13)(20) < N,   σ = N + 1                          (sigma_lower_bound)
    f_(ω+2)^30(f_(ω+1)(f_(ω+1)(3))) < N                    (beats_M14_31: M14_31's proved BB(14) bound)

and the exact score N = 2j + 1, where hoc_0^14(4) + 29 = 3j for the machine's recursion (`score_exact`; not
evaluated).

J15_fw13 runs the 12-state core of Jacobzheng's J20 ([`../BB20/`](../BB20/)) with three more states M, N, O that do
both of J20's other jobs: they rewrite the accumulator into an inner list (the expansion) and rebuild the outer list
when it is used up (the refill), scanning with period 3. Every level map keeps the accumulator ≡ 1 (mod 3). From the
blank tape: two refills give the outer list [2^14] after 1012 steps, the fourteen digits are reduced at outer levels
0 to 13, and the third merged block is ≡ 0 (mod 3), where O halts.

The bbchallenge wiki's Champions table has no BB(15) row (checked 2026-11-08). In Coq, N is above the BB(14) entry's
proved bound, so this is the best proved bound here for BB(15). The 16-state J16_w2 ([`../BB16/`](../BB16/)) is
above it. Not yet reviewed by the bbchallenge community.

- [`1LH0LG_0LI1RC..._0LA1RO_1RZ1RM.md`](1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LA0RN_0LA1RO_1RZ1RM.md):
  the write-up (the table, the expansion and the refill, the run, the mod-3 invariant, the size, verification,
  comparisons, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `step_1012`, `score_exact`,
  `sigma_lower_bound`, `beats_M14_31`. About 30 s to compile; built and probed in CI (job `bb13-bb14`), which
  requires five closed `Print Assumptions` reports.

Found and proved by Argon, a Google Gemini model run by the repository owner in Google's Antigravity (2026-11-08), by
compressing Jacobzheng's J19/J20 architecture; re-checked here, with the comparison `beats_M14_31`.
