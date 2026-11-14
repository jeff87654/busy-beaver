# Coq proofs for 44-B and 44-A (BB(4,4))

A Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`, Coq 8.20.1), logical
root `Local`, for Argon's machines

    44-B  1RB2LC3RA1RZ_2RC3LB2LB0LC_1LB2RC3RA1LD_2RC1LC3RD2LD   (A3 = 1RZ is the halt, None in Coq)
    44-A  1LB2LC3RA0RB_2RC1RZ2LB3LB_1LB2RC3RA1LD_2RC1LC3RD2LD   (B1 = 1RZ is the halt)

written by this project (agent claims-prover, 2026-11-13). The first five files are byte-identical copies of
[`../verify_44c/`](../verify_44c/) (44-C, Argon's files; `share_check.sh`): the busycoq instance, the `g` hierarchy,
the closed forms and Knuth-arrow lemmas, and 44-C's exact score `BB44_run.sigma`.

44-B (`BB44B_rules.v`, `BB44B_run.v`, `BB44B_cmp.v`):

- `bb44B_halts : halts tm c0`, `reaches_final`, `final_halted`;
- `c_final_nonzero : nonzero_cells c_final sigma` with `sigma = 2 cB + 2 dB + 9`, and `c_final_head` (the head reads
  a 3 and `tm (A, 3) = None`): σ is the number of nonzero cells of the halting configuration, unchanged by the halting
  write;
- `sigma_B_closed`: 2 dB + 4 = 2 ↑^(2 cB + 2) 3, 2 cB + 4 = 2^(2 bB + 4), 2 bB + 4 = 2 ↑↑↑ (2 a6 + 4),
  2 a6 + 4 = 2 ↑^4 (2 a5 + 4);
- `BB44B_beats_A : BB44A_run.sigma < BB44B_run.sigma`, `BB44B_beats_C : BB44_run.sigma < BB44B_run.sigma`,
  `BB44B_beats_official : knuth 509 2 3 + 510 < BB44B_run.sigma` (loader3229's exact score);
- `sigma_B_f_omega : f_omega (knuth 5 2 3) < BB44B_run.sigma`, `f_omega n = knuth (S n) 2 (n + 3)` (the Knuth-arrow
  function of `BB54/verify/BB54_score.v`, same text).

44-A (`BB44A_rules.v`, `BB44A_run.v`, `BB44A_cmp.v`): `bb44A_halts`, `reaches_final`, `final_halted`,
`c_final_nonzero` (σ = 2 M3 + 2 M1 + 3), `c_final_head`, `sigma_A_closed` (2 M3 + 4 = 2 ↑^(2 M1) (2 M2 + 5),
2 M1 + 4 = 2 ↑^4 6), `BB44A_beats_C`, `BB44A_beats_official`.

## Check it

    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`probe.v` checks both compiled transition tables against the machine strings entry by entry (32 lines generated from
the strings, not from the Coq files), prints the definitions the statements use, and runs `Print Assumptions` on 18
theorems: all are closed under the global context. CI job `bb44` runs the same script.
