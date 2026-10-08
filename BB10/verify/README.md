# Coq proofs for `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RZ0LC` (n1)

`multifile/` holds the development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For this machine (J0 undefined = the halt) it proves:

- `BB10_n1.halt : halts tm c0` -- the machine halts from the blank tape;
- `BB10_n1_bound.score_exact` -- the halting tape holds exactly `2w + f + 3k + 22` ones, with `w >= F^(2JJ+1)(34)`,
  `F n = 2↑^n 4`, `JJ = (3T-13)/7`, `T = 2↑^37 3`;
- `BB10_n1_exact.score_closed_unfolded` -- the same count as a closed formula: an explicit `JJ`-fold recursion of
  Knuth arrows (`step` / `stepn`, printed by the probe);
- `BB10_n1_bound.sigma_lower_bound` -- more than `G^((6T-19)/7)(33)` ones, `G(x) = 2↑^(x+1) 3`;
- `BB10_n1_bound.beats_champion` -- the BB(10) champion of Racheline (2024),
  `1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_0LF0LJ_1LH0LJ`, halts with `nc` ones and n1 with `no`
  ones, and `nc + 1 < no + 1` (both halting transitions write a 1 on a 0), against the champion's own Coq-proved
  exact score (`BB10_champion_bound.score_exact`);
- `BB10_n1_bound.beats_lead` -- the same against the 10-state machine
  `1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LJ0LC_1RG1LD_0RI0RH_1RG1LF_1RE1RI_1RZ1LC` (`BB10_lead_*`);
- `BB10_n1_bound.dominates` -- more ones than `(2↑^K)^x (x)` for all `K, x <= F(F(F(34)))`.

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

This compiles the ten files in dependency order (about 20 minutes, most of it `BB10_n1.v`) and then `probe.v`.
`probe.v` re-checks by conversion all 20 entries of n1's transition table against the machine string (generated
from the string, not from the Coq file), prints the definitions the statements use (`arrow`, `F`, `iter`, `JJ`,
`ones`, `step`, `stepn`), the types of the main theorems, and `Print Assumptions` for each of the eight; all eight
must say `Closed under the global context`. `compile_clean.log` and `probe.log` are the logs of a from-scratch
build; `sha256.txt` has the hashes of the source files.

A self-contained single-file version (standard library only, like `BB9/verify/`) is being prepared.
