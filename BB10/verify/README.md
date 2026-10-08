# Coq proofs for `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RZ0LC` (n1)

`BB10_n1_selfcontained.v` is ONE Coq file, depending only on the Coq standard library (Coq 8.20.1), and
`multifile/` holds the same development as separate files on top of
[busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`). For this machine (J0 undefined = the halt)
they prove (names as in `multifile/`; the single file restates each at the end as `n1_halts`, `n1_score_exact`,
`n1_beats_champion`, `n1_fgh_level`, `n1_beats_graham`, ...):

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
- `BB10_n1_bound.dominates` -- more ones than `(2↑^K)^x (x)` for all `K, x <= F(F(F(34)))`;
- `BB10_n1_fgh.fgh_level` -- `f_omega1 ((3T-13)/7 - 2) < N < f_omega1 (6T)` for the exact ones count N, with the
  standard fast-growing hierarchy (`fgh 0 n = n+1`, `fgh (k+1) n = (fgh k)^n n`, `f_omega n = fgh n n`,
  `f_omega1 n = f_omega^n n`): the level is exactly omega+1;
- `BB10_n1_fgh.beats_graham` -- more ones than Graham's number (`graham_g 0 = 4`,
  `graham_g (k+1) = up3 (graham_g k) 3` with `up3 k n = 3↑^k n`, `Graham = graham_g 64`), via
  `graham_lt_f_omega1_64 : Graham < f_omega1 64`.

## Check it

Single file (standard library only, no `-Q` flags):

    coqc BB10_n1_selfcontained.v        # about 13 minutes on one core
    coqc probe_BB10_n1_selfcontained.v  # about 1 minute, same directory

The first command must end with 28 lines `Closed under the global context`, one per `Print Assumptions` at the end
of the file; the only warnings are deprecation notices and LibTactics' `ltac_Mark` notice. The probe re-checks by conversion every transition-table
entry of n1, of the BB(10) champion and of the 0LJ0LC machine against their machine strings (61 `eq_refl` checks,
with the blank start configuration), the types of the main theorems, and prints 18 `Print Assumptions`, all
`Closed under the global context`.

The file contains busycoq's core (LibTactics, Helper, TM, Compute, Flip, Permute, Individual; MIT) inlined, one
module per file, then the eleven files of `multifile/` without changes to any proof text: each machine's files form
one module (`Champion10`, `Lead10`, `N1`), `Require` lines are hoisted or turned into `Import`, and opacity
settings are reset at file boundaries. The one textual change is in busycoq's TM: the state constructors are
`St_A` ... `St_J` and the directions `St_L`, `St_R`, each behind a notation with the usual name, because in a
single file `intros` would otherwise rename binders called `A` or `L`. `Print tm` still shows the usual names.
The file contains one `Axiom` declaration, `inj_pair2` in the inlined LibTactics; the `Print Assumptions` lines
certify that no theorem uses it. A script generated the file from the multi-file sources.

Multi-file:

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

This compiles the eleven files in dependency order (about 20 minutes, most of it `BB10_n1.v`) and then `probe.v`.
`probe.v` re-checks by conversion all 20 entries of n1's transition table against the machine string (generated
from the string, not from the Coq file), prints the definitions the statements use (`arrow`, `F`, `iter`, `JJ`,
`ones`, `step`, `stepn`, `fgh`, `f_omega`, `f_omega1`, `up3`, `graham_g`, `Graham`), the types of the main
theorems, and `Print Assumptions` for each of the twelve; all twelve must say `Closed under the global context`. `compile_clean.log` and `probe.log` are the logs of a from-scratch
build; `sha256.txt` has the hashes of the source files.

## Verification record

`VERIFICATION.txt` records the first from-scratch build of the single file with plain `coqc` in a directory holding
only the file and the probe (2026-10-08: exit 0, 756 s, 28 "Closed under the global context"; probe exit 0, 73 s,
18 closed), plus a `coqchk` kernel re-check of the compiled file (exit 0, 147 s). A second, independent
from-scratch build of the same file the same day gave the same result (build 755 s, probe 52 s);
`build.log` and `probe.log` are its outputs. `sha256.txt` has the hashes of the file and the probe.
