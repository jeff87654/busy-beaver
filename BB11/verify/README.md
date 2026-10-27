# Coq proofs for `1RG0LH_1RK1RC_0LD1LA_0RE1LD_0LI1RF_1RZ0RG_1RB1RG_1LA1LH_0LK0LJ_1LH1LI_1LJ1RE` (M11b)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For this machine (F0 undefined = the halt, `1RZ` in the string) it proves:

- `BB11_M11b.halt : halts tm c0`: the machine halts from the blank tape;
- `BB11_M11b_fgh.score_exact`: the halting tape holds exactly `fst pa_end + snd pa_end + 4` ones, where `pa_end`
  is the explicit pair computed by the run (see `BB11_M11b.v`, section "Full halting trajectory of M11");
- `BB11_M11b_fgh.sigma_lower_bound_m11`: the halting tape holds N ones with `f_omega1 (f_omega (f_omega 5)) < N`;
- `BB11_M11b_fgh.sigma_lower_bound_64`: `f_omega1 (f_omega 64) < N`;
- `BB11_M11b_upper.sigma_upper_bound_m11`: the halting tape holds N ones with
  `N + 1 < f_omega1 (f_omega (f_omega 6))`, so σ = N + 1 is below f_(ω+1)(f_ω(f_ω(6)));
- `BB11_M11b_upper.sigma_bracket_m11`: both bounds for the same N;
- `BB11_M11b_vs_n1.M11_beats_n1`: n1's halting tape holds Nn ones with `Nn + 1 < f_omega1 (f_omega 44)` (from
  n1's upper bound `BB10_n1_fgh.fgh_level`), and Nn + 1 < Nm + 1 for M11b's Nm: M11b's score is larger.

The fast-growing hierarchy is the standard one, defined in `BB11_M11b_fgh.v`: `f 0 n = n+1`,
`f (k+1) n = (f k)^n n`, `f_omega n = f n n`, `f_omega1 n = f_omega^n n`. `ones c N` says that `c`'s tape is a
finite word padded with 0s on both sides holding N ones. The machine halts in state F reading 0, and the halting
transition writes 1, so the standard score is N + 1.

## Files

| file | content |
|---|---|
| `BB112.v`, `Individual112.v` | busycoq instantiated for 11 states |
| `BB11_M11b.v` | the halting proof: configuration families, shift and cascade rules, the maps `W`, `Kc`, `Bridge`, the run |
| `BB11_M11b_fgh.v` | the exact score and the lower bounds; imports the halting file unchanged |
| `BB11_M11b_upper.v` | the upper bound (written here, not by Argon): W against the hierarchy, the bridge, phase 2 |
| `BB11_M11b_vs_n1.v` | the comparison with n1 |
| `BB102.v`, `Individual102.v`, `BB10_*.v` | n1's development, byte-identical to [`../../BB10/verify/multifile/`](../../BB10/verify/multifile/) |
| `probe.v`, `probe_vs_n1.v` | the independent probes (below) |
| `compile_clean.sh`, `compile_vs_n1.sh`, `_CoqProject` | build scripts, project file |
| `compile_clean.log`, `probe.log`, `compile_vs_n1.log`, `probe_vs_n1.log`, `sha256.txt` | logs of from-scratch builds, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh      # 21 s
    BUSYCOQ=/path/to/busycoq/verify ./compile_vs_n1.sh      # about 6 minutes, after compile_clean.sh

`probe.v` checks the compiled transition table against the machine string entry by entry (lines generated from the
string, not from the Coq file), prints the definitions the statements use, and runs `Print Assumptions` on the
first six theorems above: all six are closed under the global context. CI job `bb13-bb14` runs
`compile_clean.sh`. `probe_vs_n1.v` checks n1's table against its string and runs `Print Assumptions` on
`M11_beats_n1` (closed).

Changes from Argon's files (`BB11_M11.v`, `BB11_M11_fgh.v`): the files and modules were renamed to `M11b`; line 1
of the halting file was changed from a heading that stated `f_(omega+1)(f_omega(f_omega 6))` to the proved bound;
the comparison with n1 was moved out of the bound file and the comparison with n1_plus1 (an unpublished machine) was
dropped. The bound file did not compile as written. `Transparent W` leaked out of a lemma, so a `reflexivity` tried
to evaluate W_4(1) and W_6(1) in unary (it reached 27 GB before it was stopped). It was repaired without changing
any statement: `Opaque W Kc` after use, an off-by-one in `w10_1_bound`, `cbn [fst snd]` for a bare `cbn`, an
`iter_ext` lemma for four broken inductions, one rewrite per hypothesis, and the lemma `f_omega1_S_lt` so that no
closed tower is reduced.
