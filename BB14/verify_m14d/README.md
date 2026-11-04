# Coq proofs for `1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LL0LL_0LN1LK_1RZ0LH_0LG1LJ` (M14d_18)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For this machine (M0 undefined = the halt, `1RZ` in the string, `---` in Argon's) it proves:

- `BB14_M14d_18.halt : halts tm c0`: the machine halts from the blank tape;
- `BB14_M14d_18.score_exact`: the halting tape holds exactly `fst pa19 + snd pa19 + 5` ones, where `pa19` is the
  explicit pair computed by the run (see `BB14_M14d_18.v`, section "The 19-round trajectory of M14d_18");
- `BB14_M14d_18.sigma_bound`: the halting tape holds N ones with
  `N > iter 18 f_omega2 (iter 2 f_omega 3)`;
- `BB14_M14d_18.sigma_bound_fw1`: the halting tape holds N ones with
  `N > iter 17 f_omega2 (iter 2 f_omega1 3)`.

As published:

    Theorem halt : halts tm c0.
    Theorem score_exact :
      exists c, c0 -->* c /\ halted tm c /\ ones c (fst pa19 + snd pa19 + 5).
    Theorem sigma_bound :
      exists c n, c0 -->* c /\ halted tm c /\ ones c n /\
      n > iter 18 f_omega2 (iter 2 f_omega 3).
    Theorem sigma_bound_fw1 :
      exists c n, c0 -->* c /\ halted tm c /\ ones c n /\
      n > iter 17 f_omega2 (iter 2 f_omega1 3).

The two bound theorems have the same form as the `sigma_lower_bound` theorems of the other entries, under
Argon's names. Since the machine is deterministic, the halted configuration reached from `c0` is unique.

The fast-growing hierarchy is the standard one, defined in `BB14_M14d_18.v`: `f 0 n = n+1`,
`f (k+1) n = (f k)^n n`, `f_omega n = f n n`, `f_omega1 n = f_omega^n n`, `f_omega2 n = f_omega1^n n`;
`iter 0 g x = x`, `iter (n+1) g x = g (iter n g x)`. `ones c N` says that `c`'s tape is a finite word padded with
0s on both sides holding N ones. The machine halts in state M reading 0, and the halting transition writes 1, so
the standard score is σ = N + 1.

## Files

| file | content |
|---|---|
| `BB142.v`, `Individual142.v` | busycoq instantiated for 14 states (byte-identical to `../../verify/multifile/` and `../../verify_m14b/multifile/`). The state `L` shadows busycoq's direction `L`, so tables write `TM.L` / `TM.R`. |
| `BB14_M14d_18.v` | Argon's proof, unchanged: shift and cascade rules, the left walk through N (`D_REL`, `K_REL_step1`–`K_REL_to_5_3`, `step_5_3`, `K_REL`), the 160-step opening, the maps `W`, `Kc`, `Kc_full`, `Kd_step`, `D_round`, `K0_round`/`K1_round`/`K2_round`, the mod-3^13 invariants, the 19-round run, the score and both bounds |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build (about 35 s) and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `probe.v` checks the compiled transition table against the machine string entry by entry
(28 checks generated from the string, not from the Coq file) and the blank start configuration. It prints the
definitions the statements use and runs `Print Assumptions` on the four theorems above: all four are closed under
the global context. CI job `bb13-bb14` runs the same script. (`BB14_M14d_18.v` ends with its own three
`Print Assumptions` lines, so `compile_clean.log` also shows three closed reports while compiling it.)
