# Coq proofs for `1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0LO_1LP1RR_0RB1LI_1RS0LQ_1LN0LR_0LR1RZ` (M19_fw4_A)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For this machine (S1 undefined = the halt, `1RZ` in the string) it proves:

- `BB19_fw4_fw3_9.halt : halts tm c0`: the machine halts from the blank tape;
- `BB19_fw4_fw3_9.score_exact`: the halting tape holds exactly `fst pa_final + snd pa_final + 234` ones, where
  `pa_final` is the explicit pair computed by the run (`BB19_fw4_fw3_9.v`: `pa_R1 = Kd2_iter 9 pa_0`,
  `pa_final = Kcd_iter (snd pa_R1 + 5) (Kpark pa_R1)`);
- `BB19_fw4_fw3_9.sigma_lower_bound`: the halting tape holds N ones with `f_omega4 (f_omega3 9) < N`.

As published:

    Theorem halt : halts tm c0.
    Theorem score_exact :
      exists c, c0 -->* c /\ halted tm c /\ ones c (fst pa_final + snd pa_final + 234).
    Theorem sigma_lower_bound :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega4 (f_omega3 9) < N.

Since the machine is deterministic, the halted configuration reached from `c0` is unique, so these say that the
score is that N. The file also proves `sigma_bound` (the same statement written `n > f_omega4 (f_omega3 9)`;
`sigma_lower_bound` is proved by `exact sigma_bound`) and `pa_final_dom`
(`ok_pa (2 * X) pa_final` for X = `f_omega4 (f_omega3 9)`, that is `2 * X <= fst pa_final - 5` and
`8 * X + 6 <= snd pa_final`), from which the bound follows. The fast-growing hierarchy is the standard one, defined in
`BB19_fw4_fw3_9.v`: `f 0 n = n+1`, `f (k+1) n = (f k)^n n`, `f_omega n = f n n`, `f_omega1 n = f_omega^n n`,
`f_omega2 n = f_omega1^n n`, `f_omega3 n = f_omega2^n n`, `f_omega4 n = f_omega3^n n`; `iter 0 g x = x`,
`iter (n+1) g x = g (iter n g x)`. `ones c N` says that `c`'s tape is a finite word padded with 0s on both sides
holding N ones. The machine halts in state S reading 1, and the halting transition writes 1, so the standard score
is σ = N.

## Files

| file | content |
|---|---|
| `BB192.v`, `Individual192.v` | busycoq instantiated for 19 states (the same files as in [`../verify/`](../verify/)). The 17th, 18th and 19th states (letters Q, R and S of the machine string) are the constructors `QQ`, `RR` and `SS`, because `Q` is busycoq's state type, `R` its direction and `S` is `Datatypes.S`. The states `L` and `O` shadow busycoq's direction `L` and `Datatypes.O`, so tables write `TM.L` / `TM.R`. |
| `BB19_fw4_fw3_9.v` | Argon's proof, unchanged: the table, the engine lemmas of M18_4round's `BB18_4round_fw3.v` re-proved for this table (`bounce_155`, `P0_bounce`, `Kd1_loop`, `D1_cycle_all`, `Kd2_loop`, `Kd2_alt_loop`), the new lemmas (`SWEEP_park`, `SWEEP_cd`, `Kpark_all`, `Kcd_step_all`, `Kcd_loop`, `HALT_step`, `run_to_end`), the domination lemmas (`Kpark_dom`, `Kcd_step_dom`, `Kcd_iter_dom`, `pa_final_dom`) and the score section. |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build (about 50 s) and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `probe.v` checks the compiled transition table against the machine string entry by entry
(38 checks generated from the string, not from the Coq file) and the blank start configuration. It prints the
definitions the statements use and runs `Print Assumptions` on the three theorems above: all three are closed under
the global context. CI job `bb13-bb14` runs the same script.
