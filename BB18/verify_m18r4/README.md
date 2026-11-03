# Coq proofs for `1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0LO_1LP1LN_0RB1LI_1RR0LO_0RO1RZ` (M18_4round)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For this machine (R1 undefined = the halt, `1RZ` in the string) it proves:

- `BB18_4round_fw3.halt : halts tm c0`: the machine halts from the blank tape;
- `BB18_4round_fw3.score_exact`: the halting tape holds exactly `fst pa_R4 + snd pa_R4 + 233` ones, where `pa_R4`
  is the explicit pair computed by the run (`BB18_4round_fw3.v`: `pa_R1 = Kd2_iter 9 pa_0`,
  `pa_R2 = Round_step pa_R1`, `pa_R3 = Round_step pa_R2`, `pa_R4 = Round_step pa_R3`);
- `BB18_4round_fw3.sigma_lower_bound`: the halting tape holds N ones with `iter 4 f_omega3 9 < N`.

As published:

    Theorem halt : halts tm c0.
    Theorem score_exact :
      exists c, c0 -->* c /\ halted tm c /\ ones c (fst pa_R4 + snd pa_R4 + 233).
    Theorem sigma_lower_bound :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ iter 4 f_omega3 9 < N.

Since the machine is deterministic, the halted configuration reached from `c0` is unique, so these say that the
score is that N. The file also proves `halt_f_omega3_4` (the run reaches `c_end (fst pa_R4) (snd pa_R4)`, with
`iter 4 f_omega3 9 <= fst pa_R4 - 5` and `4 * iter 4 f_omega3 9 + 6 <= snd pa_R4`), from which the bound follows.
The fast-growing hierarchy is the standard one, defined in `BB18_4round_fw3.v`: `f 0 n = n+1`,
`f (k+1) n = (f k)^n n`, `f_omega n = f n n`, `f_omega1 n = f_omega^n n`, `f_omega2 n = f_omega1^n n`,
`f_omega3 n = f_omega2^n n`; `iter 0 g x = x`, `iter (n+1) g x = g (iter n g x)`. `ones c N` says that `c`'s tape
is a finite word padded with 0s on both sides holding N ones. The machine halts in state R reading 1, and the
halting transition writes 1, so the standard score is σ = N.

## Files

| file | content |
|---|---|
| `BB182.v`, `Individual182.v` | busycoq instantiated for 18 states (the same files as in [`../verify/`](../verify/)). The 17th and 18th states (letters Q and R of the machine string) are the constructors `QQ` and `RR`, because `Q` is busycoq's state type and `R` its direction. The states `L` and `O` shadow busycoq's direction `L` and `Datatypes.O`, so tables write `TM.L` / `TM.R`. |
| `BB18_4round_fw3.v` | Argon's proof: the table, the engine lemmas of M16_B's `BB16_halt_fw3.v` re-proved for this table, the new lemmas (`Kd2_alt_loop`, `bounce_155`, `P0_bounce`, `SWEEP_1`, `SWEEP_001`, `ROUND_after_sweep`, `Round_1_step`, `Round_001_step`, `run_to_end`), the domination lemmas and the score section. |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build (about 50 s) and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `probe.v` checks the compiled transition table against the machine string entry by entry
(36 checks generated from the string, not from the Coq file) and the blank start configuration. It prints the
definitions the statements use and runs `Print Assumptions` on the three theorems above: all three are closed under
the global context. CI job `bb13-bb14` runs the same script.
