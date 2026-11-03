# Coq proofs for `1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0LO_1LP1LN_0RB1LI_1RZ1LO` (M17_B)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For this machine (Q0 undefined = the halt, `1RZ` in the string) it proves:

- `BB17_halt_fw3.halt : halts tm c0`: the machine halts from the blank tape;
- `BB17_halt_fw3.score_exact`: the halting tape holds exactly `fst pa_final + snd pa_final + 5` ones, where
  `pa_final` is the explicit pair computed by the run (`BB17_halt_fw3.v`: `pa_R1 = Kd2_iter 9 pa_0`,
  `pa_R2 = Round_map pa_R1`, `pa_R3 = Round_map pa_R2`, `pa_R3_114 = Kd1_iter 114 pa_R3`,
  `pa_final = D1_cycle pa_R3_114`);
- `BB17_halt_fw3.sigma_lower_bound`: the halting tape holds N ones with
  `iter 116 f_omega2 (iter 3 f_omega3 9) < N`;
- `BB17_halt_fw3.sigma_lower_bound_fw3_3`: the same with `iter 3 f_omega3 9 < N`.

As published:

    Theorem halt : halts tm c0.
    Theorem score_exact :
      exists c, c0 -->* c /\ halted tm c /\ ones c (fst pa_final + snd pa_final + 5).
    Theorem sigma_lower_bound :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ iter 116 f_omega2 (iter 3 f_omega3 9) < N.
    Theorem sigma_lower_bound_fw3_3 :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ iter 3 f_omega3 9 < N.

Since the machine is deterministic, the halted configuration reached from `c0` is unique, so these say that the
score is that N. The file also proves `halt_f_omega3` (the run reaches `c_end (fst pa_final) (snd pa_final)`, with
`iter 116 f_omega2 (iter 3 f_omega3 9) <= fst pa_final - 5` and `4 * iter 116 f_omega2 (iter 3 f_omega3 9) + 6 <=
snd pa_final`), from which the two bounds follow. The fast-growing hierarchy is the standard one, defined in
`BB17_halt_fw3.v`: `f 0 n = n+1`, `f (k+1) n = (f k)^n n`, `f_omega n = f n n`, `f_omega1 n = f_omega^n n`,
`f_omega2 n = f_omega1^n n`, `f_omega3 n = f_omega2^n n`; `iter 0 g x = x`, `iter (n+1) g x = g (iter n g x)`.
`ones c N` says that `c`'s tape is a finite word padded with 0s on both sides holding N ones. The machine halts in
state Q reading 0, and the halting transition writes 1, so the standard score is σ = N + 1.

## Files

| file | content |
|---|---|
| `BB172.v`, `Individual172.v` | busycoq instantiated for 17 states. The 17th state (letter Q of the machine string) is the constructor `QQ`, because `Q` is busycoq's state type. The states `L` and `O` shadow busycoq's direction `L` and `Datatypes.O`, so tables write `TM.L` / `TM.R`. |
| `BB17_halt_fw3.v` | Argon's proof: the table, the engine lemmas of M16_B's `BB16_halt_fw3.v` re-proved for this table (the Kd2 lemmas stated for a general tail `1 0 1 s`), the new lemmas (`Kd2_alt_loop`, `SWEEP_M17B`, `bounce_156`, `P0_bounce`, `Full_Round`, `run_to_end`), the domination lemmas and the score section. |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log` | logs of a from-scratch build (about 40 s) and of the probe |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `probe.v` checks the compiled transition table against the machine string entry by entry
(34 checks generated from the string, not from the Coq file) and the blank start configuration. It prints the
definitions the statements use and runs `Print Assumptions` on the four theorems above: all four are closed under
the global context. CI job `bb13-bb14` runs the same script.
