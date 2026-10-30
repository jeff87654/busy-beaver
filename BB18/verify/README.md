# Coq proofs for `1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_1RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RQ0RG_0LG1LP_0LO1LP_1LQ0RR_1RZ0LP` (BB18_fw3)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For this machine (R0 undefined = the halt, `1RZ` in the string) it proves:

- `BB18_fw3.halt : halts tm c0`: the machine halts from the blank tape;
- `BB18_fw3.score_exact`: the halting tape holds exactly `fst (Kpass1 pa_init) + snd (Kpass1 pa_init) + 5` ones,
  where `pa_init` is the pair after the opening (`init_pass`) and `Kpass1` is one stack-reflection pass;
- `BB18_fw3.sigma_lower_bound`: the halting tape holds N ones with `f_omega2 (f_omega3 114) < N`;
- `BB18_fw3.sigma_lower_bound_fw3`: the same with `f_omega3 114 < N`.

As published:

    Theorem halt : halts tm c0.
    Theorem score_exact :
      exists c, c0 -->* c /\ halted tm c /\
        ones c (fst (Kpass1 pa_init) + snd (Kpass1 pa_init) + 5).
    Theorem sigma_lower_bound :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega2 (f_omega3 114) < N.
    Corollary sigma_lower_bound_fw3 :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega3 114 < N.

Since the machine is deterministic, the halted configuration reached from `c0` is unique, so these say that the
score is that N. The fast-growing hierarchy is the standard one, defined in `BB18_fw3.v`: `f 0 n = n+1`,
`f (k+1) n = (f k)^n n`, `f_omega n = f n n`, `f_omega1 n = f_omega^n n`, `f_omega2 n = f_omega1^n n`,
`f_omega3 n = f_omega2^n n`; `iter 0 g x = x`, `iter (n+1) g x = g (iter n g x)`. `ones c N` says that `c`'s tape
is a finite word padded with 0s on both sides holding N ones. The machine halts in state R reading 0, and the
halting transition writes 1, so the standard score is σ = N + 1.

## Files

| file | content |
|---|---|
| `BB182.v`, `Individual182.v` | busycoq instantiated for 18 states. The 17th and 18th states (letters Q and R of the machine string) are the constructors `QQ` and `RR`, because `Q` is busycoq's state type and `R` its direction. The states `L` and `O` shadow busycoq's direction `L` and `Datatypes.O`, so tables write `TM.L` / `TM.R`. |
| `BB18_fw3.v` | the proof. Generated from Argon's `BB16_fw4.v` (DUMP_2552): the table (N0 changed, states Q and R added), the pass-start lemmas `P_DUMP_raw` and `P_DUMP_boot` (the counter routine), and the end of the file (`Krel_x`, `Kpass1`, `HALT_step`, `halt`, the score) are new. Every other lemma of `BB16_fw4.v` is unchanged and re-proved for this table. |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build (about 40 s), hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `probe.v` checks the compiled transition table against the machine string entry by entry
(36 checks generated from the string, not from the Coq file) and the blank start configuration. It prints the
definitions the statements use and runs `Print Assumptions` on the four theorems above: all four are closed under
the global context. CI job `bb13-bb14` runs the same script.
