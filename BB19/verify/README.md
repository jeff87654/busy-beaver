# Coq proofs for `1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_1RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0RG_0LG1LP_0LO1LP_1LS0RR_1RZ0LP_0LR1LS` (M19_fw4)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For this machine (R0 undefined = the halt, `1RZ` in the string) it proves:

- `BB19_halt_fw4.halt : halts tm c0`: the machine halts from the blank tape;
- `BB19_halt_fw4.score_exact`: the halting tape holds exactly `fst pa_final + snd pa_final + 6` ones, where
  `pa_final = Kcycle pa_init`, `pa_init` is the pair after the opening (`init_pass`) and `Kcycle` is the parking
  pass followed by `snd pa_init / 2 + 3` countdown passes;
- `BB19_halt_fw4.sigma_lower_bound`: the halting tape holds N ones with `f_omega4 (f_omega2 114) < N`;
- `BB19_halt_fw4.sigma_lower_bound_fw4`: the same with `f_omega4 114 < N`.

As published:

    Theorem halt : halts tm c0.
    Theorem score_exact :
      exists c, c0 -->* c /\ halted tm c /\
        ones c (fst pa_final + snd pa_final + 6).
    Theorem sigma_lower_bound :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
        f_omega4 (f_omega2 114) < N.
    Corollary sigma_lower_bound_fw4 :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
        f_omega4 114 < N.

Since the machine is deterministic, the halted configuration reached from `c0` is unique, so these say that the
score is that N. The fast-growing hierarchy is the standard one, defined in `BB19_halt_fw4.v`: `f 0 n = n+1`,
`f (k+1) n = (f k)^n n`, `f_omega n = f n n`, `f_omega1 n = f_omega^n n`, `f_omega2 n = f_omega1^n n`,
`f_omega3 n = f_omega2^n n`, `f_omega4 n = f_omega3^n n`; `iter 0 g x = x`, `iter (n+1) g x = g (iter n g x)`.
`ones c N` says that `c`'s tape is a finite word padded with 0s on both sides holding N ones. The machine halts in
state R reading 0, and the halting transition writes 1, so the standard score is σ = N + 1.

## Files

| file | content |
|---|---|
| `BB192.v`, `Individual192.v` | busycoq instantiated for 19 states. The 17th, 18th and 19th states (letters Q, R and S of the machine string) are the constructors `QQ`, `RR` and `SS`, because `Q` is busycoq's state type, `R` its direction and `S` is `Datatypes.S`. The states `L` and `O` shadow busycoq's direction `L` and `Datatypes.O`, so tables write `TM.L` / `TM.R`. |
| `BB19_halt_fw4.v` | the proof, by Argon. The engine lemmas of `BB16_fw4.v` (DUMP_2552) and `Krel_x` from `BB18_fw3.v`, re-proved for this table; new: the parking pass (`SEED_c1_raw`, `SEED_c1_boot`, `Kseed`, `Kseed_c1_all`), the countdown pass (`CD_DUMP_raw`, `CD_DUMP_boot`, `Kcd_step`, `Kcd_step_all`, `Kcd_loop`), the cycle (`Kcycle`, `Kcycle1_all`), the halt (`HALT_step`, `run_end`, `halt`), the f_(ω+4) bounds (`Kseed_dom`, `Kcd_step_dom`, `Kcd_iter_dom`, `Kcycle_dom`, `pa_final_dom`) and the score. The header comment was rewritten here (Argon's original described a 20-state machine); the proof is unchanged. |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build (about 40 s), hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `probe.v` checks the compiled transition table against the machine string entry by entry
(38 checks generated from the string, not from the Coq file) and the blank start configuration. It prints the
definitions the statements use and runs `Print Assumptions` on the four theorems above: all four are closed under
the global context. CI job `bb13-bb14` runs the same script.
