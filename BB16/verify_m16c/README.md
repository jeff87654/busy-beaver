# Coq proofs for `1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RO0LO_1LP0LE_1RZ1LI` (M16_C)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For this machine (P0 undefined = the halt, `1RZ` in the string) it proves:

- `BB16_M16c_fw3.halt : halts tm c0`: the machine halts from the blank tape;
- `BB16_M16c_fw3.halt_f_omega3` (Argon's statement): the run reaches the halted configuration
  `c_end (fst pa_16) (snd pa_16)`, with `X <= fst pa_16 - 5` and `4 * X + 6 <= snd pa_16` for
  `X = f_omega2 (iter 114 f_omega1 (iter 3 f_omega2 (f_omega3 9)))`;
- `BB16_M16c_fw3.score_exact`: the halting tape holds exactly `fst pa_16 + snd pa_16 + 5` ones, where `pa_16` is the
  explicit pair computed by the run (`BB16_M16c_fw3.v`: `pa_0 = (26, W 21 1)`, `pa_9 = Kd2_iter 9 pa_0`, then
  `Kd1_step`, `D1_cycle`, `Kd1_step`, `D1_cycle`, `Kd2_step`, `Kd1_iter 114`, `D1_cycle`);
- `BB16_M16c_fw3.sigma_bound`, `sigma_lower_bound` (the same statement, written with `<`): the halting tape holds N
  ones with `f_omega2 (iter 114 f_omega1 (iter 3 f_omega2 (f_omega3 9))) < N`;
- `BB16_M16c_fw3.sigma_bound_simple`: the halting tape holds N ones with `iter 4 f_omega2 (f_omega3 9) < N`.

As published:

    Theorem halt : halts tm c0.
    Theorem halt_f_omega3 :
      c0 -->* c_end (fst pa_16) (snd pa_16) /\
      halted tm (c_end (fst pa_16) (snd pa_16)) /\
      f_omega2 (iter 114 f_omega1 (iter 3 f_omega2 (f_omega3 9))) <= fst pa_16 - 5 /\
      4 * f_omega2 (iter 114 f_omega1 (iter 3 f_omega2 (f_omega3 9))) + 6 <= snd pa_16.
    Theorem score_exact :
      exists c, c0 -->* c /\ halted tm c /\ ones c (fst pa_16 + snd pa_16 + 5).
    Theorem sigma_bound :
      exists c n, c0 -->* c /\ halted tm c /\ ones c n /\
        n > f_omega2 (iter 114 f_omega1 (iter 3 f_omega2 (f_omega3 9))).
    Theorem sigma_bound_simple :
      exists c n, c0 -->* c /\ halted tm c /\ ones c n /\
        n > iter 4 f_omega2 (f_omega3 9).
    Theorem sigma_lower_bound :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
        f_omega2 (iter 114 f_omega1 (iter 3 f_omega2 (f_omega3 9))) < N.

Since the machine is deterministic, the halted configuration reached from `c0` is unique, so these say that the
score is that N. The fast-growing hierarchy is the standard one, defined in `BB16_M16c_fw3.v`: `f 0 n = n+1`,
`f (k+1) n = (f k)^n n`, `f_omega n = f n n`, `f_omega1 n = f_omega^n n`, `f_omega2 n = f_omega1^n n`,
`f_omega3 n = f_omega2^n n`; `iter 0 g x = x`, `iter (n+1) g x = g (iter n g x)`. `ones c N` says that `c`'s tape
is a finite word padded with 0s on both sides holding N ones. The machine halts in state P reading 0, and the
halting transition writes 1, so the standard score is σ = N + 1.

## Files

| file | content |
|---|---|
| `BB162.v`, `Individual162.v` | busycoq instantiated for 16 states, byte-identical to the copies in [`../verify/multifile/`](../verify/multifile/) (M16_B). The states `L` and `O` shadow busycoq's direction `L` and `Datatypes.O`, so tables write `TM.L` / `TM.R`. |
| `BB16_M16c_fw3.v` | Argon's proof file (received 2026-11-03, sha256 `02f77b221567546f9320da98587c91999174c22a794e33de1c7d70f96c6cab05`), with two packaging changes: its three closing `Print Assumptions` lines moved to the probe, and a short section appended at the end with `sigma_lower_bound` (`Proof. exact sigma_bound. Qed.`, the repository's standard form of the bound). Its first 1587 lines are Argon's file unchanged; Argon's file already had `ones`, `score_exact`, `sigma_bound` and `sigma_bound_simple`. |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build (about 30 s) and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `probe.v` checks the compiled transition table against the machine string entry by entry
(32 checks generated from the string, not from the Coq file) and the blank start configuration. It prints the
definitions the statements use and runs `Print Assumptions` on the six theorems above: all six are closed under
the global context. CI job `bb13-bb14` runs the same script.
