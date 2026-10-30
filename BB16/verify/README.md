# Coq proofs for `1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RO0LO_1LP1RM_1RZ1LI` (M16_B)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For this machine (P0 undefined = the halt, `1RZ` in the string) it proves:

- `BB16_halt_fw3.halt : halts tm c0`: the machine halts from the blank tape;
- `BB16_halt_fw3.halt_f_omega3` (Argon's statement): the run reaches the halted configuration `c_end (fst pa_11) (snd pa_11)`,
  and `f_omega2 (f_omega3 9) <= fst pa_11 - 5` and `4 * f_omega2 (f_omega3 9) + 6 <= snd pa_11`;
- `BB16_halt_fw3.score_exact`: the halting tape holds exactly `fst pa_11 + snd pa_11 + 5` ones, where `pa_11` is the
  explicit pair computed by the run (`BB16_halt_fw3.v`, section "Bridge, 11th f_(omega+2) cycle, and halting theorem");
- `BB16_halt_fw3.sigma_lower_bound`: the halting tape holds N ones with `f_omega2 (f_omega3 9) < N`.

As published:

    Theorem halt : halts tm c0.
    Theorem halt_f_omega3 :
      c0 -->* c_end (fst pa_11) (snd pa_11) /\
      halted tm (c_end (fst pa_11) (snd pa_11)) /\
      f_omega2 (f_omega3 9) <= fst pa_11 - 5 /\
      4 * f_omega2 (f_omega3 9) + 6 <= snd pa_11.
    Theorem score_exact :
      exists c, c0 -->* c /\ halted tm c /\ ones c (fst pa_11 + snd pa_11 + 5).
    Theorem sigma_lower_bound :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega2 (f_omega3 9) < N.

The fast-growing hierarchy is the standard one, defined in `BB16_halt_fw3.v`: `f 0 n = n+1`,
`f (k+1) n = (f k)^n n`, `f_omega n = f n n`, `f_omega1 n = f_omega^n n`, `f_omega2 n = f_omega1^n n`,
`f_omega3 n = f_omega2^n n`; `iter 0 g x = x`, `iter (n+1) g x = g (iter n g x)`. `ones c N` says that `c`'s tape
is a finite word padded with 0s on both sides holding N ones. The machine halts in state P reading 0, and the
halting transition writes 1, so the standard score is σ = N + 1.

## Files

| file | content |
|---|---|
| `BB162.v`, `Individual162.v` | busycoq instantiated for 16 states (the setup written for BB16_fw4; its header comment says so). The states `L` and `O` shadow busycoq's direction `L` and `Datatypes.O`, so tables write `TM.L` / `TM.R`. |
| `BB16_halt_fw3.v` | Argon's proof (`halt`, `halt_f_omega3`) with the section "Score in the repository's standard form" added at the end (`sym_val`, `count1`, `ones`, `ones_c_end`, `score_exact`, `sigma_lower_bound`); its two closing `Print Assumptions` lines moved to the probe. Nothing else changed. |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build (about a minute), hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `probe.v` checks the compiled transition table against the machine string entry by entry
(32 checks generated from the string, not from the Coq file) and the blank start configuration. It prints the
definitions the statements use and runs `Print Assumptions` on the four theorems above: all four are closed under
the global context. CI job `bb13-bb14` runs the same script.
