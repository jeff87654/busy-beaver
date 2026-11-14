# Coq proofs for 54-L (`1RB3LC1LD2RA_2RC1RZ2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE`, BB(5,4))

A Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`, Coq 8.20.1), with
logical root `Local`. The five proof files are Argon's, unchanged. For this 5-state, 4-symbol machine (B1 = `1RZ` is
the halt, `None` in Coq) it proves:

- `BB54_run.bb54_halts : halts tm c0`: the machine halts from the blank tape;
- `BB54_run.reaches_final : c0 -->* c_final` and `BB54_run.final_halted : halted tm c_final`, where `c_final` is
  `0^inf 3^(2M+1) 2^(K+1) 1 B> 1 1 0^inf` with (K, M) = (`K_final`, `M_final`) = `Nat.iter (2 * M1 + 5) step_pair (0, 1)`,
  `M1 = g 4 0` (all sealed behind a `sig`);
- `BB54_run.final_cells_count : length final_cells = sigma` and `final_cells_all_nonblank`, with
  `final_cells = 3^(2M+1) 2^(K+1) 1 1 1` (the tape after the halting write) and `sigma = 2M + K + 5`;
- `BB54_bound.sigma_beats_f_omega1_65536 : f_omega1 (2 ^ 16) < sigma` and
  `BB54_bound.sigma_beats_official_bb54 : f_omega2 (knuth 4 2 (knuth 3 2 4)) < sigma`, where
  `f_omega n = knuth (S n) 2 (n + 3)` (2 ↑^(n+1) (n+3), the function of `../verify/BB54_score.v`; not the FGH),
  `f_omega2 n = f_omega (f_omega n)` and `f_omega1 n = Nat.iter n f_omega n`;
- `BB54_bound.bb54_new_champion_main`: all of the above in one statement.

The name `sigma_beats_official_bb54` is Argon's: the theorem is the inequality above. That f_ω²(2 ↑^4 2 ↑^3 4) is
an upper bound for the previous entry's σ is a hand calculation in [`../README.md`](../README.md#the-size-of-σ),
not a Coq proof.

## Files

| file | content |
|---|---|
| `BB54.v`, `Individual54.v` | busycoq instantiated for 5 states and 4 symbols (`BB54.v` byte-identical to `../verify/BB54.v`) |
| `BB54_rules.v` | the transition table `tm`, sweeps, `turnaround`, `B_rule`, the 25-step start `start_to_B5`, `B_sweep`, `D_step`, `D_chain` |
| `BB54_run.v` | sealed constants, `reaches_final`, `final_halted`, `bb54_halts`, the final tape and its count |
| `BB54_bound.v` | Knuth arrows, `f_omega`, closed forms, the two bounds, `bb54_new_champion_main` |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build, hashes of the source files |

## Check it

    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`probe.v` checks the compiled transition table against the machine string entry by entry (20 lines generated from
the string, not from the Coq file), prints the definitions the statements use, and runs `Print Assumptions` on 8
theorems: all are closed under the global context. CI job `bb54` runs the same script.
