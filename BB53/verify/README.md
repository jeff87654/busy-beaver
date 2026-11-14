# Coq proofs for 53-Main (`1RB1LC1RA_1LA2LC1RB_1LB1LD2LC_2RE2LD1RA_1RZ2RE1RB`, BB(5,3))

A Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`, Coq 8.20.1), with
logical root `Local`. The five proof files are Argon's, unchanged. For this 5-state, 3-symbol machine (E0 = `1RZ` is
the halt, `None` in Coq) it proves:

- `BB53_run.bb53_halts : halts tm c0`: the machine halts from the blank tape;
- `BB53_run.reaches_final : c0 -->* c_final` and `BB53_run.final_halted : halted tm c_final`, where
  `c_final = 0^inf 2^(2M+5) E> 0^inf` with `M = M53_final` (sealed behind a `sig`, as are the intermediate
  M2_0 … M2_4 and M3_0);
- `BB53_run.final_cells_count : length final_cells = sigma` and `final_cells_all_nonblank`, with `final_cells` the
  tape after the halting write and `sigma = 2M + 6`;
- `BB53_bound.sigma_exceeds_f_omega2 : f_omega (knuth 8 2 3) < sigma /\ f_omega (f_omega 7) < sigma`, where
  `knuth n a b` is Knuth's a ↑^n b (`knuth 0 a b = a * b`, `knuth (n+1) a b = (knuth n a)^b 1`) and
  `f_omega n = knuth n 2 n` = 2 ↑^n n (not the FGH f_ω);
- `BB53_bound.sigma_beats_official_bb43 : knuth 3 2 (knuth 3 2 (knuth 3 2 (2 ^ 96))) < sigma` (the name is Argon's;
  the number is the shape of the BB(4,3) entry's lower bound, not an upper bound of its σ);
- `BB53_bound.bb53_new_champion_main`: all of the above in one statement.

## Files

| file | content |
|---|---|
| `BB53.v`, `Individual53.v` | busycoq instantiated for 5 states and 3 symbols |
| `BB53_rules.v` | the transition table `tm`, sweeps, `turnaround`, `B_rule`, `lift_from_1`, `even_round`, `K_drain_step`, `K_drain_even`, `halt_from_2`, the 113-step start `start53_to_round2` |
| `BB53_run.v` | sealed constants, `reaches_final`, `final_halted`, `bb53_halts`, the final tape and its count |
| `BB53_bound.v` | Knuth arrows, `f_omega`, closed forms, the bounds, `bb53_new_champion_main` |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build, hashes of the source files |

## Check it

    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`probe.v` checks the compiled transition table against the machine string entry by entry (15 lines generated from
the string, not from the Coq file), prints the definitions the statements use, and runs `Print Assumptions` on 8
theorems: all are closed under the global context. CI job `bb53` runs the same script.
