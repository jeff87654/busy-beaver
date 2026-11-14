# Coq proofs for 44-C (`1RB3LB1RZ2RA_1LC3RB1LD2RA_3RB2LC1LC3LC_3RB1LB3LD2RD`, BB(4,4))

A Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`, Coq 8.20.1), with
logical root `Local`. The five proof files are Argon's, unchanged. For this 4-state, 4-symbol machine (A2 = `1RZ` is
the halt, `None` in Coq) it proves:

- `BB44_run.bb44_halts : halts tm c0`: the machine halts from the blank tape;
- `BB44_run.reaches_final : c0 -->* c_final` and `BB44_run.final_halted : halted tm c_final`, where
  `c_final = Bcfg (S (2 * g30)) 0 M44_final (2 >> 1 >> const 0)`, i.e. `0^inf 3^(2M+1) 2^65533 A> 2 1 0^inf` with
  `g30 = g_3(0)` and `M = M44_final = g_(2·g30)^4(0)` (both sealed behind a `sig`);
- `BB44_run.final_cells_count : length final_cells = sigma` and `final_cells_all_nonblank`, with
  `final_cells = 3^(2M+1) 2^(2·g30+1) 1 1` (the tape after the halting write) and `sigma = 2M + 2·g30 + 4`;
- `BB44_bound.sigma_exact_closed_form : sigma = knuth (2 ^ 16 - 4) 2 6 + (2 ^ 16 - 4)`, that is
  **σ = 2 ↑^65532 6 + 65532**, with `knuth n a b` Knuth's a ↑^n b (`knuth 0 a b = a * b`,
  `knuth (n+1) a b = (knuth n a)^b 1`, the same Fixpoint as in [`../verify/BB44_score.v`](../verify/BB44_score.v));
- `BB44_bound.sigma_beats_official_bb44 : knuth 509 2 3 + 510 < sigma`;
- `BB44_bound.bb44_new_champion_main`: all of the above in one statement.

`BB44C_vs_loader3229.v` (written here) loads this development and loader3229's ([`../verify/`](../verify/), logical
root `TM44`) and proves

- `knuth_same : forall n a b, TM44.BB44_score.knuth n a b = Local.BB44_bound.knuth n a b`;
- `beats_loader3229_exact : TM44.BB44_run.sigma < Local.BB44_run.sigma` (loader3229's `sigma_eq` and the theorem
  above);
- `beats_loader3229_score : length TM44.BB44_run.final_cells < length Local.BB44_run.final_cells`.

## Files

| file | content |
|---|---|
| `BB44.v`, `Individual44.v` | busycoq instantiated for 4 states and 4 symbols (`BB44.v` byte-identical to `../verify/BB44.v`; `Individual44.v` the same up to the logical root) |
| `BB44_rules.v` | the transition table `tm`, sweeps, `turnaround`, `B_rule` (Ligocki's descent, double induction), the 22-step start `start44_to_B4`, `C_lift` |
| `BB44_run.v` | sealed constants, `reaches_final`, `final_halted`, `bb44_halts`, the final tape and its count |
| `BB44_bound.v` | Knuth arrows, the closed forms, `sigma_exact_closed_form`, `sigma_beats_official_bb44`, `bb44_new_champion_main` |
| `BB44C_vs_loader3229.v` | the comparison with the previous entry (above) |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build, hashes of the source files |

## Check it

    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

It compiles the five proof files, then (building `../verify` first if its `.vo` files are missing) the comparison,
then the probe. `probe.v` checks the compiled transition table against the machine string entry by entry (16 lines
generated from the string, not from the Coq file), prints the definitions the statements use, and runs
`Print Assumptions` on 11 theorems: all are closed under the global context. CI job `bb44` builds `../verify` and
then this directory.
