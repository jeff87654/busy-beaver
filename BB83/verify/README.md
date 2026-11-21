# Coq proofs for the BB(8,3) machine `2LH1LE2RA_..._2RD1LF1LG`

This is a Coq/busycoq development (Coq 8.20.1, busycoq commit `bd2e36f`) with
logical root `TM83`.  It proves, without axioms, that the machine halts from
the blank tape and that its sigma score is `2*mfin+7`.  The score
inequality formalised here is

    f_omega1^3 (f_omega^3 14) < sigma .

## Main theorems

- `BB83_run.bb83_halts : halts tm c0`.
- `BB83_run.reaches_final : c0 -->* c_final` and
  `BB83_run.final_halted : halted tm c_final`, where state F reads the final 2.
- `BB83_run.sigma := 2 * mfin + 7`, with `mfin := m5` sealed behind a `sig`.
  `final_cells_count` and `final_cells_all_nonblank` count the nonzero cells.
- `BB83_score.fomega1_iter3_lt_sigma : Nat.iter 3 f_omega1 (Nat.iter 3 f_omega 14) < sigma`.
- `BB83_score.bb83_main`: halting, final configuration, exact sigma expression
  and the formalised FGH lower bound in one statement.

Supporting facts: `BB83_rules.B_rule`, `rule2`, `rule3a`, `rule3b`,
`halt_from_B`; `BB83_score.g_closed`, `desc_closed_gen`, `round_closed`,
`round_gt_fomega`, `iter_fo_lt_R_offset`, and the Knuth monotonicity lemmas.

## Files

| file | content |
|---|---|
| `BB83.v`, `Individual83.v` | busycoq instantiation for 8 states and 3 symbols (states A..H) and tape notations |
| `BB83_rules.v` | transition table `tm`, sweeps, `Bcfg`, `g`, `B_rule`, `rule2`, `rule3a`, `rule3b`, `halt_from_B` |
| `BB83_start.v` | generated 152-step run from the blank tape, cut into 10-step chunks |
| `BB83_run.v` | `desc`, `round`, `next`, sealed `mfin`, `c_final`, halting and `sigma` |
| `BB83_score.v` | Knuth arrows, closed forms, FGH comparison lemmas and `bb83_main` |
| `probe.v` | re-parses the machine string; prints and checks the main theorems |
| `compile_clean.sh`, `_CoqProject` | build script and editor project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | build record |

## Check it

    BUSYCOQ=D:/busycoq/verify ./compile_clean.sh

The script compiles the six files in dependency order and then `probe.v`.
Expected `probe.log`: 9 occurrences of `Closed under the global context` and
no `Axioms:` line.

`probe.v` checks by `vm_compute` that the Coq table `tm` equals the machine
string, including the halting entries `D2 = 0RH` and `F2 = 1RZ`.
