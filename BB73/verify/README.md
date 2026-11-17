# Coq proofs for the BB(7,3) machine `2RD1LE2RA_..._1LD2RA2LG`

This is a Coq/busycoq development (Coq 8.20.1, busycoq commit `bd2e36f`) with
logical root `TM73`.  It proves that the machine halts from the blank tape and
that its sigma score exceeds `f_(omega+1)(11)`.

## Main theorems

- `BB73_run.bb73_halts : halts tm c0`.
- `BB73_run.reaches_final : c0 -->* c_final` and `BB73_run.final_halted : halted tm c_final`,
  where `c_final = (1 >> [1]^^(2*mfin+3) *> const 0) {{F}}> (2 >> const 0)`:
  state F reads the final 2, whose halting write adds one last nonzero cell.
- `BB73_run.sigma := 2 * mfin + 5`, with `mfin := round^12(1)` sealed behind a `sig`.
  `final_cells_count` and `final_cells_all_nonblank` count the nonzero cells.
- `BB73_score.fomega1_lt_sigma : f_omega1 11 < sigma`, with
  `f_omega n := knuth (S n) 2 (n+3)` and `f_omega1 n := Nat.iter n f_omega n`.
- `BB73_score.bb73_main`: halting, the final configuration, the exact sigma
  expression and the FGH lower bound in one statement.

Supporting facts: `BB73_rules.B_rule` (the BB34-style Ackermann descent),
`rule2`, `rule3`, `halt_from_B`; `BB73_score.g_closed`, `desc_closed_gen`,
`round_closed`, `round_gt_fomega`, and the Knuth monotonicity lemmas.

## Files

| file | content |
|---|---|
| `BB73.v`, `Individual73.v` | busycoq instantiation for 7 states and 3 symbols (states A..G, symbols 0,1,2) and the tape notations |
| `BB73_rules.v` | the transition table `tm`, elementary sweeps, `Bcfg`, `g`, `B_rule`, `rule2`, `rule3`, `halt_from_B` |
| `BB73_start.v` | generated 255-step run from the blank tape, cut into 10-step chunks |
| `BB73_run.v` | `desc`, `round`, sealed `mfin`, the twelve rounds, `c_final`, halting and `sigma` |
| `BB73_score.v` | Knuth arrows, closed forms, FGH bound and `bb73_main` |
| `probe.v` | re-parses the machine string; prints and checks the main theorems |
| `compile_clean.sh`, `_CoqProject` | build script and editor project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | build record |
| `coq_quirks.md` | pitfalls of this development |

## Check it

    BUSYCOQ=D:/busycoq/verify ./compile_clean.sh

The script compiles the six files in dependency order and then `probe.v`.
Expected `probe.log`: 9 occurrences of `Closed under the global context` and
no `Axioms:` line.

`probe.v` checks by `vm_compute` that the Coq table `tm` equals the machine
string, including the unique halting entry `F2 = 1RZ`, and runs `Print
Assumptions` on the main statements.
