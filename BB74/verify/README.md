# Coq proofs for the BB(7,4) machine `3RD1LE2RA1LF_..._1LD2RA2LG0RB`

This is a Coq/busycoq development (Coq 8.20.1, busycoq commit `bd2e36f`) with
logical root `TM74`.  It proves, without axioms, that the machine halts from
the blank tape and that its sigma score is `2*mfin+7`.  The score
inequality formalised here is

    f_omega3 21 < sigma        (f_omega3 = f_(omega+3)) .

## Main theorems

- `BB74_run.bb74_halts : halts tm c0`.
- `BB74_run.reaches_final : c0 -->* c_final` and
  `BB74_run.final_halted : halted tm c_final`, where state F reads the final 3.
- `BB74_run.sigma := 2 * mfin + 7`, with `mfin := m24` sealed behind a `sig`.
  `final_cells_count` and `final_cells_all_nonblank` count the nonzero cells.
- `BB74_score.fomega3_21_lt_sigma : f_omega3 21 < sigma`.
- `BB74_score.bb74_main`: halting, final configuration, exact sigma expression
  and the formalised FGH lower bound in one statement.

Supporting facts: `BB74_rules.B_rule`, `rule2`, `rule3a`, `rule3b`, `rule3c`,
`halt_from_B`; `BB74_score.g_closed`, `desc_closed_gen`, `round_closed`,
`round_gt_fomega`, `iter_fo_lt_R_offset`, `gamma_eq_achain`,
`iter_fomega2_lt_gamma`, and the Knuth monotonicity lemmas.

## Files

| file | content |
|---|---|
| `BB74.v`, `Individual74.v` | busycoq instantiation for 7 states and 4 symbols (states A..G) and tape notations |
| `BB74_rules.v` | transition table `tm`, sweeps, `Bcfg`, `g`, `B_rule`, `rule2`, `rule3a`, `rule3b`, `rule3c`, `halt_from_B` |
| `BB74_start.v` | generated 730-step run from the blank tape, cut into 10-step chunks |
| `BB74_run.v` | `desc`, `round`, `next`, `gamma`, sealed `mfin`, `c_final`, halting and `sigma` |
| `BB74_score.v` | Knuth arrows, closed forms, FGH comparison lemmas and `bb74_main` |
| `probe.v` | re-parses the machine string; prints and checks the main theorems |
| `compile_clean.sh`, `_CoqProject` | build script and editor project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | build record |

## Check it

    BUSYCOQ=D:/busycoq/verify ./compile_clean.sh

The script compiles the six files in dependency order and then `probe.v`.
Expected `probe.log`: the main statements *closed under the global context*
and no `Axioms:` line.

`probe.v` checks by `vm_compute` that the Coq table `tm` equals the machine
string, including the halting entry `F3 = 1RZ`.
