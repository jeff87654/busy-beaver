# Coq proofs for the BB(6,4) machine

`1RB3LC1LD2RA_2RC1RF2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE_0LC0LB0LD1RZ`

This is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (Coq 8.20.1), with logical
root `TM64`.  For this 6-state, 4-symbol machine it proves, axiom-free:

- that the machine halts from the blank tape:
  - **`BB64_run.bb64_halts : halts tm c0`** — busycoq's halting predicate (`F3` is `None` in `tm`);
  - `BB64_run.reaches_c_final : c0 -->* c_final` — the run to the halting configuration;
  - `BB64_run.c_final_halted : halted tm c_final`.
- the exact score:
  - `BB64_score.sigma = 2·m4 + k4 + 5` and `final_cells_count : length final_cells = sigma`;
  - `final_cells_all_nonblank` — every counted cell is nonzero;
  - `BB64_score.bb64_score_main` — halting and the score in one statement.
- the lower bound, in two forms:
  - **`BB64_bound.sigma_beats_four_f_omega1 : f_omega1(f_omega1(f_omega1(f_omega1(2^16)))) < sigma`**
    with `f_omega n = 2 ↑^(n+1) (n+3)` and `f_omega1 n = f_omega^n(n)` (Knuth-arrow majorant);
  - **`FGH_BB64.bb64_fgh_four : Nat.iter 4 (FGH (osucc omega)) (2^16) < BB64_score.sigma`** — the exact
    fast-growing-hierarchy statement `f_(ω+1)^4(65536) < σ`.

## Files

| file | content |
|---|---|
| `BB64.v`, `Individual64.v` | busycoq instantiated for 6 states and 4 symbols, with notations `0`,`1`,`2`,`3` and `{{F}}>` / `<{{F}}` |
| `BB64_rules.v` | the transition table `tm`, the elementary sweeps, Lemma 1 / Corollary 2 / turnaround, the configuration family `Bcfg`, `g`, the main rule `B_rule`, the 54-L `B_sweep`, `D_step`/`D_chain`, the three marker rewrites and `final_halt` |
| `BB64_run.v` | the sealed constants `M1`, `P1`…`P4`, the four rounds `sweep1`…`round4`, `c_final`, `reaches_c_final`, `c_final_halted`, `bb64_halts` |
| `BB64_score.v` | `sigma`, `final_cells` and the exact counting lemmas |
| `BB64_bound.v` | the Knuth/FGH majorant infrastructure: `knuth` and its monotonicity, `g_closed`/`g_iter_closed`, `step_pair_closed`, `dchain_lower`, the `Aseq` slack invariants `first_slack`…`fourth_slack`, and `sigma_beats_four_f_omega1` |
| `../fgh/Ord.v`, `../fgh/KnuthFGH.v` | bundled fast-growing-hierarchy library (logical root `BB8`): ordinal notations `omega`, `osucc`, the family `FGH`, `fw_le_F`, `it_le_ge1` |
| `FGH_BB64.v` | bridges `f_omega1` to `FGH (osucc omega)` and proves `bb64_fgh_four` |
| `probe.v` | independent probe: checks `tm` against all 24 entries of the machine string, the theorem types, and `Print Assumptions` |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | from-scratch build log, probe log, source hashes |

## Big numbers are never evaluated

`g 4` unfolds to an astronomically large term; `2 ↑^3 4` and the constants `M1`, `P1`…`P4`, `Aseq` are far beyond
any arithmetic.  They are kept symbolic: `M1` is sealed behind a `sig`, and `knuth`, `g`, `f_omega`, `f_omega1`,
`N65536`, `P1`…`P4` are declared `Opaque`.  `Aseq` is a `Fixpoint` (one iota step per index) with a proved equality
`Aseq_eq_fomega1` to the iterated form, so no tactic ever normalises a huge `Nat.iter`.  Arithmetic is handled by
`lia`/`nia` on symbolic variables only.

## Check it

    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

This compiles the bundled FGH library and the 7 BB64 files in dependency order, then runs `probe.v`, writing
`probe.log`.  `BUSYCOQ` must point to the `verify/` directory of a busycoq checkout.  `probe.log` should report
`8 of 8 theorems closed under the global context` followed by eight `Closed under the global context` lines — i.e.
no axioms.
