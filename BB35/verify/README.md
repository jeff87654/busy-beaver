# Coq proofs for `1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC` (BB(3,5) champion)

This directory is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq)
(Coq 8.20), with logical root `TM35`.  For this 3-state, 5-symbol machine (B4 = `1RZ` is the
halt, `None` in Coq) it proves:

- `BB35_run.bb35_halts : halts tm c0` -- the machine halts from the blank tape;
- `BB35_run.reaches_final : c0 -->* c_final` and `BB35_run.final_halted : halted tm c_final`,
  where `c_final = ([3]^^(2 * mfin + 3) *> const 0) {{B}}> (4 >> const 0)`: state B reads the
  4 that follows the block of `2 * mfin + 3` threes, with blanks everywhere else.  The halting
  transition B4 = `1RZ` writes a 1 over that 4, so the final tape is
  `0^inf 3^(2 mfin + 3) 1 Z> 0^inf` and `sigma := 2 * mfin + 4`;
- `BB35_run.g15_eq : g15 = Nat.iter 3 (g 15) 0` -- the exact value of the score-carrying
  number, as the recursion `g` (printed by `probe.v`);
- `BB35_score.sigma_closed : sigma = aw 0 (2 * g15 + 16) 4`, i.e.
  **σ = 2 ↑^0 (2 ↑^1 (… (2 ↑^(2 g15 + 15) 4) …))**, where `aw j n x` is the nested Knuth
  expression and `knuth n a b` is Knuth's `a ↑^n b` (`knuth 0 a b = a * b`,
  `knuth (n+1) a b = (knuth n a)^b 1`);
- `BB35_score.fomega_lt_sigma : f_omega (knuth 15 2 5) < sigma`, i.e. **σ > f_ω(2 ↑^15 5)**,
  where `f_omega n = 2 ↑^(n+1) (n+3)` is the arrow normal form of the omega-th element of the
  fast-growing hierarchy;
- `BB35_score.g_closed : 2 * g (S k) m + 4 = knuth k 2 (2 * m + 4)` and
  `BB35_score.g_iter_closed : 2 * Nat.iter n (g k) 0 + 4 = knuth k 2 (n + 2)` -- the closed
  form of the `g` hierarchy (Ligocki's theorem);
- `BB35_score.desc_closed_gen : 2 * desc n m + 4 = aw 0 n (2 * m + 4)` -- the closed form of
  the rule-2 phase;
- `BB35_rules.B_rule : Bcfg (S k) n m r -->* Bcfg (S k) 0 (Nat.iter n (g k) m) r` -- Ligocki's
  Theorem 3, the double induction;
- `BB35_rules.rule1 / rule2 / rule3` -- the three BB(3,5)-specific rules;
- `BB35_score.bb35_main`: halting, the exact halting configuration and `σ > f_ω(2 ↑^15 5)` in
  one statement.

## Files

| file | content |
|---|---|
| `BB35.v`, `Individual35.v` | busycoq instantiated for 3 states and 5 symbols (after busycoq's `BB33.v`), with notations `0`, `1`, `2`, `3`, `4` for the symbols |
| `BB35_rules.v` | the transition table `tm`, the elementary sweeps, Lemma 1 (`L1`), Corollary 2 (`Cor2`), the turnaround (`turnaround`) and its generalisation (`GT`), the configuration family `Bcfg`, the function `g`, the main rule `B_rule` (the double induction) and the three new rules `rule1`, `rule2`, `rule3` |
| `BB35_start.v` | the 241-step run from the blank tape, cut into chunks of 10 steps; `start_raw : c0 -->* cfg_241` |
| `BB35_run.v` | the sealed `g15`, `B_rule_gen`/`B_rule_15`, the start lemma `start`, the rule-2 phase (`desc`, `rule2_step`, `rule2_phase`), `c_after1`, `c_after2`, `c_final`, `reaches_final`, `final_halted`, `bb35_halts` |
| `BB35_score.v` | Knuth arrows `knuth`, the closed form of the `g` hierarchy (`g_closed`, `g_iter_closed`, `g_iter_closed_gen`), `g15_closed`, the nested expression `aw` (`aw_shift`, `aw_chain`), `desc_closed_gen`, `f_omega`, `sigma`, the counting lemmas, `sigma_closed`, `sigma_gt_fomega`, `fomega_lt_sigma`, `bb35_main` |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build, hashes of the source files |
| `coq_quirks.md` | the non-obvious pitfalls of this development |

## Check it

    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

This compiles the 6 files in dependency order (about 30 s; `BB35_start.v` takes most of it) and
then runs `probe.v`, writing `probe.log`.  `BUSYCOQ` must point to the `verify/` directory of a
busycoq checkout with `Individual.vo` built.  COQC may name a specific `coqc`.  `_CoqProject`
(for editors) assumes busycoq is checked out at the root of this repository; the build script
does not use it.

`probe.v`:

- parses the machine string inside Coq and checks by `vm_compute` that all 15 entries of `tm`
  equal the parsed entries (`table_matches_string`), that the halting entry B4 is `1RZ`
  (`halt_entry`), and that `c0` is state A on the all-0 tape (`c0_is_blank_A`);
- checks by `reflexivity` the shape of the halting configuration (`c_final_shape`) and that the
  final tape holds exactly `sigma = 2 * mfin + 4` nonzero cells, all of them non-blank
  (`final_tape_cells`);
- prints the statements of `bb35_halts`, `reaches_post`, `reaches_final`, `final_halted`,
  `sigma_closed`, `bb35_main`, `B_rule`, `rule1`, `rule2`, `rule3`, `g_closed`,
  `g_iter_closed`, `g15_closed`, `start`, `sigma`, `c_final` and `f_omega`;
- runs `Print Assumptions` on 35 lemmas and theorems.

Expected: `probe.log` contains 35 lines

    Closed under the global context

and does not contain `Axioms:`.

## Verification record

`compile_clean.log` and `probe.log` are from a from-scratch build on 2025-10-31: Coq 8.20,
Windows 11.  A fresh directory held only the seven `.v` files, `_CoqProject` and
`compile_clean.sh`, next to the busycoq `verify/` directory.  Command:
`BUSYCOQ=D:/busycoq/verify ./compile_clean.sh` (exit 0; `BB35_start.v` 15 s, the other five
2-3 s each; the probe 2 s).  stderr was empty.  `sha256.txt` has the hashes of the sources.

The machine's behaviour is independently cross-checked by the Python tools in `../tools/`
(`trace35b.py` is an absolute-position simulator that recognises the macro shapes, `macro35.py`
scans for the next macro configuration, `probe35.py` checks the rules on small instances).
