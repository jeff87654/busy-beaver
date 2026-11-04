# Coq proofs for `1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC` (BB(3,4) champion)

This directory is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1), with logical root `TM34`.  For this 3-state, 4-symbol machine (A2 = `1RZ` is the halt, `None` in Coq) it
proves:

- `BB34_run.bb34_halts : halts tm c0` -- the machine halts from the blank tape;
- `BB34_run.reaches_final : c0 -->* c_final` and `BB34_run.final_halted : halted tm c_final`, where
  `c_final = Bcfg 16 0 g15 (2 >> const 0)`: state A reads the 2 that follows `3^(2 g15 + 1) 2^16`, with blanks
  everywhere else.  The halting transition A2 = `1RZ` writes a 1 over that 2, so the final tape is
  `0^inf 3^(2 g15+1) 2^16 1 Z> 0^inf` and `sigma := 2 * g15 + 18`;
- `BB34_run.g15_eq : g15 = Nat.iter 3 (g 15) 0` -- the exact value, as the recursion `g` (printed by `probe.v`);
- `BB34_score.sigma_eq : sigma = knuth 15 2 5 + 14`, that is **σ = (2 ↑^15 5) + 14**, where `knuth n a b` is
  Knuth's a ↑^n b (`knuth 0 a b = a * b`, `knuth (n+1) a b = (knuth n a)^b 1`);
- `BB34_score.g_closed : 2 * g (S k) m + 4 = knuth k 2 (2 * m + 4)` and
  `BB34_score.g_iter_closed : 2 * Nat.iter n (g k) 0 + 4 = knuth k 2 (n + 2)` -- the closed form of the `g`
  hierarchy (Ligocki's theorem);
- `BB34_score.sigma_general : 2 * Nat.iter 3 (g k) 0 + 4 = knuth k 2 5` -- the same computation at any level `k`;
- `BB34_rules.B_rule : Bcfg (S k) n m r -->* Bcfg (S k) 0 (Nat.iter n (g k) m) r` -- Ligocki's Theorem 3, the
  double induction;
- `BB34_score.bb34_main`: halting, the exact halting configuration and `sigma = knuth 15 2 5 + 14` in one statement.

## Files

| file | content |
|---|---|
| `BB34.v`, `Individual34.v` | busycoq instantiated for 3 states and 4 symbols (after busycoq's `BB33.v`), with notations `0`, `1`, `2`, `3` for the symbols |
| `BB34_rules.v` | the transition table `tm`, the elementary sweeps, Lemma 1 (`L1`), Corollary 2 (`Cor2`), the turnaround, the configuration family `Bcfg`, the function `g` and the main rule `B_rule` (the double induction) |
| `BB34_start.v` | **generated** by `../tools/gen_start.py`: the 241-step run from the blank tape, cut into chunks of 10 steps; `start_raw : c0 -->* cfg_241` |
| `BB34_run.v` | the sealed `g15`, `B_rule_gen`/`B_rule_15`, the start lemma `start`, `c_final`, `reaches_final`, `final_halted`, `bb34_halts`, `sigma`, `final_cells` and the counting lemmas |
| `BB34_score.v` | Knuth arrows `knuth`, the closed form of the `g` hierarchy (`g_closed`, `g_iter_closed`, `g_iter_closed_gen`), `g15_closed`, `score_generic`, `sigma_eq`, `sigma_general`, `bb34_main` |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build, hashes of the source files |
| `coq_quirks.md` | the two non-obvious pitfalls of this development (chunked `execute`, and never evaluating `g 15`) |

## Check it

    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

This compiles the 6 files in dependency order (about 35-45 s; `BB34_start.v` takes most of it) and then runs
`probe.v`, writing `probe.log`.  `BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit
`bd2e36f`, with `Individual.vo` built.  COQC may name a specific `coqc`.  `_CoqProject` (for editors) assumes
busycoq is checked out at the root of this repository; the build script does not use it.

`probe.v`:

- parses the machine string inside Coq and checks by `vm_compute` that all 12 entries of `tm` equal the parsed
  entries (`table_matches_string`), that the halting entry A2 is `1RZ` (`halt_entry`), and that `c0` is state A on
  the all-0 tape (`c0_is_blank_A`);
- checks by `reflexivity` the shape of the halting configuration (`c_final_shape`) and that the final tape holds
  exactly `sigma = 2 * g15 + 18` nonzero cells, all of them non-blank (`final_tape_cells`);
- prints the statements of `bb34_halts`, `reaches_final`, `final_halted`, `sigma_eq`, `bb34_main`, `B_rule`,
  `g_closed`, `g_iter_closed`, `g15_closed`, `start`, `sigma` and `c_final`;
- runs `Print Assumptions` on 24 lemmas and theorems: `underscores`, `halt_entry`, `table_matches_string`,
  `c0_is_blank_A`, `c_final_shape`, `start`, `start_raw`, `B_rule`, `B_rule_gen`, `B_rule_15`, `bb34_halts`,
  `reaches_final`, `final_halted`, `final_cells_count`, `final_cells_all_nonblank`, `g15_eq`, `g_closed`,
  `g_iter_closed`, `g_iter_closed_gen`, `g15_closed`, `score_generic`, `sigma_eq`, `sigma_general`, `bb34_main`.

Expected: `probe.log` contains 24 lines

    Closed under the global context

and does not contain `Axioms:`.

## Verification record

`compile_clean.log` and `probe.log` are from a from-scratch build on 2026-10-29: Coq 8.20.1 (Coq Platform 2025.01),
Windows 11, a 20-core machine with 24 GB RAM.  A fresh directory held only the seven `.v` files, `_CoqProject` and
`compile_clean.sh`, next to busycoq `verify/` exported from commit `bd2e36f` with its 7 needed files compiled first.
Command: `BUSYCOQ=../busycoq/verify ./compile_clean.sh` (exit 0, 31 s for the six files; `BB34_start.v` 16 s, the
other five 3 s each; the probe 5 s).  stderr contained only deprecation warnings about `app_length`.  `sha256.txt`
has the hashes of the sources.

The machine's behaviour is independently cross-checked by `../tools/sim.py` (a 60-line Python simulator): it
confirms the 241-step start and the final tape, and checks the `B(k,n,m)` rule for small `k`, `n`, `m`.
