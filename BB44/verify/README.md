# Coq proofs for `0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA` (BB(4,4) champion)

This directory is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1), with logical root `TM44`.  For this 4-state, 4-symbol machine (A2 = `1RZ` is the halt, `None` in Coq) it
proves:

- `BB44_run.bb44_halts : halts tm c0` -- the machine halts from the blank tape;
- `BB44_run.reaches_final : c0 -->* c_final` and `BB44_run.final_halted : halted tm c_final`, where
  `c_final = Bcfg 510 0 g509 (2 1 3 0^inf)`: state A reads the 2 that follows `3^(2 g509 + 1) 2^510`, with blanks
  everywhere else.  The halting transition A2 = `1RZ` writes a 1 over that 2, so the final tape is
  `0^inf 3^(2 g509+1) 2^510 1 Z> 1 3 0^inf` and `sigma := 2 * g509 + 514`;
- `BB44_run.g509_eq : g509 = Nat.iter 1 (g 509) 0` -- the exact value, as the recursion `g` (printed by `probe.v`);
- `BB44_score.sigma_eq : sigma = knuth 509 2 3 + 510`, that is **σ = (2 ↑^509 3) + 510**, where `knuth n a b` is
  Knuth's a ↑^n b (`knuth 0 a b = a * b`, `knuth (n+1) a b = (knuth n a)^b 1`);
- `BB44_score.g_closed : 2 * g (S k) m + 4 = knuth k 2 (2 * m + 4)` and
  `BB44_score.g_iter_closed : 2 * Nat.iter n (g k) 0 + 4 = knuth k 2 (n + 2)` -- the closed form of the `g`
  hierarchy (Ligocki's theorem);
- `BB44_score.sigma_general : 2 * Nat.iter 1 (g k) 0 + 4 = knuth k 2 3` -- the same computation at any level `k`;
- `BB44_rules.B_rule : Bcfg (S k) n m r -->* Bcfg (S k) 0 (Nat.iter n (g k) m) r` -- Ligocki's Theorem 3, the
  double induction;
- `BB44_rules.B_phase : Bcfg 2 0 m (const 0) -->* Bcfg 1 (2*m+2) 0 (const 0)` and
  `BB44_rules.D_phase : Bcfg 1 0 m (const 0) -->* Bcfg (S (2*m+1)) 1 0 (2 1 3 0^inf)` -- the two BB(4,4)-specific
  phases that get the machine into Ligocki's descent (phase B is a five-step cycle that eats the 3-block, phase D is
  a six-part detour through state D);
- `BB44_score.bb44_main`: halting, the exact halting configuration and `sigma = knuth 509 2 3 + 510` in one statement.

## Files

| file | content |
|---|---|
| `BB44.v`, `Individual44.v` | busycoq instantiated for 4 states and 4 symbols (after busycoq's `BB33.v`), with notations `0`, `1`, `2`, `3` for the symbols and `{{D}}` for the extra state |
| `BB44_rules.v` | the transition table `tm`, the elementary sweeps, Lemma 1 (`L1`), Corollary 2 (`Cor2`), the turnaround, the configuration family `Bcfg`, the function `g`, the main rule `B_rule` (the double induction), and the two BB(4,4)-specific phases (`B_phase`, `D_phase` with its loops `Bloop`, `D1_loop`, `D3_loop` and the shape lemma `block_snoc`) |
| `BB44_start.v` | **generated** by `../tools/gen_start.py`: the 98-step run from the blank tape, cut into chunks of 10 steps; `start_raw : c0 -->* cfg_98` |
| `BB44_run.v` | the sealed `g509`, `B_rule_gen`/`B_rule_509`, the start lemma `start`, `c_final`, `reaches_final`, `final_halted`, `bb44_halts`, `sigma`, `final_cells` and the counting lemmas |
| `BB44_score.v` | Knuth arrows `knuth`, the closed form of the `g` hierarchy (`g_closed`, `g_iter_closed`, `g_iter_closed_gen`), `g509_closed`, `score_generic`, `sigma_eq`, `sigma_general`, `bb44_main` |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log` | logs of a from-scratch build |
| `coq_quirks.md` | the non-obvious pitfalls of this development (chunked `execute`, never evaluating `g 509`, and the shape of a block of symbols) |

## Check it

    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

This compiles the 6 files in dependency order (about 20-30 s) and then runs `probe.v`, writing `probe.log`.
`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
built.  COQC may name a specific `coqc`.  `_CoqProject` (for editors) assumes busycoq is checked out at the root of
this repository; the build script does not use it.

`probe.v`:

- parses the machine string inside Coq and checks by `vm_compute` that all 16 entries of `tm` equal the parsed
  entries (`table_matches_string`), that the halting entry A2 is `1RZ` (`halt_entry`), and that `c0` is state A on
  the all-0 tape (`c0_is_blank_A`);
- checks by `reflexivity` the shape of the halting configuration (`c_final_shape`) and that the final tape holds
  exactly `sigma = 2 * g509 + 514` nonzero cells, all of them non-blank (`final_tape_cells`);
- prints the statements of `bb44_halts`, `reaches_final`, `final_halted`, `sigma_eq`, `bb44_main`, `B_rule`,
  `g_closed`, `g_iter_closed`, `g509_closed`, `start`, `sigma`, `c_final`, `B_phase`, `D_phase` and `D_phase_p`;
- runs `Print Assumptions` on 32 lemmas and theorems: `underscores`, `halt_entry`, `table_matches_string`,
  `c0_is_blank_A`, `c_final_shape`, `start`, `start_raw`, `B_rule`, `B_rule_gen`, `B_rule_509`, `B_phase`,
  `Bloop`, `Bloop_step`, `D_phase`, `D_phase_p`, `D1_loop`, `D3_loop`, `block_snoc`, `bb44_halts`,
  `reaches_final`, `final_halted`, `final_cells_count`, `final_cells_all_nonblank`, `g509_eq`, `g_closed`,
  `g_iter_closed`, `g_iter_closed_gen`, `g509_closed`, `score_generic`, `sigma_eq`, `sigma_general`, `bb44_main`.

Expected: `probe.log` contains 32 lines

    Closed under the global context

and does not contain `Axioms:`.

## Verification record

`compile_clean.log` and `probe.log` are from a from-scratch build: Coq 8.20.1, Windows 11.
Command: `BUSYCOQ=D:/busycoq/verify ./compile_clean.sh` (exit 0; the six files take 3-5 s each, the probe 4 s).
stderr contained only deprecation warnings about `app_length`.

The machine's behaviour is independently cross-checked by `../tools/check.py` (a Python simulator): it confirms the
98-step start and the two phases -- `B(2,0,m) 0^inf --> B(1,2m+2,0) 0^inf` in exactly `10m+10` steps and
`B(1,0,m) 0^inf --> B(2m+2,1,0) 2 1 3 0^inf` in exactly `20m+35` steps -- for small parameters.
