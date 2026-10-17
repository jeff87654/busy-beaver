# Coq proofs for `1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD` (BB(4,3) champion)

This directory is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1), with logical root `TM43`. For this 4-state, 3-symbol machine (C0 = `1RZ` is the halt, `None` in Coq) it
proves:

- `BB43_run.bb43_halts : halts tm c0` -- the machine halts from the blank tape;
- `BB43_run.reaches_final : c0 -->* c_final` and `BB43_run.final_halted : halted tm c_final`, where
  `c_final = C;; const 0 {{0}} [1]^^(4 * e4 + 17) *> const 0`: state C reads a 0, with exactly 4·e4 + 17 ones to its
  right and blanks everywhere else. The halting transition C0 = `1RZ` writes one more 1, so the final tape is
  1^(4·e4 + 18) and `sigma := 4 * e4 + 18`;
- `BB43_run.e4_eq : e4 = E4 e1 v` -- the exact value, as the recursion `g`, `f1`, `G`, `e1`, `v`, `E2`, `E3`, `E4`
  (printed by `probe.v`);
- `BB43_score.sigma_lower : knuth 3 2 (knuth 3 2 (knuth 3 2 (2 ^ 96 - 1))) < sigma`, that is
  2↑↑↑2↑↑↑2↑↑↑(2^96 − 1) < σ, where `knuth n a b` is Knuth's a ↑^n b (`knuth 0 a b = a * b`,
  `knuth (n+1) a b = (knuth n a)^b 1`);
- `BB43_score.e4_bounds : P (P (P (2 ^ 96 - 1))) < e4 /\ e4 <= P (P (P (2 ^ 96 + 6)))` with `P = knuth 3 2`, and
  `sigma_bounds`, the same bracket for σ;
- `BB43_score.wiki_bracket : P (P (P (792 * 10 ^ 26))) < e4 /\ e4 < P (P (P (793 * 10 ^ 26)))`, the bbchallenge
  wiki's bracket (Polygon, October 2025);
- `BB43_score.bb43_main`: halting, the exact halting configuration and `sigma = 4 * E4 e1 v + 18` in one statement.

## Files

| file | content |
|---|---|
| `BB43.v`, `Individual43.v` | busycoq instantiated for 4 states and 3 symbols (after busycoq's `BB33.v`), with notations `0`, `1`, `2` for the symbols |
| `BB43_rules.v` | the transition table `tm`, the sweeps, the rules P6, R10–R23, the configuration family `DL`, the counting rules `DL_b`, `DL_3`, `DL_3k` and the edge rules R25–R28 |
| `BB43_run.v` | the residues mod 3, the run from blank (`start`, 80 steps by `execute`), `chain`, `reaches_final`, `final_halted`, `bb43_halts`, `e4_eq`, `sigma` |
| `BB43_score.v` | Knuth arrows `knuth`, their monotonicity, lower and upper bounds on `f1`, `G` and the cascades, `sigma_lower`, `e4_bounds`, `wiki_bracket`, `sigma_bounds`, `bb43_main` |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build, hashes of the source files |

The six `.v` files are the ones of the development where the proof was written, unchanged except that line endings
were normalized to LF.

## Check it

    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

This compiles the 5 files in dependency order (about 75-110 s; `BB43_rules.v` takes most of it) and then runs `probe.v`,
writing `probe.log`. `BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with
`Individual.vo` built. COQC may name a specific `coqc`. `_CoqProject` (for editors) assumes busycoq is checked out
at the root of this repository; the build script does not use it. The GitHub workflow (`.github/workflows/coq.yml`,
job `bb43`) runs the same build and probe on every push.

`probe.v`:

- parses the machine string inside Coq and checks by `vm_compute` that all 12 entries of `tm` equal the parsed
  entries (`table_matches_string`), that the halting entry C0 is `1RZ` (`halt_entry`), and that `c0` is state A on
  the all-0 tape (`c0_is_blank_A`);
- checks by `reflexivity` the shape of the halting configuration (`c_final_shape`) and `sigma = 4 * e4 + 18`;
- prints the types of `bb43_halts`, `reaches_final`, `sigma_lower`, `bb43_main`, `e4_bounds`, `wiki_bracket`,
  `sigma_bounds`, `e4_eq` and the definitions `E4`, `E3`, `E2`,
  `G`, `f1`, `g`, `e1`, `v`, `sigma`;
- runs `Print Assumptions` on 13 theorems: `table_matches_string`, `halt_entry`, `c0_is_blank_A`, `c_final_shape`,
  `bb43_halts`, `reaches_final`, `final_halted`, `sigma_lower`, `e4_eq`, `bb43_main`, `e4_bounds`, `wiki_bracket`,
  `sigma_bounds`.

Expected: `probe.log` starts with thirteen lines

    Closed under the global context

and does not contain `Axioms:`.

## Verification record

`compile_clean.log` and `probe.log` are from a from-scratch build on 2026-10-17: Coq 8.20.1 (Coq Platform 2025.01),
Windows 11, a shared 16-core laptop, coqc at Idle priority. A fresh directory held only the six `.v` files,
`_CoqProject` and `compile_clean.sh`, next to busycoq `verify/` exported from commit `bd2e36f` (`git archive`) with its
7 needed files compiled first. Command: `BUSYCOQ=../busycoq/verify ./compile_clean.sh` (exit 0, 75 s
including the probe; `BB43_rules.v` 46 s). stderr was empty. `sha256.txt` has the hashes of the sources.
