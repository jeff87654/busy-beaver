# Coq proofs for `1LD3LB---2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_3RB---3LE3LD_------1LD1RZ` (BB(5,4) champion)

This directory is a Coq development on top of
[busycoq](https://github.com/meithecatte/busycoq) (Coq 8.20.1), with logical
root `TM54`.  For this 5-state, 4-symbol machine (E3 = `1RZ` is the halt,
`None` in Coq) it proves:

- `BB54_start.start : c0 -->* Bcfg 2 1 0 (const 0)` -- the 9-step run from the blank tape reaches Ligocki's
  configuration family;
- `BB54_rules.B_rule : Bcfg (S k) n m r -->* Bcfg (S k) 0 (Nat.iter n (g k) m) r` -- Ligocki's Theorem 3, the
  double induction;
- `BB54_rules.D_phase_raw : Bcfg 2 0 m (const 0) -->* Bcfg (2*m+1) 1 0 (3 >> 1 >> const 0)` -- the
  BB(5,4)-specific D/E phase, in which the machine alternates between the states `D` and `E`;
- `BB54_rules.D_phase_halt` and `BB54_rules.D_phase_halt_1` -- the D/E phase with an **odd** number of twos
  halts the machine (`E3 = 1RZ`);
- `BB54_rules.macro_descent`, `BB54_rules.B1_iter`, `BB54_rules.a3_step` -- the three macro steps of the run;
- `BB54_rules.chain : Bcfg 2 (S n) m (3 >> r) -->* Bcfg 2 0 (2^(S n) * (m+2) - 2) (3 >> r)` -- the long chain,
  in which the parameter `m` (the size of the block of threes on the tape) is exponentiated once per unit of `n`;
- `BB54_run.reaches_score : c0 -->* c_score`, where `c_score = Bcfg 5 0 g40 (3 >> 1 >> const 0)`: state A reads
  the 3 that follows `3^(2 g40 + 1) 2^5`, with blanks everywhere else;
- `BB54_score.sigma_eq : sigma = knuth 4 2 3 + 4`, that is **σ = (2 ↑^3 4) + 4 = 2^65536 + 4** at that point of
  the run, where `knuth n a b` is Knuth's a ↑^n b (`knuth 0 a b = a * b`, `knuth (n+1) a b = (knuth n a)^b 1`);
- `BB54_score.g_closed : 2 * g (S k) m + 4 = knuth k 2 (2 * m + 4)` and
  `BB54_score.g_iter_closed : 2 * Nat.iter n (g k) 0 + 4 = knuth k 2 (n + 2)` -- the closed form of the `g`
  hierarchy (Ligocki's theorem);
- `BB54_score.bb54_main`: the run up to the score-carrying configuration and its σ in one statement;
- `BB54_dphase.D_phase_even`, `BB54_dphase.D_phase_odd` -- the D/E phase for an **arbitrary** number of
  twos: an even number lets the machine continue, an odd number halts it (`E3 = 1RZ`);
- `BB54_dphase.bb54_dchain` -- `B(5,0,g_4(0)) [3 1] 0^inf -->* B(2X+1,1,0) [3 1]^3 0^inf` with
  `X = g_5(g_4(0))`, the first D/E phase of the main regime;
- `BB54_dphase.level`, `BB54_dphase.level_gen` -- a level of the main regime: `T` rounds, each of them a B
  rule followed by an A3 sweep;
- `BB54_halt.reaches_d1`, `BB54_halt.level0`, `BB54_halt.level1` -- the two levels of the main regime;
- **`BB54_halt.bb54_halt` -- the machine halts**: it reaches state E on a 3, where `E3 = 1RZ`;
- `BB54_halt.sigma_final` and `BB54_halt.bb54_halt_main` -- the exact number of nonzero cells at halting,
  **σ = 2 M1 + 2 M0 + X + 5** with `M0 = gchain (2X) 3 0` and `M1 = gchain (2M0) (X+2) 0`;
- `BB54_bound.knuth_3_2_4`, `BB54_bound.knuth_4_2_3` -- the shapes of the arrows, `2 ↑^3 4 = 2 ↑↑ 65536` and
  `2 ↑^4 3 = 2 ↑^3 4`;
- **`BB54_bound.X_inner` -- `2 ↑^4 2 ↑^3 4 = 2X + 4`**: the inner argument of the refined runtime bound is the descent
  parameter of the main regime, i.e. the number of twos the first D/E phase has to erase;
- `BB54_bound.target_is_jacobzheng` -- the wiki's entry is Jacobzheng's original bound,
  `target = f_ω² (10 ↑^4 10 ↑↑ 65533)`;
- **`BB54_bound.target_refined_eq` -- `f_ω² (2 ↑^4 2 ↑^3 4) = f_ω² (2X + 4)`**: the refined runtime bound, the one the
  wiki's runtime entry is being corrected to;
- `BB54_tower.tower10_inv` -- the invariant of the tower comparison, `4 · (10 ↑↑ n) + 4 ≤ 2 ↑↑ (n+3)`;
- **`BB54_tower.tower10_lt` and `BB54_tower.tower10_lt_tower3` -- `10 ↑↑ 65533 < 2 ↑↑ 65536 = 2 ↑^3 4`**: the inner
  tower of Jacobzheng's original bound is *below* the inner tower of the refined bound.

The machine is the BB(5,4) champion up to the renaming of the states A↔B and of the symbols 2↔3;
`../tools/explore.py` checks that exhaustively.

## Files

| file | content |
|---|---|
| `BB54.v`, `Individual54.v` | busycoq instantiated for 5 states and 4 symbols, with notations `0`, `1`, `2`, `3` for the symbols |
| `BB54_rules.v` | the transition table `tm`, the elementary sweeps, Lemma 1 (`L1`), Corollary 2 (`Cor2`), the turnaround, the configuration family `Bcfg`, the function `g`, the main rule `B_rule` (the double induction), the D/E phase (`D_phase_raw`, `D_phase_halt`, `D_phase_halt_1`) and the macro steps (`macro_descent`, `B1_iter`, `a3_step`, `chain_step`, `chain`) |
| `BB54_start.v` | **generated** by `../tools/gen_start.py`: the 9-step run from the blank tape, cut into chunks of 5 steps; `start_raw : c0 -->* cfg_9` |
| `BB54_run.v` | the sealed `g40`, `B_rule_gen`, the start lemma `start`, the D/E phase `D_phase_run`, the descents `descent_1` and `descent_4`, `c_score`, `reaches_score`, `sigma`, `score_cells` and the counting lemmas |
| `BB54_score.v` | Knuth arrows `knuth`, the closed form of the `g` hierarchy (`g_closed`, `g_iter_closed`, `g_iter_closed_gen`), `g40_closed`, `sigma_eq`, `f_omega`, `f_omega2`, `target`, `bb54_main` |
| `BB54_dphase.v` | the D/E phase in general: the patterns `pat13`/`pat31`, the eating of the twos (`eat2`, `eat_reach`, `eat_reach_odd`), `D_phase_even` and `D_phase_odd` (even: the machine continues, odd: it halts), the chain `bb54_dchain`, and the rounds and levels of the main regime (`round_step`, `level`, `level_gen`) |
| `BB54_halt.v` | the halting proof: the parity of the `g`'s, `reaches_d1`, the two levels `level0` and `level1`, the final count of twos (`count_final_gen`, `count_final`), **`bb54_halt`**, and the σ at halting (`sigma_final`, `final_cells`, `final_cells_count`, `bb54_halt_main`) |
| `BB54_bound.v` | the two runtime bounds: the shapes of the arrows (`knuth_3_2_4`, `knuth_4_2_3`), the level-5 closed form of `g` (`g5_closed_gen`), the level-4 closed form of `g_4 0` (`g4_zero_iter`, `g4_zero_closed`), **`X_inner`** (`2 ↑^4 2 ↑^3 4 = 2X + 4`), `target_is_jacobzheng` and **`target_refined_eq`** (`f_ω² (2 ↑^4 2 ↑^3 4) = f_ω² (2X + 4)`) |
| `BB54_tower.v` | the comparison of the two inner towers: the first two levels of the arrows as powers (`knuth_1_pow`, `knuth_2_pow`), the elementary facts about the powers of two (`pow2_pos`, `pow2_ge2`, `pow2_ge4`, `pow2_mul4`, `pow2_add4`, `pow_two_pow`), the positivity of the towers (`knuth2_pos`, `tower2_ge2`, `tower2_ge4`), the invariant **`tower10_inv`** (`4 · (10 ↑↑ n) + 4 ≤ 2 ↑↑ (n+3)`), and **`tower10_lt`** / **`tower10_lt_tower3`** (`10 ↑↑ 65533 < 2 ↑^3 4`) |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build, hashes of the source files |
| `coq_quirks.md` | the pitfalls of this development (chunked `execute`, never evaluating `g 4`, the busycoq tape conventions) |

## Check it

    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

This compiles the 10 files in dependency order (about 40 s) and then runs `probe.v`, writing `probe.log`.
`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout, with `Individual.vo` built.  COQC may name
a specific `coqc`.  `_CoqProject` (for editors) assumes busycoq is checked out at `D:/busycoq`; the build script
does not use it.

`probe.v` re-parses the machine string, checks that it agrees with the Coq table `tm`, and then prints
`Print Assumptions` for every main theorem: the log says that all 79 of them are *closed under the global
context*, i.e. the development uses no axioms at all.
