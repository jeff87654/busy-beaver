# Coq proofs for champ_231 and champ_232 (BB(7))

    champ_231 = 1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_0LD0RB
    champ_232 = 1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_1LC0RB

A Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`, Coq 8.20.1), with
logical root `BB7`. No axioms: `probe231.v` and `probe232.v` report "Closed under the global context" for every
theorem. The write-up is [`../1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_0LD0RB.md`](../1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_0LD0RB.md).

**To check the claims, read [`Defs.v`](Defs.v) and [`Statement.v`](Statement.v)** (with busycoq's `TM.v`). `Defs.v`
holds everything the statements mention: the two tables `tm231`, `tm232`, the ones count `ones`, and the numbers
`iter`, `U`, `W` (through the pair fixpoint `UW`) and `arrow` (Knuth's up-arrows). `Statement.v` proves, for
champ_231 (and the same `c232_*` for champ_232):

| theorem | statement |
|---|---|
| `c231_table` | `String.length c231_string = 48 /\ forall q s, tm231 (q, s) = parse_slot c231_string (st_idx q) (sym_idx s)`: the table is the machine string, parsed inside Coq |
| `c231_halts` | `halts tm231 c0` |
| `c231_halting_config` | `exists c, c0 -[ tm231 ]->* c /\ halted tm231 c /\ ones c (2 * W 20 5 + 7)` |
| `c231_score` | `forall c N, c0 -[ tm231 ]->* c -> halted tm231 c -> ones c N -> N = 2 * W 20 5 + 7` |
| `c231_lower` | `forall c N, c0 -[ tm231 ]->* c -> halted tm231 c -> ones c N -> arrow 20 3 3 < N` |
| `c231_beats_bb7_champion` | `forall c N, ... -> 3 * arrow 13 2 3 + 22 < N /\ arrow 11 2 (arrow 11 2 3) < N` |

Both machines halt on C1 (undefined) with the head on a 1, so σ = N.

## Files

| file | content |
|---|---|
| `BB72.v`, `Individual72.v` | busycoq instantiated for 7 states and 2 symbols (as busycoq's `BB52.v`), with notations `0`, `1` |
| `Defs.v` | the definitions the statements use (above) |
| `Uniq.v` | the halting configuration reached from a configuration is unique, and so is its ones count (`halted_unique`, `ones_unique`, `score_of`) |
| `Clr.v` | facts about U and W: `U_ge : x + 1 <= U j x`, `W_ge : B + j <= W j B` |
| `Bound.v` | Knuth arrows: monotonicity, growth, base 2 against base 3; `U_lower : arrow i 3 (y + 3 - i) <= U i y`; the nested chain `Lc`; the comparisons with the champion's numbers (`N_lower`) |
| `Bound3.v` | `W_arrow3 : arrow (S (S j)) 3 3 + S (S j) <= W (S (S j)) 5`, hence `N_lower3 : arrow 20 3 3 < N` |
| `C231_rules1.v` | the crossings of runs of 1s and the mini-cycle `MC` |
| `C231_rules2.v` | the configuration `Kc`, `R1ITER`, and the passes `START`, `FW`, `FWS`, `TURN`, `BW`, `BWS`, `FINB` |
| `C231_rules3.v` | `R23`, `R2`, `R3`; the halting phase `TURN4`, `FWZ`, `END2`, `FIN`, `R4x` (to the halted configuration `cfin`) |
| `C231_init.v` | `init_reach : c0 -->* Kc (repeat 1 20) 1 2` (3715 steps, executed) |
| `C231_clear.v` | `CH`, `CDP` (clearing a digit at any position, by induction on the position), `clear_ones` |
| `C231_run.v` | `run_to_end : c0 -->* cfin 20 (W 20 5)`, the ones count `ones_cfin`, `score_exact`, `c231_halts` |
| `C231_main.v` | the existential forms of the main results |
| `C232_*.v` | the same for champ_232: identical proof scripts, the table `tm232`, and 3775 start-up steps |
| `Statement.v` | the statements above, with the string parser |
| `probe231.v`, `probe232.v` | `Print Assumptions` on the six theorems of each machine, and the definitions they use |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe231.log`, `probe232.log`, `sha256.txt` | the logs of one clean build, hashes of the sources |

The configuration of the development is `Kc ds a b = 0^∞ E> 0 1^(2b+1) 00 (11)^a 00 [(11)^d 00 for d in ds] 1 0^∞`
(digits nearest first); the write-up's `K(a; ds)` is `Kc ds a 0`. The counter `b` is three times the write-up's
accumulator after the mini-cycles, so `W 20 5 = 3·a_f` and `2 * W 20 5 + 7 = 6·a_f + 7`.

## Build

    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

compiles the 22 files in dependency order and runs the two probes, writing `probe231.log` and `probe232.log`. `BUSYCOQ`
must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f` with `Individual.vo` and `Flip.vo`
built; `COQC` may name a specific `coqc`. The CI job `bb7` (`.github/workflows/coq.yml`) runs the same build and
requires six closed theorems from each probe.

Recorded build (`compile_clean.log`, `probe231.log`, `probe232.log`): 2026-10-22, one clean from-scratch build in a fresh
directory holding only the sources of this directory, Coq 8.20.1 (Coq Platform 2025.01), Windows 11, a shared laptop,
coqc at Idle priority, busycoq `bd2e36f`. Total 1559 s: `C231_init.v` 394 s and `C232_init.v` 456 s (the start-ups,
executed step by step), every other file 9-56 s. Both probes: 6 of 6 theorems closed under the global context, no
`Axioms:`. `sha256.txt` has the hashes of the sources.
