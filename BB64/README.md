# BB(6, 4)

## Current entry: a four-level f_(ω+1) machine (derived from 54-L)

```
1RB3LC1LD2RA_2RC1RF2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE_0LC0LB0LD1RZ
```

Found by loader3229 on 2026-11-17.
Halts from the blank tape (F3 = `1RZ`). Machine-checked, axiom-free, for σ the number of nonzero cells after the
halting write:

    f_(ω+1)^4(65536) < σ

that is,

    f_(ω+1)( f_(ω+1)( f_(ω+1)( f_(ω+1)( 65536 ) ) ) )  <  σ   (FGH_BB64.bb64_fgh_four)

where f_(ω+1) is the fast-growing hierarchy function at ω+1 (`FGH (osucc omega)`).  Equivalently, in the Knuth-arrow
majorant of the files,

    F^4(65536) < σ    (BB64_bound.sigma_beats_four_f_omega1)

with **F(n) = 2 ↑^(n+1) (n + 3)** = `f_omega` (a Knuth-arrow function that dominates the FGH f_ω; hence its fourth
iterate dominates f_(ω+1)^4).  The exact σ is `2·m4 + k4 + 5`, where `(k4, m4)` is obtained by iterating
`step_pair` four times with reservoir lengths drawn from the run (not evaluated).

This machine is the BB(5,4) champion 54-L

    1RB3LC1LD2RA_2RC1RZ2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE

with the halting transition `B1 = 1RZ` changed to `B1 = 1RF` and one extra state F (`F0=0LC, F1=0LB, F2=0LD,
F3=1RZ`).  All of 54-L's macro rules apply verbatim up to its halting configuration; the new state F then drives
four further sweep + `D_chain` rounds, each rewriting a right-hand marker

    011 → 031 → 001 → 0131 → halt,

and each lifting the Knuth-arrow level.  Four rounds suffice to pass `f_(ω+1)^4(65536)`.

- [`1RB3LC1LD2RA_2RC1RF2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE_0LC0LB0LD1RZ.md`](1RB3LC1LD2RA_2RC1RF2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE_0LC0LB0LD1RZ.md): the write-up.
- [`verify/`](verify/): the Coq proofs (busycoq, Coq 8.20.1): `bb64_halts`, `reaches_c_final`, `c_final_halted`,
  `final_cells_count`, `final_cells_all_nonblank`, `bb64_score_main`, `sigma_beats_four_f_omega1`, and the exact FGH
  bound `bb64_fgh_four`.  Built and probed: `probe.v` reports all 8 checked theorems *closed under the global context*.

## What is proved

| theorem | file | statement |
| --- | --- | --- |
| `B_rule` | `BB64_rules.v` | `Bcfg (S k) n m r -->* Bcfg (S k) 0 (Nat.iter n (g k) m) r` — Ligocki's Theorem 3 |
| `B_sweep` | `BB64_rules.v` | the 54-L last sweep: `Bcfg 5 0 m 0^inf -->* Bcfg 1 0 1 (2^(2m+5) 0 1 1 0^inf)` |
| `D_step`, `D_chain` | `BB64_rules.v` | one 2-driven level lift and its iteration |
| `marker_011_031`, `marker_031_001`, `marker_001_0131` | `BB64_rules.v` | the three state-F marker rewrites |
| `final_halt` | `BB64_rules.v` | the halting marker `0 1 3 1` reaches `F> 3` (`F3 = None`) |
| `start_to_B5` | `BB64_rules.v` | the blank tape reaches `B(5,1,0) 0^inf` |
| `reaches_c_final` | `BB64_run.v` | `c0 -->* c_final` — the four-round run to the halting configuration |
| **`bb64_halts`** | **`BB64_run.v`** | **`halts tm c0`** — the machine halts from the blank tape |
| `final_cells_count` | `BB64_score.v` | `length final_cells = sigma` — the exact score count |
| `bb64_score_main` | `BB64_score.v` | halting and the score in one statement |
| `g_closed`, `g_iter_closed` | `BB64_bound.v` | Ligocki's closed form `2·g_(k+1)(m) + 4 = 2 ↑^k (2m+4)` |
| `step_pair_closed` | `BB64_bound.v` | `2·snd(step_pair(k,m)) + 4 = 2 ↑^(2m) (k+4)` |
| `dchain_lower` | `BB64_bound.v` | a `D_chain` of length `c` lifts the parameter by `f_ω^(c/2)` |
| **`sigma_beats_four_f_omega1`** | **`BB64_bound.v`** | **`f_omega1^4(2^16) < sigma`** — the Knuth-arrow four-level bound |
| **`bb64_fgh_four`** | **`FGH_BB64.v`** | **`Nat.iter 4 (FGH (osucc omega)) (2^16) < sigma`** — the exact requested FGH bound |

`knuth n a b` is Knuth's `a ↑^n b` with `a ↑^0 b = a·b` and `a ↑^(n+1) b = (a ↑^n b)^b 1`.

**No large number is ever evaluated.** `g 4`, `2 ↑^3 4` and the sealed constants `M1`, `P1`…`P4`, `Aseq` are kept
symbolic (`Opaque` / `sig`), so no tactic tries to normalise an astronomical `Nat.iter`.

## Build

    cd verify
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

Needs Coq 8.20.1 and a busycoq checkout (the `verify/` directory of it).  The bundled fast-growing-hierarchy library
is in `fgh/`.  See [verify/README.md](verify/README.md) for details.

## Layout

    README.md                                    this file
    1RB3LC1LD2RA_...1RZ.md                       the mathematical write-up
    verify/                                      the Coq development
    fgh/                                         bundled FGH library (Ord.v, KnuthFGH.v), logical root BB8
    tools/                                       Python simulators / macro-rule checks

## Status

**The machine halts, and σ exceeds four iterates of f_(ω+1).** `BB64.v`, `Individual64.v`, `BB64_rules.v`,
`BB64_run.v`, `BB64_score.v`, `BB64_bound.v`, `FGH_BB64.v` and `probe.v` all compile from scratch on Coq 8.20.1,
and `probe.v` reports that all 8 theorems it checks are *closed under the global context* — the proof uses no axioms.

This machine is not an independently verified BB(6,4) champion; it is a construction demonstrating a score above
`f_(ω+1)^4(65536)`, obtained by extending the 54-L BB(5,4) champion.
