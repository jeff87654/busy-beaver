# BB(4, 4)

## Current entry: 44-B (Argon's machine, Coq proof here)

```
1RB2LC3RA1RZ_2RC3LB2LB0LC_1LB2RC3RA1LD_2RC1LC3RD2LD
```

Halts from the blank tape (A3 = `1RZ`, written over a 3, so the count of nonzero cells is unchanged). Machine-checked,
axiom-free:

    σ = 2c + 2d + 9,  2d + 4 = 2 ↑^(2c+2) 3,  2c + 4 = 2^(2b+4),  2b + 4 = 2 ↑↑↑ (2a₆ + 4),  2a₆ + 4 = 2 ↑^4 (2a₅ + 4)
                                                       (c_final_nonzero, sigma_B_closed)
    F(2 ↑^5 3) < σ,   F(n) = 2 ↑^(n+1) (n + 3)          (sigma_B_f_omega; the Knuth-arrow function of BB54_score.v)

In the fast-growing hierarchy (standard `Ord.v`, [`../FGH/`](../FGH/README.md), `bb44B_fgh`):
f_ω(f_2(f_4(f_5(f_4(f_3(64)))))) < σ < f_ω(f_2(f_4(f_5(f_4(f_3(256)))))). For 44-A, f_ω(2↑^4 6 − 3) < σ < f_ω(2↑^4 6 − 2)
(`bb44A_fgh`), and for 44-C, f_ω(65532) < σ < f_ω(65533) (`bb44C_fgh`).

σ is the number of nonzero cells of the halting configuration, by a theorem (`c_final_nonzero`, `c_final_head`). In
Coq, against exact scores, 44-B is above 44-A (`BB44B_beats_A`), above 44-C, the previous entry (`BB44B_beats_C`),
and above loader3229's machine, the wiki's BB(4,4) champion (`BB44B_beats_official`). Not yet reviewed by the
bbchallenge community.

**Also proved: 44-A** `1LB2LC3RA0RB_2RC1RZ2LB3LB_1LB2RC3RA1LD_2RC1LC3RD2LD` (Argon's machine, halt B1 = `1RZ`):
`bb44A_halts`, σ = 2·M₃ + 2·M₁ + 3 with 2·M₃ + 4 = 2 ↑^(2·M₁) (2·M₂ + 5) and 2·M₁ + 4 = 2 ↑^4 6 (`sigma_A_closed`),
above 44-C (`BB44A_beats_C`). It lies between 44-C and 44-B and is not an entry; its files are part of 44-B's build.

- [`1RB2LC3RA1RZ_2RC3LB2LB0LC_1LB2RC3RA1LD_2RC1LC3RD2LD.md`](1RB2LC3RA1RZ_2RC3LB2LB0LC_1LB2RC3RA1LD_2RC1LC3RD2LD.md):
  the write-up (table, the run, 44-A, the proof, verification, credit).
- [`verify_44b/`](verify_44b/): the Coq proofs of 44-B and 44-A (busycoq `bd2e36f`, Coq 8.20.1), on byte-identical
  copies of `verify_44c/`'s five files. Built and probed in CI (job `bb44`), which requires 18 closed
  `Print Assumptions` reports.

Machines and macro analysis by **Argon** (a Google Gemini model run by the repository owner), 2026-11-09, without Coq;
Coq proofs of 44-B and 44-A by this project (agent claims-prover), 2026-11-13, on Kropitz's engine.

## Previous entry: 44-C (Argon), 2026-11-13

Superseded by 44-B on the same day (`BB44B_beats_C`, against its exact score). Its files stay: 44-B's proof uses copies
of them.

```
1RB3LB1RZ2RA_1LC3RB1LD2RA_3RB2LC1LC3LC_3RB1LB3LD2RD
```

Halts from the blank tape (A2 = `1RZ`), with, machine-checked and axiom-free,

    σ = 2 ↑^65532 6 + 65532          (sigma_exact_closed_form; 65532 = 2^16 − 4 arrows)

nonzero cells after the halting write. In Coq, the exact score of the previous entry (below), σ = 2 ↑^509 3 + 510,
is smaller: `beats_loader3229_exact` in [`verify_44c/BB44C_vs_loader3229.v`](verify_44c/BB44C_vs_loader3229.v) loads
both developments and joins that entry's `sigma_eq` with 44-C's `sigma_beats_official_bb44`. Not yet reviewed by the
bbchallenge community.

The machine runs the same engine (Kropitz's BB(3,4) core, Ligocki's `B(k,n,m)` and `g` hierarchy) and adds a lift:
the 3-stack of one descent, 2·g_3(0) + 1 = 65533 cells, becomes the arrow level of the next one.

- [`1RB3LB1RZ2RA_1LC3RB1LD2RA_3RB2LC1LC3LC_3RB1LB3LD2RD.md`](1RB3LB1RZ2RA_1LC3RB1LD2RA_3RB2LC1LC3LC_3RB1LB3LD2RD.md):
  the write-up (table, the run, the proof, verification, credit).
- [`verify_44c/`](verify_44c/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `bb44_halts`, `reaches_final`,
  `final_halted`, `final_cells_count`, `final_cells_all_nonblank`, `sigma_exact_closed_form`,
  `sigma_beats_official_bb44`, `bb44_new_champion_main`, and the comparison `knuth_same`, `beats_loader3229_exact`,
  `beats_loader3229_score`, and `sigma_is_score` (σ read off the halting configuration). Built and probed in CI
  (job `bb44`, after `verify/`), which requires 15 closed
  `Print Assumptions` reports.

Found and proved by **Argon** (a Google Gemini model run by the repository owner), 2026-11-09. Re-checked, compared
with the previous entry and packaged here, 2026-11-13.

## Earlier entry: loader3229's machine (2026-11-08 to 2026-11-13)

The BB(4,4) machine **0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA** (loader3229, 2026; the bbchallenge wiki's BB(4,4)
champion, Champions page read 2026-11-13): a full
**axiom-free Coq proof** that it halts from the blank tape with

    σ = (2 ↑^509 3) + 510

nonblank symbols on the tape (509 Knuth up-arrows), and therefore with
**σ > 2 ↑^509 3**.  The write-up of the mathematics is in
[0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA.md](0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA.md);
the Coq development is in [verify/](verify/).

The proof follows the same route as the BB(3,4) development in
[`../BB34`](../BB34): Ligocki's configuration family `B(k,n,m)`, his descent
rule `B_rule`, and the closed form of the `g` hierarchy.  The BB(4,4) champion
differs from the BB(3,4) one only in `A0`, `B0` and the extra state `D`, so the
descent itself ports over unchanged — but the machine only *reaches* the
descent after two BB(4,4)-specific phases, which are proved here as well
(`B_phase` and `D_phase`).

### The main results

| theorem | file | statement |
| --- | --- | --- |
| `bb44_halts` | `BB44_run.v` | `halts tm c0` — the machine halts from the blank tape |
| `reaches_final` | `BB44_run.v` | `c0 -->* c_final`, where `c_final = Bcfg 510 0 g509 (2 1 3 0^inf)` is state A reading the 2 after `3^(2 g509 + 1) 2^510` |
| `final_halted` | `BB44_run.v` | `halted tm c_final` — that configuration is the halting one (`A2 = 1RZ`) |
| `sigma_eq` | `BB44_score.v` | `sigma = knuth 509 2 3 + 510`, i.e. **σ = (2 ↑^509 3) + 510** |
| `bb44_main` | `BB44_score.v` | all of the above in one statement |
| `B_rule` | `BB44_rules.v` | `B(k,n,m) R -->* B(k,0,g_(k-1)^n(m)) R` — Ligocki's Theorem 3, proved by double induction |
| `B_phase` | `BB44_rules.v` | `B(2,0,m) 0^inf -->* B(1,2m+2,0) 0^inf` — the BB(4,4)-specific phase B |
| `D_phase` | `BB44_rules.v` | `B(1,0,m) 0^inf -->* B(2m+2,1,0) 2 1 3 0^inf` — the BB(4,4)-specific phase D |
| `g_closed` | `BB44_score.v` | `2 g_(k+1)(m) + 4 = 2 ↑^k (2m+4)` — the closed form of the `g` hierarchy |
| `g_iter_closed` | `BB44_score.v` | `2 g_k^n(0) + 4 = 2 ↑^k (n+2)` |

`knuth n a b` is Knuth's `a ↑^n b` with `a ↑^0 b = a·b` and `a ↑^(n+1) b = (a ↑^n b)^b 1`.

**No large number is ever evaluated.**  `g 509` unfolds to an exponentially large term
(`g 509 x` iterates `g 508` `2x+2` times, so normalising it also normalises its argument),
and `2 ↑^509 3` is beyond any arithmetic.  Both are kept symbolic: `g509` is sealed behind
a `sig` so that no tactic can evaluate it, and `knuth 509 2 3` is only ever manipulated by
rewriting.  See [verify/coq_quirks.md](verify/coq_quirks.md) for the details.

### The run

    0^inf A> 0^inf  -(98 steps)->  B(2, 6, 0)  0^inf
        ->  B(2, 0, 126)  0^inf                (B_rule, k = 1)
        ->  B(1, 254, 0)  0^inf                (phase B)
        ->  B(1, 0, 254)  0^inf                (B_rule, k = 0)
        ->  B(510, 1, 0)  2 1 3 0^inf          (phase D)
        ->  B(510, 0, g_509(0))  2 1 3 0^inf  (B_rule, k = 509)
        -(A2 = 1RZ)->  0^inf 3^(2 g_509(0)+1) 2^510 1 Z> 1 3 0^inf .

### Build

    cd verify
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

Needs Coq 8.20.1 and a busycoq checkout (commit `bd2e36f`), whose seven needed
`verify/` files must be compiled first.  The whole build takes about 20 s.
See [verify/README.md](verify/README.md) for details.

### Layout

    README.md                                       this file
    0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA.md   the mathematical write-up
    verify/                                         the Coq development
    tools/sim.py                                    a small Python simulator
    tools/check.py                                  cross-check of the start and of the two phases
    tools/gen_start.py                              generator for verify/BB44_start.v

### Status

**Complete.**  `BB44.v`, `Individual44.v`, `BB44_rules.v`, `BB44_start.v`, `BB44_run.v`,
`BB44_score.v` and `probe.v` all compile from scratch on Coq 8.20.1, and `probe.v` reports
that all 32 of the theorems it checks are *closed under the global context* — that is, the
proof uses no axioms at all.
