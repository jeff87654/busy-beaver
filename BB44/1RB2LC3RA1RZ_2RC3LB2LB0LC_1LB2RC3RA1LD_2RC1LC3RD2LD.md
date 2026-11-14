# 44-B: a BB(4,4) machine above F(2 ↑^5 3), F(n) = 2 ↑^(n+1) (n+3)

```
1RB2LC3RA1RZ_2RC3LB2LB0LC_1LB2RC3RA1LD_2RC1LC3RD2LD
```

Argon (a Google Gemini model run by the repository owner) found this machine on 2026-11-09 and analysed it with
macro rules; he wrote no Coq proof for it. The Coq proof was written here (agent claims-prover, 2026-11-13). "44-B" is
Argon's name. It replaces 44-C (`1RB3LB1RZ2RA_…`, kept in this directory) as the BB(4,4) entry.

| | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| A | `1RB` | `2LC` | `3RA` | `1RZ` |
| B | `2RC` | `3LB` | `2LB` | `0LC` |
| C | `1LB` | `2RC` | `3RA` | `1LD` |
| D | `2RC` | `1LC` | `3RD` | `2LD` |

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `bb44B_halts`. The halting transition is A3 = `1RZ`. |
| Exact score | Machine-checked: **σ = 2c + 2d + 9**, the number of nonzero cells of the halting configuration (`c_final_nonzero`; the head reads a 3 and `tm (A, 3) = None`, `c_final_head`, so the halting write of a 1 does not change the count). The closed forms (`sigma_B_closed`) are 2d + 4 = 2 ↑^(2c+2) 3, 2c + 4 = 2^(2b+4), 2b + 4 = 2 ↑↑↑ (2a₆ + 4) and 2a₆ + 4 = 2 ↑^4 (2a₅ + 4). |
| Bound | Machine-checked: F(2 ↑^5 3) < σ with F(n) = 2 ↑^(n+1) (n + 3) (`sigma_B_f_omega`; F is the Knuth-arrow function of the BB(5,4) entries' files, not the fast-growing hierarchy's f_ω). |
| Compared | Machine-checked, against exact scores: above 44-A (`BB44B_beats_A`), above 44-C, the previous entry (`BB44B_beats_C`), and above loader3229's machine, the wiki's BB(4,4) champion (Champions page, read 2026-11-13), σ = 2 ↑^509 3 + 510 (`BB44B_beats_official`). |
| Steps | Not computed. |

## How it works

44-B runs the Ackermann engine of Kropitz's BB(3,4) champion in Ligocki's configurations, here with the roles of the
symbols 2 and 3 exchanged:

    B(k, n, m, r) = 0^inf 2^(2m+1) 3^k  A>  1^n r ,   B(k+1, n, m, r)  -->*  B(k+1, 0, g_k^n(m), r)     (B_rule)

with g_0(m) = m + 1, g_(k+1)(m) = g_k^(2m+2)(0) and 2·g_(k+1)(m) + 4 = 2 ↑^k (2m + 4). The run (`BB44B_run.v`):

    0^inf A> 0^inf  -(77 steps)->  B(2, 1, 0)  2 1 2 1 2 1 2 1 0^inf                         (start_to_B2)
    ladder, k = 1..4:  B(k+1, 1, a_k) -B_rule-> B(k+1, 0, a_(k+1)) -step_up-> B(k+2, 1, a_(k+1))
                       (each step up uses one "2 1" pair; a_1 = 0, a_(k+1) = g_k(a_k)),
                       then B_rule at level 5: B(6, 0, a₆) 0^inf
    phase1 -> B(4, 2a₆+2, 0)  0 3 2 1      -B_rule->  B(4, 0, b)        b = g_3^(2a₆+2)(0)
    phase2 -> B(2, 2b+2, 0)   0 2 1 2 1    -B_rule->  B(2, 0, c)        c = g_1^(2b+2)(0)
    phase3 -> B(2c+3, 1, 0)   3 2 1 2 1    -B_rule->  B(2c+3, 0, d)     d = g_(2c+2)(0)
    A reads the 3: A3 = 1RZ halts.

The last descent runs at arrow level 2c + 2, where 2c + 4 = 2^(2b+4) and 2b + 4 = 2 ↑↑↑ (2a₆ + 4), so
σ ≈ 2 ↑^(2c+2) 3.

## Also proved: 44-A

```
1LB2LC3RA0RB_2RC1RZ2LB3LB_1LB2RC3RA1LD_2RC1LC3RD2LD
```

Argon's 44-A (same engine, halt B1 = `1RZ`, written over a 1) is also proved in Coq in the same directory:
`bb44A_halts`, σ = 2·M₃ + 2·M₁ + 3 nonzero cells of the halting configuration (`c_final_nonzero`, `c_final_head`),
`sigma_A_closed`: 2·M₃ + 4 = 2 ↑^(2·M₁) (2·M₂ + 5) and 2·M₁ + 4 = 2 ↑^4 6; `BB44A_beats_C` (above 44-C's exact σ) and
`BB44A_beats_official`. It lies between 44-C and 44-B (`BB44B_beats_A`); it is not an entry. Its run: 91 steps to
B(5, 4, 0), a level-4 descent, a lift to level 2·M₁, two descents there, and the halt.

## Proof

[`verify_44b/`](verify_44b/): `BB44A_rules.v`, `BB44A_run.v`, `BB44A_cmp.v`, `BB44B_rules.v`, `BB44B_run.v`,
`BB44B_cmp.v` (written here), on byte-identical copies of the five files of [`verify_44c/`](verify_44c/) (Argon's 44-C
development, logical root `Local`; `share_check.sh`), whose `B_rule`-style closed forms (`g_closed`,
`g_iter_closed_gen`) and Knuth-arrow lemmas they reuse, and whose `BB44_run.sigma` is 44-C's exact score. Every big
number is sealed behind a `sig`, and the comparisons are proved for variables and then instantiated.

## Verification

- [`verify_44b/`](verify_44b/): busycoq `bd2e36f`, Coq 8.20.1. `probe.v` checks the 32 transitions of the two machines
  against their strings (generated from the strings, not from the Coq files), prints the definitions and runs
  `Print Assumptions` on 18 theorems: all closed under the global context. CI job `bb44`.
- Literal runs (claims-prover, outside this repository): the literal machine passes through the configurations of the
  proof up to step 85,989 for 44-B (62 of 62 checked) and up to step 91 for 44-A (26 of 26).

## Credit

Machines and macro analysis: **Argon** (Google Gemini, run by the repository owner in Google's Antigravity),
2026-11-09, on the engine of Pavel Kropitz's BB(3,4) champion as analysed by Shawn Ligocki. Coq proofs of 44-B and
44-A: this project (agent claims-prover), 2026-11-13. Not yet reviewed by the bbchallenge community.
