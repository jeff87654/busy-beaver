# 54-L: a BB(5,4) machine above F^65536(65536), F(n) = 2 ↑^(n+1) (n+3)

```
1RB3LC1LD2RA_2RC1RZ2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE
```

Found by **Argon** (a Google Gemini model run by the repository owner) on 2026-11-09, with the Coq proof; re-checked
and packaged here on 2026-11-13. "54-L" (for its level lifts) is a label used here. It replaces Jacobzheng's machine
`1LD3LB---2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_3RB---3LE3LD_------1LD1RZ` (kept in this directory) as the BB(5,4) entry;
the comparison with it rests on a paper upper bound (below).

| | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| A | `1RB` | `3LC` | `1LD` | `2RA` |
| B | `2RC` | `1RZ` | `2LB` | `2LB` |
| C | `1LD` | `3RC` | `1LE` | `2RA` |
| D | `3RC` | `0LB` | `1LD` | `3LD` |
| E | `3RC` | `1LC` | `3LE` | `2RE` |

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `bb54_halts`. The halting transition is B1 = `1RZ`. |
| Score | σ = 2·M + K + 5 nonzero cells after the halting write, for (K, M) the result of iterating `step_pair` 2·g_4(0) + 5 times from (0, 1) (`final_cells_count`; not evaluated). |
| Bounds | Machine-checked, with **F(n) = 2 ↑^(n+1) (n + 3)** (`f_omega` in the files, the Knuth-arrow function of the previous entry's `BB54_score.v`; not the fast-growing hierarchy's f_ω): F^65536(65536) < σ (`sigma_beats_f_omega1_65536`, `f_omega1 (2 ^ 16) < sigma` with `f_omega1 n = Nat.iter n f_omega n`) and F(F(2 ↑^4 2 ↑^3 4)) < σ (`sigma_beats_official_bb54`). F(n) ≥ f_ω(n) for the FGH, so on paper f_(ω+1)(65536) < σ. |
| Compared with the previous entry | Machine-checked: Jacobzheng's machine has σ = 2·M1 + 2·M0 + X + 5 exactly, at most F(F(2 ↑^4 2 ↑^3 4)) (`sigma_final_upper`, `verify_54l/BB54_J_upper.v`, formerly a hand calculation in [`README.md`](README.md#the-size-of-σ)), which is below 54-L's σ, so `new_beats_jacobzheng`: σ(Jacobzheng) < σ(54-L). |
| Steps | Not computed. |

## How it works

States A, C and E run the Ackermann engine of Kropitz's BB(3,4) champion (its A, B, C), in Ligocki's configurations

    B(k, n, m, r) = 0^inf 3^(2m+1) 2^k  A>  1^n r

with g_0(m) = m + 1, g_(k+1)(m) = g_k^(2m+2)(0), the descent B(k+1, n, m, r) →* B(k+1, 0, g_k^n(m), r) (`B_rule`)
and the closed form 2·g_(k+1)(m) + 4 = 2 ↑^k (2m + 4). States B and D add two macros:

    B(5, 0, m, 0^inf)  -->*  B(1, 0, 1, 2^(2m+5) 0 1 1 0^inf)                       (B_sweep)
    B(k+1, 0, m, 2 r)  -->*  B(2m+1, 0, g_(2m)^(k+2)(0), r)                        (D_step)

`B_sweep` turns the 3-stack into a reservoir of twos on the right; `D_step` eats one two and lifts the arrow level
from k to 2m, the size of the 3-stack. The run:

    0^inf A> 0^inf  -(25 steps)->  B(5, 1, 0)        0^inf           (start_to_B5)
        ->  B(5, 0, M1)                                0^inf           (B_rule, level 4; M1 = g_4(0), 2·M1 + 4 = 2 ↑^3 4)
        ->  B(1, 0, 1)        2^(2·M1+5) 0 1 1 0^inf                   (B_sweep)
        ->  B(K+1, 0, M)                 0 1 1 0^inf                   (D_chain: 2·M1 + 5 = 2 ↑^3 4 + 1 level lifts)
        ->  0^inf 3^(2M+1) 2^(K+1) 1 B> 1 1 0^inf                      (halt_enter; B1 = 1RZ halts)

and the tape after the halting write is 3^(2M+1) 2^(K+1) 1 1 1, so σ = 2M + K + 5. Through the closed form, the lifts
give 2M ≥ F^(M1+2)(2) (`M_final_ge_iter`), with M1 + 2 > 65536 (`M1_plus_2_ge`), which gives the bounds.

## Proof

The Coq files are Argon's ([`verify_54l/`](verify_54l/)): `BB54.v`, `Individual54.v` (busycoq instantiated for 5
states and 4 symbols; `BB54.v` byte-identical to `verify/BB54.v` of the previous entry), `BB54_rules.v` (sweeps,
`turnaround`, `B_rule`, the 25-step start, `B_sweep`, `D_step`, `D_chain`), `BB54_run.v` (`reaches_final`,
`final_halted`, `bb54_halts`, the final tape and its count), `BB54_bound.v` (Knuth arrows, `F`, the two bounds and
`bb54_new_champion_main`, everything in one statement). The theorem named `sigma_beats_official_bb54` proves
F(F(2 ↑^4 2 ↑^3 4)) < σ. `BB54_J_upper.v` (written here) loads the published development of Jacobzheng's machine
(`../verify`, logical root `TM54`) and this one (`Local`), proves `sigma_final_upper` for that machine's exact σ from
its closed forms (every bound for variables, then instantiated with the sealed terms), bridges the two identical
definitions of the Knuth arrows, and concludes `new_beats_jacobzheng`.

Score convention: σ counts the nonzero cells of the explicit tape after the halting write; `final_cells` is that tape
read off `c_final`, and this reading is not itself a Coq lemma (as in the other multi-symbol entries).

## Verification

- [`verify_54l/`](verify_54l/): busycoq `bd2e36f`, Coq 8.20.1. `probe.v` checks the 20 transitions against the
  string above (generated from the string, not from the Coq file), prints the definitions (`knuth`, `f_omega`,
  `f_omega2`, `f_omega1`, `sigma`, `final_cells`, `c_final`, `Bcfg`, `g`) and runs `Print Assumptions` on 11 theorems
  (with `bound_gen`, `sigma_final_upper`, `new_beats_jacobzheng`): all closed under the global context. CI job `bb54`
  builds `verify/` and then `verify_54l/`.
- Literal checks (argon-scout-2, outside this repository): the machine reaches B(5,1,0) at step 25; `B_rule`,
  `B_sweep` and `D_step` were checked against the literal machine on small parameters.

## The wiki

The bbchallenge wiki's Champions page (read 2026-11-13) lists for BB(5,4) a newer machine than Jacobzheng's,
`1RB3LB1RD2RA_2LC3RB1LC2RA_3RB1LB3LC2RC_1LE2LE3LE1RZ_3RC2LE1LE3LE` (Big_numbers, Nov 2026), with the runtime
bound > f_ω^3(2 ↑^15 5), not independently verified. 54-L is not compared with that machine here: no upper bound for
it is known to us.

## Credit

Machine and Coq proof: **Argon** (Google Gemini, run by the repository owner in Google's Antigravity), 2026-11-09, on
the engine of Pavel Kropitz's BB(3,4) champion as analysed by Shawn Ligocki. Probe, re-check and packaging: this
project, 2026-11-13. Not yet reviewed by the bbchallenge community.
