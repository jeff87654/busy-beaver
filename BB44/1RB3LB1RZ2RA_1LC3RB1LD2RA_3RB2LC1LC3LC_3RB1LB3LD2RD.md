# 44-C: a BB(4,4) machine with σ = 2 ↑^65532 6 + 65532

```
1RB3LB1RZ2RA_1LC3RB1LD2RA_3RB2LC1LC3LC_3RB1LB3LD2RD
```

Found by **Argon** (a Google Gemini model run by the repository owner) on 2026-11-09, with the Coq proof; re-checked
and packaged here on 2026-11-13. Argon's name for it is 44-C. It replaces loader3229's machine
`0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA` (σ = 2 ↑^509 3 + 510, kept in this directory) as the BB(4,4)
entry. It was itself superseded the same day by Argon's 44-B
([`1RB2LC3RA1RZ_...md`](1RB2LC3RA1RZ_2RC3LB2LB0LC_1LB2RC3RA1LD_2RC1LC3RD2LD.md), `BB44B_beats_C`, against 44-C's exact score).

| | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| A | `1RB` | `3LB` | `1RZ` | `2RA` |
| B | `1LC` | `3RB` | `1LD` | `2RA` |
| C | `3RB` | `2LC` | `1LC` | `3LC` |
| D | `3RB` | `1LB` | `3LD` | `2RD` |

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `bb44_halts`. The halting transition is A2 = `1RZ`. |
| Exact score | Machine-checked: **σ = 2 ↑^65532 6 + 65532** (`sigma_exact_closed_form`; 65532 = 2^16 − 4 Knuth arrows), where σ is the number of nonzero cells after the halting transition writes its 1 (the cells of `final_cells`, `final_cells_count`, `final_cells_all_nonblank`). |
| Compared with the previous entry | Machine-checked: loader3229's exact σ = 2 ↑^509 3 + 510 (its `sigma_eq`) is below 44-C's σ (`beats_loader3229_exact`, in one Coq file that loads both developments). loader3229's machine is the bbchallenge wiki's BB(4,4) champion (Champions page, read 2026-11-13; listed there as not independently verified). |
| Steps | Not computed (far beyond any simulation). |

## How it works

44-C runs the Ackermann engine of Kropitz's BB(3,4) champion in the form Ligocki analysed it, as loader3229's
machine does ([`0LB3LB...md`](0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA.md)): configurations

    B(k, n, m, r) = 0^inf 3^(2m+1) 2^k  A>  1^n r

and the hierarchy g_0(m) = m + 1, g_(k+1)(m) = g_k^(2m+2)(0), with Ligocki's descent rule

    B(k+1, n, m, r)  -->*  B(k+1, 0, g_k^n(m), r)          (B_rule)

and closed form 2·g_(k+1)(m) + 4 = 2 ↑^k (2m + 4). What is new is a lift: the stack of 3s produced by one descent
becomes the number of 2s, i.e. the arrow level, of the next one:

    B(4, 0, m, 0^inf)  -->*  B(2m+1, 4, 0, 2 1 0^inf)       (C_lift)

The run from the blank tape:

    0^inf A> 0^inf  -(22 steps)->  B(4, 1, 0)       0^inf          (start44_to_B4)
        ->  B(4, 0, g_3(0))                         0^inf          (B_rule, level 3; g_3(0) = 32766)
        ->  B(65533, 4, 0)                          2 1 0^inf      (C_lift: level 2·32766 = 65532)
        ->  B(65533, 0, M)                          2 1 0^inf      (B_rule, level 65532; M = g_65532^4(0))
        -(A2 = 1RZ)->  halt, tape 3^(2M+1) 2^65533 1 1

so σ = 2M + 1 + 65533 + 2 = 2M + 65536 and, by the closed form, 2M + 4 = 2 ↑^65532 6.

## Proof

The Coq files are Argon's ([`verify_44c/`](verify_44c/)): `BB44.v` and `Individual44.v` (busycoq instantiated
for 4 states and 4 symbols; `BB44.v` is byte-identical to `verify/BB44.v` of loader3229's development), `BB44_rules.v`
(the sweeps, `turnaround`, `B_rule` by double induction, the 22-step start, `C_lift`), `BB44_run.v` (`reaches_final`,
`final_halted`, `bb44_halts`, the final tape and its count), `BB44_bound.v` (Knuth arrows, the closed form,
`sigma_exact_closed_form`, `sigma_beats_official_bb44`: 2 ↑^509 3 + 510 < σ, and `bb44_new_champion_main`, all of it
in one statement). The big numbers are sealed (`g30`, `M44_final` behind a `sig`) so that no tactic evaluates them.

`BB44C_vs_loader3229.v` (written here) loads this development (logical path `Local`) and loader3229's
([`verify/`](verify/), logical path `TM44`), proves that their two definitions of the Knuth arrows agree
(`knuth_same`) and joins loader3229's `sigma_eq` with Argon's `sigma_beats_official_bb44`:

    beats_loader3229_exact : TM44.BB44_run.sigma < Local.BB44_run.sigma
    beats_loader3229_score : length TM44.BB44_run.final_cells < length Local.BB44_run.final_cells

Score convention: σ counts the nonzero cells of the tape after the halting write. `BB44_sigma_cfg.v` (written here)
proves that σ is exactly the number of nonzero cells of the halting configuration `c_final` (`c_final_nonzero`,
`nonzero_cells_unique`, `sigma_is_score`), and that its head is on a 2 with `tm (A, 2) = None` (`c_final_head`), so
the halting write (a 1 over that 2) does not change the count. loader3229's development has the same convention,
read off by inspection.

## Verification

- [`verify_44c/`](verify_44c/): busycoq `bd2e36f`, Coq 8.20.1. `probe.v` checks the 16 transitions against the
  string above (generated from the string, not from the Coq file), prints the definitions and runs `Print Assumptions`
  on 15 theorems (`bb44_halts`, `reaches_final`, `final_halted`, `final_cells_count`, `final_cells_all_nonblank`,
  `sigma_exact_closed_form`, `sigma_beats_official_bb44`, `bb44_new_champion_main`, `knuth_same`,
  `beats_loader3229_exact`, `beats_loader3229_score`, `c_final_nonzero`, `nonzero_cells_unique`, `c_final_head`,
  `sigma_is_score`): all closed under the global context. CI job `bb44` builds
  `verify/` and then `verify_44c/`.
- Literal runs (argon-scout-2, outside this repository): from the blank tape the machine reaches B(4,1,0) at step 22,
  B(4,0,32766) at step 5,726,230,204 and B(65533,4,0) 2 1 0^inf at step 5,726,361,279, the configurations of the proof
  before its last descent; the rules `B_rule`, `C_lift` and the start were also checked on small parameters.

## Credit

Machine and Coq proof: **Argon** (Google Gemini, run by the repository owner in Google's Antigravity), 2026-11-09, on
the engine of Pavel Kropitz's BB(3,4) champion as analysed by Shawn Ligocki. The comparison file
`BB44C_vs_loader3229.v`, the probe, the re-check and the packaging: this project, 2026-11-13. Not yet reviewed by the
bbchallenge community.
