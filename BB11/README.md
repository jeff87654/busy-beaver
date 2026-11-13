# BB11/: 11 states, 2 symbols

## Current entry: C4

    1RB1RH_1RC0LD_1LD1RJ_1LE1LB_1LF1LE_1RG0LE_1RA1RG_0LI1LF_0RC1LI_1RK0RG_1RZ0LB

Halts from the blank tape in state K reading 0 (K0 = `1RZ` writes a 1 on a 0, so σ = N + 1, where N is the number
of ones at the halt). Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+2)(f_(ω+2)(f_5(34))) < N,   σ = N + 1        (sigma_lower_bound)

the exact number of ones at the halt as an explicit recursion (`score_exact`; not evaluated), and, against the exact
score of the previous entry M11b (below): M11b's σ is below f_(ω+1)(f_ω(f_ω(6))) (its `sigma_bracket_m11`), which
is below C4's N (`beats_M11b`); `beats_M11b_score` joins the two statements in one Coq theorem, loading M11b's proof
files.

C4 is M12 ([`../BB12/`](../BB12/)) with state L removed: in M12's state names it is
`1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LJ1RF_1RK0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LI` started in state B (E0, F0 and K1
changed); the string above is the start-A relabelling the proof is about. A round turns the left block into a run
of zeros that is the counter of an f_(ω+1) loop; two stocks give two f_(ω+2) loops, and the halt hinges on two
parities settled by W mod 4. Not yet reviewed by the bbchallenge community.

C4 is also above the exact score of M12, the 12-state entry, in Coq: M12's exact count is at most
f_(ω+2)(4·f_(ω+1)^6(12)) + 3, proved from M12's own definitions (`beats_M12_exact`, `beats_M12_score`). So
BB(12) ≥ BB(11) + 1 beats M12 itself.

- [`1RB1RH_1RC0LD..._1RK0RG_1RZ0LB.md`](1RB1RH_1RC0LD_1LD1RJ_1LE1LB_1LF1LE_1RG0LE_1RA1RG_0LI1LF_0RC1LI_1RK0RG_1RZ0LB.md): the write-up (the table and the M12 naming, the stocks and rounds,
  the run, verification, comparisons, credit).
- [`verify_c4/`](verify_c4/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound`, `sigma_lower_bound_34`, `beats_M11b`, `beats_M12_lower`, `beats_M11b_score`,
  `beats_M12_exact`, `beats_M12_score`. Built and probed in CI (job `bb13-bb14`), which requires nine closed
  `Print Assumptions` reports.

Found and proved by this project (agents of the repository owner, 2026-11-12/13), by an exact macro enumeration of
M12's 10-state core plus one state; M12 is Argon's machine.

## Previous entry: M11b

    1RG0LH_1RK1RC_0LD1LA_0RE1LD_0LI1RF_1RZ0RG_1RB1RG_1LA1LH_0LK0LJ_1LH1LI_1LJ1RE

Halts from the blank tape in state F reading 0 (F0 = `1RZ` writes a 1 on a 0, so σ = N + 1, where N is the number
of ones at the halt). Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+1)(f_ω(f_ω(5))) < N  and  σ = N + 1 < f_(ω+1)(f_ω(f_ω(6)))      (sigma_bracket_m11)

so its level is exactly ω+1, and the exact number of ones at the halt is given by an explicit recursion
(`score_exact`). M11b beats n1, the BB(10) entry, against n1's proved upper bound f_(ω+1)(f_ω(44)) (`M11_beats_n1`).

- [`1RG0LH_1RK1RC..._1LJ1RE.md`](1RG0LH_1RK1RC_0LD1LA_0RE1LD_0LI1RF_1RZ0RG_1RB1RG_1LA1LH_0LK0LJ_1LH1LI_1LJ1RE.md): the write-up.
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound_m11`, `sigma_lower_bound_64`, `sigma_upper_bound_m11`, `sigma_bracket_m11` (built in CI,
  job `bb13-bb14`, 21 s) and `M11_beats_n1`
  (local build, about 6 minutes, on copies of n1's files).

M11b runs the W engine of M12 ([`../BB12/`](../BB12/)) with one outer counter. Found and proved by Argon (a Google
Gemini model run by the repository owner), 2026-10-26; the Coq files were re-checked and repaired here (see the
write-up's credit section).

M11b's three proof files are also loaded by C4's comparison (byte-identical copies in `verify_c4/multifile/`,
checked by its `share_check.sh`).
