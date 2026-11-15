# BB12/: 12 states, 2 symbols

## Current entry: P12

    1RB1RA_1RI1RC_0LD1LG_0RE1LD_1RZ1RF_0LL0RA_1RA0LH_1LG1LH_1RK0LJ_1LH1LI_0LL0RD_0LH1LK

Halts from the blank tape in state E reading 0 (E0, `---` in the Coq table, written `1RZ` here, writes a 1 on a 0,
so σ = N + 1, where N is the number of ones at the halt). Machine-checked, with the standard fast-growing hierarchy
and no axioms:

    f_(ω+2)^8(f_3(6)) < N,   σ = N + 1                       (sigma_lower_bound)

the exact number of ones at the halt as an explicit recursion (`score_exact`; not evaluated), and, against the exact
score of C4, the BB(11) entry: C4's halting tape holds exactly NC ones (C4's `score_exact`), proved here to be at most
f_(ω+2)^7(8) + 3 from C4's own definitions, and NC + 1 < N (`beats_C4_exact`, `beats_C4_score`). Both machines halt
reading a 0, so σ(P12) > σ(C4) + 1: P12 is above the bound BB(12) ≥ BB(11) + 1 that C4 gave, which was the best
proved bound for BB(12) before (it was already above M12, below).

P12 is M12 (below) with five transitions changed: E0 becomes the halt, F0 = `0LL`, I0 = `1RK`, K = `0LL 0RD`. It
keeps M12's f_ω engine; a round is an f_(ω+1) step, rounds over a stock of pairs form an f_(ω+2) loop, and each loop
ends in a gate on the parity of the stock: an even stock is rebuilt into a new, larger one, an odd stock ends in the
halt. The parities are fixed by the 2-adic residues of the engine's values (W_j(b) mod 2^13 = 3826 or 407): the
first seven stocks are even and the eighth is odd, so the machine halts in its eighth f_(ω+2) loop. Not yet reviewed
by the bbchallenge community.

- [`1RB1RA_1RI1RC..._1RK0LJ_1LH1LI_0LL0RD_0LH1LK.md`](1RB1RA_1RI1RC_0LD1LG_0RE1LD_1RZ1RF_0LL0RA_1RA0LH_1LG1LH_1RK0LJ_1LH1LI_0LL0RD_0LH1LK.md):
  the write-up (the table, the rules, the gates and their parities, the run, verification, comparisons, credit).
- [`verify_p12/`](verify_p12/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound`, `beats_C4_exact`, `beats_C4_score`. Built and probed in CI (job `bb13-bb14`), which requires
  five closed `Print Assumptions` reports. The comparison loads C4's proof (byte-identical copies of
  `../BB11/verify_c4/multifile/` files, checked by its `share_check.sh`).
- [`tools/p12/`](tools/p12/): the independent check made before the Coq proof: a literal simulator (`lit12.py`), a
  check of every rule of the write-up on concrete instances (`rules_check.py`) and the gate parities from its own
  2-adic arithmetic (`gates.py`).

Found and proved by this project (agents of the repository owner, 2026-11-15), by an exhaustive enumeration of
M12's core with E0, F0, I0 and states K, L free (925.4 million nodes); M12 is Argon's machine.

## Previous entry: M12

    1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_0LH1LK

Halts from the blank tape in state K reading 0 (K0 = `1RZ` writes a 1 on a 0, so σ = N + 1, where N is the number
of ones at the halt). Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+2)(f_(ω+1)(f_(ω+1)(3))) < σ                         (sigma_lower_bound_m12)

and the exact number of ones at the halt is given by an explicit recursion (`score_exact`). No upper bound is
proved. M12 is one level of the fast-growing hierarchy above T12a below; that comparison is on paper (T12a has no
proved upper bound).

- [`1RB1RA_1RI1RC..._0LH1LK.md`](1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_0LH1LK.md): the write-up.
- [`verify_m12/`](verify_m12/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `score_exact`,
  `sigma_lower_bound_strong`, `sigma_lower_bound_m12`. Built in CI (job `bb13-bb14`, about a minute).

M12 shares its A–D, G and H rows with M14 and is the base of M13b and M14b ([`../BB13/`](../BB13/),
[`../BB14/`](../BB14/)), of C4 ([`../BB11/`](../BB11/)) and of P12 (above). P12's directory uses copies of its two
busycoq files `BB122.v`, `Individual122.v`.

From 2026-11-13, the 11-state C4 ([`../BB11/`](../BB11/), M12 with state L removed) halted with more ones than M12,
in Coq against M12's exact score: M12's exact count is at most f_(ω+2)(4·f_(ω+1)^6(12)) + 3, proved from M12's
maps, and C4's is above f_(ω+2)(f_(ω+2)(f_5(34))) (`beats_M12_exact`, `beats_M12_score` in
[`../BB11/verify_c4/`](../BB11/verify_c4/), which loads copies of M12's proof files). So BB(12) ≥ BB(11) + 1 was the
better proved bound for BB(12) until P12; M12 stayed listed as the 12-state machine. Found and proved by Argon (a
Google Gemini model run by the repository owner), 2026-10-26; the Coq files were re-checked here.

## Earlier entry: T12a

    1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RK0LC_0RL---_0RF1RZ

Halts from the blank tape in state L reading 1 (L1 = `1RZ` writes 1 on a 1, so σ = N, the number of ones at the
halt). Machine-checked, with the standard fast-growing hierarchy and no axioms:

    f_(ω+1)(f_(ω+1)(JJ − 2)) ≤ 6σ + 11,      JJ = (3T − 13)/7,      T = 2↑^37 3        (fgh_lower2)

and σ is larger than the exact score of n1 (`beats_n1`, against n1's Coq-proved exact score). No upper bound and no
exact score are proved. One transition (K1) is never read.

- [`1RB0RA_..._0RL---_0RF1RZ.md`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RK0LC_0RL---_0RF1RZ.md):
  the write-up (how it works, the run, the score, comparisons, verification status, credit).
- [`verify/`](verify/): the Coq proofs (busycoq `bd2e36f`, Coq 8.20.1): `halt`, `sigma_lower_bound`,
  `score_ge_exact`, `beats_n1`, `fgh_lower2`. `verify/multifile/compile_clean.sh` rebuilds everything and runs a
  probe that re-checks the table entry by entry. Not built in CI: one 2.6 MB generated file takes about 2.8 h; the
  recorded from-scratch build is `verify/multifile/compile_clean.log`.

T12a is n1 ([`../BB10/`](../BB10/)) with two more states: it runs n1's whole computation, rebuilds a countdown from
n1's final values and runs n1's period loop a second time. Found and proved in this project, 2026-10-09/10.
