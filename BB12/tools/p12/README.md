# Independent check of P12 (before the Coq proof)

Written from scratch for the check of P12 (2026-11-15); they do not use the finder's macro simulator or follower.
Plain Python 3, no packages.

| file | what it does |
|---|---|
| `lit12.py` | literal simulator of `1RB1RA_1RI1RC_0LD1LG_0RE1LD_---1RF_0LL0RA_1RA0LH_1LG1LH_1RK0LJ_1LH1LI_0LL0RD_0LH1LK`; `python lit12.py N` prints the tape (run-length coded) each time the machine enters I moving right, for N steps |
| `rules_check.py` | runs each rule of the write-up (R_A, R_Bo, R_Be, BLANK, BOOT2, R_H) literally on concrete instances (p ≤ 3, small u, m, d, random tails) and finds the opening Ch 4 1 ([1;0]^3 0^∞) from the blank tape; imports `lit12.py` |
| `gates.py` | the gate parities from the 2-adic limits of the W tower: D_0, ..., D_7 mod 2^16 and their parities |

Recorded output (2026-11-15):

    python rules_check.py
    rules: 310 checks, 0 failures
    R_H: 60 checks, 0 failures
    bootstrap Ch 4 1 ([1;0]^3 0^inf) reached at literal step 248

    python gates.py
    T checks ok
    c_E mod 2^16 = 20210  c_E mod 4 = 2
    c_O mod 2^16 = 16791  c_O mod 4 = 3
    A mod 64 = 2  delta mod 64 = 43
    D_0 mod 2^16 = 10114   parity 0
    D_1 mod 2^16 = 59586   parity 0
    D_2 mod 2^16 = 52130   parity 0
    D_3 mod 2^16 = 30066   parity 0
    D_4 mod 2^16 = 4714   parity 0
    D_5 mod 2^16 = 36926   parity 0
    D_6 mod 2^16 = 9228   parity 0
    D_7 mod 2^16 = 37785   parity 1
    HALT in big round 7 (class-3 loop number 8 )
    gate parities (D_1..): [0, 0, 0, 0, 0, 0, 1]

The residues agree with the Coq proof (`BB12_P12.v`: D_0 ≡ 1922 mod 4096, ..., D_7 ≡ 25 mod 32). The Coq proof is
the verification; these scripts are the earlier, independent check.
