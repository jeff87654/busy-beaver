# busy-beaver

[![Coq proofs](https://github.com/jeff87654/busy-beaver/actions/workflows/coq.yml/badge.svg?branch=main)](https://github.com/jeff87654/busy-beaver/actions/workflows/coq.yml)

Busy beaver machines with machine-checked proofs. Every bound in the tables below is a Coq theorem, checked with no
axioms (`Print Assumptions` reports "Closed under the global context"), unless it is marked "on paper". Machines are
named by their standard strings; the short names (M8, n1, ...) are labels used in the write-ups.

The working notes behind these results are in a companion repository,
[busy-beaver-notebook](https://github.com/jeff87654/busy-beaver-notebook). It holds the search plans, investigation
reports, tools, dead ends and lessons, and is written mainly for other people's AI agents. It is an unverified lab
notebook: only what is proved here counts.

## Current entries

<!-- Layout: one short row per entry in the table (it has to fit the page width: no machine strings, no long
     prose), and the full record of the entry in a block under "Entry details". Add or change both. -->

| | machine | proved bound (Coq) | found by | added |
|---|---|---|---|---|
| [**BB(7)**](#bb7) | [champ_231](BB7/1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_0LD0RB.md) | 3↑^20 3 < σ | Argon | 2026&#8209;10&#8209;22 |
| [**BB(8)**](#bb8) | [M8](BB8/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---.md) | f_ω(f_ω(f_ω(12))) < σ < f_ω(f_ω(f_ω(13))) | this project | 2026&#8209;10&#8209;19 |
| [**BB(9)**](#bb9) | [h003](BB9/1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LH0LC_1RG1LD_0RG0RF_0LI---_1RI1RC.md) | f_ω(f_ω(f_ω(f_ω(f_ω(f_ω(f_ω(12))))))) < σ | this project | 2026&#8209;10&#8209;22 |
| [**BB(10)**](#bb10) | [n1](BB10/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RZ0LC.md) | f_(ω+1)((3T − 13)/7 − 2) < N < f_(ω+1)(6T), T = 2↑^37 3 | this project | 2026&#8209;10&#8209;08 |
| [**BB(11)**](#bb11) | [C4](BB11/1RB1RH_1RC0LD_1LD1RJ_1LE1LB_1LF1LE_1RG0LE_1RA1RG_0LI1LF_0RC1LI_1RK0RG_1RZ0LB.md) | f_(ω+2)(f_(ω+2)(f_5(34))) < N | this project | 2026&#8209;11&#8209;13 |
| [**BB(12)**](#bb12) | [M12](BB12/1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_0LH1LK.md) | f_(ω+2)(f_(ω+1)(f_(ω+1)(3))) < σ; BB(11) + 1 is higher | Argon | 2026&#8209;10&#8209;26 |
| [**BB(13)**](#bb13) | [M13_19](BB13/1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LM1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_0LM1LK_0LG1LL.md) | f_(ω+2)^19(f_ω(3)) < N | Argon | 2026&#8209;11&#8209;12 |
| [**BB(14)**](#bb14) | [M14_fw3](BB14/1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_1LN1LK_1RK0LH_1LD0RK.md) | f_(ω+3)(f_ω(3)) < N | Argon | 2026&#8209;11&#8209;12 |
| [**BB(15)**](#bb15) | [J15_fw13](BB15/1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LA0RN_0LA1RO_1RZ1RM.md) | f_(ω+13)(20) < N | Argon | 2026&#8209;11&#8209;08 |
| [**BB(16)**](#bb16) | [J16_w2](BB16/1LG1LA_0LI1RC_0LD1LG_0RE1LD_0RM1RL_1RB1RF_1LH0LA_1RF0RN_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LG0RN_0RP1RO_1RZ1RM_1LB1LI.md) | f_(ω·2)(f_15(2)) < N | Argon | 2026&#8209;11&#8209;08 |
| [**BB(17)**](#bb17) | [J17_champ](BB17/1LG1RH_0LI1RC_0LD1LQ_0RE1LD_0RP1RL_1RB1RF_1LQ1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LQ0RN_0LQ1RO_1RZ1RM_0LQ0RA_1LH0LG.md) | f_(ω·2)(f_ω^3(f_14(2))) < N | Argon | 2026&#8209;11&#8209;13 |
| [**BB(18)**](#bb18) | [R18c](BB18/1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_1LQ0LO_0LR1LP_1LQ1LN_1LF0LM_0RC1RZ.md) | f_(ω·2)(f_(ω+1)(f_4(2))) < σ | this project (Coq: Argon) | 2026&#8209;11&#8209;13 |
| [**BB(19)**](#bb19) | [J19_sq](BB19/1LB0LM_1RC1RN_1RD1RC_0LE1RQ_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RJ1RH_0RS0RK_1LN1RL_1LM1RJ_1LA1LM_0LA0RO_0LC1RP_0LA1RN_0LR1LA_0RI1LR_1RZ1LL.md) | f_(ω·2)(f_(ω·2)(f_5(2))) < N | Argon | 2026&#8209;11&#8209;13 |
| [**BB(20)**](#bb20) | [J20_cube](BB20/1LB0LM_1RC1RN_1RD1RC_0LE1RQ_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RJ1RH_0RT0RK_1LS1RL_1LM1RJ_1LA1LM_0LA0RO_0LC1RP_0LA1RN_0LR1LA_0RI1LR_0LA0LA_1RZ1LK.md) | f_(ω·2)^3(f_5(2)) < N | Argon | 2026&#8209;11&#8209;13 |
| [**BB(21)**](#bb21) | [B21](BB21/0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LR.md) | f_(ω²)(f_(ω²)(f_(ω²)(4↑↑341))) < N | Racheline | 2026&#8209;11&#8209;08 |
| [**BB(25)**](#bb25) | [W2PR](BB25/0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LV_0LH0LW_1LH0LX_1LH1LY_0LE1LR.md) | f_(ω²)^5(4↑↑341) < N | this project | 2026&#8209;11&#8209;08 |
| [**BB(29)**](#bb29) | [hydra29](BB29/hydra29.md) | f_(ω^ω)(3) < N | mxdys | 2026&#8209;10&#8209;27 |
| [**BB(30)**](#bb30) | [hydra30](BB30/hydra30.md) | f_(ω^ω)(9) < N | Argon | 2026&#8209;11&#8209;13 |
| [**BB(31)**](#bb31) | [hydra31](BB31/hydra31.md) | f_(ω^ω^ω^ω)(3) < N | mxdys | 2026&#8209;10&#8209;27 |
| [**BB(32)**](#bb32) | [hydra32](BB32/hydra32.md) | f_(ω↑↑4)(8) < N | Argon | 2026&#8209;11&#8209;13 |
| [**BB(33)**](#bb33) | [hydra33](BB33/hydra33.md) | f_(ω↑↑6)(3) < N | mxdys | 2026&#8209;10&#8209;27 |
| [**BB(34)**](#bb342) | [hydra34](BB34_2/hydra34.md) | f_(ω↑↑6)(4) < N | Argon | 2026&#8209;11&#8209;13 |
| [**BB(4,3)**](#bb43) | [write-up](BB43/1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD.md) | σ = 4·e₄ + 18, 2↑↑↑2↑↑↑2↑↑↑(2^96 − 1) < e₄ | Kropitz | 2026&#8209;10&#8209;17 |
| [**BB(5,3)**](#bb53) | [53-Main](BB53/1RB1LC1RA_1LA2LC1RB_1LB1LD2LC_2RE2LD1RA_1RZ2RE1RB.md) | f_ω(f_ω(7)) < σ | Argon | 2026&#8209;11&#8209;13 |
| [**BB(3,4)**](#bb34) | [write-up](BB34/1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC.md) | σ = 2↑^15 5 + 14 | Kropitz | 2026&#8209;11&#8209;08 |
| [**BB(4,4)**](#bb44) | [44-B](BB44/1RB2LC3RA1RZ_2RC3LB2LB0LC_1LB2RC3RA1LD_2RC1LC3RD2LD.md) | F(2↑^5 3) < σ, F(n) = 2↑^(n+1)(n+3) | Argon | 2026&#8209;11&#8209;13 |
| [**BB(5,4)**](#bb54) | [54-L](BB54/1RB3LC1LD2RA_2RC1RZ2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE.md) | F^65536(65536) < σ, F(n) = 2↑^(n+1)(n+3) | Argon | 2026&#8209;11&#8209;13 |

Each row label links to the entry's record under [Entry details](#entry-details): the machine string, the full
statement, the theorem names, how it is checked and the credit. The machine name links to its write-up. σ and N
are defined in the [notes](#notes); "BB(n) + 1 is higher" marks a row whose best proved bound comes from the row
above it.

### Entry details

#### BB(7)

**champ_231** · [write-up](BB7/1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_0LD0RB.md) · its twin champ_232 = `…_1LC0RB` has the same score

```
1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_0LD0RB
```

- **Proved (Coq):** 3↑^20 3 < σ, with σ = 2·W₂₀(5) + 7 exactly; above the champion's 3·(2↑^13 3) + 22 (not yet reviewed by the bbchallenge community)
- **Main theorems:** `c231_halts`, `c231_score`, `c231_lower`, `c231_beats_bb7_champion` (and `c232_*`)
- **Checked:** CI `bb7`
- **Found by:** Argon (a Google Gemini model run by the repository owner) in this project's scan of the bbchallenge BB(7) holdout list; Coq proof here
- **Added:** 2026-10-22 (#34)

#### BB(8)

**M8** · [write-up](BB8/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---.md)

```
1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---
```

- **Proved (Coq):** f_ω(f_ω(f_ω(12))) < σ < f_ω(f_ω(f_ω(13)))
- **Main theorems:** `m8_halts`, `m8_fgh3`, `m8_bracket`, `m8_score_exact`
- **Checked:** CI `bb8-m8`
- **Found by:** this project (reduced from C04)
- **Added:** 2026-10-19 (#27)

#### BB(9)

**h003** · [write-up](BB9/1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LH0LC_1RG1LD_0RG0RF_0LI---_1RI1RC.md)

```
1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LH0LC_1RG1LD_0RG0RF_0LI---_1RI1RC
```

- **Proved (Coq):** f_ω(f_ω(f_ω(f_ω(f_ω(f_ω(f_ω(12))))))) < σ, and f_ω⁶(6·(2↑^13 3) + 2) < σ
- **Main theorems:** `h003_halts`, `h003_lower7_12`, `h003_lower`, `h003_beats_m8_bound`
- **Checked:** CI `bb9-h003`
- **Found by:** this project
- **Added:** 2026-10-22 (#36)

#### BB(10)

**n1** · [write-up](BB10/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RZ0LC.md)

```
1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RZ0LC
```

- **Proved (Coq):** f_(ω+1)((3T − 13)/7 − 2) < N < f_(ω+1)(6T), σ = N + 1, T = 2↑^37 3
- **Main theorems:** `halt`, `score_exact`, `fgh_level`, `beats_champion`, `beats_graham`
- **Checked:** local build (about 20 min)
- **Found by:** this project
- **Added:** 2026-10-08 (#3)

#### BB(11)

**C4** · [write-up](BB11/1RB1RH_1RC0LD_1LD1RJ_1LE1LB_1LF1LE_1RG0LE_1RA1RG_0LI1LF_0RC1LI_1RK0RG_1RZ0LB.md) · M12 without state L; the previous entry M11b is kept in [`BB11/`](BB11/README.md)

```
1RB1RH_1RC0LD_1LD1RJ_1LE1LB_1LF1LE_1RG0LE_1RA1RG_0LI1LF_0RC1LI_1RK0RG_1RZ0LB
```

- **Proved (Coq):** f_(ω+2)(f_(ω+2)(f_5(34))) < N, σ = N + 1, with N = u + 3 + p exactly for (p, u) = `nFIN`; in Coq, above M11b's exact score (M11b's σ < f_(ω+1)(f_ω(f_ω(6))), its proved upper bound), and above M12's exact score (BB(12); M12's exact count is proved at most f_(ω+2)(4·f_(ω+1)^6(12)) + 3), so BB(12) ≥ BB(11) + 1 is the best proved bound for BB(12) too (not yet reviewed by the bbchallenge community)
- **Main theorems:** `halt`, `score_exact`, `sigma_lower_bound`, `beats_M11b`, `beats_M11b_score`, `beats_M12_exact`, `beats_M12_score`
- **Checked:** CI `bb13-bb14`
- **Found by:** this project (exact macro enumeration of M12's core plus one state; built on Argon's M12); Coq proof here
- **Added:** 2026-11-13

#### BB(12)

**M12** · [write-up](BB12/1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_0LH1LK.md)

```
1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_0LH1LK
```

- **Proved (Coq):** f_(ω+2)(f_(ω+1)(f_(ω+1)(3))) < σ, σ = N + 1; C4 (BB(11)) is above M12's exact score in Coq (`beats_M12_exact`, `beats_M12_score`), so BB(12) ≥ BB(11) + 1 is the better proved bound for BB(12)
- **Main theorems:** `halt`, `score_exact`, `sigma_lower_bound_m12`
- **Checked:** CI `bb13-bb14`
- **Found by:** Argon
- **Added:** 2026-10-26

#### BB(13)

**M13_19** · [write-up](BB13/1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LM1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_0LM1LK_0LG1LL.md) · the previous entries M13b and M13 are kept in [`BB13/`](BB13/README.md)

```
1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LM1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_0LM1LK_0LG1LL
```

- **Proved (Coq):** f_(ω+2)^19(f_ω(3)) < N, σ = N + 1; in Coq, above the exact score of M13b, the previous entry (its N = p + a + 5 for (p, a) = `pa7`, proved below f_(ω+2)^14(f_ω(3)) from M13b's own definitions) (not yet reviewed by the bbchallenge community)
- **Main theorems:** `halt`, `sigma_bound`, `sigma_bound_fw1`, `beats_M13b`, `beats_M13b_exact`, `beats_M13b_score` (and `_tnf` versions for the relabelled table)
- **Checked:** CI `bb13-bb14`
- **Found by:** Argon (machine and Coq proof); exact-score comparison, probe and packaging here
- **Added:** 2026-11-12

#### BB(14)

**M14_fw3** · [write-up](BB14/1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_1LN1LK_1RK0LH_1LD0RK.md) · the previous entries M14_31, M14d_18 and M14b are kept in [`BB14/`](BB14/README.md)

```
1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_1LN1LK_1RK0LH_1LD0RK
```

- **Proved (Coq):** f_(ω+3)(f_ω(3)) < N, σ = N + 1, with N = p + a + 6 exactly for (p, a) = `pa_final`; in Coq, above the exact score of M14_31, the previous entry (its σ = N = p + a + 4 for (p, a) = `pa32`, proved below f_(ω+2)^64(f_ω(3)) from M14_31's own definitions); far below the proved bounds of the BB(15) and BB(16) entries, so those rows stay (not yet reviewed by the bbchallenge community)
- **Main theorems:** `halt`, `score_exact`, `sigma_bound`, `beats_M14_31`, `beats_M14_31_exact`, `beats_M14_31_score` (and `_tnf` versions for the relabelled table)
- **Checked:** CI `bb13-bb14`
- **Found by:** Argon (machine and Coq proof); exact-score comparison, probe and packaging here
- **Added:** 2026-11-12

#### BB(15)

**J15_fw13** · [write-up](BB15/1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LA0RN_0LA1RO_1RZ1RM.md)

```
1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LA0RN_0LA1RO_1RZ1RM
```

- **Proved (Coq):** f_(ω+13)(20) < N, σ = N + 1, with N = 2j + 1 exactly, hoc_0^14(4) + 29 = 3j for the machine's recursion (halts after two refills, by a mod-3 invariant); in Coq, above M14_31's proved bound (BB(14)); the wiki's Champions table has no BB(15) row (not yet reviewed by the bbchallenge community)
- **Main theorems:** `halt`, `step_1012`, `score_exact`, `sigma_lower_bound`, `beats_M14_31`
- **Checked:** CI `bb13-bb14`
- **Found by:** Argon (machine and Coq proof, a compression of Jacobzheng's J19/J20 architecture); comparison, probe and packaging here
- **Added:** 2026-11-08

#### BB(16)

**J16_w2** · [write-up](BB16/1LG1LA_0LI1RC_0LD1LG_0RE1LD_0RM1RL_1RB1RF_1LH0LA_1RF0RN_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LG0RN_0RP1RO_1RZ1RM_1LB1LI.md) · the previous entries M16_C and M16_B are kept in [`BB16/`](BB16/README.md)

```
1LG1LA_0LI1RC_0LD1LG_0RE1LD_0RM1RL_1RB1RF_1LH0LA_1RF0RN_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LG0RN_0RP1RO_1RZ1RM_1LB1LI
```

- **Proved (Coq):** f_(ω·2)(f_15(2)) < N, σ = N + 1, with N = 2j + 4 exactly for the machine's recursion (halts after two refills, by residues mod 3 and mod 9); in Coq, above the proved bounds of M16_C, of M17_B (the previous BB(17) entry), of J15_fw13 and of M14_31; the wiki's Champions table has no BB(16) row (not yet reviewed by the bbchallenge community)
- **Main theorems:** `halt`, `score_exact`, `sigma_lower_bound`, `beats_M16_C`, `beats_M17_B`, `beats_J15`, `beats_M14_31`
- **Checked:** CI `bb13-bb14`
- **Found by:** Argon (machine and Coq proof, a compression of Jacobzheng's J19/J20 architecture); comparisons, probe and packaging here
- **Added:** 2026-11-08

#### BB(17)

**J17_champ** · [write-up](BB17/1LG1RH_0LI1RC_0LD1LQ_0RE1LD_0RP1RL_1RB1RF_1LQ1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LQ0RN_0LQ1RO_1RZ1RM_0LQ0RA_1LH0LG.md) · J16_w2 with a two-state refill; the previous entry M17_B is kept in [`BB17/`](BB17/README.md)

```
1LG1RH_0LI1RC_0LD1LQ_0RE1LD_0RP1RL_1RB1RF_1LQ1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LQ0RN_0LQ1RO_1RZ1RM_0LQ0RA_1LH0LG
```

- **Proved (Coq):** f_(ω·2)(f_ω^3(f_14(2))) < N and f_(ω·2)(f_15(2)) < N, σ = N + 1, with N = 2j + 4 exactly for the machine's recursion (halts after two refills, by residues mod 3 and mod 9, computed through tables of the inner level maps mod 486); the second bound is J16_w2's proved bound (BB(16)), so the proved bound is above BB(16) + 1's; in Coq, also above J16_w2's exact score: σ = N + 1 > σ(J16_w2) + 1 (`beats_J16_exact`: an upper bound on J16_w2's count from its own definitions) (not yet reviewed by the bbchallenge community)
- **Main theorems:** `halt`, `score_exact`, `sigma_lower_bound`, `beats_J16_exact`, `beats_J16_score` (and `halt_tnf`, `sigma_lower_bound_tnf` for the machine in tree normal form)
- **Checked:** CI `bb13-bb14`
- **Found by:** Argon (machine and Coq proof, on Jacobzheng's J19/J20 architecture, extending J16_w2); probe and packaging here
- **Added:** 2026-11-13

#### BB(18)

**R18c** · [write-up](BB18/1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_1LQ0LO_0LR1LP_1LQ1LN_1LF0LM_0RC1RZ.md) · R18a with six entries changed; the previous entries J18_w2_C, R18a, M18_229round, M18_4round and BB18_fw3 are kept in [`BB18/`](BB18/README.md)

```
1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_1LQ0LO_0LR1LP_1LQ1LN_1LF0LM_0RC1RZ
```

- **Proved (Coq):** f_(ω·2)(f_(ω+1)(f_4(2))) < N = σ and f_(ω·2)(2·f_ω^9(35)) < N, with N = 2(j + 1) + 1 exactly for the machine's recursion (halts after exactly two refills, by a mod-3 invariant; the halt R1 is read on a 1); the second bound is J18_w2_C's proved bound (the previous entry); in Coq, above J18_w2_C's exact score (σ = N > σ(J18_w2_C), `beats_J18C_exact`) and above BB(17) + 1 against J17_champ's exact score (N > σ(J17_champ) + 1, `beats_J17_exact`) (not yet reviewed by the bbchallenge community)
- **Main theorems:** `halt`, `score_exact`, `sigma_lower_bound`, `beats_J18C_exact`, `beats_J18C_score`, `beats_J17_exact`, `beats_J17_score` (and `halt_tnf`, `sigma_lower_bound_tnf` for the machine in tree normal form)
- **Checked:** CI `bb13-bb14`
- **Found by:** this project (2026-11-07, in the search for compressions of Jacobzheng's J20 that produced R18a); Coq proof by Argon (2026-11-09); probe and packaging here
- **Added:** 2026-11-13

#### BB(19)

**J19_sq** · [write-up](BB19/1LB0LM_1RC1RN_1RD1RC_0LE1RQ_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RJ1RH_0RS0RK_1LN1RL_1LM1RJ_1LA1LM_0LA0RO_0LC1RP_0LA1RN_0LR1LA_0RI1LR_1RZ1LL.md) · the previous entry J19 (Jacobzheng) and the earlier M19_fw4_A and M19_fw4 are kept in [`BB19/`](BB19/README.md)

```
1LB0LM_1RC1RN_1RD1RC_0LE1RQ_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RJ1RH_0RS0RK_1LN1RL_1LM1RJ_1LA1LM_0LA0RO_0LC1RP_0LA1RN_0LR1LA_0RI1LR_1RZ1LL
```

- **Proved (Coq):** f_(ω·2)(f_(ω·2)(f_5(2))) < N, σ = N + 1, with N = 2(j + 1) + 1 exactly for the machine's recursion (halts after three refills: a parked sentinel cell tells the second and the third exhaustion apart, residues mod 3 computed exactly); also f_(ω·2)(2·f_ω^9(35)) < N (J18_w2_C's proved bound) and f_(ω·2)(f_(ω+2)(f_(ω+2)(f_10(2)))) < N (J20's proved bound, BB(20)); in Coq, above BB(18) + 1 against R18c's exact score (σ = N + 1 > σ(R18c) + 1, `beats_R18c_exact`) and above J20's exact score (σ > σ(J20), `beats_J20_exact`) (not yet reviewed by the bbchallenge community)
- **Main theorems:** `halt`, `score_exact`, `sigma_lower_bound`, `beats_R18c_exact`, `beats_R18c_score`, `beats_J20_exact`, `beats_J20_score`
- **Checked:** CI `bb13-bb14`
- **Found by:** Argon (machine and Coq proof, on Jacobzheng's J19/J20 architecture with J18_w2_C's expansion); probe and packaging here
- **Added:** 2026-11-13

#### BB(20)

**J20_cube** · [write-up](BB20/1LB0LM_1RC1RN_1RD1RC_0LE1RQ_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RJ1RH_0RT0RK_1LS1RL_1LM1RJ_1LA1LM_0LA0RO_0LC1RP_0LA1RN_0LR1LA_0RI1LR_0LA0LA_1RZ1LK.md) · J19_sq with one more state; the previous entry J20 (Jacobzheng) is kept in [`BB20/`](BB20/README.md)

```
1LB0LM_1RC1RN_1RD1RC_0LE1RQ_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RJ1RH_0RT0RK_1LS1RL_1LM1RJ_1LA1LM_0LA0RO_0LC1RP_0LA1RN_0LR1LA_0RI1LR_0LA0LA_1RZ1LK
```

- **Proved (Coq):** f_(ω·2)^3(f_5(2)) < N and f_(ω·2)(f_(ω+2)(f_(ω+2)(f_10(2)))) < N, σ = N + 1, with N = 2(j + 1) + 1 exactly for the machine's recursion (halts after four refills, with a two-cell sentinel); the second bound is J20's proved bound (the previous entry); in Coq, above BB(19) + 1 against J19_sq's exact score (σ > σ(J19_sq) + 1, `beats_J19sq_exact`), and so above J20's exact score too (J19_sq's `beats_J20_exact`) (not yet reviewed by the bbchallenge community)
- **Main theorems:** `halt`, `score_exact`, `sigma_lower_bound`, `beats_J19sq_exact`, `beats_J19sq_score`
- **Checked:** CI `bb13-bb14`
- **Found by:** Argon (machine and Coq proof, on Jacobzheng's J19/J20 architecture, extending J19_sq); probe and packaging here
- **Added:** 2026-11-13

#### BB(21)

**B21** · [write-up](BB21/0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LR.md) · the first published bound, 4↑↑341 < N, is kept in [`BB21/verify/`](BB21/verify/)

```
0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LR
```

- **Proved (Coq):** f_(ω²)(f_(ω²)(f_(ω²)(4↑↑341))) < N, σ = N + 1, one f_(ω²) above the wiki's claimed f_(ω²)^2(4↑↑341), which is also proved in the wiki's form (`sigma_lower_bound_wsq`), so the wiki's claim is confirmed and the new bound is stronger; halts at the sixth refill, by a residue schedule mod 4 and a dominance invariant; in Coq, above J20's proved bound f_(ω·2)(f_(ω+2)^2(f_10(2))) (the previous BB(20) entry, `beats_J20`); far above J20_cube's proved f_(ω·2)^3(f_5(2)) (BB(20)) on paper, as an f_(ω²)-class bound (not yet reviewed by the bbchallenge community)
- **Main theorems:** `halt`, `sigma_lower_bound_wsq3`, `sigma_lower_bound_wsq`, `beats_J20`, `sigma_lower_bound`
- **Checked:** CI `bb13-bb14`
- **Found by:** Racheline (the bbchallenge wiki's BB(21) champion, listed as not independently verified); analysis and Coq proof here
- **Added:** 2026-11-08 (#53; ω² bound #55)

#### BB(25)

**W2PR** · [write-up](BB25/0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LV_0LH0LW_1LH0LX_1LH1LY_0LE1LR.md) · the first published bound, Fh⁵(4↑↑341) < N with Fh f_ω-class, is kept in [`BB25/verify/`](BB25/verify/)

```
0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LV_0LH0LW_1LH0LX_1LH1LY_0LE1LR
```

- **Proved (Coq):** f_(ω²)^5(4↑↑341) < N, σ = N + 1 (five applications of f_(ω²)); halts at the eighth refill, after five big ω² phases (B21 with its refill tested mod 8 instead of mod 4); in Coq, above B21's proved f_(ω²)^3(4↑↑341) (BB(21), `beats_B21`) (not yet reviewed by the bbchallenge community)
- **Main theorems:** `halt`, `sigma_lower_bound_wsq`, `beats_B21`, `sigma_lower_bound`
- **Checked:** CI `bb13-bb14`
- **Found by:** this project (built on Racheline's B21: U1 changed to `1LV` and a copy V–Y of B21's refill cycle, so the refill tests the accumulator mod 8)
- **Added:** 2026-11-08 (#54; ω² bound #56)

#### BB(29)

**hydra29** · [write-up](BB29/hydra29.md) · hydra machine

```
0LP1LD_---0LC_1LR0LB_1RF1LE_0LD1LD_0R[1RG_1RN0RK_0RI1RJ_1LZ1RH_0RH1RH_0RL1RM_1L\1RK_0RK1RK_0RO1RO_0L\1RN_1R[1LA_0RV0RV_0LT1LS_0R[1LT_0RY1LU_0LR1L\_0RW1RX_0RN1RV_0LC1RV_0LA1LZ_0LY1LY_0RQ0RH_1L]1LR_1LH1LZ
```

- **Proved (Coq):** f_(ω^ω)(3) < N, with N = T₄(S)(1) + 1 exactly; upper bound T₄(S)(1) ≤ f_(ω^3·7)(26) (`BB29_upper.T4_upper`, with `halts_with_exact`: every halting run leaves exactly T₄(S)(1) + 1 ones; in [`BB30/verify_vs29/`](BB30/verify_vs29/))
- **Main theorems:** `halt`, `score_exact`, `sigma_lower_bound`
- **Checked:** CI `bb13-bb14`
- **Found by:** mxdys (AI-generated, posted in the bbchallenge Discord); Coq proof here
- **Added:** 2026-10-27

#### BB(30)

**hydra30** · [write-up](BB30/hydra30.md) · hydra machine: up to renaming, hydra29 with one transition redirected into one new state, and another start state

```
1RC1L[_---0LY_0RD1RW_0RE0RN_0RF0RF_0RG1RX_0RH1RF_0RI1RI_0LJ1RH_1LK1LU_0LL1LP_1LM0RD_0RD1LT_0RO1RV_1LP1RN_0LQ1LQ_0LR1LP_0LS1LA_1RD1LR_0RQ1LZ_0LT1LM_0RN1RN_1RH0R\_0LY1RF_1LU0LB_0LU1LJ_0LA1LA_0R^1R]_0R\1R\_1LJ1R\
```

- **Proved (Coq):** f_(ω^9)(10) ≤ N + 2, so f_(ω^ω)(9) < N (`Z` is an ordinary state here; the only halt is B0 = `---`); in Coq above hydra29's exact score: hydra29's N = T₄(S)(1) + 1 with T₄(S)(1) ≤ f_(ω^3·7)(26) (`BB29_upper.T4_upper`, `halts_with_exact`, proved on the published hydra29 files), and hydra30's N is at least hydra29's + 22 (`BB30_beats_BB29`), so above BB(29) + 1 (not yet reviewed by the bbchallenge community)
- **Main theorems:** `halt`, `hardy_bound`, `hardy_score`, `sigma_lower_bound_w2_9`, `sigma_lower_bound`; comparison: `BB29_upper.T4_upper`, `BB30_beats_BB29` (in [`BB30/verify_vs29/`](BB30/verify_vs29/))
- **Checked:** CI `bb13-bb14`
- **Found by:** Argon (machine and Coq proof, 2026-11-09), from mxdys's hydra machines (the BB(29), BB(31) and BB(33) entries); probe and packaging here; the upper bounds for hydra29, hydra31 and hydra33 and the comparisons by this project (2026-11-13)
- **Added:** 2026-11-13

#### BB(31)

**hydra31** · [write-up](BB31/hydra31.md) · hydra machine

```
0RK1RK_---0LC_1LQ0LB_1RF1LE_0LD1LD_0R\1RG_1RM0RK_0RI1RJ_1L[1RH_0RH1RH_0RL1RA_1L]1RK_0RN1RN_0L]1RM_1R\1L^_0RW0RW_0LU1LR_0R\1LS_0L]1LT_0LQ1LU_0RZ1LV_0LS1L]_0RX1RY_0RM1RW_0LC1RW_0L^1L[_0LZ1LZ_0RP0RH_1L_1LQ_0LO1LD_1LH1L[
```

- **Proved (Coq):** f_(ω^ω^ω^ω)(4) ≤ N + 2, so f_(ω^ω^ω^ω)(3) < N; upper bound N + 2 ≤ f_(ω^ω^ω^4)(6) for every halting configuration (`BB31_upper.upper_bound`, in [`BB32/verify_vs31/`](BB32/verify_vs31/))
- **Main theorems:** `halt`, `hardy_score`, `sigma_lower_bound_w4`
- **Checked:** CI `bb13-bb14`
- **Found by:** mxdys (AI-generated, posted in the bbchallenge Discord); Coq proof here
- **Added:** 2026-10-27

#### BB(32)

**hydra32** · [write-up](BB32/hydra32.md) · hydra machine: up to renaming, hydra31 with one transition redirected into one new state, and another start state

```
1RC1LT_---0LZ_0RD1RU_0RE0RW_0RF0RF_0RG1RS_0RH1RF_0RI1RI_0LJ1RH_1LK1L[_0RL1LO_1RM1RL_0RN1RV_1LJ1RM_0LP1LP_0LQ1LO_0LR1LA_1RD1LQ_0LZ1RF_0LA1LA_1RH0RM_0RM1RM_0RX1RY_1LO1RW_0RW1RW_1L[0LB_0L_1L\_0RD1L]_0LJ1L^_0L[1L__0RP1L`_0L]1LJ
```

- **Proved (Coq):** f_(ω^ω^(ω^8·3))(4) ≤ N + 2, so f_(ω↑↑4)(8) < N (`Z` is an ordinary state here; the only halt is B0 = `---`); in Coq above hydra31's exact score: hydra31's N satisfies N + 2 ≤ f_(ω^ω^ω^4)(6) for every halting configuration (`BB31_upper.upper_bound`, an upper bound proved on the published hydra31 files), and hydra32's N is at least hydra31's + 6 (`BB32_beats_BB31`), so above BB(31) + 1 (not yet reviewed by the bbchallenge community)
- **Main theorems:** `halt`, `hardy_bound`, `hardy_score`, `sigma_lower_bound_w4_8`, `sigma_lower_bound_w4`; comparison: `BB31_upper.upper_bound`, `BB32_beats_BB31` (in [`BB32/verify_vs31/`](BB32/verify_vs31/))
- **Checked:** CI `bb13-bb14`
- **Found by:** Argon (machine and Coq proof, 2026-11-09), from mxdys's hydra machines (the BB(29), BB(31) and BB(33) entries); probe and packaging here; the upper bounds for hydra29, hydra31 and hydra33 and the comparisons by this project (2026-11-13)
- **Added:** 2026-11-13

#### BB(33)

**hydra33** · [write-up](BB33/hydra33.md) · hydra machine

```
1LH1L^_---0LC_1LR0LB_1RF1LE_0LD1LD_0R_1RG_1RN0RK_0RI1RJ_1L^1RH_0RH1RH_0RL1RM_1L`1RK_0RK1RK_0RO1RO_0L`1RN_1R_1La_0RZ0RZ_0LX1LS_0R_1LT_0L`1LU_0LR1LV_0LS1LW_0LT1LX_0R]1LY_0LV1L`_0R[1R\_0RN1RZ_0LC1RZ_0La1L^_0L]1L]_0RQ0RH_1LA1LR_0LP1LD
```

- **Proved (Coq):** f_(ω^ω^ω^ω^ω^3)(4) ≤ N + 2, so f_(ω↑↑6)(3) < N; upper bound N + 2 ≤ f_(ω^ω^ω^ω^ω^3)(6) for every halting configuration (`BB33_upper.upper_bound`, in [`BB34_2/verify_vs33/`](BB34_2/verify_vs33/))
- **Main theorems:** `halt`, `hardy_score`, `sigma_lower_bound_w6`
- **Checked:** CI `bb13-bb14`
- **Found by:** mxdys (AI-generated, posted in the bbchallenge Discord); Coq proof here
- **Added:** 2026-10-27

#### BB(34,2)

BB(34) with 2 symbols; its directory is [`BB34_2/`](BB34_2/README.md), since `BB34/` is BB(3,4) (below)

**hydra34** · [write-up](BB34_2/hydra34.md) · hydra machine: up to renaming, hydra33 with one transition redirected into one new state, and another start state

```
1LC1LT_---0LS_1RD1LH_0RE0RC_0RF1RF_0RG1RE_1LA1RF_0LI1LI_0LJ1LH_0LK1LY_1RL1LJ_0RM0RV_0RN0RN_0RO1RR_0RP1RN_0RQ1RQ_0LA1RP_0LS1RN_1LT0LB_0La1LU_0RL1L\_0RX1RW_0RV1RV_1LH1RV_1RZ1L^_0RL1R[_1RP0RF_0LA1L]_0LT1L__0LY1LY_0LU1L`_0L\1La_0RI1Lb_0L_1LA
```

- **Proved (Coq):** f_(ω^ω^ω^ω^ω^4)(5) ≤ N + 2, so f_(ω↑↑6)(4) < N (`Z` is an ordinary state here; the only halt is B0 = `---`); in Coq above hydra33's exact score: hydra33's N satisfies N + 2 ≤ f_(ω^ω^ω^ω^ω^3)(6) for every halting configuration (`BB33_upper.upper_bound`, an upper bound proved on the published hydra33 files), and hydra34's N is at least hydra33's + 3 (`BB34_beats_BB33`), so above BB(33) + 1 (not yet reviewed by the bbchallenge community)
- **Main theorems:** `halt`, `hardy_bound`, `hardy_score`, `sigma_lower_bound_w6_4`, `sigma_lower_bound_w6`; comparison: `BB33_upper.upper_bound`, `BB34_beats_BB33` (in [`BB34_2/verify_vs33/`](BB34_2/verify_vs33/))
- **Checked:** CI `bb13-bb14`
- **Found by:** Argon (machine and Coq proof, 2026-11-09), from mxdys's hydra machines (the BB(29), BB(31) and BB(33) entries); probe and packaging here; the upper bounds for hydra29, hydra31 and hydra33 and the comparisons by this project (2026-11-13)
- **Added:** 2026-11-13

#### BB(4,3)

[write-up](BB43/1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD.md)

```
1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD
```

- **Proved (Coq):** σ = 4·e₄ + 18 exactly, 2↑↑↑2↑↑↑2↑↑↑(2^96 − 1) < e₄ ≤ 2↑↑↑2↑↑↑2↑↑↑(2^96 + 6)
- **Main theorems:** `bb43_halts`, `bb43_main`, `e4_bounds`, `wiki_bracket`
- **Checked:** CI `bb43`
- **Found by:** Kropitz (machine), Polygon (analysis); Coq proof here
- **Added:** 2026-10-17 (#22, #23)

#### BB(5,3)

**53-Main** · [write-up](BB53/1RB1LC1RA_1LA2LC1RB_1LB1LD2LC_2RE2LD1RA_1RZ2RE1RB.md)

```
1RB1LC1RA_1LA2LC1RB_1LB1LD2LC_2RE2LD1RA_1RZ2RE1RB
```

- **Proved (Coq):** f_ω(f_ω(7)) < σ and f_ω(2↑^8 3) < σ in the standard fast-growing hierarchy (`sigma_exceeds_FGH`, with `Ord.v`'s FGH), from Argon's F(F(7)) < σ and F(2↑^8 3) < σ, F(n) = 2↑^n n (that is, 2↑^x x < σ with x = 2↑^7 7), and f_ω(n) ≤ F(n) for n ≥ 4 (`FGH_omega_le_home`); in Coq above the exact σ of the BB(4,3) entry + 1 (`BB53_beats_BB43`, against that entry's Coq upper bound σ ≤ 4·2↑↑↑2↑↑↑2↑↑↑(2^96 + 6) + 18); the wiki's Champions page (read 2026-11-13) has no BB(5,3) champion (not yet reviewed by the bbchallenge community)
- **Main theorems:** `bb53_halts`, `sigma_exceeds_f_omega2`, `bb53_new_champion_main`; `sigma_exceeds_FGH`, `FGH_omega_le_home`, `BB53_beats_BB43` (in [`BB53/verify_cmp/`](BB53/verify_cmp/))
- **Checked:** CI `bb53`
- **Found by:** Argon (machine and Coq proof, 2026-11-09), a 3-symbol version of Kropitz's BB(3,4) engine; probe and packaging here; the FGH restatement and the comparison with BB(4,3) by this project (2026-11-13)
- **Added:** 2026-11-13

#### BB(3,4)

[write-up](BB34/1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC.md)

```
1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC
```

- **Proved (Coq):** σ = 2↑^15 5 + 14 exactly (the wiki's champion, listed as > 2↑^15 5)
- **Main theorems:** `bb34_halts`, `bb34_main`, `sigma_eq`
- **Checked:** CI `bb34`
- **Found by:** Pavel Kropitz (machine, 2024), Shawn Ligocki (analysis); Coq proof by MiniMax, contributed by loader3229; reviewed and packaged here
- **Added:** 2026-11-08 (#48)

#### BB(4,4)

**44-B** · [write-up](BB44/1RB2LC3RA1RZ_2RC3LB2LB0LC_1LB2RC3RA1LD_2RC1LC3RD2LD.md) · the previous entries 44-C and loader3229's machine, and 44-A (also proved, between 44-C and 44-B), are kept in [`BB44/`](BB44/README.md)

```
1RB2LC3RA1RZ_2RC3LB2LB0LC_1LB2RC3RA1LD_2RC1LC3RD2LD
```

- **Proved (Coq):** σ = 2c + 2d + 9 exactly, with 2d + 4 = 2↑^(2c+2) 3, 2c + 4 = 2^(2b+4), 2b + 4 = 2↑↑↑(2a₆ + 4) and 2a₆ + 4 = 2↑^4(2a₅ + 4) (`sigma_B_closed`); F(2↑^5 3) < σ with F(n) = 2↑^(n+1)(n+3) (the Knuth-arrow function of the BB(5,4) files, not the FGH f_ω); σ is the number of nonzero cells of the halting configuration (`c_final_nonzero`, `c_final_head`); in Coq above the exact scores of 44-A, of 44-C (the previous entry) and of loader3229's machine, the wiki's BB(4,4) champion (`BB44B_beats_A`, `BB44B_beats_C`, `BB44B_beats_official`) (not yet reviewed by the bbchallenge community)
- **Main theorems:** `bb44B_halts`, `c_final_nonzero`, `sigma_B_closed`, `sigma_B_f_omega`, `BB44B_beats_A`, `BB44B_beats_C`, `BB44B_beats_official`
- **Checked:** CI `bb44`
- **Found by:** Argon (machine and macro analysis, 2026-11-09, no Coq), on Kropitz's BB(3,4) engine; Coq proof by this project (2026-11-13)
- **Added:** 2026-11-13

#### BB(5,4)

**54-L** · [write-up](BB54/1RB3LC1LD2RA_2RC1RZ2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE.md) · the previous entry, Jacobzheng's machine, is kept in [`BB54/`](BB54/README.md)

```
1RB3LC1LD2RA_2RC1RZ2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE
```

- **Proved (Coq):** F^65536(65536) < σ and F(F(2↑^4 2↑^3 4)) < σ, with F(n) = 2↑^(n+1)(n+3) (`f_omega` of the files, a Knuth-arrow function, not the FGH f_ω; on paper f_(ω+1)(65536) < σ in the FGH). In Coq above the exact σ of the previous entry, Jacobzheng's machine: its σ = 2·M1 + 2·M0 + X + 5 is at most F(F(2↑^4 2↑^3 4)) (`sigma_final_upper`, proved from the published development; formerly a hand calculation in [`BB54/README.md`](BB54/README.md)), so it is below 54-L's σ (`new_beats_jacobzheng`). The wiki's Champions page (read 2026-11-13) lists a newer BB(5,4) machine by Big_numbers (runtime > f_ω^3(2↑^15 5), not independently verified), which is not compared here (not yet reviewed by the bbchallenge community)
- **Main theorems:** `bb54_halts`, `sigma_beats_f_omega1_65536`, `sigma_beats_official_bb54`, `bb54_new_champion_main`, `sigma_final_upper`, `new_beats_jacobzheng`
- **Checked:** CI `bb54`
- **Found by:** Argon (machine and Coq proof, 2026-11-09), on Kropitz's BB(3,4) engine; probe and packaging here; the upper bound for Jacobzheng's machine and the comparison by this project (2026-11-13)
- **Added:** 2026-11-13

### Notes

- σ is the score: the number of ones on the tape after the halting transition. Where the halting transition is read
  on a 1 (champ_231/232: C1 undefined; M8 and h003: H1 undefined; the previous BB(14) entry M14_31: N1 undefined), σ = N, the ones count of the
  halted configuration; where it is `1RZ` read on a 0 (n1, C4, M12, M13_19, M14_fw3, J15_fw13, J16_w2, J17_champ, J19_sq, J20_cube, B21, W2PR, and the previous entries M11b, M13, M13b, M14, M14b, M14d_18, M16_B, M16_C, M17_B, J18_w2_C, M18_229round, BB18_fw3, J19, M19_fw4 and J20), σ = N + 1; R18c (R1), the previous BB(18) entries R18a (R1) and M18_4round (R1) and the earlier BB(19) entry M19_fw4_A (S1) halt on
  `1RZ` read on a 1, so σ = N. The hydra machines hydra29 to hydra34
  halt on B0 = `---` read on a 0, so σ = N or N + 1 by convention; their bounds are on N, so they hold for σ
  either way (their strings use the characters after Z as state names, and in hydra30, hydra32 and hydra34 `Z` is an
  ordinary state, the 26th). Each write-up's "Main facts" table says which. For the multi-symbol entries BB(5,3), BB(3,4), BB(4,4) and
  BB(5,4), σ is the number of nonzero symbols after the halting transition `1RZ` (read on a 0 for 53-Main, on a 2 for
  BB(3,4), on a 3 for 44-B, on a 1 for 54-L; the previous entries 44-C, loader3229's and Jacobzheng's read a 2, a 2 and
  a 3), counted from the explicit final tape, as for BB(4,3); for 44-B, 44-A and 44-C this count is a theorem about the
  halting configuration (`c_final_nonzero`, `sigma_is_score`).
- Rows not in the table: BB(n + k) ≥ BB(n) + k (the standard fact BB(n + 1) ≥ BB(n) + 1: redirect the halting
  transition into one new state that adds a 1 before halting), so an entry also bounds the next rows, as the BB(11) entry says for BB(12). In particular B21's
  proved bound is the best here for BB(21) to BB(24), and W2PR's for BB(25) to BB(28) (the wiki's Champions table has
  no rows between BB(21) and BB(29)).
- Fast-growing hierarchy, as defined in the Coq files: f_0(n) = n + 1, f_(k+1)(n) = f_k^n(n), f_ω(n) = f_n(n),
  f_(ω+1)(n) = f_ω^n(n), f_(ω+2)(n) = f_(ω+1)^n(n), f_(ω+3)(n) = f_(ω+2)^n(n), f_(ω+4)(n) = f_(ω+3)^n(n), and in general f_(ω+k+1)(n) = f_(ω+k)^n(n) (`f_wk` in J19's and J20's files) and
  f_(ω·2)(n) = f_(ω+n)(n) (`f_w2`; R18a's, J16_w2's, J17_champ's, J18_w2_C's, R18c's, J19_sq's and J20_cube's files use the same definitions); f_(ω·(a+1))(n) = f_(ω·a+n)(n) and f_(ω²)(n) = f_(ω·n)(n) (`f_wa`, `f_wsq` in `BB_FGH_wa.v`, B21's and W2PR's `verify_w2/`); for the hydra machines (BB29–BB34), f_α for all α < ε₀ with the standard fundamental
  sequences (`Ord.v` in their `verify/` directories), and ω↑↑k = ω^ω^…^ω (k omegas). a ↑^k b is Knuth's up-arrow.
- Comparisons, in Coq: champ_231 and champ_232 are above the BB(7) champion's score 3·(2↑^13 3) + 22 (our analysis
  of that machine, on paper) and the wiki's lower bound 2↑^11 (2↑^11 3); M8 beats champ35's and fw2's exact scores;
  h003 is above M8's Coq upper bound; n1 beats Racheline's 2024 BB(10) champion against that machine's Coq-proved exact score; M11b is above n1's Coq upper bound; C4 is above M11b's exact score (`beats_M11b`, `beats_M11b_score`: M11b's Coq upper bound) and above M12's exact score (`beats_M12_exact`, `beats_M12_score`: an upper bound on M12 from its own definitions); M13_19 is above M13b's exact score and M14_fw3 above M14_31's (`beats_M13b_exact`, `beats_M14_31_exact`: Coq upper bounds on those scores, proved from the older machines' own definitions); T12a (the previous BB(12) entry, kept in `BB12/`) beats n1's exact score; R18a's proved bound is above J19's and M18_229round's proved bounds (`beats_J19`, `beats_M18_229`); M14_31's is above M14d_18's (`beats_M14d_18`), J15_fw13's above M14_31's (`beats_M14_31`), J16_w2's above J15_fw13's, M14_31's, M16_C's and M17_B's (`beats_J15`, `beats_M14_31`, `beats_M16_C`, `beats_M17_B`), and J18_w2_C's above R18a's and J16_w2's (`beats_R18a`, `beats_J16`); J17_champ, R18c, J19_sq and J20_cube are above the exact scores of the machines they replace (`beats_J16_exact`: BB(16) + 1 = J16_w2 + 1; `beats_J18C_exact` and `beats_J17_exact`: J18_w2_C and BB(17) + 1; `beats_R18c_exact` and `beats_J20_exact`: BB(18) + 1 and J20; `beats_J19sq_exact`: BB(19) + 1), by upper bounds on those scores proved from the older machines' own definitions with the generic bounds of `JZ_UB.v`; besides its own bound, each one's `sigma_lower_bound` also states the replaced entry's proved bound; the following compare proved lower bounds; 44-B (BB(4,4)) is above the exact scores of 44-A and 44-C
  (`BB44B_beats_A`, `BB44B_beats_C`: all exact, in one development), and 44-C above the exact score of loader3229's
  machine (`beats_loader3229_exact`); 54-L (BB(5,4)) is above the exact score of Jacobzheng's
  machine (`new_beats_jacobzheng`, by the Coq upper bound `sigma_final_upper`); 53-Main (BB(5,3)) is above the BB(4,3)
  entry's exact score + 1 (`BB53_beats_BB43`, by that entry's Coq upper bound); hydra30, hydra32 and hydra34 are above the
  exact scores of hydra29, hydra31 and hydra33 (`BB30_beats_BB29`, `BB32_beats_BB31`, `BB34_beats_BB33`, by upper
  bounds proved on the published hydra29, hydra31 and hydra33 files, `BB29_upper.T4_upper`, `BB31_upper.upper_bound`,
  `BB33_upper.upper_bound`); B21's proved bound is above J20's (`beats_J20`), and W2PR's above B21's (`beats_B21`). `beats_J20` and `beats_B21` compare proved lower bounds, not upper bounds on the other machine's σ. **On
  paper only:** M12's proved lower bound exceeds T12a's (T12a is f_(ω+1)(f_(ω+1)(·))-class); M13b's and M14b's
  proved lower bounds exceed those of the previous BB(13) and BB(14) entries M13 and M14 (kept in `BB13/`, `BB14/`;
  neither has a proved upper bound) and the published BB(14)–BB(16) lower bounds; M13b runs M12's whole computation
  and then continues. None of these f_(ω+2)-class entries has been compared with the f_(ω+2)-class BB(17)/BB(18)
  champions. **Arguments, not Coq lemmas:** M16_B's proved lower bound f_(ω+2)(f_(ω+3)(9)) = f_(ω+2)^10(9) is above
  M14b's proved f_(ω+2)^9(f_(ω+1)(f_(ω+1)(3))), since f_(ω+2)(9) > f_(ω+1)(f_(ω+1)(3)), and above the f_(ω+2)-class
  BB(17) champion (Jacobzheng). BB18_fw3's proved lower bound f_(ω+3)(114) = f_(ω+2)^114(114) is far above M16_B's,
  M14b's and the f_(ω+2)-class BB(17)/BB(18) champions. M17_B's proved f_(ω+2)^116(f_(ω+3)^3(9)) is above
  BB18_fw3's, since f_(ω+3)(9) > 114 gives f_(ω+3)^3(9) > f_(ω+3)(115) = f_(ω+2)^115(115) > f_(ω+2)(f_(ω+3)(114)).
  M18_4round's f_(ω+3)^4(9) = f_(ω+2)^X(X) with X = f_(ω+3)^3(9) is above M17_B's f_(ω+2)^116(X). M14d_18's
  f_(ω+2)^17(f_(ω+1)(f_(ω+1)(3))) is above M14b's (eight more f_(ω+2) rounds) and above both 16-state entries:
  M16_C's f_(ω+2)(f_(ω+1)^114(f_(ω+2)^3(f_(ω+3)(9)))) is at most f_(ω+2)^14(9), since f_(ω+1)^114(y) ≤ f_(ω+2)(y) for
  y ≥ 114 and f_(ω+3)(9) = f_(ω+2)^9(9); M16_C's is above M16_B's f_(ω+2)^10(9). M18_229round's f_(ω+3)^229(9) is
  above M18_4round's f_(ω+3)^4(9). M19_fw4_A's f_(ω+4)(f_(ω+3)(9)) is above M19_fw4's f_(ω+4)(f_(ω+2)(114)), since
  f_(ω+3)(9) = f_(ω+2)^9(9) > f_(ω+2)(114), and M19_fw4's f_(ω+4)(n) = f_(ω+3)^n(n) with n = f_(ω+2)(114) > 229 is above
  M18_229round's f_(ω+3)^229(9). J19's proved f_(ω+7)(f_(ω+7)(5)) is far above M19_fw4_A's f_(ω+4)(f_(ω+3)(9)), since
  f_(ω+7)(5) ≥ f_(ω+3)(9), and J20's proved f_(ω·2)(f_(ω+2)^2(f_10(2))) is far above J19's, since
  f_(ω·2)(n) ≥ f_(ω+8)(n) = f_(ω+7)^n(n) for n ≥ 8; J20's proved bound is above R18a's f_(ω·2)(f_ω(f_ω(f_10(2)))), since
  f_(ω+2)(n) ≥ f_ω(n). It is also above J18_w2_C's f_(ω·2)(2·f_ω^9(35)), since for x ≥ 35,
  f_(ω+2)(x) ≥ f_(ω+1)(x) = f_ω^x(x) ≥ f_ω^10(35) ≥ 2·f_ω^9(35). B21's proved f_(ω²)^3(4↑↑341) and W2PR's proved f_(ω²)^5(4↑↑341)
  are compared with J20's and B21's in Coq (above). Apart from those proved in Coq above, these comparisons are not
  machine-checked, and they have not yet been reviewed by the bbchallenge community. J19 and J20
  are Jacobzheng's machines, the wiki's BB(19) and BB(20) champions (listed there as not independently verified);
  the Coq proofs here confirm the wiki's bounds exactly. The wiki lists them as bounds on the number of steps; σ is
  at most the number of steps, so the bounds proved here on σ give those too.
- "This project" is the repository owner's work with Claude models (Anthropic) as agents; each write-up's credit
  section has the details. Argon is a Google Gemini model run by the repository owner in Google's Antigravity; its
  machines and Coq files were re-checked here. The hydra machines BB29, BB31 and BB33 were found by mxdys, who posted
  them in the bbchallenge Discord (#large-bb-domains, 2026-10-26) as unverified AI-generated results with the bounds
  f_(ω^ω)(3), f_(ω^ω^ω^ω)(3) and f_(ω↑↑6)(3); the analysis and the Coq proofs that confirm those bounds were done here. hydra30,
  hydra32 and hydra34 are Argon's machines (2026-11-09): up to a renaming of states, mxdys's hydra29, hydra31 and
  hydra33 with one transition redirected into one new state and another start state, so that a much larger first
  hydra is built from the blank tape; Argon also wrote their Coq proofs, which were re-checked here.
  J19 and J20 were found by Jacobzheng and are listed on the bbchallenge wiki's Champions page as the BB(19) and
  BB(20) champions; the analysis and the Coq proofs that confirm the wiki's bounds were done here. R18a is this
  project's machine, derived from Jacobzheng's J20. J15_fw13, J16_w2 and J18_w2_C are Argon's machines (2026-11-08),
  compressions of Jacobzheng's J19/J20 architecture; their comparison files were written here. J17_champ, J19_sq and
  J20_cube are Argon's machines and Coq proofs (2026-11-09) on the same architecture. R18c is this project's machine
  (found 2026-11-07 with R18a); its Coq proof was written by Argon (2026-11-09). M13_19 and M14_fw3
  are Argon's machines (2026-11-09), built on M12's core; their exact-score comparison files were written here. C4 is
  this project's machine (2026-11-13), M12 with one state removed, found by an exact macro enumeration of M12's core
  plus one state; its Coq proof was written here. B21 was found by Racheline and is listed on the wiki's Champions
  page as the BB(21) champion; the analysis and the Coq proofs that confirm the wiki's bound (and one more f_(ω²))
  were done here. W2PR is this project's machine, built on Racheline's B21. 44-B (BB(4,4)) and 44-A are Argon's
  machines with his macro analysis (2026-11-09); their Coq proofs were written here. 44-C (the previous BB(4,4) entry),
  54-L (BB(5,4)) and 53-Main (BB(5,3)) are Argon's machines and Coq proofs (2026-11-09), on the engine of Kropitz's BB(3,4) champion
  (Ligocki's configurations and `g` hierarchy); they were re-checked here, and 44-C's comparison file was written
  here. The Coq proofs of the earlier 4-symbol entries BB(3,4), loader3229's BB(4,4) and Jacobzheng's BB(5,4) machines
  were written by MiniMax (an AI model) and contributed by loader3229
  (#48); they were reviewed, re-built and packaged here (CI jobs, `bb54_halts`). Their machines are by Pavel Kropitz
  (analysed by Shawn Ligocki), loader3229 and Jacobzheng, all listed on the bbchallenge wiki's Champions page when they were added.
- Each directory has a README with the entry's files, its full list of theorems and how to build it:
  [BB7](BB7/README.md), [BB8](BB8/README.md), [BB9](BB9/README.md), [BB10](BB10/README.md),
  [BB11](BB11/README.md), [BB12](BB12/README.md), [BB13](BB13/README.md), [BB14](BB14/README.md), [BB15](BB15/README.md), [BB16](BB16/README.md), [BB17](BB17/README.md), [BB18](BB18/README.md), [BB19](BB19/README.md), [BB20](BB20/README.md), [BB21](BB21/README.md), [BB25](BB25/README.md), [BB29](BB29/README.md), [BB30](BB30/README.md),
  [BB31](BB31/README.md), [BB32](BB32/README.md), [BB33](BB33/README.md), [BB34_2](BB34_2/README.md) (34 states, 2 symbols), [BB43](BB43/README.md), [BB53](BB53/README.md), [BB34](BB34/README.md), [BB44](BB44/README.md),
  [BB54](BB54/README.md), [PA](PA/README.md), [ZF](ZF/README.md).

## Consistency machines

Turing machines that halt from the blank tape if and only if a theory is inconsistent, each proved end to end in Coq
with closed assumptions.

| theory | states | machine | main theorems | by | directory |
|---|---|---|---|---|---|
| ZF, ZFC | **253** | [`zfc_253.tm`](ZF/m253/machine/zfc_253.tm) | `zf253_halts_iff_ZF`, `zf253_halts_iff_ZFC` | mira-emmy (a one-state reduction of Mira-Cult's 254) | [`ZF/m253/`](ZF/m253/) |
| ZF, ZFC | 254 | [`zfc_254.tm`](ZF/m254/machine/zfc_254.tm) | `zf254_halts_iff_ZF`, `zf254_halts_iff_ZFC` | Mira-Cult (machine); Coq proof here | [`ZF/m254/`](ZF/m254/) |
| ZFC + Grothendieck universes | **296** | [`m254tg_wade.tm`](ZF/tg296/machine/m254tg_wade.tm) | `tg296_halts_iff_ZFGU`, `tg296_halts_iff_ZFCGU` | this project (Mira-Cult's program plus one schema, Wade's compiler) | [`ZF/tg296/`](ZF/tg296/) |
| ZF, ZFC, with or without regularity | 335 | [`R3Y1_335.tm`](ZF/machines/R3Y1_335.tm) | `zf335_halts_iff_ZF`, …, `zf335_halts_iff_ZFC_reg` | this project (Wade's compiler) | [`ZF/stdzf_r3/`](ZF/stdzf_r3/) |
| PA | **238** | [`pa_238.tm`](PA/m238/machine/pa_238.tm) | `pa238_iff_ordinary_proved` | mira-emmy | [`PA/m238/`](PA/m238/) |
| PA + ¬Goldbach, i.e. halts iff PA ⊢ Goldbach's conjecture | **449** | [`pa_wade.tm`](PA/goldbach/machine/pa_wade.tm) | `pagb_halts_iff_PA_GC`, `GC_adequate` | this project (Mira-Cult's program with new axiom rows, Wade's compiler) | [`PA/goldbach/`](PA/goldbach/) |

Bold: the smallest machine here for that theory. The last row is a provability machine: `pagb_halts_iff_PA_GC`
states that it halts iff `PAeq ⊢ GC_form`, and `GC_adequate` that `GC_form` holds in ℕ iff Goldbach's conjecture
does. [`ZF/README.md`](ZF/README.md) has the whole ZF line (393, 361, 354,
336, 335 states, from Wade's 393-state machine), what has to be trusted, and the credits.

## Decided holdouts

Machines from bbchallenge holdout lists proved in Coq never to halt from the blank tape (`~ halts tm c0`, no axioms).

| | machines | directory | checked |
|---|---|---|---|
| **BB(7)** | 131 holdouts of the June 2026 list (16,949,557 machines): seven with individual arguments (`1RB1LD_1RC0RF_…`, `1RB0RC_1RC0RA_…`, `1RB1RE_1LC0RA_…`, `1RB1RE_1RC1RA_…`, `1RB1RF_0LC1LD_…`, and c01/c02 `1RB---_0RC0RA_…_0LD0LB`, `…_0RD0LB`) and 124 digit-list machines with one shared proof scheme | [`BB7/holdouts/`](BB7/holdouts/README.md) | CI `bb7-holdouts` |

## Superseded entries

Their files stay where they are: most are proof bases of the current entries or are still built in CI, and links
elsewhere point at these paths.

| | machine | entry | superseded by | why the files remain |
|---|---|---|---|---|
| BB(8) | [`1RB0RA_..._1LC0RH_1RG1LF`](BB8/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_1LC0RH_1RG1LF.txt) (champ35), σ = 12·(2↑^37 3) + 59 exactly | 2026-10-04 to 2026-10-18 | M8 (`m8_beats_champ35`) | M8's comparison loads its Coq files ([`BB8/verify/`](BB8/verify/), CI `bb8`); n1 and T12a begin with its computation |
| BB(9) | [`1RB0RA_..._0LI---_1LC0RA`](BB9/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_1LC0RA.md) (C7), f_ω(f_ω(f_ω(f_ω(f_ω(f_ω(12)))))) < σ | 2026-10-22 (#32) | h003 (one f_ω higher) | h003's proof reuses five of its files ([`BB9/verify_c7/`](BB9/verify_c7/), CI `bb9-c7`) |
| BB(9) | [`1RB0RA_..._0LI---_0RC1RF`](BB9/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_0RC1RF.md) (f3_0RC), above M8's Coq upper bound | 2026-10-22 (#30 to #32) | C7 | C7's and h003's proofs reuse its files ([`BB9/verify_f3/`](BB9/verify_f3/), CI `bb9-f3`) |
| BB(9) | [`1RB0RA_..._1RI---_0RI0RF`](BB9/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF.md) (C04), f_ω³(12) < σ < f_ω³(13) | 2026-10-18 to 2026-10-19 | M8 (8 states, the same score) | the proof base of M8, f3_0RC, C7 and h003 ([`BB9/verify_c04/`](BB9/verify_c04/), CI `bb9-c04`) |
| BB(9) | [`1RB0RD_..._1RD1RI_1RZ1RA`](BB9/1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA.md) (fw2, by Argon), f_ω(f_ω(465009)) < σ | 2026-10-17 to 2026-10-18 | C04 (`c04_beats_fw2`) | C04's tree uses copies of its files ([`BB9/verify_fw2/`](BB9/verify_fw2/), CI `bb9-fw2`) |
| BB(9) | [`1RB0RA_..._0RG0RE_0LH1RZ`](BB9/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_1RG1LD_0RH0RF_0RG0RE_0LH1RZ.txt) (the 2026-10-07 record), σ = 3·(2↑^(6T−33) 8) + (54T + 26)/5, T = 2↑^13 3 | 2026-10-07 to 2026-10-17 | fw2 (`fw2_beats_record`) | kept as published ([`BB9/verify/`](BB9/verify/)); fw2's comparison uses copies of its Coq files |
| BB(11) | [`1RG0LH_..._1LH1LI_1LJ1RE`](BB11/1RG0LH_1RK1RC_0LD1LA_0RE1LD_0LI1RF_1RZ0RG_1RB1RG_1LA1LH_0LK0LJ_1LH1LI_1LJ1RE.md) (M11b, by Argon), f_(ω+1)(f_ω(f_ω(5))) < N, σ = N + 1 < f_(ω+1)(f_ω(f_ω(6))) | 2026-10-26 to 2026-11-13 | C4 (`beats_M11b_score`, against its exact score) | C4's comparison loads its Coq files; its comparison with n1 stays ([`BB11/verify/`](BB11/verify/), CI `bb13-bb14`) |
| BB(13) | [`1RB1RA_..._0LH1LK_1RZ0LH`](BB13/1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LL0LL_0LH1LK_1RZ0LH.md) (M13b), f_(ω+2)^6(f_(ω+1)(f_(ω+1)(3))) < σ | 2026-10-28 to 2026-11-12 | M13_19 (`beats_M13b_exact`, against its exact score) | M13_19's comparison loads its Coq files ([`BB13/verify_m13b/`](BB13/verify_m13b/), CI `bb13-bb14`) |
| BB(14) | [`1RB1RA_..._0LK0LH_1LM---`](BB14/1RB1RA_1RI1RC_0LD1LG_0RE1LD_0RN1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LL0LL_0LH1LK_0LK0LH_1LM---.md) (M14_31), f_(ω+2)^30(f_(ω+1)(f_(ω+1)(3))) < σ | 2026-11-08 to 2026-11-12 | M14_fw3 (`beats_M14_31_exact`, against its exact score) | M14_fw3's comparison loads its Coq file ([`BB14/verify_m14_31/`](BB14/verify_m14_31/), CI `bb13-bb14`) |
| BB(18) | [`0LB1LF_..._0LH1RR_0LF1RP`](BB18/0LB1LF_0RC1LB_0RD1RM_1LE0RN_1LF1LE_1LG0LE_1RH1RP_1RI1RH_0LJ1RA_1LK1LJ_0LL1LJ_1RM1RC_0RM0RH_1LE1RO_1RZ1RD_0LF0RQ_0LH1RR_0LF1RP.md) (J18_w2_C, by Argon), f_(ω·2)(2·f_ω^9(35)) < N, σ = N + 1 | 2026-11-08 to 2026-11-13 | R18c (`beats_J18C_exact`, against its exact score) | R18c's comparison loads its Coq file ([`BB18/verify_j18c/`](BB18/verify_j18c/), CI `bb13-bb14`) |
| BB(20) | [`1LH0LG_..._0LF1LT_0LF0LR`](BB20/1LH0LG_0LI1RC_0LD1LA_0RE1LD_1RQ1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_0RF0LO_0RF1LP_0RF1LN_1LR1RQ_1RZ1LS_0LF1LT_0LF0LR.md) (J20, by Jacobzheng), f_(ω·2)(f_(ω+2)(f_(ω+2)(f_10(2)))) < N, σ = N + 1 | 2026-11-07 to 2026-11-13 | J20_cube (via J19_sq: `beats_J19sq_exact` and `beats_J20_exact`, against exact scores) | J19_sq's comparison loads its Coq file ([`BB20/verify/`](BB20/verify/), CI `bb13-bb14`) |
| BB(4,4) | [`0LB3LB1RZ2RA_..._0RD2RC2LB0RA`](BB44/0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA.md) (loader3229; Coq proof by MiniMax), σ = 2↑^509 3 + 510 exactly | 2026-11-08 to 2026-11-13 | 44-C (`beats_loader3229_exact`, against its exact score) | 44-C's comparison loads its Coq files ([`BB44/verify/`](BB44/verify/), CI `bb44`) |
| BB(4,4) | [`1RB3LB1RZ2RA_..._3RB1LB3LD2RD`](BB44/1RB3LB1RZ2RA_1LC3RB1LD2RA_3RB2LC1LC3LC_3RB1LB3LD2RD.md) (44-C, Argon), σ = 2↑^65532 6 + 65532 exactly | 2026-11-13 (#67) to 2026-11-13 | 44-B (`BB44B_beats_C`, against its exact score) | 44-B's proof uses copies of its Coq files ([`BB44/verify_44c/`](BB44/verify_44c/), CI `bb44`) |
| BB(5,4) | [`1LD3LB---2RA_..._------1LD1RZ`](BB54/1LD3LB---2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_3RB---3LE3LD_------1LD1RZ.md) (Jacobzheng; Coq proof by MiniMax), halts, σ = 2·M1 + 2·M0 + X + 5 exactly | 2026-11-08 to 2026-11-13 | 54-L (`new_beats_jacobzheng`, against its exact score) | kept as published ([`BB54/verify/`](BB54/verify/), CI `bb54`) |

## Layout and CI

- `BBn/`: one directory per number of states (`BB43/`, `BB53/`: 4 and 5 states, 3 symbols; `BB34/`, `BB44/`, `BB54/`: 3, 4 and 5 states, 4 symbols;
  `BB34_2/`: 34 states, 2 symbols). In each: the write-ups
  (`<machine string>.md`, older ones `.txt`), `verify*/` (Coq, on [busycoq](https://github.com/meithecatte/busycoq)
  at commit `bd2e36f` with Coq 8.20.1, unless the README says otherwise), `tools/` (independent simulators that
  re-check the write-ups' rules), and a `README.md` index.
- `ZF/`, `PA/`: the consistency machines, each with its own `check.py` (see their READMEs).
- [`.github/workflows/coq.yml`](.github/workflows/coq.yml) builds every entry except BB(10) (about 20 min), M11b's comparison with n1 (about 6 min), T12a in BB(12)
  (about 3 h) and stage 2 of fw2 (about 2 h); their recorded local builds are in their directories. On a pull request
  a job runs only when its entry's files (or files it depends on) change; editing the workflow alone runs no job. Every
  job runs in the weekly scheduled run and on manual runs (Actions > Coq proofs > Run workflow).
  [`zf253.yml`](.github/workflows/zf253.yml) checks `ZF/m253/` on every push and pull request.
