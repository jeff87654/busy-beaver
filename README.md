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

| | machine | proved (Coq) | main theorems | checked | found by | added |
|---|---|---|---|---|---|---|
| **BB(7)** | [`1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_0LD0RB`](BB7/1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_0LD0RB.md) (champ_231; its twin champ_232 = `…_1LC0RB` has the same score) | 3↑^20 3 < σ, with σ = 2·W₂₀(5) + 7 exactly; above the champion's 3·(2↑^13 3) + 22 (not yet reviewed by the bbchallenge community) | `c231_halts`, `c231_score`, `c231_lower`, `c231_beats_bb7_champion` (and `c232_*`) | CI `bb7` | Argon (a Google Gemini model run by the repository owner) in this project's scan of the bbchallenge BB(7) holdout list; Coq proof here | 2026-10-22 (#34) |
| **BB(8)** | [`1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---`](BB8/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---.md) (M8) | f_ω(f_ω(f_ω(12))) < σ < f_ω(f_ω(f_ω(13))) | `m8_halts`, `m8_fgh3`, `m8_bracket`, `m8_score_exact` | CI `bb8-m8` | this project (reduced from C04) | 2026-10-19 (#27) |
| **BB(9)** | [`1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LH0LC_1RG1LD_0RG0RF_0LI---_1RI1RC`](BB9/1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LH0LC_1RG1LD_0RG0RF_0LI---_1RI1RC.md) (h003) | f_ω(f_ω(f_ω(f_ω(f_ω(f_ω(f_ω(12))))))) < σ, and f_ω⁶(6·(2↑^13 3) + 2) < σ | `h003_halts`, `h003_lower7_12`, `h003_lower`, `h003_beats_m8_bound` | CI `bb9-h003` | this project | 2026-10-22 (#36) |
| **BB(10)** | [`1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RZ0LC`](BB10/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RZ0LC.md) (n1) | f_(ω+1)((3T − 13)/7 − 2) < N < f_(ω+1)(6T), σ = N + 1, T = 2↑^37 3 | `halt`, `score_exact`, `fgh_level`, `beats_champion`, `beats_graham` | local build (about 20 min) | this project | 2026-10-08 (#3) |
| **BB(11)** | [`1RG0LH_1RK1RC_0LD1LA_0RE1LD_0LI1RF_1RZ0RG_1RB1RG_1LA1LH_0LK0LJ_1LH1LI_1LJ1RE`](BB11/1RG0LH_1RK1RC_0LD1LA_0RE1LD_0LI1RF_1RZ0RG_1RB1RG_1LA1LH_0LK0LJ_1LH1LI_1LJ1RE.md) (M11b) | f_(ω+1)(f_ω(f_ω(5))) < N, σ = N + 1 < f_(ω+1)(f_ω(f_ω(6))) | `halt`, `score_exact`, `sigma_bracket_m11`, `M11_beats_n1` | CI `bb13-bb14` (`M11_beats_n1`: local build, about 6 min) | Argon | 2026-10-26 |
| **BB(12)** | [`1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_0LH1LK`](BB12/1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_0LH1LK.md) (M12) | f_(ω+2)(f_(ω+1)(f_(ω+1)(3))) < σ, σ = N + 1 | `halt`, `score_exact`, `sigma_lower_bound_m12` | CI `bb13-bb14` | Argon | 2026-10-26 |
| **BB(13)** | [`1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LM1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_0LM1LK_0LG1LL`](BB13/1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LM1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_0LM1LK_0LG1LL.md) (M13_19; the previous entries M13b and M13 are kept in [`BB13/`](BB13/README.md)) | f_(ω+2)^19(f_ω(3)) < N, σ = N + 1; in Coq, above the exact score of M13b, the previous entry (its N = p + a + 5 for (p, a) = `pa7`, proved below f_(ω+2)^14(f_ω(3)) from M13b's own definitions) (not yet reviewed by the bbchallenge community) | `halt`, `sigma_bound`, `sigma_bound_fw1`, `beats_M13b`, `beats_M13b_exact`, `beats_M13b_score` (and `_tnf` versions for the relabelled table) | CI `bb13-bb14` | Argon (machine and Coq proof); exact-score comparison, probe and packaging here | 2026-11-12 |
| **BB(14)** | [`1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_1LN1LK_1RK0LH_1LD0RK`](BB14/1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_1LN1LK_1RK0LH_1LD0RK.md) (M14_fw3; the previous entries M14_31, M14d_18 and M14b are kept in [`BB14/`](BB14/README.md)) | f_(ω+3)(f_ω(3)) < N, σ = N + 1, with N = p + a + 6 exactly for (p, a) = `pa_final`; in Coq, above the exact score of M14_31, the previous entry (its σ = N = p + a + 4 for (p, a) = `pa32`, proved below f_(ω+2)^64(f_ω(3)) from M14_31's own definitions); far below the proved bounds of the BB(15) and BB(16) entries, so those rows stay (not yet reviewed by the bbchallenge community) | `halt`, `score_exact`, `sigma_bound`, `beats_M14_31`, `beats_M14_31_exact`, `beats_M14_31_score` (and `_tnf` versions for the relabelled table) | CI `bb13-bb14` | Argon (machine and Coq proof); exact-score comparison, probe and packaging here | 2026-11-12 |
| **BB(15)** | [`1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LA0RN_0LA1RO_1RZ1RM`](BB15/1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LA0RN_0LA1RO_1RZ1RM.md) (J15_fw13) | f_(ω+13)(20) < N, σ = N + 1, with N = 2j + 1 exactly, hoc_0^14(4) + 29 = 3j for the machine's recursion (halts after two refills, by a mod-3 invariant); in Coq, above M14_31's proved bound (BB(14)); the wiki's Champions table has no BB(15) row (not yet reviewed by the bbchallenge community) | `halt`, `step_1012`, `score_exact`, `sigma_lower_bound`, `beats_M14_31` | CI `bb13-bb14` | Argon (machine and Coq proof, a compression of Jacobzheng's J19/J20 architecture); comparison, probe and packaging here | 2026-11-08 |
| **BB(16)** | [`1LG1LA_0LI1RC_0LD1LG_0RE1LD_0RM1RL_1RB1RF_1LH0LA_1RF0RN_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LG0RN_0RP1RO_1RZ1RM_1LB1LI`](BB16/1LG1LA_0LI1RC_0LD1LG_0RE1LD_0RM1RL_1RB1RF_1LH0LA_1RF0RN_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LG0RN_0RP1RO_1RZ1RM_1LB1LI.md) (J16_w2; the previous entries M16_C and M16_B are kept in [`BB16/`](BB16/README.md)) | f_(ω·2)(f_15(2)) < N, σ = N + 1, with N = 2j + 4 exactly for the machine's recursion (halts after two refills, by residues mod 3 and mod 9); in Coq, above the proved bounds of M16_C, of M17_B (BB(17)), of J15_fw13 and of M14_31, so BB(17) ≥ BB(16) + 1 is the best proved bound for BB(17) too; the wiki's Champions table has no BB(16) row (not yet reviewed by the bbchallenge community) | `halt`, `score_exact`, `sigma_lower_bound`, `beats_M16_C`, `beats_M17_B`, `beats_J15`, `beats_M14_31` | CI `bb13-bb14` | Argon (machine and Coq proof, a compression of Jacobzheng's J19/J20 architecture); comparisons, probe and packaging here | 2026-11-08 |
| **BB(17)** | [`1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0LO_1LP1LN_0RB1LI_1RZ1LO`](BB17/1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0LO_1LP1LN_0RB1LI_1RZ1LO.md) (M17_B) | f_(ω+2)^116(f_(ω+3)^3(9)) < N, σ = N + 1, with N = p + a + 5 exactly for (p, a) = `pa_final`; on paper (an argument, not a Coq lemma) above the proved bounds of BB18_fw3 and M16_B; J16_w2's proved bound (BB(16)) is above it in Coq (`beats_M17_B`), so BB(17) ≥ BB(16) + 1 is the better proved bound for BB(17) (not yet reviewed by the bbchallenge community) | `halt`, `score_exact`, `sigma_lower_bound`, `sigma_lower_bound_fw3_3` | CI `bb13-bb14` | Argon (machine and Coq proof); probe and packaging here | 2026-11-02 |
| **BB(18)** | [`0LB1LF_0RC1LB_0RD1RM_1LE0RN_1LF1LE_1LG0LE_1RH1RP_1RI1RH_0LJ1RA_1LK1LJ_0LL1LJ_1RM1RC_0RM0RH_1LE1RO_1RZ1RD_0LF0RQ_0LH1RR_0LF1RP`](BB18/0LB1LF_0RC1LB_0RD1RM_1LE0RN_1LF1LE_1LG0LE_1RH1RP_1RI1RH_0LJ1RA_1LK1LJ_0LL1LJ_1RM1RC_0RM0RH_1LE1RO_1RZ1RD_0LF0RQ_0LH1RR_0LF1RP.md) (J18_w2_C; the previous entries R18a, M18_229round, M18_4round and BB18_fw3 are kept in [`BB18/`](BB18/README.md)) | f_(ω·2)(2·f_ω^9(35)) < N, σ = N + 1, with N = 2j + 2 exactly for the machine's recursion (halts after exactly two refills, by a mod-3 invariant); in Coq, above R18a's proved f_(ω·2)(f_ω(f_ω(f_10(2)))) and J16_w2's f_(ω·2)(f_15(2)), so BB(19) ≥ BB(18) + 1 is the best proved bound for BB(19) (not yet reviewed by the bbchallenge community) | `halt`, `score_exact`, `sigma_lower_bound`, `beats_R18a`, `beats_J16` | CI `bb13-bb14` | Argon (machine and Coq proof, a compression of Jacobzheng's J20 by two states); comparisons, probe and packaging here | 2026-11-08 |
| **BB(19)** | [`1RQ1RL_0LI1RC_0LD1LF_0RA1LD_1RB1RE_1LH0LG_1LF1LG_1RE1RM_1LJ1LI_0LK1LI_1RL1RA_0RL0RE_0LN1RM_1LO0LO_1RE1LP_1LN1LN_1LR1RQ_1RZ1LS_0LE0LR`](BB19/1RQ1RL_0LI1RC_0LD1LF_0RA1LD_1RB1RE_1LH0LG_1LF1LG_1RE1RM_1LJ1LI_0LK1LI_1RL1RA_0RL0RE_0LN1RM_1LO0LO_1RE1LP_1LN1LN_1LR1RQ_1RZ1LS_0LE0LR.md) (J19; the earlier entries M19_fw4_A and M19_fw4, Argon's, are kept in [`BB19/`](BB19/README.md)) | f_(ω+7)(f_(ω+7)(5)) < N, σ = N + 1, with 2N = T_8(2) + 23 exactly for the machine's recursion T; the wiki's claimed bound, exactly; the BB(18) entries R18a and J18_w2_C have higher proved bounds, in Coq (`beats_J19`, `beats_R18a`), so BB(19) ≥ BB(18) + 1 is the better proved bound for BB(19) | `halt`, `score_exact`, `sigma_lower_bound` | CI `bb13-bb14` | Jacobzheng (the bbchallenge wiki's BB(19) champion, listed as not independently verified); analysis and Coq proof here | 2026-11-07 |
| **BB(20)** | [`1LH0LG_0LI1RC_0LD1LA_0RE1LD_1RQ1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_0RF0LO_0RF1LP_0RF1LN_1LR1RQ_1RZ1LS_0LF1LT_0LF0LR`](BB20/1LH0LG_0LI1RC_0LD1LA_0RE1LD_1RQ1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_0RF0LO_0RF1LP_0RF1LN_1LR1RQ_1RZ1LS_0LF1LT_0LF0LR.md) (J20) | f_(ω·2)(f_(ω+2)(f_(ω+2)(f_10(2)))) < N, σ = N + 1, with N = 2j + 1 exactly for the machine's recursion (halts after exactly two refills, by a mod-3 invariant); the wiki's claimed bound, exactly | `halt`, `score_exact`, `sigma_lower_bound` | CI `bb13-bb14` | Jacobzheng (the bbchallenge wiki's BB(20) champion, listed as not independently verified); analysis and Coq proof here | 2026-11-07 |
| **BB(21)** | [`0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LR`](BB21/0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LR.md) (B21; the first published bound, 4↑↑341 < N, is kept in [`BB21/verify/`](BB21/verify/)) | f_(ω²)(f_(ω²)(f_(ω²)(4↑↑341))) < N, σ = N + 1, one f_(ω²) above the wiki's claimed f_(ω²)^2(4↑↑341), which is also proved in the wiki's form (`sigma_lower_bound_wsq`), so the wiki's claim is confirmed and the new bound is stronger; halts at the sixth refill, by a residue schedule mod 4 and a dominance invariant; in Coq, above J20's proved bound f_(ω·2)(f_(ω+2)^2(f_10(2))) (BB(20), `beats_J20`) (not yet reviewed by the bbchallenge community) | `halt`, `sigma_lower_bound_wsq3`, `sigma_lower_bound_wsq`, `beats_J20`, `sigma_lower_bound` | CI `bb13-bb14` | Racheline (the bbchallenge wiki's BB(21) champion, listed as not independently verified); analysis and Coq proof here | 2026-11-08 (#53; ω² bound #55) |
| **BB(25)** | [`0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LV_0LH0LW_1LH0LX_1LH1LY_0LE1LR`](BB25/0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LV_0LH0LW_1LH0LX_1LH1LY_0LE1LR.md) (W2PR; the first published bound, Fh⁵(4↑↑341) < N with Fh f_ω-class, is kept in [`BB25/verify/`](BB25/verify/)) | f_(ω²)^5(4↑↑341) < N, σ = N + 1 (five applications of f_(ω²)); halts at the eighth refill, after five big ω² phases (B21 with its refill tested mod 8 instead of mod 4); in Coq, above B21's proved f_(ω²)^3(4↑↑341) (BB(21), `beats_B21`) (not yet reviewed by the bbchallenge community) | `halt`, `sigma_lower_bound_wsq`, `beats_B21`, `sigma_lower_bound` | CI `bb13-bb14` | this project (built on Racheline's B21: U1 changed to `1LV` and a copy V–Y of B21's refill cycle, so the refill tests the accumulator mod 8) | 2026-11-08 (#54; ω² bound #56) |
| **BB(29)** | [`0LP1LD_---0LC_1LR0LB_1RF1LE_0LD1LD_0R[1RG_1RN0RK_0RI1RJ_1LZ1RH_0RH1RH_0RL1RM_1L\1RK_0RK1RK_0RO1RO_0L\1RN_1R[1LA_0RV0RV_0LT1LS_0R[1LT_0RY1LU_0LR1L\_0RW1RX_0RN1RV_0LC1RV_0LA1LZ_0LY1LY_0RQ0RH_1L]1LR_1LH1LZ`](BB29/hydra29.md) (hydra machine) | f_(ω^ω)(3) < N, with N = T₄(S)(1) + 1 exactly | `halt`, `score_exact`, `sigma_lower_bound` | CI `bb13-bb14` | mxdys (AI-generated, posted in the bbchallenge Discord); Coq proof here | 2026-10-27 |
| **BB(31)** | [`0RK1RK_---0LC_1LQ0LB_1RF1LE_0LD1LD_0R\1RG_1RM0RK_0RI1RJ_1L[1RH_0RH1RH_0RL1RA_1L]1RK_0RN1RN_0L]1RM_1R\1L^_0RW0RW_0LU1LR_0R\1LS_0L]1LT_0LQ1LU_0RZ1LV_0LS1L]_0RX1RY_0RM1RW_0LC1RW_0L^1L[_0LZ1LZ_0RP0RH_1L_1LQ_0LO1LD_1LH1L[`](BB31/hydra31.md) (hydra machine) | f_(ω^ω^ω^ω)(4) ≤ N + 2, so f_(ω^ω^ω^ω)(3) < N | `halt`, `hardy_score`, `sigma_lower_bound_w4` | CI `bb13-bb14` | mxdys (AI-generated, posted in the bbchallenge Discord); Coq proof here | 2026-10-27 |
| **BB(33)** | [``1LH1L^_---0LC_1LR0LB_1RF1LE_0LD1LD_0R_1RG_1RN0RK_0RI1RJ_1L^1RH_0RH1RH_0RL1RM_1L`1RK_0RK1RK_0RO1RO_0L`1RN_1R_1La_0RZ0RZ_0LX1LS_0R_1LT_0L`1LU_0LR1LV_0LS1LW_0LT1LX_0R]1LY_0LV1L`_0R[1R\_0RN1RZ_0LC1RZ_0La1L^_0L]1L]_0RQ0RH_1LA1LR_0LP1LD``](BB33/hydra33.md) (hydra machine) | f_(ω^ω^ω^ω^ω^3)(4) ≤ N + 2, so f_(ω↑↑6)(3) < N | `halt`, `hardy_score`, `sigma_lower_bound_w6` | CI `bb13-bb14` | mxdys (AI-generated, posted in the bbchallenge Discord); Coq proof here | 2026-10-27 |
| **BB(4,3)** | [`1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD`](BB43/1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD.md) | σ = 4·e₄ + 18 exactly, 2↑↑↑2↑↑↑2↑↑↑(2^96 − 1) < e₄ ≤ 2↑↑↑2↑↑↑2↑↑↑(2^96 + 6) | `bb43_halts`, `bb43_main`, `e4_bounds`, `wiki_bracket` | CI `bb43` | Kropitz (machine), Polygon (analysis); Coq proof here | 2026-10-17 (#22, #23) |
| **BB(3,4)** | [`1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC`](BB34/1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC.md) | σ = 2↑^15 5 + 14 exactly (the wiki's champion, listed as > 2↑^15 5) | `bb34_halts`, `bb34_main`, `sigma_eq` | CI `bb34` | Pavel Kropitz (machine, 2024), Shawn Ligocki (analysis); Coq proof by MiniMax, contributed by loader3229; reviewed and packaged here | 2026-11-08 (#48) |
| **BB(4,4)** | [`0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA`](BB44/0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA.md) | σ = 2↑^509 3 + 510 exactly (the wiki's champion, listed as > 2↑^509 3 and as not independently verified) | `bb44_halts`, `bb44_main`, `sigma_eq` | CI `bb44` | loader3229 (machine, 2026); Coq proof by MiniMax, contributed by loader3229; reviewed and packaged here | 2026-11-08 (#48) |
| **BB(5,4)** | [`1LD3LB---2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_3RB---3LE3LD_------1LD1RZ`](BB54/1LD3LB---2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_3RB---3LE3LD_------1LD1RZ.md) | halts, with σ = 2·M1 + 2·M0 + X + 5 exactly, for X = g_5(g_4(0)) and nested `g` chains M0, M1 (Ligocki's `g` hierarchy; see [BB54/README.md](BB54/README.md)). Only halting and this exact formula are proved: the wiki's bound f_ω²(10↑^4 10↑↑65533) is on paper only, a hand calculation in the README | `bb54_halts`, `bb54_halt_main` | CI `bb54` | Jacobzheng (machine, 2026; the wiki's champion, listed as not independently verified); Coq proof by MiniMax, contributed by loader3229; reviewed and packaged here | 2026-11-08 (#48) |

- σ is the score: the number of ones on the tape after the halting transition. Where the halting transition is read
  on a 1 (champ_231/232: C1 undefined; M8 and h003: H1 undefined; the previous BB(14) entry M14_31: N1 undefined), σ = N, the ones count of the
  halted configuration; where it is `1RZ` read on a 0 (n1, M11b, M12, M13_19, M14_fw3, J15_fw13, J16_w2, M17_B, J18_w2_C, J19, J20, B21, W2PR, and the previous entries M13, M13b, M14, M14b, M14d_18, M16_B, M16_C, M18_229round, BB18_fw3 and M19_fw4), σ = N + 1; the previous BB(18) entries R18a (R1) and M18_4round (R1) and the earlier BB(19) entry M19_fw4_A (S1) halt on
  `1RZ` read on a 1, so σ = N. The hydra machines BB29, BB31
  and BB33 halt on B0 = `---` read on a 0, so σ = N or N + 1 by convention; their bounds are on N, so they hold for σ
  either way. Each write-up's "Main facts" table says which. For the 4-symbol entries BB(3,4), BB(4,4) and BB(5,4),
  σ is the number of nonzero symbols after the halting transition `1RZ` (read on a 2 for BB(3,4) and BB(4,4), on a 3
  for BB(5,4)), counted from the explicit final tape, as for BB(4,3).
- Rows not in the table: BB(n + k) ≥ BB(n) + k (the standard fact BB(n + 1) ≥ BB(n) + 1: redirect the halting
  transition into one new state that adds a 1 before halting), so an entry also bounds the next rows, as the BB(16) and BB(18) rows say for BB(17) and BB(19). In particular B21's
  proved bound is the best here for BB(21) to BB(24), and W2PR's for BB(25) to BB(28) (the wiki's Champions table has
  no rows between BB(21) and BB(29)).
- Fast-growing hierarchy, as defined in the Coq files: f_0(n) = n + 1, f_(k+1)(n) = f_k^n(n), f_ω(n) = f_n(n),
  f_(ω+1)(n) = f_ω^n(n), f_(ω+2)(n) = f_(ω+1)^n(n), f_(ω+3)(n) = f_(ω+2)^n(n), f_(ω+4)(n) = f_(ω+3)^n(n), and in general f_(ω+k+1)(n) = f_(ω+k)^n(n) (`f_wk` in J19's and J20's files) and
  f_(ω·2)(n) = f_(ω+n)(n) (`f_w2`; R18a's, J16_w2's and J18_w2_C's files use the same definitions); f_(ω·(a+1))(n) = f_(ω·a+n)(n) and f_(ω²)(n) = f_(ω·n)(n) (`f_wa`, `f_wsq` in `BB_FGH_wa.v`, B21's and W2PR's `verify_w2/`); for BB29–BB33, f_α for all α < ε₀ with the standard fundamental
  sequences (`Ord.v` in their `verify/` directories), and ω↑↑k = ω^ω^…^ω (k omegas). a ↑^k b is Knuth's up-arrow.
- Comparisons, in Coq: champ_231 and champ_232 are above the BB(7) champion's score 3·(2↑^13 3) + 22 (our analysis
  of that machine, on paper) and the wiki's lower bound 2↑^11 (2↑^11 3); M8 beats champ35's and fw2's exact scores;
  h003 is above M8's Coq upper bound; n1 beats Racheline's 2024 BB(10) champion against that machine's Coq-proved exact score; M11b is above n1's Coq upper bound; M13_19 is above M13b's exact score and M14_fw3 above M14_31's (`beats_M13b_exact`, `beats_M14_31_exact`: Coq upper bounds on those scores, proved from the older machines' own definitions); T12a (the previous BB(12) entry, kept in `BB12/`) beats n1's exact score; R18a's proved bound is above J19's and M18_229round's proved bounds (`beats_J19`, `beats_M18_229`); M14_31's is above M14d_18's (`beats_M14d_18`), J15_fw13's above M14_31's (`beats_M14_31`), J16_w2's above J15_fw13's, M14_31's, M16_C's and M17_B's (`beats_J15`, `beats_M14_31`, `beats_M16_C`, `beats_M17_B`), and J18_w2_C's above R18a's and J16_w2's (`beats_R18a`, `beats_J16`); these compare proved lower bounds; B21's proved bound is above J20's (`beats_J20`), and W2PR's above B21's (`beats_B21`). `beats_J20` and `beats_B21` compare proved lower bounds, not upper bounds on the other machine's σ. **On
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
  are compared with J20's and B21's in Coq (above). None of these machines has a proved upper bound, so the
  comparisons are not machine-checked, and they have not yet been reviewed by the bbchallenge community. J19 and J20
  are Jacobzheng's machines, the wiki's BB(19) and BB(20) champions (listed there as not independently verified);
  the Coq proofs here confirm the wiki's bounds exactly. The wiki lists them as bounds on the number of steps; σ is
  at most the number of steps, so the bounds proved here on σ give those too.
- "This project" is the repository owner's work with Claude models (Anthropic) as agents; each write-up's credit
  section has the details. Argon is a Google Gemini model run by the repository owner in Google's Antigravity; its
  machines and Coq files were re-checked here. The hydra machines BB29, BB31 and BB33 were found by mxdys, who posted
  them in the bbchallenge Discord (#large-bb-domains, 2026-10-26) as unverified AI-generated results with the bounds
  f_(ω^ω)(3), f_(ω^ω^ω^ω)(3) and f_(ω↑↑6)(3); the analysis and the Coq proofs that confirm those bounds were done here.
  J19 and J20 were found by Jacobzheng and are listed on the bbchallenge wiki's Champions page as the BB(19) and
  BB(20) champions; the analysis and the Coq proofs that confirm the wiki's bounds were done here. R18a is this
  project's machine, derived from Jacobzheng's J20. J15_fw13, J16_w2 and J18_w2_C are Argon's machines (2026-11-08),
  compressions of Jacobzheng's J19/J20 architecture; their comparison files were written here. M13_19 and M14_fw3
  are Argon's machines (2026-11-09), built on M12's core; their exact-score comparison files were written here. B21 was found by Racheline and is listed on the wiki's Champions
  page as the BB(21) champion; the analysis and the Coq proofs that confirm the wiki's bound (and one more f_(ω²))
  were done here. W2PR is this project's machine, built on Racheline's B21. The Coq proofs of
  the 4-symbol entries BB(3,4), BB(4,4) and BB(5,4) were written by MiniMax (an AI model) and contributed by loader3229
  (#48); they were reviewed, re-built and packaged here (CI jobs, `bb54_halts`). Their machines are by Pavel Kropitz
  (analysed by Shawn Ligocki), loader3229 and Jacobzheng, all listed on the bbchallenge wiki's Champions page.
- Each directory has a README with the entry's files, its full list of theorems and how to build it:
  [BB7](BB7/README.md), [BB8](BB8/README.md), [BB9](BB9/README.md), [BB10](BB10/README.md),
  [BB11](BB11/README.md), [BB12](BB12/README.md), [BB13](BB13/README.md), [BB14](BB14/README.md), [BB15](BB15/README.md), [BB16](BB16/README.md), [BB17](BB17/README.md), [BB18](BB18/README.md), [BB19](BB19/README.md), [BB20](BB20/README.md), [BB21](BB21/README.md), [BB25](BB25/README.md), [BB29](BB29/README.md),
  [BB31](BB31/README.md), [BB33](BB33/README.md), [BB43](BB43/README.md), [BB34](BB34/README.md), [BB44](BB44/README.md),
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
| BB(13) | [`1RB1RA_..._0LH1LK_1RZ0LH`](BB13/1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LL0LL_0LH1LK_1RZ0LH.md) (M13b), f_(ω+2)^6(f_(ω+1)(f_(ω+1)(3))) < σ | 2026-10-28 to 2026-11-12 | M13_19 (`beats_M13b_exact`, against its exact score) | M13_19's comparison loads its Coq files ([`BB13/verify_m13b/`](BB13/verify_m13b/), CI `bb13-bb14`) |
| BB(14) | [`1RB1RA_..._0LK0LH_1LM---`](BB14/1RB1RA_1RI1RC_0LD1LG_0RE1LD_0RN1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LL0LL_0LH1LK_0LK0LH_1LM---.md) (M14_31), f_(ω+2)^30(f_(ω+1)(f_(ω+1)(3))) < σ | 2026-11-08 to 2026-11-12 | M14_fw3 (`beats_M14_31_exact`, against its exact score) | M14_fw3's comparison loads its Coq file ([`BB14/verify_m14_31/`](BB14/verify_m14_31/), CI `bb13-bb14`) |

## Layout and CI

- `BBn/`: one directory per number of states (`BB43/`: 4 states, 3 symbols; `BB34/`, `BB44/`, `BB54/`: 3, 4 and 5 states, 4 symbols). In each: the write-ups
  (`<machine string>.md`, older ones `.txt`), `verify*/` (Coq, on [busycoq](https://github.com/meithecatte/busycoq)
  at commit `bd2e36f` with Coq 8.20.1, unless the README says otherwise), `tools/` (independent simulators that
  re-check the write-ups' rules), and a `README.md` index.
- `ZF/`, `PA/`: the consistency machines, each with its own `check.py` (see their READMEs).
- [`.github/workflows/coq.yml`](.github/workflows/coq.yml) builds every entry except BB(10) (about 20 min), M11b's comparison with n1 (about 6 min), T12a in BB(12)
  (about 3 h) and stage 2 of fw2 (about 2 h); their recorded local builds are in their directories. On a pull request
  a job runs only when its entry's files (or files it depends on) change; editing the workflow alone runs no job. Every
  job runs in the weekly scheduled run and on manual runs (Actions > Coq proofs > Run workflow).
  [`zf253.yml`](.github/workflows/zf253.yml) checks `ZF/m253/` on every push and pull request.
