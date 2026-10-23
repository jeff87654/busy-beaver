# busy-beaver

[![Coq proofs](https://github.com/jeff87654/busy-beaver/actions/workflows/coq.yml/badge.svg?branch=main)](https://github.com/jeff87654/busy-beaver/actions/workflows/coq.yml)

Busy beaver machines with machine-checked proofs. Every bound in the tables below is a Coq theorem, checked with no
axioms (`Print Assumptions` reports "Closed under the global context"), unless it is marked "on paper". Machines are
named by their standard strings; the short names (M8, n1, ...) are labels used in the write-ups.

## Current entries

| | machine | proved (Coq) | main theorems | checked | found by | added |
|---|---|---|---|---|---|---|
| **BB(7)** | [`1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_0LD0RB`](BB7/1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_0LD0RB.md) (champ_231; its twin champ_232 = `…_1LC0RB` has the same score) | 3↑^20 3 < σ, with σ = 2·W₂₀(5) + 7 exactly | `c231_halts`, `c231_score`, `c231_lower`, `c231_beats_bb7_champion` (and `c232_*`) | CI `bb7` | Argon (a Google Gemini model run by the repository owner) in this project's scan of the bbchallenge BB(7) holdout list; Coq proof here | 2026-10-22 |
| **BB(8)** | [`1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---`](BB8/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---.md) (M8) | f_ω(f_ω(f_ω(12))) < σ < f_ω(f_ω(f_ω(13))) | `m8_halts`, `m8_fgh3`, `m8_bracket`, `m8_score_exact` | CI `bb8-m8` | this project (reduced from C04) | 2026-10-19 (#27) |
| **BB(9)** | [`1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_1LC0RA`](BB9/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_1LC0RA.md) (C7) | f_ω(f_ω(f_ω(f_ω(f_ω(f_ω(12)))))) < σ, and f_ω⁵(2·(2↑^13 3)) < σ | `c7_halts`, `c7_lower6_12`, `c7_lower5`, `c7_beats_m8_bound` | CI `bb9-c7` | this project | 2026-10-22 (#32) |
| **BB(10)** | [`1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RZ0LC`](BB10/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RZ0LC.md) (n1) | f_(ω+1)((3T − 13)/7 − 2) < N < f_(ω+1)(6T), σ = N + 1, T = 2↑^37 3 | `halt`, `score_exact`, `fgh_level`, `beats_champion`, `beats_graham` | local build (about 20 min) | this project | 2026-10-08 (#3) |
| **BB(12)** | [`1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RK0LC_0RL---_0RF1RZ`](BB12/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RK0LC_0RL---_0RF1RZ.md) (T12a) | f_(ω+1)(f_(ω+1)((3T − 13)/7 − 2)) ≤ 6σ + 11 | `halt`, `fgh_lower2`, `beats_n1` | local build (about 3 h) | this project | 2026-10-11 (#12) |
| **BB(13)** | [`1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_0LG1RI_1RE0RH_1LF0RC_1RM0LE_1LA1LE_0LL1LB_0RM1LL_1RZ1RH`](BB13/1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_0LG1RI_1RE0RH_1LF0RC_1RM0LE_1LA1LE_0LL1LB_0RM1LL_1RZ1RH.md) (M13) | f_(ω+2)(f_ω(20)) < σ | `halt`, `score_exact`, `sigma_lower_bound_strong` | CI `bb13-bb14` | Argon | 2026-10-14 (#17) |
| **BB(14)** | [`1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LN1RF_1LJ0RA_1RA0LH_1LG1LH_1RK0LM_1RZ0LE_0LE0RJ_1LH1LM_0LH0LL_0LG1LN`](BB14/1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LN1RF_1LJ0RA_1RA0LH_1LG1LH_1RK0LM_1RZ0LE_0LE0RJ_1LH1LM_0LH0LL_0LG1LN.md) (M14) | f_(ω+2)(f_(ω+2)(f_(ω+2)(15))) < σ | `halt`, `score_exact`, `sigma_lower_bound` | CI `bb13-bb14` | Argon | 2026-10-14 (#17) |
| **BB(4,3)** | [`1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD`](BB43/1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD.md) | σ = 4·e₄ + 18 exactly, 2↑↑↑2↑↑↑2↑↑↑(2^96 − 1) < e₄ ≤ 2↑↑↑2↑↑↑2↑↑↑(2^96 + 6) | `bb43_halts`, `bb43_main`, `e4_bounds`, `wiki_bracket` | CI `bb43` | Kropitz (machine), Polygon (analysis); Coq proof here | 2026-10-17 (#22, #23) |

- σ is the score: the number of ones on the tape after the halting transition. Where the halting transition is read
  on a 1 (champ_231/232: C1 undefined; M8 and C7: H1 undefined; T12a: L1 = `1RZ`), σ = N, the ones count of the
  halted configuration; where it is `1RZ` read on a 0 (n1, M13, M14), σ = N + 1. Each write-up's "Main facts" table says which.
- Fast-growing hierarchy, as defined in the Coq files: f_0(n) = n + 1, f_(k+1)(n) = f_k^n(n), f_ω(n) = f_n(n),
  f_(ω+1)(n) = f_ω^n(n), f_(ω+2)(n) = f_(ω+1)^n(n). a ↑^k b is Knuth's up-arrow.
- Comparisons, in Coq: champ_231 and champ_232 are above the BB(7) champion's score 3·(2↑^13 3) + 22 (our analysis
  of that machine, on paper) and the wiki's lower bound 2↑^11 (2↑^11 3); M8 beats champ35's and fw2's exact scores;
  C7 is above M8's Coq upper bound; n1 beats Racheline's 2024 BB(10) champion against that machine's Coq-proved exact score; T12a beats n1's exact score. **On
  paper only:** M13's and M14's proved lower bounds exceed T12a's and the published BB(14)–BB(16) lower bounds; they
  have not been compared with the f_(ω+2)-class BB(17)/BB(18) champions. BB(11) has no entry of its own here.
- "This project" is the repository owner's work with Claude models (Anthropic) as agents; each write-up's credit
  section has the details. Argon is a Google Gemini model run by the repository owner in Google's Antigravity; its
  machines and Coq files were re-checked here.
- Each directory has a README with the entry's files, its full list of theorems and how to build it:
  [BB7](BB7/README.md), [BB8](BB8/README.md), [BB9](BB9/README.md), [BB10](BB10/README.md),
  [BB12](BB12/README.md), [BB13](BB13/README.md), [BB14](BB14/README.md), [BB43](BB43/README.md), [PA](PA/README.md), [ZF](ZF/README.md).

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

Bold: the smallest machine here for that theory. [`ZF/README.md`](ZF/README.md) has the whole ZF line (393, 361, 354,
336, 335 states, from Wade's 393-state machine), what has to be trusted, and the credits.

## Superseded entries

Their files stay where they are: most are proof bases of the current entries or are still built in CI, and links
elsewhere point at these paths.

| | machine | entry | superseded by | why the files remain |
|---|---|---|---|---|
| BB(8) | [`1RB0RA_..._1LC0RH_1RG1LF`](BB8/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_1LC0RH_1RG1LF.txt) (champ35), σ = 12·(2↑^37 3) + 59 exactly | 2026-10-04 to 2026-10-18 | M8 (`m8_beats_champ35`) | M8's comparison loads its Coq files ([`BB8/verify/`](BB8/verify/), CI `bb8`); n1 and T12a begin with its computation |
| BB(9) | [`1RB0RA_..._0LI---_0RC1RF`](BB9/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_0RC1RF.md) (f3_0RC), above M8's Coq upper bound | 2026-10-22 (#30 to #32) | C7 | C7's proof reuses its files ([`BB9/verify_f3/`](BB9/verify_f3/), CI `bb9-f3`) |
| BB(9) | [`1RB0RA_..._1RI---_0RI0RF`](BB9/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF.md) (C04), f_ω³(12) < σ < f_ω³(13) | 2026-10-18 to 2026-10-19 | M8 (8 states, the same score) | the proof base of M8, f3_0RC and C7 ([`BB9/verify_c04/`](BB9/verify_c04/), CI `bb9-c04`) |
| BB(9) | [`1RB0RD_..._1RD1RI_1RZ1RA`](BB9/1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA.md) (fw2, by Argon), f_ω(f_ω(465009)) < σ | 2026-10-17 to 2026-10-18 | C04 (`c04_beats_fw2`) | C04's tree uses copies of its files ([`BB9/verify_fw2/`](BB9/verify_fw2/), CI `bb9-fw2`) |
| BB(9) | [`1RB0RA_..._0RG0RE_0LH1RZ`](BB9/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_1RG1LD_0RH0RF_0RG0RE_0LH1RZ.txt) (the 2026-10-07 record), σ = 3·(2↑^(6T−33) 8) + (54T + 26)/5, T = 2↑^13 3 | 2026-10-07 to 2026-10-17 | fw2 (`fw2_beats_record`) | kept as published ([`BB9/verify/`](BB9/verify/)); fw2's comparison uses copies of its Coq files |

## Layout and CI

- `BBn/`: one directory per number of states (`BB43/`: 4 states, 3 symbols). In each: the write-ups
  (`<machine string>.md`, older ones `.txt`), `verify*/` (Coq, on [busycoq](https://github.com/meithecatte/busycoq)
  at commit `bd2e36f` with Coq 8.20.1, unless the README says otherwise), `tools/` (independent simulators that
  re-check the write-ups' rules), and a `README.md` index.
- `ZF/`, `PA/`: the consistency machines, each with its own `check.py` (see their READMEs).
- [`.github/workflows/coq.yml`](.github/workflows/coq.yml) builds every entry except BB(10) (about 20 min), BB(12)
  (about 3 h) and stage 2 of fw2 (about 2 h); their recorded local builds are in their directories. On a pull request
  a job runs only when its entry's files (or files it depends on) change; editing the workflow alone runs no job. Every
  job runs in the weekly scheduled run and on manual runs (Actions > Coq proofs > Run workflow).
  [`zf253.yml`](.github/workflows/zf253.yml) checks `ZF/m253/` on every push and pull request.
