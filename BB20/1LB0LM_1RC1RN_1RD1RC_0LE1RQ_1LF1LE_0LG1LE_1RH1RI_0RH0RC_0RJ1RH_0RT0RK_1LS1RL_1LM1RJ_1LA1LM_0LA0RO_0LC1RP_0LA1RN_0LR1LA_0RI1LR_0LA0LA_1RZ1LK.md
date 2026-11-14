# J20_cube: a 20-state machine at level f_(ω·2)^3, on Jacobzheng's two-list engine

    1LB0LM_1RC1RN_1RD1RC_0LE1RQ_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RJ1RH_0RT0RK_1LS1RL_1LM1RJ_1LA1LM_0LA0RO_0LC1RP_0LA1RN_0LR1LA_0RI1LR_0LA0LA_1RZ1LK

The machine is written in tree normal form (start in A, states named in order of first use), the table the Coq file
proves. Argon's file also gives it in the lettering of J20's core (comment only, checked here by comparing the two
tables under the renaming): `1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RR1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LA0RN_0LF1RO_0LA1RM_1LT1RQ_1LG1RR_0RS0RP_1RZ1LP_0LA0LA`.

|   | 0   | 1   |                                                                              |
|---|-----|-----|------------------------------------------------------------------------------|
| A | 1LB | 0LM | engine: A1 erases the first cell of a digit ≥ 2 (J20's A)                     |
| B | 1RC | 1RN | <B = the inner list's left end (`CI`); B1 = marker: the expansion, into N     |
| C | 1RD | 1RC | C> = the sweep over a list (`SW`, `CO`) (J20's F)                             |
| D | 0LE | 1RQ | engine (J20's B)                                                              |
| E | 1LF | 1LE | engine: end of a list (J20's I)                                               |
| F | 0LG | 1LE | engine (J20's J)                                                              |
| G | 1RH | 1RI | engine: G1 = outer list used up (J20's K)                                     |
| H | 0RH | 0RC | engine: start of a sweep (J20's L)                                            |
| I | **0RJ** | 1RH | engine (J20's E); I0 starts the refill                                    |
| J | **0RT** | 0RK | J> at the merged block (`EX`); refill rewriter, period 3 (with K, L)      |
| K | **1LS** | 1RL | refill                                                                    |
| L | 1LM | 1RJ | refill                                                                        |
| M | 1LA | 1LM | engine: walk back (J20's G)                                                   |
| N | 0LA | 0RO | expansion rewriter, period 3 (with O, P)                                      |
| O | 0LC | 1RP | expansion                                                                     |
| P | 0LA | 1RN | expansion                                                                     |
| Q | 0LR | 1LA | engine (J20's C)                                                              |
| R | 0RI | 1LR | engine (J20's D)                                                              |
| S | **0LA** | **0LA** | refill (new)                                                          |
| T | **1RZ** | **1LK** | after the refill rewriter: T0 = `1RZ`, the halt (blank right of the block); T1 = a sentinel |

J20_cube is J19_sq ([`../BB19/`](../BB19/)) with one more state: the entries in bold are new or changed (J19_sq's
halting state S becomes T, with T1 = `1LK`; K0 = `1LS` enters the new state S). Engine, expansion and level maps are
J19_sq's (the Coq definitions `h`, `hc`, `G0`, `G`, `ho`, `hoc` have the same text). The refill can now park a
**two-cell** sentinel 1 1 behind the outer list, so the third refill does not end the sentinel's life: it leaves
one more refill for later. Four refills, three rounds at level f_(ω·2).

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB20_J20_w2_cube.halt`. The halt is decided by residues mod 3 and the sentinel, which the proof follows exactly: every level map is x ↦ x + 1 (mod 3), for every residue of x. |
| Exact score | Machine-checked formula: the halting tape holds 2(j + 1) + 1 ones, where ho_0^2(10) + 4 = 3(k₁ + 2) + 1, a₂ = hoc_0^(k₁+1)(10), a₂ + 2(k₁ + 1) + 2 = 3(k₂ + 2), a₃ = hoc_0^(k₂)(10), a₃ + 2(k₂ + 1) + 2 = 3(k₃ + 1) + 2, a₄ = ho_(k₃)^4(hoc_0^(k₃)(10)) and a₄ + 2(k₃ + 1) + 2 = 3(j + 1) (section 1; `score_exact`). The halt T0 = `1RZ` is read on a 0, so σ = N + 1 = 2j + 4. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω·2)^3(f_5(2)) < N (`sigma_lower_bound`, which also states f_(ω·2)(f_(ω+2)(f_(ω+2)(f_10(2)))) < N). |
| Comparisons | **In Coq**: the second form is exactly J20's proved bound (the previous BB(20) entry), so N is above it. Comparisons with the exact scores of J20 and of J19_sq (BB(19) + 1): on paper only (section 4). |
| Steps | Not computed. |

## 1. How it works

The configurations, the engine and the outer rules are J19_sq's (read [its write-up](../BB19/) first): the inner
list CI x [...] R, the outer list CO a [...] R, the merged block EX B R = 0^∞ 1 0 J> 1^B 0 R with the right part R
(blank, or a sentinel), and

    outer head map     G(3c) = G₀(c),  G(3c + 1) = 3c + 5,  G(3c + 2) = G₀(c) + 2,  G₀(c) = hc_1^c(6) + 2c + 4
    outer level maps   ho_0 = G,  ho_(m+1)(a) = ho_m^(a+1)(6),  hoc_m^0(a) = a,  hoc_m^(n+1)(a) = hoc_(m+1)^n(ho_m(a))

    R0   CO a [e+2, r] R           →*  CO G(a) [e+1, r] R
    R1   CO a [1^(p+1), e+2, r] R  →*  CO 6 [1^p, a+2, e+1, r] R
    OEX  CO a [1^n] (0 R)          →*  EX (a + 2n + 2) R           (one 0 of the right part is taken off)

The refill reads the block with J, K, L (period 3) and then the cells after it:

| block, right part | result |
|---|---|
| 5, blank | the outer list CO 10 [3] (`RF_1`; only at the boot) |
| 3(k + 2) + 1, blank | CO 10 [2^(k+1)], right part 0 1 0^∞: a one-cell sentinel parked (`RF_2`) |
| 3(k + 2), sentinel 1 | CO 10 [2^k, 1], right part 0 1 1 0^∞: the sentinel grows to two cells (`RF_3`) |
| 3(k + 1) + 2, sentinel 1 1 | both cells taken in: CO 10 [2^k, 5], right part blank (`RF_4`) |
| 3k, blank | T reads the blank: T0 = `1RZ`, the halt, with 2k + 1 ones (`RF_halt`, `ones_Hc`) |

## 2. The run, and why it halts

| phase | result |
|---|---|
| boot, round 1, exhaustion 1, round 2 | as in J19_sq: CO 3 [] (`boot`), EX 5, CO 10 [3], a₁ = ho_0^2(10), EX (3(k₁ + 2) + 1), CO 10 [2^(k₁+1)] with a sentinel, a₂ = hoc_0^(k₁+1)(10) |
| exhaustion 2 | EX 3(k₂ + 2) with the sentinel 1: refill CO 10 [2^(k₂), 1], sentinel 1 1 |
| round 3 | `Chain_out` on the k₂ twos at outer levels 0, ..., k₂ − 1: CO a₃ [1^(k₂+1)], a₃ = hoc_0^(k₂)(10) |
| exhaustion 3 | EX (a₃ + 2(k₂ + 1) + 2) = EX (3(k₃ + 1) + 2) with the sentinel 1 1: refill CO 10 [2^(k₃), 5], blank right part |
| round 4 | `Chain_out` on the k₃ twos, then the digit 5 at level k₃: CO a₄ [1^(k₃+1)], a₄ = ho_(k₃)^4(hoc_0^(k₃)(10)) |
| exhaustion 4 | EX (a₄ + 2(k₃ + 1) + 2) = EX 3(j + 1), blank right part: the halt (`run_gen`, `run`, `halt`) |

**The mod-3 invariant.** As in J19_sq, hoc_m^n(a) ≡ a + n (mod 3) and ho_m^4(a) ≡ a + 4. The first two exhaustions
are those of J19_sq (classes 1 and 0). Then a₃ ≡ 10 + k₂ and a₃ + 2(k₂ + 1) + 2 ≡ 3k₂ + 14 ≡ 2 at the third (refill
`RF_4`, which needs the two-cell sentinel), and a₄ ≡ 10 + k₃ + 4, a₄ + 2(k₃ + 1) + 2 ≡ 3k₃ + 18 ≡ 0 at the fourth,
with nothing to the right: the halt (`K1_gen`, `K2_gen`, `K3_gen`, `J_gen`). Nothing depends on a residue the proof
does not compute.

**Size.** As in J19_sq, k₂ is of order f_(ω·2)(f_5(2)); round 3 ends at outer level k₂ − 1, so k₃ is of order
f_(ω·2)(k₂), and round 4 reduces its last digit at level k₃: N > f_(ω·2)^3(f_5(2)) (`bound_4refill`,
`sigma_lower_bound`).

## 3. Verification

[`verify_j20cube/`](verify_j20cube/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about a minute, built in
CI (job `bb13-bb14`). `probe.v` re-checks the transition table entry by entry against the string above (40 checks
generated from the string) and the blank start configuration, prints the definitions the statements use, and
confirms that `halt`, `score_exact` and `sigma_lower_bound` are closed under the global context. The proof also
passes this project's `check.py` (2026-11-13), and literal simulation here reproduces the boot lemmas (CO 3 [] at
step 13, EX 5 at step 26, CO 10 [3] at step 108).

`BB20_J20_w2_cube.v` is Argon's file, unchanged except for the first line `(* machine: ... *)`, added here (the string
above, which is the file's transition table), which `check.py` reads. There is no
independent simulator for this write-up; every rule cited is a lemma of the Coq file.

## 4. Comparisons

- **In Coq**: f_(ω·2)(f_(ω+2)(f_(ω+2)(f_10(2)))) < N, the proved bound of Jacobzheng's J20 (the previous BB(20)
  entry, the bbchallenge wiki's BB(20) champion). That compares proved lower bounds; J20 has no proved upper bound.
- **On paper**: J20 halts after two refills, with one round at level f_(ω·2), at a level of order
  f_(ω+2)^2(f_10(2)); here there are three such rounds. And J20_cube's first two refills and rounds are exactly
  J19_sq's, after which it runs a further round at level k₂ and a fourth refill, so its N is far above J19_sq's exact
  score + 1.
- B21 ([`../BB21/`](../BB21/), f_(ω²)-class) stays far above. Not yet reviewed by the bbchallenge community.

## Credit

Found and proved in Coq by Argon, a Google Gemini model run by the repository owner in Google's Antigravity
(2026-11-09), on Jacobzheng's J19/J20 architecture (the engine, the two lists and the mod-3 schedule are
Jacobzheng's), as a one-state extension of Argon's J19_sq. Re-checked here (check.py, clean build, probe, literal
simulation of the boot, the core renaming), with this write-up.
