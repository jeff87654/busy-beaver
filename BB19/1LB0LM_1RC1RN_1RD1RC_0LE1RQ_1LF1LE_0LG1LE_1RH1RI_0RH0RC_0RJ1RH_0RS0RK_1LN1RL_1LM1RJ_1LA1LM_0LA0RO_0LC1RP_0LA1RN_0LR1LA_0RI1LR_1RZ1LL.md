# J19_sq: a 19-state machine at level f_(ω·2)^2, on Jacobzheng's two-list engine

    1LB0LM_1RC1RN_1RD1RC_0LE1RQ_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RJ1RH_0RS0RK_1LN1RL_1LM1RJ_1LA1LM_0LA0RO_0LC1RP_0LA1RN_0LR1LA_0RI1LR_1RZ1LL

The machine is written in tree normal form (start in A, states named in order of first use), the table the Coq file
proves. Argon's file also gives it in the lettering of J20's core (comment only, checked here by comparing the two
tables under the renaming): `1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RR1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LA0RN_0LF1RO_0LA1RM_1LM1RQ_1LG1RR_0RS0RP_1RZ1LQ`.

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
| J | 0RS | 0RK | J> at the merged block (`EX`); refill rewriter, period 3 (with K, L: `triRPQ`) |
| K | 1LN | 1RL | refill                                                                        |
| L | 1LM | 1RJ | refill                                                                        |
| M | 1LA | 1LM | engine: walk back (J20's G)                                                   |
| N | 0LA | 0RO | expansion rewriter, period 3 (with O, P: `triMNO`)                            |
| O | 0LC | 1RP | expansion                                                                     |
| P | 0LA | 1RN | expansion                                                                     |
| Q | 0LR | 1LA | engine (J20's C)                                                              |
| R | 0RI | 1LR | engine (J20's D)                                                              |
| S | **1RZ** | 1LL | after the refill rewriter: S0 = `1RZ`, the halt (blank right of the block); S1 = the sentinel (below) |

Under the renaming, rows A–L of the core lettering are Jacobzheng's 12-state J20 core ([`../BB20/`](../BB20/)) with
E0 changed (here: rows A–I, M, Q, R, with I0 changed). The outer head map, the outer level maps and the three-state
expansion N, O, P are those of Argon's J18_w2_C ([`../BB18/`](../BB18/); the Coq definitions `h`, `hc`, `G0`, `G`,
`ho`, `hoc` have the same text). The new part is the four-state refill J, K, L, S, which can leave a **sentinel**, a
single 1 parked behind the outer list after a gap of two 0s. The outer rounds never reach it; when the list is used up, the
merged block ends next to it, and the refill reads it. That gives the machine a third refill: two rounds at level
f_(ω·2) instead of one.

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB19_J19_w2_sq.halt`. The halt is decided by residues mod 3 and the sentinel, which the proof follows exactly: every level map is x ↦ x + 1 (mod 3), for every residue of x. |
| Exact score | Machine-checked formula: the halting tape holds 2(j + 1) + 1 ones, where ho_0^2(10) + 4 = 3(k₁ + 2) + 1, a₂ = hoc_0^(k₁+1)(10), a₂ + 2(k₁ + 1) + 2 = 3(k₂ + 2), a₃ = ho_(k₂)^4(hoc_0^(k₂)(10)) and a₃ + 2(k₂ + 1) + 2 = 3(j + 1) (section 1; `score_exact`). The halt S0 = `1RZ` is read on a 0, so σ = N + 1 = 2j + 4. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω·2)(f_(ω·2)(f_5(2))) < N (`sigma_lower_bound`, which also states f_(ω·2)(f_(ω+2)(f_(ω+2)(f_10(2)))) < N and f_(ω·2)(2·f_ω^9(35)) < N). |
| Comparisons | **In Coq**, against the exact scores: N > N(R18c) = σ(R18c), so σ(J19_sq) = N + 1 > σ(R18c) + 1 = BB(18) + 1 (`BB19_J19sq_cmp.beats_R18c_exact`, `beats_R18c_score`), and N > N(J20), so σ(J19_sq) > σ(J20), Jacobzheng's 20-state machine (`beats_J20_exact`, `beats_J20_score`; section 4). |
| Steps | Not computed. |

## 1. How it works

The configurations (Coq names) are the inner list CI x [...] R = 0^∞ <B 1^x 0 [...] R, the outer list
CO a [...] R = 0^∞ 1 0 0 C> 1^a 0 [...] R and the merged block EX B R = 0^∞ 1 0 J> 1^B 0 R, where R is the rest of the
tape to the right: the blank tape 0^∞, or a sentinel 1 0^∞. The inner rules are J20's (`CI_E0`, `CI_E1`, `CI_exit`,
`LV_in`, `Chain_in`), the outer rules hold for every R (`R0`, `R1`, `OEX`), and

    inner level maps   h_0(x) = x + 4,  h_(m+1)(x) = h_m^(x+2)(2),  hc_m^0(x) = x,  hc_m^(n+1)(x) = hc_(m+1)^n(h_m(x))
    outer head map     G(3c) = G₀(c),  G(3c + 1) = 3c + 5,  G(3c + 2) = G₀(c) + 2,  G₀(c) = hc_1^c(6) + 2c + 4
    outer level maps   ho_0 = G,  ho_(m+1)(a) = ho_m^(a+1)(6)                      (level m is f_(ω+m)-class)
    hoc_m^0(a) = a,  hoc_m^(n+1)(a) = hoc_(m+1)^n(ho_m(a))

    R0   CO a [e+2, r] R           →*  CO G(a) [e+1, r] R          (`EXP_0`, `EXP_1`, `EXP_2`, `R0`)
    R1   CO a [1^(p+1), e+2, r] R  →*  CO 6 [1^p, a+2, e+1, r] R   (`R1`)
    OEX  CO a [1^n] (0 R)          →*  EX (a + 2n + 2) R           (the outer list used up, `OEX`)

OEX takes one 0 off the right part: a sentinel parked as 0 1 0^∞ behind the list ends up directly right of the
merged block. The refill reads the block with J, K, L (period 3) and then the cell after it:

| block, right part | result |
|---|---|
| 5, blank | the outer list CO 10 [3] (`RF_1`; only at the boot) |
| 3(k + 2) + 1, blank | the outer list CO 10 [2^(k+1)], with a sentinel parked behind it: right part 0 1 0^∞ (`RF_2`) |
| 3(k + 2), sentinel | the sentinel is taken in: the outer list CO 10 [2^k, 5], right part blank (`RF_3`) |
| 3k, blank | S reads the blank: S0 = `1RZ`, the halt, with 2k + 1 ones (`RF_halt`, `ones_Hc`) |

## 2. The run, and why it halts

| phase | result |
|---|---|
| boot | CO 3 [] (`boot`; step 13 by literal simulation here), EX 5: refill CO 10 [3] (step 108) |
| round 1 | the digit 3 at outer level 0 (two R0 rounds): CO a₁ [1], a₁ = ho_0^2(10) |
| exhaustion 1 | EX (a₁ + 4) = EX (3(k₁ + 2) + 1): refill CO 10 [2^(k₁+1)], sentinel parked |
| round 2 | `Chain_out` on the k₁ + 1 twos at outer levels 0, ..., k₁: CO a₂ [1^(k₁+1)], a₂ = hoc_0^(k₁+1)(10) |
| exhaustion 2 | EX (a₂ + 2(k₁ + 1) + 2) = EX 3(k₂ + 2), sentinel next to it: refill CO 10 [2^(k₂), 5], blank right part |
| round 3 | `Chain_out` on the k₂ twos at levels 0, ..., k₂ − 1, then the digit 5 at level k₂ (four rounds of ho_(k₂)): CO a₃ [1^(k₂+1)], a₃ = ho_(k₂)^4(hoc_0^(k₂)(10)) |
| exhaustion 3 | EX (a₃ + 2(k₂ + 1) + 2) = EX 3(j + 1), blank right part: the halt (`run_gen`, `run`, `halt`) |

**The mod-3 invariant.** Every level map is x ↦ x + 1 (mod 3) (`G_P1`, `ho_P1`; R1 restarts at 6 ≡ 0), so
hoc_m^n(a) ≡ a + n. Then a₁ ≡ 10 + 2 ≡ 0 and a₁ + 4 ≡ 1 at the first exhaustion; a₂ ≡ 10 + k₁ + 1 and
a₂ + 2(k₁ + 1) + 2 ≡ 3k₁ + 15 ≡ 0 at the second, where the sentinel is waiting; a₃ ≡ 10 + k₂ + 4 and
a₃ + 2(k₂ + 1) + 2 ≡ 3k₂ + 18 ≡ 0 at the third, with nothing to the right: the halt. The block lengths are
≡ 0 (mod 3) at the second and the third exhaustion alike; only the sentinel tells them apart. Nothing depends on a
residue the proof does not compute.

**Size.** a₁ ≥ 8·f_5(2) (`a1_bound`), so k₁ is of order f_5(2); round 2 ends at outer level k₁, so k₂ is of order
f_(ω·2)(f_5(2)); round 3 reduces its last digit at level k₂: N > f_(ω·2)(f_(ω·2)(f_5(2))) (`bound_3refill`,
`sigma_lower_bound`).

## 3. Verification

[`verify_j19sq/`](verify_j19sq/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about a minute, built in
CI (job `bb13-bb14`). `probe.v` re-checks the transition table entry by entry against the string above (38 checks
generated from the string) and the blank start configuration, prints the definitions the statements use, and
confirms that `halt`, `score_exact` and `sigma_lower_bound` are closed under the global context. The proof also
passes this project's `check.py` (2026-11-13), and literal simulation here reproduces the boot lemmas (CO 3 [] at
step 13, EX 5 at step 26, CO 10 [3] at step 108).

`BB19_J19_w2_sq.v` is Argon's file, unchanged except for the first line `(* machine: ... *)`, added here (the string
above, which is the file's transition table), which `check.py` reads. There is no
independent simulator for this write-up; every rule cited is a lemma of the Coq file.

## 4. Comparisons

- **In Coq**: f_(ω·2)(2·f_ω^9(35)) < N and f_(ω·2)(f_(ω+2)(f_(ω+2)(f_10(2)))) < N, the proved bounds of J18_w2_C
  (BB(18) until R18c) and of Jacobzheng's 20-state J20 (the previous BB(20) entry). Those compare proved lower
  bounds.
- **In Coq, against the exact scores** (`BB19_J19sq_cmp.v`, written here): `beats_R18c_exact` states that for the a₁, k₁, b₀,
  a₂, j of R18c's `score_exact` (count 2(j + 1) + 1 = σ(R18c)), 2(j + 1) + 1 < N; `beats_J20_exact` states that for
  the k, a₂, j of J20's `score_exact` (count 2j + 1, σ = 2j + 2), 2j + 1 < N. Both via upper bounds
  N(R18c), N(J20) ≤ f_(ω·2)(Z) with Z ≤ f_(ω·2)(f_5(2)). The `_score` versions combine these with the other machines'
  halting tapes. The upper bounds come from `JZ_UB.v` (written here): for any maps satisfying the engine's equations, h_m(y) + 4 ≤ f_(m+1)(y + 4), hc_m^n(x) + 4 ≤ f_ω(m + n + x + 5), ho_m(a) + 20 ≤ f_(ω+m)(a + 20) and hoc_m^n(a) + 20 ≤ f_(ω+m+n+1)(n + a + 20), given G(a) + 20 ≤ f_ω(a + 20), which the comparison file proves for the older machine's own head map.
- **Why**: R18c, J18_w2_C and J20 halt after two refills, with one round at level f_(ω·2) whose level comes from
  an f_(ω+1)-sized number (R18c), an f_ω^15-sized one (J18_w2_C) or an f_(ω+2)^2(f_10(2))-sized one (J20). Here the
  second refill already gives an f_(ω·2)(f_5(2))-sized k₂, and round 3 runs at that level, so J19_sq's N is far
  above the exact scores of R18c (+ 1), J18_w2_C (+ 1) and J20.
- The previous BB(19) entry, Jacobzheng's J19 (f_(ω+7)(f_(ω+7)(5)) < N), was already below the proved bounds of the
  BB(18) entries in Coq (`beats_J19` in [`../BB18/verify_r18a/`](../BB18/verify_r18a/)).
- The 20-state J20_cube ([`../BB20/`](../BB20/)) has a higher proved bound. Not yet reviewed by the bbchallenge
  community.

## Credit

Found and proved in Coq by Argon, a Google Gemini model run by the repository owner in Google's Antigravity
(2026-11-09), on Jacobzheng's J19/J20 architecture (the engine, the two lists and the mod-3 schedule are
Jacobzheng's), with the expansion of Argon's J18_w2_C and a new sentinel refill. Re-checked here (check.py, clean
build, probe, literal simulation of the boot, the core renaming), with this write-up.
