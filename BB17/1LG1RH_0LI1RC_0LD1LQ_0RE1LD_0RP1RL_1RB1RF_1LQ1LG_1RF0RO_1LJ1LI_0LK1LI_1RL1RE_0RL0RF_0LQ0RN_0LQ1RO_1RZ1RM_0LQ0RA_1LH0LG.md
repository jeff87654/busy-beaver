# J17_champ: a 17-state machine at level f_(ω·2), on Jacobzheng's two-list engine

    1LG1RH_0LI1RC_0LD1LQ_0RE1LD_0RP1RL_1RB1RF_1LQ1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LQ0RN_0LQ1RO_1RZ1RM_0LQ0RA_1LH0LG

The same machine in tree normal form (states renamed in order of first use; the Coq file proves the halt and the
bound for this table too, `halt_tnf`, `sigma_lower_bound_tnf`):
`1LB1RD_1LC1LB_1LD0LB_1RE0RM_1RF1RE_0LG1RP_1LH1LG_0LI1LG_1RJ1RK_0RJ0RE_0RL1RJ_0LC0RA_1RZ1RN_0LC0RO_0LC1RM_0LQ1LC_0RK1LQ`.

|   | 0   | 1   |                                                                                  |
|---|-----|-----|----------------------------------------------------------------------------------|
| A | 1LG | 1RH | start; refill (entered only from P1)                                             |
| B | 0LI | 1RC | engine                                                                           |
| C | 0LD | 1LQ | engine                                                                           |
| D | 0RE | 1LD | engine                                                                           |
| E | **0RP** | 1RL | E> at the merged block (`EX`): E0 = `0RP` starts the refill                  |
| F | 1RB | 1RF | F> = the sweep over a list (`SW`, `CO`)                                          |
| G | 1LQ | 1LG | engine                                                                           |
| H | 1RF | 0RO | <H = the inner list's left end (`CI`)                                            |
| I | 1LJ | 1LI | engine                                                                           |
| J | 0LK | 1LI | engine                                                                           |
| K | 1RL | 1RE | engine                                                                           |
| L | 0RL | 0RF | engine                                                                           |
| M | 0LQ | 0RN | period-3 rewriter (with N, O: `triOMN`)                                          |
| N | 0LQ | 1RO | period-3 rewriter                                                                |
| O | **1RZ** | 1RM | period-3 rewriter; O0 is the halt                                            |
| P | 0LQ | **0RA** | refill (entered only from E0)                                                |
| Q | 1LH | 0LG | <Q: the sweep stops at a digit ≥ 2 here (`SW_E`) and the expansion starts        |

The machine is built on J16_w2 ([`../BB16/`](../BB16/)): rows B–O and Q are J16_w2's rows under the renaming
A → G, G → Q (Jacobzheng's J20 sweep engine and the period-3 rewriter M, N, O), except E0, H1 and N0. J16_w2's refill
exit P is replaced by a two-state refill A, P, entered only through E0 = `0RP` (and A also at the start). The refill
turns a merged block of length ≡ 1 (mod 3) into a two-part outer list [1, 2^(k+1)], and the run reaches its second
refill much later than J16_w2's: after five applications of the outer head map G instead of two.

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB17_J17_w2_champ.halt` (and `halt_tnf` for the table above). The halt is decided by residues mod 3 and mod 9, which the proof computes exactly. |
| Exact score | Machine-checked formula: the halting tape holds 2j + 4 ones, where G^5(4) + 6 = 9(q₁ + 1) + 1, k₁ = 3q₁ + 1, a₂ = hoc_1^(k₁+1)(4) and a₂ + 6(q₁ + 1) + 2 = 3(j + 2) (section 1; `score_exact`). The halt O0 = `1RZ` is read on a 0, so σ = N + 1 = 2j + 5. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω·2)(f_ω^3(f_14(2))) < N and f_(ω·2)(f_15(2)) < N (`sigma_lower_bound`). |
| Comparisons | **In Coq**, against the exact score: N > N(J16_w2) + 1, i.e. σ(J17_champ) = N + 1 > σ(J16_w2) + 1, so this machine beats BB(16) + 1 (`BB17_J17_cmp.beats_J16_exact`, `beats_J16_score`; section 4). The second bound is also J16_w2's proved lower bound. |
| Steps | Not computed. |

## 1. How it works

The configurations (Coq names) are the inner list CI x [...] = 0^∞ <H 1^x 0 [...], the outer list
CO a [...] = 0^∞ 1 0 0 F> 1^a 0 [...] (a digit d is written 1^d 0) and the merged block EX B = 0^∞ 1 E> 0 1^B 0^∞.
The inner rules are J20's (`CI_E0`, `CI_E1`, `CI_exit`, `LV_in`, `Chain_in`), and

    inner level maps   h_0(x) = x + 4,  h_(m+1)(x) = h_m^(x+2)(2),  hc_m^0(x) = x,  hc_m^(n+1)(x) = hc_(m+1)^n(h_m(x))
    outer head map     G(3k + 1) = hc_0^(k+1)(2) + 2(k + 1) + 2                      (f_ω-class)
    outer level maps   ho_0 = G,  ho_(m+1)(a) = ho_m^(a+1)(4)                       (level m is f_(ω+m)-class)
    hoc_m^0(a) = a,  hoc_m^(n+1)(a) = hoc_(m+1)^n(ho_m(a))

    R0   CO a [e+2, r]           →*  CO G(a) [e+1, r]          (a ≡ 1 mod 3; the expansion, `R0`)
    R1   CO a [1^(p+1), e+2, r]  →*  CO 4 [1^p, a+2, e+1, r]   (`R1`)
    OEX  CO a [1^n]              →*  EX (a + 2n + 2)           (the outer list used up, `OEX`)

The refill reads the merged block with the rewriter M, N, O (period 3) and A, P:

| block | result |
|---|---|
| 3(k + 2) + 1 | the outer list CO 4 [1, 2^(k+1)] (`RF_1`) |
| 3(j + 2) | O reads the blank: O0 = `1RZ`, the halt, with 2j + 4 ones (`RF_halt`, `ones_Hc`) |

The outer accumulator always stays ≡ 1 (mod 3): G(3k + 1) ≡ 1 (`Gk_mod3`), R1 and the refill restart at 4, and so
every ho_m and hoc_m keeps the class (`ho_mod3`, `hoc_mod3`).

## 2. The run, and why it halts

| phase | result |
|---|---|
| boot | CO 5 [] (`boot1`, 19 steps), EX 7, refill CO 4 [1, 2], then R1: CO 4 [6, 1] (`boot`; step 135 by literal simulation here) |
| round 1 | the digit 6 at outer level 0: five R0 rounds, CO a₁ [1, 1] with a₁ = G^5(4), G(4) = 40 (`G4_eq`) |
| exhaustion 1 | EX (a₁ + 6), a₁ + 6 = 9(q₁ + 1) + 1 = 3(k₁ + 2) + 1 with k₁ = 3q₁ + 1: refill CO 4 [1, 2^(k₁+1)] |
| round 2 | `Chain_out` on the k₁ + 1 twos at outer levels 1, ..., k₁ + 1: CO a₂ [1^(k₁+2)], a₂ = hoc_1^(k₁+1)(4) |
| exhaustion 2 | EX (a₂ + 2(k₁ + 2) + 2) = EX 3(j + 2): the halt (`run_gen`, `run`, `halt`) |

**Why the second block has the halting residue.** a₂ ≡ 1 (mod 3), so a₂ + 2(k₁ + 2) + 2 ≡ 2k₁ + 1 (mod 3), which is 0
exactly when k₁ ≡ 1 (mod 3), that is, when G^5(4) ≡ 4 (mod 9). The proof computes this exactly (`G5_4_mod9`): it
shows that the inner level maps act on residues mod 486 with a table that is stable from level 5 on (`stab_t5`,
`h5_rep486`), that hc_0^n(2) mod 486 is periodic in n with period 3 (`hc_period3_486`), and follows the five G steps
down through the moduli 243, 81, 27, 9 (`J_gen` then gives the halting residue).

**Size.** G(40) ≥ 6·f_14(2) (`G40_bound`); each further G is at least one f_ω step (`G_dom`), so
a₁ = G^4(40) ≥ 6·f_ω^3(f_14(2)) (`G5_4_bound`). The last digit of round 2 is reduced at outer level k₁ + 1, where ho
is f_(ω+k₁+1)-class: N > f_(ω·2)(f_ω^3(f_14(2))) (`hoc1_dom_w2`, `bound_gen`), and f_15(2) ≤ f_ω^3(f_14(2))
(`beat_J16_inner`) gives the second form.

## 3. Verification

[`verify_j17/`](verify_j17/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about a minute, built in CI
(job `bb13-bb14`). `probe.v` re-checks both transition tables (`tm` against the string above, `tm_tnf` against the
tree-normal-form string; 68 checks generated from the strings) and the blank start configuration, prints the
definitions the statements use, and confirms that `halt`, `score_exact`, `sigma_lower_bound`, `halt_tnf` and
`sigma_lower_bound_tnf` are closed under the global context. The proof also passes this project's `check.py`
(2026-11-13), and literal simulation here reproduces the boot lemmas (CO 5 [] at step 19, CO 4 [6, 1] at step 135,
all 17 states used) and agrees with the renamed table for 2,000,000 steps.

`BB17_J17_w2_champ.v` is Argon's file, unchanged except for the first line `(* machine: ... *)`, added here (the string
above, which is the file's transition table `tm`), which `check.py` reads. There is no
independent simulator for this write-up; every rule cited is a lemma of the Coq file.

## 4. Comparisons

- **In Coq**: f_(ω·2)(f_15(2)) < N, and f_(ω·2)(f_15(2)) is J16_w2's proved bound (`BB16_J16_w2.sigma_lower_bound`,
  the same definitions). So J17_champ's proved bound is above BB(16) + 1's. J16_w2 has no proved upper bound, so
  that compares proved lower bounds.
- **In Coq, against the exact score** (`BB17_J17_cmp.v`, written here): `beats_J16_exact` states that for the k₁, q₁, a₂, j
  of J16_w2's `score_exact` (its count N(J16_w2) = 2j + 4), 2j + 4 + 1 < N; `beats_J16_score` combines this with J16_w2's
  halting tape. The proof bounds J16_w2's count from above, N(J16_w2) + 1 ≤ f_(ω·2)(k₁ + G(44) + 20), and
  k₁ + G(44) + 20 ≤ f_ω^3(f_14(2)). The upper bounds come from `JZ_UB.v` (written here): for any maps satisfying the engine's equations, h_m(y) + 4 ≤ f_(m+1)(y + 4), hc_m^n(x) + 4 ≤ f_ω(m + n + x + 5), ho_m(a) + 20 ≤ f_(ω+m)(a + 20) and hoc_m^n(a) + 20 ≤ f_(ω+m+n+1)(n + a + 20), given G(a) + 20 ≤ f_ω(a + 20), which the comparison file proves for the older machine's own head map.
- **Why**: J16_w2 runs the same kind of second round, but its level k₁ comes from G(G(5)) = G(44), an
  f_15(2)-sized number, while here it comes from G^5(4), f_ω^3(f_14(2))-sized. So J16_w2's exact score is below
  f_(ω·2)(f_ω(f_15(2))), far below this machine's N.
- M17_B (the previous BB(17) entry) was already below J16_w2's proved bound in Coq (`beats_M17_B` in
  [`../BB16/verify_j16/`](../BB16/verify_j16/)), and J17_champ's proved bound contains J16_w2's.
- Argon's earlier 17-state J17_w2 (proved f_(ω·2)(f_13(2)) < N) is below this.
- The 18-state R18c ([`../BB18/`](../BB18/)) has a higher proved bound. Not yet reviewed by the bbchallenge community.

## Credit

Found and proved in Coq by Argon, a Google Gemini model run by the repository owner in Google's Antigravity
(2026-11-09), on Jacobzheng's J19/J20 architecture (the engine, the two lists and the mod-3 schedule are
Jacobzheng's), as a 17-state extension of Argon's J16_w2. Re-checked here (check.py, clean build, probe, literal
simulation of the boot and of the renaming), with this write-up.
