# J18_w2_C: an 18-state machine at level f_(ω·2), on Jacobzheng's two-list engine

    0LB1LF_0RC1LB_0RD1RM_1LE0RN_1LF1LE_1LG0LE_1RH1RP_1RI1RH_0LJ1RA_1LK1LJ_0LL1LJ_1RM1RC_0RM0RH_1LE1RO_1RZ1RD_0LF0RQ_0LH1RR_0LF1RP

|   | 0   | 1   |                                                                      |
|---|-----|-----|----------------------------------------------------------------------|
| A | 0LB | 1LF |                                                                      |
| B | 0RC | 1LB |                                                                      |
| C | 0RD | 1RM |                                                                      |
| D | 1LE | 0RN | D> at the start of a merged block: the refill (`EX`)                 |
| E | 1LF | 1LE |                                                                      |
| F | 1LG | 0LE |                                                                      |
| G | 1RH | 1RP | <G = the inner list's left end (`CI`); G1 starts the expansion in P  |
| H | 1RI | 1RH | H> = the outer sweep on the accumulator (`CO`)                       |
| I | 0LJ | 1RA |                                                                      |
| J | 1LK | 1LJ |                                                                      |
| K | 0LL | 1LJ |                                                                      |
| L | 1RM | 1RC |                                                                      |
| M | 0RM | 0RH |                                                                      |
| N | 1LE | 1RO | refill                                                               |
| O | 1RZ | 1RD | refill; O0 is the halt                                               |
| P | 0LF | 0RQ | expansion                                                            |
| Q | 0LH | 1RR | expansion; Q0 = `0LH` is the one-pass merge for a ≡ 1 (mod 3)        |
| R | 0LF | 1RP | expansion                                                            |

The machine is written in tree normal form (start in A, states named in order of first use). Its 12-state engine
is Jacobzheng's J20 core ([`../BB20/`](../BB20/)) under other names; the expansion P, Q, R and the refill N, O
(with D) are Argon's. The Coq file names its configurations as the table's last column says.

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB18_J18_w2_C_tnf.halt`. The halt is decided by a residue mod 3, which the proof computes exactly: every level map is x ↦ x + 1 (mod 3), for every residue of x. |
| Exact score | Machine-checked formula: the halting tape holds 2j + 2 ones, where hoc_0^2(10) + 6 = 3(k + 2), a₂ = ho_k^3(hoc_0^k(10)) and a₂ + 2(k + 1) + 2 = 3j + 2 (section 1; `score_exact`). The halt O0 = `1RZ` is read on a 0, so σ = N + 1 = 2j + 3. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω·2)(2·f_ω^9(35)) < N (`sigma_lower_bound`, which also states f_(ω·2)(2·f_ω^8(f_3(17))) < N). |
| Comparisons | **In Coq** (`BB18_J18_w2_C_tnf_cmp.v`): N is above R18a's proved bound f_(ω·2)(f_ω(f_ω(f_10(2)))) (the previous BB(18) entry, `beats_R18a`) and above J16_w2's f_(ω·2)(f_15(2)) (BB(16), `beats_J16`). So BB(19) ≥ BB(18) + 1 is the best proved bound here for BB(19) as well. |
| Steps | Not computed. |

## 1. How it works

The lists, the sweep engine and the outer rounds are J20's, as in R18a ([`R18a`](1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_0LQ0LO_1LR1LP_0LQ1LN_0RO1LB_0LL1RZ.md)'s
write-up, section 1), with the inner list CI x [...] = 0^∞ <G 1^x 0 ..., the outer list
CO a [...] = 0^∞ 1 0 0 H> 1^a 0 ..., and J20's lemmas (`CI_E0`, `CI_E1`, `CI_exit`, `LV_in`, `Chain_in`, `R1`,
`LV_out`, `Chain_out`):

    inner level maps   h_0(x) = x + 4,  h_(m+1)(x) = h_m^(x+2)(2)
    outer head map     G(3c) = G₀(c),  G(3c + 1) = 3c + 5,  G(3c + 2) = G₀(c) + 2,  G₀(c) = hc_1^c(6) + 2c + 4
    outer level maps   ho_0 = G,  ho_(m+1)(a) = ho_m^(a+1)(6)
    hoc_m^0(a) = a,  hoc_m^(n+1)(a) = hoc_(m+1)^n(ho_m(a))

**Expansion** (`EXP_0`, `EXP_1`, `EXP_2`, `R0`). G1 = `1RP` sends the accumulator 1^a to P, Q, R, which rewrite it
with period 3. For a = 3c and a = 3c + 2 the result is an inner list (CI 2 [2^(c+1)], resp. CI 2 [2^(c+1), 1]) that
the engine reduces; for a = 3c + 1, Q0 = `0LH` merges the block back in one pass, so G(3c + 1) = 3c + 5 is small.
In every case G(a) ≡ a + 1 (mod 3) (`G_P1`). One G alone is not f_ω-class, but two in a row are
(`GG_dom`: 6n ≤ z gives 6 f_ω(n) ≤ G(G(z))), which is enough for the levels.

**Refill and halt.** When the outer list is used up, `OEX` merges it: CO a [1^n] →* EX (a + 2n + 2), and N, O
(with D) read the block with period 3:

| block | result |
|---|---|
| 3(k + 2) | the outer list CO 10 [2^k, 4] (`RF_0`) |
| 3(k + 1) + 1 | the outer list CO 10 [2^(k+1)] (`RF_1`) |
| 3k + 2 | O reads the blank: O0 = `1RZ`, the halt, with 2k + 2 ones (`RF_halt`, `ones_Hc`) |

## 2. The run, and why it halts

| phase | result |
|---|---|
| boot | CO 5 [] (`boot`) |
| exhaustion 1 | EX 7 = EX (3·2 + 1): refill CO 10 [2, 2] |
| two digits | `Chain_out` at outer levels 0, 1: CO a₁ [1, 1], a₁ = hoc_0^2(10) |
| exhaustion 2 | EX (a₁ + 6) = EX 3(k + 2): refill CO 10 [2^k, 4] |
| the long part | `Chain_out` on the k twos at levels 0, ..., k − 1, then the digit 4 at level k (three rounds of ho_k): CO a₂ [1^(k+1)], a₂ = ho_k^3(hoc_0^k(10)) |
| exhaustion 3 | EX (a₂ + 2(k + 1) + 2) = EX (3j + 2): the halt (`run`, `halt`) |

**The mod-3 invariant.** Every level map is x ↦ x + 1 (mod 3) (`G_P1`, `ho_P1`), so hoc_m^n(a) ≡ a + n
(`hoc_mod`). Then a₁ ≡ 10 + 2 ≡ 0 and a₁ + 6 ≡ 0 at the second exhaustion (`K_gen`), and
a₂ ≡ 10 + k + 3 ≡ k + 1, so a₂ + 2(k + 1) + 2 ≡ 3k + 5 ≡ 2 at the third (`J_gen`): the halt, for every value of k.
Nothing depends on a residue the proof does not compute, so the machine halts after exactly two refills.

**Size.** a₁ = hoc_0^2(10) ≥ 6·f_ω^9(35) (`a1_bound_35`, from `G3_dom` and `G3_base`), so k ≥ 2·f_ω^9(35), and the
last digit is reduced at level k, where ho is f_(ω+k)-class: N > f_(ω·2)(2·f_ω^9(35)) (`bound_gen`,
`sigma_lower_bound`).

## 3. Verification

[`verify_j18c/`](verify_j18c/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about 45 s, built in CI (job
`bb13-bb14`). `probe.v` re-checks the transition table entry by entry against the string above (36 checks
generated from the string) and the blank start configuration, prints the definitions the statements use, and
confirms that `halt`, `score_exact`, `sigma_lower_bound`, `beats_R18a` and `beats_J16` are closed under the global
context. The proof also passes this project's `check.py`, 2026-11-08.

`BB18_J18_w2_C_tnf.v` is Argon's file, unchanged except for line endings. `BB18_J18_w2_C_tnf_cmp.v` (the
comparisons) was written here. There is no independent simulator for this write-up; every rule cited is a lemma of
the Coq file.

## 4. Comparisons

- **In Coq**: `beats_R18a` and `beats_J16` (above). They compare proved lower bounds; R18a and J16_w2 have no proved
  upper bounds. On the exact scores (paper): R18a's k comes from G³(28) and J18_w2_C's from hoc_0^2(10) = ho_1(G(10)),
  G iterated G(10) + 1 times, so J18_w2_C is far ahead there too.
- So BB(19) ≥ BB(18) + 1 > f_(ω·2)(2·f_ω^9(35)) is the best proved bound here for BB(19); J19's f_(ω+7)^2(5) is far
  below.
- J20 (20 states, [`../BB20/`](../BB20/)) stays above: its proved f_(ω·2)(f_(ω+2)(f_(ω+2)(f_10(2)))) is above
  f_(ω·2)(2·f_ω^9(35)), since f_(ω+2)(n) is far above f_ω^9(n) (paper argument).
- Argon's 18-state sibling J18_w2_A (proved f_(ω·2)(2·f_5(2)) < N) and the 19-state J19_w2 (f_(ω·2)(2·f_ω(f_2(15))))
  are below R18a's proved bound and are not listed.
- Not yet reviewed by the bbchallenge community.

## Credit

Found and proved in Coq by Argon, a Google Gemini model run by the repository owner in Google's Antigravity
(2026-11-08), by compressing Jacobzheng's J20 by two states (a three-state expansion whose level maps are +1 mod 3
in every residue, and a three-state refill): the engine, the two lists and the mod-3 schedule are Jacobzheng's.
Re-checked here (check.py, clean build, probe), with the comparison file and this write-up.
