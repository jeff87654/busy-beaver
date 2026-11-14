# R18c: an 18-state machine at level f_(ω·2), in the R18a family

    1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_1LQ0LO_0LR1LP_1LQ1LN_1LF0LM_0RC1RZ

The same machine in tree normal form (states renamed in order of first use; the Coq file proves the halt and the
bound for this table too, `halt_tnf`, `sigma_lower_bound_tnf`):
`1LB0LP_1RC1RJ_1RD1RC_0LE1RO_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RB1RH_0LK1RJ_1LN0LL_0LR1LM_1LN1LK_1LC0LJ_0LQ1LA_1LA1LP_0RI1LQ_0RO1RZ`.

|   | 0   | 1   |                                                                              |
|---|-----|-----|------------------------------------------------------------------------------|
| A | 1LH | 0LG | engine: A1 erases the first cell of a digit ≥ 2 (J20's)                      |
| B | 0LI | 1RC | engine: B0 = end of the list, B1 = next digit (J20's)                        |
| C | 0LD | 1LA | engine: C0 = digit 1 (pass), C1 = digit ≥ 2 (J20's)                          |
| D | 0RE | 1LD | engine: walk left over a passed digit (J20's)                                |
| E | 0RH | 1RL | E1 splits a cell off the head (engine); E> at the merged block (`EX`): E0 starts the refill |
| F | 1RB | 1RF | engine: the sweep state, walks right over the accumulator (J20's)            |
| G | 1LA | 1LG | engine: walk back (J20's)                                                    |
| H | 1RF | 1RM | left end (`CI`: <H): H0 = inner list (new sweep), H1 = marker: expansion or refill |
| I | 1LJ | 1LI | end of a list: merge it into one block (J20's)                               |
| J | 0LK | 1LI | end of a list (J20's)                                                        |
| K | 1RL | 1RE | K0 writes the marker (outer boundary), K1 = outer list exhausted (J20's)     |
| L | 0RL | 0RF | start of a sweep (J20's)                                                     |
| M | 0LN | 1RM | walk right over the block (expansion and refill)                             |
| N | **1LQ** | 0LO | rewrite the block from the right, period 3 (`triNOP`); N0 exits into Q   |
| O | **0LR** | 1LP | rewriter; O0 exits into R                                                |
| P | **1LQ** | 1LN | rewriter; P0 exits into Q                                                |
| Q | **1LF** | **0LM** | exit: Q0 = blank (expansion, back to F), Q1 = marker: erases it (refill)         |
| R | **0RC** | 1RZ | exit: R0 = blank (expansion, back to the engine), R1 = marker: the halt  |

R18c is R18a ([`R18a`](1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_0LQ0LO_1LR1LP_0LQ1LN_0RO1LB_0LL1RZ.md),
this project's 18-state compression of Jacobzheng's J20, with the six entries in bold changed: the rewriter exits
N0, O0, P0 and the two dispatch states Q, R. Rows A–M are J20's 12-state core with E0 changed, as in R18a. The
changed exits give a different expansion head map G (section 1) and a longer refill: a merged block of length
3(k + 2) becomes the outer list [3, 2^(k+1)], and 3(k + 1) + 2 becomes [2^(k+2)]. The first refill (from the boot)
is [2, 2] instead of R18a's [1, 1, 2], so the second refill happens after an f_(ω+1)-sized first round.

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB18_R18c.halt` (and `halt_tnf` for the table above). The halt is decided by a residue mod 3, which the proof computes exactly: every level map is x ↦ x + 1 (mod 3), for every residue of x. |
| Exact score | Machine-checked formula: the halting tape holds 2(j + 1) + 1 ones, where a₁ = hoc_0^2(7), a₁ + 6 = 3(k₁ + 2), b₀ = G(G(7)), a₂ = hoc_1^(k₁+1)(b₀) and a₂ + 2(k₁ + 2) + 2 = 3(j + 1) + 1 (section 1; `score_exact`). The halt R1 = `1RZ` is read on a 1 and writes 1, so σ = N = 2j + 3. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω·2)(f_(ω+1)(f_4(2))) < N = σ (`sigma_lower_bound`, which also states f_(ω·2)(2·f_ω^9(35)) < N). |
| Comparisons | **In Coq**: the second bound is exactly the proved bound of J18_w2_C (the previous BB(18) entry), so N is above it. Comparison with J18_w2_C's exact score: on paper only (section 4). |
| Steps | Not computed. |

## 1. How it works

The configurations (Coq names) are the inner list CI x [...] = 0^∞ <H 1^x 0 [...], the outer list
CO a [...] = 0^∞ 1 0 0 F> 1^a 0 [...] and the merged block EX B = 0^∞ 1 E> 0 1^B 0^∞. The inner rules are J20's
(`CI_E0`, `CI_E1`, `CI_exit`, `LV_in`, `Chain_in`), and

    inner level maps   h_0(x) = x + 4,  h_(m+1)(x) = h_m^(x+2)(2),  hc_m^0(x) = x,  hc_m^(n+1)(x) = hc_(m+1)^n(h_m(x))
    outer head map     G(0) = 4,  G(3(c + 1)) = hc_1^c(6) + 2c + 4,
                       G(3c + 1) = hc_1^(c+1)(7) + 2(c + 1) + 4,  G(3c + 2) = hc_1^(c+1)(11) + 2(c + 1) + 4
    outer level maps   ho_0 = G,  ho_(m+1)(a) = ho_m^(a+1)(15)                      (level m is f_(ω+m)-class)
    hoc_m^0(a) = a,  hoc_m^(n+1)(a) = hoc_(m+1)^n(ho_m(a))

    R0   CO a [e+2, r]           →*  CO G(a) [e+1, r]          (every a; `EXP_zero`, `EXP_0s`, `EXP_1`, `EXP_2`, `R0`)
    R1   CO a [1^(p+1), e+2, r]  →*  CO 15 [1^p, a+2, e+1, r]  (`R1`)
    OEX  CO a [1^n]              →*  EX (a + 2n + 2)           (the outer list used up, `OEX`)

In both an expansion and a refill, M walks right over the block and N, O, P rewrite it from the right with period 3
(`triNOP`). At the exit, Q and R read the cell left of the block: the blank in an expansion (back to the engine),
the marker in a refill, where E0 = `0RH` has kept it one cell further left:

| block | result |
|---|---|
| 3j + 1 | R reads the marker: R1 = `1RZ`, the halt, with 2j + 1 ones (`RF_halt`, `ones_Hc`) |
| 3(k + 1) + 2 | Q1 = `0LM` erases the marker: the outer list CO 7 [2^(k+2)] (`RF_2`) |
| 3(k + 2) | the outer list CO 7 [3, 2^(k+1)] (`RF_0`) |

## 2. The run, and why it halts

| phase | result |
|---|---|
| boot | CO 3 [] (`boot1`), EX 5 = EX (3·1 + 2): refill CO 7 [2, 2] (`boot`; step 83 by literal simulation here) |
| round 1 | `Chain_out` on the two twos at outer levels 0, 1: CO a₁ [1, 1], a₁ = hoc_0^2(7) = ho_1(G(7)) |
| exhaustion 1 | EX (a₁ + 6) = EX 3(k₁ + 2): refill CO 7 [3, 2^(k₁+1)] |
| round 2 | the digit 3 at level 0 (two R0 rounds): b₀ = G(G(7)); then `Chain_out` on the k₁ + 1 twos at levels 1, ..., k₁ + 1: CO a₂ [1^(k₁+2)], a₂ = hoc_1^(k₁+1)(b₀) |
| exhaustion 2 | EX (a₂ + 2(k₁ + 2) + 2) = EX (3(j + 1) + 1): the halt (`run_gen`, `run`, `halt`) |

**The mod-3 invariant.** Every level map is x ↦ x + 1 (mod 3) (`G_P1`, `ho_P1`; R1 restarts at 15 ≡ 0), so
hoc_m^n(a) ≡ a + n (`hoc_P1`). Then a₁ ≡ 7 + 2 ≡ 0, so the first exhaustion is in the class 3(k + 2); b₀ ≡ 0 and
a₂ ≡ k₁ + 1, so a₂ + 2(k₁ + 2) + 2 ≡ 3k₁ + 7 ≡ 1 at the second: the halt, for every value of k₁. Nothing depends on a
residue the proof does not compute, so the machine halts after exactly two refills.

**Size.** G(7) = hc_1^3(7) + 10 ≥ 6·f_4(2) (`G7_bound`), and a₁ = ho_1(G(7)) ≥ 6·f_(ω+1)(f_4(2)) (`a1_bound`,
`ho_dom`), so k₁ is of that order, and the last two of round 2 is reduced at outer level k₁ + 1, where ho is
f_(ω+k₁+1)-class: N > f_(ω·2)(f_(ω+1)(f_4(2))) (`hoc1_dom_w2`, `bound_gen`). Since
2·f_ω^9(35) ≤ f_(ω+1)(f_4(2)) (`beat_J18_inner`), the second form follows.

## 3. Verification

[`verify_r18c/`](verify_r18c/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about a minute, built in CI
(job `bb13-bb14`). `probe.v` re-checks both transition tables (`tm` against the string above, `tm_tnf` against the
tree-normal-form string; 72 checks generated from the strings) and the blank start configuration, prints the
definitions the statements use, and confirms that `halt`, `score_exact`, `sigma_lower_bound`, `halt_tnf` and
`sigma_lower_bound_tnf` are closed under the global context. The proof also passes this project's `check.py`
(2026-11-13), and literal simulation here reproduces the boot lemmas (CO 3 [] at step 13, CO 7 [2, 2] at step 83)
and agrees with the renamed table for 2,000,000 steps.

`BB18_R18c.v` is Argon's file, unchanged except for the first line `(* machine: ... *)`, added here (the string
above, which is the file's transition table `tm`), which `check.py` reads. There is no
independent simulator for this write-up; every rule cited is a lemma of the Coq file.

## 4. Comparisons

- **In Coq**: f_(ω·2)(2·f_ω^9(35)) < N, and f_(ω·2)(2·f_ω^9(35)) is J18_w2_C's proved bound
  (`BB18_J18_w2_C_tnf.sigma_lower_bound`, the same definitions). J18_w2_C has no proved upper bound, so that
  compares proved lower bounds.
- **On paper**: J18_w2_C's second-round level k comes from hoc_0^2(10) = ho_1(G(10)), with its G(10) = 14 (the
  linear branch of its head map), an f_ω^15-sized number; here k₁ comes from ho_1(G(7)) with G(7) ≥ 6·f_4(2), an
  f_(ω+1)(f_4(2))-sized number. So J18_w2_C's exact score is far below this machine's N.
- R18c is also above BB(17) + 1 (J17_champ, f_(ω·2)(f_ω^3(f_14(2))) < N there) on paper: f_ω^3(f_14(2)) is far below
  f_(ω+1)(f_4(2)).
- The 19-state J19_sq ([`../BB19/`](../BB19/)) has a higher proved bound. Not yet reviewed by the bbchallenge
  community.

## Credit

The machine is this project's: found on 2026-11-07 by the search that produced R18a (agent jz-compress, a search for
compressions of Jacobzheng's J20; R18c was one of the variants with a larger first refill, then without a proof).
Its Coq proof, `BB18_R18c.v`, was written by Argon, a Google Gemini model run by the repository owner in Google's
Antigravity (2026-11-09). The engine, the two lists and the mod-3 schedule are Jacobzheng's. Re-checked here
(check.py, clean build, probe, literal simulation of the boot and of the renaming), with this write-up.
