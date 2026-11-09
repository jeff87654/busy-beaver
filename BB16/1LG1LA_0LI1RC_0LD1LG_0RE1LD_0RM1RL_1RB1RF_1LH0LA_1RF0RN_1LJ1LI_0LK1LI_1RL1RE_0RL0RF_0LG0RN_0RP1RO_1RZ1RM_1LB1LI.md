# J16_w2: a 16-state machine at level f_(ω·2), on Jacobzheng's two-list engine

    1LG1LA_0LI1RC_0LD1LG_0RE1LD_0RM1RL_1RB1RF_1LH0LA_1RF0RN_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LG0RN_0RP1RO_1RZ1RM_1LB1LI

The same machine in tree normal form (states renamed in order of first use; checked here by comparing the two
tables under the renaming, not in Coq):
`1LB1LA_1LC0LA_1RD0RL_1RE1RD_0LF1RO_1LG1LF_0LH1LF_1RI1RJ_0RI0RD_0RK1RI_0LB0RL_0RN1RM_1RZ1RK_1LE1LF_0LP1LB_0RJ1LP`.
The Coq proof is about the string above.

|   | 0   | 1   |                                                                              |
|---|-----|-----|------------------------------------------------------------------------------|
| A | 1LG | 1LA | engine: J20's G (walk back), renamed so that the start state is A             |
| B | 0LI | 1RC | engine (J20's)                                                               |
| C | 0LD | 1LG | engine (J20's)                                                               |
| D | 0RE | 1LD | engine (J20's)                                                               |
| E | **0RM** | 1RL | E0: outer list exhausted, start the refill                               |
| F | 1RB | 1RF | engine: the sweep state (J20's)                                              |
| G | 1LH | 0LA | engine: J20's A                                                              |
| H | 1RF | **0RN** | H0 = inner list (new sweep); H1 = marker: expansion, into N              |
| I | 1LJ | 1LI | engine (J20's)                                                               |
| J | 0LK | 1LI | engine (J20's)                                                               |
| K | 1RL | 1RE | engine (J20's)                                                               |
| L | 0RL | 0RF | engine (J20's)                                                               |
| M | 0LG | 0RN | period-3 rewriter                                                            |
| N | **0RP** | 1RO | period-3 rewriter; N0 peeks right into P                                 |
| O | **1RZ** | 1RM | period-3 rewriter; O0 is the halt                                       |
| P | 1LB | 1LI | new: the refill's exit                                                       |

Rows A–L are the 12-state core of Jacobzheng's J20 ([`../BB20/`](../BB20/)), with A and G renamed and E0, H1
changed. M, N, O are the period-3 rewriter of J15_fw13 ([`../BB15/`](../BB15/)), and the extra state P turns the
refill of a block of length ≡ 0 (mod 3) into a three-digit outer list, which is what lifts the level from
f_(ω+13) to f_(ω·2).

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB16_J16_w2.halt`. The halt is decided by residues mod 3 and mod 9, which the proof computes exactly. |
| Exact score | Machine-checked formula: the halting tape holds 2j + 4 ones, where G(44) + 4 = 3(k₁ + 3), k₁ = 3q₁ + 2, a₂ = hoc_1^(k₁)(G(44)) and a₂ + 2(k₁ + 1) + 2 = 3(j + 1) + 1 (section 1; `score_exact`). The halt O0 = `1RZ` is read on a 0, so σ = N + 1 = 2j + 5. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω·2)(f_15(2)) < N (`sigma_lower_bound`, which also states f_(ω·2)(f_13(2)) < N). |
| Comparisons | **In Coq** (`BB16_J16_w2_cmp.v`): N is above the proved bounds of M16_C (the previous BB(16) entry, `beats_M16_C`), M17_B (BB(17), `beats_M17_B`), J15_fw13 (BB(15), `beats_J15`) and M14_31 (BB(14), `beats_M14_31`). So J16_w2 also gives the best proved bound here for BB(17): BB(17) ≥ BB(16) + 1. The bbchallenge wiki's Champions table has no BB(16) row (checked 2026-11-08). |
| Steps | Not computed. |

## 1. How it works

The lists, the engine and the outer rounds are J20's, as in J15_fw13 (read [its write-up](../BB15/) first): the
inner list CI, the outer list CO and the lemmas `CI_E0`, `CI_E1`, `CI_exit`, `R1`, `LV_in`, `Chain_in`, `LV_out`,
`Chain_out`. Here the outer accumulator lives in the class a ≡ 2 (mod 3), and

    inner level maps   h_0(x) = x + 4,  h_(m+1)(x) = h_m^(x+2)(2)
    outer head map     G(a) = hc_0^(k+1)(3) + 2(k + 1) + 2,  k = a div 3           (f_ω-class)
    outer level maps   ho_0 = G,  ho_(m+1)(a) = ho_m^(a+1)(5)                      (level m is f_(ω+m)-class)
    hoc_m^0(a) = a,  hoc_m^(n+1)(a) = hoc_(m+1)^n(ho_m(a))

    R0   CO a [e+2, r]           →*  CO G(a) [e+1, r]          (a ≡ 2 mod 3; H1 = `0RN` starts the expansion)
    R1   CO a [1^(p+1), e+2, r]  →*  CO 5 [1^p, a+2, e+1, r]
    OEX  CO a [1^n]              →*  EX (a + 2n + 2)           (the merged block, E0 = `0RM`)

The refill reads the merged block with M, N, O (period 3), and N0 = `0RP` looks one cell to the right:

| block | result |
|---|---|
| 3(k + 3) | P sends the head back into the engine: the outer list CO 5 [3, 2^k] (`RF_0`) |
| 3(j + 1) + 1 | O reads the blank: O0 = `1RZ`, the halt, with 2j + 4 ones (`RF_halt`, `ones_Hc`) |

Argon's report notes that an earlier draft (N0 = `0RP`, P = `1LM0LG` on a different core) erased the accumulator in
the R1 round with p = 1 and never halted the intended way; the machine here is the corrected one, and the Coq proof
is about it.

## 2. The run, and why it halts

| phase | result |
|---|---|
| boot | CO 5 [1] after 80 steps (`boot1`); EX 9 = EX 3·3; refill CO 5 [3] after 172 steps (`boot`) |
| round 1 | the digit 3 at level 0: two R0 rounds, G(5) = 44 (`G5_eq`), then G(44): CO (G(44)) [1] |
| exhaustion | EX (G(44) + 4) = EX 3(k₁ + 3): refill CO 5 [3, 2^(k₁)] |
| round 2 | the digit 3 again gives G(44), then `Chain_out` on the k₁ twos at outer levels 1, ..., k₁: CO a₂ [1^(k₁+1)], a₂ = hoc_1^(k₁)(G(44)) |
| exhaustion | EX (a₂ + 2(k₁ + 1) + 2) = EX (3(j + 1) + 1): the halt (`run`, `halt`) |

**Why the last block has the halting residue.** Every map keeps a ≡ 2 (mod 3) (`G_mod3`, `ho_mod3`, `hoc_mod3`),
so the last block is ≡ 2 + 2(k₁ + 1) + 2 (mod 3), which is the halting class 1 exactly when k₁ ≡ 2 (mod 3). That
depends on G(44) mod 9: the proof shows that the inner level maps h_m (m ≥ 4) act on residues mod 18 with period 3
(`h_Cyc18`), computes hc_0^15(3) ≡ 6 (mod 18) (`hc15_18`) and gets G(44) + 4 = 3(k₁ + 3) with k₁ = 3q₁ + 2
(`G44_mod9`).

**Size.** G(44) ≥ 8·f_15(2) (`G44_bound`), so k₁ is at least of that order, and the chain's last step is at level
k₁, where ho is f_(ω+k₁)-class: N > f_(ω·2)(f_15(2)) (`bound_gen`, `sigma_lower_bound`).

## 3. Verification

[`verify_j16/`](verify_j16/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about 40 s, built in CI (job
`bb13-bb14`). `probe.v` re-checks the transition table entry by entry against the string above (32 checks
generated from the string) and the blank start configuration, prints the definitions the statements use, and
confirms that `halt`, `score_exact`, `sigma_lower_bound`, `beats_J15`, `beats_M14_31`, `beats_M16_C` and
`beats_M17_B` are closed under the global context. The proof also passes this project's `check.py`, 2026-11-08.

`BB16_J16_w2.v` is Argon's file with two changes: a byte-order mark and Windows line endings removed, and the
first line `(* machine: ... *)` added (the string above, which is the file's transition table), which `check.py`
reads. `BB16_J16_w2_cmp.v` (the comparisons) was written here. There is no independent simulator for this
write-up; every rule cited is a lemma of the Coq file.

## 4. Comparisons

- **In Coq**: `beats_M16_C` (f_(ω+2)(f_(ω+1)^114(f_(ω+2)^3(f_(ω+3)(9)))), M16_C's proved bound), `beats_M17_B`
  (f_(ω+2)^116(f_(ω+3)^3(9)), M17_B's), `beats_J15` (f_(ω+13)(20)) and `beats_M14_31`
  (f_(ω+2)^30(f_(ω+1)(f_(ω+1)(3)))). These compare proved lower bounds; none of those machines has a proved upper
  bound.
- The 17-state J17_w2 (Argon, same family, proved f_(ω·2)(f_13(2)) < N) is below J16_w2's proved bound, so it is not
  listed; BB(17) ≥ BB(16) + 1 is the better proved bound.
- The 18-state J18_w2_C ([`../BB18/`](../BB18/)) is above J16_w2 in Coq.
- Not yet reviewed by the bbchallenge community.

## Credit

Found and proved in Coq by Argon, a Google Gemini model run by the repository owner in Google's Antigravity
(2026-11-08), by compressing Jacobzheng's J19/J20 architecture: the engine, the two lists and the mod-3 schedule
are Jacobzheng's. Re-checked here (check.py, clean build, probe, the tree-normal-form renaming), with the comparison
file and this write-up.
