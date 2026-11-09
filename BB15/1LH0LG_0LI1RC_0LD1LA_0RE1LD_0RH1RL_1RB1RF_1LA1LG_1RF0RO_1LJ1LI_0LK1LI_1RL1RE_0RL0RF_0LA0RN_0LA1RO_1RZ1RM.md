# J15_fw13: a 15-state machine at level f_(ω+13), on Jacobzheng's two-list engine

    1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LA0RN_0LA1RO_1RZ1RM

|   | 0   | 1   |                                                                                 |
|---|-----|-----|---------------------------------------------------------------------------------|
| A | 1LH | 0LG | engine (J20's)                                                                  |
| B | 0LI | 1RC | engine (J20's)                                                                  |
| C | 0LD | 1LA | engine (J20's)                                                                  |
| D | 0RE | 1LD | engine (J20's)                                                                  |
| E | **0RH** | 1RL | E0: outer list exhausted, start the refill (as in R18a)                     |
| F | 1RB | 1RF | engine: the sweep state (J20's)                                                 |
| G | 1LA | 1LG | engine (J20's)                                                                  |
| H | 1RF | **0RO** | H0 = inner list (new sweep); H1 = marker: expansion or refill, now into O   |
| I | 1LJ | 1LI | engine (J20's)                                                                  |
| J | 0LK | 1LI | engine (J20's)                                                                  |
| K | 1RL | 1RE | engine (J20's)                                                                  |
| L | 0RL | 0RF | engine (J20's)                                                                  |
| M | 0LA | 0RN | period-3 rewriter                                                               |
| N | 0LA | 1RO | period-3 rewriter                                                               |
| O | **1RZ** | 1RM | period-3 rewriter; O0 is the halt                                          |

Rows A–L are the 12-state core of Jacobzheng's J20 ([`../BB20/`](../BB20/)) and of R18a ([`../BB18/`](../BB18/)),
with H1 changed; E0 = `0RH` is R18a's. J20's expansion states and its refill states are replaced by three states
M, N, O that do both jobs, scanning left to right.

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB15_J15_fw13.halt`. The halt is decided by a residue mod 3, which the proof computes exactly: every level map is x ↦ x + 1 (mod 3) on the class a ≡ 1. |
| Exact score | Machine-checked formula: the halting tape holds 2j + 1 ones, where hoc_0^14(4) + 29 = 3j (section 1; `score_exact`). The halt O0 = `1RZ` is read on a 0, so σ = N + 1 = 2j + 2. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+13)(20) < N (`sigma_lower_bound`). |
| Comparisons | **In Coq** (`BB15_J15_fw13_cmp.v`, `beats_M14_31`): N is above M14_31's proved BB(14) bound f_(ω+2)^30(f_(ω+1)(f_(ω+1)(3))). The bbchallenge wiki's Champions table has no BB(15) row (checked 2026-11-08). |
| Steps | Not computed. |

## 1. How it works

As in J20 and R18a, lists are blocks of 1s separated by single 0s, and the tape holds an **inner** list at the left
end and an **outer** list; one sweep engine runs both. The Coq file's configurations (J20's):

    inner:  CI x [d2, ..., dn] R  =  0^∞ <H 1^x 0 1^d2 0 ... 0 1^dn 0 0 R
    outer:  CO a [o1, ..., om]    =  0^∞ 1 0 0 F> 1^a 0 1^o1 0 ... 0 1^om 0^∞
    refill: RQ N                  =  0^∞ 1 0 0 O> 1^N 0^∞

The inner list and the outer rounds are J20's (`CI_E0`, `CI_E1`, `CI_exit`, `R1`, `LV_in`, `Chain_in`, `LV_out`,
`Chain_out`), with

    inner level maps   h_0(x) = x + 4,  h_(m+1)(x) = h_m^(x+2)(2)
    outer head map     G(3c + 1) = hc_0^(c+1)(2) + 2(c + 1) + 2                (f_ω-class)
    outer level maps   ho_0 = G,  ho_(m+1)(a) = ho_m^(a+1)(4)                  (level m is f_(ω+m)-class)
    hoc_m^0(a) = a,  hoc_m^(n+1)(a) = hoc_(m+1)^n(ho_m(a))

**Expansion** (an outer R0 round, `R0`): H1 = `0RO` enters O, and M, N, O rewrite the accumulator 1^(3c+1) left to
right, three cells at a time (`triOMN`, `triGA`), into the inner list CI 2 [2^(c+1)], which the engine reduces to
G(3c + 1) (`EXP_c`, `R0_c`). R0 needs a ≡ 1 (mod 3), and every map keeps that class (`G_mod3_1`, `ho_mod3_1`,
`hoc_mod3_1`).

**Refill and halt**: when the outer list is used up, `OEX` merges it: CO a [1^n] →* RQ (a + 2n + 1). Then M, N, O
scan the block with period 3:

| N | result |
|---|---|
| 3k + 1 | the outer list CO 4 [2^k] (`RF_1`) |
| 3j | O reads the blank: O0 = `1RZ`, the halt, with 2j + 1 ones (`RF_halt`, `ones_Hc`) |

## 2. The run, and why it halts

| phase | result |
|---|---|
| boot | CO 3 [] (`boot`) |
| exhaustion 1 | RQ 4 = RQ (3·1 + 1): refill CO 4 [2] |
| R0 rounds | G(4) = 40 (`G_4`): CO 40 [1] |
| exhaustion 2 | RQ 43 = RQ (3·14 + 1): refill CO 4 [2^14]; 1012 steps from the blank tape (`step_1012`) |
| the long part | `Chain_out` on the 14 twos at outer levels 0, ..., 13: CO (hoc_0^14(4)) [1^14] |
| exhaustion 3 | RQ (hoc_0^14(4) + 29); hoc_0^14(4) ≡ 1 (mod 3), so this is RQ (3j): the halt (`run`, `halt`) |

**Size** (`BB15_J15_fw13.v`, the hierarchy section). The last outer digit is reduced at level 13, where
ho_13 is f_(ω+13)-class: `hoc14_dom`, with the transfer lemmas `h_dom`, `G_dom`, `ho_dom`, gives
N = 2j + 1 > f_(ω+13)(20) (`sigma_lower_bound`).

## 3. Verification

[`verify/`](verify/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about 30 s, built in CI (job
`bb13-bb14`). `probe.v` re-checks the transition table entry by entry against the string above (30 checks
generated from the string) and the blank start configuration, prints the definitions the statements use, and
confirms that `halt`, `step_1012`, `score_exact`, `sigma_lower_bound` and `beats_M14_31` are closed under the
global context. The proof also passes this project's `check.py`, 2026-11-08.

`BB15_J15_fw13.v` is Argon's file, unchanged except for line endings. `BB15_J15_fw13_cmp.v` (the comparison with
M14_31) was written here. There is no independent simulator for this write-up; every rule cited is a lemma of the
Coq file.

## 4. Comparisons

- **In Coq**: `beats_M14_31` (above). So BB(15) > f_(ω+13)(20) is the best proved bound here for BB(15), above
  BB(14) + 1.
- The 16-state J16_w2 ([`../BB16/`](../BB16/)), one state more, is at level f_(ω·2) and above J15_fw13 in Coq.
- On paper: f_(ω+13)(20) is far above the 19-state J19's f_(ω+7)(f_(ω+7)(5)) ([`../BB19/`](../BB19/)), with four
  states fewer; it is below R18a's f_(ω·2) bound.
- Not yet reviewed by the bbchallenge community.

## Credit

Found and proved in Coq by Argon, a Google Gemini model run by the repository owner in Google's Antigravity
(2026-11-08), by compressing Jacobzheng's J19/J20 architecture: the engine, the two lists and the mod-3 schedule
are Jacobzheng's. Re-checked here (check.py, clean build, probe), with the comparison file and this write-up.
