# M13b: a 13-state machine at level f_(ω+2), six rounds deep

    1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LL0LL_0LH1LK_1RZ0LH

|   | 0   | 1   |                                                   |
|---|-----|-----|---------------------------------------------------|
| A | 1RB | 1RA |                                                   |
| B | 1RI | 1RC |                                                   |
| C | 0LD | 1LG |                                                   |
| D | 0RE | 1LD |                                                   |
| E | 1LK | 1RF |                                                   |
| F | 1RM | 0RA | F0 goes to M (M12: to G)                          |
| G | 1RA | 0LH |                                                   |
| H | 1LG | 1LH |                                                   |
| I | 1RE | 0LJ |                                                   |
| J | 1LH | 1LI |                                                   |
| K | 0LL | 0LL | K0 starts the reload (M12: K0 is the halt)        |
| L | 0LH | 1LK |                                                   |
| M | 1RZ | 0LH | M0 is the halt; M1 = G1                           |

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB13_M13b.halt`. |
| Exact score | Machine-checked formula: N = p + a + 5 ones at the halt, where (p, a) = `pa7` is given by the recursion of section 2 (`score_exact`). The halt M0 = `1RZ` is read on a 0, so σ = N + 1 = p + a + 6. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+2)^6(f_(ω+1)(f_(ω+1)(3))) < σ (`sigma_lower_bound`). |
| M13 (previous BB(13) entry) | M13's proved lower bound is f_(ω+2)(f_ω(20)), far below M13b's. M13 has no proved upper bound, so the comparison is between proved lower bounds. |
| M12 (BB(12) entry) | M13b runs all of M12's computation (section 2, rounds 1–2), and where M12 halts it continues for five more rounds. On paper; M12's exact score is not compared in Coq. |
| Steps | Not computed. |

## 1. How it works

M13b is M12 ([`../BB12/`](../BB12/)) with one more state. M12's halt K0 becomes `0LL`, a reload that recycles
the whole tape into a fresh counter. The halt moves to the new state M, which acts like G on a 1 and halts on a 0.
All rules below are lemmas of `BB13_M13b.v` (names in brackets). Tapes are written left to right; `X>` / `<X` is
the head in state X facing right / left.

Configurations (the same as M12's, plus the halting one):

| Coq | tape |
|---|---|
| `Ca j b z` | `0^∞ (10)^j 1^b A> 0 z` |
| `Ch j b z` | `0^∞ (10)^j <H 1^(b+1) 0 z` |
| `Ce p a c d` | `0^∞ (10)^p 1^(a+2) I> (10)^c 0 (10)^d 0^∞` |
| `Cd p b d` | `0^∞ (10)^p 1^(b+2) I> (10)^d 0^∞` |
| `c_end p a` | `0^∞ (10)^p 1^(a+5) M> 0^∞` (halted: M reads 0) |

**Inner engine (as in M12).** A finite-level hierarchy W with W_0(b) = b + 3 and W_(j+1)(b) = W_j^(b+1)(2), so
W_j grows like f_j. States A, D, G, H run it: `Ch j b z →+ Ca j (W_j(b)) z` [`CH_CA`], and a block 1^(a+1) 0
to the right is absorbed as `Ca j b (1^(a+1) 0 z) →+ Ca (j+1) (W_j^a(b)) z` [`BLK_iter_aux`].

**Outer counters (as in M12).** From state I, with c-tokens and d-tokens (`10` cells) to the right of the head:

- `Ce (p+1) (2k) (c+1) d →+ Ce (p+k+1) (W_p(1)) c d` [`CE_EVEN`]
- `Cd (p+1) (2m+1) (d+1) →+ Ce p (W_p(3)) m d` [`C_REL`]
- `Ce p a 0 (d+2) →+ Cd p (W_p(a+4)) d` [`D_STEP`]
- `Ce (p+1) (2k) 0 0 →+ Cd p (W_p(0)) (k+2)` [`D_REL`]

**New: the reload and the halt.**

- `Cd p (2m+1) 0 →+ Cd 8 (W_8(8)) (p+m−1)` for p ≥ 1 [`K_REL`]. This is where M12 halts. In M13b, K walks left
  and turns the level cells `(10)^p`, together with half the odd accumulator, into d-tokens. This gives
  `Cd 2 3 (p+m+2)` [`K_REL_step1`, `K_REL_step2`]. Then it replays the machine's opening (`C_REL`, `CE_EVEN`,
  `D_STEP`) to reach level 8 with p + m − 1 d-tokens [`K_REL_step3`].
- `Ce p a 0 1 →+ c_end p a` [`HALT_step`]: a single leftover d-token sends F to M on a 0, which halts with
  N = p + a + 5 ones.

## 2. The run

Pairs (p, a) or (p, b) stand for `Ce p a 0 0` or `Cd p b ·`. The macro steps are:

- Kc(p, a) = (p + a/2, W_(p−1)(1)): one `CE_EVEN`, level f_ω.
- Kc_full(p, b) = Kc^(b/2)(p − 1, W_(p−1)(3)): one `C_REL` (one d-token) plus its b/2 c-tokens, level f_(ω+1).
- Kd_step(p, b) = (p', W_(p')(a' + 4)) where (p', a') = Kc_full(p, b): uses three d-tokens. Iterating it is
  level f_(ω+2).
- D_reload(p, a) = (p − 1, W_(p−1)(0)), which is `D_REL`.

What happens after `K_REL` depends on the number d of d-tokens mod 3. The machine runs Kd_step ⌊d/3⌋ times. With
one token left, one Kc_full brings it to `Ce p a 0 0`, ready for a D round. With two left, Kc_full leaves
`Ce p a 0 1`, and that halts.

From the blank tape, 352 steps reach `Ce 8 4 0 0` [`init_352`]. Then:

| round | what runs | result | invariant proved (`run_*`) |
|---|---|---|---|
| 1 | `D_REL`, one Kd_step, one Kc_full (as M12) | pa1 = `Ce` p a 0 0 | p ≡ 60 (mod 81), a ≡ 38 (mod 162) |
| 2 | D round: `D_REL` gives a/2 + 2 tokens; Kd_step a/6 + 1 times (as M12) | pb2 = `Cd` p b 0 | p ≡ 15 (mod 27), b ≡ 119 (mod 162) |
| 3 | K round: `K_REL`, d3 = p + b/2 − 1 ≡ 1 (mod 3); Kd_step (d3−1)/3 times from (8, W_8(8)); Kc_full | pa3 | p ≡ 0 (mod 9) |
| 4 | D round | pb4 | p ≡ 0 (mod 9) |
| 5 | K round, d5 ≡ 1 (mod 3) | pa5 | p ≡ 1 (mod 3) |
| 6 | D round | pb6 | p ≡ 1 (mod 3) |
| 7 | K round, d7 ≡ 2 (mod 3): Kd_step (d7−2)/3 times, Kc_full, then `HALT_step` | `c_end` pa7 | — |

M12 halts at the end of round 2, where M13b reloads instead. Since b ≡ 119 (mod 162), b/2 ≡ 2 (mod 3), so every K
round has d ≡ p + 1 (mod 3). The machine halts at the first K round with p ≡ 1 (mod 3). The residue of p is known
modulo a power of 3 that drops by one factor of 3 per K round (81, 27, 9, 3). That 3-adic countdown is what
decides the halt, and it allows exactly three K rounds. The residues mod 162 come from the parity and mod-162
lemmas for W (`W_par`, `W_ge3_even_mod162`, `W_ge3_odd_mod162`, …).

**Size** (`BB13_M13b_bound.v`). Round 1 gives pa1 above f_(ω+1)(f_(ω+1)(3)) (`pa1_dom`). Each D round applies
Kd_step (≥ f_(ω+1)) a/6 + 1 times, so it is one f_(ω+2) (`round_D_dom`). A K round starts with at least twice
as many d-tokens as the previous bound (`K_count_ge`), so it is another f_(ω+2) (`round_K_dom`). Rounds 2–7 give
six applications of f_(ω+2), which is `sigma_lower_bound`.

## 3. Verification

[`verify_m13b/`](verify_m13b/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about 30 s, built in CI
(job `bb13-bb14`). `probe.v` re-checks the transition table entry by entry against the string above and confirms
that `halt`, `score_exact` and `sigma_lower_bound` are closed under the global context. The bound was also
restated, outside the repository, against separately written definitions of iteration, the fast-growing
hierarchy and the ones count, bridged by induction lemmas; that restatement is closed under the global context
too.

[`tools/m13b_m14b_writeup_chk.py`](tools/m13b_m14b_writeup_chk.py) simulates the machine string cell by cell. It
re-checks every rule of section 1 on concrete instances (143 for this machine) and the 352-step opening. It does
not depend on the Coq files.

## 4. Relation to other entries

- M12 ([`../BB12/`](../BB12/)) is M13b without state M, with F0 = `1RG` and K0 as the halt. Rounds 1–2 above are
  M12's whole run.
- M14b ([`../BB14/`](../BB14/)) is M13b with one more state, N. The reload then depends on the parity of p, which
  makes room for nine f_(ω+2) rounds.
- M13 (previous entry, [`README.md`](README.md)) is a different machine with a single f_(ω+2) round.
- On paper, M13b's proved lower bound also exceeds M14's (the previous BB(14) entry). It has not been compared with
  the f_(ω+2)-class BB(17)/BB(18) champions.

## Credit

Found and proved in Coq by Argon (a Google Gemini model run by the repository owner in Google's Antigravity),
2026-10-28. How it was found is not recorded. The proofs were re-checked here (busycoq `check.py`,
`Print Assumptions`, the probe, the independent restatement of the bound).
