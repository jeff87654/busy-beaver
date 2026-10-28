# M14b: a 14-state machine at level f_(ω+2), nine rounds deep

    1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LN0LL_0LH1LK_1RZ0LH_0RJ0LI

|   | 0   | 1   |                                                   |
|---|-----|-----|---------------------------------------------------|
| A | 1RB | 1RA |                                                   |
| B | 1RI | 1RC |                                                   |
| C | 0LD | 1LG |                                                   |
| D | 0RE | 1LD |                                                   |
| E | 1LK | 1RF |                                                   |
| F | 1RM | 0RA |                                                   |
| G | 1RA | 0LH |                                                   |
| H | 1LG | 1LH |                                                   |
| I | 1RE | 0LJ |                                                   |
| J | 1LH | 1LI |                                                   |
| K | 0LN | 0LL | K0 goes to N (M13b: to L)                         |
| L | 0LH | 1LK |                                                   |
| M | 1RZ | 0LH | M0 is the halt                                    |
| N | 0RJ | 0LI | new: splits the reload by the parity of the level |

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB14_M14b.halt`. |
| Exact score | Machine-checked formula: N = p + a + 5 ones at the halt, where (p, a) = `pa13` is given by the recursion of section 2 (`score_exact`). The halt M0 = `1RZ` is read on a 0, so σ = N + 1 = p + a + 6. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+2)^9(f_(ω+1)(f_(ω+1)(3))) < σ (`sigma_lower_bound`). |
| M14 (previous BB(14) entry) | M14's proved lower bound is f_(ω+2)(f_(ω+2)(f_(ω+1)^15(f_ω(21)))), far below M14b's. M14 has no proved upper bound, so the comparison is between proved lower bounds. |
| Steps | Not computed. |

## 1. How it works

M14b is M13b ([`../BB13/`](../BB13/)) with one more state, N, between K0 and the rest of the reload. Read that
write-up first: the configurations `Ca`, `Ch`, `Ce`, `Cd`, `c_end`, the engine W, the counter rules `CE_EVEN`,
`C_REL`, `D_STEP`, `D_REL` and the halt `Ce p a 0 1 →+ c_end p a` [`HALT_step`] are the same, and all of them
are re-proved for this table in `BB14_M14b.v`.

The difference is the reload from `Cd p (2m+1) 0`. In M13b it always turns the tape into d-tokens. In M14b, K0
goes to N, and the walk left over the level cells `(10)^p` now runs two cells at a time
[`cr_KN_0101_1010`, `cr_KN_even`], so the parity of p chooses the branch:

- p odd: `Cd (2q+1) (2m+1) 0 →+ Cd 8 (W_8(8)) (2q+m)` [`K_REL_odd`]. This is M13b's reload: p + m − 1 d-tokens
  and a fresh start at level 8.
- p even: `Cd (2q) (2m+1) 0 →+ Ce (2q+m+2) 4 0 0` [`K_REL_even`]. Here the tape does not become tokens. It becomes
  a level, and the machine replays its own opening round, which starts from `Ce 8 4 0 0`, at level p + m + 2.
  The result is K_even_reload(p, b) = Kc_full(Kd_step(D_reload(p + b/2 + 2, 4))), a `Ce · · 0 0` configuration
  ready for another D round.

## 2. The run

The macro steps Kc, Kc_full, Kd_step (three d-tokens, level f_(ω+2) when iterated) and D_reload are M13b's. After
an odd reload with d tokens, Kd_step runs ⌊d/3⌋ times. Then:

- with no token left, the machine is back at `Cd p b 0` and reloads again;
- with one left, Kc_full gives `Ce p a 0 0`, ready for a D round;
- with two left, Kc_full gives `Ce p a 0 1`, and that halts.

From the blank tape, 352 steps reach `Ce 8 4 0 0` [`init_352`]. Then (each `run_*` lemma also proves the
residues listed; the accumulator stays ≡ 362 (mod 972) at `Ce` points and ≡ 119 (mod 972) at `Cd` points):

| phase | what runs | result | p (proved) |
|---|---|---|---|
| 1 | opening round: `D_REL`, Kd_step, Kc_full | pa1 = `Ce` p a 0 0 | ≡ 141 (mod 162) |
| 2 | D round: `D_REL`, Kd_step a/6 + 1 times | pb2 = `Cd` p b 0 | ≡ 96 (mod 162), even |
| 3 | even reload | pa3 | ≡ 128 (mod 162) |
| 4 | D round | pb4 | ≡ 83 (mod 162), odd |
| 5 | odd reload, d5 ≡ 0 (mod 3): Kd_step d5/3 times | pb5 = `Cd` p b 0 | ≡ 52 (mod 54), even |
| 6 | even reload | pa6 | ≡ 30 (mod 54) |
| 7 | D round | pb7 | ≡ 39 (mod 54), odd |
| 8 | odd reload, d8 ≡ 1 (mod 3): Kd_step (d8−1)/3 times, then Kc_full | pa8 | ≡ 14 (mod 18) |
| 9 | D round | pb9 | ≡ 5 (mod 18), odd |
| 10 | odd reload, d10 ≡ 0 (mod 3) | pb10 | ≡ 2 (mod 6), even |
| 11 | even reload | pa11 | ≡ 4 (mod 6) |
| 12 | D round | pb12 | ≡ 1 (mod 6), odd |
| 13 | odd reload, d13 ≡ 2 (mod 3): Kd_step (d13−2)/3 times, Kc_full, `HALT_step` | `c_end` pa13 | — |

At every odd reload the token count is d = p + b/2 − 1 ≡ p + 1 (mod 3), since b/2 ≡ 2 (mod 3). So p mod 6 decides
everything at a `Cd · · 0` point. Even p gives an even reload. Odd p gives an odd reload, which, by p mod 3,
returns to `Cd`, goes on to a D round, or halts. As in M13b, the residue of p is known modulo a modulus that
loses a factor of 3 at each odd reload (162, 54, 18, 6). That countdown ends the run at phase 13.

**Size** (`BB14_M14b_bound.v`). Phase 1 gives f_(ω+1)(f_(ω+1)(3)) (`pa1_dom`). Each D round (phases 2, 4, 7, 9,
12) is one f_(ω+2) (`round_D_dom`). So is each odd reload followed by its Kd_step loop (phases 5, 8, 10, 13:
`round_K_dom`, `round_K_r0_dom`). An even reload only keeps the bound (`K_even_reload_dom`). That makes nine
applications of f_(ω+2), which is `sigma_lower_bound`.

## 3. Verification

[`verify_m14b/`](verify_m14b/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about 40 s, built in CI
(job `bb13-bb14`). `probe.v` re-checks the transition table entry by entry against the string above and confirms
that `halt`, `score_exact` and `sigma_lower_bound` are closed under the global context. The bound was also
restated, outside the repository, against separately written definitions of iteration, the fast-growing
hierarchy and the ones count; that restatement is closed under the global context too.

[`../BB13/tools/m13b_m14b_writeup_chk.py`](../BB13/tools/m13b_m14b_writeup_chk.py) simulates the machine string
cell by cell. It re-checks the rules of section 1 and of M13b's write-up on concrete instances (143 for this
machine, including both reload branches) and the 352-step opening. It does not depend on the Coq files.

## 4. Relation to other entries

- M13b ([`../BB13/`](../BB13/)) is M14b without N, where K0 = `0LL`. Every M13b reload is an odd reload, so it
  gets six f_(ω+2) rounds instead of nine.
- M12 ([`../BB12/`](../BB12/)) and M14 (previous entry, [`README.md`](README.md)) share the A–D, G and H rows
  (the W engine).
- On paper, M14b's proved lower bound exceeds the published BB(14)–BB(16) lower bounds. It has not been compared
  with the f_(ω+2)-class BB(17)/BB(18) champions.

## Credit

Found and proved in Coq by Argon (a Google Gemini model run by the repository owner in Google's Antigravity),
2026-10-28. How it was found is not recorded. The proofs were re-checked here (busycoq `check.py`,
`Print Assumptions`, the probe, the independent restatement of the bound).
