# M14d_18: a 14-state machine at level f_(ω+2), eighteen rounds deep

    1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LL0LL_0LN1LK_1RZ0LH_0LG1LJ

(Argon writes the halt as `---`; this repository writes it as `1RZ`.)

|   | 0   | 1   |                                                         |
|---|-----|-----|---------------------------------------------------------|
| A | 1RB | 1RA |                                                         |
| B | 1RI | 1RC |                                                         |
| C | 0LD | 1LG |                                                         |
| D | 0RE | 1LD |                                                         |
| E | 1LK | 1RF |                                                         |
| F | 1RM | 0RA |                                                         |
| G | 1RA | 0LH |                                                         |
| H | 1LG | 1LH |                                                         |
| I | 1RE | 0LJ |                                                         |
| J | 1LH | 1LI |                                                         |
| K | 0LL | 0LL | as M13b (M14b: K0 = `0LN`)                              |
| L | 0LN | 1LK | L0 goes to N (M13b and M14b: to H)                      |
| M | 1RZ | 0LH | M0 is the halt                                          |
| N | 0LG | 1LJ | new: ends the left walk of both reloads (M14b: `0RJ0LI`) |

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB14_M14d_18.halt`. |
| Exact score | Machine-checked formula: N = p + a + 5 ones at the halt, where (p, a) = `pa19` is given by the recursion of section 2 (`score_exact`). The halt M0 = `1RZ` is read on a 0, so σ = N + 1 = p + a + 6. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+2)^18(f_ω(f_ω(3))) < N (`sigma_bound`) and f_(ω+2)^17(f_(ω+1)(f_(ω+1)(3))) < N (`sigma_bound_fw1`); σ = N + 1. |
| M14b (previous BB(14) entry) | M14b's proved lower bound is f_(ω+2)^9(f_(ω+1)(f_(ω+1)(3))), below M14d_18's f_(ω+2)^17(f_(ω+1)(f_(ω+1)(3))) (same seed, 17 > 9). M14b has no proved upper bound, so the comparison is between proved lower bounds. |
| Steps | Not computed. |

## 1. How it works

M14d_18 is M13b ([`../BB13/`](../BB13/)) with one transition changed, L0 = `0LH` → `0LN`, and one new state,
N = `0LG1LJ`. The K row is M13b's. (M14b, the previous entry, is also M13b plus a state N, but there N is reached
from K0.) Read M13b's write-up first: the configurations `Ca`, `Ch`, `Ce`, `Cd`, `c_end`, the engine W, the
counter rules `CE_EVEN`, `C_REL`, `D_STEP` and the halt `Ce p a 0 1 →+ c_end p a` [`HALT_step`] are the same,
and all of them are re-proved for this table in `BB14_M14d_18.v` (lemma names in brackets).

| Coq | tape |
|---|---|
| `Ca j b z` | `0^∞ (10)^j 1^b A> 0 z` |
| `Ch j b z` | `0^∞ (10)^j <H 1^(b+1) 0 z` |
| `Ce p a c d` | `0^∞ (10)^p 1^(a+2) I> (10)^c 0 (10)^d 0^∞` |
| `Cd p b d` | `0^∞ (10)^p 1^(b+2) I> (10)^d 0^∞` |
| `c_end p a` | `0^∞ (10)^p 1^(a+5) M> 0^∞` (halted: M reads 0) |

The engine: W_0(b) = b + 3, W_(j+1)(b) = W_j^(b+1)(2), `Ch j b z →+ Ca j (W_j(b)) z` [`CH_CA`]. The counters:

- `Ce (p+1) (2k) (c+1) d →+ Ce (p+k+1) (W_p(1)) c d` [`CE_EVEN`]
- `Cd (p+1) (2m+1) (d+1) →+ Ce p (W_p(3)) m d` [`C_REL`]
- `Ce p a 0 (d+2) →+ Cd p (W_p(a+4)) d` [`D_STEP`]

**What N changes.** When I reads 0 with no c- or d-token in front of it (`Ce · · 0 0` or `Cd · · 0`), it goes
I0 → E0 → K, and K and L walk left over the accumulator, turning each `11` into `10` [`cr_KL_11_10`]. The parity
of the accumulator decides in which state the walk reaches the level cells `(10)^p`:

- Even accumulator, from `Ce`: the walk arrives in L on the 0 of the last level cell. L0 now goes to N, which reads
  the 1 next to it and hands over to J and the engine one level cell further left than in M13b:
  `Ce (p+2) (2k) 0 0 →+ Cd p (W_p(2)) (k+2)` [`D_REL`]. (M13b: `Ce (p+1) (2k) 0 0 →+ Cd p (W_p(0)) (k+2)`.)
- Odd accumulator, from `Cd p (2m+1) 0`: the walk arrives in K, which carries on through the level cells and
  turns each `01` into `10` [`cr_KL_01_10`], so the whole tape becomes d-tokens. At the left end L0 → N, N0 → G,
  G0 → A, and A, B, I restart the counter: `Cd p (2m+1) 0 →+ Ce 0 1 0 (p+m+3)` [`K_REL_step1`, `K_REL_step2`].
  One `D_STEP` and a few literal steps then give `Ce 0 1 0 (d+3) →+ Cd 5 3 d` [`K_REL_step3_aux`], so
  `Cd p (2m+1) 0 →+ Cd 5 3 (p+m)` for p ≥ 1 [`K_REL_to_5_3`].

From `Cd 5 3 (d+3)`, one `C_REL` (to `Ce 4 (W_4(3)) 1 (d+2)`), one `CE_EVEN` (which turns the accumulator
W_4(3) into W_4(3)/2 more level cells) and one `D_STEP` give
`Cd 5 3 (d+3) →+ Cd p_K0 b_K0 d` [`step_5_3`], where

    pb_K0 = (p_K0, b_K0) = (4 + W_4(3)/2,  W_(p_K0)(W_3(1) + 4)).

So every reload restarts at the same configuration, with p + m − 3 d-tokens:
`Cd p (2m+1) 0 →+ Cd p_K0 b_K0 (p+m−3)` for p ≥ 1, m ≥ 2 [`K_REL`]. In M13b the reload restarts at level 8
(`Cd 8 (W_8(8)) (p+m−1)`); here the restart point is already large: p_K0 > f_ω(3) and
b_K0 ≥ 18·f_ω(f_ω(3)) + 17 [`pb_K0_dom_strong`].

The opening from the blank tape is part of that path: 160 steps reach `Cd 5 3 3` [`init_160`], and `step_5_3`
takes it to `Cd p_K0 b_K0 0` [`init_pb1`]. (M13b starts at `Ce 8 4 0 0` after 352 steps.)

## 2. The run

Pairs (p, a) or (p, b) stand for `Ce p a 0 0` or `Cd p b ·`. The macro steps are M13b's:

- Kc(p, a) = (p + a/2, W_(p−1)(1)): one `CE_EVEN`, level f_ω.
- Kc_full(p, b) = Kc^(b/2)(p − 1, W_(p−1)(3)): one `C_REL` plus its b/2 c-tokens, level f_(ω+1).
- Kd_step(p, b) = (p', W_(p')(a' + 4)) where (p', a') = Kc_full(p, b): uses three d-tokens; iterating it is level
  f_(ω+2).
- D_reload(p, a) = (p − 2, W_(p−2)(2)), which is `D_REL` (M13b: (p − 1, W_(p−1)(0))).

There are four kinds of round:

- **D round** from `Ce p a 0 0` (a even): `D_REL` leaves a/2 + 2 d-tokens, a multiple of 3, and Kd_step runs
  (a/2 + 2)/3 times. The result is `Cd · · 0` (`D_round`).
- **Reload** from `Cd p b 0` (b odd): `K_REL` leaves d = p + b/2 − 3 tokens in front of pb_K0, and Kd_step runs
  ⌊d/3⌋ times. Then, by d mod 3:
  - **K0** (d ≡ 0): back at `Cd · · 0`, and the machine reloads again (`K0_round`);
  - **K1** (d ≡ 1): one Kc_full gives `Ce · · 0 0`, ready for a D round (`K1_round`);
  - **K2** (d ≡ 2): one Kc_full gives `Ce p a 0 1`, and `HALT_step` halts (`K2_round`).

From the blank tape the machine reaches pb1 = `Cd p_K0 b_K0 0`. Then (each `run_*` lemma proves the residue of p
listed):

| # | round | result | p (proved) | p mod 3 at `Cd` (picks the next reload) |
|---|---|---|---|---|
| 1 | opening (`init_pb1`) | pb1 = pb_K0, `Cd` | ≡ 1195745 (mod 3^13) | 2 |
| 2 | K1 | pa2, `Ce` | ≡ 132863 (mod 3^12) | |
| 3 | D | pb3, `Cd` | ≡ 107950 (mod 3^12) | 1 |
| 4–9 | K0, six times | pb4 … pb9, `Cd` | pb9 ≡ 350 (mod 3^6) | 1, 1, 1, 1, 1, then 2 |
| 10 | K1 | pa10 | ≡ 144 (mod 3^5) | |
| 11 | D | pb11 | ≡ 17 (mod 3^5) | 2 |
| 12 | K1 | pa12 | ≡ 78 (mod 3^4) | |
| 13 | D | pb13 | ≡ 32 (mod 3^4) | 2 |
| 14 | K1 | pa14 | ≡ 8 (mod 27) | |
| 15 | D | pb15 | ≡ 16 (mod 27) | 1 |
| 16 | K0 | pb16 | ≡ 2 (mod 9) | 2 |
| 17 | K1 | pa17 | ≡ 1 (mod 3) | |
| 18 | D | pb18 | ≡ 0 (mod 3) | 0 |
| 19 | K2: Kd_step, Kc_full, `HALT_step` | `c_end` pa19 | — | |

(The intermediate residues of rounds 4–8 are 45499 mod 3^11, 2326 mod 3^10, 13531 mod 3^9, 2794 mod 3^8 and
1141 mod 3^7.)

**Why this order.** For p ≥ 3 and b ≥ 1, every accumulator W_p(b) equals W_2(y) for some y ≥ 29
[`W_ge3_S_is_W2`], and 2·W_2(y) + 5 = 3^(y+3) [`W2_closed`]. So every accumulator the run produces is known
modulo 3^13: a/2 ≡ −5/4 for an even value and ⌊b/2⌋ ≡ −7/4 for an odd one [`W_ge3_odd`, `W_ge3_even`]. Then, mod
3^13, each Kc adds −5/4 to p, each Kc_full or Kd_step adds −1 + (−7/4)(−5/4) = 19/16, p_K0 ≡ 4 − 5/4 = 11/4, a
D round runs 1/4 (mod 3^12) Kd_steps, and a reload has d ≡ p − 7/4 − 3 ≡ p + 2 (mod 3) tokens. So at a `Cd · · 0`
point, p ≡ 1 gives K0, p ≡ 2 gives K1 and p ≡ 0 halts. A reload's step count ⌊d/3⌋ is known only modulo M/3
when p is known modulo M, so each reload uses up one factor of 3; D rounds use none. The run has 13 reloads,
which is why the proof starts from p mod 3^13. Nothing in the table forces eighteen rounds: it is where this
3-adic orbit first lands in the halting class. (M13b's orbit reaches its halting class at the third reload.)

**Size.** Write B0 = f_ω(f_ω(3)); pb_K0 is above it (`pb_K0_dom_strong`). Each D round applies Kd_step (at
least f_(ω+1)) at least n + 1 times to a pair of size n, which is one f_(ω+2) (`round_D_dom`). Each reload, of
any kind, runs at least 2n + 1 Kd_steps from pb_K0 [`K_count_ge`], and f_(ω+1)^(2n)(3) ≥ f_(ω+2)(n)
[`f_omega2_le_iter_2n`], so it is one f_(ω+2) too (`round_K0_dom`, `round_K1_dom`, `round_K2_dom`). Rounds 2–19
give eighteen applications: f_(ω+2)^18(B0) < N (`sigma_bound`). Since f_(ω+1)(f_(ω+1)(3)) ≤ f_(ω+2)(B0)
(`B1_le_f_omega2_B0`), this gives f_(ω+2)^17(f_(ω+1)(f_(ω+1)(3))) < N (`sigma_bound_fw1`).

## 3. Verification

[`verify_m14d/`](verify_m14d/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about 35 s, built in CI
(job `bb13-bb14`). Argon's proof file is unchanged. `probe.v` re-checks the transition table entry by entry
against the string above (28 checks generated from the string) and confirms that `halt`, `score_exact`,
`sigma_bound` and `sigma_bound_fw1` are closed under the global context.

[`tools/m14d_writeup_chk.py`](tools/m14d_writeup_chk.py) simulates the machine string cell by cell. It
re-checks the rules of section 1 on 168 concrete instances (including both branches of the left walk, the
reload down to `Cd 5 3 (p+m)`, and the 160-step opening). It then re-derives the order of the rounds and all
eighteen residues in the table above from the closed form 2·W_2(y) + 5 = 3^(y+3) (checked on instances), taking
from the Coq file only the fact that every accumulator with p ≥ 3 is such a W_2 value with y ≥ 29
(`W_ge3_S_is_W2`), and compares the result with the residues the Coq file proves.
Run on M14b's table instead, it fails exactly the `D_REL`, reload and opening checks, the rules that N changes.

## 4. Relation to other entries

All comparisons below are between proved lower bounds and are on paper (an argument, not a Coq lemma). None of
these machines has a proved upper bound, so the true scores of the others are not known to be smaller.

- M13b ([`../BB13/`](../BB13/)) is M14d_18 without N, with L0 = `0LH`. Its proved bound is
  f_(ω+2)^6(f_(ω+1)(f_(ω+1)(3))).
- M14b (previous entry, [`README.md`](README.md)) adds its N after K0 instead and splits the reload by the parity
  of p. Its proved f_(ω+2)^9(f_(ω+1)(f_(ω+1)(3))) is below M14d_18's f_(ω+2)^17(f_(ω+1)(f_(ω+1)(3))).
- The 16-state entries ([`../BB16/`](../BB16/)): M16_B's proved f_(ω+2)(f_(ω+3)(9)) equals f_(ω+2)^10(9), and
  M16_C's proved f_(ω+2)(f_(ω+1)^114(f_(ω+2)^3(f_(ω+3)(9)))) is at most f_(ω+2)^14(9), because
  f_(ω+3)(9) = f_(ω+2)^9(9) and f_(ω+1)^114(y) ≤ f_(ω+1)^y(y) = f_(ω+2)(y) for y ≥ 114. Since
  f_(ω+1)(f_(ω+1)(3)) > 9, M14d_18's f_(ω+2)^17(f_(ω+1)(f_(ω+1)(3))) is above f_(ω+2)^17(9), so above both.
- It is below the 17-state entry M17_B ([`../BB17/`](../BB17/)), whose proved bound f_(ω+2)^116(f_(ω+3)^3(9)) is
  f_(ω+3)-class.
- The bbchallenge Champions page (checked 2026-11-04) lists M14b (this repository's previous entry) for BB(14),
  nothing for BB(15), and M16_B for BB(16). M14d_18 has not yet been reviewed by the bbchallenge community.

## Credit

Found and proved by Argon, a Google Gemini model, run by the repository owner in Google's Antigravity
(2026-11-03); re-checked here (busycoq `check.py`, `Print Assumptions`, the probe, the simulator). How it was
found is not recorded.
