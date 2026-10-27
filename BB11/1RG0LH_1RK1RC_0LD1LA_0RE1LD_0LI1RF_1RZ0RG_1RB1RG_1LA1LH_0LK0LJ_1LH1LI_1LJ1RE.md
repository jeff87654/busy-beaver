# M11b: an 11-state machine at level f_(ω+1)

    1RG0LH_1RK1RC_0LD1LA_0RE1LD_0LI1RF_1RZ0RG_1RB1RG_1LA1LH_0LK0LJ_1LH1LI_1LJ1RE

|   | 0   | 1   |                 |
|---|-----|-----|-----------------|
| A | 1RG | 0LH |                 |
| B | 1RK | 1RC |                 |
| C | 0LD | 1LA |                 |
| D | 0RE | 1LD |                 |
| E | 0LI | 1RF |                 |
| F | 1RZ | 0RG | F0 is the halt  |
| G | 1RB | 1RG |                 |
| H | 1LA | 1LH |                 |
| I | 0LK | 0LJ |                 |
| J | 1LH | 1LI |                 |
| K | 1LJ | 1RE |                 |

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB11_M11b.halt`. |
| Exact score | Machine-checked formula: N = p + a + 4 ones at the halt, where (p, a) = `pa_end` is given by the recursion of section 2 (`score_exact`). The halt F0 = `1RZ` is read on a 0, so σ = N + 1. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+1)(f_ω(f_ω(5))) < N (`sigma_lower_bound_m11`), hence f_(ω+1)(f_ω(64)) < N (`sigma_lower_bound_64`). No upper bound is proved. |
| n1 (BB(10) entry) | Beaten, in Coq: n1's halting count is below f_(ω+1)(f_ω(44)) by n1's proved upper bound, and M11b's is above f_(ω+1)(f_ω(f_ω(5))) (`M11_beats_n1`). |
| M12 (BB(12) entry) | Larger, on paper: M12 is f_(ω+2)-class. |
| Steps | Not computed. |

## 1. How it works

Tapes are written left to right; `X>` / `<X` is the head in state X facing right / left. All rules below are lemmas
of `BB11_M11b.v` (names in brackets).

Configurations:

| Coq | tape |
|---|---|
| `Ca j b z` | `0^∞ (10)^j 1^b G> 0 z` |
| `Ch j b z` | `0^∞ (10)^j <H 1^(b+1) 0 z` |
| `Ce p a c z` | `0^∞ (10)^p 1^(a+2) K> (10)^c z` |
| `blk a z` | the block `1^(a+1) 0` followed by `z` |

The inner engine is the finite-level hierarchy W of M12: W_0(b) = b + 3 and W_(j+1)(b) = W_j^(b+1)(2), so W_j grows
like f_j. States A, C, D, G, H run it (they are M12's rows G, C, D, A, H, with A and G swapped):

- `Ch j b z →+ Ca j (W_j(b)) z` [`CH_CA`];
- `Ca j b (10 z) →+ Ca (j+1) b z` [`CA_SH`]: a `10` pair to the right raises the level;
- `Ca j b (blk a z) →+ Ca (j+1) (W_j^a(b)) z` [`BLK_iter`]: a block is absorbed, iterating W_j a times;
- `Ca j b (0 z) →+ 0^∞ (10)^j 1^(b+2) K> z` [`CA_EXIT`].

The outer level runs from state K over the c tokens `10` to its right:

- `Ce (p+1) (2k) (c+1) z →+ Ce (p+k+1) (W_p(1)) c z` [`CE_EVEN`]: one token moves half of the accumulator into the
  level and refills the accumulator with W_p(1), which is even again (`W_par`).
- With no tokens left, the accumulator 1^(2k+2) is rewritten as k tokens in front of the rest of the tape and the
  engine restarts at level p [`K_EVEN_0`]; on an odd accumulator 1^(2m+3) at the blank right end the same happens
  with m + 1 tokens and the level drops by 2 [`K_ODD_0`].
- `Ce p a 0 (11 0^∞) →+ 0^∞ (10)^p 1^(a+4) F> 0^∞` [`HALT_step`], and F reads 0: the halt, with p + a + 4 ones.

## 2. The run

From the blank tape, 424 steps reach `Ce 1 8 3 z0` with z0 = `0 (10)^7 11 0^∞` [`init_424`]. On pairs (p, a), Kc(p, a) = (p + a/2, W_(p−1)(1)) is one `CE_EVEN`; each application raises the level
by half of the previous accumulator W_(p−1)(1), so it acts like f_ω, and c applications act like f_(ω+1)(c).

- Phase 1: the 3 tokens give pa1 = Kc³(1, 8) = (7 + W_4(1)/2, W_6(1)) [`Kc_loop`, `pa1_val`].
- Bridge [`BRIDGE_step`, `Bridge_all`]: with no tokens left, write pa1 = (p'+1, 2k) and j7 = p' + k. `K_EVEN_0`
  restarts the engine at level p', which runs through the k new tokens (level j7), absorbs the `11` block of z0
  (W_j7 twice), runs through its 6 remaining `10` pairs and absorbs the last `11` block (one W_(j7+7)). It exits onto
  blank tape with the odd accumulator w10 = W_(j7+7)(W_j7(W_j7(W_p'(1)))). `K_ODD_0` turns it into c10 = w10/2 + 1
  tokens, and the engine gives `Ce p10 W_p10(1) c10 (11 0^∞)` with p10 = j7 + 6.
- Phase 2: the c10 tokens run Kc c10 times: pa_end = Kc^c10(p10, W_p10(1)) [`Kc_loop`], then `HALT_step`.

So N = p + a + 4 for (p, a) = pa_end, and σ = N + 1. In `BB11_M11b_fgh.v`: W_6(1) ≥ 32·f_ω(5) (`W6_1_bound`), so
j7 ≥ 16·f_ω(5) and c10 ≥ 2·f_ω(f_ω(5)) + 3 (`c2_0_bound`). Two Kc steps apply f_ω to the level (`Kc_dom2`), so
phase 2 applies f_ω at least f_ω(f_ω(5)) times, which gives `sigma_lower_bound_m11`.

## 3. Verification

[`verify/`](verify/): busycoq `bd2e36f`, Coq 8.20.1. `compile_clean.sh` builds the halting proof and the bounds from
scratch in 18 s (CI job `bb13-bb14`); `probe.v` re-checks the transition table entry by entry against the string
above and confirms that `halt`, `score_exact`, `sigma_lower_bound_m11` and `sigma_lower_bound_64` are closed under
the global context. `compile_vs_n1.sh` builds the comparison with n1 on copies of n1's Coq files (about 6 minutes,
recorded locally, not in CI).

## 4. Relation to other entries

M11b runs M12's W engine ([`../BB12/`](../BB12/)) with one outer counter instead of M12's two. One counter gives
level ω+1 and two give ω+2. It fills the BB(11) row, which until now had no entry of its own: n1 (BB(10)) was the
best bound for 11 states.

## Credit

Found and proved in Coq by Argon (a Google Gemini model run by the repository owner in Google's Antigravity),
2026-10-26. It is a different machine from an earlier 11-state candidate of Argon's (2026-10-15) whose claimed bound
was refuted. The proofs were re-checked here: busycoq `check.py`, `Print Assumptions`, and the probe. Argon's bound
file did not compile (one step unfolded W and tried to evaluate W_6(1) in unary). It was repaired here without
changing any statement: W is sealed after use, plus five local tactic fixes. The comparison with n1 was moved to its
own file. The heading of `BB11_M11b.v` was corrected: Argon's stated f_(ω+1)(f_ω(f_ω(6))), but the proved bound
is f_(ω+1)(f_ω(f_ω(5))).
