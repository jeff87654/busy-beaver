# M14_31: a 14-state machine at level f_(ω+2), thirty-one rounds deep

    1RB1RA_1RI1RC_0LD1LG_0RE1LD_0RN1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LL0LL_0LH1LK_0LK0LH_1LM---

|   | 0   | 1   |                                                                      |
|---|-----|-----|----------------------------------------------------------------------|
| A | 1RB | 1RA |                                                                      |
| B | 1RI | 1RC |                                                                      |
| C | 0LD | 1LG |                                                                      |
| D | 0RE | 1LD |                                                                      |
| E | **0RN** | 1RF | E0 goes to N (M14d_18: `1LK`)                                     |
| F | 1RM | 0RA |                                                                      |
| G | 1RA | 0LH |                                                                      |
| H | 1LG | 1LH |                                                                      |
| I | 1RE | 0LJ |                                                                      |
| J | 1LH | 1LI |                                                                      |
| K | 0LL | 0LL | as M14d_18                                                           |
| L | **0LH** | 1LK | L0 back to H, as in M13b (M14d_18: `0LN`)                         |
| M | **0LK** | 0LH | M0 now continues into K (M14d_18: M0 was the halt)                |
| N | **1LM** | --- | new role: plants or reads a sentinel cell; N1 is the halt         |

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB14_M14_31.halt`. |
| Exact score | Machine-checked formula: N = p + a + 4 ones at the halt, where (p, a) = `pa32` is given by the recursion of section 2 (`score_exact`). The halt N1 (`---`) is read on a 1, so σ = N = p + a + 4. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+2)^31(f_ω(f_ω(3))) < σ (`sigma_bound`) and f_(ω+2)^30(f_(ω+1)(f_(ω+1)(3))) < σ (`sigma_bound_fw1`). |
| M14d_18 (previous BB(14) entry) | **In Coq** (`BB14_M14_31_cmp.v`): σ is above both of M14d_18's proved bounds, f_(ω+2)^18(f_ω(f_ω(3))) (`beats_M14d_18`) and f_(ω+2)^17(f_(ω+1)(f_(ω+1)(3))) (`beats_M14d_18_fw1`). Those are M14d_18's proved lower bounds; it has no proved upper bound. |
| Steps | Not computed. |

## 1. How it works

M14_31 runs the engine and counters of M13b and M14d_18 ([`../BB13/`](../BB13/), and M14d_18's write-up in this
directory); read those first. The configurations `Ca`, `Ch`, `Ce`, `Cd`, the engine W (W_0(b) = b + 3,
W_(j+1)(b) = W_j^(b+1)(2)), the counter rules `CE_EVEN`, `C_REL`, `D_STEP` and the macro steps Kc, Kc_full and
Kd_step (one f_(ω+2) round per iterated Kd_step) are the same, re-proved for this table in `BB14_M14_31.v`.

What changes is how a round ends. In M14d_18, M0 was the halt, so the machine stopped the first time a reload ended
with d ≡ 2 (mod 3). Here M0 = `0LK` continues, and the four changed slots (E0, L0, M0, N) keep one extra bit on the
tape: a **sentinel** cell to the right of the counter, absent (z₀ = 0^∞) or present (z₁ = 0 1 0^∞). The rounds start
from `Cd_z p b d z` (M14d_18's `Cd` with the right tail z), and the round type depends on d mod 3 and on the
sentinel (Argon's analysis; each case is a Coq lemma):

- **d ≡ 0, no sentinel**: E0 → N0 → M0 writes the sentinel, and K, L shift the level cells into d-tokens; the
  machine reloads at the fixed point pb_K0 = (8, W_8(8)) with the sentinel set (`K0_z0_round`).
- **d ≡ 0, sentinel present**: F0 → M0 reads and erases it, and the machine reloads at pb_K0 without it
  (`K0_z1_round`).
- **d ≡ 2**: one Kc_full, then a D reload that keeps the sentinel as it is; the next round then has d ≡ 0
  (`K2_z0_round`, `K2_z1_round`, then `D2_round`).
- **d ≡ 1**: one Kc_full, then a D reload; with the sentinel present this is `K1_z1_round` and `D1_round`; without
  it, `K1_z0_round` ends at `Ce p a 0 1` with N reading the 1 next to the counter: N1 is the halt (`HALT_step`).

So the machine halts only when a round with d ≡ 1 finds no sentinel. The sentinel lets M14_31 survive the
residues that ended M14d_18.

## 2. The run

From the blank tape, 118 steps reach `Cd_z 2 3 5 z₀` (`init_118`), and the opening reaches the reload point pb_K0
(`init_pb0`). Then the Coq file defines the 32 rounds one by one (`pa1` … `pa32`):

    pa1 = Kc_full(pb_K0); then D2, K0_z0, K2_z1, D2, K0_z0, K0_z1, K2_z0, D2, K2_z1, D2, K2_z0, D2, K1_z1, D1, D2,
    K1_z1, D1, D2, K0_z1, K2_z0, D2, K1_z1, D1, D2, K2_z1, D2, K2_z0, D2, K2_z1, D2, and K1_z0 (round 32: halt).

Each round's type is fixed by residues of (p, a) that the proof computes (`run_pa32`); the halting round 32 is
`K1_z0`. 31 of the 32 rounds iterate Kd_step a huge number of times, so each adds an f_(ω+2) level
(`pa32_dom`, `pa32_dom_fw1`: the domination chain through the rounds), which gives

    f_(ω+2)^31(f_ω(f_ω(3))) < σ   and   f_(ω+2)^30(f_(ω+1)(f_(ω+1)(3))) < σ.

The halting configuration is `c_end p a` = 0^∞ (10)^p 1^(a+3) 0 N> 1 0^∞ (N reading a 1), with p + a + 4 ones
(`ones_c_end`, `score_exact`).

## 3. Verification

[`verify_m14_31/`](verify_m14_31/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about 40 s, built in CI
(job `bb13-bb14`). `probe.v` re-checks the transition table entry by entry against the string above (28 checks
generated from the string) and the blank start configuration, prints the definitions the statements use, and
confirms that `halt`, `score_exact`, `sigma_bound`, `sigma_bound_fw1`, `beats_M14d_18` and `beats_M14d_18_fw1` are
closed under the global context. The proof also passes this project's `check.py` (the statement `halts tm c0` read
from the file, the table compared with the machine string, `Print Assumptions halt` closed), 2026-11-08.

`BB14_M14_31.v` is Argon's file, unchanged except for line endings. `BB14_M14_31_cmp.v` (the comparison with
M14d_18) was written here.

There is no independent simulator for this write-up; section 1 summarises Argon's analysis, and every rule cited
is a lemma of the Coq file.

## 4. Comparisons

- **In Coq**: `beats_M14d_18`, `beats_M14d_18_fw1` (above). M14d_18's iterations of f_(ω+2) start from the same seeds
  (f_ω(f_ω(3)) and f_(ω+1)(f_(ω+1)(3))), with 18 and 17 rounds against 31 and 30 here.
- Both 16-state entries before this one (M16_B, M16_C) were already below M14d_18; the 15-state J15_fw13
  ([`../BB15/`](../BB15/)) and the 16-state J16_w2 ([`../BB16/`](../BB16/)) are above M14_31, in Coq.
- The bbchallenge wiki's BB(14) row (checked 2026-11-08) is M14d_18, listed as "> f_(ω+3)(17)". On paper:
  f_(ω+3)(17) = f_(ω+2)^17(17), and f_(ω+1)(f_(ω+1)(3)) ≥ 17, so M14_31's proved bound is above it.
- Not yet reviewed by the bbchallenge community.

## Credit

Found and proved in Coq by Argon, a Google Gemini model run by the repository owner in Google's Antigravity
(2026-11-08), by a search of the outer transitions (E0, K, L, M, N) around M12's 10-state core, which M13b and
M14d_18 share. Re-checked here (check.py, clean build, probe), with the comparison file and this write-up.
