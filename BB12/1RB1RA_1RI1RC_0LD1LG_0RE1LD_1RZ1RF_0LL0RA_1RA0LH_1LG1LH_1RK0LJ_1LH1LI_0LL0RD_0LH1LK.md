# P12: a 12-state machine at level f_(ω+2), eight loops deep

    1RB1RA_1RI1RC_0LD1LG_0RE1LD_1RZ1RF_0LL0RA_1RA0LH_1LG1LH_1RK0LJ_1LH1LI_0LL0RD_0LH1LK

| state | 0 | 1 | M12 | |
|---|---|---|---|---|
| A | 1RB | 1RA | same | |
| B | 1RI | 1RC | same | |
| C | 0LD | 1LG | same | |
| D | 0RE | 1LD | same | |
| E | **1RZ** | 1RF | E0 = `1LK` | E0 is the halt |
| F | **0LL** | 0RA | F0 = `1RG` | |
| G | 1RA | 0LH | same | |
| H | 1LG | 1LH | same | |
| I | **1RK** | 0LJ | I0 = `1RE` | |
| J | 1LH | 1LI | same | |
| K | **0LL** | **0RD** | K0 = `1RZ` (M12's halt), K1 = `0LL` | |
| L | 0LH | 1LK | same | |

P12 is Argon's 12-state machine M12 ([`README.md`](README.md), previous entry) with five transitions changed: E0
becomes the halt, F0, I0, K0 and K1 are new; the states and the start state A are M12's. The halting transition E0 is
undefined in the Coq table (`---`); it is written `1RZ` here. As a Coq string:
`1RB1RA_1RI1RC_0LD1LG_0RE1LD_---1RF_0LL0RA_1RA0LH_1LG1LH_1RK0LJ_1LH1LI_0LL0RD_0LH1LK`.

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB12_P12.halt`. |
| Exact score | Machine-checked formula: N = u + p + 1 ones when E0 is read, where (p, u) = `nP` is given by the recursion of section 2 (`score_exact`). E0 is read on a 0 and the halting transition writes a 1, so σ = N + 1. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+2)^8(f_3(6)) < N (`sigma_lower_bound`). |
| C4 (BB(11) entry) | **In Coq, against its exact score** (`BB12_P12_cmp.v`): C4's halting tape holds exactly NC = snd nFIN + 3 + fst nFIN ones (C4's `score_exact`), proved here to be at most f_(ω+2)^7(8) + 3 from C4's own definitions, and NC + 1 < N (`beats_C4_exact`, `beats_C4_score`). Both halt reading a 0, so σ(P12) = N + 1 > NC + 2 = σ(C4) + 1: P12 is above the bound BB(12) ≥ BB(11) + 1 that C4 gave. |
| M12 (previous BB(12) entry) | Below C4's score in Coq (`beats_M12_exact` in [`../BB11/verify_c4/`](../BB11/verify_c4/)), hence below P12's. |
| Steps | Not computed. |

## 1. How it works

P12 keeps M12's engine. With the configurations (busycoq notation, left side written nearest-first)

    Ca j b z = [1]^b [0;1]^j 0^∞  A>  0 z          Ch j b z = [0;1]^j 0^∞  <H  1 [1]^b 0 z

the engine rule `CH_CA` is Ch j b z → Ca j (W j b) z, with W_0(b) = b + 3 and W_(j+1)(b) = W_j^(b+1)(2), so
W_j(b) grows like f_j: one engine call is one f_ω-level step. `CA_SH` shifts a pair [1;0] of the right side into the
left block, and `CA_EXIT` hands over to state I. These rules, and the cycle lemmas they use, are M12's, unchanged:
P12 agrees with M12 on every transition they read.

What is new is how the engine is fed. Write

    Y p u w = [1]^u [0;1]^p 0^∞  I>  w           X p u t = Y p u (0 t)

(on the tape, from left to right: (10)^p 1^u, then the head in state I). The rules of `BB12_P12.v`:

- **R_A**: X p u ([1;0]^(d+2) t) → Y p (W_p(u) + 2) ([1;0]^(d+1) t): one engine call at level p on the 1-block,
  using up a pair of the stock [1;0]^d on the right.
- **R_Bo**: Y (q+1) (2m+3) (1 t) → Y q (W_q(1) + 2) ([1;0]^(m+1) t): an odd 1-block is cut into m + 1 new pairs on
  the right, and the engine runs at level q on 1.
- **R_Be**: Y (q+1) (2m+2) (1 0 t) → Y (q+m+1) (W_q(1) + 2) t: an even 1-block raises the level by about half its
  length, through the same engine call. As a map on (q, u) this is `Be` (q, u) = (q − 1 + u/2, W_(q−1)(1) + 2).
- **BLANK**: Y p (2m+2) 0^∞ → Y 0 4 ([1;0]^(p+m+2) 0^∞): at the blank, the left block is converted into a new
  stock of pairs on the right.
- **BOOT2**: Y 0 4 ([1;0]^(D+2) t) → Y 2 5 ([1;0]^(D+1) t).
- **R_H**: X p u (1 0 0^∞) reaches E reading a 0: the halt, with u + p + 1 ones.

A **round** (`ROUND`, map `Rd`) uses two pairs of the stock: R_A gives an odd 1-block of length W_p(u) + 2, R_Bo
cuts it into m = (W_p(u) + 1)/2 pairs, and m passes of R_Be eat them one by one, each raising the level q by u/2 − 1,
where u is the current 1-block (the previous engine call's output plus 2). So one round is an f_(ω+1)-level step: `Rd` (p, u) = `Be`^((W_p(u)+1)/2) (p − 1, W_(p−1)(1) + 2).
Rounds iterated over a stock (`ROUNDS`) form an f_(ω+2) loop.

A **big round** on a base of D pairs starts from Y 0 4 ([1;0]^D 0^∞); BOOT2, R_Bo and two passes of R_Be reach
X 7 (W_4(1) + 2) ([1;0]^(D−2) 0^∞), the same configuration in every big round apart from D (`BOOT`). Then:

- if D is even, (D − 2)/2 rounds use up the stock and BLANK rebuilds a base of D' = P + U/2 + 1 pairs, where (P, U) =
  `Rd`^((D−2)/2) (7, W_4(1) + 2) (`BIG_EVEN`, map `Big`);
- if D is odd, (D − 3)/2 rounds leave X P U (1 0 0^∞) and R_H halts (`BIG_ODD`).

So the base is a gate: the machine halts in the first big round whose base is odd.

## 2. The run

From the blank tape, 248 steps reach Ch 4 1 ([1;0]^3 0^∞); the engine, three CA_SH and CA_EXIT give
Y 7 (W_4(1) + 2) 0^∞, and BLANK makes the first base D_0 = 7 + W_4(1)/2 + 2 (`boot`). With D_(k+1) = `Big` (D_k),

    nD0 = 7 + W_4(1)/2 + 2,   nD7 = Big^7 (nD0),   nP = Rd^((nD7 − 3)/2) (7, W_4(1) + 2),

the bases D_0, ..., D_6 are even and D_7 is odd, so the machine runs seven full big rounds, then (D_7 − 3)/2 rounds
of the eighth and halts at E0 with (p, u) = `nP` (`RUN_GEN`, `run_FIN`, `halt`, `score_exact`).

**The parities.** Every W in the run is W_j(b) with j ≥ 4 and b ≥ 1. For j ≥ 3, W_j(b) is a value T_h of the tower
T_0 = 2, T_(h+1) = W_2(T_h), W_2(y) = (3^(y+3) − 5)/2 (`W2_closed`), with h ≡ b + 1 (mod 2) and h large (`W_T`,
`W_big`). Since 3 has order 2^(n+1) modulo 2^(n+3) (`ord3`), T_h mod 2^(k+1) depends only on T_(h−1) mod 2^k
(`W2_cong`), so for h ≥ 12 the residue mod 2^13 depends only on the parity of h (`T_tab`, `T_mod`): W_j(b) mod 2^13 =
3826 for b odd and 407 for b even (j ≥ 4, b ≥ 1; `W_res`). The rounds then act linearly on residues, and
`Big` D ≡ 1922 + 1131·(D − 2)/2 (mod 4096) (`Big_mod`). Each big round loses one bit of precision:

    D_0 ≡ 1922 (mod 4096),  D_1 ≡ 194 (mod 2048),  D_2 ≡ 930 (mod 1024),  D_3 ≡ 370 (mod 512),
    D_4 ≡ 106 (mod 256),  D_5 ≡ 62 (mod 128),  D_6 ≡ 12 (mod 64),  D_7 ≡ 25 (mod 32)

(`D0_mod`, `Big1` to `Big7`, `chain`): the gate parities of D_1, ..., D_7 are 0, 0, 0, 0, 0, 0, 1.

**The size.** One round takes p − 4 to at least f_(ω+1)(p − 4), so a big round takes a base D ≥ 4y + 8 to at least
4·f_(ω+2)(y) + 8; D_0 ≥ 4·f_3(6) + 8, and the eight big rounds give p ≥ 4·f_(ω+2)^8(f_3(6)) + 8
(`BB12_P12_bound.v`, `N_dom`), hence `sigma_lower_bound`.

## 3. Verification

[`verify_p12/`](verify_p12/): busycoq `bd2e36f`, Coq 8.20.1, built in CI (job `bb13-bb14`). `probe.v` re-checks the
transition table entry by entry against the machine string (24 checks generated from the string) and the blank
start configuration, prints the definitions the statements use, and confirms that `halt`, `score_exact`,
`sigma_lower_bound`, `beats_C4_exact` and `beats_C4_score` are closed under the global context. The halting proof
also passes this project's `check.py` (the statement `halts tm c0` read from the file, the table compared with the
machine string, `Print Assumptions halt` closed), 2026-11-15.

`BB12_P12.v`, `BB12_P12_bound.v` and `BB12_P12_cmp.v` are this project's proof files, unchanged. The comparison loads
C4's proof `BB11_C4.v` (byte-identical copy of [`../BB11/verify_c4/multifile/`](../BB11/verify_c4/multifile/), with
busycoq for 11 states); busycoq for 12 states is copied from [`verify_m12/multifile/`](verify_m12/multifile/).
`share_check.sh` checks the five copies.

[`tools/p12/`](tools/p12/) has the independent check made before the Coq proof (a literal simulator written from
scratch, not the finder's tools): `rules_check.py` runs every rule above on concrete instances (p ≤ 3, small u, m,
d, random tails; 310 rule instances, 60 halts and the 248-step opening, no failures), and `gates.py` computes the
gate parities with its own 2-adic arithmetic (D_0, ..., D_7 mod 2^16 = 10114, 59586, 52130, 30066, 4714, 36926,
9228, 37785).

## 4. Comparisons

- **C4 (BB(11)), in Coq against its exact score** (`BB12_P12_cmp.v`, which loads C4's proof file): from the
  definitions of C4's maps (W, Zs, Rnd and the run's numbers), C4's exact count is at most f_(ω+2)^7(8) + 3
  (`c4_score_ub`), below P12's lower bound (`beats_C4_exact`, `beats_C4_score`: NC + 1 < N). Before P12, C4 gave the
  best proved bound for BB(12) through BB(12) ≥ BB(11) + 1; P12 is above that bound.
- **M12 (previous BB(12) entry)**: C4 is above M12's exact score in Coq (`beats_M12_exact`, `beats_M12_score`), so
  P12 is too.
- **M13_19 (BB(13))**: its proved lower bound f_(ω+2)^19(f_ω(3)) is above P12's f_(ω+2)^8(f_3(6)) (on paper:
  f_(ω+2)(f_ω(3)) > f_3(6)). P12 has no proved upper bound.
- Not yet reviewed by the bbchallenge community.

## Credit

Found and proved in Coq by this project (the repository owner's work with Claude models as agents), 2026-11-15. An
exhaustive enumeration of the 12-state family
`1RB1RA_1RI1RC_0LD1LG_0RE1LD_???1RF_???0RA_1RA0LH_1LG1LH_???0LJ_1LH1LI_??????_??????` (M12's core with E0, F0, I0 and
states K, L free; 925.4 million nodes, with a compiled macro simulator) listed P12 in its second pass as a halt
conditional on residues; an exact-residue follower then showed that it halts from the blank tape after the seven
gates 0, 0, 0, 0, 0, 0, 1; an independent derivation (own literal simulator, own 2-adic arithmetic, `tools/p12/`)
confirmed it; then the Coq proof. P12 is built on M12, Argon's machine (Argon is a Google Gemini model run by the
repository owner).
