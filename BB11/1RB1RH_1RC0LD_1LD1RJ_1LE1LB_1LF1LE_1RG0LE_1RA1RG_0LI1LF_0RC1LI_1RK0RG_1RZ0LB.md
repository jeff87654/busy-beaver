# C4: an 11-state machine at level f_(ω+2), two loops deep

    1RB1RH_1RC0LD_1LD1RJ_1LE1LB_1LF1LE_1RG0LE_1RA1RG_0LI1LF_0RC1LI_1RK0RG_1RZ0LB

| start-A | 0 | 1 | M12 name | |
|---|---|---|---|---|
| A | 1RB | 1RH | B | |
| B | 1RC | 0LD | I | |
| C | **1LD** | 1RJ | E | M12-named E0 = `1LJ` (M12: `1LK`) |
| D | 1LE | 1LB | J | |
| E | 1LF | 1LE | H | |
| F | 1RG | 0LE | G | |
| G | 1RA | 1RG | A | |
| H | 0LI | 1LF | C | |
| I | 0RC | 1LI | D | |
| J | **1RK** | 0RG | F | M12-named F0 = `1RK` (M12: `1RG`) |
| K | 1RZ | **0LB** | K | K0 is the halt, as in M12; M12-named K1 = `0LI` (M12: `0LL`) |

C4 is the 12-state machine M12 ([`../BB12/`](../BB12/)) with its state L removed and three transitions changed.
In M12's state names it is `1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LJ1RF_1RK0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LI`, started in
state B. The string above is the same machine with the states renamed in order of first visit, so that it starts in
A; the map is A>G B>A C>H D>I E>C F>J G>F H>E I>B J>D K>K (M12 name > start-A name), and the Coq proof is about the
start-A table. The halting transition K0 is undefined in the Coq table (`---`); it is written `1RZ` here.

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB11_C4.halt`. |
| Exact score | Machine-checked formula: N = u + 3 + p ones when K0 is read, where (p, u) = `nFIN` is given by the recursion of section 2 (`score_exact`). K0 is read on a 0 and the halting transition writes a 1, so σ = N + 1. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+2)(f_(ω+2)(f_5(34))) < N (`sigma_lower_bound`), and f_(ω+2)(f_(ω+2)(34)) < N (`sigma_lower_bound_34`). |
| M11b (previous BB(11) entry) | **In Coq, against its exact score**: M11b's proved upper bound N_M11b + 1 < f_(ω+1)(f_ω(f_ω(6))) (`sigma_bracket_m11`, with σ(M11b) = N_M11b + 1) is below C4's N (`beats_M11b`); `beats_M11b_score` (`BB11_C4_cmp.v`) joins the two statements, loading M11b's proof files: NM + 1 < N for the numbers of ones on the two halting tapes. |
| M12 (BB(12) entry) | **In Coq, against its exact score** (`BB11_C4_vs_M12.v`): M12's halting tape holds exactly fst pb2 + snd pb2/2 + 3 ones (M12's `score_exact`), proved here to be at most f_(ω+2)(4·f_(ω+1)^6(12)) + 3, below C4's N (`beats_M12_exact`, `beats_M12_score`). Both halt reading a 0, so σ(C4) > σ(M12) and BB(12) ≥ BB(11) + 1 > σ(M12). `beats_M12_lower` compares with M12's proved lower bound only. |
| Steps | Not computed. |

## 1. How it works

C4 keeps M12's engine: the configurations `Ca` and `Ch`, the engine W (W_0(b) = b + 3, W_(j+1)(b) = W_j^(b+1)(2)),
and the rules `CA_SH`, `CA_EXIT`, `CA_CH`, `CH_CA` are M12's, re-proved for this table with the states renamed. What
is new is how the engine is fed. The left block (10)^p of the tape is turned into a run of zeros, and that run is the
counter of an f_(ω+1) loop (lemma names from `BB11_C4.v`):

- **STOCK** takes two pairs from a stock [1;0]^d on the right and starts a conversion; **CONV** (`CONV_iter`) turns
  each pair of the left block into two zeros, and **RESTART** gives `Z 1 3 (2p+1) y`: the engine facing a run of
  2p + 1 zeros.
- **ZSTEP** eats four zeros per step, with one engine application in which the output becomes the next W index:
  Zs (j, b) = (j + b/2 + 1, W (j + b/2) (W (j−1) 1)). Iterated (`ZLOOP`) this is the f_(ω+1) loop.
- **ZEND**: when three zeros are left, the engine absorbs the rest of the stock block into the left block. One
  **ROUND** = STOCK, conversion, Z loop, ZEND takes (p, u) to `Rnd (p, u)`; iterating rounds (`ROUNDS`) over a stock
  is the f_(ω+2) loop. The invariant p odd, u ≡ 1 (mod 4) holds from round to round (`Rnd_inv`).
- **HALT**: when the stock is used up, `X p u (1 0 0^∞)` runs into K reading a blank: the halt, with u + 3 + p ones.

The halt hinges on two parities, both settled by `W_mod4` (for j ≥ 2, W_j(b) ≡ 3 − (b mod 2) mod 4) and `W_par`.

## 2. The run

From the blank tape, 150 steps and a few engine rules reach `Ca 5 (W 5 (W 2 4)) (1 0^∞)` (`boot_ca`); W_5(W_2(4)) =
W_5(1091) is ≡ 2 (mod 4) (`W5_mod`). The opening then builds the **first stock**, a1 = W_5(1091)/4 copies of
[1;0;1;0], behind a "1 1" sentinel (`boot_gen`). With

    nT3 = Zs^3 (1, 3),   nQ1 = Rnd^a1 (nT3 + (0, 2)),
    nM1 = Zs^(p/2 + 1) (1, 3) for (p, u) = nQ1,   then the second stock of nc2 = (second coordinate of nM1)/4 pairs,
    nFIN = Rnd^nc2 (Zs^ns2 (1, 3) + (0, 2)),

the machine runs a1 rounds on the first stock (`run_Q1`), meets the sentinel, makes the **second stock** from the
accumulator (`T2`, `T3`, `MID`; its length is odd because the accumulator is ≡ 3 mod 4), runs nc2 rounds on it, and
halts by HALT at `c_end p u` with (p, u) = `nFIN` (`run_FIN`, `score_exact`). If the second stock had even length,
the last Z loop would face the blank tape and never end; the proof shows it is odd.

Each round is at least one f_(ω+1) step on the left block (`Rnd_dom`), so the a1 rounds of the first stock give
f_(ω+2)(a1) and the second stock, longer than f_(ω+2)(a1), gives f_(ω+2)(f_(ω+2)(a1)); with a1 ≥ f_5(34) (`a1_ge`) this is
`sigma_lower_bound`.

## 3. Verification

[`verify_c4/`](verify_c4/): busycoq `bd2e36f`, Coq 8.20.1, built in CI (job `bb13-bb14`). `probe.v` re-checks the
transition table entry by entry against the string above (22 checks generated from the string) and the blank start
configuration, prints the definitions the statements use, and confirms that `halt`, `score_exact`,
`sigma_lower_bound`, `sigma_lower_bound_34`, `beats_M11b`, `beats_M12_lower`, `beats_M11b_score`, `beats_M12_exact` and
`beats_M12_score` are closed under
the global context. The main proof also passes this project's `check.py` (the statement `halts tm c0` read from the
file, the table compared with the machine string, `Print Assumptions halt` closed), 2026-11-13.

`BB11_C4.v` and `BB11_C4_bound.v` are this project's files, unchanged except for line endings. `BB11_C4_cmp.v` (the
joined comparison with M11b) was written for this entry; it loads M11b's three proof files, byte-identical copies of
[`verify/multifile/`](verify/multifile/). `BB11_C4_vs_M12.v` (the comparison with M12, written as `BB11_C4_cmp.v` in
the project's notes; first comment line changed for the new name) loads byte-identical copies of M12's files from
[`../BB12/verify_m12/multifile/`](../BB12/verify_m12/multifile/).

There is no independent simulator for this write-up in the repository; the finder's exact macro simulator and
literal checks are described in the working notes, and every rule cited here is a lemma of the Coq file.

## 4. Comparisons

- **M11b (BB(11))**: above its exact score, in Coq (above).
- **M12 (BB(12)), in Coq against its exact score** (`BB11_C4_vs_M12.v`, which loads M12's proof files): from the
  definitions of M12's maps (the same W, Kc, Kc_full, Kd_step, Kd_iter and D_reload as in M13b; the argument is that of
  the BB(13) comparison file), M12's exact count is at most f_(ω+2)(4·f_(ω+1)^6(12)) + 3, below C4's lower bound
  (`beats_M12_exact`, `beats_M12_score`). With BB(12) ≥ BB(11) + 1 (redirect the halt into one new state that writes a
  1), C4 gives a 12-state score above M12's. M12's row is kept as the 12-state machine of record here, with a note,
  as for BB(17).
- Not yet reviewed by the bbchallenge community.

## Credit

Found and proved in Coq by this project (the repository owner's work with Claude models as agents), 2026-11-12/13:
an exact macro enumeration of M12's 10-state core plus one state (about 2.07 million nodes) found C4, and a separate
agent wrote the Coq proof and the comparison with M12. C4 is built on M12, Argon's 12-state machine.
