# C7: a 9-state machine at f_ω⁴, two levels above M8

    1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_1LC0RA

Below we call this machine **C7**, its label in the screen that found it (section 4). It halts from the blank tape. Coq
proves, with no axioms and with the standard fast-growing hierarchy, that its score σ satisfies

    f_ω(f_ω(f_ω(f_ω(6·(2↑^13 3) + 3)))) < σ        (c7_lower)

The BB(8) entry M8
([`../BB8/1RB0RA_..._0RG0RF_1RG---.md`](../BB8/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---.md)) has the Coq
upper bound σ(M8) < f_ω(f_ω(6·(2↑^13 3) + 3)) (`m8_bracket`). So C7 beats M8 by two applications of f_ω. It also beats
f3_0RC ([`1RB0RA_..._0LI---_0RC1RF.md`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_0RC1RF.md)), which is at
M8's level. Written 2026-10-22.

C7 runs M8's engine. It differs from M8 only in state H and in a new state I:

|   | 0   | 1   |                                             |
|---|-----|-----|---------------------------------------------|
| A | 1RB | 0RA |                                             |
| B | 1LC | 1LF |                                             |
| C | 1RD | 0LB |                                             |
| D | 1RA | 1LE |                                             |
| E | 1LH | 0LC |                                             |
| F | 1RG | 1LD |                                             |
| G | 0RG | 0RF |                                             |
| H | 0LI | --- | H1 is undefined: the halt                   |
| I | 1LC | 0RA | read at every exhaustion (after E0 and H0)  |

**Main facts.** N is the number of 1s on the tape when the machine is in state H reading 1. The cell under the head
already holds a 1, so σ = N whatever 1 the halting transition is taken to write (the usual convention is 1RZ).

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `c7_halts : halts tm7 c0`. |
| Score | **f_ω⁴(6·(2↑^13 3) + 3) < σ**, machine-checked (`c7_lower`), where 6·(2↑^13 3) + 3 = 12B + 27. |
| Level | f_ω⁵(12) < σ, on paper: f_ω(12) < 12B + 26 (C04's `Bx_fw`), and f_ω is increasing. No upper bound is proved. |
| M8 (the BB(8) entry, `../BB8/`) | **Beaten**, machine-checked through M8's Coq upper bound: σ(M8) < f_ω(f_ω(6·(2↑^13 3) + 3)) < σ (`m8_bracket` there, `c7_beats_m8_bound` here). |
| f3_0RC, C04, fw2 (this folder) | Beaten: they are at M8's level or below. |
| n1 (`../BB10/`, f_(ω+1)) | **Not** beaten. |
| Steps | Not computed. |

---

## 1. How it works

The notation is that of C04's write-up
([`1RB0RA_..._1RI---_0RI0RF.md`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF.md), section 1.1).
Kt(list; m; r; t) is the digit-list counter of the BB(7) champion. It consists of tokens D(d) = (10)^d 1, the token m,
an accumulator run (10)^r and t tail blocks. A digit d is the token 3d + 1. U_j is the clear of a digit list of depth j,
with 2·U_j(x) + 4 = 2↑^(j+1)(2x + 4). B is C04's and M8's first accumulator, with 2B + 4 = 2↑^13 3.

### 1.1 Relation to M8

M8 = `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---` and C7 agree on states A–G and on H1, the halt. M8
reaches H only by E0 = 1LH, that is, at an exhaustion, when the digit list is used up. There M8's H0 = 1RG continues its
rebuild. C7's H0 = 0LI writes 0 and looks one cell further left, with I:

- if that cell is blank, I0 = 1LC writes a 1 there and moves left in C;
- if it holds a 1, I1 = 0RA erases it and moves back right in A.

Either way, C7 leaves M8's run at its first exhaustion and never returns to it. The champion's counter rules and its
clears contain no E0, so between exhaustions C7 still runs M8's engine. Every exhaustion of C7, including every step
of its endgame cascade, is C7's own.

### 1.2 The run

The run alternates *clears* and *exhaustions*. In a clear, the champion's counter empties a digit list and produces an
accumulator U_j^v(…). In an exhaustion, the head reaches the far end with every digit zero and rebuilds a list from the
accumulator. Each exhaustion below was checked on literal runs for many parameter values. Each is a lemma of the Coq
proof that is parametric in its inputs.

- **P0, start.** As in M8, the blank tape reaches Kt(1^11; 1; 3B + 2; 0). This is the first exhaustion, with n = 11
  zero digits.
- **Exhaustions of type A (n ≡ 1 mod 5).** Start from Kt(1^n; 1; 3R + 2; t) and let K = (27R + 3n + 10)/5. A loop at the
  far left turns the accumulator into a run of D(1) tokens, and one more pass divides that run by 5. The result has one
  non-zero digit, the token K + 5, behind K − 2 zero digits, a single-1 frame at the far end, and t + 2 tail blocks.
  Clearing it gives the next accumulator.
- **Exhaustions of type B (single-1 frame, no E0).** Every second exhaustion is of this type. It rebuilds the list
  1^(12R + n + 4) followed by the digit 2, and the frame is again 11. Clearing the digit 2 at depth 12R + n + 4 gives the
  next accumulator.
- **J1–J5.** With n = 11 and R = B, the exhaustions alternate A, B, A, B:

      K₂ = (27B + 43)/5,             R₁ = U_(K₂−2)^((K₂+4)/3)(0)
      K₃ = 12R₁ + K₂ + 4,            R₂ = U_(K₃−1)^2(0)
      K₄ = (27R₂ + 3K₃ + 10)/5,      R₃ = U_(K₄−2)^((K₄+4)/3)(0)
      K₅ = 12R₃ + K₄ + 4,            R₄ = U_(K₅−1)^2(0)

- **J6, an exhaustion of type C (n ≡ 3 mod 5).** With n = K₅ ≡ 3 (mod 5), let K₆ = (27R₄ + 3K₅ + 44)/5. Behind the
  frame 11, the exhaustion writes the tokens 1 and 7, a gap 00, the digit token K₆ − 12, and K₆ − 1 zero digits. Clearing
  that digit gives R₅ = U_(K₆−1)^((K₆−13)/3)(0).
- **The counter (J7 onward).** The next exhaustion has no E0. It leaves a counter token C = 6R₅ + 12 next to a digit 2,
  behind N = K₆ − 3 zero digits. Each round clears the deposited digit at depth N (R → U_(N+1)(R)), borrows 3 from C, and
  deposits a new digit 6R' + 7. After 2R₅ + 3 rounds, C = 3 and R₉ = U_(N+1)^(2R₅+3)(0). Three more clears and two short
  exhaustions follow. They eat the far frame and leave Kt(1^N; 1; 3R₁₀ + 2; 6) with nothing to its left.
- **C7's cascade.** The last exhaustion parks a list of P = 12R₁₀ + 8 blocks and starts a cascade on a run of
  L₁ = 3N − 4 ones. Each step is one exhaustion of C7, with one I1 event, and maps

      L → (3L + c_r)/5,   r = L mod 5,   c_1 = −23, c_3 = −14, c_0 = −20, c_4 = −32.

  Each step takes 4 or 6 parked blocks and deposits one token at the far end. These constants differ from M8's. In
  particular, r = 0 is an ordinary step in C7, not a stop. The case r = 2 is the halting branch.
- **The r = 2 branch and the halt.** Every step of the orbit below lands on L ≡ 2 (mod 3), so at r = 2 we have
  L = 15u + 17. The branch runs u rounds. Each round takes 15 cells from the run and 4 parked blocks, and deposits a
  token D(4). The branch then eats the leftover run of 18u + 23 ones in blocks of 5. If 18u + 23 ≡ 4 (mod 5), that is if
  u ≡ 2 (mod 5), the head ends on H reading 1 and the machine halts. In literal runs from small L, the branch halts for
  u ≡ 1, 2 (mod 5) with u ≥ 2, and continues otherwise.

### 1.3 Residues

Every accumulator above, B included, is a clear of depth at least 2. So 2R + 4 is a power tower of 2s of height at least
20. Such towers are constant modulo 2^6·3^4·5^14 from height 16 on, so every accumulator is ≡ ρ = 5059528974366 modulo
M = 2^5·3^4·5^14 (`Res.U_res`). Write each accumulator as M·q + ρ. Then every quantity above is an explicit linear form in
the q's, and every division by 5 is exact:

- K₂ and K₄ are exact, and K₃ ≡ 1, K₅ ≡ 3 (mod 5), so J1 and J3 are of type A and J5 is of type C;
- N = K₆ − 3 is a multiple of 5 (N ≡ 8136900 mod 5^10), so the cascade starts with r = 1;
- the orbit takes r = 1, 3, 0, 3, 4, 0, 0, 3 and reaches L₉ ≡ 4805222 (mod 5^11) with L₉ ≡ 2 (mod 3). So
  L₉ = 15u + 17 with u ≡ 2 (mod 5), which is the halt.

All of these residues come from ρ alone. So C7's run does not depend on anything uncomputable, unlike M8's run, whose
endgame class depends on residues of B that the cascade reaches only far down.

---

## 2. The score

### 2.1 What Coq proves

The files to read are [`verify_c7/c7/Defs.v`](verify_c7/c7/Defs.v) and
[`verify_c7/c7/Statement.v`](verify_c7/c7/Statement.v), with busycoq's `TM.v`. `Defs.v` defines `tm7`, `ones`, `iter`,
`arrow`, `f` and `f_omega`; from the ones count on, it has the same text as M8's `Defs.v`. `Statement.v` states:

    Statement.c7_table          : String.length c7_string = 62 /\
                                  forall q s, tm7 (q, s) = parse_slot c7_string (st_idx q) (sym_idx s)
    Statement.c7_halts          : halts tm7 c0
    Statement.c7_lower          : forall c N, c0 -[ tm7 ]->* c -> halted tm7 c -> ones c N ->
                                    f_omega (f_omega (f_omega (f_omega (6 * arrow 13 2 3 + 3)))) < N
    Statement.c7_beats_m8_bound : forall c N, c0 -[ tm7 ]->* c -> halted tm7 c -> ones c N ->
                                    f_omega (f_omega (6 * arrow 13 2 3 + 3)) < N

The comparison with M8 is the chain of `m8_bracket` (in `../BB8/verify_m8`) and `c7_beats_m8_bound` (here). The two
`Defs.v` define `f_omega` and `arrow` with the same text, which CI checks by `diff`.

### 2.2 Where the four f_ω come from, and why not five

At the halt the tape holds the parked list, about 12R₁₀ blocks with two 1s each, so σ > R₁₀. Let a = 12B + 27. Then:

- R₂'s clear has depth K₃ − 1 > a, so f_ω(a) ≤ R₂.
- R₃'s clear has depth K₄ − 2 > R₂ + 2, so f_ω(f_ω(a)) < R₃. This uses `Score.S1_core`: f_ω(x) + 2 ≤ K implies
  f_ω(f_ω(x)) < U_K(0).
- R₄'s depth K₅ − 1 > 12R₃ gives f_ω³(a) < R₄, and R₅'s depth K₆ − 1 > R₄ gives f_ω⁴(a) < R₅.
- R₅ ≤ R₉ ≤ R₁₀ < σ.

The clears after R₅ run at depth about N ≈ 5.4·R₄, a level below f_ω⁴(a), iterated about 2R₅ times. A fifth f_ω would
need a clear whose level is above R₅, and C7 has none. On paper these clears give roughly f_(R₄)(R₅). That is more than
f_ω⁴(a), but not provably f_ω⁵(a). The f_ω⁵(5B) estimate in the screening notes is therefore not claimed: we claim and
prove f_ω⁴(12B + 27) only.

---

## 3. Verification

### 3.1 How the proof is organised

[`verify_c7/`](verify_c7/) holds the development: Coq 8.20.1 on busycoq (commit `bd2e36f`), 43 files and a probe, no
axioms. Like f3_0RC's proof ([`verify_f3/`](verify_f3/)), it runs on an auxiliary 11-state machine:

    X' = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LJ0LC_0RG1LD_0LH1LH_1RI---_0RI0RF_0LK---_1LC0RA

X' is C04 with E0 = 1LJ, J = 0LK / halt and K = 1LC / 0RA. In other words, it is f3_0RC's auxiliary machine X with K's
row replaced by C7's state I.

Every exhaustion of C7 is new, so only three files of C04's development are reused: the champion rules
(`dev/G_rules.v`), the token layer (`dev/Abs.v`, with the first 2369 steps and the clears) and the cascade moment
(`dev/Lift.v`). `port_check.sh` checks these against `../verify_c04`. `lib/`, `score/Score.v` and, up to K's row,
`dev/Base.v` are those of `../verify_f3`.

- **Generated machine lemmas.** These come from the symbolic executor of C04's development, run on X' and counting raw
  X' steps. Each is parametric in the run lengths and proved by stepping and by induction over repeated blocks.
  - Types A and C: `PA1`, `PA2`, `PC2`.
  - Type B: `PBab`, `PBc`.
  - The counter's exhaustion, its last borrow and its end: `PD`, `R30`, `E2`, `E3`.
  - The cascade: `ENTRY1` (the entry with its first step), `SUB3`, `SUB0`, `SUB4`.
  - The r = 2 branch: `R2A1` (its first pass), `PRE`, `ROUND` (one round), `VHq` (the end of the last round), `VH2b`
    (the halt).
- **Abstract files.**
  - `C7Phases`, `C7PhB`, `C7Count`, `C7Casc` and `C7Entry` restate these lemmas on token configurations. `C7Count`
    handles the counter by induction on rounds.
  - `C7Top` chains J1 to the step-9 cascade moment.
  - `C7Halt` does the r = 2 branch, with its u rounds by induction.
  - `C7Final` puts it together: X' halts with N ones, and f_ω⁴(12B + 27) < N.
- **Residues.**
  - `Res.v` proves the tower residue, by a Carmichael chain of 16 moduli and the stdlib's verified modular
    exponentiation.
  - `C7Arith.v` was generated from the run's linear formulas. It proves every exact division and the residues of
    section 1.3, using explicit linear forms in the q's.
- **Score.** `C7Score.v` uses `score/Score.v` (`S1_core`, f_k ≤ U_k).
- **Simulation.** `c7/Sim.v` maps C7's states A..F → A..F, G → I, H → J, I → K. C7's F0 = 1RG is X''s F0, G, H0, and
  every other step is one X' step. C7 halts exactly where X' does, on the same tape.

`probe.v` checks the 18 table entries by conversion and against the parser of the literal string. It also prints `c0`,
`tape0` and the definitions. It states the three main results as one conjunction with qualified names (`c7_all_ok`), and
runs `Print Assumptions` five times. All five report "Closed under the global context".

### 3.2 Build

`verify_c7/compile_clean.sh` builds everything from scratch, then runs the probe. The GitHub workflow (job `bb9-c7`)
runs it whenever these files change, and weekly. It also runs `port_check.sh` and diffs `c7/Defs.v` against M8's
`Defs.v`. Timings and the recorded local build are in [`verify_c7/README.md`](verify_c7/README.md).

### 3.3 Not machine-checked

- **σ = N.** In Coq the halt is the undefined transition H1, and `ones` counts the 1s of the halted configuration.
- **f_ω⁵(12) < σ** (section 2.2). It composes C04's `Bx_fw` with `c7_lower` and the monotonicity of f_ω.
- **The M8 comparison as one theorem.** It is the chain of the two theorems in section 2.1.
- **The u ≡ 1, 2 (mod 5) criterion for general L** (section 1.2). It was observed on literal runs. The proof uses only
  the real class u ≡ 2 (mod 5).

---

## 4. Discovery and credit

- **Found** by this project's screen of 9-state extensions of M8 (2026-10-20). The screen tried M8 with H0 = 0LI and
  each choice of the new state I, and re-ran the candidates with a counter-aware simulator. The structure of the run
  (phases, cascade, the r = 2 branch) was then derived and checked on literal runs whose parameters lie in the real
  residue classes. An independent simulator reproduced the chain J1–J6 and the counter on parameter grids, and computed
  the same residues. The twins `…_1LI---_0RC{1RA,0RF,1LG}` were listed with C7 in the screen; they are not proved here.
- **Proved** in Coq in this project (2026-10-22), with the tools of C04's and f3_0RC's developments. Section 5 of C04's
  write-up gives the credits for those tools.
- **Built on** the BB(7) champion of Kropitz (2025; analysed by Ligocki), whose counter C7 runs, and on C04 and M8,
  whose engine it shares.
