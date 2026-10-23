# h003: a 9-state machine above f_ω⁷(12), four levels above M8

    1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LH0LC_1RG1LD_0RG0RF_0LI---_1RI1RC

Below we call this machine **h003**, its label in the re-screen that found it (section 4). It halts from the blank tape.
Coq proves, with no axioms and with the standard fast-growing hierarchy, that its score σ satisfies

    f_ω(f_ω(f_ω(f_ω(f_ω(f_ω(6·(2↑^13 3) + 2)))))) < σ        (h003_lower)
    f_ω(f_ω(f_ω(f_ω(f_ω(f_ω(f_ω(12))))))) < σ              (h003_lower7_12)

The BB(8) entry M8
([`../BB8/1RB0RA_..._0RG0RF_1RG---.md`](../BB8/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---.md)) has the Coq
upper bound σ(M8) < f_ω(f_ω(6·(2↑^13 3) + 3)) (`m8_bracket`), and f_ω³(12) < σ(M8) < f_ω³(13). So h003's lower bound
has four more applications of f_ω than M8's bracket, and Coq also proves directly that σ is above M8's upper bound
(`h003_beats_m8_bound`). The previous BB(9) entry C7
([`1RB0RA_..._0LI---_1LC0RA.md`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_1LC0RA.md)) is proved above
f_ω⁶(12); h003's proved bound is one f_ω higher (section 2.3 for what is and is not proved about the comparison).
Written 2026-10-22.

h003 runs M8's engine. It differs from M8 only in E0, in H0 and in a new state I:

|   | 0   | 1   |                                                       |
|---|-----|-----|-------------------------------------------------------|
| A | 1RB | 0RA |                                                       |
| B | 1LC | 1LF |                                                       |
| C | 1RD | 0LB |                                                       |
| D | 1RA | 1LE |                                                       |
| E | 0LH | 0LC | M8: 1LH                                               |
| F | 1RG | 1LD |                                                       |
| G | 0RG | 0RF |                                                       |
| H | 0LI | --- | H1 is undefined: the halt. M8: H0 = 1RG               |
| I | 1RI | 1RC | new                                                   |

**Main facts.** N is the number of 1s on the tape when the machine is in state H reading 1. The cell under the head
already holds a 1, so σ = N whatever 1 the halting transition is taken to write (the usual convention is 1RZ).

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `h003_halts : halts tmh c0`. |
| Score | **f_ω⁶(6·(2↑^13 3) + 2) < σ** and **f_ω⁷(12) < σ**, machine-checked (`h003_lower`, `h003_lower7_12`), where 6·(2↑^13 3) + 2 = 12B + 26. |
| Level | f_ω⁷(12) < σ, four f_ω above M8 (f_ω³(12) < σ(M8) < f_ω³(13)). On paper σ < f_ω⁶(12B + c) for a small constant c (not computed); no upper bound is proved. |
| M8 (the BB(8) entry, `../BB8/`) | **Beaten**, machine-checked through M8's Coq upper bound: σ(M8) < f_ω(f_ω(6·(2↑^13 3) + 3)) < σ (`m8_bracket` there, `h003_beats_m8_bound` here). |
| C7 (the previous BB(9) entry) | Proved bound one f_ω higher (f_ω⁷(12) against C7's f_ω⁶(12)). On paper σ(h003) > f_ω(σ(C7)) (section 2.3); not machine-checked, since C7 has no proved upper bound. |
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

M8 = `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---` and h003 agree on states A–D, F, G, on E1 and on H1, the
halt. Both reach H only by E0. M8's E0 = 1LH writes 1 and its H0 = 1RG continues; h003's E0 = 0LH writes 0, and its
H0 = 0LI writes 0 and moves one more cell left into the new state I. I = 1RI / 1RC writes 1 and moves right, to C after a
1 or staying in I after a 0.

**Resync.** Let E read 0 at cell e, with a 0 in the cell e − 1 that H reads. Then

    M8:    E0 (e := 1)  H0 (e−1 := 1)  G1 (e := 0)    F1 (e+1 := 1)  D0 (e := 1)  A1 (e+1 := 0)
    h003:  E0 (e := 0)  H0 (e−1 := 0)  I1 (e−2 := 1)  C0 (e−1 := 1)  D0 (e := 1)  A1 (e+1 := 0)

and both machines are in A at e + 2 with the same tape after six steps, provided the cells e − 2 and e + 1 hold 1. If H
reads 1, both halt. So h003 can leave M8's run only at an E0 event where e − 2 or e + 1 holds 0. The champion's counter
rules and clears contain no E0 at all, and the E0 events of M8's exhaustions and cascade are "good" ones (e − 2 and
e + 1 hold 1), except for the event below. So outside that event h003 runs M8's engine step for step.

**The far-left event.** Once per top-level exhaustion, E reads 0 at the far left of the tape with a blank cell to its
left. There h003 runs H0, then I0 three times (writing three 1s) and I1, and continues differently from M8. These are
the only places where h003 and M8 differ before the endgame.

### 1.2 The run: rebuilding tops

From the blank tape h003 follows M8 to the first clear, J1, at step 2117. The first far-left event comes at step 8110,
at the start of the first exhaustion. From then on, the run is a chain of *tops*. Let Top(K) be the moment when the
digit list is K − 1 zero digits followed by the digit 2 ("0*2 7 1*K"), with t tail blocks. Its clear has depth K − 1 and gives the
accumulator R_a = U_(K−1)^2(0). The exhaustion that follows depends on K mod 5 (with Kb = (3K − 14)/5 and
Ka = (3K − 27)/5):

- **K ≡ 1 (mod 5):** one exhaustion, to Top(K'), K' = 12R_a + (9K + 36)/5.
- **K ≡ 3 (mod 5):** the exhaustion leaves "0 1 (6R_a + 1) (Kb + 8) 1*Kb"; clearing the token Kb + 8 at depth Kb − 1
  gives R_b = U_(Kb−1)^((Kb+7)/3)(0), then a second clear gives R_c = U_Kb^(2R_a)(R_b); a rebuild without E0 then gives
  Top(K'), K' = 12R_c + (3K + 16)/5.
- **K ≡ 4 (mod 5):** the exhaustion leaves "0 1 (6R_a + 5) 2 00 (Ka + 7) 1*Ka"; three clears follow, at depths Ka − 1,
  Ka − 2 and Ka − 1 (the accumulators R_b, then R_c = U_(Ka−2)^(2R_b+3)(0), then R_d = U_(Ka−1)^(2R_a+1)(R_c)); a rebuild
  without E0 gives Top(K'), K' = 12R_d + (3K − 2)/5.
- **K ≡ 0 (mod 5):** the exit (section 1.4).

Every top adds 3 tail blocks. Each rebuilding top has K' ≥ 12R_a, so the depth of the next top's clear is at least the
previous accumulator: each top adds one f_ω. The first top is Top(K₀), K₀ = 12B + 27 (the case K ≡ 1 applied to
Top(11) with R = B).

### 1.3 The real orbit

Every accumulator, B included, is a clear of depth at least 2, so 2R + 4 is a power tower of 2s of height at least 20.
Such towers are constant modulo 2^6·3^4·5^14 from height 16 on, so every accumulator is ≡ ρ = 5059528974366 modulo
M = 2^5·3^4·5^14 (`Res.U_res`, the same file as C7's). Writing each accumulator as M·q + ρ makes every quantity of
section 1.2 an explicit linear form in the q's. Then every division above is exact, and

    K₀ ≡ 4,  K₁ ≡ 3,  K₂ ≡ 1,  K₃ ≡ 1,  K₄ ≡ 0   (mod 5),

so the run makes four rebuilding tops (branches 4, 3, 1, 1) and exits at Top(K₄), with t = 15. Also K₄ is odd and
≡ 0 (mod 3), and K₄ = 10h + 15 (`HArith.v`). All of this comes from ρ alone.

### 1.4 The exit: M8's endgame

At Top(K₄) the clear gives R_e = U_(K₄−1)^2(0), and the exhaustion that follows has the far-left event at its start.
After it, h003 reaches the first moment of M8's cascade, D0f(16, 3K₄ − 1, 2, …), equal to the configuration M8 would
have at that moment with one more block in the far field (y + 1). After one more sub-step the cascade starts on a run of
L₁ = 3J + 1 ones (3K₄ − 1 = 5J + 24), which is odd and ≡ 1 (mod 3), with a parked list of about 12R_e blocks.

From there on, every E0 event is a good one, so h003 is M8 step for step: M8's cascade, its escape and its endgame (keys
31, 37, 43, 49, 55), which halt in every residue class (C04's and M8's Coq development proves this for every class). So
h003 halts where M8 run from that configuration halts, with M8's halting tape. The far field, where the two runs differ,
is never read again.

---

## 2. The score

### 2.1 What Coq proves

The files to read are [`verify_h003/h003/Defs.v`](verify_h003/h003/Defs.v) and
[`verify_h003/h003/Statement.v`](verify_h003/h003/Statement.v), with busycoq's `TM.v`. `Defs.v` defines `tmh`, `ones`,
`iter`, `arrow`, `f` and `f_omega`; from the ones count on, it has the same text as M8's `Defs.v`. `Statement.v` states:

    Statement.h003_table          : String.length h003_string = 62 /\
                                    forall q s, tmh (q, s) = parse_slot h003_string (st_idx q) (sym_idx s)
    Statement.h003_halts          : halts tmh c0
    Statement.h003_lower          : forall c N, c0 -[ tmh ]->* c -> halted tmh c -> ones c N ->
                                      f_omega (f_omega (f_omega (f_omega (f_omega (f_omega (6 * arrow 13 2 3 + 2)))))) < N
    Statement.h003_lower7_12      : forall c N, c0 -[ tmh ]->* c -> halted tmh c -> ones c N ->
                                      f_omega (f_omega (f_omega (f_omega (f_omega (f_omega (f_omega 12)))))) < N
    Statement.h003_beats_m8_bound : forall c N, c0 -[ tmh ]->* c -> halted tmh c -> ones c N ->
                                      f_omega (f_omega (6 * arrow 13 2 3 + 3)) < N

The comparison with M8 is the chain of `m8_bracket` (in `../BB8/verify_m8`) and `h003_beats_m8_bound` (here). The two
`Defs.v` define `f_omega` and `arrow` with the same text, which CI checks by `diff`.

### 2.2 Where the six f_ω come from

- **The endgame (two levels).** M8's endgame ends with at least 6R_l + 2 ones, where R_l ≥ U_K^2(0) for a clear depth K
  at least the parked count minus 1000, which is at least R_e. Since f_ω(a) + 2 ≤ R_e for every a ≤ K₄ − 1, `S1_core`
  gives f_ω(f_ω(a)) < σ for every a ≤ K₄ − 1 (`HScore.x_goal`; this is f3_0RC's score file with h003's top).
- **The four rebuilding tops (four levels).** R_(a,i) = U_(K_i−1)^2(0) is the clear of Top(K_i), and
  K_(i+1) − 1 ≥ R_(a,i) in every branch. So x ≤ K_i − 1 gives f_ω(x) + 2 ≤ R_(a,i) ≤ K_(i+1) − 1, and
  f_ω⁴(12B + 26) ≤ K₄ − 1, since K₀ − 1 = 12B + 26 (`HGoal.chain4`).
- Together: f_ω⁶(12B + 26) < σ, and 12B + 26 = 6·(2↑^13 3) + 2. For f_ω⁷(12): f_ω(12) = f_12(12) ≤ U_10(12) ≤ B
  (f_(k+2) ≤ U_k, `HGoal.fw12_le_Bx`), so f_ω⁴(f_ω(12)) ≤ K₄ − 1 as well. No monotonicity of f_ω is needed. For
  `h003_beats_m8_bound`: K₄ − 1 ≥ 12B + 27.

The intermediate clears of the branches K ≡ 3, 4 (R_b, R_c, R_d) are not counted as levels: their depths are linear in
K, not in the previous accumulator.

### 2.3 Comparison with C7 (on paper)

C7's Coq bound is f_ω⁶(12) < σ(C7). From C7's run rules (its write-up, section 1.2), every clear satisfies
R ≤ f_ω(depth + small), which gives σ(C7) ≤ f_ω⁵(5.4B + 12) on paper, so σ(h003) > f_ω⁶(12B + 26) > f_ω(σ(C7)). This
upper bound for C7 is not machine-checked, so "h003 beats C7" is a paper statement; what Coq proves is that h003's lower
bound is one f_ω above C7's.

---

## 3. Verification

### 3.1 How the proof is organised

[`verify_h003/`](verify_h003/) holds the development: Coq 8.20.1 on busycoq (commit `bd2e36f`), 66 files and a probe, no
axioms. Like f3_0RC's and C7's proofs, it runs on an auxiliary 11-state machine:

    C04 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF                (verify_c04)
    X3  = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LJ0LC_0RG1LD_0LH1LH_1RI---_0RI0RF_0LK---_1RK1RC    (verify_h003/dev/Base.v)

X3 is C04 with E0 = 0LJ, J = 0LK / halt and K = 1RK / 1RC: h003's H and I. C04 is M8 with M8's F0 = 1RG split into three
steps; on X3, h003's H is J, its I is K and its G is C04's I (`h003/Sim.v`).

The key point is the resync of section 1.1, in C04's form: at a good E0 event C04 runs E0 H0 I1 F1 D0 A1 and X3 runs
E0 J0 K1 C0 D0 A1, six steps each, with the same configuration after them. So in `dev/Base.v` the tactic `step` is one
raw X3 step, and C04's generated proof scripts, which count raw steps, replay on X3 with the same counts wherever their
E0 events are good. This is why the whole of C04's cascade and endgame is reused:

- 33 files are byte-identical to [`verify_f3/`](verify_f3/) (C04's tree as ported there: the champion rules, the
  token layer, the cascade, the endgame and the key-31 files, including the two longest, `k31/K_e1.v` and
  `dev/G_sub2.v`), and 5 more are `verify_f3`'s with only the halting tape changed (X3 halts after E0 = 0LJ, so the cell
  right of the halting head holds 0 instead of 1);
- 5 files are byte-identical to [`verify_c7/`](verify_c7/): `Res.v` (the tower residue), the generic token layer
  `KStep.v`, `Ones.v`, and the rebuild without E0 (`G_pbab.v`, `G_pbc.v`);
- `port_check.sh` checks all of this.

New for h003:

- **Generated machine lemmas** (the symbolic executor of C04's development, run on X3): the K ≡ 1 top
  (`G_t1_*.v`: `T1a1`, `T1a2a`, then the far-left loop by one round `YR` and its end `YE`, then `T1b`), the K ≡ 3 and
  K ≡ 4 exhaustions (`G_tops_P3.v`, `G_tops_P4.v`, `G_tops_P4b.v`), the exit (`G_tops_TXa.v`) and the first cascade
  sub-step for a run of length 5J + 24 (`G_xt1.v`).
- **`HTop.v`**: the four kinds of top as theorems on tokens (`T1`, `T3`, `T4`, `TX`), the orbit with the residues of
  `HArith.v`, and `reach_D0_top`: the blank tape reaches the cascade moment.
- **`HFinal.v`**: `x_halts`, from f3_0RC's endgame theorem (`Endgame.halts_from_reach`, generalised there over the parked
  margin) and C04's key-31 endgame.
- **`HScore.v`, `HGoal.v`**: the score of section 2.2.
- **`h003/`**: `Defs.v`, `Sim.v` (the simulation, a port of C7's), `Final.v` (the transfer to h003, with the bridges
  between `Defs.v`'s definitions and the development's taken at variable arguments only) and `Statement.v`.

`probe.v` checks the 18 table entries by conversion and against the parser of the literal string. It also prints `c0`,
`tape0` and the definitions. It states the four main results as one conjunction with qualified names (`h003_all_ok`),
and runs `Print Assumptions` on it and on each theorem of `Statement.v`. All six report "Closed under the global
context".

### 3.2 Build

`verify_h003/compile_clean.sh` builds everything from scratch, then runs the probe. The GitHub workflow (job `bb9-h003`)
runs it whenever these files change, and weekly. It also runs `port_check.sh` and diffs `h003/Defs.v` against M8's
`Defs.v`. Timings and the recorded local build are in [`verify_h003/README.md`](verify_h003/README.md).

### 3.3 Not machine-checked

- **σ = N.** In Coq the halt is the undefined transition H1, and `ones` counts the 1s of the halted configuration.
- **The M8 comparison as one theorem.** It is the chain of the two theorems in section 2.1.
- **The comparison with C7** (section 2.3), and the upper bound σ < f_ω⁶(12B + c).
- **The step numbers** 2117 and 8110 of section 1.2, and the description of the K ≡ 0 (mod 5) exit as "M8 with y + 1",
  come from literal runs; the proof uses its own lemmas for the exit.

---

## 4. Discovery and credit

- **Found** by re-screening this project's set of 9-state extensions of M8 (the screen that found C7) in
  residue-faithful worlds: simulations whose accumulators have the real tower residues modulo powers of 5 and 3600, so
  that the branch taken at each top is the real one. h003 is C7's sibling with I = 1RI / 1RC and E0 = 0LH. The top map,
  the real orbit [4, 3, 1, 1, 0] and the exit were then re-derived with independent simulators, and checked on grids of
  parameters (every residue of K mod 125, several t and R) and on 399 exit runs covering every endgame key and class.
- **Proved** in Coq in this project (2026-10-22), with the tools of C04's, f3_0RC's and C7's developments. Section 5 of
  C04's write-up gives the credits for those tools.
- **Built on** the BB(7) champion of Kropitz (2025; analysed by Ligocki), whose counter h003 runs, and on C04 and M8,
  whose engine and endgame it shares.
