# M8: an 8-state machine with f_ω(f_ω(f_ω(12))) < σ < f_ω(f_ω(f_ω(13)))

    1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---

Below we call this machine **M8**. It halts from the blank tape, and Coq proves, with no axioms and with the
standard fast-growing hierarchy, that its score σ satisfies

    f_ω(f_ω(f_ω(12))) < σ < f_ω(f_ω(f_ω(13)))        (m8_fgh3)

More precisely, f_ω(f_ω(12B + 26)) < σ < f_ω(f_ω(12B + 27)) with 2B + 4 = 2↑^13 3 (`m8_fgh_bracket`, `Bx_knuth`;
12B + 26 lies strictly between f_ω(12) and f_ω(13)). As an easier placement, f_(ω+1)(3) < σ < f_(ω+1)(4), where
f_(ω+1)(n) = f_ω^n(n) (`m8_fgh_coarse`). Coq also gives σ exactly: it is `sigma_c04`, an explicit symbolic recursion
along the run (`m8_score_exact`), and it beats the exact score 12·(2↑^37 3) + 59 of the previous BB(8) entry of this folder
([`1RB0RA_..._1RG1LF`](1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_1LC0RH_1RG1LF.txt)), which M8 supersedes
(`m8_beats_champ35`, `m8_beats_bb8r`). Written 2026-10-18.

M8 was obtained by reducing a 9-state machine, C04
([`../BB9/1RB0RA_..._1RI---_0RI0RF.md`](../BB9/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF.md)):
C04 spends two states on a gadget that M8 does in one transition. The two machines run the same computation and halt
on the same tape, so they have the same score, and M8's proof is built on C04's. Directly, M8 is the BB(7) champion
`1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_0RG0RF` (Kropitz 2025) with its halting transition E0 redirected to a new
state H (E0 = 1LH), where H0 = 1RG does what the champion's F0 does and H1 is the halt.

|   | 0   | 1   |                           |
|---|-----|-----|---------------------------|
| A | 1RB | 0RA |                           |
| B | 1LC | 1LF |                           |
| C | 1RD | 0LB |                           |
| D | 1RA | 1LE |                           |
| E | 1LH | 0LC |                           |
| F | 1RG | 1LD |                           |
| G | 0RG | 0RF |                           |
| H | 1RG | --- | H1 is undefined: the halt |

**Main facts.** N is the number of 1s on the tape when the machine is in state H reading 1. The cell under the head
already holds a 1, so whatever 1 the halting transition is taken to write (the usual convention is 1RZ), σ = N.

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `m8_halts : halts tm8 c0`. |
| Score | **f_ω(f_ω(f_ω(12))) < σ < f_ω(f_ω(f_ω(13)))**, machine-checked with the standard fast-growing hierarchy (`m8_fgh3`). |
| More precisely | f_ω(f_ω(12B+26)) < σ < f_ω(f_ω(12B+27)), 2B + 4 = 2↑^13 3, machine-checked (`m8_fgh_bracket`, `Bx_knuth`). |
| Coarse placement | f_(ω+1)(3) < σ < f_(ω+1)(4), f_(ω+1)(n) = f_ω^n(n), machine-checked (`m8_fgh_coarse`). |
| Exact score | Machine-checked: σ = `sigma_c04`, C04's exact symbolic score (`m8_score_exact`, `m8_score_reached`); every count of M8's halting tape is one of C04's and back (`m8_score_to_c04`, `m8_score_from_c04`). Not evaluated as a number. |
| Previous BB(8) entry (`1RB0RA_..._1RG1LF`, σ = 12·(2↑^37 3) + 59) | **Beaten**, machine-checked against its Coq-proved exact count (`m8_beats_champ35`), and 12·(2↑^37 3) + 59 < σ (`m8_beats_bb8r`). |
| fw2 (`../BB9/`) | Beaten, machine-checked (`m8_beats_fw2`). |
| C04 (`../BB9/`, 9 states) | M8 is reduced from it: same halting tape, same score, one state fewer. |
| Steps | Not computed. |

---

## 1. The collapse

C04 = `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF` and M8 agree on states A–E and on F1. The
state map from M8 to C04 is

    A..F -> A..F,    G -> I,    H -> H          (C04's G has no counterpart)

- M8's F0 = 1RG writes a 1 and moves right into G. C04 does this in three steps: F0 = 0RG writes 0 and moves right;
  G (0LH / 1LH) writes back what it reads and moves left; H reads the 0 that F has just written, H0 = 1RI writes the 1
  and moves right into I. The tape and head position are then those of M8 after its one step, and C04's I = 0RI 0RF is
  M8's G = 0RG 0RF.
- M8's E0 = 1LH is C04's E0 = 1LH. From there both machines are in H on the same tape: H0 = 1RG in M8 is H0 = 1RI in
  C04 (I being M8's G), and H1 is undefined in both.
- So C04's H is entered in two ways. From G it always reads 0 (the cell F has just cleared), so it never halts there.
  From E it may read 0 or 1, exactly as M8's H does. Every M8 step is one C04 step, except F0, which is three, and
  M8 halts exactly when C04 does, on the same tape.

In Coq (`verify_m8/Sim.v`): `stmap` and `symmap` are the maps above, `Rel` relates an M8 configuration to a C04
configuration through finite tape lists (so no stream bisimulation is needed), `sim_step` is the step correspondence,
and `sim_run` follows a whole run by strong induction on C04's step count, using that both machines are deterministic.
`m8_to_c04` and `c04_to_m8` transfer reachable halting configurations and their ones counts in both directions. All
the facts about C04 come from its Coq development ([`../BB9/verify_c04/`](../BB9/verify_c04/)), used unchanged.

## 2. How it runs

Since M8 runs C04's computation step for step (up to the detour), the description of C04 applies verbatim with the
state names mapped: the BB(7) champion's digit-list counter, the start-up to the counter B with 2B + 4 = 2↑^13 3, the
first exhaustion rebuilding 12B + 25 digits (R₂ with 2R₂ + 4 = 2↑^(12B+26) 4), the second exhaustion parking
12R₂ − 10 digits, the cascade L → (3L + c)/5 whose constants are all even (so the orbit stays odd and enters one of the
keys 31, 37, 43, 49, 55), the second escalation across the parked list, and the halt. See sections 1–2 of C04's
write-up. The BB(7) champion halts where M8 reads E0 the first time; M8 instead keeps going.

## 3. The score

### 3.1 What Coq proves

The files to read are [`verify_m8/Defs.v`](verify_m8/Defs.v) and [`verify_m8/Statement.v`](verify_m8/Statement.v),
with busycoq's `TM.v`. `Defs.v` defines `tm8`, `ones`, `iter`, `arrow`, `f`, `f_omega` and `f_w1`; `Statement.v` states
the results in those terms and busycoq's (`halts`, `halted`, `c0`, `-[ ]->*`), without B, and pins the three machine
tables (M8's and the two compared machines') against their strings:

    Statement.m8_halts         : halts tm8 c0
    Statement.m8_fgh3          : forall c N, c0 -[ tm8 ]->* c -> halted tm8 c -> ones c N ->
                                   f_omega (f_omega (f_omega 12)) < N /\ N < f_omega (f_omega (f_omega 13))
    Statement.m8_bracket       : ... -> f_omega (f_omega (6 * arrow 13 2 3 + 2)) < N /\
                                          N < f_omega (f_omega (6 * arrow 13 2 3 + 3))
    Statement.m8_coarse        : ... -> f_w1 3 < N /\ N < f_w1 4
    Statement.m8_reached       : exists c N, c0 -[ tm8 ]->* c /\ halted tm8 c /\ ones c N
    Statement.m8_score_exact   : ... -> N = Exact.sigma_c04
    Statement.m8_beats_bb8     : ... -> 12 * arrow 37 2 3 + 59 < N
    Statement.m8_beats_champ35, Statement.m8_beats_fw2 : as below, with Defs's names
    Statement.m8_table, champ35_table, fw2_table : the tables equal the strings, through a string parser

(6 · arrow 13 2 3 + 2 = 6 · (2↑^13 3) + 2 = 12B + 26.) They are proved in one line each from the development's
theorems, listed next, through `Bridge.v` (pointwise equalities of the copied definitions, by reflexivity).

    m8_halts          : halts tm8 c0
    m8_fgh3           : forall c N, c0 -[ tm8 ]->* c -> halted tm8 c -> ones c N ->
                          f_omega (f_omega (f_omega 12)) < N /\ N < f_omega (f_omega (f_omega 13))
    m8_fgh_bracket    : forall c N, c0 -[ tm8 ]->* c -> halted tm8 c -> ones c N ->
                          f_omega (f_omega (12 * Bx + 26)) < N /\ N < f_omega (f_omega (12 * Bx + 27))
    m8_fgh_coarse     : forall c N, c0 -[ tm8 ]->* c -> halted tm8 c -> ones c N -> f_w1 3 < N /\ N < f_w1 4
    m8_score_exact    : forall c N, c0 -[ tm8 ]->* c -> halted tm8 c -> ones c N -> N = sigma_c04
    m8_score_reached  : exists c, c0 -[ tm8 ]->* c /\ halted tm8 c /\ ones c sigma_c04
    m8_sigma_bracket  : f_omega (f_omega (12 * Bx + 26)) < sigma_c04 /\ sigma_c04 < f_omega (f_omega (12 * Bx + 27))
    m8_beats_bb8r     : forall c N, c0 -[ tm8 ]->* c -> halted tm8 c -> ones c N ->
                          12 * BB8_champ35_bound.arrow 37 2 3 + 59 < N
    m8_beats_champ35  : exists c N, c0 -[ tm8 ]->* c /\ halted tm8 c /\ ones c N /\
                          exists cf Nf, (champ35 halts in cf) /\ BB8_champ35_bound.ones cf Nf /\ Nf + 1 < N
    m8_beats_fw2      : the same against fw2, as C04's c04_beats_fw2

`tm8` is a busycoq machine over a genuine 8-state context (`BB82`). `ones` (with `count1` and `sym_val`) is textually
identical to the previous BB(8) entry's `BB8_champ35_bound.ones` and to fw2's `BB9_fw2_bound.ones` (checked by diff;
they are over different `Sym` types, so Coq cannot compare them by `eq_refl`), and `Tm8.ones` (= `Defs.ones`) is
printed in the probe. `f`, `f_omega`, `f_w1` (f_(ω+1)), `arrow`
(Knuth's ↑^k) and `Bx` (B) are those of C04's development. `Beats8.arrow_same` shows that its `arrow` is the same
Fixpoint as the previous entry's. The previous entry's machine halts on E0 = `None` and its halting transition writes
a 1, so its score is Nf + 1.

### 3.2 How large

The bracket pins σ between f_ω(f_ω(12B + 26)) and f_ω(f_ω(12B + 27)) with 12B + 26 = 6·(2↑^13 3) + 2, that is,
between f_(ω+1)(3) and f_(ω+1)(4). The previous BB(8) entry, 12·(2↑^37 3) + 59, is at a finite level of the
hierarchy (around f_38 of a small argument); M8, like C04, is at level ω+1 with an argument between 3 and 4. The finer paper estimate of C04's write-up
(σ = f_ω(K + 1 + θ), 0 < θ < 2, not machine-checked) applies unchanged.

---

## 4. Verification

### 4.1 Files

[`verify_m8/`](verify_m8/) holds the M8 layer, Coq 8.20.1 on busycoq (commit `bd2e36f`), built on top of the
compiled C04 tree [`../BB9/verify_c04/`](../BB9/verify_c04/) and, for the comparison only, the previous entry's
[`verify/`](verify/). No axioms.

| file | content |
|---|---|
| `BB82.v`, `Individual82.v` | busycoq instantiated for 8 states (logical path `M8`; the same text as `../verify/`'s, which is under `BB8`) |
| `Defs.v` | **read this**: M8's table `tm8`, `sym_val`, `count1`, `ones`, and copies of `iter`, `arrow`, `f`, `f_omega`, `f_w1` |
| `Statement.v` | **read this**: the results in terms of `Defs.v` and busycoq only, and the three tables against their strings |
| `Tm8.v` | re-exports `Defs.v` (so `Tm8.tm8`, `Tm8.ones`, … are the same constants); uniqueness of the halting configuration |
| `Sim.v` | the state and symbol maps, `Rel`, `sim_step`, `sim_run`, `m8_halts_sim`, `m8_to_c04`, `c04_to_m8` |
| `Transfer.v` | the theorems of section 3.1, transferred from C04's (`c04_halts`, `c04_fgh_bracket`, `c04_score_exact`, …) |
| `Headline8.v` | `m8_fgh3`: the bound without B, from `m8_fgh_bracket` and C04's `Headline.Bx_fw` |
| `Beats8.v` | the comparison with the previous BB(8) entry's exact count (`m8_beats_bb8r`, `m8_beats_champ35`) |
| `Bridge.v` | `Defs.v`'s copies equal the development's definitions pointwise (by reflexivity), and the helper steps of `Statement.v` |
| `probe.v` | the independent probe (below) |

`probe.v` checks the table by conversion (16 `eq_refl` lines) and also against a parser of the literal string
(`m8_string_ok`: every slot of `tm8` is what the string says, H1 = `---` = `None`), checks that the start is the blank
tape in state A, prints the definitions, checks the theorem types, states the main results as one conjunction
(`m8_all_ok`), and runs `Print Assumptions` eight times (the conjunction, `m8_beats_fw2`, the two transfer theorems,
`m8_string_ok`, `m8_beats_bb8r`, `m8_beats_champ35`, and `m8_fgh3` as `m8_headline_ok`). Then it prints busycoq's `c0`
and `tape0` and every definition of `Defs.v`, checks the two compared machines' tables entry by entry against their
strings, and runs `Print Assumptions` on each of the twelve theorems of `Statement.v`. All twenty report "Closed under
the global context".

**Logical paths.** The C04 tree is loaded with its own paths (`lib` = `BB8`, `dev` = `Dev`, `k31` = `K31`,
`score` = `Score`, `fgh` = `Fgh`) and this directory is `M8`. `Beats8.v` and `probe.v` also load `../verify` as `BB8`:
its file names (`BB82`, `Individual82`, `BB8_champ35_*`) do not overlap the C04 tree's `lib/` (`BB92`, `Individual92`,
`BB9_fw2_*`), and M8's own `BB82`/`Individual82` live under `M8`, so every name resolves to one file.

**Build.** `verify_m8/compile_clean.sh deps` builds `../../BB9/verify_c04` and `../verify` from scratch with their own
scripts and then this directory; without `deps` it expects those two trees to be compiled. The M8 files take about a
minute; the probe about 10 minutes, nearly all of it `Print Assumptions` over C04's development. The GitHub workflow
(job `bb8-m8`) runs the whole chain whenever these files or the C04 tree change (and weekly), and fails unless the
probe reports twenty closed results. The recorded local build is in [`verify_m8/README.md`](verify_m8/README.md).

### 4.2 Not machine-checked

- **σ = N.** In Coq the halt is the undefined transition H1 and `ones` counts the 1s of the halted configuration.
- **The finer estimate** of C04's section 3.2, and the hierarchy-level comparison of section 3.2 here.
- **Section 2,** which summarizes C04's run.

---

## 5. Discovery and credit

- **Found** in this project (a Claude Opus agent, 2026-10-18), re-examining the 8-state neighbourhood of the BB(7)
  champion after C04 was proved: removing C04's two-state detour gives an 8-state machine. A literal lockstep
  comparison (3·10⁹ C04 steps = 2·10⁹ M8 steps, full tapes compared at regular sync points and at the end) agreed
  before any proof was written. M8 had been in an earlier screen of that neighbourhood in this project, where a
  small-world screen graded it TIME and dismissed it.
- **Proved** in Coq in this project (a Claude Opus agent, 2026-10-18): the simulation and the transfer of C04's
  theorems, on top of C04's development (section 5 of C04's write-up for its credits: this project's n1f0 search,
  the parity analysis by a Claude Fable agent, the Coq proof by Claude Opus agents).
- **Built on** the BB(7) champion of Kropitz (2025; analysed by Ligocki), whose counter M8 runs, and on the previous
  BB(8) entry's Coq files, used unchanged for the comparison.
