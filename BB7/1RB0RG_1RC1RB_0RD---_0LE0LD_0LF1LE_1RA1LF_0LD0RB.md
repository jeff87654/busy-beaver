# BB(7): `1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_0LD0RB` (champ_231)

A 7-state, 2-symbol Turing machine that halts from the blank tape with

    σ = 6·a_f + 7  >  3↑^20 3 = 3↑^19 (3↑^19 3),

where a_f is the explicit recursion of section 3. This is larger than the score of the current BB(7) champion
`1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_0RG0RF` (Pavel Kropitz, May 2025), which is about 3·(2↑^13 3). The
halting, the exact score and the bounds are proved in Coq with no axioms ([`verify/`](verify/)). Its twin
`1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_1LC0RB` (champ_232, G0 = `1LC` instead of `0LD`) has the same score and is
proved by the same files.

**Status: not yet reviewed by the bbchallenge community.** The machine was found by Argon (section 8) and checked
here by independent simulators and the Coq proof.

## 1. Main facts

| | |
|---|---|
| machine | `1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_0LD0RB` (C1 undefined = the halt; `1RZ` in the wiki's format) |
| twin | `1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_1LC0RB` (champ_232): same configurations, 2 extra steps at every G0 |
| configuration | `K(a; d1, ..., dn) = 0^∞ E> 0 100 (11)^a 00 (11)^d1 00 ... (11)^dn 00 1 0^∞` (section 2) |
| start | `K(8; 0, 1^19)` at step 3897 (champ_232: step 3959): 20 digits |
| rules | D: `K(a; d+1, …) → K(3a+3; d, …)`; Bk: `K(a; 0^k, y+1, …) → K(1; 1^(k−1), 3a+3−k, y, …)` (k ≤ 3a); E: `K(a; 0^n)` halts with 6a+7 ones (n ≤ 3a) |
| halting | at C1, head on a 1: σ = the number N of ones on the halted tape (writing `1RZ` there changes nothing) |
| exact score | σ = 6·a_f + 7, a_f = V_19(V_18(⋯V_1(8)⋯)) (section 3); in Coq σ = 2·W 20 5 + 7 |
| proved bounds (Coq) | 3↑^20 3 < σ; 3·(2↑^13 3) + 22 < σ; 2↑^11 (2↑^11 3) < σ |
| theorems | `c231_halts`, `c231_score`, `c231_lower`, `c231_beats_bb7_champion` (and `c232_*`), in [`verify/Statement.v`](verify/Statement.v) |
| checked | CI job `bb7`; independent simulator [`tools/c231_chk.py`](tools/c231_chk.py) |

a ↑^k b is Knuth's up-arrow (a ↑^0 b = a·b, a ↑^1 b = a^b, a ↑^2 b = tetration).

## 2. Configurations and rules

The table:

| | 0 | 1 |
|---|---|---|
| A | 1RB | 0RG |
| B | 1RC | 1RB |
| C | 0RD | --- |
| D | 0LE | 0LD |
| E | 0LF | 1LE |
| F | 1RA | 1LF |
| G | 0LD (champ_232: 1LC) | 0RB |

The machine keeps a list of digits written in unary, with an accumulator `a` at the left end, where the head comes
back each time in state E:

    K(a; d1, ..., dn) = 0^∞ E> 0 100 (11)^a 00 (11)^d1 00 (11)^d2 00 ... (11)^dn 00 1 0^∞

(head in state E on the first cell; `d1` is the digit next to the accumulator, the "active end"; the final `1` is the
right boundary). Three rules, exact for all values in their range:

| rule | | precondition | steps (champ_231) |
|---|---|---|---|
| D | `K(a; d+1, R) → K(3a+3; d, R)` | a ≥ 1 | 12a² + 66a + 56 |
| Bk | `K(a; 0^k, y+1, R) → K(1; 1^(k−1), 3a+3−k, y, R)` | 1 ≤ k ≤ 3a | 12a² + (24k+66)a + 74 + 10(k−1) − 4(k−1)(k−2) |
| E | `K(a; 0^n)` → halt at C1 with 6a + 7 ones | n ≤ 3a | 48a² + 192a + 137 − 28n |

For champ_232 add 2 steps to D and 2(k+1) to Bk; E takes 48a² + 198a + 143 − 30n. The step counts come from the
independent checks' simulations (they are re-checked by [`tools/c231_chk.py`](tools/c231_chk.py)); they are not part of
the Coq proof. Just past each precondition (k = 3a + 1, n = 3a + 1) the rule fails: no K configuration, no halt.

How the rules work, in the tape picture (the Coq proof follows exactly these phases):

- **Mini-cycle.** `0^∞ E> 0 1^m 00 1 X → 0^∞ E> 0 1^(m+3) 00 X` in 2m + 10 steps: the head walks right over the
  left block, takes one cell of the accumulator block and walks back, and the left block grows by three cells. So
  the 2a cells of `(11)^a` turn into 6a cells: from `K(a; ...)`, after 2a mini-cycles the tape is
  `E> 0 1^(6a+1) 0000 (11)^d1 00 ...`. This is the factor 3 in `3a+3`.
- **Forward and backward passes.** The machine then sweeps the block `1^(6a+4)` to the right through the zeros that
  follow it, one pass per zero cell, leaving a trail `(10)^p` behind. When the sweep meets the first nonzero digit it
  takes one unit off it (`y+1 → y`) and turns around, and the backward passes convert the trail: every two pairs
  `1010` become one digit `1100` = 1. In D there are no zero digits, the trail is short, and the block becomes the
  new accumulator 3a+3. In Bk the k zero digits become k−1 digits 1 and a new accumulator 1, and the rest of the
  block, 3a+3−k, becomes the refilled digit. The block must not run out while it crosses the 2k+1 zero cells it has
  to cross: that is the precondition k ≤ 3a.
- **Exhaustion.** If no nonzero digit follows (`K(a; 0^n)`), the sweep runs past the boundary `1` into the blank
  tape, comes back, and its backward passes end in state C reading a 1, which is undefined: the halt, with 6a + 7 ones
  on the tape whatever n is. Again n ≤ 3a is needed.

**The run.** From the blank tape the machine reaches `K(8; 0, 1^19)` at step 3897 (champ_232: step 3959), 20 digits.
From there only D, Bk (with k ≤ 19) and finally E (with n = 20) are used, and their preconditions always hold:
right after a Bk the accumulator is 1 but the next digit is nonzero, so the next rule is D, which gives a ≥ 6; so
before any Bk with k ≥ 2 (which needs k−1 cleared positions in front) the accumulator is at least 21, and
3a ≥ 63 > 20. In Coq this is the inequality W_j(B) ≥ B + j (section 6).

## 3. The high-level rule and the score

As in Ligocki's analysis of the champion, clear the list one position at a time. Let `V_k(a)` be the accumulator
after one unit of a digit at position k (k zero digits in front of it) has been cleared, starting from accumulator a,
with the zeros restored:

    K(a; [0]*k, n, ...)  →  K(V_k^n(a); [0]*k, 0, ...)

    V_0(x) = 3x + 3,     V_(k+1)(x) = V_k^(3x+2−k)(s_k),     s_0 = 1,  s_(k+1) = V_k(s_k).

(Bk at position k+1 writes `1^k, 3x+2−k` with accumulator 1; the k ones are cleared first, positions 0..k−1, which
turns the accumulator 1 into s_k; then the digit 3x+2−k at position k is cleared.) Each step up in k iterates the
previous map, so each list position adds one up-arrow level: V_k(x) is about 3↑^k(3x).

The run clears the 20 digits of `K(8; 0, 1^19)` one after the other:

    a_f = V_19(V_18(⋯V_2(V_1(8))⋯)),        σ = 6·a_f + 7.

In Coq the same recursion is written for the counter b = 3a that the machine holds after the mini-cycles:
`U 0 x = 3x + 9`, `U (j+1) x = (U j)^(x+2−j) (W j 3)`, `W 0 B = B`, `W (j+1) B = U j (W j B)`
(so U_j(3x) = 3·V_j(x) and W_j(3) = 3·s_j), and

    σ = 2·W_20(5) + 7          (W_20(5) = U_19(U_18(⋯U_0(5)⋯)) = 3·a_f).

**Bounds (Coq).** U_i(y) ≥ 3↑^i (y + 3 − i) for all i, y; W_2(5) = U_0^26(3) ≥ 2·3^27 = 2·(3↑↑3); and
W_j(5) ≥ 3↑^j 3 + j for all j ≥ 2. Hence

    3↑^20 3 < σ.

The development also proves that σ is above the nested chain 3↑^19 3↑^18 ⋯ 3↑^2 3↑ 15 and above 3↑^19 (3↑^18 3)
(both weaker). No upper bound is proved; we expect σ < 3↑^20 4.

## 4. Side by side with the BB(7) champion

The champion `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_0RG0RF` was found by Pavel Kropitz (10 May 2025) and
analysed by Shawn Ligocki (13 May 2025) on its [BusyBeaverWiki page](https://wiki.bbchallenge.org/wiki/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_0RG0RF)
(CC BY 4.0). Both machines are digit-list counters of the same family: an accumulator, a unit decrement of the active
digit that multiplies the accumulator, a borrow that refills the zeros in front of the next nonzero digit from the
accumulator, and a halt when the digits run out. Ligocki's notation for the champion, and champ_231 written the same
way:

| | BB(7) champion (Ligocki) | champ_231 |
|---|---|---|
| configuration | `B(a; b, ..., z) = 0^∞ 111 (01)^(3z+1) 1 ... 1 (01)^(3b+1) 1 (01) 01 (01)^(3a+1) 0011100 A> 0^∞` | `K(a; b, ..., z) = 0^∞ E> 0 100 (11)^a 00 (11)^b 00 ... (11)^z 00 1 0^∞` |
| decrement | `B(a; b+1, ...) → B(2a+4; b, ...)` | `K(a; b+1, ...) → K(3a+3; b, ...)` |
| borrow | `B(a; [0]*k, 0, n+1, ...) → B(0; [0]*k, a+2, n, ...)` | `K(a; [0]*k, 0, n+1, ...) → K(1; [1]*k, 3a+2−k, n, ...)` (k+1 ≤ 3a) |
| halt | `B(a; [0]*k) → Halt(3a + 2k + 10)` (the page says +9; see below) | `K(a; [0]*k) → Halt(6a + 7)` (k ≤ 3a) |
| high-level map | `g_0(x) = 2x+4`, `g_(k+1)(x) = g_k^(x+2)(0)` | `V_0(x) = 3x+3`, `V_(k+1)(x) = V_k^(3x+2−k)(s_k)` |
| closed form | `g_k(x) = 2↑^k (x+4) − 4` | none as simple; U_k(y) ≥ 3↑^k (y+3−k) in the Coq scaling |
| start | 12 digits: `B(4; [1]*12)` at step 8574 | 20 digits: `K(8; 0, [1]*19)` at step 3897 |
| score | `a_(k+1) = g_k(a_k)`, `a_0 = 4`, `a_k + 4 = 2↑^(k+1) 3`, σ = 3·a_12 + 34 = 3·(2↑^13 3) + 22 | a_f = V_19(⋯V_1(8)⋯), σ = 6·a_f + 7 > 3↑^20 3 |
| status | analysis on paper | Coq: halting, exact score, bounds |

The differences that matter:

1. **The decrement triples instead of doubling.** The champion's accumulator grows by a factor 2 per unit of the
   active digit, champ_231's by a factor 3 (its mini-cycle writes three cells for each cell it takes). This changes
   the base of the arrows, 2↑ against 3↑, which is a small effect at these sizes.
2. **The borrow refills with ones.** The champion's borrow leaves the k zeros in front of the refilled digit at 0 and
   sets the accumulator to 0. champ_231 sets them to 1, sets the accumulator to 1, and lowers the refilled digit by
   k. The extra ones are cleared before the refilled digit, which is where s_k comes from; this does not change the
   number of arrows per position.
3. **The halt.** Both halt when the list is all zeros; the champion's ones count depends on the list length,
   champ_231's does not (6a + 7).
4. **The number of digits decides.** Each list position is one up-arrow level, so the score is about
   (base) ↑^(number of digits) (start). The champion starts with 12 digits and reaches about 2↑^13 3; champ_231
   starts with 20 and passes 3↑^20 3. Eight more digits are eight more arrow levels.

**Where the 20 digits come from.** At step 934 the tape is `0^∞ E> 0 1^40 000000 1 0^∞`: an exhaustion configuration
like the one of rule E, but with a left block of even length 40 (in a K configuration the block after the
mini-cycles, 1^(6a+1), is odd). The block was built by 13 mini-cycles from `0^∞ E> 0 1 00 1^13 0000 1` at step 310
(1 + 3·13 = 40). The exhaustion sweep then runs as in rule E: forward passes, passes into the blank tape, and
backward passes that each turn two trail pairs into one digit `1100`. In rule E the backward passes end on the halting
pattern; with the even block they end one cell further, without halting, and leave twenty digits 1: the tape
`Kc(1^20; a = 1, b = 2)` of the Coq development at step 3715, which is `K(8; 0, 1^19)` after one decrement (step
3897). So the start-up uses the halting sweep itself to write the list, one digit for each two cells of the 40-cell
block.

**Notes on the champion's page.** Our earlier check of Ligocki's page (2026-10-04, with an independent simulator)
found two off-by-ones that do not affect its lower bound: the halt rule's constant is +10, not +9 (the page's own
low-level rule 4 gives +10), and in the page's own `B` form the start is `B(4; [1]*12)` at step 8574 (the page says
"step 8178: B(2; [1]*12)", which reads the accumulator as `(01)^(3a)`). With a_0 = 4 the recursion closes,
a_k + 4 = 2↑^(k+1) 3, and σ(champion) = 3·(2↑^13 3) + 22, about three times the page's stated upper bound 2↑^13 3;
the page's lower bound 2↑^11 (2↑^11 3) is right. These points are ours, from simulation, and have not been confirmed
by the page's author. The Coq theorem `c231_beats_bb7_champion` compares champ_231 with both numbers,
3·(2↑^13 3) + 22 and 2↑^11 (2↑^11 3), as plain numbers; it does not formalize the champion.

## 5. champ_232

`1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_1LC0RB` differs only in G0. Whenever G reads a 0, the cell to its left is
0, so `1LC`, then C0 = `0RD`, then D1 = `0LD` does in three steps what `0LD` does in one. Both machines pass through the
same K configurations (champ_232 reaches `K(8; 0, 1^19)` at step 3959) and halt on the same tape, so
σ(champ_232) = σ(champ_231). The Coq files for champ_232 are those of champ_231 with the table changed and the
start-up step count 3775 instead of 3715; no proof script changed.

## 6. The Coq proof

[`verify/`](verify/) (busycoq `bd2e36f`, Coq 8.20.1, logical root `BB7`). To check the claims, read
[`verify/Defs.v`](verify/Defs.v) (the two tables, the ones count, iter, U, W, arrow) and
[`verify/Statement.v`](verify/Statement.v), together with busycoq's `TM.v`. For each machine `Statement.v` proves:

- `c231_table`: the table equals the machine string, parsed inside Coq;
- `c231_halts : halts tm231 c0`;
- `c231_halting_config`: a halting configuration with 2·W 20 5 + 7 ones is reached from the blank tape;
- `c231_score : forall c N, c0 -[ tm231 ]->* c -> halted tm231 c -> ones c N -> N = 2 * W 20 5 + 7`;
- `c231_lower : forall c N, ... -> arrow 20 3 3 < N`;
- `c231_beats_bb7_champion : forall c N, ... -> 3 * arrow 13 2 3 + 22 < N /\ arrow 11 2 (arrow 11 2 3) < N`;

and the same `c232_*` for champ_232. `probe231.v` and `probe232.v` run `Print Assumptions` on each: "Closed under the
global context".

The development uses a configuration with two counters, `Kc ds a b = 0^∞ E> 0 1^(2b+1) 00 (11)^a 00 [(11)^d 00 for d
in ds] 1 0^∞`, so that `K(a; ds) = Kc ds a 0`. Its rules: `R1ITER : Kc ds a b →* Kc ds 0 (b + 3a)` (the
mini-cycles); `R2 : Kc (y+1 :: t) 0 b →+ Kc (y :: t) (b+3) 0`; `R3 : k+1 ≤ b → Kc (0^(k+1) ++ y+1 :: t) 0 b →+
Kc (1^k ++ (b+2−k) :: y :: t) 1 0`; `R4x : k ≤ b → Kc 0^k 0 b →* cfin k b`, a halted configuration with 2b + 7 ones.
Each is built from lemmas for the passes (`START`, `FW`, `TURN`, `BW`, `FINB`, `TURN4`, `FWZ`, `END2`, `FIN`), each a
few symbolic steps plus crossing lemmas for runs of 1s. The clearing lemma `CDP` (clear one digit at position m, by
induction on m) replaces a lexicographic descent, and `W_j(B) ≥ B + j` gives every precondition. The start-up (3715
steps to `Kc (1^20) 1 2`) is executed step by step. See [`verify/README.md`](verify/README.md) for the files and the
build times.

## 7. Verification

- Coq: [`verify/`](verify/), CI job `bb7`; `compile_clean.log` and `probe231.log` / `probe232.log` are from one clean
  build.
- Independent simulation, before the proof: [`tools/c231_chk.py`](tools/c231_chk.py) (a plain cell-by-cell
  simulator; checks the start, D/Bk/E with exact step counts on a grid, the halting ones count, and the failure just
  past each precondition, for both machines). A separate check by another agent ran a literal C++ simulator for
  3·10^10 steps on each machine and matched ten consecutive macro steps (up to step 3,632,810,465, accumulator 49206)
  with the rules and their step counts.
- Not yet reviewed by the bbchallenge community, and not on the BusyBeaverWiki as of 2026-10-22 (which lists the May
  2025 champion).

## 8. Credit

- **Machine**: found by Argon (a Google Gemini model run by the repository owner in Google's Antigravity) in this
  project's scan of the bbchallenge BB(7) holdout list, where a digit-list classifier graded both machines CHAMPION.
  Argon's report had the rules and the 20-digit start right; its estimate "σ ~ 3↑^19" undersold the score, and its
  remark that G0 is used only once in the start-up is wrong (G0 is used at every macro step, harmlessly).
- **Checks, Coq proof and this write-up**: this project (the repository owner with Claude models as agents),
  2026-10-22.
- **The BB(7) champion and its analysis**: Pavel Kropitz (machine, 10 May 2025) and Shawn Ligocki (analysis, 13 May
  2025), BusyBeaverWiki, CC BY 4.0; the comparison table restates Ligocki's rules in his notation.
