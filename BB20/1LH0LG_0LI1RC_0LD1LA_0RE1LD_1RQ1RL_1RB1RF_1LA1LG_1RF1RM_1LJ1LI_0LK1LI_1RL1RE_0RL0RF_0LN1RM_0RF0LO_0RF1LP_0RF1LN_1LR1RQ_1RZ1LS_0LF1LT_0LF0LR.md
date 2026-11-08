# J20: Jacobzheng's BB(20) champion, at level f_(ω·2)

    1LH0LG_0LI1RC_0LD1LA_0RE1LD_1RQ1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_0RF0LO_0RF1LP_0RF1LN_1LR1RQ_1RZ1LS_0LF1LT_0LF0LR

|   | 0   | 1   |                                                                  |
|---|-----|-----|------------------------------------------------------------------|
| A | 1LH | 0LG | engine: A1 erases the first cell of a digit ≥ 2                  |
| B | 0LI | 1RC | engine: B0 = end of the list, B1 = next digit                    |
| C | 0LD | 1LA | engine: C0 = digit 1 (pass), C1 = digit ≥ 2                      |
| D | 0RE | 1LD | engine: walk left over a passed digit                            |
| E | 1RQ | 1RL | E1 splits a cell off the head (engine); E0 starts the refill     |
| F | 1RB | 1RF | engine: the sweep state, walks right over the accumulator        |
| G | 1LA | 1LG | engine: walk back                                                |
| H | 1RF | 1RM | left end: H0 = inner list (new sweep), H1 = marker: expansion    |
| I | 1LJ | 1LI | end of a list: merge it into one block                           |
| J | 0LK | 1LI | end of a list                                                    |
| K | 1RL | 1RE | K0 writes the marker (outer boundary), K1 = outer list exhausted |
| L | 0RL | 0RF | start of a sweep                                                 |
| M | 0LN | 1RM | expansion: walk right over the block                             |
| N | 0RF | 0LO | expansion: rewrite the block from the right                      |
| O | 0RF | 1LP | expansion                                                        |
| P | 0RF | 1LN | expansion                                                        |
| Q | 1LR | 1RQ | refill: walk to the right end                                    |
| R | 1RZ | 1LS | refill: R0 is the halt                                           |
| S | 0LF | 1LT | refill                                                           |
| T | 0LF | 0LR | refill                                                           |

Found by Jacobzheng (the BB(20) row of the bbchallenge wiki's
[Champions](https://wiki.bbchallenge.org/wiki/Champions) page, checked 2026-11-07, which gives the lower bound
f_(ω·2)(f_(ω+2)^2(f_10(2))) and marks it "Not independently verified"). The analysis and the Coq proof below are
this project's. All 39 non-halting slots are used.

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB20_JZ20.halt`. The halt is decided by a residue mod 3, which the proof computes exactly (section 2): every level map of the machine is x ↦ x + 1 (mod 3). |
| Exact score | Machine-checked formula: the halting tape holds 2j + 1 ones, where 3k + 2 = ho_2(ho_2(ho_1(1))) + 10, a₂ = ho_k(ho_k(hoc_0^k(1))) and 3j = a₂ + 2(k+1) + 4, for the recursion of section 1 (`score_exact`). The halt R0 = `1RZ` is read on a 0 and writes 1, so σ = 2j + 2. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω·2)(f_(ω+2)(f_(ω+2)(f_10(2)))) < N = 2j + 1 < σ (`sigma_lower_bound`). This is the wiki's claimed bound, exactly. |
| Comparisons | **Argument, not a Coq lemma** (section 4): far above every entry here with fewer states. Not yet reviewed by the bbchallenge community. |
| Steps | Not computed. The wiki lists its bound as a bound on the number of steps; σ is at most the number of steps (each step writes at most one new 1), so the proved bound on σ gives it too. |

## 1. How it works

Lists are blocks of 1s separated by single 0s: [a, b, c] is 1^a 0 1^b 0 1^c. The tape holds two lists, an **inner**
list at the left end and an **outer** list, separated by `0 0`, and one sweep engine (states A–H, L) runs both. A
marker (a single 1 at the far left) says which list is being swept. The two boundaries are

    inner:  CI x [d2, ..., dn] R  =  0^∞ [H] 1^x 0 1^d2 0 ... 0 1^dn 0 0 R        (H on the blank left of the list)
    outer:  CO a [o2, ..., om]    =  0^∞ 1 0 0 [F] 1^a 0 1^o2 0 ... 0 1^om 0^∞     (F on the first 1 of the head)

**The inner list** (H0 = `1RF` starts a sweep; `CI_E0`, `CI_E1`, `CI_exit`):

    E0    [x, e, r]        →  [x+4, e−1, r]
    E1    [x, 1^p, e, r]   →  [2, 1^(p−1), x+3, e−1, r]
    exit  [x, 1^n]         →  the outer head x + 2n + 2   (I and J merge the list into one block; K0 = `1RL` writes
                              the marker, and the machine is at an outer boundary)

Reducing a digit at position m + 2 takes the head through h_m, with h_0(x) = x + 4 and h_(m+1)(x) = h_m^(x+2)(2)
(`LV_in`), so position m + 2 is f_m-class (h_1(x) = 4x + 10).

**The outer list** (`R0`, `R1`, `OEX`):

    R0   CO [a, e, r]          →*  CO [G(a), e−1, r]
    R1   CO [a, 1^p, e, r]     →*  CO [3, 1^(p−1), a+2, e−1, r]
    EX   CO [a, 1^n]           →*  the merged block of N = a + 2n + 4 ones, and the refill

In R0 the sweep reaches the head through H, which reads the marker: H1 = `1RM` starts the **expansion** (M, N, O, P;
`EXP`, three residue cases), which rewrites the head block from the right as an inner list of about a/3 twos and
starts an inner sweep. The inner run then exits into the new outer head (`Inner_run`):

    G(a) = hc_1^(a div 3)(a mod 3 + 3) + 2(a div 3) + 4,

where hc_m^n(x) reduces n twos at positions m + 2, m + 3, ... (hc_m^0(x) = x, hc_m^(n+1)(x) = hc_(m+1)^n(h_m(x))).
G(1..5) = 8, 9, 28, 32, 36, and G is f_ω-class. Reducing an outer digit at position m + 2 takes the head through
ho_m, with ho_0 = G and ho_(m+1)(a) = ho_m^(a+1)(3) (`LV_out`), so outer position m + 2 is f_(ω+m)-class.

**The refill** (K1 = `1RE`, E0 = `1RQ`, then Q, R, S, T; `RF_halt`, `RF_1`, `RF_2`): Q walks to the right end of the
merged block, and R, S, T rewrite it from the right with period 3. The left end decides:

| N | result |
|---|---|
| 3j | R reads the blank and halts, with 2j + 1 ones on the tape |
| 3k + 1 | the outer list [1, 1, 2^(k−1), 3] |
| 3k + 2 | the outer list [1, 2^k, 3] |

In [1, 2^k, 3] the last digit, 3, sits at outer position k + 2, where it is reduced by ho_k, an f_(ω+k)-class
map. Since k is itself huge, that is the f_(ω·2) step.

## 2. The run, and why it halts

| phase | what runs | result |
|---|---|---|
| boot | 13 steps from the blank tape | CO [3] (`boot`) |
| exhaustion 1 | EX: N = 3 + 4 = 7 = 3·2 + 1 | refill: CO [1, 1, 2, 3] |
| position 3 | `LV_out` at level 1 on the digit 2 | CO [ho_1(1), 1, 3] |
| position 4 | `LV_out` at level 2 on the digit 3 | CO [a₁, 1, 1], a₁ = ho_2(ho_2(ho_1(1))) |
| exhaustion 2 | EX: N = a₁ + 10 = 3k + 2 | refill: CO [1, 2^k, 3] |
| the long part | `Chain_out` on the k twos, then `LV_out` at level k on the 3 | CO [a₂, 1^(k+1)], a₂ = ho_k(ho_k(hoc_0^k(1))) |
| exhaustion 3 | EX: N = a₂ + 2(k+1) + 4 = 3j | R0 is read: halt, 2j + 1 ones (`run_gen`, `run`, `halt`) |

**The mod-3 invariant.** Every level map is x ↦ x + 1 (mod 3): h_0(x) = x + 4, and if h_m is, then
h_(m+1)(x) = h_m^(x+2)(2) ≡ 2 + x + 2 ≡ x + 1 (`h_P1`); G(a) ≡ a + 1 (`G_P1`); and in the same way every ho_m
(`ho_P1`), so hoc_m^n(a) ≡ a + n (`hoc_mod`). Hence ho_1(1) ≡ 2, a₁ ≡ 1, and N = a₁ + 10 ≡ 2 at the second
exhaustion (`K_gen`); then hoc_0^k(1) ≡ k + 1, a₂ ≡ k + 3, and N = a₂ + 2k + 6 ≡ 0 at the third (`J_gen`). No residue
depends on anything the proof does not compute: the boot gives N ≡ 1, the refill [1, 1, 2^(k−1), 3] always leads to
N ≡ 2, and the refill [1, 2^k, 3] always leads to N ≡ 0, the halt. So the machine halts after exactly two refills.

The halting tape is 0^∞ [R on 0] (0 1 1)^j 1 0^∞: 2j + 1 ones (`ones_Hc`, `score_exact`), and R0 writes one more.

**Size** (`BB20_JZ20.v`, sections "Fast-growing hierarchy up to f_(omega*2)", "Lower bounds for the machine's
hierarchy" and "Final bound"). A generic transfer lemma (`transfer`: a hierarchy that iterates at least z + 1 times
from a constant dominates the fast-growing one, up to a scale factor) gives

- `h_dom`: 2n ≤ z implies 2 f_m(n) ≤ h_m(z);
- `G_dom`: 6n ≤ z implies 6 f_ω(n) ≤ G(z);
- `ho_dom`: 6n ≤ z implies 6 f_(ω+m)(n) ≤ ho_m(z);
- `ho11`: ho_1(1) = G(G(3)) = G(28) ≥ hc_1^9(4) ≥ 8 f_10(2) (`G3`, `hc_tower`, `hc9`).

So a₁ = ho_2(ho_2(ho_1(1))) ≥ 6 f_(ω+2)(f_(ω+2)(f_10(2))), which gives k ≥ f_(ω+2)^2(f_10(2)); then, since
hoc_0^k(1) ≥ 6k + 1 (`hoc_ge`), a₂ ≥ ho_k(hoc_0^k(1)) ≥ 6 f_(ω+k)(k) = 6 f_(ω·2)(k), and N = 2j + 1 > f_(ω·2)(f_(ω+2)^2(f_10(2))) (`bound_gen`,
`sigma_lower_bound`).

## 3. Verification

[`verify/`](verify/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about 25 s, built in CI (job
`bb13-bb14`). `BB202.v` and `Individual202.v` instantiate busycoq for 20 states (new here). `probe.v` re-checks the
transition table entry by entry against the string above (40 checks generated from the string) and the blank start
configuration. It prints the definitions the statements use and confirms that `halt`, `score_exact` and
`sigma_lower_bound` are closed under the global context.

[`tools/j20_writeup_chk.py`](tools/j20_writeup_chk.py) simulates the machine string (exactly, jumping only over
same-state runs), without the Coq files (about 2 minutes). It checks:

1. the inner rules E0, E1 and the exit on 600 random inner lists with random outer lists behind them;
2. 330 random outer rounds (R0 with heads a ≤ 5, where G(a) is small; R1 with any head);
3. the expansion of the outer head a = 1..199: the first inner boundary after it is the one the residue cases give;
4. exhaustion and refill of [a, 1^n] for a = 1..39, n = 0..5: the three cases of the table above, and the number of
   ones at the halt;
5. the mod-3 residue law of the inner engine on 2336 random small lists, and G(1..5) = 8, 9, 28, 32, 36;
6. the run from the blank tape against the model, boundary by boundary, inner and outer (222,193 boundaries in the
   first 7.7·10^10 steps with the default settings; an earlier run with ten times as many macro steps matched
   2,222,191 boundaries, 8.85·10^12 steps).

## 4. Comparisons (an argument, not a Coq lemma)

No Coq lemma compares this machine with another entry: none of them has a proved upper bound.

- f_(ω·2)(n) = f_(ω+n)(n), so for n ≥ 8, f_(ω·2)(n) ≥ f_(ω+8)(n) = f_(ω+7)^n(n) ≥ f_(ω+7)^2(5); here
  n = f_(ω+2)^2(f_10(2)) is far larger than 8. So J20's bound is far above J19's (BB(19), [`../BB19/`](../BB19/)),
  and above every entry here with fewer states, all of which are below f_(ω·2).
- The hydra machines (BB(29), BB(31), BB(33)) are far higher (f_(ω^ω) and above).
- Not yet reviewed by the bbchallenge community.

## Credit

Machine by Jacobzheng, listed as the BB(20) champion on the bbchallenge wiki's Champions page (with the bound
f_(ω·2)(f_(ω+2)^2(f_10(2))), "Not independently verified"). This project (the repository owner with Claude models
(Anthropic) as agents) found the rules above and the mod-3 argument, wrote the Coq proof `BB20_JZ20.v`
(2026-11-04), the 20-state busycoq setup, the probe, the checker and this write-up. The proof confirms the wiki's
claim: the machine halts, with σ > f_(ω·2)(f_(ω+2)^2(f_10(2))).
