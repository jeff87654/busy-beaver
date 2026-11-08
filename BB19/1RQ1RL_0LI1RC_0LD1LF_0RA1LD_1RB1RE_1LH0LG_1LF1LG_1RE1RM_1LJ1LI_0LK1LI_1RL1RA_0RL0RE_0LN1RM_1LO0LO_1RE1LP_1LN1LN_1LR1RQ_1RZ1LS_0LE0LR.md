# J19: Jacobzheng's BB(19) champion, at level f_(ω+7)^2

    1RQ1RL_0LI1RC_0LD1LF_0RA1LD_1RB1RE_1LH0LG_1LF1LG_1RE1RM_1LJ1LI_0LK1LI_1RL1RA_0RL0RE_0LN1RM_1LO0LO_1RE1LP_1LN1LN_1LR1RQ_1RZ1LS_0LE0LR

|   | 0   | 1   |                                                                  |
|---|-----|-----|------------------------------------------------------------------|
| A | 1RQ | 1RL | A0 starts the refill; A1 splits a cell off the head (engine)     |
| B | 0LI | 1RC | engine: B0 = end of the list, B1 = next digit                    |
| C | 0LD | 1LF | engine: C0 = digit 1 (pass), C1 = digit ≥ 2 (decrement)          |
| D | 0RA | 1LD | engine: walk left over a passed digit                            |
| E | 1RB | 1RE | engine: the sweep state, walks right over the head block         |
| F | 1LH | 0LG | engine: decrement                                                |
| G | 1LF | 1LG | engine: walk left                                                |
| H | 1RE | 1RM | left end: H0 = engine mode (new sweep), H1 = marker: expansion   |
| I | 1LJ | 1LI | end of a list: merge it into one block                           |
| J | 0LK | 1LI | end of a list                                                    |
| K | 1RL | 1RA | outer boundary: K0 = next outer round, K1 = marker: refill       |
| L | 0RL | 0RE | start of a sweep                                                 |
| M | 0LN | 1RM | expansion: walk right over the block                             |
| N | 1LO | 0LO | expansion: rewrite the block from the right                      |
| O | 1RE | 1LP | expansion                                                        |
| P | 1LN | 1LN | expansion                                                        |
| Q | 1LR | 1RQ | refill: walk to the right end                                    |
| R | 1RZ | 1LS | refill: R0 is the halt                                           |
| S | 0LE | 0LR | refill                                                           |

Found by Jacobzheng (the BB(19) row of the bbchallenge wiki's
[Champions](https://wiki.bbchallenge.org/wiki/Champions) page, checked 2026-11-07, which gives the lower bound
f_(ω+7)^2(5) and marks it "Not independently verified"). The analysis and the Coq proof below are this project's.

## Main facts

| | |
|---|---|
| Halts | **Yes**, machine-checked (Coq, no axioms): `BB19_JZ19.halt`. |
| Exact score | Machine-checked formula: the halting tape holds N ones with 2N = T_8(2) + 23, for the recursion T of section 1 (`score_exact`). The halt R0 = `1RZ` is read on a 0 and writes 1, so σ = N + 1 = (T_8(2) + 25)/2. Not evaluated as a number. |
| Level | Machine-checked, with the standard fast-growing hierarchy: f_(ω+7)(f_(ω+7)(5)) < N, so f_(ω+7)^2(5) < σ (`sigma_lower_bound`). This is the wiki's claimed bound, exactly. |
| Comparisons | **Argument, not a Coq lemma** (section 4): far above the other 19-state machines here (M19_fw4_A, M19_fw4) and the BB(18) entries. Not yet reviewed by the bbchallenge community. |
| Steps | Not computed. The wiki lists its bound as a bound on the number of steps; σ is at most the number of steps (each step writes at most one new 1), so the proved bound on σ gives it too. |

## 1. How it works

Lists are blocks of 1s separated by single 0s: [a, b, c] is 1^a 0 1^b 0 1^c. One sweep engine (states A–G, L) runs
on a list in two modes, depending on what lies at the far left: nothing (**engine mode**, the inner, level-1 list)
or a single 1, the marker (**marker mode**, the outer list). The sweep configuration is

    SW b p W R  =  W 0 0 (1 0)^p 1^b [E] 0 R                (E walking right; p passed 1-digits parked as (1 0))

and it has four rules, the same in both modes (`SW_pass`, `SW_dec0`, `SW_dec1`, `SW_end`):

    pass   SW b p W (1 0 R)                →+  SW b (p+1) W R
    dec0   SW b 0 W (1^(e+2) 0 R)          →+  W [<H] 1^(b+3) 0 1^(e+1) 0 R
    dec1   SW b (p+1) W (1^(e+2) 0 R)      →+  W [<H] 1 1 0 (1 0)^p 1^(b+2) 0 1^(e+1) 0 R
    end    SW b p W (0 R)                  →+  W [<K] 0 1^(b+2p+2) 0 R

H then reads the cell of W. In engine mode it reads 0, and H0 = `1RE` starts the next sweep (`H_engine`). In marker
mode it reads the marker, and H1 = `1RM` starts the **expansion** (states M, N, O, P; `EXP0`–`EXP2`): the block
1^c to the right of the marker is rewritten as a level-1 list of about c/3 twos, the marker is used up, and the
engine runs that list in engine mode. When the level-1 list is used up, `end` merges it into a single block in
front of the outer list, and K reads the 0 at the far left: an outer boundary

    Kbnd [a, d2, ..., dn]  =  0^∞ [K] 0 1^a 0 1^d2 0 ... 0 1^dn 0^∞      (K on the blank left of the 0),

where K0 = `1RL` puts the marker back and starts a sweep of the outer list (`K_round`).

**The level-1 list** (engine mode, head digit x): E0 [x, e, r] → [x+4, e−1, r], E1 [x, 1^p, e, r] →
[2, 1^(p−1), x+3, e−1, r], and an exhausted list [x, 1^n] exits with the block x + 2n + 3. Clearing a digit at
depth p takes the head through U_p, with U_0(b) = b + 4 and U_(p+1)(b) = U_p^(b+1)(3) (`eng_clear`), so depth p is
f_p-class; a list of k twos is f_k, which makes one expansion f_ω (`eng_twos`, `eng_run`).

**The outer list** (marker mode):

    R0   Kbnd [a, e, r]          →+  Kbnd [G(a), e−1, r]                (K_R0: expansion + engine run)
    R1   Kbnd [a, 1^p, e, r]     →+  Kbnd [6, 1^(p−1), a+1, e−1, r]     (K_R1)
    EX   Kbnd [a, 1^n]           →+  the marker, then the block M = a + 2n + 1     (K_EX)

with G(a) = Wc(a/3, 4) + 2(a/3) + 2 (a ≡ 0 mod 3; similar for the other residues), where Wc(k, ·) clears k twos.
Clearing an outer digit at depth p takes the head through T_p, with T_0 = G and T_(p+1)(a) = T_p^a(6)
(`outer_clear`), so outer depth p is f_(ω+p)-class.

**The refill** (K1 = `1RA`, then A0, Q, R, S): with the marker and a block of M ones, R and S rewrite the block from
the right in pairs. If M is odd, the result is the outer list [2, 1^((M+1)/2), 2] (`Mk_odd`). If M is even, R reads
the blank at the left end and halts, with M/2 + 2 ones on the tape (`Mk_even`).

## 2. The run

| phase | what runs | result |
|---|---|---|
| boot | 9 steps from the blank tape | Kbnd [2, 2] (`boot`) |
| round 1 | R0 on [2, 2]: G(2) = 12 (by computation, `G_2`) | Kbnd [12, 1] |
| exhaustion | EX: M = 12 + 2 + 1 = 15, odd | refill: Kbnd [2, 1^8, 2] |
| the long part | `outer_clear` at depth 8 on the last digit 2 | Kbnd [T_8(2), 1^9] |
| exhaustion | EX: M = T_8(2) + 19 | (`run_to_Mk`) |
| halt | M is even, since T_8(2) is odd (`T_odd`) | R0 is read, N = M/2 + 2 ones (`run_to_halt`, `halt`) |

Parity is the only question about the end, and it is settled exactly: U_(p+1)(b) ≡ 3 (mod 4) for every b
(`U_mod`), so G(a) is odd for a ≥ 4 (`G_odd`), and T_(p+1)(a) is odd for a ≥ 1 (`T_odd`). So the machine halts at
the second exhaustion. The halting tape is 0^∞ [R on 0] (0 1)^(k+1) 1 0^∞ with 2k = T_8(2) + 19: N = k + 2 ones, and
2N = T_8(2) + 23 (`ones_c_halt`, `score_exact`).

**Size** (`BB19_JZ19.v`, section "Fast-growing hierarchy and the lower bound"). The recursions are compared with the
standard hierarchy by division-free conjugations:

- `U_dom`: 2z ≤ y implies 2 f_p(z) ≤ U_p(y);
- `G_dom`: 6z ≤ y implies 6 f_ω(z) ≤ G(y);
- `T_dom`: 6z ≤ y implies 6 f_(ω+p)(z) ≤ T_p(y), by induction on p, with the base point 6 absorbed by
  F^z(z) ≤ F^y(1) for y ≥ 2z (`base_absorb`);
- `T82_dom`: T_6(6) ≥ 30, T_7(6) = T_6^5(T_6(6)) ≥ 6 f_(ω+7)(5), and T_8(2) = T_7(T_7(6)) ≥ 6 f_(ω+7)(f_(ω+7)(5)).

So 2N = T_8(2) + 23 > 2 f_(ω+7)(f_(ω+7)(5)) (`sigma_lower_bound`).

## 3. Verification

[`verify_jz19/`](verify_jz19/): busycoq `bd2e36f`, Coq 8.20.1, a from-scratch build of about 25 s, built in CI
(job `bb13-bb14`). `probe.v` re-checks the transition table entry by entry against the string above (38 checks
generated from the string) and the blank start configuration. It prints the definitions the statements use and
confirms that `halt`, `score_exact` and `sigma_lower_bound` are closed under the global context.

[`tools/j19_writeup_chk.py`](tools/j19_writeup_chk.py) simulates the machine string (exactly, jumping only over
same-state runs), without the Coq files (a few seconds). It checks:

1. the boot: Kbnd [2, 2] after 9 steps;
2. the level-1 sweep rules E0, E1 and the exit on 400 random lists with random outer lists behind them;
3. the expansion of the outer head a = 1..30 (three tails each): the level-1 list [4, 1, 2^q] (a ≡ 1 mod 3) or
   [7, 1, 2^q], q = (a − 1) div 3, at the first engine-mode left end, with the outer list intact;
4. the refill for M = 1..59: the outer list [2, 1^((M+1)/2), 2] for odd M, and a halt with M/2 + 2 ones for even M;
5. the outer-round model (R0, R1, EX, refill) against the machine on 159 crafted outer lists (up to 12 rounds
   each), and on the first 13 outer boundaries from the blank tape (until G is too large to evaluate).

## 4. Comparisons (an argument, not a Coq lemma)

No Coq lemma compares this machine with another entry: none of them has a proved upper bound.

- f_(ω+k) is increasing in k and in its argument, and x < f_(ω+k)(x).
- **M19_fw4_A** (the previous 19-state entry here, proved f_(ω+4)(f_(ω+3)(9))) and **M19_fw4** (proved
  f_(ω+4)(f_(ω+2)(114))): with x = f_(ω+7)(5) ≥ f_(ω+3)(9), f_(ω+7)(x) ≥ f_(ω+4)(x) ≥ f_(ω+4)(f_(ω+3)(9)). So J19's
  bound is above both, and above every entry here with fewer states.
- **BB(20)**: Jacobzheng's J20 ([`../BB20/`](../BB20/)), proved f_(ω·2)(f_(ω+2)^2(f_10(2))), is far larger.
- Not yet reviewed by the bbchallenge community.

## Credit

Machine by Jacobzheng, listed as the BB(19) champion on the bbchallenge wiki's Champions page (with the bound
f_(ω+7)^2(5), "Not independently verified"). This project (the repository owner with Claude models (Anthropic) as
agents) found the rules above, wrote the Coq proof `BB19_JZ19.v` (2026-11-04), the probe, the checker and this
write-up. The proof confirms the wiki's claim: the machine halts, with σ > f_(ω+7)^2(5).
