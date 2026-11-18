# 1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC (BB(3,5) champion)

Source: the BB(3,5) champion, listed on the Busy Beaver Wiki
(<https://busybeaverwiki.org/index.php?title=BB(3,5)>); the machine was found by
S. Ligocki / M. Marx, and the runtime bound `> f_ω(2 ↑^15 5)` quoted there is marked
*"Not independently verified"*.  This file restates the mathematics of the run; the Coq
development in [verify/](verify/) follows it and is machine-checked.

    0    1    2    3    4
A   1RB  3LB  4LC  2RA  4LB
B   2LC  3RB  1LC  2RA  1RZ
C   3RB  1LB  3LC  2RC  4LC

Halting transition: **B4 = 1RZ** (B reading a 4 writes 1, moves right, halts).
In busycoq (`verify/BB35_rules.v`) this is the only `None` entry of `tm`; `verify/probe.v`
re-parses the machine string above and checks that all fifteen entries agree.

## Notation

- `X` and `Y` in a rule stand for arbitrary left/right context; `A>` = state A, head on the
  first cell of the block to the right (moving right); `<B` = state B, head on the last
  cell of the block to the left.
- Left streams in Coq are written from the head outwards, so `0^inf 3^(2m+1) 2^k A> 1^n R`
  is `Bcfg k n m r` with left stream `[2]^^k *> [3]^^(2m+1) *> const 0`.
- "X → Y" means zero or more steps (Coq's `-->*`).

The one configuration family (Ligocki):

    B(k, n, m) R  =  0^inf  3^(2m+1)  2^k  A>  1^n  R

and the functions (Coq: `g` in `BB35_rules.v`):

    g_0(m)     =  m + 1
    g_(k+1)(m) =  g_k^(2m+2)(0)

## The run

The BB(3,5) champion agrees with the BB(3,4) champion on the symbols 0..3 and on the whole
descent; only the halting transition differs (`A2 = 1RZ` in BB(3,4), `B4 = 1RZ` in BB(3,5)).
In BB(3,5) state `A` does not halt on the 2, it executes `A2 = 4LC`, which starts the
BB(3,5)-specific tail.  The whole run is

    0^inf A> 0^inf  -(241)->  B(16, 3, 0)  2  0^inf
        ->  B(16, 0, g_15^3(0))  2  0^inf                       (Theorem 3, the descent)
        -(rule 1)->  B(K+12, 0, 0)  4  0^inf                   (K = 2 g_15^3(0) + 4)
        -(rule 2, K+12 times)->  B(1, 0, mfin)  4  0^inf
        -(rule 3)->  0^inf  3^(2 mfin + 3)  B> 4  0^inf          (halt)

with `mfin = desc (K+12) 0` the value of the "m" parameter at the end of the rule-2 phase.

## The rules

1. **Start** (`BB35_start.v`, `start`): the blank tape reaches `B(16,3,0) 2 0^inf` in
   exactly 241 steps.  This is literally the same run as for BB(3,4) (the two machines
   agree until the first 2 is read), and `BB35_start.v` is the file of BB34's `BB34_start.v`
   with the machine replaced.

2. **Lemma 1 / Corollary 2 / Theorem 3** (`BB35_rules.v`, `L1`, `Cor2`, `B_rule`): Ligocki's
   descent, ported verbatim from BB(3,4):

        B(k, n, m) R  →  B(k, 0, g_(k-1)^n(m)) R          (k ≥ 1)

   proved by double induction, using the sweeps `C_sweep_left`, `C_right_3s`, `A_3s`,
   `B_1s`, `BA_sweep` and the "turnaround"

        0^inf 2^(k+1) <B 1^(2m+1) 3 1^n R  →  0^inf 3 2^k A> 1^(2m+2) 3 1^n R .

3. **Rule 1** (`BB35_rules.v`, `rule1`): the head is in state `A` on the 2 that follows the
   block `3^(2m+1) 2^k`; `A2 = 4LC` writes a 4 and moves left onto the block of twos, and
   the machine then eats the `2m+1` threes one at a time (each round is `StepE` in Coq),
   which grows the block of twos:

        B(k+1, 0, m) 2  →  B(k+1+2m, 0, 0) 4 .

   In the notation of the original request: `B(k,0,m) 2 → B(k+2m+1,0,0) 4`.

4. **Rule 2** (`BB35_rules.v`, `rule2`): the head is in state `A` on the 4; `A4 = 4LB`
   writes a 4 and moves left, Corollary 2 turns the `2m+1` threes into `2m+1` ones, and the
   generalised turnaround `GT` (the turnaround of BB(3,4) with an arbitrary right context)
   moves the head back to the right:

        B(k+2, 0, m) 4  →  B(k+1, 2m+2, 0) 4 .

   In the notation of the original request: `B(k,0,m) 4 → B(k-1,2m+2,0) 4` (for `k ≥ 2`).
   Each application of rule 2 is followed by one application of Theorem 3 (the descent),
   which is what makes the `m` parameter grow; after `N` applications the machine is in
   `B(1, 0, desc N m) 4` (`desc` in `BB35_run.v`).

5. **Rule 3** (`BB35_rules.v`, `rule3`): the head is in state `A` on the 4 that follows the
   last 2; `A4 = 4LB` moves left onto the 2, and the machine then performs `2m+3` cycles
   (`cycle3` in Coq) that turn the single 2 into a block of `2m+3` threes and move the head
   back onto the 4, in state `B`:

        B(1, 0, m) 4  →  0^inf 3^(2m+3) B> 4 0^inf .

   Now `B4 = 1RZ` is executed and the machine halts.  The number of non-blank cells on the
   final tape is `2m+4`.

## The score

Closed form of the `g` hierarchy (BB35_score.v, `g_closed`), by induction on k, using
`Nat.iter` lemmas and the coincidence `2 ↑^k 2 = 4`:

    2 * g_(k+1)(m) + 4  =  2 ↑^k (2m+4)

Corollary (`g_iter_closed`): `2 * g_k^n(0) + 4 = 2 ↑^k (n+2)`; with k = 15, n = 3:

    2 * g_15^3(0) + 4  =  2 ↑^15 5  =:  K .

The rule-2 phase applies the descent `K+12` times, and the closed form of that phase
(`desc_closed_gen`) turns the score into a **nested Knuth expression** (`aw j n x` is
`2 ↑^j (2 ↑^(j+1) ( ... (2 ↑^(n-1) x) ... ))`):

    sigma = 2 * mfin + 4  =  2 ↑^0 (2 ↑^1 ( ... (2 ↑^(K+11) 4) ... )) .

The innermost term of that expression is `2 ↑^(K+11) 4`, and the expression is at least
twice that term, so

    sigma  >  2 ↑^(K+11) 4 .

### Comparison with `f_ω(2 ↑^15 5)`

The Busy Beaver wiki quotes the **runtime** of the champion as `> f_ω(2 ↑^15 5)` with
`f_ω` the omega-th element of the fast-growing hierarchy in Wainer's normalisation
(`F_0(n) = n+3`, `F_(k+1)(n) = F_k^(n+3)(n)`, `F_ω(n) = F_n(n)`).  The arrow normal form of
that function is

    f_ω(n)  =  2 ↑^(n+1) (n+3)         (BB35_score.v, `f_omega`)

which **upper-bounds** `F_n(n)`, so every inequality proved with it also holds for the
hierarchy's own value.  With `n = K = 2 ↑^15 5` this is

    f_ω(K)  =  2 ↑^(K+1) (K+3)  =  2 ↑^(2g+5) (2g+7)        (g = g_15^3(0)).

Now `K+11 = 2g+15` arrows beat `K+1 = 2g+5` arrows, because *two* more arrows already beat
a bigger argument (`knuth_2_4_S`: `2 ↑^(k+3) 4 > 2 ↑^(k+1) (k+5)`), and `knuth 2 4` is
monotone in the argument:

    2 ↑^(2g+15) 4   ≥   2 ↑^(2g+7) 4   >   2 ↑^(2g+5) (2g+9)   ≥   2 ↑^(2g+5) (2g+7)
                                          \___________________________________________/
                                                     f_ω(K)

Hence

    sigma  >  f_ω(2 ↑^15 5) .

This is the content of `BB35_score.sigma_gt_fomega` and `BB35_score.fomega_lt_sigma`; the
whole statement is bundled in `BB35_score.bb35_main`.

### Exact value of the score

    sigma  =  2 ↑^0 (2 ↑^1 (2 ↑^2 ( ... (2 ↑^(2g+15) 4) ... )))      (2g+16 arrow levels)

which is `2 ↑^0 (2 ↑^1 (... (2 ↑^(2 ↑^15 5 + 11) 4) ...)))` in terms of `2 ↑^15 5`.
It is of course not a number that can be written down; the Coq development keeps it
symbolic from beginning to end (`g15` is sealed, `knuth 15 2 5` is never evaluated).

## What is proved and what is not

**Proved (axiom-free Coq, `verify/`).**

- the machine halts from the blank tape (`bb35_halts`);
- the exact halting configuration `0^inf 3^(2 mfin + 3) B> 4 0^inf` (`reaches_final`,
  `final_halted`), and that it contains exactly `sigma = 2 * mfin + 4` non-blank cells;
- the closed form of the score and the inequality `f_ω(2 ↑^15 5) < sigma`
  (`sigma_closed`, `sigma_gt_fomega`, `fomega_lt_sigma`, `bb35_main`).

**Not proved here.**

- the *runtime* bound of the wiki (`> f_ω(2 ↑^15 5)` steps).  The proof above bounds the
  **space** (σ), which is what was asked for; the runtime is a different quantity and is
  not counted by the development (the steps of the macro phases are not enumerated).
- the claim that `2 ↑^15 5` is the exact optimum for the runtime of any 3-state, 5-symbol
  machine; that is an open question.
