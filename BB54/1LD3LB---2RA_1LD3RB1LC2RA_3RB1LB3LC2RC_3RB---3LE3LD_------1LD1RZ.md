# 1LD3LB---2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_3RB---3LE3LD_------1LD1RZ

The BB(5,4) champion, machine-checked with busycoq.

## 1. The machine

In the TNF notation of the Busy Beaver Challenge the machine is

    1LD3LB---2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_3RB---3LE3LD_------1LD1RZ

i.e. the transition table

    | state | 0        | 1        | 2        | 3        |
    | A     | 1LD      | 3LB      | ---      | 2RA      |
    | B     | 1LD      | 3RB      | 1LC      | 2RA      |
    | C     | 3RB      | 1LB      | 3LC      | 2RC      |
    | D     | 3RB      | ---      | 3LE      | 3LD      |
    | E     | ---      | ---      | 1LD      | 1RZ      |

`---` is an undefined transition; in busycoq it is modelled by `None`, which
stops the machine.  The only halting entry is therefore `E3 = 1RZ`.

The wiki's Champions page (checked 2026-11-08) lists exactly this string for
BB(5,4).  The machine

    1LD2RA3RB1LC_1LD2LA3RB---_2RA1LA3RC2LC_2RA---2LD2LE_------1RZ1LD

is the same machine after the renaming of the states A↔B and of the
symbols 2↔3.  `tools/explore.py` checks this exhaustively: it enumerates all
state/symbol pairs of both machines and reports that they agree under the
relabelling `state (0,1,3,2)` and `symbol (1,0,2,3,4)`.

Two features distinguish this machine from its BB(3,4) and BB(4,4)
relatives:

* the halting transition sits in the *extra* state `E` (`E3 = 1RZ`), not in
  `A` (`A2 = 1RZ`);
* the entries `A0 = 1LD` and `B0 = 1LD` open a new phase in which the
  machine alternates between the states `D` and `E` while it eats a block of
  twos.

Everything else — the sweeps `A3`, `B1`, `B2`, `B3`, `C0`, `C1`, `C2`, `C3`
— is literally the same as in the BB(3,4) champion, so Ligocki's machinery
ports over unchanged.

## 2. Conventions

A tape is written in the busycoq convention: the head is in the state `Q`,
the symbol under the head is `s`, the cells to the *left* are listed from the
head outwards, and so are the cells to the right.  `l {{Q}}> r` puts the head
on the first cell of `r`, `l <{{Q}} r` on the first cell of `l`.

Ligocki's configurations are

    B(k, n, m) R  =  0^inf  3^(2m+1)  2^k  A>  1^n  R ,

which in Coq is

    Definition Bcfg (k n m : nat) (r : Stream sym) : Q * tape :=
      ([2]^^k *> [3]^^(2 * m + 1) *> const 0) {{A}}> ([1]^^n *> r).

So the head is in the state `A` on the *first* of the `n` ones, the right
context is `1^(n-1) :: r`, and to the left of the head there are `k` twos,
then `2m+1` threes, then blanks.

The function `g` is Ligocki's Ackermann-like hierarchy

    g_0(m) = m+1,     g_(k+1)(m) = g_k^(2m+2)(0),

whose closed form is

    2 g_(k+1)(m) + 4 = 2 ↑^k (2m+4),          (g_closed)
    2 g_k^n(0) + 4   = 2 ↑^k (n+2).           (g_iter_closed)

## 3. Ligocki's machinery (proved)

Everything in this section is proved in `verify/BB54_rules.v`.

**The sweeps.**  `C` sweeps left over a block of twos writing threes
(`C_sweep_left`), `C` and `A` sweep right over a block of threes writing
twos (`C_right_3s`, `A_3s`), `B` sweeps right over a block of ones writing
threes (`B_1s`), and the combination `B3 = 2RA` followed by `A3 = 2RA`
sweeps right over a block of threes writing twos (`BA_sweep`).

**Lemma 1 (Ligocki).**  `3 2^k <B --> 2^k <B 1` in `2k+1` steps (`L1`).

**Corollary 2 (Ligocki).**  `3^m 2^k <B --> 2^k <B 1^m` (`Cor2`).

**The turnaround.**  `0^inf 2^(k+2) <B 1^m 3 1^n R --> 0^inf 3 2^(k+1) A> 1^(m+1) 3 1^n R`
(`turnaround`).

**Theorem 3 (Ligocki).**  `B(k+1, n, m) R -->* B(k+1, 0, g_k^n(m)) R`
(`B_rule`), proved by double induction on `k` and `n`.

## 4. The D/E phase (proved)

This is the part that is specific to the BB(5,4) machine.

Suppose the machine is in the state `A` on a blank cell, with `k` twos and a
block of `2m+1` threes to its left:

    0^inf  3^(2m+1)  2^k  A>  0^inf .

Then `A0 = 1LD` writes a one on the blank and steps left onto the first
two, and the machine eats the twos from right to left, alternating between
the states `D` and `E`:

    D2 = 3LE : write a three, step left, go to E
    E2 = 1LD : write a one,  step left, go to D

After `k` such steps the machine stands on the first three of the block,
in the state `D` if `k` is even and in the state `E` if `k` is odd.

* **`k` odd.**  The machine is in the state `E` on a three, and `E3 = 1RZ`
  halts it.  This is `D_phase_halt` (for `k = 3`) and `D_phase_halt_1`
  (for `k = 1`).
* **`k` even.**  The state `D` walks left over the whole block of threes
  (`D3 = 3LD`), writes a three on the blank in front of it (`D0 = 3RB`),
  rewrites the first three of the block as a two (`B3 = 2RA`) and sweeps
  right over the rest of the block, turning the threes into twos
  (`A3 = 2RA`).  The machine ends in the state `A` on a one, the block of
  threes has become a block of `2m+1` twos, and the right context has
  grown by `3 1`.  For `k = 2` this is `D_phase_raw`:

      B(2, 0, m) 0^inf  -->*  B(2m+1, 1, 0) [3 1] 0^inf .

  (The general `k` even case produces the right context `(3 1)^(k/2)`; the
  proof in `D_phase_raw` covers `k = 2`, which is the case the run meets.)

## 5. The macro steps (proved)

The run of the machine is organised in three macro steps, all proved in
`verify/BB54_rules.v`:

    macro_descent   B(k, n+1, m, r) -->* B(k-1, 2m+2, 0) [3 1^n r]
    B1_iter         B(1, n, m, r)    -->* B(1, 0, m+n) r
    a3_step         B(k, 0, m, 3 1^b r) -->* B(k+1, b, m) r

`macro_descent` is the A1 step followed by `Cor2` and the turnaround;
`B1_iter` is `B1_step` iterated; `a3_step` is a single `A3 = 2RA` step.

Composing them gives the **chain**, which is the engine of the run:

    chain_step   B(2, n+1, m, [3 r]) -->* B(2, n, 2m+2, [3 r])
    chain        B(2, n+1, m, [3 r]) -->* B(2, 0, 2^(n+1) (m+2) - 2) [3 r]

One macro cycle lowers `n` by one and doubles `m`; after `n+1` cycles the
parameter `m` — the size of the block of threes on the tape — has been
replaced by `2^(n+1) (m+2) - 2`.  This is where the run grows so fast.

## 6. The run (proved)

    0^inf A> 0^inf  -(9 steps)->  B(2, 1, 0)  0^inf
        ->  B(2, 0, 2)  0^inf                     (B_rule, level 1)
        ->  B(5, 1, 0)  [3 1] 0^inf               (the D/E phase, 14 steps)
        ->  B(5, 0, g_4(0))  [3 1] 0^inf          (B_rule, level 4)

The tape of the last configuration is

    0^inf  3^(2 g_4(0) + 1)  2^5  A>  3 1  0^inf ,

so it carries `(2 g_4(0) + 1) + 5 + 2 = 2 g_4(0) + 8` nonzero symbols, and

    2 g_4(0) + 4 = 2 ↑^3 4 = 2 ↑↑↑ 4 = 2 ↑↑ 65536 ,

so the tape carries (2 ↑↑ 65536) + 4 nonzero symbols at that point of the run.  The machine never writes a
blank over a non-blank cell (the only symbol it writes besides 1, 2, 3 is
nothing), so the number of nonzero cells never decreases: the final σ of the
machine is at least that.

## 7. The main regime and the halting (proved)

The D/E phase of Section 4 works for an arbitrary number of twos; this is
proved in `verify/BB54_dphase.v` (`eat2`, `eat_reach`, `eat_reach_odd`,
`D_phase_even`, `D_phase_odd`):

* **even** number of twos: the machine continues, the block of threes
  becomes a block of `2m+1` twos, and the right context becomes
  `(3 1)^(k/2)`;
* **odd** number of twos: the machine arrives in the state `E` on the first
  three of the block and halts.

After the two descents of Section 6 the machine is in
`B(5, 0, g_4(0)) [3 1] 0^inf`.  The A3 sweep and the B rule at level 5 give

    B(5, 0, g_4(0)) [3 1] 0^inf
        ->  B(6, 1, g_4(0)) 0^inf                  (a3_step)
        ->  B(6, 0, X) 0^inf                      (B_rule, level 5)

with `X = g_5(g_4(0))`, and the D/E phase then sees `6` twos -- an even
number -- and produces

    B(2X+1, 1, 0) [3 1]^3 0^inf .

From there the run consists of **levels**.  A level is `T` rounds, each of
them a B rule followed by an A3 sweep (`level`, `level_gen` in
`verify/BB54_dphase.v`); a level

* raises the number of twos by `T`,
* replaces the number `m` of threes by the nested application
  `gchain k T m` of the `g`'s,
* and ends with another D/E phase.

So the main regime is

    level 0:  T = 3 rounds
        B(2X+1, 1, 0) [3 1]^3 0^inf
            ->  B(2X+4, 0, M0) 0^inf             (3 rounds, M0 = gchain (2X) 3 0)
            ->  the D/E phase sees 2X+4 twos (even) and continues
            ->  B(2M0+1, 1, 0) [3 1]^(X+2) 0^inf

    level 1:  T = X+2 rounds
            ->  B(2M0+X+3, 0, M1) 0^inf          (M1 = gchain (2M0) (X+2) 0)
            ->  the D/E phase sees 2M0+X+3 twos

and `2M0+X+3` is **odd**, because `X = g_5(g_4(0))` is even: `g_j(m)` is even
for every `j ≥ 1` (`g_even` in `verify/BB54_halt.v`, from `g_1(m) = 2m+2`).
The machine therefore arrives in the state `E` on the first three of the
block of threes, where `E3 = 1RZ` halts it.  This is the theorem
`bb54_halt` of `verify/BB54_halt.v`:

    c0 -->* E;; ( 3^(2 M1) E> 3 (1 3)^(M0 + X/2 + 1) 1 0^inf )

The final tape carries

    2 M1 + 1 + 1 + 2 (M0 + X/2 + 1) + 1  =  2 M1 + 2 M0 + X + 5

nonzero cells, which is the exact σ of the machine (`sigma_final`,
`bb54_halt_main`).

Note that the recursion of the run is *not* the one guessed by the
symbolic macro model of an earlier version of this development: the run has
**two** levels in the main regime, not 65533 of them, and the number 65533
of the wiki's bound does not occur in it.

## 8. What is proved and what is not

**Proved (axiom-free, see `verify/probe.log`):** the start, Ligocki's
descent rule and the closed form of `g`, the D/E phase in both of its
outcomes and for an arbitrary number of twos, the three macro steps, the
chain, the fact that the machine reaches `B(5, 0, g_4(0)) [3 1] 0^inf` with
`(2 ↑↑ 65536) + 4` nonzero symbols on the tape, **that the machine halts**
(`bb54_halts : halts tm c0`), and
**the exact value of its σ**, namely `2 M1 + 2 M0 + X + 5`.

**Not proved in Coq:** any comparison of σ with the wiki's bound (below).

### The wiki's bound and an upper comparison number

The wiki's Champions page lists, for BB(5,4), the **runtime** bound

    > f_ω² (10 ↑^4 10 ↑↑ 65533) ,

Jacobzheng's bound (2026), which the wiki marks *"not independently verified"*.
The hand calculation below shows that it lies below σ, and that

    f_ω² (2 ↑^4 2 ↑^3 4)  =  f_ω² (2X + 4)

lies above σ: it is an *upper* bound for σ, not a lower bound.  Here f_ω(n)
is `2 ↑^(n+1)(n+3)` (`f_omega`), a Knuth-arrow function at least as large as
the fast-growing hierarchy's f_ω.  The inner argument `2X + 4` is
*proved* to be a number of the machine: `BB54_bound.v`
establishes

    2 ↑^4 2 ↑^3 4  =  2X + 4         (X_inner)

with `X = g_5(g_4(0))` the descent parameter of the main regime — the very
number of twos that the first D/E phase of the main regime has to erase
(`bb54_dchain`).

### The comparison

**Proved in Coq** are the identification of the two numbers with the machine
and the direction of the inner towers:

* `target = f_ω²(10 ↑^4 10 ↑↑ 65533)` (`target_is_jacobzheng`, an unfolding
  of the definition);
* `2 ↑^4 2 ↑^3 4 = 2X + 4` (`X_inner`) and hence
  `f_ω²(2 ↑^4 2 ↑^3 4) = f_ω²(2X + 4)` (`target_refined_eq`);
* `10 ↑↑ 65533 < 2 ↑^3 4` (`tower10_lt`, `tower10_lt_tower3` of
  `BB54_tower.v`), proved with the invariant
  `4 · (10 ↑↑ n) + 4 ≤ 2 ↑↑ (n+3)` (`tower10_inv`).

**Not proved in Coq:** the comparison of the *levels* of the three numbers.
It is a hand calculation on the closed forms, and it goes as follows.  With
`2 g_(k+1)(m) + 4 = 2 ↑^k (2m+4)` (Ligocki's closed form, `g_closed`), call
the number of arrows of a number of the form `2 ↑^k (·)` its **level**:

| number | closed form | level |
| --- | --- | --- |
| `g_4(0)` | `2 ↑^3 4 / 2` | 3 |
| `X = g_5(g_4(0))` | `2 ↑^4 (2 ↑^3 4) / 2` | 4 |
| `M0 = g_(2X+3)(g_(2X+2)(g_(2X+1)(g_(2X) 0)))` | `2 ↑^(2X+2) (…)/2` | `2X+2` |
| `M1 = g_(2M0+X+1)(…)` | `2 ↑^(2M0+X) (…)/2` | `2M0+X` |
| `σ = 2 M1 + 2 M0 + X + 5` | `2 ↑^(2M0+X) (…)` | `2M0+X` |

The level of σ, `2M0+X`, is itself a number of level `2X+2` (because
`2 M0 = 2 ↑^(2X+2) (… ) - 4`).  Since `f_ω(n) = 2 ↑^(n+1)(n+3)`, the two
bounds have the levels

| number | level | level of the level |
| --- | --- | --- |
| `f_ω²(10 ↑^4 10 ↑↑ 65533)` | `f_ω(A)+1`, `A = 10 ↑^4 10 ↑↑ 65533` | `A+1` — level 4, argument `10 ↑↑ 65533` |
| `f_ω²(2 ↑^4 2 ↑^3 4)` | `f_ω(B)+1`, `B = 2X+4` | `B+1 = 2X+5` — level 4, argument `2 ↑^3 4` |
| `σ` | `2M0+X` | `2X+2` — level 4, argument `2 ↑^3 4` |

Three elementary facts about the towers do the work:

* `10 ↑↑ n < 2 ↑↑ (n+3)` for every `n ≥ 1`; in particular

      10 ↑↑ 65533  <  2 ↑↑ 65536  =  2 ↑^3 4 ,

  — the base-10 tower of the wiki's bound is *below* the base-2 tower of the
  refined bound, not above it.  (This one is machine-checked, see above.);
* at the 4-arrow level, changing the base from 2 to 10 costs at most two
  levels: `2 ↑^4 m < 10 ↑^4 m < 2 ↑^4 (m+2)`;
* a number of strictly larger level is larger, whatever its argument.

It follows that `A = 10 ↑^4 (10 ↑↑ 65533) < 2 ↑^4 (2 ↑^3 4) = B`, and hence

    level of Jacobzheng's bound = A+1 < 2X+2 = level of σ
                                  < 2X+5 = level of the refined bound,

which gives the ordering

    f_ω² (10 ↑^4 10 ↑↑ 65533)   <   σ   <   f_ω² (2 ↑^4 2 ↑^3 4) .

So, on paper, σ > f_ω²(10 ↑^4 10 ↑↑ 65533): Jacobzheng's bound lies below
the σ of the machine, and f_ω²(2 ↑^4 2 ↑^3 4) lies above it.  (The wiki's entry is a statement about the *runtime* of
the machine, which is at least σ; the comparison above locates σ itself
between the two numbers.)

