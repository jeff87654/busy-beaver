# A BB(6, 4) machine breaking four levels of f_(ω+1)

```
1RB3LC1LD2RA_2RC1RF2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE_0LC0LB0LD1RZ
```

Found by loader3229 on 2026-11-17.
This is a 6-state, 4-symbol Turing machine that halts from the blank tape with a
score (number of nonzero cells after the halting write)

    σ  >  f_(ω+1)( f_(ω+1)( f_(ω+1)( f_(ω+1)( 65536 ) ) ) )

where f_(ω+1) is the fast-growing hierarchy function at ordinal ω+1 (Coq:
`FGH (osucc omega)`).  Both the halting and the inequality are machine-checked
in Coq, axiom-free (see [`verify/`](verify/)).

## Origin

The machine is the BB(5,4) champion **54-L**

    1RB3LC1LD2RA_2RC1RZ2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE

with a single change: the halting transition `B1 = 1RZ` is replaced by
`B1 = 1RF`, and a sixth state F is added with the TNF behaviour

    F0 = 0LC    F1 = 0LB    F2 = 0LD    F3 = 1RZ (halt).

Consequently the first part of the run is *identical* to 54-L: every macro
step proved for 54-L applies verbatim until the configuration in which 54-L
halts.  There the new state F takes over and performs four more levels.

## The run

Let

    Bcfg k n m r  =  0^inf  3^(2m+1)  2^k  A>  1^n  r

(the busycoq left stream is nearest-first).  The 54-L part of the run is

    0^inf A> 0^inf
      ->  B(5, 1, 0) 0^inf                       (blank-tape start)
      ->  B(5, 0, M1) 0^inf,   M1 = g_4(0)        (B rule, level 4)
      ->  B(1, 0, 1)  2^(2 M1 + 5)  0 1 1 0^inf  (the last 54-L sweep)

Here 54-L would read `B1 = 1RZ` and halt.  Instead `B1 = 1RF` starts a
four-round regime.  In each round the machine (i) sweeps the reservoir of
twos back into the counter, (ii) applies the `D_chain` to reach the next
`B(k, 0, m, marker)` configuration, and (iii) rewrites the right-hand marker
according to the state-F automaton.  The four marker transitions are exactly

    B(k,0,m) 0 1 1 0^inf    ->  B(1,0,1) 2^(k+2m) 0 3 1 0^inf
    B(k,0,m) 0 3 1 0^inf    ->  B(1,0,1) 2^(k+2m) 0 0 1 0^inf
    B(k,0,m) 0 0 1 0^inf    ->  B(1,0,1) 2^(k+2m) 0 1 3 1 0^inf
    B(k,0,m) 0 1 3 1 0^inf  ->  halt

(the first sweep, over `0^inf`, is 54-L's `B_sweep`).  Writing
`P_{i+1} = step_pair^{c_i}(P_i)` with

    step_pair (k, m) = (2m, g_(2m)^(2k+2)(0)),

the four rounds produce parameters `(k1,m1), …, (k4,m4)`, and the machine
halts with the tape

    0^inf  3^(2 m4 + 1)  2^k4  1  1  F>  3  1  0^inf ,

so that

    σ = 2 m4 + k4 + 5 .

## Why four levels of f_(ω+1)

Define the Knuth-arrow majorant

    f_ω(n)    = 2 ↑^(n+1) (n + 3)
    f_(ω+1)(n) = f_ω^n(n) = FGH (osucc omega) n  (up to the standard identification).

Two facts drive the bound:

* `step_pair` is majorised by one application of `f_ω` (in fact
  `2·snd(step_pair(k,m)) + 4 = 2 ↑^(2m)(k+4)`), so a `D_chain` of length `c`
  lifts the parameter by roughly `f_ω^{c/2}`;
* each round's reservoir length `k + 2m` supplies a fresh, huge number of
  such lifts.

Threading these through the four rounds gives

    f_(ω+1)^4 (2^16)  <  σ ,

proved in two stages:

* `BB64_bound.sigma_beats_four_f_omega1` proves the Knuth-arrow version
  `f_omega1^4(2^16) < sigma`, where `f_omega1 n = f_omega^n(n)`;
* `FGH_BB64.bb64_fgh_four` bridges `f_omega1` to the genuine fast-growing
  hierarchy (via the bundled `FGH/` library, `fw_le_F`) and proves the exact
  statement `Nat.iter 4 (FGH (osucc omega)) (2^16) < sigma`.

Note `f_omega1 n = f_ω^n(n)` is a *Knuth-arrow* upper bound for the FGH
`f_(ω+1)(n) = f_ω^n(n)` at these arguments (the Knuth `f_ω` dominates the FGH
`f_ω`, hence its iterates dominate `f_(ω+1)`), so the inequality is in the
right direction.

## Build and check

    cd verify
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

See [`verify/README.md`](verify/README.md) for the list of theorems and the
`Print Assumptions` check.  `tools/` holds the Python simulators used to
discover the macro rules and to cross-check the trajectory.
