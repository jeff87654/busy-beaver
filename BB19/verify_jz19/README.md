# Coq proofs for `1RQ1RL_0LI1RC_0LD1LF_0RA1LD_1RB1RE_1LH0LG_1LF1LG_1RE1RM_1LJ1LI_0LK1LI_1RL1RA_0RL0RE_0LN1RM_1LO0LO_1RE1LP_1LN1LN_1LR1RQ_1RZ1LS_0LE0LR` (J19, Jacobzheng)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For this machine (R0 undefined = the halt, `1RZ` in the string) it proves:

- `BB19_JZ19.halt : halts tm c0`: the machine halts from the blank tape;
- `BB19_JZ19.score_exact`: the halting tape holds exactly N ones with `2 * N = T 8 2 + 23`, where `T` is the
  explicit recursion of the file (below);
- `BB19_JZ19.sigma_lower_bound`: the halting tape holds N ones with `f_wk 7 (f_wk 7 5) < N`, that is
  f_(ω+7)(f_(ω+7)(5)) < N.

As published:

    Theorem halt : halts tm c0.
    Theorem score_exact :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ 2 * N = T 8 2 + 23.
    Theorem sigma_lower_bound :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_wk 7 (f_wk 7 5) < N.

Since the machine is deterministic, the halted configuration reached from `c0` is unique, so these say that the
score is that N plus one: the machine halts in state R reading 0, and the halting transition `1RZ` writes a 1, so
σ = N + 1. The machine's own recursion, as defined in `BB19_JZ19.v`:

    U 0 b = b + 4,          U (p+1) b = (U p)^(b+1) (3)        (engine: clearing a level-1 digit at depth p)
    Wc 0 b = b,             Wc (k+1) b = U k (Wc k b)          (clearing k leading 2s)
    G a = Wc (a/3) 4 + 2(a/3) + 2          if a mod 3 = 0
          Wc (a/3 + 1) 1 + 2(a/3 + 1) + 2  if a mod 3 = 1
          Wc (a/3 + 1) 4 + 2(a/3 + 1) + 2  if a mod 3 = 2   (an outer R0 round: expansion + engine run)
    T 0 a = G a,            T (p+1) a = (T p)^a (6)            (outer: clearing a digit at depth p)

The fast-growing hierarchy is the standard one, defined in the same file: `f 0 n = n+1`, `f (k+1) n = (f k)^n n`,
`f_omega n = f n n`, `f_wk 0 = f_omega`, `f_wk (k+1) n = (f_wk k)^n n`, so `f_wk k` is f_(ω+k);
`iter 0 g x = x`, `iter (n+1) g x = g (iter n g x)`. `ones c N` says that `c`'s tape is a finite word padded with 0s
on both sides holding N ones.

## Files

| file | content |
|---|---|
| `BB192.v`, `Individual192.v` | busycoq instantiated for 19 states (the same files as in [`../verify/`](../verify/)). The 17th, 18th and 19th states (letters Q, R and S of the machine string) are the constructors `QQ`, `RR` and `SS`, because `Q` is busycoq's state type, `R` its direction and `S` is `Datatypes.S`. The states `L` and `O` shadow busycoq's direction `L` and `Datatypes.O`, so tables write `TM.L` / `TM.R`. |
| `BB19_JZ19.v` | the proof: the table; walk lemmas; the sweep `SW b p W R` with its four rules (`SW_pass`, `SW_dec0`, `SW_dec1`, `SW_end`), generic in the left context W (blank = engine mode, a single 1 = marker mode); the mode boundaries (`H_engine`, `K_round`, the three expansion cases `EXP0`–`EXP2`, `REFILL_even`, `REFILL_odd`); digit lists on the tape (`enc`, `sw`, `Kbnd`, `Mk`); the engine macros (`eng_clear`, `eng_twos`, `eng_run`); the outer rounds (`K_R0`, `K_R1`, `K_EX`, `Mk_odd`, `Mk_even`, `outer_clear`); parity (`U_mod`, `G_odd`, `T_odd`); the run (`boot`, `run_to_Mk`, `run_to_halt`, `halt`); the score (`ones_c_halt`, `score_exact`); and the bound (`U_dom`, `G_dom`, `T_dom`, `T82_dom`, `sigma_lower_bound`). |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build (about 25 s) and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `probe.v` checks the compiled transition table against the machine string entry by entry
(38 checks generated from the string, not from the Coq file) and the blank start configuration. It prints the
definitions the statements use and runs `Print Assumptions` on the three theorems above: all three are closed under
the global context. CI job `bb13-bb14` runs the same script.

The proof was also checked with this project's `check.py` (the statement `halts tm c0` read from the file, the
table compared with the machine string, `Print Assumptions halt` closed): PASS, 2026-11-07.
