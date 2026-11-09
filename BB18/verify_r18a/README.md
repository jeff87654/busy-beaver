# Coq proofs for `1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_0LQ0LO_1LR1LP_0LQ1LN_0RO1LB_0LL1RZ` (R18a)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For this machine (R1 undefined = the halt, `1RZ` in the string) it proves:

- `BB18_R18a.halt : halts tm c0`: the machine halts from the blank tape;
- `BB18_R18a.score_exact`: the halting tape holds exactly 2c + 2 ones, for the c given by the explicit recursion
  of the file (below);
- `BB18_R18a.sigma_lower_bound`: the halting tape holds N ones with
  `f_w2 (f_omega (f_omega (f 10 2))) < N`, that is f_(ω·2)(f_ω(f_ω(f_10(2)))) < N;
- `BB18_R18a.beats_J19`: the same with `f_wk 7 (f_wk 7 5) < N` (J19's proved BB(19) bound, f_(ω+7)(f_(ω+7)(5)));
- `BB18_R18a.beats_M18_229`: the same with `iter 229 (f_wk 3) 9 < N` (M18_229round's proved BB(18) bound,
  f_(ω+3)^229(9)).

As published:

    Theorem halt : halts tm c0.
    Theorem score_exact : exists k a2 c cfg,
      iter 3 G 28 + 8 = 3 * S k /\ a2 = hoc 2 k 28 /\ a2 + 2 * (k + 2) + 2 = 3 * c + 1 /\
      c0 -->* cfg /\ halted tm cfg /\ ones cfg (2 * c + 2).
    Theorem sigma_lower_bound :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_w2 (f_omega (f_omega (f 10 2))) < N.
    Theorem beats_J19 : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_wk 7 (f_wk 7 5) < N.
    Theorem beats_M18_229 : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ iter 229 (f_wk 3) 9 < N.

Since the machine is deterministic, the halted configuration reached from `c0` is unique, so these say that the
score is that N: the machine halts in state R reading 1, and the halting transition `1RZ` writes a 1 on it, so
σ = N = 2c + 2. The machine's recursion, as defined in `BB18_R18a.v` (J20's, from `BB20_JZ20.v`):

    h 0 x = x + 4,          h (m+1) x = (h m)^(x+2) (2)        (inner list: reducing a digit at position m+2)
    hc m 0 x = x,           hc m (n+1) x = hc (m+1) n (h m x)  (n digits 2 at positions m+2, m+3, ...)
    G a = hc 1 (a/3) (a mod 3 + 3) + 2(a/3) + 4                (an outer R0 round: expansion + inner run)
    ho 0 a = G a,           ho (m+1) a = (ho m)^(a+1) (3)      (outer list: reducing a digit at level m)
    hoc m 0 a = a,          hoc m (n+1) a = hoc (m+1) n (ho m a)

The fast-growing hierarchy is the standard one, defined in the same file: `f 0 n = n+1`, `f (k+1) n = (f k)^n n`,
`f_omega n = f n n`, `f_wk 0 = f_omega`, `f_wk (k+1) n = (f_wk k)^n n` (f_(ω+k)), and `f_w2 n = f_wk n n`
(f_(ω·2), with the fundamental sequence ω·2[n] = ω+n); `iter 0 g x = x`, `iter (n+1) g x = g (iter n g x)`.
`f`, `f_omega` and `iter` are defined as in `BB19_JZ19.v` (J19) and `BB18_229round_fw3.v` (M18_229round), and
`f_wk` as in `BB19_JZ19.v`, so `beats_J19` states J19's bound exactly as that file does; `BB18_229round_fw3.v` writes
f_(ω+3) as `f_omega3` (`f_omega1 n = iter n f_omega n`, and so on), which unfolds to the same function as `f_wk 3`. `ones c N` says that `c`'s tape is a finite word padded
with 0s on both sides holding N ones.

## Files

| file | content |
|---|---|
| `BB182.v`, `Individual182.v` | busycoq instantiated for 18 states (as in `../verify/`). The 17th and 18th states (letters Q and R of the machine string) are the constructors `QQ` and `RR`, because `Q` is busycoq's state type and `R` its direction. The states `L` and `O` shadow busycoq's direction `L` and `Datatypes.O`, so tables write `TM.L` / `TM.R`. |
| `BB18_R18a.v` | the proof, adapted from `BB20_JZ20.v`: the table; walk lemmas; digit lists on the tape (`rl`); the sweep `SW` (`SW_pass`, `SW_E`, `SW_exit_in`, `SW_exit_out`); the inner boundary `CI` (`CI_E0`, `CI_E1`, `CI_exit`); the expansion `EXP` (three residue cases, now exiting through Q and R); the refill (`RN`, `RF_halt`, `RF_A`, `RF_B`); the outer boundary `CO` (`OEX`, `R1`, `R0`); level lemmas (`LV_in`, `Chain_in`, `LV_out`, `Chain_out`); the mod-3 invariant (`h_P1`, `G_P1`, `ho_P1`, `hoc_mod`, `K_gen`, `C_gen`); the run (`boot`, `run_gen`, `run`, `halt`); the score (`ones_Hh`, `score_exact`); the bound (`transfer`, `h_dom`, `G_dom`, `ho_dom`, `hc_tower`, `G28`, `hoc_last`, `bound_gen`, `sigma_lower_bound`); and the comparisons (`Y_big`, `J19_dom`, `M18_dom`, `beats_J19`, `beats_M18_229`). |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build (about 30 s) and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `probe.v` checks the compiled transition table against the machine string entry by entry
(36 checks generated from the string, not from the Coq file) and the blank start configuration. It prints the
definitions the statements use and runs `Print Assumptions` on the five theorems above: all five are closed under
the global context. CI job `bb13-bb14` runs the same script.

The proof was also checked with this project's `check.py` (the statement `halts tm c0` read from the file, the
table compared with the machine string, `Print Assumptions halt` closed): PASS, 2026-11-08.
