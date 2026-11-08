# Coq proofs for `1LH0LG_0LI1RC_0LD1LA_0RE1LD_1RQ1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_0RF0LO_0RF1LP_0RF1LN_1LR1RQ_1RZ1LS_0LF1LT_0LF0LR` (J20, Jacobzheng)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). For this machine (R0 undefined = the halt, `1RZ` in the string) it proves:

- `BB20_JZ20.halt : halts tm c0`: the machine halts from the blank tape;
- `BB20_JZ20.score_exact`: the halting tape holds exactly 2j + 1 ones, for the j given by the explicit recursion
  of the file (below);
- `BB20_JZ20.sigma_lower_bound`: the halting tape holds N ones with
  `f_w2 (f_wk 2 (f_wk 2 (f 10 2))) < N`, that is f_(ω·2)(f_(ω+2)(f_(ω+2)(f_10(2)))) < N.

As published:

    Theorem halt : halts tm c0.
    Theorem score_exact : exists k a2 j c,
      iter 2 (ho 2) (ho 1 1) + 10 = 3 * k + 2 /\ a2 = iter 2 (ho k) (hoc 0 k 1) /\
      a2 + 2 * S k + 4 = 3 * j /\ c0 -->* c /\ halted tm c /\ ones c (2 * j + 1).
    Theorem sigma_lower_bound :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_w2 (f_wk 2 (f_wk 2 (f 10 2))) < N.

Since the machine is deterministic, the halted configuration reached from `c0` is unique, so these say that the
score is that N plus one: the machine halts in state R reading 0, and the halting transition `1RZ` writes a 1, so
σ = N + 1 = 2j + 2. The machine's own recursion, as defined in `BB20_JZ20.v`:

    h 0 x = x + 4,          h (m+1) x = (h m)^(x+2) (2)        (inner list: reducing a digit at position m+2)
    hc m 0 x = x,           hc m (n+1) x = hc (m+1) n (h m x)  (n digits 2 at positions m+2, m+3, ...)
    G a = hc 1 (a/3) (a mod 3 + 3) + 2(a/3) + 4                (an outer R0 round: expansion + inner run)
    ho 0 a = G a,           ho (m+1) a = (ho m)^(a+1) (3)      (outer list: reducing a digit at position m+2)
    hoc m 0 a = a,          hoc m (n+1) a = hoc (m+1) n (ho m a)

The fast-growing hierarchy is the standard one, defined in the same file: `f 0 n = n+1`, `f (k+1) n = (f k)^n n`,
`f_omega n = f n n`, `f_wk 0 = f_omega`, `f_wk (k+1) n = (f_wk k)^n n` (f_(ω+k)), and `f_w2 n = f_wk n n`
(f_(ω·2), with the fundamental sequence ω·2[n] = ω+n); `iter 0 g x = x`, `iter (n+1) g x = g (iter n g x)`.
`ones c N` says that `c`'s tape is a finite word padded with 0s on both sides holding N ones.

## Files

| file | content |
|---|---|
| `BB202.v`, `Individual202.v` | busycoq instantiated for 20 states (new here; the 19-state files with a 20th constructor). The 17th to 20th states (letters Q, R, S and T of the machine string) are the constructors `QQ`, `RR`, `SS` and `TT`, because `Q` is busycoq's state type, `R` its direction, `S` is `Datatypes.S` and `T` is a common type variable. The states `L` and `O` shadow busycoq's direction `L` and `Datatypes.O`, so tables write `TM.L` / `TM.R`. |
| `BB20_JZ20.v` | the proof: the table; walk lemmas; digit lists on the tape (`rl`); the sweep `SW l j y ds R`, shared by both lists (`SW_pass`, `SW_E`, `SW_exit_in`, `SW_exit_out`); the inner boundary `CI` (`CI_E0`, `CI_E1`, `CI_exit`); the expansion `EXP` (three residue cases); the refill (`RF_halt`, `RF_1`, `RF_2`); the outer boundary `CO` (`R0`, `R1`, `OEX`); level lemmas over arbitrary digit lists (`LV_in`, `Chain_in`, `LV_out`, `Chain_out`); the mod-3 invariant (`h_P1`, `G_P1`, `ho_P1`, `hoc_mod`, `K_gen`, `J_gen`); the run (`boot`, `run_gen`, `run`, `halt`); the score (`ones_Hc`, `score_exact`); and the bound (`transfer`, `h_dom`, `G_dom`, `ho_dom`, `hc_tower`, `ho11`, `bound_gen`, `sigma_lower_bound`). |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build (about 25 s) and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `probe.v` checks the compiled transition table against the machine string entry by entry
(40 checks generated from the string, not from the Coq file) and the blank start configuration. It prints the
definitions the statements use and runs `Print Assumptions` on the three theorems above: all three are closed under
the global context. CI job `bb13-bb14` runs the same script.

The proof was also checked with this project's `check.py` (extended to 20 states: the statement `halts tm c0` read
from the file, the table compared with the machine string, `Print Assumptions halt` closed): PASS, 2026-11-07.
