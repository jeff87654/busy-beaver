# Coq proofs for `1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LA0RN_0LA1RO_1RZ1RM` (J15_fw13, Argon)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). The halt is O0 (`1RZ` in the string), read on a 0 and writing 1, so σ = N + 1, where N is the number of ones in the halted configuration. It proves:

- `BB15_J15_fw13.halt : halts tm c0`: the machine halts from the blank tape;
- `BB15_J15_fw13.step_1012`: after the second refill (1012 steps), the outer list is CO 4 [2^14];
- `BB15_J15_fw13.score_exact`: the halting tape holds exactly 2j + 1 ones, where `hoc 0 14 4 + 29 = 3 * j`;
- `BB15_J15_fw13.sigma_lower_bound`: N > f_(ω+13)(20);
- `BB15_J15_fw13_cmp.beats_M14_31`: N is above M14_31's proved BB(14) bound f_(ω+2)^30(f_(ω+1)(f_(ω+1)(3)))
  (`../../../BB14/verify_m14_31/`).

As published:

    Theorem halt : halts tm c0.
    Theorem step_1012 : c0 -->* CO 4 (rl (repeat 2 14) (const S0)).
    Theorem score_exact : exists j c,
      hoc 0 14 4 + 29 = 3 * j /\ c0 -->* c /\ halted tm c /\ ones c (2 * j + 1).
    Theorem sigma_lower_bound :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_wk 13 20 < N.
    Theorem beats_M14_31 :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ iter 30 f_omega2 (iter 2 f_omega1 3) < N.

Since the machine is deterministic, the halted configuration reached from `c0` is unique, so the theorems describe
one tape. The fast-growing hierarchy is the standard one, defined in `BB15_J15_fw13.v`: `f 0 n = n+1`, `f (k+1) n = (f k)^n n`,
`f_omega n = f n n`, `f_wk 0 = f_omega`, `f_wk (k+1) n = (f_wk k)^n n` (f_(ω+k)); `iter 0 g x = x`, `iter (n+1) g x = g (iter n g x)`. `ones c N` says that `c`'s tape is a finite
word padded with 0s on both sides holding N ones. The comparison file repeats `BB14_M14_31.v`'s definitions `f_omega1 n = iter n f_omega n` and `f_omega2 n = iter n f_omega1 n` over this file's `iter` and `f_omega` (the same text), so `beats_M14_31` states M14_31's bound exactly; they are `f_wk 1` and `f_wk 2` by definition (`f_omega1_wk`, `f_omega2_wk`). The machine's own recursion (`h`, `hc`, `G`, `ho`, `hoc`) is printed by the probe and described in the write-up.

## Files

| file | content |
|---|---|
| `BB152.v`, `Individual152.v` | busycoq instantiated for 15 states (this project's setup files, as in `bb8_list/proofs`). The states `L` and `O` shadow busycoq's direction `L` and `Datatypes.O`, so tables write `TM.L` / `TM.R`. |
| `BB15_J15_fw13.v` | Argon's proof, unchanged except for line endings: walk and zig-zag lemmas, digit lists (`rl`), the sweep `SW`, the inner and outer boundaries `CI`, `CO`, the expansion (`EXP_c`, `R0_c`, `R0`), the refill (`OEX`, `RF_1`, `RF_halt`), `R1`, the level lemmas, the mod-3 invariant (`h_P1`, `hc_mod`, `G_mod3_1`, `ho_mod3_1`, `hoc_mod3_1`), the run (`boot`, `step_1012`, `run`, `halt`), the score and the bound (`hoc14_dom`) |
| `BB15_J15_fw13_cmp.v` | written here: generic facts about the hierarchy (proved for abstract arguments, then made opaque) and `beats_M14_31` |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject` | build script, project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `probe.v` checks the compiled transition table against the machine string entry by entry
(30 checks generated from the string, not from the Coq file) and the blank start configuration. It prints the
definitions the statements use and runs `Print Assumptions` on the five theorems above: all five are closed under
the global context. CI job `bb13-bb14` runs the same script.

The main proof was also checked with this project's `check.py` (the statement `halts tm c0` read from the file, the
table compared with the machine string, `Print Assumptions halt` closed): PASS, 2026-11-08.
