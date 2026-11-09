# Coq proofs for `1LG1LA_0LI1RC_0LD1LG_0RE1LD_0RM1RL_1RB1RF_1LH0LA_1RF0RN_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LG0RN_0RP1RO_1RZ1RM_1LB1LI` (J16_w2, Argon)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). The halt is O0 (`1RZ` in the string), read on a 0 and writing 1, so σ = N + 1, where N is the number of ones in the halted configuration. It proves:

- `BB16_J16_w2.halt : halts tm c0`: the machine halts from the blank tape;
- `BB16_J16_w2.score_exact`: the halting tape holds exactly 2j + 4 ones, for the k₁, q₁, a₂, j of the statement;
- `BB16_J16_w2.sigma_lower_bound`: N > f_(ω·2)(f_13(2)) and N > f_(ω·2)(f_15(2));
- `BB16_J16_w2_cmp.beats_J15`, `beats_M14_31`, `beats_M16_C`, `beats_M17_B`: N is above the proved bounds of
  J15_fw13 (BB(15), f_(ω+13)(20)), M14_31 (BB(14)), M16_C (the previous BB(16) entry,
  f_(ω+2)(f_(ω+1)^114(f_(ω+2)^3(f_(ω+3)(9))))) and M17_B (BB(17), f_(ω+2)^116(f_(ω+3)^3(9))).

As published:

    Theorem halt : halts tm c0.
    Theorem score_exact : exists k1 q1 a2 j c,
      G 44 + 4 = 3 * (k1 + 3) /\ k1 = 3 * q1 + 2 /\
      a2 = hoc 1 k1 (G 44) /\ a2 + 2 * S k1 + 2 = 3 * S j + 1 /\
      c0 -->* c /\ halted tm c /\ ones c (2 * j + 4).
    Theorem sigma_lower_bound :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_w2 (f 13 2) < N /\ f_w2 (f 15 2) < N.
    Theorem beats_J15 :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_wk 13 20 < N.
    Theorem beats_M14_31 :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ iter 30 f_omega2 (iter 2 f_omega1 3) < N.
    Theorem beats_M16_C :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
        f_omega2 (iter 114 f_omega1 (iter 3 f_omega2 (f_omega3 9))) < N.
    Theorem beats_M17_B :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ iter 116 f_omega2 (iter 3 f_omega3 9) < N.

Since the machine is deterministic, the halted configuration reached from `c0` is unique, so the theorems describe
one tape. The fast-growing hierarchy is the standard one, defined in `BB16_J16_w2.v`: `f 0 n = n+1`, `f (k+1) n = (f k)^n n`,
`f_omega n = f n n`, `f_wk 0 = f_omega`, `f_wk (k+1) n = (f_wk k)^n n` (f_(ω+k)), and `f_w2 n = f_wk n n` (f_(ω·2), with the fundamental sequence ω·2[n] = ω+n); `iter 0 g x = x`, `iter (n+1) g x = g (iter n g x)`. `ones c N` says that `c`'s tape is a finite
word padded with 0s on both sides holding N ones. The comparison file repeats the definitions `f_omega1 n = iter n f_omega n`, `f_omega2 n = iter n f_omega1 n`, `f_omega3 n = iter n f_omega2 n` of `BB14_M14_31.v`, `BB16_M16c_fw3.v` and `BB17_halt_fw3.v` over this file's `iter` and `f_omega` (the same text), so the comparisons state those machines' bounds exactly; they are `f_wk 1`, `f_wk 2`, `f_wk 3` by definition.

## Files

| file | content |
|---|---|
| `BB162.v`, `Individual162.v` | busycoq instantiated for 16 states (byte-identical to `../../verify_m16c/multifile/`). The states `L` and `O` shadow busycoq's direction `L` and `Datatypes.O`, so tables write `TM.L` / `TM.R`. |
| `BB16_J16_w2.v` | Argon's proof. Changed here: a byte-order mark and Windows line endings removed, and line 1 `(* machine: ... *)` added (the machine string, which is the file's transition table) for `check.py`. Content: walk and zig-zag lemmas, digit lists, the sweep, `CI`, `CO`, `EX`, the expansion (`R0_CI`, `R0_k`, `R0`), the refill (`OEX`, `RF_0`, `RF_halt`), `R1`, the level lemmas, the mod-3 invariant, the mod-18 periodicity of the inner level maps (`h_Cyc18`, `hc15_18`, `G44_mod9`), the run (`boot1`, `boot`, `run`, `halt`), the score and the bound (`G44_bound`, `bound_gen`) |
| `BB16_J16_w2_cmp.v` | written here: generic facts about the hierarchy (proved for abstract arguments, then made opaque) and the four comparisons |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject`, `share_check.sh` | build script, project file, check that the busycoq setup files are byte-identical to `../../verify_m16c/multifile/` |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `compile_clean.sh` first runs `share_check.sh` when the other directory is present. `probe.v` checks the compiled transition table against the machine string entry by entry
(32 checks generated from the string, not from the Coq file) and the blank start configuration. It prints the
definitions the statements use and runs `Print Assumptions` on the seven theorems above: all seven are closed under
the global context. CI job `bb13-bb14` runs the same script.

The main proof was also checked with this project's `check.py` (the statement `halts tm c0` read from the file, the
table compared with the machine string, `Print Assumptions halt` closed): PASS, 2026-11-08.
