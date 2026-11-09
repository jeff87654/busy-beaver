# Coq proofs for `1RB1RA_1RI1RC_0LD1LG_0RE1LD_0RN1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LL0LL_0LH1LK_0LK0LH_1LM---` (M14_31, Argon)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). The halt is N1 (undefined, `---`), read on a 1, so σ = N, the number of ones at the halt. It proves:

- `BB14_M14_31.halt : halts tm c0`: the machine halts from the blank tape;
- `BB14_M14_31.score_exact`: the halting tape holds exactly `fst pa32 + snd pa32 + 4` ones, for the explicit pair
  `pa32` computed by the 32-round run (`BB14_M14_31.v`, section "The 32-round trajectory of M14_31");
- `BB14_M14_31.sigma_bound`: N > f_(ω+2)^31(f_ω(f_ω(3)));
- `BB14_M14_31.sigma_bound_fw1`: N > f_(ω+2)^30(f_(ω+1)(f_(ω+1)(3)));
- `BB14_M14_31_cmp.beats_M14d_18`, `beats_M14d_18_fw1`: N is above both proved bounds of M14d_18, the previous
  BB(14) entry (`../../verify_m14d/`): f_(ω+2)^18(f_ω(f_ω(3))) and f_(ω+2)^17(f_(ω+1)(f_(ω+1)(3))).

As published:

    Theorem halt : halts tm c0.
    Theorem score_exact :
      exists c, c0 -->* c /\ halted tm c /\ ones c (fst pa32 + snd pa32 + 4).
    Theorem sigma_bound :
      exists c n, c0 -->* c /\ halted tm c /\ ones c n /\
      n > iter 31 f_omega2 (iter 2 f_omega 3).
    Theorem sigma_bound_fw1 :
      exists c n, c0 -->* c /\ halted tm c /\ ones c n /\
      n > iter 30 f_omega2 (iter 2 f_omega1 3).
    Theorem beats_M14d_18 :
      exists c n, c0 -->* c /\ halted tm c /\ ones c n /\ n > iter 18 f_omega2 (iter 2 f_omega 3).
    Theorem beats_M14d_18_fw1 :
      exists c n, c0 -->* c /\ halted tm c /\ ones c n /\ n > iter 17 f_omega2 (iter 2 f_omega1 3).

Since the machine is deterministic, the halted configuration reached from `c0` is unique, so the theorems describe
one tape. The fast-growing hierarchy is the standard one, defined in `BB14_M14_31.v`: `f 0 n = n+1`, `f (k+1) n = (f k)^n n`,
`f_omega n = f n n`, `f_omega1 n = f_omega^n n`, `f_omega2 n = f_omega1^n n`; `iter 0 g x = x`, `iter (n+1) g x = g (iter n g x)`. `ones c N` says that `c`'s tape is a finite
word padded with 0s on both sides holding N ones. `BB14_M14d_18.v` defines `iter`, `f`, `f_omega`, `f_omega1` and `f_omega2` with the same text, so the comparisons state M14d_18's bounds exactly as that file does.

## Files

| file | content |
|---|---|
| `BB142.v`, `Individual142.v` | busycoq instantiated for 14 states (byte-identical to `../../verify_m14d/multifile/`). The state `L` shadows busycoq's direction `L`, so tables write `TM.L` / `TM.R`. |
| `BB14_M14_31.v` | Argon's proof, unchanged except for line endings: the shift and cascade rules, the sentinel cases of the outer walk (E0, K, L, M, N), the 118-step opening, the maps `W`, `Kc`, `Kc_full`, `Kd_step` and the round maps (`D2_round`, `K0_z0_round`, …), the residue bookkeeping, the 32-round run, the score and both bounds |
| `BB14_M14_31_cmp.v` | written here: `beats_M14d_18`, `beats_M14d_18_fw1` (from the bounds above and `iter_mono_n`) |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject`, `share_check.sh` | build script, project file, check that the busycoq setup files are byte-identical to `../../verify_m14d/multifile/` |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `compile_clean.sh` first runs `share_check.sh` when the other directory is present. `probe.v` checks the compiled transition table against the machine string entry by entry
(28 checks generated from the string, not from the Coq file) and the blank start configuration. It prints the
definitions the statements use and runs `Print Assumptions` on the six theorems above: all six are closed under
the global context. CI job `bb13-bb14` runs the same script.

The main proof was also checked with this project's `check.py` (the statement `halts tm c0` read from the file, the
table compared with the machine string, `Print Assumptions halt` closed): PASS, 2026-11-08.
