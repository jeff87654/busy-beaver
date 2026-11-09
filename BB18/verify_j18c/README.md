# Coq proofs for `0LB1LF_0RC1LB_0RD1RM_1LE0RN_1LF1LE_1LG0LE_1RH1RP_1RI1RH_0LJ1RA_1LK1LJ_0LL1LJ_1RM1RC_0RM0RH_1LE1RO_1RZ1RD_0LF0RQ_0LH1RR_0LF1RP` (J18_w2_C, Argon)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). The halt is O0 (`1RZ` in the string), read on a 0 and writing 1, so σ = N + 1, where N is the number of ones in the halted configuration. The 17th and 18th states (letters Q and R) are the constructors `QQ` and `RR`. It proves:

- `BB18_J18_w2_C_tnf.halt : halts tm c0`: the machine halts from the blank tape;
- `BB18_J18_w2_C_tnf.score_exact`: the halting tape holds exactly 2j + 2 ones, for the k, a₂, j of the statement;
- `BB18_J18_w2_C_tnf.sigma_lower_bound`: N > f_(ω·2)(2·f_ω^9(35)) and N > f_(ω·2)(2·f_ω^8(f_3(17)));
- `BB18_J18_w2_C_tnf_cmp.beats_R18a`, `beats_J16`: N is above R18a's proved bound f_(ω·2)(f_ω(f_ω(f_10(2)))) (the
  previous BB(18) entry, `../../verify_r18a/`) and J16_w2's f_(ω·2)(f_15(2)) (BB(16)).

As published:

    Theorem halt : halts tm c0.
    Theorem score_exact : exists k a2 j c,
      hoc 0 2 10 + 6 = 3 * S (S k) /\ a2 = iter 3 (ho k) (hoc 0 k 10) /\
      a2 + 2 * S k + 2 = 3 * j + 2 /\ c0 -->* c /\ halted tm c /\ ones c (2 * j + 2).
    Theorem sigma_lower_bound :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
        f_w2 (2 * iter 9 f_omega 35) < N /\ f_w2 (2 * iter 8 f_omega (f 3 17)) < N.
    Theorem beats_R18a :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_w2 (f_omega (f_omega (f 10 2))) < N.
    Theorem beats_J16 :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_w2 (f 15 2) < N.

Since the machine is deterministic, the halted configuration reached from `c0` is unique, so the theorems describe
one tape. The fast-growing hierarchy is the standard one, defined in `BB18_J18_w2_C_tnf.v`: `f 0 n = n+1`, `f (k+1) n = (f k)^n n`,
`f_omega n = f n n`, `f_wk 0 = f_omega`, `f_wk (k+1) n = (f_wk k)^n n` (f_(ω+k)), and `f_w2 n = f_wk n n` (f_(ω·2), with the fundamental sequence ω·2[n] = ω+n); `iter 0 g x = x`, `iter (n+1) g x = g (iter n g x)`. `ones c N` says that `c`'s tape is a finite
word padded with 0s on both sides holding N ones. `BB18_R18a.v` and `BB16_J16_w2.v` define `iter`, `f`, `f_omega`, `f_wk` and `f_w2` with the same text, so the comparisons state their bounds exactly.

## Files

| file | content |
|---|---|
| `BB182.v`, `Individual182.v` | busycoq instantiated for 18 states (byte-identical to `../../verify_r18a/multifile/`). The 17th and 18th states are `QQ` and `RR`; the states `L` and `O` shadow busycoq's direction `L` and `Datatypes.O`, so tables write `TM.L` / `TM.R`. |
| `BB18_J18_w2_C_tnf.v` | Argon's proof, unchanged except for line endings: walk and zig-zag lemmas, digit lists, the sweep, `CI`, `CO`, `EX`, the three-residue expansion (`EXP_0`, `EXP_1`, `EXP_2`, `R0`), the refill (`OEX`, `RF_0`, `RF_1`, `RF_halt`), `R1`, the level lemmas, the mod-3 invariant (`G_P1`, `ho_P1`, `hoc_mod`, `K_gen`, `J_gen`), the run (`boot`, `run`, `halt`), the score and the bound (`GG_dom`, `G3_dom`, `a1_bound_35`, `bound_gen`) |
| `BB18_J18_w2_C_tnf_cmp.v` | written here: generic facts about the hierarchy (proved for abstract arguments, then made opaque), `beats_R18a` and `beats_J16` |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject`, `share_check.sh` | build script, project file, check that the busycoq setup files are byte-identical to `../../verify_r18a/multifile/` |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `compile_clean.sh` first runs `share_check.sh` when the other directory is present. `probe.v` checks the compiled transition table against the machine string entry by entry
(36 checks generated from the string, not from the Coq file) and the blank start configuration. It prints the
definitions the statements use and runs `Print Assumptions` on the five theorems above: all five are closed under
the global context. CI job `bb13-bb14` runs the same script.

The main proof was also checked with this project's `check.py` (the statement `halts tm c0` read from the file, the
table compared with the machine string, `Print Assumptions halt` closed): PASS, 2026-11-08.
