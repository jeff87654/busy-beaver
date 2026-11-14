# Coq proofs for `1LB0LM_1RC1RN_1RD1RC_0LE1RQ_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RJ1RH_0RS0RK_1LN1RL_1LM1RJ_1LA1LM_0LA0RO_0LC1RP_0LA1RN_0LR1LA_0RI1LR_1RZ1LL` (J19_sq, Argon)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). The halt is S0 (`1RZ` in the string), read on a 0 and writing 1, so σ = N + 1, where N is the number of
ones in the halted configuration. The 17th to 19th states (letters Q, R, S) are the constructors `QQ`, `RR`, `SS`.
It proves:

- `BB19_J19_w2_sq.halt : halts tm c0`: the machine halts from the blank tape;
- `BB19_J19_w2_sq.score_exact`: the halting tape holds exactly 2(j + 1) + 1 ones, for the k₁, a₂, k₂, a₃, j of the
  statement;
- `BB19_J19_w2_sq.sigma_lower_bound`: N > f_(ω·2)(f_(ω·2)(f_5(2))), N > f_(ω·2)(f_(ω+2)(f_(ω+2)(f_10(2)))) and
  N > f_(ω·2)(2·f_ω^9(35)).
- `BB19_J19sq_cmp.beats_R18c_exact`, `beats_R18c_score`: N > σ(R18c), so σ(J19_sq) = N + 1 > σ(R18c) + 1, against
  R18c's exact score; `beats_J20_exact`, `beats_J20_score`: N > N(J20), so σ(J19_sq) > σ(J20), against J20's exact score.

As published:

    Theorem halt : halts tm c0.
    Theorem score_exact : exists k1 a2 k2 a3 j c,
      iter 2 (ho 0) 10 + 4 = 3 * S (S k1) + 1 /\
      a2 = hoc 0 (S k1) 10 /\ a2 + 2 * S k1 + 2 = 3 * S (S k2) /\
      a3 = iter 4 (ho k2) (hoc 0 k2 10) /\ a3 + 2 * S k2 + 2 = 3 * S j /\
      c0 -->* c /\ halted tm c /\ ones c (2 * S j + 1).
    Theorem sigma_lower_bound :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
        iter 2 f_w2 (f 5 2) < N /\
        f_w2 (f_wk 2 (f_wk 2 (f 10 2))) < N /\
        f_w2 (2 * iter 9 f_omega 35) < N.
    Theorem beats_R18c_exact : exists c N, c0 -[ Q.tm ]->* c /\ halted Q.tm c /\ Q.ones c N /\
      forall a1 k1 b0 a2 j, a1 = R.hoc 0 2 7 -> a1 + 6 = 3 * S (S k1) -> b0 = R.iter 2 (R.ho 0) 7 ->
        a2 = R.hoc 1 (S k1) b0 -> a2 + 2 * (1 + S k1) + 2 = 3 * S j + 1 -> 2 * S j + 1 < N.
    Theorem beats_J20_exact : exists c N, c0 -[ Q.tm ]->* c /\ halted Q.tm c /\ Q.ones c N /\
      forall k a2 j, Z.iter 2 (Z.ho 2) (Z.ho 1 1) + 10 = 3 * k + 2 -> a2 = Z.iter 2 (Z.ho k) (Z.hoc 0 k 1) ->
        a2 + 2 * S k + 4 = 3 * j -> 2 * j + 1 < N.
    (beats_R18c_score / beats_J20_score: exists NX, (X halts from the blank tape with NX ones) /\
       exists c N, ... Q.ones c N /\ NX < N)
  (Q = BB19_J19_w2_sq, R = BB18_R18c, Z = BB20_JZ20)

Since the machine is deterministic, the halted configuration reached from `c0` is unique, so the theorems describe
one tape. The fast-growing hierarchy is the standard one, defined in `BB19_J19_w2_sq.v`: `f 0 n = n+1`,
`f (k+1) n = (f k)^n n`, `f_omega n = f n n`, `f_wk 0 = f_omega`, `f_wk (k+1) n = (f_wk k)^n n` (f_(ω+k)), and
`f_w2 n = f_wk n n` (f_(ω·2), with the fundamental sequence ω·2[n] = ω+n); `iter 0 g x = x`,
`iter (n+1) g x = g (iter n g x)`. `ones c N` says that `c`'s tape is a finite word padded with 0s on both sides
holding N ones. These are the definitions of `BB20_JZ20.v` ([`../../BB20/verify/`](../../BB20/verify/)) and
`BB18_J18_w2_C_tnf.v` ([`../../BB18/verify_j18c/`](../../BB18/verify_j18c/)), with the same text, so the second and
third bounds are J20's and J18_w2_C's proved bounds exactly.

## Files

| file | content |
|---|---|
| `BB192.v`, `Individual192.v` | busycoq instantiated for 19 states (byte-identical to `../../verify_jz19/multifile/`). The 17th to 19th states are `QQ`, `RR`, `SS`; the states `L` and `O` shadow busycoq's direction `L` and `Datatypes.O`, so tables write `TM.L` / `TM.R`. |
| `BB19_J19_w2_sq.v` | Argon's proof. Unchanged except for line 1 `(* machine: ... *)`, added here (the string above, the file's table) for `check.py`. Content: walk and zig-zag lemmas, the period-3 rewriters (`triMNO`, `triRPQ`), digit lists, the sweep `SW`, `CI`, `CO`, `EX` (with a right part `R`), the expansion (`EXP_0`, `EXP_1`, `EXP_2`, `R0`), the refill (`RF_1`, `RF_2`, `RF_3`, `RF_halt`), `OEX`, `R1`, the level lemmas, the mod-3 invariant, the run (`boot`, `run_gen`, `run`, `halt`), the score and the bound (`a1_bound`, `bound_3refill`) |
| `BB182.v`, `Individual182.v`, `BB18_R18c.v` | byte-identical copies of `../../../BB18/verify_r18c/multifile/`'s (18-state setup and R18c's proof) |
| `BB202.v`, `Individual202.v`, `BB20_JZ20.v` | byte-identical copies of `../../../BB20/verify/multifile/`'s (20-state setup and J20's proof) |
| `JZ_UB.v` | generic upper bounds for the engine's level maps (written here; home `../../../BB18/verify_r18c/multifile/`) |
| `BB19_J19sq_cmp.v` | written here: R18c's and J20's maps satisfy JZ_UB's hypotheses, their exact counts are bounded above, the four theorems |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject`, `share_check.sh` | build script, project file, check that the shared files (busycoq setup, the loaded proofs, `JZ_UB.v`) are byte-identical to their originals; the busycoq setup files come from `../../verify_jz19/multifile/` |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `compile_clean.sh` first runs `share_check.sh` when the other directory is present. `probe.v`
checks the compiled transition table against the machine string entry by entry (38 checks generated from the string,
not from the Coq file) and the blank start configuration. It prints the definitions the statements use and runs
`Print Assumptions` on the seven theorems above: all seven are closed under the global context. CI job `bb13-bb14`
runs the same script.

The main proof was also checked with this project's `check.py` (the statement `halts tm c0` read from the file, the
table compared with the machine string, `Print Assumptions halt` closed): PASS, 2026-11-13.
