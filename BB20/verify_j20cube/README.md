# Coq proofs for `1LB0LM_1RC1RN_1RD1RC_0LE1RQ_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RJ1RH_0RT0RK_1LS1RL_1LM1RJ_1LA1LM_0LA0RO_0LC1RP_0LA1RN_0LR1LA_0RI1LR_0LA0LA_1RZ1LK` (J20_cube, Argon)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). The halt is T0 (`1RZ` in the string), read on a 0 and writing 1, so σ = N + 1, where N is the number of
ones in the halted configuration. The 17th to 20th states (letters Q, R, S, T) are the constructors `QQ`, `RR`, `SS`,
`TT`. It proves:

- `BB20_J20_w2_cube.halt : halts tm c0`: the machine halts from the blank tape;
- `BB20_J20_w2_cube.score_exact`: the halting tape holds exactly 2(j + 1) + 1 ones, for the k₁, a₂, k₂, a₃, k₃, a₄, j
  of the statement;
- `BB20_J20_w2_cube.sigma_lower_bound`: N > f_(ω·2)^3(f_5(2)) and N > f_(ω·2)(f_(ω+2)(f_(ω+2)(f_10(2)))).
- `BB20_J20cube_cmp.beats_J19sq_exact`, `beats_J19sq_score`: N + 1 > σ(J19_sq) + 1, against J19_sq's exact score.

As published:

    Theorem halt : halts tm c0.
    Theorem score_exact : exists k1 a2 k2 a3 k3 a4 j c,
      iter 2 (ho 0) 10 + 4 = 3 * S (S k1) + 1 /\
      a2 = hoc 0 (S k1) 10 /\ a2 + 2 * S k1 + 2 = 3 * S (S k2) /\
      a3 = hoc 0 k2 10 /\ a3 + 2 * S k2 + 2 = 3 * S k3 + 2 /\
      a4 = iter 4 (ho k3) (hoc 0 k3 10) /\ a4 + 2 * S k3 + 2 = 3 * S j /\
      c0 -->* c /\ halted tm c /\ ones c (2 * S j + 1).
    Theorem sigma_lower_bound :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
        iter 3 f_w2 (f 5 2) < N /\
        f_w2 (f_wk 2 (f_wk 2 (f 10 2))) < N.
    Theorem beats_J19sq_exact : exists c N, c0 -[ C.tm ]->* c /\ halted C.tm c /\ C.ones c N /\
      forall k1 a2 k2 a3 j, Q.iter 2 (Q.ho 0) 10 + 4 = 3 * S (S k1) + 1 -> a2 = Q.hoc 0 (S k1) 10 ->
        a2 + 2 * S k1 + 2 = 3 * S (S k2) -> a3 = Q.iter 4 (Q.ho k2) (Q.hoc 0 k2 10) ->
        a3 + 2 * S k2 + 2 = 3 * S j -> 2 * S j + 1 + 1 < N.
    Theorem beats_J19sq_score : exists NQ, (J19_sq halts from the blank tape with NQ ones) /\
      exists c N, c0 -[ C.tm ]->* c /\ halted C.tm c /\ C.ones c N /\ NQ + 1 < N.
  (C = BB20_J20_w2_cube, Q = BB19_J19_w2_sq)

Since the machine is deterministic, the halted configuration reached from `c0` is unique, so the theorems describe
one tape. The fast-growing hierarchy is the standard one, defined in `BB20_J20_w2_cube.v`: `f 0 n = n+1`,
`f (k+1) n = (f k)^n n`, `f_omega n = f n n`, `f_wk 0 = f_omega`, `f_wk (k+1) n = (f_wk k)^n n` (f_(ω+k)), and
`f_w2 n = f_wk n n` (f_(ω·2), with the fundamental sequence ω·2[n] = ω+n); `iter 0 g x = x`,
`iter (n+1) g x = g (iter n g x)`. `ones c N` says that `c`'s tape is a finite word padded with 0s on both sides
holding N ones. These are the definitions of `BB20_JZ20.v` ([`../verify/`](../verify/)), with the same text, so the
second bound is J20's proved bound exactly.

## Files

| file | content |
|---|---|
| `BB202.v`, `Individual202.v` | busycoq instantiated for 20 states (byte-identical to `../../verify/multifile/`). The 17th to 20th states are `QQ`, `RR`, `SS`, `TT`; the states `L` and `O` shadow busycoq's direction `L` and `Datatypes.O`, so tables write `TM.L` / `TM.R`. |
| `BB20_J20_w2_cube.v` | Argon's proof. Unchanged except for line 1 `(* machine: ... *)`, added here (the string above, the file's table) for `check.py`. Content: as `../../BB19/verify_j19sq/`'s `BB19_J19_w2_sq.v` (same engine, expansion and level maps), with the refill `RF_1`, `RF_2`, `RF_3`, `RF_4`, `RF_halt`, the run (`boot`, `run_gen`, `run`, `halt`, with the residue lemmas `K1_gen`, `K2_gen`, `K3_gen`, `J_gen`), the score and the bound (`a1_bound`, `bound_4refill`) |
| `BB192.v`, `Individual192.v`, `BB19_J19_w2_sq.v` | byte-identical copies of `../../../BB19/verify_j19sq/multifile/`'s (19-state setup and J19_sq's proof) |
| `JZ_UB.v` | generic upper bounds for the engine's level maps (written here; home `../../../BB18/verify_r18c/multifile/`) |
| `BB20_J20cube_cmp.v` | written here: J19_sq's maps satisfy JZ_UB's hypotheses, its exact count is bounded above, the two theorems |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject`, `share_check.sh` | build script, project file, check that the shared files (busycoq setup, the loaded proofs, `JZ_UB.v`) are byte-identical to their originals; the busycoq setup files come from `../../verify/multifile/` |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `compile_clean.sh` first runs `share_check.sh` when the other directory is present. `probe.v`
checks the compiled transition table against the machine string entry by entry (40 checks generated from the string,
not from the Coq file) and the blank start configuration. It prints the definitions the statements use and runs
`Print Assumptions` on the five theorems above: all five are closed under the global context. CI job `bb13-bb14`
runs the same script.

The main proof was also checked with this project's `check.py` (the statement `halts tm c0` read from the file, the
table compared with the machine string, `Print Assumptions halt` closed): PASS, 2026-11-13.
