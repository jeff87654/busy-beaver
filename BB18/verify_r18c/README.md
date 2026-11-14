# Coq proofs for `1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_1LQ0LO_0LR1LP_1LQ1LN_1LF0LM_0RC1RZ` (R18c; Coq proof by Argon)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). The halt is R1 (`1RZ` in the string), read on a 1 and writing 1, so σ = N, where N is the number of ones
in the halted configuration. The 17th and 18th states (letters Q and R) are the constructors `QQ` and `RR`. It
proves:

- `BB18_R18c.halt : halts tm c0`: the machine halts from the blank tape;
- `BB18_R18c.score_exact`: the halting tape holds exactly 2(j + 1) + 1 ones, for the a₁, k₁, b₀, a₂, j of the statement;
- `BB18_R18c.sigma_lower_bound`: N > f_(ω·2)(2·f_ω^9(35)) and N > f_(ω·2)(f_(ω+1)(f_4(2)));
- `BB18_R18c.halt_tnf`, `sigma_lower_bound_tnf`: the same for `tm_tnf`, the machine in tree normal form
  `1LB0LP_1RC1RJ_1RD1RC_0LE1RO_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RB1RH_0LK1RJ_1LN0LL_0LR1LM_1LN1LK_1LC0LJ_0LQ1LA_1LA1LP_0RI1LQ_0RO1RZ`
  (the file proves that the renaming `perm_tnf` maps every transition of `tm` to one of `tm_tnf`).
- `BB18_R18c_cmp.beats_J18C_exact`, `beats_J18C_score`: N > σ(J18_w2_C), against J18_w2_C's exact score; and
  `beats_J17_exact`, `beats_J17_score`: N > σ(J17_champ) + 1, against J17_champ's exact score (both loaded from
  byte-identical copies of their published files).

As published:

    Theorem halt : halts tm c0.
    Theorem score_exact : exists a1 k1 b0 a2 j c,
      a1 = hoc 0 2 7 /\
      a1 + 6 = 3 * S (S k1) /\
      b0 = iter 2 (ho 0) 7 /\
      a2 = hoc 1 (S k1) b0 /\
      a2 + 2 * (1 + S k1) + 2 = 3 * S j + 1 /\
      c0 -->* c /\ halted tm c /\ ones c (2 * S j + 1).
    Theorem sigma_lower_bound :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
        f_w2 (2 * iter 9 f_omega 35) < N /\ f_w2 (f_wk 1 (f 4 2)) < N.
    Theorem sigma_lower_bound_tnf :
      exists c N, c0 -[ tm_tnf ]->* c /\ halted tm_tnf c /\ ones c N /\
        f_w2 (2 * iter 9 f_omega 35) < N /\ f_w2 (f_wk 1 (f 4 2)) < N.
    Theorem halt_tnf : halts tm_tnf c0.
    Theorem beats_J18C_exact : exists c N, c0 -[ R.tm ]->* c /\ halted R.tm c /\ R.ones c N /\
      forall k a2 j, J.hoc 0 2 10 + 6 = 3 * S (S k) -> a2 = J.iter 3 (J.ho k) (J.hoc 0 k 10) ->
        a2 + 2 * S k + 2 = 3 * j + 2 -> 2 * j + 2 + 1 < N.
    Theorem beats_J17_exact : exists c N, c0 -[ R.tm ]->* c /\ halted R.tm c /\ R.ones c N /\
      forall q1 k1 a2 j, K.iter 5 K.G 4 + 6 = 9 * S q1 + 1 -> k1 = 3 * q1 + 1 -> a2 = K.hoc 1 (S k1) 4 ->
        a2 + 2 * (3 * S q1) + 2 = 3 * S (S j) -> 2 * j + 4 + 2 < N.
    (beats_J18C_score / beats_J17_score: exists NX, (X halts from the blank tape with NX ones) /\
       exists c N, ... R.ones c N /\ NX + 1 < N   resp.   NX + 2 < N)
  (R = BB18_R18c, J = BB18_J18_w2_C_tnf, K = BB17_J17_w2_champ)

Since the machine is deterministic, the halted configuration reached from `c0` is unique, so the theorems describe
one tape. The fast-growing hierarchy is the standard one, defined in `BB18_R18c.v`: `f 0 n = n+1`,
`f (k+1) n = (f k)^n n`, `f_omega n = f n n`, `f_wk 0 = f_omega`, `f_wk (k+1) n = (f_wk k)^n n` (f_(ω+k)), and
`f_w2 n = f_wk n n` (f_(ω·2), with the fundamental sequence ω·2[n] = ω+n); `iter 0 g x = x`,
`iter (n+1) g x = g (iter n g x)`. `ones c N` says that `c`'s tape is a finite word padded with 0s on both sides
holding N ones. These are the definitions of `BB18_J18_w2_C_tnf.v` ([`../verify_j18c/`](../verify_j18c/)), with the
same text, so f_(ω·2)(2·f_ω^9(35)) < N is J18_w2_C's proved bound exactly.

## Files

| file | content |
|---|---|
| `BB182.v`, `Individual182.v` | busycoq instantiated for 18 states (byte-identical to `../../verify_r18a/multifile/`). The 17th and 18th states are `QQ` and `RR`; the states `L` and `O` shadow busycoq's direction `L` and `Datatypes.O`, so tables write `TM.L` / `TM.R`. |
| `BB18_R18c.v` | Argon's proof. Unchanged except for line 1 `(* machine: ... *)`, added here (the string above, the file's table `tm`) for `check.py`. Content: walk and zig-zag lemmas, the period-3 rewriter `triNOP`, digit lists, the sweep `SW`, `CI`, `CO`, `EX`, the refill (`RF_halt`, `RF_2`, `RF_0`), the expansion (`EXP_zero`, `EXP_0s`, `EXP_1`, `EXP_2`, `R0`), `OEX`, `R1`, the level lemmas, the mod-3 invariant (`G_P1`, `ho_P1`, `hoc_P1`), the run (`boot1`, `boot`, `run_gen`, `run`, `halt`), the score and the bound (`G7_bound`, `a1_bound`, `bound_gen`, `beat_J18_inner`), the renamed table and its theorems |
| `BB18_J18_w2_C_tnf.v` | byte-identical copy of `../../verify_j18c/multifile/`'s (J18_w2_C's proof) |
| `BB172.v`, `Individual172.v`, `BB17_J17_w2_champ.v` | byte-identical copies of `../../../BB17/verify_j17/multifile/`'s (17-state setup and J17_champ's proof) |
| `JZ_UB.v` | generic upper bounds for the engine's level maps (written here; this is its home, the other directories hold copies) |
| `BB18_R18c_cmp.v` | written here: J18_w2_C's and J17_champ's maps satisfy JZ_UB's hypotheses, their exact counts are bounded above, the four theorems |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject`, `share_check.sh` | build script, project file, check that the shared files (busycoq setup, the loaded proofs, `JZ_UB.v`) are byte-identical to their originals; the busycoq setup files come from `../../verify_r18a/multifile/` |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `compile_clean.sh` first runs `share_check.sh` when the other directory is present. `probe.v`
checks both compiled transition tables against the two machine strings entry by entry (72 checks generated from the
strings, not from the Coq file) and the blank start configuration. It prints the definitions the statements use and
runs `Print Assumptions` on the nine theorems above: all nine are closed under the global context. CI job
`bb13-bb14` runs the same script.

The main proof was also checked with this project's `check.py` (the statement `halts tm c0` read from the file, the
table compared with the machine string, `Print Assumptions halt` closed): PASS, 2026-11-13.
