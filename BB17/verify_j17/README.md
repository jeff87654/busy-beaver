# Coq proofs for `1LG1RH_0LI1RC_0LD1LQ_0RE1LD_0RP1RL_1RB1RF_1LQ1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LQ0RN_0LQ1RO_1RZ1RM_0LQ0RA_1LH0LG` (J17_champ, Argon)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). The halt is O0 (`1RZ` in the string), read on a 0 and writing 1, so σ = N + 1, where N is the number of
ones in the halted configuration. The 17th state (letter Q) is the constructor `QQ`. It proves:

- `BB17_J17_w2_champ.halt : halts tm c0`: the machine halts from the blank tape;
- `BB17_J17_w2_champ.score_exact`: the halting tape holds exactly 2j + 4 ones, for the q₁, k₁, a₂, j of the statement;
- `BB17_J17_w2_champ.sigma_lower_bound`: N > f_(ω·2)(f_15(2)) and N > f_(ω·2)(f_ω^3(f_14(2)));
- `BB17_J17_w2_champ.halt_tnf`, `sigma_lower_bound_tnf`: the same for `tm_tnf`, the machine in tree normal form
  `1LB1RD_1LC1LB_1LD0LB_1RE0RM_1RF1RE_0LG1RP_1LH1LG_0LI1LG_1RJ1RK_0RJ0RE_0RL1RJ_0LC0RA_1RZ1RN_0LC0RO_0LC1RM_0LQ1LC_0RK1LQ`
  (the file proves that the renaming `perm_tnf` maps every transition of `tm` to one of `tm_tnf`).
- `BB17_J17_cmp.beats_J16_exact`, `beats_J16_score`: N + 1 > σ(J16_w2) + 1, against J16_w2's exact score (its
  `score_exact`, count 2j + 4, loaded from byte-identical copies of `../../BB16/verify_j16/multifile/`).

As published:

    Theorem halt : halts tm c0.
    Theorem score_exact : exists q1 k1 a2 j c,
      iter 5 G 4 + 6 = 9 * S q1 + 1 /\
      k1 = 3 * q1 + 1 /\
      a2 = hoc 1 (S k1) 4 /\
      a2 + 2 * (3 * S q1) + 2 = 3 * S (S j) /\
      c0 -->* c /\ halted tm c /\ ones c (2 * j + 4).
    Theorem sigma_lower_bound :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
        f_w2 (f 15 2) < N /\ f_w2 (iter 3 f_omega (f 14 2)) < N.
    Theorem sigma_lower_bound_tnf :
      exists c N, c0 -[ tm_tnf ]->* c /\ halted tm_tnf c /\ ones c N /\
        f_w2 (f 15 2) < N /\ f_w2 (iter 3 f_omega (f 14 2)) < N.
    Theorem halt_tnf : halts tm_tnf c0.
    Theorem beats_J16_exact : exists c N, c0 -[ K.tm ]->* c /\ halted K.tm c /\ K.ones c N /\
      forall k1 q1 a2 j, J.G 44 + 4 = 3 * (k1 + 3) -> k1 = 3 * q1 + 2 -> a2 = J.hoc 1 k1 (J.G 44) ->
        a2 + 2 * S k1 + 2 = 3 * S j + 1 -> 2 * j + 4 + 1 < N.
    Theorem beats_J16_score : exists NJ, (J16_w2 halts from the blank tape with NJ ones) /\
      exists c N, c0 -[ K.tm ]->* c /\ halted K.tm c /\ K.ones c N /\ NJ + 1 < N.
  (K = BB17_J17_w2_champ, J = BB16_J16_w2)

Since the machine is deterministic, the halted configuration reached from `c0` is unique, so the theorems describe
one tape. The fast-growing hierarchy is the standard one, defined in `BB17_J17_w2_champ.v`: `f 0 n = n+1`,
`f (k+1) n = (f k)^n n`, `f_omega n = f n n`, `f_wk 0 = f_omega`, `f_wk (k+1) n = (f_wk k)^n n` (f_(ω+k)), and
`f_w2 n = f_wk n n` (f_(ω·2), with the fundamental sequence ω·2[n] = ω+n); `iter 0 g x = x`,
`iter (n+1) g x = g (iter n g x)`. `ones c N` says that `c`'s tape is a finite word padded with 0s on both sides
holding N ones. These are the definitions of `BB16_J16_w2.v` ([`../../BB16/verify_j16/`](../../BB16/verify_j16/)),
with the same text, so f_(ω·2)(f_15(2)) < N is J16_w2's proved bound exactly.

## Files

| file | content |
|---|---|
| `BB172.v`, `Individual172.v` | busycoq instantiated for 17 states (byte-identical to `../../verify/multifile/`). The 17th state is `QQ`; the states `L` and `O` shadow busycoq's direction `L` and `Datatypes.O`, so tables write `TM.L` / `TM.R`. |
| `BB17_J17_w2_champ.v` | Argon's proof. Unchanged except for line 1 `(* machine: ... *)`, added here (the string above, the file's table `tm`) for `check.py`. Content: walk and zig-zag lemmas, digit lists, the sweep `SW`, `CI`, `CO`, `EX`, the refill (`RF_1`, `RF_halt`), `OEX`, `R1`, the expansion (`R0_CI`, `R0_k`, `R0`), the level lemmas, the mod-3 invariant (`Gk_mod3`, `ho_mod3`, `hoc_mod3`), the mod-486 tables of the inner levels (`h5_rep486`, `hc_period3_486`) and `G5_4_mod9`, the run (`boot1`, `boot`, `run_gen`, `run`, `halt`), the score and the bound (`G40_bound`, `G5_4_bound`, `bound_gen`), the renamed table and its theorems |
| `BB162.v`, `Individual162.v`, `BB16_J16_w2.v` | byte-identical copies of `../../../BB16/verify_j16/multifile/`'s (16-state setup and J16_w2's proof, loaded by the comparison) |
| `JZ_UB.v` | generic upper bounds for the engine's level maps (written here; home `../../../BB18/verify_r18c/multifile/`) |
| `BB17_J17_cmp.v` | written here: J16_w2's maps satisfy JZ_UB's hypotheses, its exact count is bounded above, `beats_J16_exact`, `beats_J16_score` |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject`, `share_check.sh` | build script, project file, check that the shared files (busycoq setup, the loaded proofs, `JZ_UB.v`) are byte-identical to their originals; the busycoq setup files come from `../../verify/multifile/` |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `compile_clean.sh` first runs `share_check.sh` when the other directory is present. `probe.v`
checks both compiled transition tables against the two machine strings entry by entry (68 checks generated from the
strings, not from the Coq file) and the blank start configuration. It prints the definitions the statements use and
runs `Print Assumptions` on the seven theorems above: all seven are closed under the global context. CI job
`bb13-bb14` runs the same script.

The main proof was also checked with this project's `check.py` (the statement `halts tm c0` read from the file, the
table compared with the machine string, `Print Assumptions halt` closed): PASS, 2026-11-13.
