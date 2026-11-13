# Coq proofs for `1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_1LN1LK_1RK0LH_1LD0RK` (M14_fw3, Argon)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). In the Coq table the halt K0 is undefined (`---`); it is read on a 0 and the halting transition writes a
1, so σ = N + 1, where N is the number of ones at the halt. It proves:

- `BB14_M14_fw3.halt : halts tm c0`: the machine halts from the blank tape;
- `BB14_M14_fw3.score_exact`: the halting tape holds exactly `fst pa_final + snd pa_final + 6` ones, for the explicit
  pair `pa_final` = Phase1_pa (Outer_step^E₀ (pa_init)) (`BB14_M14_fw3.v`);
- `BB14_M14_fw3.sigma_bound`: N > f_(ω+3)(f_ω(3));
- `BB14_M14_fw3.beats_M14_31`: N > f_(ω+2)^31(f_ω(f_ω(3))), M14_31's proved LOWER bound (Argon's statement);
- `halt_tnf`, `sigma_bound_tnf`, `beats_M14_31_tnf`: the same for `tm_tnf`, the machine with its states renamed in
  order of first visit (`1RB1RA_1RC1RJ_1RD0LK_0LE1RI_---0LF_1LG1LE_1LH0RE_0RD1LH_1RL0RA_0LH1LN_1LM1LC_1RE0LM_1LN1LM_1RA0LM`),
  through the renaming lemma `tm_perm_tnf`;
- `BB14_M14_fw3_cmp.beats_M14_31_exact`: N is above M14_31's EXACT score: M14_31's halting tape holds p + a + 4 ones
  for its pair (p, a) = `pa32` (`BB14_M14_31.score_exact`), and p + a + 4 < N;
- `BB14_M14_fw3_cmp.beats_M14_31_score`: the two statements together, for one number N31.

As published:

    Theorem halt : halts tm c0.
    Theorem score_exact :
      exists c, c0 -->* c /\ halted tm c /\ ones c (fst pa_final + snd pa_final + 6).
    Theorem sigma_bound :
      exists c n, c0 -->* c /\ halted tm c /\ ones c n /\ n > f_omega3 (f_omega 3).
    Corollary beats_M14_31 :
      exists c n, c0 -->* c /\ halted tm c /\ ones c n /\ n > iter 31 f_omega2 (iter 2 f_omega 3).
    Theorem beats_M14_31_exact :
      exists c n, c0 -->* c /\ halted tm c /\ ones c n /\
      fst BB14_M14_31.pa32 + snd BB14_M14_31.pa32 + 4 < n.
    Theorem beats_M14_31_score :
      exists N31,
        (exists c, c0 -[ BB14_M14_31.tm ]->* c /\ halted BB14_M14_31.tm c /\ BB14_M14_31.ones c N31) /\
        (exists c n, c0 -[ tm ]->* c /\ halted tm c /\ ones c n /\ N31 < n).

Since the machines are deterministic, the halted configuration reached from `c0` is unique, so the theorems
describe one tape per machine. M14_31 halts reading a 1 (σ = N31), M14_fw3 reading a 0 (σ = N + 1), so
`beats_M14_31_score` gives σ(M14_fw3) > σ(M14_31). The fast-growing hierarchy is the standard one, defined in
`BB14_M14_fw3.v`: `f 0 n = n+1`, `f (k+1) n = (f k)^n n`, `f_omega n = f n n`, `f_omega1 n = f_omega^n n`,
`f_omega2 n = f_omega1^n n`, `f_omega3 n = f_omega2^n n`; `iter 0 g x = x`, `iter (n+1) g x = g (iter n g x)`.
`ones c N` says that `c`'s tape is a finite word padded with 0s on both sides holding N ones; `BB14_M14_31.ones` has
the same text.

## How the comparison with M14_31's exact score is proved

`BB14_M14_fw3_cmp.v` loads M14_31's proof file unchanged and proves an upper bound on M14_31's score from the
definitions of M14_31's maps, with M14_fw3's hierarchy, in the size p + a of a pair: W_j(b) ≤ f_ω(j + b + 4)
(`cmp_W`); Kc ≤ f_ω³, Kc_full ≤ f_(ω+1)², Kd_step ≤ f_(ω+1)³, D_reload ≤ f_(ω+1) (`cmp_Kc` … `cmp_D_reload`); each of
the eight round maps `D2_round`, `D1_round`, `K0_z0_round`, `K1_z0_round`, `K2_z0_round`, `K0_z1_round`,
`K1_z1_round`, `K2_z1_round` at most two applications of f_(ω+2) (`ok_D2` … `ok_K2_z1`). From B0 = f_(ω+2)(f_ω(3)),
above `pa1` and the reload point (8, W_8(8)), the 31 rounds give p + a ≤ f_(ω+2)^62(B0) for `pa32` (`cmp_pa32`), and
p + a + 4 < f_(ω+2)^64(f_ω(3)) ≤ f_(ω+3)(f_ω(3)) since f_ω(3) ≥ 192 (`cmp_Fw3`, `cmp_score_M14_31`).

No closed term of the hierarchy, and no closed pair of M14_31's run, is ever converted or computed: every bound is
proved for variables and instantiated, and the closed iterates are regrouped with rewriting lemmas.

## Files

| file | content |
|---|---|
| `BB142.v`, `Individual142.v` | busycoq instantiated for 14 states (byte-identical to `../../verify_m14_31/multifile/`). The state `L` shadows busycoq's direction `L`, so tables write `TM.L` / `TM.R`. |
| `BB14_M14_31.v` | M14_31's proof (byte-identical to `../../verify_m14_31/multifile/`), loaded by the comparison |
| `BB14_M14_fw3.v` | Argon's proof, unchanged except for a first line `(* machine: … *)`: the cascade rules with a right tail, the two-phase outer step that decrements the counter E, the 139-step opening and 72-step bridge, the outer loop, the halt at E = 0, the score and the bounds, and the renamed table `tm_tnf` |
| `BB14_M14_fw3_cmp.v` | written here: `beats_M14_31_exact`, `beats_M14_31_score` |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject`, `share_check.sh` | build script, project file, check that the three shared files are byte-identical to `../../verify_m14_31/multifile/` |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `compile_clean.sh` first runs `share_check.sh` when the other directory is present. `probe.v`
checks both compiled transition tables, `tm` and `tm_tnf`, against the two machine strings entry by entry (56 checks
generated from the strings, not from the Coq file) and the blank start configuration. It prints the definitions the
statements use and runs `Print Assumptions` on the nine theorems above: all nine are closed under the global
context (`compile_clean.log`: about 2 minutes). CI job `bb13-bb14` runs the same script.

The main proof also passes this project's `check.py` (the statement `halts tm c0` read from the file, the table
compared with the machine string, `Print Assumptions halt` closed): PASS, 2026-11-12.
