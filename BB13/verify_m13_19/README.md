# Coq proofs for `1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LM1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_0LM1LK_0LG1LL` (M13_19, Argon)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). In the Coq table the halt K0 is undefined (`---`); it is read on a 0 and the halting transition writes a
1, so σ = N + 1, where N is the number of ones at the halt. It proves:

- `BB13_M13_19.halt : halts tm c0`: the machine halts from the blank tape;
- `BB13_M13_19.sigma_bound`: N > f_(ω+2)^19(f_ω(3));
- `BB13_M13_19.sigma_bound_fw1`: N > f_(ω+2)^18(f_(ω+1)(f_(ω+1)(3)));
- `BB13_M13_19.beats_M13b`: N > f_(ω+2)^6(f_(ω+1)(f_(ω+1)(3))), M13b's proved LOWER bound (Argon's statement);
- `halt_tnf`, `sigma_bound_tnf`, `beats_M13b_tnf`: the same for `tm_tnf`, the machine with its states renamed in
  order of first visit (`1RB1RA_1RC1RK_1RD0LM_0LE1RI_0LH1LF_0LE1LG_---0LF_1RA0LJ_1RH0RA_1LH1LJ_0LL1LH_0RD1LL_1LJ1LC`),
  through the renaming lemma `tm_perm_tnf`;
- `BB13_M13_19_cmp.beats_M13b_exact`: N is above M13b's EXACT score: M13b's halting tape holds p + a + 5 ones for
  its pair (p, a) = `pa7` (`BB13_M13b_bound.score_exact`), and p + a + 5 < N;
- `BB13_M13_19_cmp.beats_M13b_score`: the two statements together (M13b's `score_exact` and the comparison), for
  one number NM.

As published:

    Theorem halt : halts tm c0.
    Theorem sigma_bound :
      exists c n, c0 -->* c /\ halted tm c /\ ones c n /\ n > iter 19 f_omega2 (f_omega 3).
    Theorem sigma_bound_fw1 :
      exists c n, c0 -->* c /\ halted tm c /\ ones c n /\ n > iter 18 f_omega2 (iter 2 f_omega1 3).
    Corollary beats_M13b :
      exists c n, c0 -->* c /\ halted tm c /\ ones c n /\ n > iter 6 f_omega2 (iter 2 f_omega1 3).
    Theorem beats_M13b_exact :
      exists c n, c0 -->* c /\ halted tm c /\ ones c n /\
      fst BB13_M13b.pa7 + snd BB13_M13b.pa7 + 5 < n.
    Theorem beats_M13b_score :
      exists NM,
        (exists c, c0 -[ BB13_M13b.tm ]->* c /\ halted BB13_M13b.tm c /\ BB13_M13b_bound.ones c NM) /\
        (exists c n, c0 -[ tm ]->* c /\ halted tm c /\ ones c n /\ NM < n).

Since the machines are deterministic, the halted configuration reached from `c0` is unique, so the theorems
describe one tape per machine. Both machines halt reading a 0 with a halting transition that writes a 1, so
σ = N + 1 for both, and `beats_M13b_score` gives σ(M13_19) > σ(M13b). The fast-growing hierarchy is the standard
one, defined in `BB13_M13_19.v`: `f 0 n = n+1`, `f (k+1) n = (f k)^n n`, `f_omega n = f n n`,
`f_omega1 n = f_omega^n n`, `f_omega2 n = f_omega1^n n`; `iter 0 g x = x`, `iter (n+1) g x = g (iter n g x)`.
`ones c N` says that `c`'s tape is a finite word padded with 0s on both sides holding N ones; `BB13_M13b_bound.ones`
has the same text.

## How the comparison with M13b's exact score is proved

`BB13_M13_19_cmp.v` loads M13b's proof files unchanged and proves an upper bound on M13b's score from the
definitions of M13b's maps, with M13_19's hierarchy, in the size p + a of a pair:

- W_j(b) + 3 ≤ f_(j+1)(b + 3), so W_j(b) ≤ f_ω(j + b + 4) (`cmp_W`);
- one Kc step: size ≤ f_ω³(t) (`cmp_Kc`); Kc_full ≤ f_(ω+1)²(t) (`cmp_Kc_full`); Kd_step ≤ f_(ω+1)³(t)
  (`cmp_Kd_step`); m Kd_steps ≤ f_(ω+1)^(3m)(t) (`cmp_Kd_iter`); D_reload ≤ f_(ω+1)(t);
- each of M13b's two kinds of big round (a reload and about t/6 or t/3 Kd_steps, with or without a Kc_full) is at
  most f_(ω+2)(f_(ω+2)(t)) (`cmp_stageA`, `cmp_stageB`);
- M13b's opening pair `pa1` and its reload point (8, W_8(8)) are below B0 = f_(ω+2)(f_ω(3)) (`cmp_B0`), so after
  the six big rounds p + a ≤ f_(ω+2)^12(B0) for `pa7` (`cmp_pa7`), and p + a + 5 < f_(ω+2)^14(f_ω(3))
  (`cmp_score_M13b`), below M13_19's f_(ω+2)^19(f_ω(3)).

No closed term of the hierarchy, and no closed pair of M13b's run, is ever converted or computed: every bound is
proved for variables and instantiated, and the closed iterates are regrouped with rewriting lemmas
(`cmp_iter_1`, `cmp_iter_iter`, `cmp_sz`, `cmp_B0_eq`).

## Files

| file | content |
|---|---|
| `BB132.v`, `Individual132.v` | busycoq instantiated for 13 states (byte-identical to `../../verify_m13b/multifile/`). The state `L` shadows busycoq's direction `L`, so tables write `TM.L` / `TM.R`. |
| `BB13_M13b.v`, `BB13_M13b_bound.v` | M13b's proof (byte-identical to `../../verify_m13b/multifile/`), loaded by the comparison |
| `BB13_M13_19.v` | Argon's proof, unchanged except for line endings and a first line `(* machine: … *)`: the cascade rules with a right tail, the stack (`stack_tail`) and its push, pop and drain rules, the 388-step opening, `RoundState` and the 19 rounds, the bounds, and the renamed table `tm_tnf` |
| `BB13_M13_19_cmp.v` | written here: `beats_M13b_exact`, `beats_M13b_score` |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject`, `share_check.sh` | build script, project file, check that the four shared files are byte-identical to `../../verify_m13b/multifile/` |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `compile_clean.sh` first runs `share_check.sh` when the other directory is present. `probe.v`
checks both compiled transition tables, `tm` and `tm_tnf`, against the two machine strings entry by entry (52 checks
generated from the strings, not from the Coq file) and the blank start configuration. It prints the definitions the
statements use and runs `Print Assumptions` on the nine theorems above: all nine are closed under the global
context (`compile_clean.log`: about 2 minutes). CI job `bb13-bb14` runs the same script.

The main proof also passes this project's `check.py` (the statement `halts tm c0` read from the file, the table
compared with the machine string, `Print Assumptions halt` closed): PASS, 2026-11-12.
