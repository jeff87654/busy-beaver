# Coq proofs for `1RB0LK_1RC1RB_1RD1RM_1RE0LH_1LF1RI_0LA1LG_1RL0LF_1LK1LD_1RJ0RB_1RG0LK_1LA1LK_1RZ0LF_0LN1LA_0RE1LN` (M14_fw3x4, Gemini 4 Neon)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). In the Coq tables the halt is undefined (`---`): L0 in the machine string's state order, K0 in the state
order of M12's core that Neon's proof works in. It is read on a 0 and the halting transition writes a 1, so
σ = N + 1, where N is the number of ones at the halt. It proves:

- `BB14_M14_fw3x4_entry.halt : halts tm c0`: the machine halts from the blank tape, for `tm` = the table of the
  machine string above (states in order of first visit, start A);
- `BB14_M14_fw3x4_entry.score_exact`: the halting tape holds exactly `N_final` = `fst pa_final + snd pa_final + 7`
  ones, for the explicit pair `pa_final` of the four-loop recursion (`BB14_M14_fw3x4.v`);
- `BB14_M14_fw3x4_entry.sigma_bound`: N > f_(ω+3)^4(f_ω(4));
- `BB14_M14_fw3x4_cmp.beats_M14_fw3_exact`: N is above M14_fw3's EXACT score, the previous entry's: M14_fw3's
  halting tape holds p + a + 6 ones for its pair (p, a) = `pa_final` (`BB14_M14_fw3.score_exact`), and p + a + 6 < N;
- `BB14_M14_fw3x4_cmp.beats_M14_fw3_score`: the two statements together, for one number N3;
- `BB14_M14_fw3x4_cmp.beats_M14_fw3_all`: every halting tape of M14_fw3 reached from the blank tape holds fewer ones
  than every halting tape of M14_fw3x4;
- `BB14_M14_fw3x4_cmp.M14_fw3_score_agrees`: M14_fw3's published exact score equals `M14_Old.N_old`, the exact score
  of M14_fw3 that Neon's file proves on its own (it re-proves M14_fw3 from scratch in a module `M14_Old`).

As published:

    Theorem halt : halts tm c0.
    Theorem score_exact :
      exists c, c0 -[ tm ]->* c /\ halted tm c /\ BB14_M14_fw3x4.ones c BB14_M14_fw3x4.N_final.
    Theorem sigma_bound :
      exists c n, c0 -[ tm ]->* c /\ halted tm c /\ BB14_M14_fw3x4.ones c n /\
      n > BB14_M14_fw3x4.iter 4 BB14_M14_fw3x4.f_omega3 (BB14_M14_fw3x4.f_omega 4).
    Theorem beats_M14_fw3_exact :
      exists c n, c0 -[ BB14_M14_fw3x4_entry.tm ]->* c /\ halted BB14_M14_fw3x4_entry.tm c /\
                  BB14_M14_fw3x4.ones c n /\
                  fst BB14_M14_fw3.pa_final + snd BB14_M14_fw3.pa_final + 6 < n.
    Theorem beats_M14_fw3_score :
      exists N3,
        (exists c, c0 -[ BB14_M14_fw3.tm ]->* c /\ halted BB14_M14_fw3.tm c /\ BB14_M14_fw3.ones c N3) /\
        (exists c n, c0 -[ BB14_M14_fw3x4_entry.tm ]->* c /\ halted BB14_M14_fw3x4_entry.tm c /\
                     BB14_M14_fw3x4.ones c n /\ N3 < n).
    Theorem beats_M14_fw3_all : forall c1 n1 c2 n2,
      c0 -[ BB14_M14_fw3.tm ]->* c1 -> halted BB14_M14_fw3.tm c1 -> BB14_M14_fw3.ones c1 n1 ->
      c0 -[ BB14_M14_fw3x4_entry.tm ]->* c2 -> halted BB14_M14_fw3x4_entry.tm c2 -> BB14_M14_fw3x4.ones c2 n2 ->
      n1 < n2.

Both machines halt reading a 0 (σ = N + 1 for both), so these give σ(M14_fw3x4) > σ(M14_fw3). Since the machines
are deterministic, the halted configuration reached from `c0` and its count of ones are unique (Neon's
`evstep_halted_unique`, `ones_unique`), which is what makes `beats_M14_fw3_all` a statement about M14_fw3's true
score. The fast-growing hierarchy is the standard one, defined in `BB14_M14_fw3x4.v` with the same text as in
`BB14_M14_fw3.v`: `f 0 n = n+1`, `f (k+1) n = (f k)^n n`, `f_omega n = f n n`, `f_omega1 n = f_omega^n n`,
`f_omega2 n = f_omega1^n n`, `f_omega3 n = f_omega2^n n`; `iter 0 g x = x`, `iter (n+1) g x = g (iter n g x)`.
`ones c N` says that `c`'s tape is a finite word padded with 0s on both sides holding N ones; `BB14_M14_fw3.ones` has
the same text.

## Why there is an entry file

Neon's proof works with the machine in the state order of M12's core, started in G (`tm`, `c0_core`, its theorem
`halt : halts tm c0_core`), and transfers everything to the same machine with the states renamed in order of first
visit and started in A (`tm_tnf`, BusyCoq's `c0`; `halt_tnf`, `score_exact_tnf`, `sigma_bound_tnf`, through the
renaming lemma `tm_perm_tnf`). Repository names start in A, so the machine string is the renamed table. Rather than
edit Neon's file (renaming its `tm` would touch the whole proof), it is kept byte-identical to the audited version
(SHA-256 `dcc4514c…d1f1`, in `sha256.txt`), and `BB14_M14_fw3x4_entry.v` restates its `_tnf` results for the table of
the machine string under the name `tm`, with `Theorem halt : halts tm c0`, the form this project's `check.py` reads.
The table there is written out again; Coq accepts the proofs (`exact BB14_M14_fw3x4.halt_tnf` and so on) only because
it is the same term as Neon's `tm_tnf`.

## How the comparison with M14_fw3's exact score is proved

Neon's file already contains a complete, self-contained proof about M14_fw3: module `M14_Old` runs M14_fw3 from the
blank tape (with its own copy of the table, pinned to the published string by `tm_M14_fw3_str_pin`), proves its exact
count `N_old`, an upper bound `N_old ≤ f_(ω+3)(f_ω(13))`, and `N_old_lt_N_final`. `BB14_M14_fw3x4_cmp.v` connects
this to the published proof, loaded unchanged (`BB14_M14_fw3.v`, a byte-identical copy of
[`../verify_m14_fw3/multifile/BB14_M14_fw3.v`](../verify_m14_fw3/multifile/BB14_M14_fw3.v)): the two tables agree
entry by entry, so a halting run of one is a halting run of the other, and by uniqueness the published exact score
p + a + 6 is `N_old` (`M14_fw3_score_agrees`). The upper bound itself is f_(ω+3)(f_ω(13)) ≤ f_(ω+3)^2(f_ω(4)), since
f_ω(4) ≥ 13, far below f_(ω+3)^4(f_ω(4)) < N.

## The audit file

`BB14_M14_fw3x4_audit.v` comes from the independent audit of Neon's proof (2026-11-23). It does not use the entry
or comparison files: it transcribes both machine strings by hand (M14_fw3x4's and M14_fw3's published name), defines
its own count of ones (`my_ones`, with `filter`/`length`) and its own hierarchy with Coq's `Nat.iter` (`fgh`, `fw`,
`fwk`), and proves, from Neon's theorems:

    Theorem my_new_halts : halts my_new c0.
    Theorem my_new_sigma :
      (exists c n, c0 -[ my_new ]->* c /\ halted my_new c /\ my_ones c n) /\
      (forall c n, c0 -[ my_new ]->* c -> halted my_new c -> my_ones c n ->
         Nat.iter 4 (fwk 3) (fw 4) < n).
    Theorem my_beats :
      halts my_old c0 /\
      (forall c1 n1 c2 n2,
         c0 -[ my_old ]->* c1 -> halted my_old c1 -> my_ones c1 n1 ->
         c0 -[ my_new ]->* c2 -> halted my_new c2 -> my_ones c2 n2 -> n1 < n2).

It also proves that both machines halt only reading a 0 (`my_new_halts_on_blank`, `my_old_halts_on_blank`).

## Files

| file | content |
|---|---|
| `BB142.v`, `Individual142.v` | busycoq instantiated for 14 states (byte-identical to `../../verify_m14_fw3/multifile/`). The state `L` shadows busycoq's direction `L`, so tables write `TM.L` / `TM.R`. |
| `BB14_M14_fw3.v` | M14_fw3's proof (byte-identical to `../../verify_m14_fw3/multifile/`), loaded by the comparison |
| `BB14_M14_fw3x4.v` | Gemini 4 Neon's proof, unchanged (byte-identical to the audited file): the cascade rules of M12's core, the macro steps Kc, Kc_full, Kd_step, the outer step and outer loop, the 240-step opening, the four loops and their three bridges, the halt, the exact score, the bound, the renamed table `tm_tnf`, and the module `M14_Old` with its own proof about M14_fw3 |
| `BB14_M14_fw3x4_entry.v` | written here: the table of the machine string as `tm`, `halt`, `score_exact`, `sigma_bound` (from Neon's `_tnf` theorems) |
| `BB14_M14_fw3x4_cmp.v` | written here: `M14_fw3_score_agrees`, `beats_M14_fw3_all`, `beats_M14_fw3_exact`, `beats_M14_fw3_score` |
| `BB14_M14_fw3x4_audit.v` | from the independent audit: the statements over hand-transcribed tables and its own definitions (above) |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject`, `share_check.sh` | build script, project file, check that the three shared files are byte-identical to `../../verify_m14_fw3/multifile/` |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `compile_clean.sh` first runs `share_check.sh` when the other directory is present. `probe.v`
checks three compiled transition tables against the two machine strings entry by entry (84 checks generated from
the strings, not from the Coq files): the entry's `tm` and Neon's `tm_tnf` against the machine string, and Neon's
`tm` against the same machine in M12's state order,
`1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LL1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_---0LL_0LG1LN_1RN0LH_1RK0LL` (start G). It
checks the start configurations (`c0` = blank tape in A, Neon's `c0_core` = blank tape in G), prints the
definitions the statements use, and runs `Print Assumptions` on fourteen theorems (the entry's three, Neon's `halt`,
`score_exact`, `sigma_bound`, `beats_M14_fw3_exact`, the comparison file's four and the audit file's three): all
fourteen are closed under the global context (`compile_clean.log`: about 2.5 minutes). CI job `bb13-bb14` runs the
same script.

The entry file also passes this project's `check.py` (the statement `halts tm c0` read from the file, the table
compared with the machine string, `Print Assumptions halt` closed): PASS, 2026-11-23. Neon's file on its own does
not (it has no `(* machine: … *)` line, and its `halt` is stated for the G-started table), which is why the entry
file exists.
