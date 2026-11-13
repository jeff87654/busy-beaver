# Coq proofs for `1RB1RH_1RC0LD_1LD1RJ_1LE1LB_1LF1LE_1RG0LE_1RA1RG_0LI1LF_0RC1LI_1RK0RG_1RZ0LB` (C4)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). In the Coq table the halt K0 is undefined (`---`); it is read on a 0 and the halting transition writes a
1, so σ = N + 1, where N is the number of ones at the halt. The table is the start-A relabelling of M12 without state
L (see the write-up). It proves:

- `BB11_C4.halt : halts tm c0`: the machine halts from the blank tape;
- `BB11_C4.score_exact`: the halting tape holds exactly `snd nFIN + 3 + fst nFIN` ones, for the explicit pair `nFIN`
  of the run (notations in `BB11_C4.v`, section "the run");
- `BB11_C4_bound.sigma_lower_bound`: N > f_(ω+2)(f_(ω+2)(f_5(34)));
- `BB11_C4_bound.sigma_lower_bound_34`: N > f_(ω+2)(f_(ω+2)(34));
- `BB11_C4_bound.beats_M11b`: N > f_(ω+1)(f_ω(f_ω(6))), the upper end of M11b's proved bracket
  (`sigma_bracket_m11`: N_M11b + 1 < f_(ω+1)(f_ω(f_ω(6))));
- `BB11_C4_bound.beats_M12_lower`: N > f_(ω+2)(f_(ω+1)(f_(ω+1)(3))), M12's proved LOWER bound only;
- `BB11_C4_cmp.beats_M11b_score`: the comparison with M11b's exact score as one statement: M11b's halting tape holds
  NM ones and C4's holds n ones with NM + 1 < n;
- `BB11_C4_vs_M12.beats_M12_exact`, `beats_M12_score`: C4's N is above M12's EXACT score: M12's halting tape holds
  `fst pb2 + snd pb2 / 2 + 3` ones (`BB12_M12_bound.score_exact`), proved here to be at most
  f_(ω+2)(4·f_(ω+1)^6(12)) + 3 from the definitions of M12's maps.

As published:

    Theorem halt : halts tm c0.
    Theorem score_exact : exists c, c0 -->* c /\ halted tm c /\ ones c (snd nFIN + 3 + fst nFIN).
    Theorem sigma_lower_bound :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega2 (f_omega2 (f 5 34)) < N.
    Theorem beats_M11b :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega1 (f_omega (f_omega 6)) < N.
    Theorem beats_M12_lower :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega2 (f_omega1 (f_omega1 3)) < N.
    Theorem beats_M11b_score :
      exists NM,
        (exists c, c0 -[ BB11_M11b.tm ]->* c /\ halted BB11_M11b.tm c /\ BB11_M11b_fgh.ones c NM) /\
        (exists c n, c0 -[ tm ]->* c /\ halted tm c /\ ones c n /\ NM + 1 < n).
    Theorem beats_M12_exact :
      exists c n, c0 -->* c /\ halted tm c /\ ones c n /\ fst BB12_M12.pb2 + snd BB12_M12.pb2 / 2 + 3 < n.
    Theorem beats_M12_score :
      exists NM,
        (exists c, (M12 reaches c from c0) /\ halted BB12_M12.tm c /\ BB12_M12_bound.ones c NM) /\n        (exists c n, c0 -->* c /\ halted tm c /\ ones c n /\ NM < n).
    (in the file the first conjunct is written with busycoq's fully qualified evstep and c0 for M12's 12 states)

Since the machines are deterministic, the halted configuration reached from `c0` is unique, so the theorems
describe one tape per machine. Both machines halt reading a 0 with a halting transition that writes a 1, so
`beats_M11b_score` gives σ(M11b) = NM + 1 < n < σ(C4). The fast-growing hierarchy is the standard one, defined in
`BB11_C4_bound.v`: `f 0 n = n+1`, `f (k+1) n = (f k)^n n`, `f_omega n = f n n`, `f_omega1 n = f_omega^n n`,
`f_omega2 n = f_omega1^n n`; `iter` is defined in `BB11_C4.v`. M11b's files define `iter`, `f`, `f_omega`,
`f_omega1` and `ones` with the same text; `BB11_C4_cmp.v` proves the equalities for variables and rewrites M11b's
upper bound with explicit instances (no closed term of the hierarchy is computed). M12 also halts reading a 0 with a
halting transition that writes a 1, so `beats_M12_score` gives σ(M12) < σ(C4), and BB(12) ≥ BB(11) + 1 > σ(M12).
`BB11_C4_vs_M12.v` bounds M12's maps W, Kc, Kc_full, Kd_step, Kd_iter and D_reload from above, with the argument of
`BB13/verify_m13_19/multifile/BB13_M13_19_cmp.v` (M13b has the same maps), and uses C4's `FIN_dom`.

## Files

| file | content |
|---|---|
| `BB112.v`, `Individual112.v` | busycoq instantiated for 11 states (byte-identical to `../../verify/multifile/`) |
| `BB11_M11b.v`, `BB11_M11b_fgh.v`, `BB11_M11b_upper.v` | M11b's proof (byte-identical to `../../verify/multifile/`), loaded by the comparison |
| `BB11_C4.v` | the halting proof: M12's engine lemmas with the states renamed, W mod 4 (`W_mod4`), the configurations X, Y, Z, V, the rules STOCK, CONV, RESTART, ZSTEP, ZEND, ROUND, HALT, T2, T3, MID, the 150-step opening, the run and `score_exact` |
| `BB11_C4_bound.v` | the lower bounds (`Zs_dom`, `Rnd_dom`, `FIN_dom`) and the theorems above; imports `BB11_C4.v` |
| `BB11_C4_cmp.v` | `beats_M11b_score` |
| `BB122.v`, `Individual122.v`, `BB12_M12.v`, `BB12_M12_bound.v` | busycoq for 12 states and M12's proof (byte-identical to `../../../BB12/verify_m12/multifile/`), loaded by the comparison with M12 |
| `BB11_C4_vs_M12.v` | `beats_M12_exact`, `beats_M12_score` (written as `BB11_C4_cmp.v` in the project's notes; only its first comment line was changed, for the new name) |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject`, `share_check.sh` | build script, project file, check that the nine shared files are byte-identical to `../../verify/multifile/` and `../../../BB12/verify_m12/multifile/` |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build and of the probe, hashes of the source files |

`BB11_C4.v` and `BB11_C4_bound.v` are this project's proof files, unchanged except for line endings (CRLF to LF).

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `compile_clean.sh` first runs `share_check.sh` when the other directory is present. `probe.v`
checks the compiled transition table against the machine string entry by entry (22 checks generated from the
string, not from the Coq file) and the blank start configuration. It prints the definitions the statements use and
runs `Print Assumptions` on the nine theorems above: all nine are closed under the global context. CI job
`bb13-bb14` runs the same script.

The halting proof also passes this project's `check.py` (the statement `halts tm c0` read from the file, the table
compared with the machine string, `Print Assumptions halt` closed): PASS, 2026-11-13.
