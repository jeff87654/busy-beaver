# Coq proofs for `1RB1RA_1RI1RC_0LD1LG_0RE1LD_1RZ1RF_0LL0RA_1RA0LH_1LG1LH_1RK0LJ_1LH1LI_0LL0RD_0LH1LK` (P12)

`multifile/` is a Coq development on top of [busycoq](https://github.com/meithecatte/busycoq) (commit `bd2e36f`,
Coq 8.20.1). In the Coq table the halt E0 is undefined (`---`); it is read on a 0 and the halting transition writes a
1, so σ = N + 1, where N is the number of ones at the halt. It proves:

- `BB12_P12.halt : halts tm c0`: the machine halts from the blank tape;
- `BB12_P12.score_exact`: the halting tape holds exactly `snd nP + fst nP + 1` ones, for the explicit pair `nP` of
  the run (notations `nD0`, `nD7`, `nP` in `BB12_P12.v`, before `run_FIN`);
- `BB12_P12_bound.sigma_lower_bound`: N > f_(ω+2)^8(f_3(6));
- `BB12_P12_cmp.beats_C4_exact`, `beats_C4_score`: N is above C4's EXACT score plus one: C4's halting tape holds
  `snd nFIN + 3 + fst nFIN` ones (`BB11_C4.score_exact`), proved here to be at most f_(ω+2)^7(8) + 3 from the
  definitions of C4's maps (`c4_score_ub`).

As published:

    Theorem halt : halts tm c0.
    Theorem score_exact : exists c, c0 -->* c /\ halted tm c /\ ones c (snd nP + fst nP + 1).
      (nD0 = 7 + W 4 1 / 2 + 2,  nD7 = iter 7 Big nD0,  nP = iter ((nD7 - 3) / 2) Rd (7, W 4 1 + 2))
    Theorem sigma_lower_bound :
      exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ iter 8 f_omega2 (f 3 6) < N.
    Theorem beats_C4_exact :
      exists c n, c0 -->* c /\ halted tm c /\ ones c n /\ snd nFIN + 3 + fst nFIN + 1 < n.
    Theorem beats_C4_score :
      exists NC,
        (exists c, (C4 reaches c from c0) /\ halted BB11_C4.tm c /\ BB11_C4.ones c NC) /\
        (exists c n, c0 -->* c /\ halted tm c /\ ones c n /\ NC + 1 < n).
    (in the file the first conjunct is written with busycoq's fully qualified evstep and c0 for C4's 11 states)

Since the machines are deterministic, the halted configuration reached from `c0` is unique, so the theorems
describe one tape per machine. Both machines halt reading a 0 with a halting transition that writes a 1, so
`beats_C4_score` gives σ(C4) + 1 = NC + 2 ≤ n < σ(P12): P12 is above the bound BB(12) ≥ BB(11) + 1 that C4 gives.
The fast-growing hierarchy is the standard one, defined in `BB12_P12_bound.v` with the text of
`BB11_C4_bound.v`: `f 0 n = n+1`, `f (k+1) n = (f k)^n n`, `f_omega n = f n n`, `f_omega1 n = f_omega^n n`,
`f_omega2 n = f_omega1^n n`; `iter` is defined in `BB12_P12.v`. `BB12_P12_cmp.v` bounds C4's maps W, Zs and Rnd
from above and uses P12's `N_dom`.

## Files

| file | content |
|---|---|
| `BB122.v`, `Individual122.v` | busycoq instantiated for 12 states (byte-identical to `../../verify_m12/multifile/`) |
| `BB12_P12.v` | the halting proof: M12's engine (Ca, Ch, W) for this table, the configurations X, Y, the rules R_A, R_H, R_Bo, R_Be, BLANK, BOOT2, the 2-adic residues of W (`W2_closed`, `ord3`, `W2_cong`, `T_tab`, `W_res`), the maps Be, Rd, Big and their residues (`Big_mod`, `Big1`–`Big7`, `chain`), the loops (`ROUND`, `ROUNDS`, `BOOT`, `BIG_EVEN`, `BIG_ODD`, `RUN_GEN`), the opening `boot`, `halt` and `score_exact` |
| `BB12_P12_bound.v` | the lower bound (`N_dom`) and `sigma_lower_bound`; imports `BB12_P12.v` |
| `BB112.v`, `Individual112.v`, `BB11_C4.v` | busycoq for 11 states and C4's halting proof (byte-identical to `../../../BB11/verify_c4/multifile/`), loaded by the comparison |
| `BB12_P12_cmp.v` | `c4_score_ub`, `beats_C4_exact`, `beats_C4_score` |
| `probe.v` | the independent probe (below) |
| `compile_clean.sh`, `_CoqProject`, `share_check.sh` | build script, project file, check that the five shared files are byte-identical to `../../verify_m12/multifile/` and `../../../BB11/verify_c4/multifile/` |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build and of the probe, hashes of the source files |

`BB12_P12.v`, `BB12_P12_bound.v` and `BB12_P12_cmp.v` are this project's proof files, unchanged.

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `compile_clean.sh` first runs `share_check.sh` when the other directories are present.
`BB12_P12.v` takes about 5 minutes. `probe.v` checks the compiled transition table against the machine string entry
by entry (24 checks generated from the string) and the blank start configuration. It prints the definitions the
statements use and runs `Print Assumptions` on the five theorems above: all five are closed under the global
context. CI job `bb13-bb14` runs the same script.

The halting proof also passes this project's `check.py` (the statement `halts tm c0` read from the file, the table
compared with the machine string, `Print Assumptions halt` closed): PASS, 2026-11-15.
