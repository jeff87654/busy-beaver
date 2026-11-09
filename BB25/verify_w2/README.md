# Coq proofs for W2PR's ω² bound (`0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LV_0LH0LW_1LH0LX_1LH1LY_0LE1LR`)

`multifile/` extends W2PR's halting proof in [`../verify/`](../verify/) with B21's quantitative layer
([`../../BB21/verify_w2/`](../../BB21/verify_w2/)). On top of busycoq (commit `bd2e36f`, Coq 8.20.1), for this
machine (R0 undefined = the halt, `1RZ` in the string), it proves:

- `BB25_W2PR_w2.halt : halts tm c0` (the same proof as `../verify/`'s);
- `BB25_W2PR_w2.sigma_lower_bound`: Fh⁵(4↑↑341) < N (as in `../verify/`);
- `BB25_W2PR_w2.sigma_lower_bound_wsq`: f_(ω²)^5(4↑↑341) < N;
- `BB25_W2PR_w2.beats_B21`: f_(ω²)^3(4↑↑341) < N, B21's proved BB(21) bound (`BB21_B21_w2.sigma_lower_bound_wsq3`).

Here N is the number of ones on the halting tape, and σ = N + 1. As published:

    Theorem sigma_lower_bound_wsq :
      exists c N, c0 -[ tm ]->* c /\ halted tm c /\ BB25_W2PR_score.onesN c N /\
        (BB21_B21_absdef.iter 5 BB_FGH_wa.f_wsq (BB25_W2PR_run.tet 341) < N)%nat.
    Theorem beats_B21 :
      exists c N, c0 -[ tm ]->* c /\ halted tm c /\ BB25_W2PR_score.onesN c N /\
        (BB21_B21_absdef.iter 3 BB_FGH_wa.f_wsq (BB21_B21_score.tet 341) < N)%nat.

`f_wsq` = f_(ω²) is the standard one, from `BB_FGH_wa.v` (see `../../BB21/verify_w2/README.md`); `BB25_W2PR_run.tet`
and `BB21_B21_score.tet` are the same function (both `tet 0 = 1`, `tet (n+1) = 4 ^ tet n`; `tet_B21`). `beats_B21`
compares W2PR with B21's proved lower bound, not with an upper bound on B21's σ.

**How:** `BB25_W2PR_bound.v` runs phases 4 to 8 through B21's quantitative phase lemma `phase_from_work_q`, with
W2PR's refill rule. Each phase applies f_(ω²), and the factor-4 losses at the refills are absorbed by `chain_step` and
`chain_last` (`abstract_finalW_q`, `sigma_lower_boundW_wsq`, `beats_B21_bound`).

## Files (in dependency order)

All files except `BB25_W2PR_bound.v` and `BB25_W2PR_w2.v` are **byte-identical** copies of published files:

| file | copied from |
|---|---|
| `BB252.v`, `Individual252.v`, `BB25_W2PR_{tm,sim,run,score}.v`, `BB21_B21_{absdef,grow,steps,inv,proc,phase,run}.v` | [`../verify/multifile/`](../verify/multifile/) |
| `BB202.v`, `Individual202.v`, `BB20_JZ20.v`, `BB182.v`, `Individual182.v`, `BB18_R18a.v`, `BB212.v`, `Individual212.v`, `BB21_B21_{tm,sim,score}.v`, `BB_FGH_wa.v`, `BB_FGH_wa2.v`, `BB21_B21_qnt.v` to `BB21_B21_qnt4.v` | [`../../BB21/verify_w2/multifile/`](../../BB21/verify_w2/multifile/) (themselves copies of `BB20/verify`, `BB18/verify_r18a` and `BB21/verify` where they come from there) |
| `BB25_W2PR_bound.v` | new: phases 4 to 8 with the quantitative layer |
| `BB25_W2PR_w2.v` | new: the table and the four headline theorems |
| `probe.v` | the independent probe (below) |
| `share_check.sh` | checks the 30 copies against the published files |
| `compile_clean.sh`, `_CoqProject` | build script (runs `share_check.sh` first when the other trees are present), project file |
| `compile_clean.log`, `probe.log`, `sha256.txt` | logs of a from-scratch build (about 5 minutes) and of the probe, hashes of the source files |

## Check it

    cd multifile
    BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh

`BUSYCOQ` must point to the `verify/` directory of a busycoq checkout at commit `bd2e36f`, with `Individual.vo`
and `Flip.vo` built. `probe.v` checks the compiled transition table of `BB25_W2PR_w2.tm` against the machine string
entry by entry (50 checks generated from the string, not from the Coq file) and the blank start configuration. It
prints the definitions the statements use and runs `Print Assumptions` on the four theorems above: all four are closed
under the global context. CI job `bb13-bb14` runs the same script.

The proof was also checked with this project's `check.py` (25 states): PASS, 2026-11-08.
